;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.core
  "Vaelii — a contextualized common-sense knowledge base.

  A KB bundles a record store (the durable ground truth), an index store (derived
  from it, rebuildable), a JTMS, and a taxonomy (cached genl / genlCx closures).
  The unit of knowledge is a *sentex*: a sentence plus the context it holds in.
  Rules are sentexes too.

  Public API: `open-kb`, `assert`, `assert-rule`, `forward-chain`, `query`,
  `sentexes-matching`, `ask`, `prove`, `retract!`, `why`, `in?`, `isa?`.  This is a
  signpost, not the full list — docs/api.md is that, and its \"Choosing a query
  function\" table is what separates the five ways to answer a goal.

  This namespace is the engine's whole API; the engine itself lives in layered
  `vaelii.impl.*` namespaces (kb <- checks <- special <- integrate <- chain <-
  settle) and everything here is either a delegation into that stack or the
  `assert` / `retract!` / `recover` orchestration that spans it.

  Five entry points are public beside it, each a thin shim over the same stack:
  `vaelii.client` (the network client), `vaelii.starter` (the bundled ontology),
  and `vaelii.web` / `vaelii.serve` / `vaelii.cli` (the browser, the daemon, the
  command line).  Those six namespaces are the compatibility boundary — everything
  under `vaelii.impl.*` is free to change without notice."
  (:refer-clojure :exclude [assert isa?])
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.abduce :as abduce]
            [vaelii.impl.argtype-pass :as argpass]
            [vaelii.impl.assert-entry :as entry]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches-impl]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.config :as config]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.except :as exc]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.fluent :as fluent]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.inference :as inference]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.integrity :as integrity]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.io.import :as io-import]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.levels :as lvl]
            [vaelii.impl.logging :as logging]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.modal :as modal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-maintenance :as nat-maint]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.predall :as predall]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.quality :as quality]
            [vaelii.impl.quasiquote :as quasiquote]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.record-edit :as record-edit]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rete :as rete]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.scenario :as scenario]
            [vaelii.impl.seal :as seal]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.skolem :as skolem]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.vantage :as vantage]
            [vaelii.impl.violations :as viol]
            [vaelii.impl.vocabulary :as vocab]
            [vaelii.impl.wiring :refer [*defer-settle?*]])
  (:gen-class))

;; recover and reindex are defined at the bottom of this namespace (they rebuild
;; through everything above them), and open-kb's :recover? :auto needs both — a
;; genuine forward reference: construction sits below the whole engine stack
;; (vaelii.impl.kb), so the two functions are injected rather than required.
(declare recover reindex)

(defn- releasing-on-throw
  "Call `construct`, which opens the KB `opts` describes.  A throw *after* the durable
  stores resolve — a stale-index refusal, a `:pg` identity mismatch, a fork's base that
  grew into its handles, a `recover` over a corrupt store — returns no KB, so the exclusive
  lock those stores took would be held for the JVM's life with nothing to release it.
  Snapshot which of the KB's directories are already open (a healthy KB may share one —
  `store-for` keys stores per canonical path), construct, and on a throw close only the
  directories *this* call newly opened, writing no image: what the failed open holds is a
  partly loaded index or belief, and an image of it would replace the one on disk.
  `store-for` already releases a lock its own component-open throws under; this covers
  the gap where one component opened and a later step threw."
  [opts construct]
  (let [dirs (kb/durable-dirs opts)
        pre  (into #{} (filter #(seq (disk/opened %))) dirs)]
    (try
      (construct)
      (catch Throwable t
        (doseq [d dirs :when (and (not (contains? pre d)) (seq (disk/opened d)))]
          (try (disk/close-dir! d {:images? false})
               ;; best-effort: the construction failure `t` is what the caller needs, and a
               ;; release that itself throws must not replace it
               (catch Throwable _ nil)))
        (throw t)))))

(defn open-kb
  "Construct a KB.  Every option is optional; `(open-kb {})` is records and index in RAM.

  | opt | what it picks | default |
  |---|---|---|
  | `:backend` | a records×index pair, spelled `<records>-<index>` | `:memory` |
  | `:records` / `:index` | one axis of that pair on its own | from `:backend` |
  | `:space` | which in-RAM stores this KB shares | `0` |
  | `:dir` | the directory a durable half lives in | derived from the space |
  | `:base` / `:overlay` | the two halves of an `:overlay` fork | — |
  | `:tms` | `:dense` or `:reference` truth-maintenance representation | `:dense` |
  | `:naming` | `:strict` / `:warn` / `:off` — what the public entry point does with a name | `:strict` |
  | `:recover?` | `:trust` / `:auto` (or `true`) / `:background` / `:warn` / `false` — what a non-empty store gets | `:trust` |
  | `:oplog?` | `true` (or `:each`) / `:tick` / `false` — an operation log, and when its frames are fsynced | `false` |

  The seven legal backends and why the eighth is refused: docs/storage.md.  What
  `:recover? :background` installs, and what it refuses until its rebuild finishes:
  docs/storage.md, \"Rebuilding behind an image\"; what `:trust` keeps instead: \"Trusting
  an image\".  What `:oplog?` attaches, and what an
  open with it restores: docs/storage.md, \"The operation log\".  The naming
  policy and what no setting moves: docs/naming.md.  `fork` is the ergonomic spelling of
  `:overlay` and takes its base from a live KB; the raw form takes `:base` opts instead,
  which is what mounts a base this process has no KB open over.

  **An option this fn does not read is refused** rather than ignored, and the space
  number is why: a misspelt `:space` is a key nothing looks at, so the KB would
  quietly open on the default space and two KBs meant for separate stores would share
  one — each one's flush emptying the other.  `vaelii.impl.kb/opt-keys` is the key set.

  **The space number names the store, and it defaults.**  So `(open-kb {})` twice in one
  process is one set of records behind two KB values — the second recovers the first's
  facts, and from then on a write through either is invisible to the other, since belief
  is per-KB and only the writer's is relabelled.  That is the REPL's ordinary gesture for
  starting clean, so the second default open logs a warning naming the fix.  Give a KB
  that wants its own store its own space (`{:space 2}`); naming the number at all — 0
  included — says the sharing is meant.

  **One number, both stores.**  The records and the index answer to it together: each
  backend keys its own registry, so a KB cannot be handed a private index over records
  it shares, nor a shared index over records it does not.  An index is a function of the
  records, so the two are shared or separate as one thing.

  **A non-empty store needs `recover`, and gets it.**  A fresh KB over stores that
  already hold sentexes has an empty TMS and taxonomy, so `sentexes-matching` answers
  nothing, `isa?` answers false, and the definitional checks pass vacuously — every
  answer quietly wrong for one forgotten call.  The default, `:recover? :trust`, repairs
  that on construction (`reindex` first when the index is derived and therefore opened
  empty): it installs a `:disk-snapshot` store's reasoning image when the image describes
  the records, and recovers from them, one pass over the stored records, when it does not.
  It recovers by default because the failure it prevents is a *wrong answer* rather than
  an error: `false` and `[]` are legitimate results, so no caller can tell them apart, and
  a warning is a log line a configured level can drop.

  **An image an earlier build wrote is kept by default.**  `:trust` installs an image
  written under other engine source, and settles move belief under this build only where
  they reach.  `:auto` declines that image and recovers under this build, which at
  millions of sentexes is an hour or more; it is the setting for a caller that needs
  belief this build derived in full, as `lein cli upgrade` does.  `:warn` only logs;
  `false` is silent, for a caller managing recovery itself.  `true` is an alias for
  `:auto`, since a caller takes a `?`-suffixed option for a boolean; anything else is
  refused (`:type :unknown-option`), because the dispatch cannot tell an unrecognized
  setting from `:warn` and would hand back the empty TMS the caller asked to avoid.

  **And such a KB does not accept writes.**  What `:warn` and `false` leave is a state a
  read can survive — an empty answer is one you can ask again — and a write cannot: the
  definitional checks all pass vacuously over an empty network and nothing re-runs them,
  so the store keeps content it would have refused.  So the write entry points refuse it by name
  (`:unrecovered-kb`), and `*write-unrecovered?*` is the opt that accepts one anyway.
  `false` stays silent about the *read* side and says the write side once, at `:info`:
  a caller managing recovery itself already knows the queries answer nothing, and cannot
  be expected to know the refusal is waiting.

  The KB value's slots — the prover registry, the solver, the ledgers, the caches — are
  documented on the record in `vaelii.impl.kb`."
  ([] (open-kb {}))
  ([opts]
   (let [plain (fn [o] (recovery/register-fresh-store! (kb/open-kb o recover reindex)))
         mode  (kb/oplog-mode opts)]
     (releasing-on-throw opts (if mode
                                #(seal/open! opts plain {:fsync mode})
                                #(plain opts))))))

(defn fork
  "A private, writable KB over this one's stores — a **fork**.  Reads resolve fork-first
  and fall through to `kb`, writes land only in the fork, and **`kb` is never written**,
  so several forks may share one base and evolve independently.

  `opts` names the fork's *own* storage, as an ordinary opts map (`:backend :memory` by
  default — an ephemeral hypothesis on a space nothing else uses, which `close!` drops;
  `{:backend :disk-log :dir …}` gives a durable one, which can be remounted over the same
  base later and serves the merged contents it was left in).  `:tms` selects the fork's truth-maintenance
  representation and, unlike the entry-point policies below, does **not** inherit: an
  unnamed `:tms` takes the engine default (`:dense`), not the base's rep.  That is safe
  because the two are belief-identical (`jtms_dense_oracle_test`), so a fork holds the same
  beliefs whichever representation it rebuilds them in.

  **The fork's belief is rebuilt, not inherited.**  Belief is not storage — it is a
  derived graph over the records — so the fork is `recover`ed over the merged contents rather
  than layered over the base's network.  That is one pass over the merged records, which
  is what `recover` costs anywhere.

  The base is frozen by the mount, not copied: nothing is written and nothing is
  duplicated, so the cost of taking a fork is the recovery and not the base.  The index
  must be one written over the `KvBackend` protocol (`:memory`, `:dense`, `:disk-log`); a
  `:columnar` index is refused, since a KV decorator would fork its roots and leave its
  native trie behind.

  **The naming policy is inherited** unless `opts` names one.  A fork is a hypothesis
  over the base's own content, and a fork that quietly held it to different conventions
  would answer a different question from the one the caller asked."
  ([kb] (fork kb {}))
  ([kb opts]
   (let [own    (dissoc opts :tms :naming)
         ;; a RAM overlay that names no :space would land on the shared process
         ;; default (space 0) — two such forks would see each other's writes, and a
         ;; plain open-kb in the same JVM would see both — so any opts naming neither
         ;; a :space nor a :dir take the fresh fork space, exactly as no opts do;
         ;; naming one explicitly stays the remount spelling
         fresh  {:backend :memory :space (mem/engine-space :fork)}
         own    (cond
                  (not (seq own))              fresh
                  (or (:space own) (:dir own)) own
                  :else                        (merge fresh own))
         spec   {:records  :overlay
                 :index    :overlay
                 :base-stores {:records (:records kb) :index (:index kb)}
                 :overlay  own
                 :tms      (:tms opts :dense)
                 :naming   (:naming opts (:naming kb :strict))
                 :recover? false}]
     (releasing-on-throw spec #(doto (kb/open-kb spec recover reindex) recover)))))

(def default-chain-opts
  "The bounds a chaining run takes when `opts` names none: `:max-term-depth`, the
  termination bound for term-building recursion, and `:max-derivations`, the cap on one
  run's writes.  `:max-depth` has no default (docs/inference.md, \"Forward chaining\")."
  chain/default-chain-opts)

;; ---- the content order ---------------------------------------------------
;; Order independence is a property of the engine, not only of its internals: a caller
;; that ranks its own answers has the same tie to break, and breaking it on a handle —
;; allocated in assertion order — would make the ranking a fact about how the KB was
;; loaded.  So the engine's own order is public, and an application layered on this API
;; ranks by the same one rather than re-deriving a weaker one.

(defn sort-by-content
  "`coll` ordered by `(keyfn element)` under `cmp` — the engine's own **content** order,
  and what a caller ranking sentexes, sentences or terms should reach for instead of
  `sort-by` on a printed key or on a handle.

  `cmp` defaults to the structural comparator the engine's internal orders use: it walks
  a key in place instead of printing it, so no ambient `*print-*` var can elide two
  distinct keys to one and drop the tie back onto enumeration order, and numbers compare
  numerically (9 before 10) rather than lexicographically.  Different kinds order by kind,
  same-kind scalars by the natural `compare`, and two sequentials element by element then
  shorter first — arbitrary but **stable**, which is the contract a content order owes.
  A key outside that shape — a map, a set — is the one thing it prints, through a guard
  that releases the print bounds first, so it is ordered by its full print and not walked.  Pass
  `compare` instead when the key is already a `Comparable` tuple whose own order is the
  contract.

  The key is built **once per element**, not once per comparison as `sort-by` would, and a
  `coll` below two builds none at all — which matters when the key is a store read per
  element.

  Total and deterministic over whatever `keyfn` returns.  **The content half is the
  caller's:** no handle enters the comparator, but nothing stops a `keyfn` from returning
  one, and then the ranking is a fact about how the KB was loaded again.  Key on the
  sentex's own `:sentence` / `:context`, never on its handle, and two KBs holding the same
  knowledge rank it the same however differently they were built."
  ([keyfn coll] (nm/sort-by-content-key keyfn coll))
  ([keyfn cmp coll] (nm/sort-by-content-key keyfn cmp coll)))

;; ---- type queries -------------------------------------------------------

(defn isa?
  "Is individual `x` (transitively) of type `t`?  Considers only type memberships
  visible from `context` (default: any context)."
  ([kb x t] (kb/isa? kb x t))
  ([kb x t context] (kb/isa? kb x t context)))

(defn find-sentexes
  "Every stored sentex that contains `term` anywhere (any position, any nesting).
  Powered by the inverted term index."
  [kb term]
  (kb/find-sentexes kb term))

(defn find-sentexes-all
  "Every stored sentex that contains all of `terms`."
  [kb terms]
  (kb/find-sentexes-all kb terms))

;; ---- the vocabulary: enumerate and search the terms themselves ----------
;; `find-sentexes` goes from a term to the sentexes mentioning it.  These go one step
;; earlier: *which terms are there at all*.  They read the index's term-name set — the set
;; of names the inverted term index is keyed by, maintained beside its postings — so the
;; cost is the size of the **vocabulary**, never the size of the KB.

(defn terms
  "Every term the index is keyed by — the KB's vocabulary: each predicate, individual,
  type, and context name mentioned by a stored sentex, at any nesting depth.  Sorted by
  name, so the answer is stable and reads the same in-process and over the wire (a
  sorted set would lose its order to EDN; a vector keeps it).

  Read from the term-name set, so it is O(terms), not O(sentexes) — and the sort is the
  only superlinear part, which `find-terms` pays over its hits alone.  A *ground
  compound* subterm keys the term index too (`find-sentexes` takes one), but it is a
  sentence fragment rather than a name, so it is not part of the vocabulary.

  Terms are what is **stored**: a defeated or unsupported sentex keeps its names here,
  exactly as it keeps its extent in the secondary roots."
  [kb]
  (vec (sort (reads/stored-terms-global (:index kb)))))

(defn term-count
  "How many distinct terms the KB's vocabulary holds — one set-size read, O(1), nothing
  fetched.  The cardinality of `terms`, and like it a count of what is stored."
  [kb]
  (reads/stored-term-count-global (:index kb)))

(defn sentex-count
  "How many sentexes the KB holds, in total — the count the count-aware trie keeps at its
  root, so O(1) and nothing fetched.

  A count of what is **stored**, like the `count-*` trio: a defeated or unsupported
  sentex is included, as is a rule and a metadata declaration.  Summing `count-in-context`
  over `contexts` is not the same number — that counts only what is in a context the
  *taxonomy* knows, so content in a context no `genlCx` edge mentions is invisible
  to it."
  [kb]
  (reads/stored-count-at (:index kb) []))

(defn- check-bound-opts!
  "Refuse an opts key `fn-name` does not read (its key set is `opt-keys`), and a
  non-nil non-map `opts` — `check-assert-opts!`'s reasoning at the two consequence
  entry points.  Every key either of them reads is a bound on the run or on the answer, so
  the silent-default failure is a cap silently off: `{:max-result 5}` reads as no key
  at all and the diff comes back uncapped, with `:bounded?` false as though the whole
  answer had been asked for."
  [opts opt-keys fn-name]
  (opts/check! opts opt-keys fn-name
               (str "An option nothing reads takes the default in silence,"
                    " which for a bound means running or answering uncapped.")))

(defn- check-limit!
  "Refuse a cap that is not a positive integer, `where` naming the entry point and the spelling
  it arrived under (`\"find-terms :limit\"`, `\"qualitative-scenarios limit\"`).

  The **value** refusal beside the key check above, and the key set cannot make it: a
  key nothing reads is one failure, and a key that is read holding a value it cannot mean
  is the other.  Unchecked, a cap that is not a number fails two ways depending on the
  entry point: it reaches `take` — or, at `qualitative-scenarios`, the enumerator — and raises a
  bare cast error carrying no `:type`, which over the daemon is a 500 where every sibling
  refusal is a typed 400; or it is guarded by a `pos-int?` and read as **no cap at all**,
  which is the silent default the key set beside it exists to refuse, answering uncapped
  with `:bounded?` false as though the whole answer had been asked for.  Every entry point taking
  a cap says it the same way, so the sentence lives here rather than once per entry point.

  A caller with an *optional* cap tests for the key first (`when-some`): an absent one is
  no cap, which is a legitimate request rather than a bad value."
  [n where]
  (when-not (pos-int? n)
    (throw (ex-info (str where " must be a positive integer, got " (pr-str n))
                    {:type :unknown-option :mismatch :bad-value :limit n}))))

(def ^:private ^:const regex-step-budget
  "Characters one match may read against a single term before the pattern is refused as
  too costly.  A linear match reads O(term length); a catastrophically-backtracking one
  reads super-linearly and blows this in short order, so the two separate cleanly.  Per
  candidate, not cumulative — scanning a large vocabulary is not itself the abuse; the
  scan as a whole is bounded separately by `regex-scan-budget`."
  1000000)

(def ^:private regex-scan-budget
  "Characters one `find-terms` regex may read across the **whole** vocabulary before it
  is refused.  The per-candidate budget above catches a pattern that backtracks; it does
  nothing about a merely expensive one asked over a six-figure vocabulary, where the
  spend is the product of the two — and on the daemon that spend is taken holding the
  single writer, and on a public browser bind by an unauthenticated `GET /find`.  A
  hundred times the per-candidate budget: a linear pattern over an imported ontology reads
  tens of millions of characters and passes; a pathological one over the same vocabulary
  is refused before it has read the lot.  A plain `def` so a test can set it low."
  100000000)

(defn- step-limited
  "A `CharSequence` over `s` that throws `:pattern-too-costly` once a match has read more
  than `budget` characters — the standard interruptible-regex guard.  `Matcher` reads a
  char per backtracking step, so a pathological pattern (`(a+)+$` and its kin) is refused
  on the step that exceeds the budget rather than occupying a core.  That core matters:
  `:find-terms` runs over the daemon's single-writer monitor, so an unbounded match there
  wedges every write behind it, and the browser's length cap does not reach that path and
  would not stop a six-character pattern anyway.

  The scan-wide counter `scan` is shared by every candidate of one `find-terms` and
  refused past `scan-budget` — the same `:type`, with `:scope :scan`, so a caller reads
  one refusal either way."
  ^CharSequence [^String s ^long budget ^java.util.concurrent.atomic.AtomicLong scan
                 ^long scan-budget]
  (let [n    (.length s)
        seen (java.util.concurrent.atomic.AtomicLong.)]
    (reify CharSequence
      (length [_] n)
      (charAt [_ i]
        (when (> (.incrementAndGet seen) budget)
          (throw (ex-info (str "regex is too costly to evaluate against " (pr-str s)
                               " — the match read past " budget " characters of that one"
                               " term.  Anchor the pattern, or ask with :match :prefix or"
                               " :substring")
                          {:type :pattern-too-costly :scope :candidate})))
        (when (> (.incrementAndGet scan) scan-budget)
          (throw (ex-info (str "regex is too costly to evaluate across the whole"
                               " vocabulary — the scan read past " scan-budget
                               " characters, the last of them in " (pr-str s)
                               ".  Anchor the pattern, or ask with :match :prefix or"
                               " :substring")
                          {:type :pattern-too-costly :scope :scan})))
        (.charAt s i))
      (subSequence [_ a b] (.subSequence s ^int a ^int b))
      (toString [_] s))))

(defn- term-matcher
  "The predicate `find-terms` filters term names by, over a term's `str`."
  [q {:keys [match case-sensitive?]}]
  (case (or match :prefix)
    :prefix (let [p (str q), n (count p)]
              (if case-sensitive?
                (fn [^String s] (str/starts-with? s p))
                (fn [^String s] (.regionMatches s true 0 p 0 n))))
    :substring (if case-sensitive?
                 (let [p (str q)] (fn [^String s] (str/includes? s p)))
                 (let [p (str/lower-case (str q))]
                   (fn [^String s] (str/includes? (str/lower-case s) p))))
    ;; every candidate is matched through a step-limited wrapper, so a catastrophic pattern
    ;; is a `:pattern-too-costly` refusal rather than an unbounded spin (docs/web.md, and
    ;; the daemon runs this under its write monitor)
    :regex (let [^java.util.regex.Pattern re (if (instance? java.util.regex.Pattern q)
                                               q (re-pattern (str q)))
                 scan (java.util.concurrent.atomic.AtomicLong.)
                 scan-budget (long regex-scan-budget)]
             (fn [^String s]
               (.find (.matcher re (step-limited s regex-step-budget scan scan-budget)))))
    (throw (ex-info (str "unknown :match " (pr-str match) " — want :prefix, :substring, or :regex")
                    {:type :unknown-option :mismatch :bad-value :match match}))))

(defn- smallest-n
  "The first `n` of `(sort xs)`, without sorting `xs`: a bounded selection over one pass,
  O(m log n) for m hits against the full sort's O(m log m).  What `find-terms` with a
  `:limit` answers — the browser's search box asks for 201 of a vocabulary per keystroke,
  and on an imported ontology the hits for one letter run to tens of thousands.

  **Identical to the full sort and take, ties included.**  `sort` is stable, so among
  elements `compare` cannot tell apart it keeps the earlier ones; each candidate here
  carries its position and the order is `compare` then position, which is that same
  total order.  A max-heap of the `n` best so far, a new hit displacing the worst only
  when it is strictly better, then the kept `n` sorted under the same order.

  The heap's **initial capacity is not `n`**: `PriorityQueue(int)` allocates that array
  before an element is added, and `n` is a caller's `:limit` — the browser's paging
  computes it from a URL offset — so sizing on it turns a request for a million-th page
  into a million-element array over a KB holding one hit.  It grows from a small floor
  instead, which costs a few doublings in the one case where the hits really do run to
  `n` and nothing at all in the case the bound exists for."
  [n xs]
  (let [n     (long n)
        order (fn [[a i] [b j]]
                (let [c (compare a b)] (if (zero? c) (compare i j) c)))
        heap  (java.util.PriorityQueue. (int (min (max 1 n) 1024))
                                        ^java.util.Comparator (fn [x y] (order y x)))]
    (loop [xs (seq xs), i 0]
      (when xs
        (let [e [(first xs) i]]
          (if (< (.size heap) n)
            (.add heap e)
            (when (neg? (order e (.peek heap)))
              (.poll heap)
              (.add heap e))))
        (recur (next xs) (inc i))))
    (into [] (map first) (sort order (.toArray heap)))))

(defn find-terms
  "The vocabulary terms whose name matches `q`, sorted by name.  This is the search a
  term picker wants: it filters the **term-name set**, so it costs the size of the
  vocabulary and never a scan of the KB.

  `opts`:

    :match           :prefix (default) | :substring | :regex
    :case-sensitive? false by default — a search box should find `Dog` for `dog`;
                     ignored by :regex, where the pattern says so itself (`(?i)`)
    :limit           keep the first n of the sorted answer, so a bounded search is a
                     stable prefix of the unbounded one; anything but a positive
                     integer is refused (`:unknown-option`)

  `q` is a string or symbol; under `:match :regex` it may also be a compiled
  `java.util.regex.Pattern` in-process (over the daemon wire, send the pattern's source
  as a string — EDN carries no regex literal).  An unparsable regex throws, like
  `re-pattern` itself."
  ([kb q] (find-terms kb q nil))
  ([kb q opts]
   ;; the key set first: a misspelt `:mtch` or `:case-sensitve?` silently ran the
   ;; default search, and a prefix answer where substring was asked for reads as
   ;; \"no such term\" — in the browser's own search box, over the wire
   (check-bound-opts! opts #{:match :case-sensitive? :limit} "find-terms")
   ;; then the `:match`-style value refusal: a known key holding a value it cannot
   ;; mean.  Unchecked, a string limit reaches `take` and raises a bare cast error —
   ;; over the daemon's `:find-terms` op, a 500 with no `:type` on it.  An explicit
   ;; nil is no limit, which the `if-let` below already reads it as.
   (when-some [n (:limit opts)]
     (check-limit! n "find-terms :limit"))
   (let [match? (term-matcher q opts)
         hits   (filter #(match? (str %)) (reads/stored-terms-global (:index kb)))]
     (if-let [n (:limit opts)]
       (smallest-n n hits)
       (vec (sort hits))))))

;; ---- secondary roots: extent + cardinality from the other directions ----
;; The trie is ordered [pred args… ctx] and narrows only left-to-right, so it can
;; count "predicate P" but not "context C" or "X in argument position 2".

(defn- records-of
  "The records behind `handles`, **lazily**: the handle set is read now, each record is
  fetched as the seq is walked, and a handle whose record has gone by then is skipped.

  Lazy on purpose, and the three extent readers below hand this seq back as it is.  A
  root on an imported ontology runs to a hundred thousand records (`comment` alone,
  on OpenCyc), and the browser shows fifty of them a page: a reader that fetched every
  record to answer `(take 50 …)` would turn each page into a full walk of the root.
  The price is that the seq reads **live** state — hold it across a write and what it
  yields is what is stored when it is walked, not when it was asked for.  A caller that
  wants a snapshot takes one with `vec`, and the daemon's wire does so for every
  remote reader (`serve`'s `wire-safe`)."
  [kb handles]
  (->> handles (map #(p/get-sentex (:records kb) %)) (filter some?)))

;; ## Stored vs believed — read this before comparing an extent with a count
;;
;; The three `count-*` readers read set cardinalities: no records fetched, no belief
;; consulted.  Two are one read outright — `count-in-context` and `count-with-functor`
;; each size a single posting — and `count-with-arg` is one read *per predicate holding
;; the term at that position*, since the argument postings are scoped by predicate: it
;; reads the slot predicate set and sums a cardinality over it, which is one key in the
;; overwhelmingly common case and a handful otherwise.  That is the whole point of the
;; secondary roots, and it is why none of them touches the extent.  The price is that
;; they count what is **stored**, which includes a sentex the JTMS currently holds
;; OUT — a defeated default, or a conclusion whose support was withdrawn.  Such a
;; sentex is retained on purpose (it can be revived), so it is real storage, just not
;; current belief.
;;
;; `sentexes-matching` and `types-of`, by contrast, filter belief.  So
;; `(count (sentexes-matching ...))` and `(count-with-functor ...)` can legitimately
;; disagree, and neither is wrong.
;;
;; The extent fns bridge the two: each takes an optional `{:believed? true}`, which
;; costs a record fetch plus a TMS lookup **per handle** — O(n) in the extent.  There
;; is no O(1) believed count and this API does not pretend otherwise: a believed
;; count is `(count (sentexes-in-context kb ctx {:believed? true}))`, and it is O(n).

(def ^:private extent-opt-keys
  "Every key the extent readers (`sentexes-in-context` / `sentexes-with-functor` /
  `sentexes-with-arg`) read."
  #{:believed?})

(defn- check-extent-opts!
  "Refuse an opts key the extent readers do not read, and a non-nil non-map `opts` —
  `check-assert-opts!`'s reasoning at these entry points.  The one option is the belief
  filter, so the silent-default failure is the filter silently *off*: `{:believed
  true}` reads as no key at all and the stored extent comes back whole, defeated
  defaults included, indistinguishable from a believed extent that happens to have
  nothing defeated in it."
  [opts fn-name]
  (opts/check! opts extent-opt-keys fn-name
               (str "An option nothing reads takes the default in silence, which here"
                    " means the stored extent — defeated defaults included — where the"
                    " believed one was asked for."))
  ;; and the value: `:believed?` is a boolean, so `{:believed? \"yes\"}` — which
  ;; `believed-filter` reads as truthy — is refused rather than silently answering the
  ;; believed extent under a value that only looks like `true` (`opts/bound-domains`)
  (opts/check-values! opts fn-name))

(defn- believed-filter
  "Apply the extent fns' `{:believed? true}` option: keep only sentexes believed as their
  own context reads them (`res/believed-at?`) — IN in the network, and not withdrawn from
  that context by a scoped defeat.  O(n) in the extent — the caller opted into it."
  [kb opts sentexes]
  (if (:believed? opts)
    (filter #(res/believed-at? kb (:id %) (:context %)) sentexes)
    sentexes))

(defn sentexes-in-context
  "Every **stored** sentex asserted in `context` (its extent, rules included) — a
  defeated or unsupported one included.  Pass `{:believed? true}` to keep only what
  the JTMS currently believes; that costs a TMS lookup per handle (O(n)), unlike the
  unfiltered read.  An opts key this fn does not read is refused (`:unknown-option`),
  so a misspelt filter never silently answers the stored extent.

  **A lazy seq over live state**, as the other two extent readers are: the handles are
  read now and each record is fetched as the seq is walked, so `(take 50 …)` costs fifty
  fetches however large the context — and a seq held across a write yields what is
  stored when it is walked.  `vec` it for a snapshot."
  ([kb context] (sentexes-in-context kb context nil))
  ([kb context opts]
   (check-extent-opts! opts "sentexes-in-context")
   (believed-filter kb opts (records-of kb (reads/as-stored-in-context (:index kb) context)))))

(defn count-in-context
  "How many sentexes are **stored** in `context` — one set-size read, O(1), nothing fetched.

  Counts stored-not-believed sentexes too (a defeated default still occupies the
  context), so this can exceed `(count (sentexes-matching kb pattern context))`, which filters
  belief.  For the believed count use
  `(count (sentexes-in-context kb context {:believed? true}))` — necessarily O(n),
  since belief lives in the TMS and not in the index."
  [kb context] (reads/stored-count-in-context (:index kb) context))

(defn sentexes-with-functor
  "Every **stored** fact sentex whose functor is `pred`, any arity, either polarity —
  a defeated or unsupported one included.  Pass `{:believed? true}` to keep only what
  the JTMS believes (O(n) in the extent).  An opts key this fn does not read is
  refused (`:unknown-option`).  A lazy seq over live state, as `sentexes-in-context`
  is — `vec` it for a snapshot."
  ([kb pred] (sentexes-with-functor kb pred nil))
  ([kb pred opts]
   (check-extent-opts! opts "sentexes-with-functor")
   (believed-filter kb opts (records-of kb (reads/as-stored-with-functor (:index kb) pred)))))

(defn count-with-functor
  "How many fact sentexes with functor `pred` are **stored** — one set-size read, O(1).

  Counts stored-not-believed sentexes too, so it can exceed
  `(count (sentexes-matching kb (list pred ...) '?ctx))`.  The believed count is
  `(count (sentexes-with-functor kb pred {:believed? true}))` and is O(n)."
  [kb pred] (reads/stored-count-with-functor (:index kb) pred))

(defn stored-first-args
  "The terms **stored** at argument 1 of a fact with functor `pred`, as a set: the index's
  own child set under `pred`, one read — no record fetched and no belief consulted, so a
  defeated or unsupported fact's term is in it.  For a type, its members without its
  extent: a type with a hundred thousand members answers in milliseconds, where
  `sentexes-with-functor` fetches a hundred thousand records.  A caller that needs belief
  checks the terms it keeps (`types-of`)."
  [kb pred] (set (reads/as-stored-children (:index kb) [pred])))

(defn sentexes-with-arg
  "Every **stored** fact sentex holding `term` at 1-based argument position `pos` —
  a defeated or unsupported one included.  Pass `{:believed? true}` to keep only what
  the JTMS believes (O(n) in the extent).  An opts key this fn does not read is
  refused (`:unknown-option`).  A lazy seq over live state, as `sentexes-in-context`
  is — `vec` it for a snapshot."
  ([kb pos term] (sentexes-with-arg kb pos term nil))
  ([kb pos term opts]
   (check-extent-opts! opts "sentexes-with-arg")
   (believed-filter kb opts (records-of kb (reads/as-stored-with-arg-global (:index kb) pos term)))))

(defn count-with-arg
  "How many fact sentexes hold `term` at argument position `pos`, as **stored** — cheap,
  one O(1) set-size read per predicate declaring an argument at that slot.

  Counts stored-not-believed sentexes too.  The believed count is
  `(count (sentexes-with-arg kb pos term {:believed? true}))` and is O(n)."
  [kb pos term] (reads/stored-count-with-arg-global (:index kb) pos term))

(defn types-of
  "The types asserted of individual `x` — functors of unary sentexes (T x), found
  via the term index.  Scoped to memberships visible from `context` (default:
  any context)."
  ([kb x] (kb/types-of kb x))
  ([kb x context] (kb/types-of kb x context)))

(defn disjoint?
  "Are types `a` and `b` provably disjoint (via disjoint declarations, closed
  under genl)?  With a `context`, only declarations and genl edges visible from
  it count — the vantage every definitional check now judges from.

  The 3-arity reads every declaration and edge the taxonomy holds, including one a
  `defeat` or an `except` hides from every reader: the KB-wide reading."
  ([kb a b] (kb/disjoint? kb a b))
  ([kb a b context] (kb/disjoint? kb a b context)))

(defn term-role
  "The naming role of `term`, for display / classification — one of `:variable` (`?x`),
  `:number`, `:lexeme`, `:context`, `:individual`, `:predicate`, `:sense`, `:type`, or
  nil (a string, or a symbol matching no convention).  Reads the naming invariants
  (`vaelii.impl.naming`) that `assert` enforces, so a caller — a UI coloring a term, a
  tool grouping one — can classify it by the same rules the engine validates by.

  Decided most-specific first.  `:lexeme` is first because a namespace decides it
  outright and the name half is not ours to read; a context name is also CapitalCamel, so
  `:context` wins over `:individual`; and a sense is a type, so `:sense` is reported
  before the `:type` it is a kind of."
  [term]
  (cond
    (sx/variable? term)    :variable
    (number? term)         :number
    (not (symbol? term))   nil
    (nm/lexeme? term)      :lexeme
    (nm/context? term)     :context
    (nm/individual? term)  :individual
    (nm/predicate? term)   :predicate
    (nm/sense? term)       :sense
    (nm/type-symbol? term) :type
    :else                  nil))

(defn indexable-terms
  "The distinct terms that make `sentex` findable — the indexable subterms of its
  connective-free content (numbers, strings, and variables dropped).  These are exactly
  the keys of the inverted term index this sentex is posted under.

  Every name it mentions is here.  A ground *compound* subterm is here when it sits
  between `sentex/*min-indexed-depth*` and `sentex/max-indexed-compound` — outside those
  bounds `find-sentexes` still returns this sentex for it, narrowing on the atoms and
  verifying against the record rather than reading a key."
  [sentex]
  (sx/index-terms sentex))

(defn negative?
  "Is `sentex` a negative literal — a sentex whose sentence is `(not S)`?  Canonical form
  leaves at most one `not`, at the head, so the head decides it.  False for a rule, which
  holds no sentence.  Reads `:sentence` alone, so it answers the same for a record and for
  the map a daemon sends in its place."
  [sentex]
  (sx/negative? sentex))

(defn rests-on
  "Every handle justification `j` needs believed to be valid: its antecedents, plus its
  informant when the informant is a rule handle.  A pure read of the map `justification`
  returns, so a caller asking which of a justification's supports are OUT, or which
  justifications a retraction would take down, reads the same set the JTMS reads."
  [j]
  (jtms/rests-on j))

(def query-contexts
  "The **query contexts**, as a set: `CxEverything`, `CxInference` and `CxNothing`, each
  a reading mode spelled as a context rather than a context a sentex can be stored in.  A
  write given one is refused.  A set is a predicate, so `(query-contexts x)` asks whether
  `x` is one.  [docs/contexts.md](docs/contexts.md)"
  nm/query-contexts)

(def assertable-strengths
  "The strengths `assert` accepts in `{:strength s}`, as a set: `:monotonic` and
  `:default`.  `assert` refuses any other value against this set, so a form offering a
  strength control refuses the same values by calling `(assertable-strengths s)`."
  strength/assertable)

(defn reified-term?
  "Is `term` a **reified non-atomic term** — the opaque constant a ground `(F a…)`
  under a `reifiable_function` was minted as (docs/nat.md)?  A pure test on the
  symbol's reserved namespace, so a display layer can ask it of every term it renders
  and pay a read only where the answer is true.  `term-expression` is what to render
  in its place."
  [term]
  (nat-read/reified-nat-symbol? term))

(defn term-expression
  "The functional expression a reified term denotes — `(FruitFn AppleTree)` for the
  constant minted from it — or nil for an ordinary term, and for a reified one whose
  `(natFormula K E)` map is not believed.

  One hop: an argument that is itself a reified term comes back as its constant
  (docs/nat.md, Display / export).  One index read per call."
  [kb term]
  (nat/nat-expression kb term))

;; ---- the taxonomy, read ------------------------------------------------
;; The cached genl / genlCx closures and the predicate metadata are derived
;; state the whole engine reasons from, so reading them is part of the public
;; surface — a KB nobody can ask "what is a dog?" is not introspectable.  These are
;; thin delegations to `vaelii.impl.taxonomy`; the closures are in-memory sets, so
;; every one of them is a map lookup.
;;
;; Reads only.  Edges and metadata are *maintained* by `assert` / `retract!` from
;; the sentexes that state them — there is deliberately no public mutator, because
;; an edge added behind the KB's back would have no supporter, no belief, and no way
;; back out.

(defn genls
  "The supertypes of type `t`, reflexively — `t` itself plus everything reachable
  from it by `genl`.  A set; `#{t}` when `t` is not a node in the type hierarchy.
  With a `context`, only edges visible from it are walked (docs/taxonomy.md).

  The 2-arity reads every edge the taxonomy holds, including one a `defeat` or an
  `except` hides from every reader: the KB-wide reading."
  ([kb t] (tax/genls-global (reasoning/taxonomy kb) t))
  ([kb t context] (tax/genls (reasoning/taxonomy kb) t context)))

(defn specs
  "The subtypes of type `t`, reflexively — `t` itself plus everything that reaches
  it by `genl`.  A set; `#{t}` when `t` is not a node in the type hierarchy.  This
  is the fan-out that lets an antecedent `(animal ?x)` match a stored `(dog Muffet)`.
  With a `context`, only edges visible from it are walked.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb t] (tax/specs-global (reasoning/taxonomy kb) t))
  ([kb t context] (tax/specs (reasoning/taxonomy kb) t context)))

(defn direct-genls
  "The types `t` is a subtype of by **one** `genl` edge in the closure — its direct
  parents, where `genls` is everything they reach.  Not reflexive.  An edge counts
  whatever installed it: a stated `(genl t super)`, or a `covering`, `separating` or
  `partition` declaration naming `t` as a part of `super`.  O(degree).  A set; `#{}` when
  `t` is not a node in the type hierarchy.  With a `context`, only edges visible from it
  count.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb t] (tax/direct-genls-global (reasoning/taxonomy kb) t))
  ([kb t context] (tax/direct-genls (reasoning/taxonomy kb) t context)))

(defn direct-specs
  "The types that are a subtype of `t` by **one** `genl` edge in the closure — its
  direct children.  `direct-genls`, the other direction.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb t] (tax/direct-specs-global (reasoning/taxonomy kb) t))
  ([kb t context] (tax/direct-specs (reasoning/taxonomy kb) t context)))

(defn min-genls
  "The **minimal** supertypes of type `t`: its direct parents (`direct-genls`) with no
  other direct parent of `t` strictly below them.  Every other strict supertype of `t` is
  a supertype of one of these, so the set is `t`'s position in the subsumption order read
  from below.  The read is over every believed edge, whatever installed it: a stated
  `(genl dog animal)` beside `dog ⊂ mammal ⊂ animal` leaves `animal` out, and a parent
  only an `intersection` or a cover declaration gives is a member.  Two parents that subsume
  each other are both members.  Not reflexive.  One memoized closure read per direct
  parent.  A set; `#{}` when `t` is not a node in the type hierarchy.  With a `context`,
  only edges visible from it count.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb t] (tax/min-genls-global (reasoning/taxonomy kb) t))
  ([kb t context] (tax/min-genls (reasoning/taxonomy kb) t context)))

(defn max-specs
  "The **maximal** subtypes of type `t`: its direct children (`direct-specs`) with no
  other direct child of `t` strictly above them.  `min-genls`, the other direction.  One
  memoized closure read per direct child, so the cost follows `t`'s own fan-out.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb t] (tax/max-specs-global (reasoning/taxonomy kb) t))
  ([kb t context] (tax/max-specs (reasoning/taxonomy kb) t context)))

(defn common-genls
  "The supertypes **every** type in `types` has, a collection of types: the intersection
  of their `genls`.  Reflexive, as `genls` is, so a member above all the others is in the
  set and one type's common genls are its `genls`.  One memoized closure read per distinct
  type.  A set; `#{}` for an empty `types`.  With a `context`, only edges visible from it
  count.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb types] (tax/common-genls-global (reasoning/taxonomy kb) types))
  ([kb types context] (tax/common-genls (reasoning/taxonomy kb) types context)))

(defn common-specs
  "The subtypes **every** type in `types` has: the intersection of their `specs`.
  Reflexive, as `specs` is.  `common-genls`, the other direction.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb types] (tax/common-specs-global (reasoning/taxonomy kb) types))
  ([kb types context] (tax/common-specs (reasoning/taxonomy kb) types context)))

(defn min-common-genls
  "The **minimal** common supertypes of `types`: the members of `common-genls` that are no
  member of `types` and have no other such member strictly below them.  Every type
  strictly above all of `types` is a supertype of one of these, so for `dog` and
  `cat` the set is where a new type above both would sit.  Not reflexive: for `dog`
  and `mammal` under `dog ⊂ mammal ⊂ animal` the set is `#{animal}`.  One distinct type
  gives `min-genls` of it, exactly.  A set.  With a `context`, only edges visible from it
  count.  `(minCommonGenl ?x t1 t2 …)` asks the same question as a query.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb types] (tax/min-common-genls-global (reasoning/taxonomy kb) types))
  ([kb types context] (tax/min-common-genls (reasoning/taxonomy kb) types context)))

(defn max-common-specs
  "The **maximal** common subtypes of `types`: the members of `common-specs` that are no
  member of `types` and have no other such member strictly above them.  One distinct type
  gives `max-specs` of it, exactly.  `min-common-genls`, the other direction, and
  `(maxCommonSpec ?x t1 t2 …)` as a query.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb types] (tax/max-common-specs-global (reasoning/taxonomy kb) types))
  ([kb types context] (tax/max-common-specs (reasoning/taxonomy kb) types context)))

(defn genl?
  "Is `sub` a (reflexive-transitive) subtype of `super`?  Types, not individuals —
  for an individual's type membership use `isa?`.  With a `context`, only edges
  visible from it count.

  The short arity reads the KB-wide edge set, as `genls`' does."
  ([kb sub super] (tax/genl?-global (reasoning/taxonomy kb) sub super))
  ([kb sub super context] (tax/genl? (reasoning/taxonomy kb) sub super context)))

(defn types
  "Every type currently in the genl hierarchy — the nodes of the closure, i.e. every
  type named by some believed `genl` edge. With a `context`, only a node touched by an
  edge visible from it counts — the same visibility `genl?` and `disjoint?` read with a
  `context`."
  ([kb] (tax/types (reasoning/taxonomy kb)))
  ([kb context] (tax/types (reasoning/taxonomy kb) context)))

(defn- scoped-read?
  "Does `context` name a place to scope a read by?  A variable and the three query
  contexts each read unscoped already, so only a concrete `Cx…` starts an ancestor set walk."
  [context]
  (and (symbol? context) (not (sx/variable? context)) (not (nm/query-context? context))))

(defn relation?
  "Is `term` a relation of two or more places by what the KB stores of it, visible from
  `context` (default `?ctx`, every context): an `(arity P n)` declaration or exact-arity
  class membership of two or more, or a `variable_arity` membership, or, where none of these
  answers, a length of two or more inherited through `genl`.  A `genl` edge between
  two relations puts both in `types`; such a node is a relation and not a type, and a node
  with an arity of one or none is a type.  No spelling is read.  docs/taxonomy.md."
  ([kb term] (relation? kb term '?ctx))
  ([kb term context] (kb/relation? kb term (when (scoped-read? context) context))))

(defn relation-arity
  "The exact number of places that binds `term`, its own or one inherited through `genl`,
  or nil when no exact length binds it (a `variable_arity` relation, or none stored).
  Read the same at every context.  docs/taxonomy.md, \"Arity\"."
  [kb term] (kb/relation-arity kb term))

(defn contexts
  "Every context currently in the genlCx hierarchy — the nodes of the closure."
  [kb] (tax/contexts (reasoning/taxonomy kb)))

(defn context-up
  "The contexts `c` inherits from, reflexively — `c` plus everything it *sees* via
  `genlCx`.  A sentex in any of these is visible from `c`."
  [kb c] (tax/context-up (reasoning/taxonomy kb) c))

(defn context-down
  "The contexts that inherit from `c`, reflexively — `c` plus every context that
  sees it."
  [kb c] (tax/context-down (reasoning/taxonomy kb) c))

(defn min-context-parents
  "The **minimal** contexts context `c` inherits from: the contexts `c` reaches over one
  `genlCx` edge with no other such context strictly below them.  Every other context
  `c` sees (`context-up`) is seen through one of these, so the set is `c`'s position in
  the context lattice read from below.  A stated `(genlCx CxLeaf CxTop)` beside
  `CxLeaf → CxMid → CxTop` leaves `CxTop` out.  Read as `context-up` reads: an edge an
  `except` hides from `c` is not walked.  Not reflexive.  One memoized closure read per
  direct parent.  A set; `#{}` when `c` is not a node in the context hierarchy."
  [kb c] (tax/min-context-parents (reasoning/taxonomy kb) c))

(defn max-context-children
  "The **maximal** contexts that inherit from context `c`: the contexts that reach `c`
  over one `genlCx` edge with no other such context strictly above them.
  `min-context-parents`, the other direction.  Read as `context-down` reads: while an
  `except` reaches a `genlCx` edge, a context is a member when `c` is one of its own
  `min-context-parents`."
  [kb c] (tax/max-context-children (reasoning/taxonomy kb) c))

(defn sees?
  "Does context `k` see assertions made in context `y`?  True iff `y` is in `k`'s
  genlCx up-closure (reflexively, so a context sees itself)."
  [kb k y] (tax/sees? (reasoning/taxonomy kb) k y))

(defn has-prop?
  "Does `pred` carry the metadata property `kind`?  The kinds are the ones the grammar's
  declarations maintain — `vaelii.impl.predicates/prop-kinds` enumerates them, and
  docs/api.md lists them: the relation algebra (`:transitive`, `:symmetric`,
  `:asymmetric`, `:reflexive`, `:functional`, `:irreflexive`, `:anti-symmetric`,
  `:anti-transitive`), the grants (`:decontextualized`, `:forced-decontextualized`,
  `:forced-monotonic`, `:abducible`, `:closed-extent`, `:modal`, `:target-following`),
  the function kinds (`:reifiable`, `:unreifiable`) and
  the `:declares-*` kinds naming a predicate as the subject of an argument constraint.
  Declared by the corresponding sentex, e.g. `(symmetric siblingOf)`.  A kind not in that
  list answers false for every term rather than being refused.

  A predicate carries every relation kind and grant; the function kinds are a
  *function*'s, declared by `(reifiable_function F)` and read by the reify pass
  (`vaelii.impl.nat`).

  Argument-position *preservation* is not here: `(transitiveInArg P n R)` is per
  position, so like `arg` it is an ordinary stored sentex read through
  `matches-visible` rather than a cached predicate property (`vaelii.impl.inherit`).

  With a `context`, the declaration must be visible from it — except `:symmetric` and
  `:commutative`, which sort a sentex's arguments and are read from every context, so a
  context answers whether it believes a statement, which a `defeat` or an `except` it
  sees takes away.  The two forced-monotonic kinds (`:forced-monotonic`,
  `:forced-between-predicates`) answer the baseline forced-monotonic set from every
  context, and a declaration in any context from the contexts that see it
  (docs/nmtms.md).

  The 3-arity reads the KB-wide declarations, as `disjoint?`'s does."
  ([kb kind pred]
   (if (decide/forced-kinds kind)
     (decide/forced-monotonic? (reasoning/taxonomy kb) kind pred)
     (tax/has-prop? (reasoning/taxonomy kb) kind pred)))
  ([kb kind pred context]
   (let [tax (reasoning/taxonomy kb)]
     (if (decide/forced-kinds kind)
       (or (decide/global? tax kind pred) (tax/has-prop? tax kind pred context))
       (tax/has-prop? tax kind pred context)))))

(defn props
  "The set of predicates carrying metadata property `kind` (see `has-prop?`).

  The KB-wide reading: every predicate a declaration the taxonomy holds marks,
  including one a `defeat` or an `except` hides from every reader; `has-prop?` with a
  context reads one reader's."
  [kb kind]
  (if (decide/forced-kinds kind)
    (decide/forced-predicates (reasoning/taxonomy kb) kind)
    (tax/props (reasoning/taxonomy kb) kind)))

(defn inverse-of
  "The predicate declared inverse to `pred` by an `(inverse P Q)` sentex, or nil.
  The relation is stored both ways, so `(inverse-of kb Q)` answers `P`.  With a
  `context`, the declaration must be visible from it.

  The 2-arity reads the KB-wide declarations, as `disjoint?`'s does."
  ([kb pred] (tax/inverse-of (reasoning/taxonomy kb) pred))
  ([kb pred context] (tax/inverse-of (reasoning/taxonomy kb) pred context)))

(defn disjoint-metatypes
  "The declared disjoint metatypes — each a type whose member types are pairwise
  disjoint by `(disjoint_metatype M)`.  The clique is *consulted*, not materialized: no
  `(disjoint a b)` pair is stored, so to render the induced pairs, take
  `metatype-members` of each and pair them yourself."
  [kb] (tax/disjoint-metatypes (reasoning/taxonomy kb)))

(defn metatype-members
  "The member types of disjoint metatype `m` — the set whose every pair `disjoint?`
  holds of, closed under genl."
  [kb m] (tax/metatype-members (reasoning/taxonomy kb) m))

(defn separating-covers
  "The believed `separating` and `partition` declarations, as a set of `[whole parts kind]`:
  every two distinct `parts` are disjoint, and `disjoint?` reads them from this table.
  Like a metatype's clique, the pairs are consulted, never stored as `(disjoint a b)`."
  [kb] (tax/separating-covers (reasoning/taxonomy kb)))

(defn covers-of
  "The believed `covering`, `separating` and `partition` sentexes whose whole is `whole`,
  in every context, as a set of `[kind parts]`: `kind` is `:covering`, `:separating` or
  `:partition`, and `parts` is the declared part vector, deduplicated and sorted by printed
  name.  A rule-concluded cover sentex counts as a stated one does; an `intersection`
  declares no part list and adds nothing.  One believed argument-root read per functor at
  position 1, so the cost follows `whole`'s own declarations."
  [kb whole]
  (into #{}
        (for [f    '[covering separating partition]
              h    (reads/believed-with-args kb f [[1 whole]])
              :let [[w parts] (some-> (p/get-sentex (:records kb) h) :sentence tax/cover-parts)]
              :when (= w whole)]
          [(keyword f) (vec (nm/by-print-key parts))])))

;; ---- what the engine does with its own grammar --------------------------
;; A declaration's shape says nothing about whether anything reads it: `(maxCardinality
;; parentOf 2)` is a well-formed ternary fact, storable and believed, and a KB author
;; gets the same silence from a constraint that is enforced and one that was never
;; implemented.  So the answer is published rather than left in `impl`.

(defn interpreted
  "What the engine does with vocabulary term `term`: `{:enforced \"where\"}`,
  `{:inert \"why\"}`, or nil.

  `:enforced` means a code path reads it and the KB refuses, derives, or answers
  differently because of it — the string names which path.  `:inert` means nothing does,
  and says why that is the intended answer rather than an omission (most are *derived*
  predicate types, which exist so a KB can be queried for what a mark implies; the checks
  read the mark).

  **Nil is not \"nothing reads it\".**  The question is asked of the engine's own grammar
  — the terms core.txt comments — so an ordinary domain predicate is simply not in
  scope.  `vocabulary-audit` classifies every declared term, and reports one this leaves
  unclassified."
  [term] (vocab/classify term))

(defn vocabulary-audit
  "Every term core.txt comments in `kb`, classified — `{:enforced [[term why] …]
  :inert [[term why] …] :unclassified [term …] :retired [term …] :contradicted [term
  …]}`.

  `:unclassified` is the finding this exists to surface: a declaration that landed in the
  grammar without anybody deciding whether the engine reads it.  `:retired` is the mirror,
  a claim about a term the KB no longer declares.  `:contradicted` needs no judgement at
  all — a term the special-predicate table gives an arm to and the classification table
  calls inert.

  Empty in all three on the shipped ontology, and a test holds it there."
  [kb] (vocab/audit kb))

;; ---- the knowledge, as against the engine -------------------------------
;; `settle-stats`, `chain-stats` and `violations` all report on a *run*: how many
;; iterations, how many conclusions, what was dropped.  None of them is a reading about
;; the KB, so an author of a large one has no answer to "is any of this any good" — and
;; the seven questions below are the ones they actually ask.

(defn kb-quality
  "Seven readings about the **knowledge** — one map, seven keys, each a distribution rather
  than a number:

    :rules     {:total n :never [{:handle :sentence :context} …] :never-count n
                :all-defeated […] :all-defeated-count n :fired n :firings n :truncated? b}
               ; :firings is every recorded firing in the KB, the defeated ones included —
               ; not the live rules' share of them
    :extents   {:predicates n :with-extent n :stored n :gini d :buckets {k n}
                :heaviest [[pred n] …]}
    :chains    {:functors n :components n :cyclic n :largest n :rules n
                :depths {depth n} :at-least {depth fraction}}
    :taxonomy  {:names n :edged n :root term :rooted n :islands n}
    :declarations {:total n :stranded-count n :truncated? b
                   :stranded [{:handle :sentence :context :predicate :position
                               :arity :via :message} …]
                   :typed-thing-count n
                   :typed-thing [{:handle :sentence :context :facts} …]}
               ; argument constraints naming a position their predicate does not have.
               ; :message is the one the check itself wrote, so this map and
               ; `try-assert`'s refusal say the same thing in the same words.  :typed-thing lists the
               ; declarations typing a position `thing`, which mint nothing, each with
               ; its predicate's stored extent
    :subsumption {:total n :subsumed-count n :truncated? b
                  :subsumed [{:subsumed h2 :by h1 :substitution σ :context C
                              :sentence :by-sentence} …]}
               ; rules another stored rule already covers — h1 fires wherever h2 does and
               ; concludes at least as much, under σ
    :clashes  {:total n :pair-count n :truncated? b
               :pairs [{:rules [h1 h2] :kind :negation|:disjoint|:functional|:asymmetric
                        :unifier σ :context C :excepted b :sentences [s1 s2]} …]}
               ; rule pairs that would contradict each other if both fired. :excepted
               ; marks the intended shape — one of the two carries an `exceptWhen`
               ; naming the other's case, so the clash is already stated

  Data, not a printer: `quality-report` renders this same map, so nothing can print a
  figure the data does not hold.  **This is not a required check either**: a threshold
  on somebody's ontology is not a build failure.

  **Three keys count `kb-integrity` findings.**  `:taxonomy`, `:declarations` and
  `:clashes` are `vaelii.impl.integrity`'s `taxonomy-coverage`, `stranded-declarations` and
  `clash-pairs` read over the whole KB — the checks behind kb-integrity's
  `:taxonomy-island`, `:stranded-declaration`, `:rule-clash` and `:rule-clash-review`
  categories, which are where a caller wanting a verdict reads them (docs/integrity.md).
  A stranded declaration constrains nothing, refuses nothing and mints nothing, and reads
  the same an hour later, which is why it is a sweep question and not a `violations`
  entry; a wrong-length **fact** is a nogood the settle places (docs/taxonomy.md).

  `opts`: `:limit` caps each listed set (default 25 — the counts are the headline, and a
  30,000-entry list is not one); `:on-progress` is called with `{:phase :done :total}` as
  each phase advances and may **throw to cancel**, the reading being of current state so a
  half-finished one is discarded rather than repaired.  An unknown option is refused
  (`:unknown-option`), like every other bound on a run.

  **`:subsumption` and `:clashes` are static analysis of the rules**, and the only two
  readings here that are: no inference is run, no fact is consulted, and belief is read of
  the *declarations* they consult (`genl`, `disjoint`, `functional`, `asymmetric`) rather
  than of the rules themselves — a rule the KB currently disbelieves is still a rule
  somebody wrote.  A `:clashes` pair is a contradiction that *could* form and not one that
  has: a clash already formed is in `(contradictions kb)`.  Neither reading judges intent —
  a covered rule may be a deliberate specialization, and a clash marked `:excepted` is the
  shape a stated exception has — so both name the pair and leave the reading to the reader.

  Three things to know before comparing the numbers with anything:

  - **A firing is a *currently supported* one.**  The census reads live justifications, so
    a rule that fired and whose conclusion was then retracted has none and counts as never
    fired.  Firings-ever is a different question and nothing here answers it.
  - **\"Fired, every conclusion defeated\" is its own category**, and the more interesting
    one: such a rule runs, contributes nothing, and would read as working from a firing
    count alone.
  - **Extents are counts of what is stored** (`count-with-functor`, O(1) each), never of
    what is believed — a believed extent is O(n) per predicate, which would turn an
    O(predicates) report into an O(sentexes) one.

  Rules are enumerated from the rule index, so a rule the index cannot key by any
  predicate — an `:inert` one written with a variable functor throughout — is outside the
  census.  Cost is
  `O(terms + rules + firings + genl edges + declarations × super-predicates
  + candidate rule pairs)`: the **vocabulary and the rule set**, walked once each, and
  never the KB.  Two terms are not flat — a declaration whose predicate inherits its
  length costs a read per predicate above it, where one carrying its own costs a map read,
  and the two rule-hygiene readings cost a record read per rule and a unification per
  candidate pair — and `vaelii.impl.quality` and `vaelii.impl.integrity` say how.

  **Read without a snapshot**, like every other reader here: a write landing mid-report can
  leave a count and a list disagreeing by one (a rule enumerated and then retracted is
  dropped from the listed set and stays in the total).  A reading of a moving KB, not a
  transaction over a still one."
  ([kb] (kb-quality kb nil))
  ([kb opts]
   (check-bound-opts! opts #{:limit :on-progress} "kb-quality")
   (when-some [n (:limit opts)]
     (check-limit! n "kb-quality :limit"))
   ;; `:on-progress` is a function, so a non-fn one is a bare cast on the first phase
   ;; report — refused here as `:unknown-option` (`opts/bound-domains`).  `:limit` is not
   ;; in that table; `check-limit!` above owns it
   (opts/check-values! opts "kb-quality")
   (quality/census kb opts)))

(defn quality-report
  "A `kb-quality` map as Markdown — the counts first and the capped lists after.  Takes the
  **map**, not the KB, so a caller reports on a reading it already holds (and a stored one
  renders the same a year later).

  A map that is not one of `kb-quality`'s answers is refused (`:not-a-report`).  The
  alternative is a page of zeros and dashes, which is a report a caller who passed the
  wrong map has no way to tell from a report of an empty KB."
  [quality] (quality/report quality))

;; ---- the equality closure, read -----------------------------------------
;; docs/equality.md, "Public surface".

(defn representative
  "The term standing for `term`'s equivalence class — `term` itself when nothing has
  merged it, so this is total and never nil.

  With a `context`, only the merges that context inherits count, and the answer is its
  own election over them, since an invisible edge can split a class
  (docs/equality.md, \"Scope, context, and re-election\")."
  ([kb term] (tax/representative (reasoning/taxonomy kb) term))
  ([kb term context]
   (res/representative-in kb (res/visible-supporter-fn kb context) term)))

(defn same-class?
  "Do `a` and `b` denote the same thing?  Distinct symbols denote distinct individuals
  until an equality sentex says otherwise.  Scoped by `context` like `representative`.

  **Not the complement of a provable `(different a b)`.**  Both read false of an unmerged
  `indeterminate_term` — a skolem constant, or a member of a kind declared indeterminate —
  because the unique-name assumption is suspended for one and no merge has identified it
  either ([predall.md](../docs/predall.md)).  A caller wanting *provably different* asks
  `(different a b)` and reads that answer; `(not (same-class? …))` answers the weaker
  *not known to be the same thing*."
  ([kb a b] (tax/same-class? (reasoning/taxonomy kb) a b))
  ([kb a b context] (= (representative kb a context) (representative kb b context))))

(defn equiv-class
  "Every term known equal to `term`, itself included.  `#{term}` when nothing has
  merged it — an unseen term is its own singleton class.  Scoped by `context` like
  `representative`."
  ([kb term] (tax/equiv-class (reasoning/taxonomy kb) term))
  ([kb term context]
   (if-let [vis (and (tax/merged? (reasoning/taxonomy kb) term)
                     (res/visible-supporter-fn kb context))]
     (first (tax/scoped-class (reasoning/taxonomy kb) term vis))
     (tax/equiv-class (reasoning/taxonomy kb) term))))

(defn deprecated?
  "Did a believed `rewriteOf` name `term` the dispreferred side?  False for a `sameAs`
  or `equals` member: those merge without retiring either name.  Scoped by `context`
  like `representative` — a retirement holds where it is visible, so a context outside
  the `rewriteOf`'s ancestor set is told nothing and keeps the name."
  ([kb term] (tax/deprecated? (reasoning/taxonomy kb) term))
  ([kb term context]
   (tax/deprecated? (reasoning/taxonomy kb) term (res/visible-supporter-fn kb context))))

;; ---- public API ---------------------------------------------------------

;; `*defer-settle?*` is referred from `vaelii.impl.wiring`, which is where the write path
;; and the layers below it both reach it: `skolem` binds it around a mid-fixpoint mint,
;; and the assert path here reads it to decide whether to settle.

(def ^:dynamic *bulk-load?*
  "When true, the `assert` path runs in **bulk-load mode**: for a caller-guaranteed
  well-formed, DISTINCT premise load (a corpus import, the bench wload/w8x/w5x setup),
  the per-fact machinery that only *validates* or *dedups* is turned off, since the
  caller has already guaranteed what it checks.  Specifically, `assert-one` skips:

  - the definitional checks (`nm/problems` naming, `check-ground`, `wff-problems`,
    `check-edge-stratified`, `constraint-checks` — the last of which runs a LIVE
    `(arg pred ?n ?type)` store query on *every* fact, the dominant per-fact cost);
  - the `find-sentex-handle` dedup trie-walk — a distinct corpus creates one sentex per
    fact regardless, so the probe is guaranteed to miss;
  - provenance recording (`record-provenance!`) — belief never reads provenance, so a
    bulk premise carries none.

  It stores, indexes and believes the same sentex for the same fact, with one exception:
  no argument-type entailment is drawn, neither the fact's own nor what a declaration, a
  `genl` edge or a `genlCx` edge draws over the stored facts (docs/argtypes.md).
  `record-arg-types` records them afterwards, and a KB loaded this way answers as a
  per-fact load does once it has run.  A write the caller's bound or a refusal ends
  throws and rolls back as it does outside bulk mode (`undoing-refusal`).  Bind it only
  around a load whose facts are known well-formed and pairwise distinct; normal `assert`
  (the default) keeps every guarantee.  Pair it with `with-deferred-settle` (one settle
  at the end) and `{:chain? false}` for the full fast path — `bulk-assert-facts!` does
  all three."
  false)

;; ---- writing into a KB whose derived state was never built ---------------

(def ^:dynamic *write-unrecovered?*
  "Accept writes into a KB opened over a store whose derived state was never built —
  `{:recover? false}` or `:warn` over a populated store, or an `import-dump` with
  `:belief? false` / `:belief? :stored`.  False by default, which **refuses** them
  (`:type :unrecovered-kb`); the repair is `recover`, or `reindex` when the index is
  derived and so opened empty.

  Refusal rather than the naming check's store-it-and-warn, because the two failures do
  not cost the same.  A write into an unrecovered KB is wrong in ways nothing later
  catches:

  - **Every definitional check passes vacuously.**  All ten arms of the constraint
    check read `kb/memberships` and `checks/declaration-reader`, both of which filter on
    `jtms/in?`; with no nodes there are no types and no declarations, so arity, arg,
    genlArg, interArg, declaration-consistency, disjointness, functionality and
    asymmetry all match nothing and the assert lands.  Nothing re-runs them: `recover`
    does not, and its closing settle binds `settle/*rebuilding?*`, which turns the
    settle's reports off.  A store can accumulate content its own constraints forbid,
    indefinitely, with every instrument green.
  - **Two writes land under the wrong key.**  `res/kb-sentex` sorts a symmetric
    predicate's arguments only when the taxonomy says the predicate is symmetric, and a
    commutative one's only when it says which positions commute, so `(siblingOf Bob Ann)`
    is stored where a recovered KB writes `(siblingOf Ann Bob)`; and a
    `:forced-decontextualized` predicate lands in the caller's context instead of
    `CxUniverse`.
  - **On a derived index, dedup misses everything.**  `assert` dedups through
    `kb/find-sentex-handle`, so every assert mints a fresh handle for a sentence already
    stored — and `reindex` cannot merge the two, because they are two records.

  A naming violation is recoverable; an un-canonicalized duplicate is not.  So this is
  the opt that names what it gives up, and binding it says the caller has read the list.
  It does **not** cover a `retract!` whose dependency sweep cannot be computed — that
  one is refused whatever this says, since its result is not merely risky but unknown
  (`:type :unrecovered-premise`).  Nor does it cover a KB whose belief is being rebuilt
  behind an installed image (`:stale-belief`, `:recover? :background`): a write there is
  checked against the earlier build's belief, and the rebuilt belief that replaces it may
  not include the write.  `*bulk-load?*` is deliberately not this opt: it skips
  the very dedup walk that is already missing, which would turn the duplicate risk into
  a certainty."
  false)

(defn- writable-problem
  "The refusal a write into this KB earns, as a value, or nil when there is none.  One
  statement of the policy, read by every write entry point — `assert`, `assert-inert`,
  `retract!`, `edit!` and `preview` — so no entry point can hold a different one, and a value
  rather than a throw so the same words serve the accept-anyway warning."
  [kb where]
  (when-let [hz (seq (kb/write-hazards kb))]
    (let [hz      (into {} hz)
          index?  (:no-index hz)
          belief? (:no-belief hz)]
      (if (:stale-belief hz)
        {:type :unrecovered-kb
         :hazards (vec (sort (keys hz)))
         :operation where
         :repair 'recover
         :message
         (str where " into a KB whose belief is being rebuilt: the open installed the belief"
              " image an earlier engine build wrote, and a rebuild under this build replaces"
              " it when it finishes.  A write now would be checked against the earlier"
              " build's belief, and the rebuilt belief might not include it.  Retry once"
              " (write-hazards kb) answers {}, or call (recover kb) to finish the rebuild on"
              " this thread.")}
        {:type :unrecovered-kb
         :hazards (vec (sort (keys hz)))
         :operation where
         :repair (if index? 'reindex 'recover)
         :message
         ;; each hazard names itself: `recover` over a derived-index KB clears `:no-belief`
         ;; and leaves `:no-index`, which is the documented halfway state, and a message
         ;; still saying "belief and index" there names a repair that has already been run
         (str where " into a KB whose "
              (cond (and belief? index?) "belief and index were"
                    index?               "index was"
                    :else                "belief was")
              " never built over the store it opened: "
              (str/join "; "
                        (cond-> []
                          (:no-belief hz)
                          (conj (str "the TMS is empty, so every definitional check "
                                     "passes vacuously and nothing later re-runs them"))
                          index?
                          (conj (str "the derived index is empty, so dedup misses and "
                                     "every assert mints a second handle for a sentence "
                                     "already stored"))))
              ".  Call " (if index? "(reindex kb)" "(recover kb)")
              " first, or bind vaelii.core/*write-unrecovered?* to accept the write"
              " unchecked — its docstring lists what that gives up.")}))))

(defn- unrecovered-problems
  "`writable-problem` as `check` reports problems, or nil — the reading half of the
  unrecovered-KB check below.  `check` answers \"would `assert` succeed, and if not
  why\", so a refusal the entry point makes before any other is a problem the report has
  to carry, or a caller validating a batch is told every line is fine and then refused on
  the first one.

  Nil under `*write-unrecovered?*`, since `assert` lands the write there and `check`
  answers about `assert` rather than about the KB — except for `:stale-belief`, which the
  opt does not cover."
  [kb where]
  (when-let [p (writable-problem kb where)]
    (when (or (not *write-unrecovered?*) (some #{:stale-belief} (:hazards p)))
      [p])))

(defn- check-writable!
  "The write entry points' one check: refuse an unrecovered KB by name, or — under
  `*write-unrecovered?*` — let the write through and say **once per KB** what it gave
  up.  Once, because the caller who bound the var has already read the list and a line
  per assert would bury the corpus load it was bound for.

  The hazard is read before the problem is built, and that ordering is the whole cost of
  the opt on the path it exists for: `writable-problem` assembles a `str/join`ed sentence
  and a map, and under the opt every accepted write threw both away.  The opt is
  documented for corpus-scale loads, where that is one allocation per record.  So the
  cheap question — is there a hazard at all — is asked first, and the expensive one only
  where it is going to be said or thrown."
  [kb where]
  ;; A hazard standing over an *empty* store is retired here rather than refused: this is
  ;; the write that starts filling it, so the network it builds is this KB's own.  The
  ;; importer never reaches this entry point — it writes at the dump's own handles, around the
  ;; assert path — which is what keeps its declaration standing for the whole load.
  (kb/discharge-over-empty-store! kb)
  (when-let [hz (not-empty (kb/write-hazards kb))]
    (if (and *write-unrecovered?* (not (:stale-belief hz)))
      ;; `announce-once!` before the message, for the same reason: it is a CAS per write
      ;; either way, but the sentence is built only for the one write that prints it
      (when (kb/announce-once! kb)
        (let [p (writable-problem kb where)]
          (trove/log! {:level :warn :id ::unrecovered-writes-accepted
                       :msg (str "*write-unrecovered?* is bound, so this KB accepts writes"
                                 " its own state cannot check: " (:message p))
                       :data (dissoc p :message)})))
      (let [p (writable-problem kb where)]
        (throw (ex-info (:message p) (dissoc p :message)))))))

;; Rule assertion is *idempotent* (first-writer-wins on direction / defeasibility):
;; if the α-equivalent rule already exists, its indexing and firing are untouched, so
;; re-asserting the same rule with a different direction can't union its index entries
;; and re-marking it default can't leave a stale non-defeasible justification.  To change a rule's
;; direction or defeasibility, retract it first.

;; ---- provenance ---------------------------------------------------------
;; A per-handle bookkeeping map (creator + creation date, plus whatever an
;; application adds) kept beside the record, never as fields on it (see
;; protocols/RecordStore).  Belief never reads it, so a wall-clock `:created` cannot
;; affect order independence.

(def ^:dynamic *creator*
  "The creator `assert` records in a sentex's provenance when opts carries no
  `:creator`.  nil by default; bind it per session / import / user."
  nil)

(def ^:dynamic *clock*
  "A 0-arg fn returning the `:created` time `assert` records (epoch milliseconds by
  default).  Bind it in tests to fix the value; belief never reads provenance, so a
  wall-clock default does not touch order independence."
  (fn [] (System/currentTimeMillis)))

(defn- record-provenance!
  "Record creation provenance for the handle(s) `assert` produced.  First-writer-wins
  on `:creator` / `:created` — a re-asserted sentex keeps its original values — while
  an application's extra `:provenance` fields are merged in on any assert.  Called
  once per public `assert`, so derived and lifted sentexes (which never go through it)
  carry no creation provenance."
  [kb handle-or-vec opts]
  (when-not *bulk-load?*                                ; a bulk premise carries no provenance
    (let [rec     (:records kb)
          creator (get opts :creator *creator*)
          extras  (:provenance opts)
          now     (delay (*clock*))]                     ; ticks only if a new handle needs it
      (doseq [h (if (sequential? handle-or-vec) handle-or-vec [handle-or-vec])
              :when (integer? h)]
        (let [cur (p/get-provenance rec h)]
          (cond
            ;; the store's own entry does not count: it may have written the row's
            ;; spelling record (`integrate/spellings-key`) before this runs, and an
            ;; inert record's `:inert` mark (`assert-inert`) is no creation provenance
            (empty? (dissoc cur integrate/spellings-key :inert))
            (p/put-provenance rec h (merge cur {:creator creator :created @now} extras))
            (seq extras) (p/put-provenance rec h (merge cur extras)))))))
  nil)

(defn- after-the-write
  "Run `f`, the steps `assert` takes after its sentence is stored, chained and settled —
  `record-provenance!`, `rehome-forced-extent!`, `nat-maint/reconcile-assert` — where a
  store that stops (`:store-unusable`, `:compaction-failed`) is logged at `:error` and
  not thrown.  The write has landed by then and a reopen holds it, so a throw would
  report as failed a write that took effect.  The store refuses every call after the
  fault, so the caller learns of it on the next one; what the log names is the step
  left undone for `handle`."
  [handle f]
  (try (f)
       (catch clojure.lang.ExceptionInfo e
         (if (#{:store-unusable :compaction-failed} (:type (ex-data e)))
           (trove/log! {:level :error :id ::store-stopped-after-write
                        :msg (str "the store stopped after assert stored " (pr-str handle)
                                  " — the write stands, and its provenance or the"
                                  " maintenance after it is missing: " (ex-message e))
                        :error e})
           (throw e)))))

;; ---- non-atomic terms: the write-path reify + mint -----------------------
;; The write-mode reify (mint + result-type materialization + collision merge) lives in
;; `vaelii.impl.nat`, storing through the assert path via `vaelii.impl.wiring` — so all NAT
;; reification is in one namespace.  The maintenance the write paths run around it — the
;; post-assert reconciliation and the orphan sweep — is `vaelii.impl.nat-maintenance`, which
;; this namespace reaches through one call per site; skolemizing an existential head is
;; `vaelii.impl.skolem`.
;;
;; `retract!` and `edit` are both forward-referenced and both defined far below, because
;; the write path and the query family are interleaved in this file: `finish-teardown!` and
;; `rollback-batch!` hand `retract!` to the orphan sweep as the teardown entry point to
;; remove bookkeeping with, `rehome-forced-extent!` moves premises into CxUniverse with
;; `edit!`, and `abduce` is handed `edit` to discard a scratch context with.

(declare retract! edit!)

;; `prepare-goal-for-read` moved to `vaelii.impl.quasiquote`, where it composes the two
;; read-time reductions it already holds with the equality rewrite, so `vaelii.impl.predall`
;; can prepare an audit goal exactly as the read entry points here do without depending on
;; this namespace (docs/namespaces.md, "The layering").

;; ---- the assert opts key set --------------------------------------------

(def assert-opt-keys
  "Every key `assert` / `assert-rule` reads.  Public for the same reason
  `kb/opt-keys` is: it is the answer to \"is this a real option?\", and a caller that
  can ask does not have to find out from a wrong answer.

  `:strength` is the assumption class, `:chain?` whether to forward-chain, `:direction`
  the programmatic spelling of a `set/*Rule` wrapper, `:creator` / `:provenance` the
  provenance it records, `:max-ms` / `:stop?` the caller's bound on the whole call
  (`chain/call-with-stop`); the rest flow to `chain/chain-all`."
  #{:strength :chain? :direction :creator :provenance
    :max-depth :max-term-depth :max-derivations :max-ms :stop? :on-progress
    :progress-every-ms})

(defn- context-shape-problem
  "The `:shape` problem a context slot of the wrong shape is refused with, or nil.  A
  context is a bare symbol — or a **ground application** `(CxTimeFn …)`, which reifies to
  its `cx/` constant before anything downstream reads it (docs/context-nat.md).

  The compound is admitted when reification yields a symbol: it is ground and headed by a
  symbol (`nat/context-application?`).  The test reads the form alone and no declaration,
  so the stored set does not depend on the order a declaration and a fact arrive in.  This
  is a shape invariant — a stored sentex's context is always a symbol — so it does not
  depend on the naming policy: a non-ground `(CxTimeFn CxMonad ?x)` never reifies, would
  store a raw list as the context, and is refused here whatever `:naming` is set to.

  A **query context** (`nm/query-contexts`) is refused too, whatever `:naming` says: the
  read entry points resolve one before the engine sees it, so nothing written there could
  be read back (docs/contexts.md)."
  [context]
  (cond
    (nm/query-context? context)
    {:type :shape :context context
     :message (str context " is a query context — a way of reading, not a place to write: "
                   "nothing is asserted into one.  Assert into the context you mean, and "
                   "pass " context " to a read instead.")}

    (not (or (symbol? context) (nat/context-application? context)))
    {:type :shape :context context
     :message (str "the context must be a bare symbol or a ground application headed by a "
                   "symbol (CxTimeFn …), got " (pr-str context))}))

(defn- sentence-shape-problem
  "The `:shape` problem a would-be assertion is refused with before it is even a sentence,
  or nil.

  A sentence is an s-expression.  Anything else names nothing the checks below can read:
  a string is the form a failed EDN read hands back (`impl.cli`'s `read-arg`, the
  daemon's `:args`), and `nil` is what an absent one is.  Unrefused, both would
  *store* — indexed, marked a premise and believed, as an object no query can ever
  match — while a symbol, a number or a map reaches `nth` and throws a bare
  `UnsupportedOperationException` that carries no `:type`.

  **A list, and not a vector**, which is the second arm and the sharper one: a vector is
  `sequential?` too, and `sentex/canon` flattens it to the list it looks like, so
  `[likes Tom Ann]` stored the sentence `(likes Tom Ann)` and every write-side check
  passed.  The read entry points do not read it that way.  A vector goal is a **conjunctive
  query** (docs/api.md), so `query` and `prove` handed the same spelling back join over
  the sentence's own elements as separate goals and answer nothing, silently, while
  `ask` and `sentexes-matching` canonicalize and find the fact — one spelling, two
  entry points, opposite answers, no error from either.  The read side cannot be made to
  **accept** it — the conjunctive vector is what every query entry point means by one, and one
  spelling cannot mean two things — so the spelling that collides is refused here.  It
  is refused *there* too, by `sentence-goal-problem` and `conjunction-goal-problem`
  below: refusing at one entry point and canonicalizing at the others left the split live on
  the read side, which is where its own example is measured.

  `check` and `assert` read this one fn, so what `check` predicts is what `assert` does.
  That is the whole contract `check` exists to keep, and the `(ist Ctx S)` arm below
  states the same reasoning for its own shape."
  [sentence]
  (cond
    (not (sequential? sentence))
    {:type :shape :sentence sentence
     :message (str "the sentence must be an s-expression, got " (pr-str sentence))}

    (not (seq? sentence))
    {:type :shape :sentence sentence
     :message (str "the sentence must be a list, not a vector: " (pr-str sentence)
                   " — a vector is how every read entry point spells a conjunction, so this"
                   " spelling would store one sentence and ask for a join over "
                   (count sentence) ".  Write " (pr-str (apply list sentence)))}))

(defn- check-shape!
  "Throw the `:shape` refusal `check` reports for a context or sentence that is not one.

  Called in `shape-problems`' own precedence — context, then opts, then sentence — so the
  two entry points refuse the same input for the same reason."
  [problem]
  (when problem
    (throw (ex-info (:message problem) (dissoc problem :message)))))

(defn- disjunction-shape-problem
  "The problem an `or` the polycanonicalization cannot expand away is refused with, or
  nil — `rules/disjunction-problems` as one problem map, read by both entry points right after
  the connective frames.

  Here rather than beside the other rule checks because it is a pure read of the
  sentence and because the expansion runs *before* them: `assert` splits the rule into
  its alternatives and then checks each, so a rule too wide to split, or one whose `or`
  sits where nothing would split it, has to be refused before the split is attempted.
  The per-alternative range check rides along for the same reason — after the split
  there is no disjunct left to name."
  [sentence]
  (first (rules/disjunction-problems sentence)))

(defn- check-sentence-shape!
  "The five refusals a would-be assertion earns before any check reads the KB — that it
  is an s-expression and a list rather than a vector, that its connective frames are
  whole, that every `or` it carries is one the polycanonicalization can expand away,
  that a measure magnitude is finite, and that every leaf survives the durable
  log.  In `shape-problems`' order, which is `assert`'s.

  One fn because **both storage entry points run all five**: `assert` and `assert-inert` write
  through different paths, and a guard one of them dropped would let that entry point store what
  the other refuses — which is the structure of corruption the checks exist to stop.  The
  context guard stays at the call sites, since `assert` reads its opts between the two
  and `check` reports them in that order."
  [sentence]
  (check-shape! (sentence-shape-problem sentence))
  (check-shape! (sx/connective-problem sentence))
  (check-shape! (disjunction-shape-problem sentence))
  (check-shape! (checks/quantity-shape-problem sentence))
  ;; Every leaf must survive the durable log: a non-serializable value (a function, an
  ;; atom) stores in memory and throws at write time on the first disk backend, so the
  ;; same assert would succeed or fail by backend.  Refused here, before anything is
  ;; stored, exactly as `shape-problems` reports it to `check`.
  (checks/check-encodable sentence))

(def ^:private direction-values
  "What a `:direction` opt may say — the three `set/*Rule` wrappers' values plus
  `:both`, which is what a bare `(implies …)` already is and so has no wrapper."
  (into #{:both} (vals sx/rule-direction-wrappers)))

(defn- direction-opt-problem
  "The problem an `opts :direction` carries, as a value, or nil when it is applicable.

  One fn read by both entry points: `apply-direction-opt` throws what this returns and
  `check` reports it, so a `:direction` refusal is never one `check` cannot predict.

  Four refusals.  A value outside `direction-values` would otherwise wrap nothing
  (`rules/wrap-direction` returns the sentence untouched for a value it does not know)
  and the rule would store `:both` and forward-chain — the silent default the option's
  own validation exists to stop, reachable by the plural typo `:backwards`.  A
  direction on something that is not a rule names nothing, and neither does one on a
  choice or constraint rule, which never chains.  And one that disagrees
  with a wrapper the sentence already carries is two answers to one question; refused
  rather than resolved, since either resolution would be a guess about which the
  writer meant."
  [sentence opts]
  (let [d (:direction opts)]
    (when (some? d)
      (let [inner (rules/inner-rule sentence)
            [written] (sx/peel-rule-wrapper sentence)]
        (cond
          (not (direction-values d))
          {:type :unknown-option :mismatch :bad-value :direction d :options (vec (sort direction-values))
           :message (str "unknown :direction " (pr-str d) " — assert takes "
                         (str/join ", " (map pr-str (sort direction-values)))
                         ".  A value nothing reads would wrap nothing, storing :both"
                         " and forward-chaining a rule that asked not to.")}

          (not (rules/rule-sentence? inner))
          {:type :unknown-option :mismatch :conflict :direction d :sentence sentence
           :message (str ":direction " (pr-str d) " on a sentence that is not a rule"
                         " — a direction says when a rule is run, and " (pr-str sentence)
                         " concludes nothing.")}

          ;; a choice or constraint head is decided by a solve and never chained, so a
          ;; direction on one says nothing (`sx/wrapper-stack-problems` refuses the
          ;; written wrapper for the same reason)
          (let [[_ _ _ assum con] (sx/peel-rule-wrapper sentence)] (or assum con))
          {:type :unknown-option :mismatch :conflict :direction d :sentence sentence
           :message (str ":direction " (pr-str d) " on a choice or constraint rule — its"
                         " head is decided by a solve and never chained, so it takes no"
                         " direction.")}

          ;; already wrapped and agreeing — `assert-rule` wraps and then calls through
          ;; here with the same opts, so this is the ordinary path, not a special case
          (= written d) nil

          (some? written)
          {:type :unknown-option :mismatch :conflict :direction d :written written :sentence sentence
           :message (str ":direction " (pr-str d) " contradicts the "
                         (pr-str written) " wrapper the sentence already carries"
                         " — state the direction once.")})))))

(defn- apply-direction-opt
  "Express an `opts :direction` as the `set/*Rule` wrapper it is the programmatic spelling
  of, or refuse it.

  `assert-rule` spells it this way already, and `assert`'s `:direction` key is in
  `assert-opt-keys` — waved through by `check-assert-opts!` — so this is where the key
  is read.  Accepted and read nowhere, `{:direction :backward}` would store `:both`
  and forward-chain, materializing exactly the cross product a backward-only rule
  exists to avoid — the silent-default failure the key set's own docstring says the
  guard is for.  The refusals themselves live in `direction-opt-problem`,
  which `check` reads too."
  [sentence opts]
  (let [d (:direction opts)]
    (if (nil? d)
      sentence
      (do (check-shape! (direction-opt-problem sentence opts))
          (let [[written] (sx/peel-rule-wrapper sentence)]
            (if (some? written) sentence (rules/wrap-direction sentence d)))))))

(defn- check-assert-opts!
  "Refuse an opts key `assert` does not read, and a `:strength` that is not a class a
  caller may assert.

  Both failures are silent otherwise, and both are the same silence: the assertion
  lands, so nothing downstream is missing — it lands at the **wrong defeat class**.
  `{:strenth :monotonic}` is a key nothing reads, so known-true content becomes
  defeasible and the first default that contradicts it wins; `{:strength 0.7}` reads as
  a class the KB does not have, and `strength/rank-of` scores an unknown class 0, so it
  would order *below* `:default` if anything ranked it.  A sentex is indistinguishable
  afterwards from one asserted at the class it fell back to, which makes here — where
  what the caller wrote is still legible — the only place either can be caught.

  There are exactly two assertable classes and undercutting is `exceptWhen`'s job
  (`vaelii.impl.strength`), so a caller reaching for a third has a design question
  rather than a spelling one, and a refusal is the answer that says so."
  [opts]
  ;; A non-nil non-map `opts` is refused here rather than ignored, so that `check` and
  ;; `assert` agree: `shape-problems` runs this same fn, and a guard that only
  ;; looked inside a map would let `(assert kb s ctx :oops)` sail through taking every
  ;; default while `(check kb s ctx :oops)` said it would not.
  (opts/check! opts assert-opt-keys "assert"
               (str "An option nothing reads takes the default in silence, which for"
                    " :strength means storing a default where known-true was meant."))
  ;; the chain bounds and the progress callback carried through to `chain/chain-all`
  ;; (`:max-depth` / `:max-derivations` / `:progress-every-ms` / `:on-progress`), value
  ;; checked here so a bad one refuses at the assert entry point rather than reaching the
  ;; fixpoint's arithmetic only when a rule happens to fire (`opts/bound-domains`)
  (opts/check-values! opts "assert")
  (when (map? opts)
    (when (and (contains? opts :strength)
               (not (strength/assertable? (:strength opts))))
      (throw (ex-info (str "unknown :strength " (pr-str (:strength opts)) " — assert takes "
                           (str/join ", " (map pr-str (sort strength/assertable)))
                           ".  Defeasibility past those two is stated with exceptWhen"
                           " on the rule, not with a class.")
                      {:type :unknown-option :mismatch :bad-value :strength (:strength opts)
                       :options (vec (sort strength/assertable))})))))

(defn- rehome-forced-extent!
  "When `sentence` is a `(forced_decontextualized_predicate P)` declaration, move every
  `(P …)` premise stored outside CxUniverse into it: the same sentence asserted there
  at the premise's own strength, and the original retracted, as one `edit!` batch
  (docs/contexts.md#forced_decontextualized_predicate-a-canonical-home-in-cxuniverse).

  Premises only: a derived `(P …)` outside CxUniverse is placed by the rule that
  concluded it.  The extent is snapshotted before the first move, since each move writes
  to the posting being read.  The mark is read unscoped."
  [kb sentence]
  (let [s    (rules/inner-rule sentence)
        pred (when (and (seq? s) (= 'forced_decontextualized_predicate (first s))) (second s))]
    (when (and (symbol? pred)
               (tax/has-prop? (reasoning/taxonomy kb) :forced-decontextualized pred))
      (let [tms   (reasoning/tms kb)
            moved (filterv #(and (= pred (nm/functor (:sentence %)))
                                 (not= special/universal-context (:context %))
                                 (jtms/premise? tms (:id %)))
                           (kb/find-sentexes kb pred))]
        (when (seq moved)
          (edit! kb {:add    (mapv #(vector (:sentence %) special/universal-context
                                            {:strength (p/premise-strength (:records kb) (:id %))})
                                   moved)
                     :remove (mapv :id moved)}))))))

(defn- teardown-refusal
  "The refusal a storage teardown of `handle` earns, as a value, or nil — one statement
  of the policy read by both entry points that need it: `retract-storage!`, which throws it,
  and `edit!`, which asks it of **every** removal in a batch while nothing has been
  removed yet.  A value rather than a throw for that second reader: an atomic batch can
  roll an assertion back at its handle and cannot un-delete a record, so the removals
  have to be known refusable-or-not before the first one runs.

  A forced-monotonic declaration whose predicate has no unforced semantics is refused whatever its
  node (`checks/forcing-retraction-problem`, docs/nmtms.md).  Otherwise nil for a handle
  with a TMS node — the dependency sweep can be computed, which is the whole question —
  and nil for a handle naming nothing stored, which `retract!` answers with zero counts.

  Where there is no node, the store holds two different facts and only one of them
  licenses a direct teardown.  An **inert** sentex (`assert-inert`) was never premised
  and never derived, so no justification names it and nothing rests on it — the teardown
  is complete.  A **stored premise whose network was never built** looks identical to the
  node test and is the opposite case: the store's own justifications may rest on it, and
  the sweep that would decide what falls with it cannot run over a network that does not
  exist.  Taking the inert branch there deletes one record, reports
  `{:removed-sentexes 1}`, and leaves every justification naming it pointing at nothing —
  a later `recover` reads each of those as a conclusion whose antecedent is gone, OUT
  forever with no instrument reporting it.

  The store answers the premise half per handle: a premise is a sentex whose `:strength`
  is non-nil (`kb/create-sentex`), which is also what `p/premise-ids` is rebuilt from at
  open.  So that one is refused rather than guessed, and refused **whatever
  `*write-unrecovered?*` says** — that opt accepts a write whose consequences are known
  and unchecked, and this one's are not known at all.

  A **derived** sentex is the third fact the node test cannot see, and carries no
  strength to be told apart by: a forward-chained record is not premised, so
  `p/premise-ids` does not name it, and over an unbuilt network it reads exactly like an
  inert one — while the store holds the justifications that concluded it and the ones
  naming it as an antecedent.  Nothing per-handle separates the two, the store keeping no
  index from a handle to the justifications that cite it, so the question is asked of the
  **KB** instead: where the network was never built, no record here can be shown to be
  the inert one, and the teardown is refused for all of them.  Where it was built, a
  record with no node genuinely is inert and the teardown is complete.  `write-hazards`
  is the same reader the entry point upstream uses, so the two refuse on one fact rather than on
  two tests that can disagree.

  `where` names the entry point for the refusal's `:operation`, which with `:hazards` and
  `:repair` is the shape `writable-problem` gives the same `:type` upstream: one
  `:unrecovered-kb` reads the same however a caller reached it."
  [kb handle where]
  (or
   (checks/forcing-retraction-problem kb handle where)
   (when-not (jtms/known-datum? (reasoning/tms kb) handle)
     (when-let [sx (p/get-sentex (:records kb) handle)]
       (if (some? (:strength sx))
         {:type :unrecovered-premise :handle handle :strength (:strength sx)
          :operation where
          :message (str "handle " handle " is a stored premise this KB has no TMS"
                        " node for, so the dependency sweep a retraction owes"
                        " cannot be computed — the store may hold justifications"
                        " resting on it.  Call (recover kb) (or (reindex kb) when"
                        " the index is derived) and retract then.")}

         (when-let [hz (seq (kb/write-hazards kb))]
           (let [hz (into {} hz)]
             {:type :unrecovered-kb :handle handle
              :hazards (vec (sort (keys hz)))
              :operation where
              :repair (if (:no-index hz) 'reindex 'recover)
              :message (str "handle " handle " has no TMS node in a KB whose belief was"
                            " never built, so whether anything rests on it cannot be"
                            " computed — an inert sentex and a derived one read alike"
                            " here, and only the derived one leaves justifications"
                            " naming a record this would delete.  Call (recover kb) (or"
                            " (reindex kb) when the index is derived) and retract"
                            " then.")})))))))

(defn- retract-storage!
  "The storage teardown behind `retract!` and `edit`, with **no settle**.  A datum
  runs the dependency-directed sweep (which decides what else falls with it); an
  inert sentex (never a TMS datum) is torn down directly through the removal choke
  point.  Returns `{:removed-sentexes n :removed-justifications n :datum? bool
  :seeds [handle] :rederive [justification] :sentences [s]}` — `:sentences` the facts
  the teardown removed, `:datum?` tells the caller whether
  belief could have moved and a settle is owed, `:seeds` what the removal owes a
  re-chain (a subsumption or a sighting whose named witness left but whose reachability
  survives — `special/resubsumption-seeds`), and `:rederive` the derivations that
  descended through a departing `genl` edge and are owed a re-derivation over a route
  that survives (`special/edge-descended-justifications`).  An absent key reads as
  empty."
  [kb handle]
  (if (jtms/known-datum? (reasoning/tms kb) handle)
    (do (p/unmark-premise! (:records kb) handle)         ; no longer an asserted premise
        (let [{:keys [removed-sentexes removed-justifications] :as r} (jtms/retract! (reasoning/tms kb) handle)
              ;; fetch each swept record BEFORE tearing it down — the JTMS returns handles,
              ;; and `sentex-removed!` is what deletes the record.  The retracted handle
              ;; goes even when `assert-inert` wrote it, as an inert record's retraction does.
              ;; Keep the sweep's order: the retracted handle torn down after the n nogoods it
              ;; sits in costs n² (perf's filler-beside-clashing-fillers).
              gone (integrate/swept-records kb removed-sentexes handle)
              ;; ...and read the re-chain seeds while the taxonomy still holds the
              ;; departing edges, since it is their spec subtree the seeds come from
              seeds (special/resubsumption-seeds kb gone removed-justifications)
              ;; ...and the derivations that descended through a departing genl edge,
              ;; read while their justification records still exist
              owed  (special/edge-descended-justifications kb gone removed-justifications)]
          ;; the removal choke point: disintegrate + unindex + delete + re-check queued,
          ;; one call — the same teardown the excepted-conclusion sweep runs, stated once
          (doseq [sx gone]
            (integrate/sentex-removed! kb sx))
          (doseq [jid removed-justifications]
            (p/delete-justification! (:records kb) jid))
          (special/retire-unjustified-mints! kb r)
          ;; a premise a derivation still holds up is now the derivation's alone
          (when-not (some #{handle} removed-sentexes)
            (special/note-unpremised! kb handle))
          {:removed-sentexes   (count gone)
           :removed-justifications (count removed-justifications)
           :datum?             true
           :seeds              seeds
           :rederive           owed
           :sentences          (into [] (keep :sentence) gone)}))
    ;; The two refusals this branch owes are `teardown-refusal`'s, stated once because
    ;; `edit!` has to ask them *before* it removes anything: a batch is atomic, and a
    ;; removal is the one half no rollback can put back.  Which is also why the entry point this
    ;; one names is `retract!` and not either: a batch that reaches here has already
    ;; cleared every removal, so the throw below is only ever a `retract!`'s.
    (if-let [sx (p/get-sentex (:records kb) handle)]
      (if-let [problem (teardown-refusal kb handle "retract!")]
        (throw (ex-info (:message problem) (dissoc problem :message)))
        (do (integrate/sentex-removed! kb sx)
            {:removed-sentexes 1 :removed-justifications 0 :datum? false :seeds []
             :sentences (into [] (keep :sentence) [sx])}))
      {:removed-sentexes 0 :removed-justifications 0 :datum? false :seeds []})))

(defn- settle-after-teardown!
  "The settle a teardown owes.  Relabel to revive any default the removed data were
  defeating, then re-derive what the removal released and relabel again.  Two things
  can need re-deriving, and both cost a *re-derivation* rather than a relabel because
  the sweep deleted what they would have revived (docs/exceptions.md, \"Garbage
  collection, not defeat\"):

  * a rule whose `exceptWhen` the removal released — `released`, captured by the caller
    **before** the first settle drains the re-check queue;
  * a subsumption whose named `genl` witness left while the reachability survived, or a
    placement whose named `genlCx` witness left while the sighting survived —
    `seeds`, the facts `special/resubsumption-seeds` puts back on the agenda;
  * an argument-type entailment or a descended equality whose named `genl` route left
    while another route survives — `rederive`, the justification records
    `special/edge-descended-justifications` read before the teardown deleted them.

  `rederive` is drawn after the first settle, because an equality is found by matching
  the facts that fill a functional slot, and matching reads the belief that settle
  publishes for a spelling the departed merge gave back.  What it creates joins the
  seeds.

  The seed re-chain files no `:no-placement`, and `chain/*report-no-placement?*` says
  why: it is re-asking firings the removal already swept, so one it cannot place is the
  retraction restated to the caller who made it."
  ([kb released seeds] (settle-after-teardown! kb released seeds nil))
  ([kb released seeds rederive]
   (settle/settle kb)
   (let [seeds (cond-> (vec seeds)
                 (seq rederive) (into (special/rederive-descended kb rederive)))]
     (when (or (seq released) (seq seeds) (seq rederive))
       (when (seq released) (settle/rechain-exception-rules kb released))
       (when (seq seeds)
         (binding [chain/*report-no-placement?* false] (settle/rechain-seeds kb seeds)))
       (settle/settle kb)))))

;; ---- rolling a batch back: the code `edit!`, `preview` and `assert` share -----
;; docs/preview.md, "The mechanism" and "The rollback is one implementation".

(defn- batch-baseline
  "The derived state a batch writes and `rollback-batch!` puts back — the violations
  ledger, the program, the refusal record and the mint queues — snapshotted before the
  batch runs, plus `:filed`, the identity set the batch binds `viol/*batch-entries*` to,
  and the taxonomy value and generations the refusal record's entries were decided under."
  [kb]
  {:violations @(reasoning/violations kb)
   :program    @(reasoning/program kb)
   :refused    @(reasoning/refused kb)
   :queues     (select-keys @(reasoning/mint-queues kb) [:owed :defer-next])
   :filed      (viol/batch-entries)
   :taxonomy   @(reasoning/taxonomy kb)
   :gens       (special/taxonomy-generations kb)
   :conviction (special/conviction-generations kb)})

(defn- recheck-suspended
  "Queue the re-checks that suspending or restoring the premise `h` owes: the sentence's
  exception re-check (`special/recheck-on-sentence`) and, for an `except`, the re-join of
  the firings it refused (`special/recheck-except`).  These are the posts the removal and
  arrival entry points make for a stored sentex leaving or arriving
  (`special/disintegrate-sentex!`, `special/structural-integrate`).  A handle with no
  record posts nothing."
  [kb h]
  (when-let [sx (p/get-sentex (:records kb) h)]
    (let [sentence (sx/sentence-of sx)]
      (special/recheck-on-sentence kb sentence)
      (when (= sx/except-functor (nm/functor sentence))
        (special/recheck-except kb sx)))))

(defn- remove-above-mark!
  "Remove every justification and then every sentex stored at a handle above `h0`, the
  write's mark (`entry/*write-mark*`), each pass newest first, so each justification's
  removal relabels the one node of a chain it concludes.  Reads each handle the write
  allocated twice, as a justification and as a sentex; reads nothing below `h0`."
  [kb h0]
  (let [tms     (reasoning/tms kb)
        records (:records kb)
        hs      (range (dec (p/next-id records)) h0 -1)]
    (doseq [h hs :when (p/get-justification records h)]
      (let [r (jtms/drop-justification! tms h)]
        (p/delete-justification! records h)
        (integrate/apply-removals! kb r)))
    (doseq [h hs :when (p/get-sentex records h)]
      (integrate/take-out! kb h))))

(defn- rollback-batch-unbounded!
  "`rollback-batch!`'s body, run under `chain/call-unbounded`."
  [kb {:keys [audit suspended violations program refused sink filed mark queues]
       :as baseline}]
  (let [tms     (reasoning/tms kb)
        records (:records kb)]
    ;; both bindings file the rollback's own entries into the batch's set, so the restore
    ;; drops them with the batch's
    (binding [feed/*enabled?* false
              viol/*batch-entries* filed
              entry/*premise-audit* nil
              *defer-settle?* true
              integrate/*removed-sink* (or sink integrate/*removed-sink*)
              ;; the undo of a write a shutdown stopped runs to its end
              dur/*abortable?* false]
      (doseq [[h strength] suspended]
        (jtms/add-premise tms h strength)
        ;; the mirror of the re-checks the suspension queued
        (recheck-suspended kb h))
      ;; the rule slots first, so nothing below reads an engine the batch added
      (doseq [[h {:keys [slots]}] @audit :when slots]
        (entry/restore-rule-slots! kb h slots))
      (doseq [[h {:keys [premise? strength spellings] :as e}] @audit
              :when (contains? e :premise?)]
        (cond
          ;; `put-premise-mark`, not `mark-premise`, whose `strength/max` would keep a
          ;; class the batch raised; the spellings go back so the row hands back no
          ;; spelling the batch folded into it when a permuting mark leaves
          premise?                 (do (entry/put-premise-mark kb h strength)
                                       (integrate/put-spellings! kb h spellings))
          (p/get-sentex records h) (retract-storage! kb h)))
      ;; what the batch derived from content it did not store, which no premise above
      ;; holds up; before the settle, which rewrites records below the mark
      (when-let [h0 (some-> mark deref)]
        (remove-above-mark! kb h0)))
    ;; no re-chain seeds: what they would re-derive is content the batch created, at
    ;; handles the audit cannot take back
    (binding [feed/*enabled?* false
              viol/*batch-entries* filed
              integrate/*removed-sink* (or sink integrate/*removed-sink*)
              dur/*abortable?* false]
      (settle-after-teardown! kb (settle/rechain-owed kb @(reasoning/recheck kb)) nil)
      ;; the whole-KB arm for a batch, the region arm for a single `assert`'s `:sink`
      ;; (`nat-maint/collect-orphans!`)
      (if sink
        (nat-maint/collect-orphans! kb sink retract!)
        (nat-maint/collect-orphans! kb retract!)))
    (viol/restore! kb violations filed)
    (reset! (reasoning/program kb) program)
    ;; the refusal record: an entry the batch's content wrote names handles the rollback
    ;; took away (docs/preview.md, "What the rollback restores")
    (reset! (reasoning/refused kb) refused)
    (swap! (reasoning/mint-queues kb) #(merge (dissoc % :owed :defer-next) queues))
    (special/advance-refusal-generations! kb baseline)))

(defn- rollback-batch!
  "Put the KB back the way the batch found it, at the handles it wrote: restore the
  premises it suspended, retract what the audit says the batch created, re-mark at the
  recorded strength and spellings what was already a premise, settle with the sweep on,
  and restore what `batch-baseline` snapshotted, the refusal entries under the generations
  now (`special/advance-refusal-generations!`).  The handle counter stays moved.
  docs/preview.md.

  Takes that baseline plus `:audit` (the `entry/*premise-audit*` atom the batch ran under),
  `:suspended` (`[[handle strength] …]`, empty for an entry point that suspends nothing),
  an optional `:mark` (the `entry/*write-mark*` volatile), above which every record is
  removed before the settle (`remove-above-mark!`), and an optional `:sink`
  (`integrate/removal-sink`) that scopes the orphan sweep to the rollback's own removals.
  The rule slots the audit recorded go back before anything else.  A handle in both sets is restored from `:suspended` and then
  put back at the audit's record: the adds run before the suspensions, so the audit holds
  the state the batch found, and the suspension the class an add raised.
  Runs with the change feed off (docs/feed.md, \"What does not arrive\"), and unbounded
  (`chain/call-unbounded`)."
  [kb baseline]
  (chain/call-unbounded #(rollback-batch-unbounded! kb baseline)))

(defn- write-checked
  "`f`, run so that `entry/*write-check*`, when bound, is called with the handles `f`'s
  rule firings concluded once `f` returns.  An enclosing call that bound the sink already
  checks them, so `f` comes back as it was."
  [kb f]
  (if-let [check (when-not observe/*fired-sink* entry/*write-check*)]
    (fn []
      (let [sink (java.util.HashSet.)
            r    (binding [observe/*fired-sink* sink] (f))]
        (check kb (set sink))
        r))
    f))

(defn- undoing-refusal
  "Run `f`, the body of one `assert`, under a premise audit and the bound `opts` sets
  (`chain/call-with-stop`), and return what `f` returns; a throw out of it runs
  `rollback-batch!` over the audit and is rethrown as raised, with a rollback that fails
  too attached as suppressed (docs/api.md, \"Validating without writing\").  Under its own
  audit a run the caller's bound ends throws `:interrupted` (`chain/*rollback-scope*`).

  The write's mark (`entry/*write-mark*`) is bound for the call, and a rollback removes
  every record above it once taken.  An empty audit and no mark skip the rollback.  An
  enclosing audit (`edit!`, `preview`, or the `assert` this one is nested in, such as the
  mint's own) owns the undo, so this adds none.  With a change-feed listener installed the call holds the feed
  (`feed/with-one-event`), since a mint settles before the sentence it serves is checked;
  after a rollback the held event is empty and not delivered.  The write's
  stratification checks share one stored graph (`rules/*stratification-memo*`).  A bound
  `entry/*write-check*` reads what `f`'s rule firings concluded before the call returns
  (`write-checked`), and its throw is a refusal like any other."
  [kb opts f]
  (if entry/*premise-audit*
    (binding [rules/*stratification-memo* (or rules/*stratification-memo* (volatile! nil))]
      (chain/call-with-stop opts (write-checked kb f)))
    (let [audit    (atom {})
          mark     (volatile! nil)
          baseline (batch-baseline kb)
          run      (fn []
                     (try
                       (binding [entry/*premise-audit* audit
                                 entry/*write-mark*    mark
                                 viol/*batch-entries*  (:filed baseline)
                                 ;; the defeats the write removes, whose targets the
                                 ;; settle reads as moved (`settle/defeat-moves`)
                                 integrate/*removed-sink*
                                 (or integrate/*removed-sink*
                                     (integrate/removal-sink (exc/placed-reads? kb)))
                                 observe/*write-record* (settle/write-record kb)
                                 rules/*stratification-memo*
                                 (or rules/*stratification-memo* (volatile! nil))
                                 chain/*rollback-scope* true]
                         ;; the write a rollback takes back whole, so a shutdown or the
                         ;; caller's bound may stop it
                         (dur/as-unit #(chain/call-with-stop opts (write-checked kb f))))
                       (catch Throwable t
                         (when (or (seq @audit) @mark)
                           (try
                             (rollback-batch! kb (assoc baseline :audit audit :suspended nil
                                                        :mark mark
                                                        :sink (integrate/removal-sink true)))
                             (catch Throwable r (.addSuppressed t r))))
                         (throw t))))]
      (if (feed/wants-region? kb)
        (feed/with-one-event kb (run))
        (run)))))

(defn- exceptWhen-rule-forms
  "An inline `(exceptWhen <query> <rule>)` as the rules `assert` stores for it: one per
  form of the rule's polycanonicalization (`rules/expand-rule`, a DNF alternative of a
  disjunctive antecedent times a conjunct of a conjunctive consequent), each wrapped in
  the exception.  `exc` and `inner` are `rules/split-exceptWhen`'s two halves.

  `assert` and `check` hold every one of these to the whole-rule checks and to the
  exception's closure before anything is stored, because each form is a rule of its own
  once stored.  The closure reads that form's antecedents, so an exception variable only
  one alternative binds is refused for the alternative that leaves it unbound.  The
  stratification walk reads that form's consequent predicate, so the exception's negative
  edge is placed on the predicate the stored rule concludes rather than on `and`."
  [exc inner]
  (mapv #(list sx/except-wrapper exc %) (rules/expand-rule inner)))

(defn- check-reified-inputs!
  "Refuse a fact whose function applications are given inputs their functions' argument
  declarations forbid, asked of the sentence **before** the reify pass mints its ground
  reifiable applications away (`checks/check-application-inputs`).

  Routed the way `assert-entry/assert-one` routes what it stores, so the check reads the
  fact that would be stored from the context it would be stored in: an imperative and a
  rule are passed over (neither is a fact), an `(ist Ctx S)` is `S` in `Ctx`, a virtual
  wrapper is peeled, and a forced-decontextualized predicate reads from CxUniverse.
  Skipped under `*bulk-load?*`, which skips every definitional check, and in a KB
  declaring no `reifiable_function`, where the pass mints nothing and
  `constraint-checks` reads every application after it."
  [kb sentence context]
  (when (and (not *bulk-load?*) (nat-read/any-reifiable-functions? kb) (sequential? sentence))
    (cond
      (sx/do-form? sentence) nil

      (= sx/ist-functor (first sentence))
      (when-let [[ctx s] (entry/ist-parts sentence)]
        (when (symbol? ctx) (check-reified-inputs! kb s ctx)))

      (rules/rule-sentence? (rules/inner-rule sentence)) nil

      :else
      (let [s (rules/inner-rule sentence)]
        (checks/check-application-inputs
         kb s (entry/storage-context kb (nm/functor s) context))))))

(defn assert
  "Assert `sentence` in `context` (default 'CxUniverse) as a JTMS premise: enforce
  naming, arg, and disjointness constraints, persist, index (trie + term index),
  mark IN, integrate into the taxonomy / rule index, then forward-chain.  A
  virtual set/forwardRule|backwardRule|inertRule wrapper directs the enclosed
  rule.  `opts` flows to chaining ({:max-depth ..}, {:chain? false}) and carries the
  assumption `:strength` (:default, the common case, or :monotonic for known-true
  content that no default may defeat and that is never sent to a solver).  A
  rebuttal — the negation of a believed sentence — is resolved at settle time, never
  thrown; a definitional clash (`:disjoint`, `:functional`, `:asymmetric`) against stored
  content is stored and settled too, and reported by `conflicts` when every member is
  `:monotonic` (`check`'s docstring).  A rule that
  concludes a conjunction is polycanonicalized into one rule per conjunct — then this
  returns the vector of their handles; otherwise it returns the single sentex handle.

  Records **provenance** for the created sentex: `:creator` (from `opts :creator`, else
  `*creator*`) and `:created` (from `*clock*`), plus any `opts :provenance` map merged
  in — read with `provenance`, extended with `add-provenance`.

  An `opts` key this fn does not read is **refused** (`:unknown-option`), as is a
  `:strength` outside `{:default :monotonic}` — see `assert-opt-keys`.  Both would
  otherwise store the sentence at a defeat class the caller did not ask for, which
  nothing downstream can tell from one that was asked for.

  **An `exceptWhen` is two assertions and `opts` is one**, so `:strength` reaches the
  rule *and* the exception qualifying it.  Where the two differ, the exception's own
  class is stated on its query — `(exceptWhen (set/monotonic Q) R)` is a known-true
  exception on a default rule, the one pairing an `opts` cannot express.  The wrapper is
  peeled before anything is split, checked or stored (docs/exceptions.md).  Around the
  whole sentence, `(set/monotonic S)` is `S` asserted `{:strength :monotonic}`, as the
  text KB format reads it, and beside an `opts` `:strength` other than `:monotonic` it is
  refused (`:shape`).  Elsewhere on the wrapper chain it is refused (`:shape`), and so is
  `(set/inert …)`, the text KB format's spelling of `assert-inert` (docs/kbs.md).

  **The sentence is a list, and a vector is refused** (`:shape`).  A vector is what
  every read entry point spells a *conjunction* with, so the one spelling would store a
  sentence and query a join — see `sentence-shape-problem`.

  **A KB whose belief was never built refuses this** (`:unrecovered-kb`), since every
  definitional check below would pass vacuously and the store would keep the result —
  `*write-unrecovered?*` is the opt that names what accepting one gives up.

  **A refusal leaves the KB as the call found it**, the handle counter aside.  A mint, a
  skolem declaration, or the sentence itself can be written before the check that
  refuses the call, and `undoing-refusal` takes them back before the throw leaves.

  `:max-ms` bounds the call by wall-clock milliseconds, and `:stop?` is a function of no
  arguments whose truthy answer ends it.  Either one, and a `:max-derivations` the run
  reaches, refuses the call (`:interrupted`) and leaves the KB as the call found it
  (docs/inference.md, *Stopping a run*)."
  ([kb sentence] (assert kb sentence 'CxUniverse nil))
  ([kb sentence context] (assert kb sentence context nil))
  ([kb sentence context opts]
   ;; Before the shape guards and so before `*bulk-load?*` can skip anything: bulk mode
   ;; turns off the dedup walk this state has already lost, so it must not be the way
   ;; into it.
   (check-writable! kb "assert")
   ;; a whole-form `(set/monotonic S)` is `S` at `:strength :monotonic`, refused here
   ;; when malformed, in the precedence `check` reports it
   (let [[sentence opts] (sx/peel-strength sentence opts)]
     ;; In `shape-problems`' precedence, so `check` and `assert` refuse the same input for
     ;; the same reason: a sentence that is not an s-expression would store in silence,
     ;; and one that is not sequential throws bare, with no `:type` to discriminate on.
     ;; The vector arm is the same failure at one remove — it stores, and then the read
     ;; entry points read the spelling as a conjunction.
     (check-shape! (context-shape-problem context))
     (check-assert-opts! opts)
     (check-sentence-shape! sentence)
     ;; Reify ground reifiable NATs to their opaque constants before `expand-consequent`,
     ;; WFF and the constraint checks, so the compound never reaches the index and the minted constant's materialized types are in
     ;; place for the checks below (docs/nat.md).  The pass runs only when the KB declares
     ;; a reifiable_function, so a KB with none is unaffected.
     (undoing-refusal
      kb
      opts
      (fn []
        (let [;; A ground application `(CxTimeFn …)` in the context slot reifies to its `cx/`
              ;; constant here — the context-slot twin of the sentence reify below, since the
              ;; context argument is not on the sentence walk (docs/context-nat.md).  A no-op
              ;; for a symbol.
              context  (nat/maybe-reify-context kb context)
              sentence (apply-direction-opt sentence opts)
              ;; The answer-set surface forms — an `(asp/atMost k ?v pattern)` / `(asp/atLeast …)`
              ;; cardinality bound, an `(asp/minimize p ?w body)` objective, and a priority-tagged
              ;; `(set/softConstraint p (implies …))` — are rewritten to the constraint rules they
              ;; are (a `set/hardConstraint`/`set/softConstraint` whose consequent marker carries
              ;; the operands) before anything reads their shape, so the split, the checks and the
              ;; store all see ordinary constraint rules (docs/solving.md).  The identity on every
              ;; other sentence.
              sentence (rules/normalize-solve-surface sentence)
              ;; `(exceptWhen (set/monotonic <query>) <rule>)` states the **exception's** own
              ;; defeat class, which one `opts` cannot: it reaches both halves, so the pairing
              ;; a known-true exception makes with a default rule had no spelling at all
              ;; (docs/exceptions.md).  Peeled here, before the split — so `split-exceptWhen`,
              ;; the naming checks and the store all read the sentence they always did — and
              ;; `exc-opts` is what the meta-sentex alone is stored under.
              [sentence exc-mono?] (sx/peel-exception-strength sentence)
              exc-opts (cond-> opts exc-mono? (assoc :strength :monotonic))
              ;; a directly-asserted ground `(Quasiquote …)` reduces to its `(Quote E)` mention
              ;; form here, *before* the reify pass below turns `(Quote E)` into its constant —
              ;; so it never reaches the index as a raw structural compound.  The reduction is
              ;; a no-op unless the KB declares quasiquotation.
              sentence (quasiquote/maybe-reduce kb sentence)
              ;; a reifiable application's inputs are read here or nowhere: the pass below
              ;; replaces it with a constant that carries its result types, not its inputs
              _        (check-reified-inputs! kb sentence context)
              written  sentence
              sentence (nat/maybe-reify-nats kb sentence (:chain? opts true) context)
              ;; after the mints, whose own asserts settle, so the settle this write runs
              ;; finds the use stored
              _        (nat/queue-split-uses! kb written)
              ;; An `(exceptWhen <query> <rule>)` is split into the bare rule (or a handle it
              ;; named directly) and the exception.  The rule is asserted normally and the
              ;; exception stored as a separate belief-following meta-sentex against its
              ;; handle, so a rule and its unexcepted twin share one handle and asserting or
              ;; retracting an exception amends the rule in place (docs/exceptions.md).
              [exc inner] (rules/split-exceptWhen sentence)]
          (if exc
            (if (sx/sentex-handle? inner)
              ;; The exceptWhen names a rule by handle directly: no new rule to store, and the
              ;; exception aligns against the stored rule's own varmap (the only author names
              ;; there are).  Its checks live in `assert-exceptWhen-meta!`.
              (let [h  (sx/handle-id inner)
                    mh (entry/assert-exceptWhen-meta! kb h exc (:varmap (p/get-sentex (:records kb) h))
                                                      context exc-opts)]
                (after-the-write mh #(record-provenance! kb mh opts))
                mh)
              ;; An inline-rule exceptWhen.  Run the whole-rule checks (naming,
              ;; range-restriction, stratification with the exception's negative edge,
              ;; exception closure, and the naming of the exception's own literals) on
              ;; every *wrapped* form the rule is stored as (`exceptWhen-rule-forms`)
              ;; before anything is stored, so a refused exception leaves no bare rule
              ;; behind — `assert-exceptWhen-meta!` checks again, but it runs
              ;; after the rule is stored and chaining, so a refusal only it made would
              ;; leave the bare rule believed and firing unguarded, with no handle returned
              ;; to retract it by.  Then store the rule(s) and attach the exception to
              ;; **each** — aligned against that conjunct's *own* canonicalization: a
              ;; conjunctive consequent splits into one rule per conjunct, and a self-join
              ;; tie group can be numbered differently by each (the consequent breaks the
              ;; tie), so one shared varmap would misalign the exception on a conjunct
              ;; whose numbering differs.
              (let [_       (when-let [p (rules/exceptWhen-not-a-rule exc inner)]
                              (throw (ex-info (:message p) (dissoc p :message))))
                    _       (run! (fn [form]
                                    (entry/check-rule-sentence kb form context)
                                    (sx/check-exception-closed (rules/antecedents (rules/inner-rule form)) exc))
                                  (exceptWhen-rule-forms exc inner))
                    ;; as written rather than aligned — naming reads functors and argument
                    ;; spellings, which alpha-renaming does not touch
                    _       (run! #(nm/check! (:naming kb) % context) exc)
                    rule-hs (assert kb inner context opts)
                    hs      (if (sequential? rule-hs) rule-hs [rule-hs])
                    ;; the expanded rule forms, in the same order `assert` stored them —
                    ;; one per DNF alternative of a disjunctive antecedent, and one per
                    ;; conjunct within each
                    forms   (rules/expand-rule inner)
                    meta-hs (mapv (fn [h form]
                                    (entry/assert-exceptWhen-meta!
                                     kb h exc
                                     (:varmap (res/kb-sentex kb (rules/inner-rule form) context))
                                     context exc-opts))
                                  hs forms)]
                (after-the-write meta-hs #(record-provenance! kb meta-hs opts))
                (if (= 1 (count meta-hs)) (first meta-hs) meta-hs)))
            ;; a rule with a head existential `(exists ?y C)` will skolemize when it
            ;; fires; declare its reifiable function *now*, before chaining, so a rule
            ;; that fires during its own assert already finds it (docs/skolem.md)
            (let [_ (when (skolem/has-existential-head? sentence)
                      (skolem/ensure-skolem-function kb))
                  forms (rules/expand-rule sentence)
                  h     (if (next forms)
                          ;; A disjunctive antecedent or a conjunctive consequent is ONE rule
                          ;; the caller wrote, stored as several.  Check every one before
                          ;; storing any, so the split stays invisible: the whole rule is
                          ;; asserted or none of it is.
                          ;; Without this a refusal on a later conjunct left the earlier ones
                          ;; stored and firing.
                          (do (run! #(entry/check-rule-sentence kb % context) forms)
                              (mapv #(entry/assert-one kb % context opts {:assert-fn assert :bulk? *bulk-load?*}) forms))
                          (entry/assert-one kb (first forms) context opts {:assert-fn assert :bulk? *bulk-load?*}))]
              (after-the-write
               h
               (fn []
                 (record-provenance! kb h opts)
                 (rehome-forced-extent! kb sentence)
                 ;; The collision merge a rename may have caused, the correspondence a value
                 ;; or a declaration arriving last leaves to settle, the structural genlCx
                 ;; edges the stored fact entails, and the merges those edges license —
                 ;; sequenced below core, behind one presence check that a KB reifying
                 ;; nothing never passes (docs/nat.md, docs/context-nat.md).
                 (nat-maint/reconcile-assert kb sentence context opts)))
              h))))))))

(defn try-assert
  "`assert`, refusing a sentence that would open a definitional clash with believed
  content visible from `context`: a `:disjoint`, `:functional`, `:asymmetric`,
  `:anti-transitive` or `:cover` clash formed by the sentence, by a membership its
  argument declarations mint, or, for a `(forced_decontextualized_predicate P)`
  declaration, by a `(P …)` premise it moves into CxUniverse (`rehome-forced-extent!`);
  an argument holding a type the taxonomy separates from its declared type (`:arg-type`,
  `:arg-genl`, `:inter-arg-type`), under either argtype reading; an `arg` / `genlArg`
  / `interArg` declaration a stored tuple breaks; a rule one of whose variables no term
  can fill (`:arg-variable`); an `arg` / `genlArg` / `quotedArg` declaration that
  would convict a stored, believed rule so, which names the rule in `:clashes-with`; a
  fact whose length breaks its relation's length binding, or a length binding, `genl`
  edge or `:monotonic` metatype membership or edge that would break the length of stored
  tuples, or an `except` of a binding (`:arity`); an argument declaration naming a
  position past its predicate's bound length, or a length binding, `genl` edge or
  `:monotonic` metatype membership or edge that would strand a stored, believed one so
  (`:arg-position`); a `genlArg` on an `instance_relation_predicate`, or a membership
  stating a predicate one over a stored, believed `genlArg` on it
  (`:arg-constraint-kind`); a self tuple of an `irreflexive`
  relation, or an `irreflexive` mark over stored ones (`:irreflexive`), or the converse
  of a believed tuple of an
  `anti_symmetric` one (`:anti-symmetric`), where the relation is marked or below a
  marked one through `genl`; and a literal whose complement (`(not S)` for `S`, `S` for `(not S)`) a read from `context`
  answers `:monotonic` through `:monotonic` edges alone (`:complement`), a forced-monotonic
  complement at either written strength, unless the literal is itself a forced-monotonic
  positive.
  The refusal is `:definitional-clash`, carrying the clash
  kind in `:violation`, the members it clashes with in `:clashes-with`, and
  `:entailed-from` when a mint clashes, and the call stores nothing.  Every other
  refusal, argument and return value is `assert`'s.

  Whether a write is refused depends on what is already stored, so this is the one write
  entry point whose result depends on arrival order (docs/api.md, \"Refusing a clash\")."
  ([kb sentence] (try-assert kb sentence 'CxUniverse nil))
  ([kb sentence context] (try-assert kb sentence context nil))
  ([kb sentence context opts]
   (binding [checks/*refuse-clashes?* true]
     (assert kb sentence context opts))))

(defn assert-rule
  "Assert a rule (a sentex whose sentence is an implication) in `context`.
  `opts` may carry `:direction` (:forward | :backward | :inert | :both, default
  :backward) — or use a set/*Rule virtual predicate with `assert`.  A generator (a rule
  concluding a rule) defaults to :forward instead — no backward goal asks for a rule."
  ([kb antecedents consequent] (assert-rule kb antecedents consequent 'CxUniverse nil))
  ([kb antecedents consequent context] (assert-rule kb antecedents consequent context nil))
  ([kb antecedents consequent context opts]
   ;; the unrecovered-KB check first, before the range check, so this refuses like every
   ;; other write entry point: on a KB whose belief was never built `assert` answers
   ;; `:unrecovered-kb`, and the early range check would otherwise answer
   ;; `:not-range-restricted` where `checks/check-rule!` inside `assert` makes the same
   ;; range check anyway (the early call only decides which refusal wins)
   (check-writable! kb "assert-rule")
   (rules/check-range-restricted antecedents consequent)
   ;; `:direction` is just the programmatic spelling of a set/*Rule wrapper — wrap
   ;; and hand it to the one rule path, where the sentex constructor turns it into
   ;; the record's :direction.  assert also splits a conjunctive consequent.  The
   ;; wrapper then carries the direction, so `:direction` leaves the opts: `assert`
   ;; reads a second statement of it as a conflict when the two spell one class
   ;; differently (`:both` against the `:forward` wrapper).
   (let [sentence (rules/wrap-direction (rules/rule-sentence antecedents consequent)
                                        (:direction opts :backward))]
     (assert kb sentence context (dissoc opts :direction)))))

;; ---- check: would this assert succeed, and why not? ----------------------
;;
;; `assert` answers that question by *doing* it: the first check that fails throws and
;; nothing is stored.  A caller that wants the answer rather than the effect — an
;; editor validating a line before saving it, a critic grading a proposed batch, an
;; importer triaging a corpus — otherwise has to store-and-catch (which writes when the
;; content is fine) or reimplement the chain (which drifts).
;;
;; `check` runs `assert`'s own checks for their answer instead: the same functions in
;; the same order, reporting each failure under the `:type` keyword `assert` would have
;; thrown, and writing nothing.  Some of those checks are already values
;; (`nm/problems`, `special/wff-problems`); the rest throw, and are read back through
;; `problem`.  Running them rather than restating them is what keeps the two in step.

(defn- problem
  "Run `f` for its checks alone and return the typed problem it threw as a map, or nil
  when it passed.  The `ex-data` is kept whole — so `:arg` / `:expected` / `:cycle`
  survive for a caller that wants more than the sentence — with the exception's own
  message under `:message`."
  [f]
  (try (f) nil
       (catch clojure.lang.ExceptionInfo e
         (assoc (ex-data e) :type (:type (ex-data e) :error) :message (.getMessage e)))
       (catch Exception e
         {:type :error :message (or (.getMessage e) (.getName (class e)))})))

(defn- first-problems
  "The problems of the first stage that finds any — `assert`'s order, stopping where
  `assert` would have thrown.  Later stages read the KB *assuming* the earlier ones
  held (the constraint checks match a sentence whose functor naming already passed), so
  running on past a failure would report noise rather than more problems."
  [stages]
  (reduce (fn [_ stage] (let [ps (stage)] (if (seq ps) (reduced (vec ps)) []))) [] stages))

(defn- shape-problems
  "What stops a would-be assertion from even being a sentence in a context.  In
  `assert`'s own precedence — context, then the whole opts read (`check-assert-opts!`:
  non-map, unknown key, bad `:strength`), then the sentence — and through `assert`'s
  own check fns, so the two entry points refuse the same input for the same reason with the
  same `:type`.  Nil when all three hold.

  The opts key set is checked here as well, so `check` answers for the *request* and not
  only for the sentence: an entry whose `:strength` is misspelt is admissible knowledge
  asserted at the wrong class, which is exactly what a batch critic exists to catch
  before it lands."
  [sentence context opts]
  (or (some-> (context-shape-problem context) vector)
      (some-> (problem (fn [] (check-assert-opts! opts))) vector)
      (some-> (sentence-shape-problem sentence) vector)
      ;; A malformed answer-set surface (`asp/atMost` / `asp/atLeast` / `asp/minimize`, or a
      ;; priority-tagged `set/softConstraint`) is reported here, as a returned problem, so
      ;; `check` predicts the `:not-well-formed` refusal `assert` throws when it normalizes
      ;; the form rather than throwing out of `check` itself.  `normalize-solve-surface`
      ;; throws on a bad bound/priority/weight and is the identity on every other sentence,
      ;; so `problem` catches the throw and this is nil unless the sentence is one of those
      ;; surfaces, malformed.
      (some-> (problem (fn [] (rules/normalize-solve-surface sentence))) vector)
      (some-> (sx/connective-problem sentence) vector)
      (some-> (disjunction-shape-problem sentence) vector)
      (some-> (checks/quantity-shape-problem sentence) vector)
      (some-> (problem (fn [] (checks/check-encodable sentence))) vector)))

(defn- fact-problems
  "The checks `assert-one` runs over a non-rule sentence, as values.  The virtual
  wrapper is peeled and the context is `assert-entry/storage-context`'s, the one the
  assert path stores in, so what is checked is the sentence that would be stored."
  [kb sentence context]
  (let [sentence (rules/inner-rule sentence)
        context  (entry/storage-context kb (nm/functor sentence) context)]
    (first-problems
     (cond->>
      [#(for [p (nm/blocking-problems (:naming kb) sentence context)]
          {:type :naming :sentence sentence :context context
           :message (str "naming invariant: " p)})
       #(some-> (problem (fn [] (checks/check-length-binding
                                 (if (= :strict (:naming kb)) :strict :off) sentence context)))
                vector)
       #(some-> (problem (fn [] (checks/check-no-defeat sentence))) vector)
       #(some-> (problem (fn [] (checks/check-ground kb sentence context))) vector)
       #(for [p (special/wff-problems (reasoning/taxonomy kb) sentence context)]
          {:type :not-well-formed :sentence sentence :message (str "not well-formed: " p)})
       #(some-> (problem (fn [] (checks/check-except-target kb sentence))) vector)
       #(some-> (problem (fn [] (checks/check-edge-stratified kb sentence context))) vector)
       #(some-> (problem (fn [] (checks/check-closed-extent-stratified kb sentence context))) vector)
       #(some-> (problem (fn [] (checks/constraint-checks kb sentence context))) vector)]))))

(defn- rule-problems
  "The pre-storage checks a rule must pass — per rule the polycanonicalization stores,
  which is one per DNF alternative of a disjunctive antecedent times one per conjunct of
  a conjunctive consequent, since `assert` checks every one of them before storing any.
  Covers the imperative ban, range-restriction, naming, the argument constraints
  the rule's own variables carry, and stratification."
  [kb sentence context]
  (first-problems
   (for [form (rules/expand-rule sentence)]
     #(some-> (problem (fn [] (entry/check-rule-sentence kb form context))) vector))))

(defn- exceptWhen-naming-problems
  "The naming problems an exceptWhen query's own literals carry, as values.

  `assert` holds each conjunct to the invariants every other literal a rule carries is
  held to; this is that check as a report, so `check` predicts it.  The conjuncts are
  read as written rather than aligned to the rule's varmap — naming reads a literal's
  functor and argument spellings, which alpha-renaming does not touch."
  [kb exc context]
  (vec (for [lit exc
             p   (nm/blocking-problems (:naming kb) lit context)]
         {:type :naming :sentence lit :context context
          :message (str "naming invariant: " p)})))

(defn- exceptWhen-handle-problems
  "An `(exceptWhen <query> (sentexHandle H))` amends a rule that is already stored
  rather than storing one, so what is answerable without writing is that H names a
  stored rule and that the exception's variables are ones that rule binds."
  [kb inner exc]
  (let [h   (sx/handle-id inner)
        rsx (p/get-sentex (:records kb) h)]
    (if-not (and rsx (rules/rule? rsx))
      [{:type :not-well-formed :handle h
        :message (str "exceptWhen names handle " h ", which is not a rule")}]
      (some-> (problem #(sx/check-exception-closed (vec (vals (:varmap rsx))) exc))
              (assoc :rule h)
              vector))))

(defn check
  "Would `(assert kb sentence context opts)` succeed, and if not, why?  Returns a
  **vector of problems** — empty when the sentence is admissible — and **stores
  nothing**: no sentex, no index entry, no taxonomy edge, no chaining, no settle.

  Each problem is a map carrying the `:type` keyword `assert` would have thrown, a
  human-readable `:message`, and whatever else that check knows (`:sentence`,
  `:context`, `:arg` / `:expected` / `:position` for an arg breach, `:cycle` for a
  stratification one):

    :naming                a naming invariant (predicate / individual / type / context)
    :not-ground            a fact still holding a variable
    :not-well-formed       a special predicate's structure (genl, arg, the equalities…)
    :unknown-handle        an `except` naming a handle no sentex is stored under
    :not-range-restricted  a rule variable the antecedents never bind
    :not-indexable         a rule antecedent literal whose predicate is a variable
    :disjunction-too-wide  a disjunctive antecedent that expands to more rules than
                           `rules/max-alternatives`
    :not-stratified        a cycle through negation the rule or edge would close
    :not-assertible        a `do/` imperative inside a rule
    :derived-only          a `defeat` literal, which only the engine derives
    :exception-not-closed  an exceptWhen variable no antecedent of the rule binds
    :arg-type              an arg constraint on an argument
    :arg-genl              a genlArg constraint — the argument is not a subtype of the floor
    :inter-arg-type        an interArg, interArgs or interArgAndRest constraint whose
                           trigger argument holds and whose target argument does not
    :disjoint              a type membership the taxonomy separates
    :functional            a second, irreconcilable value for a functional slot
    :asymmetric            the converse of a claim a declared-asymmetric relation made
    :anti-transitive       the two-step chain an anti_transitive relation forbids closing

  plus `:unrecovered-kb`, which is about neither the request nor the knowledge but the
  KB: every write entry point refuses one whose belief was never built over the store it opened,
  and it refuses before reading the sentence at all, so it is reported alone and first.
  Absent under `*write-unrecovered?*`, where `assert` lands the write.

  Plus three that are about the *request* rather than the knowledge: `:shape` (the
  context is neither a symbol nor a ground application, the sentence is not an
  s-expression, or it is a vector — which is how a read entry point spells a
  conjunction), `:unknown-option`
  (`opts` is not a map, an `opts` key `assert` does not read, a `:strength` that is
  not an assertable class, or a `:direction` that is unknown, on a non-rule, or
  contradicting the wrapper the sentence already carries — see `assert-opt-keys`) and
  `:not-checkable` (a top-level `do/` imperative — an instruction, which `check` will
  not run to find out what it does).

  A `:disjoint`, `:functional`, `:cover`, `:asymmetric` or `:anti-transitive` clash that
  names the other stored members of its nogood is not a problem: `assert` stores the
  sentence, and `settle` places the nogood, which `conflicts` reports when every
  member is `:monotonic` (docs/nmtms.md, \"What a refusal may rest on\").  `check`
  reports one of those types only for a clash that names no stored member.  A fact's own
  `:arg-type`, `:arg-genl`, `:inter-arg-type` or `:quoted-arg-type` conviction is not a
  problem either: `assert` stores the fact and holds it inert (docs/argtypes.md, \"An
  argument that fails its declared type is held inert\"), and `try-assert` refuses it.
  Nor is a rule's own `:arg-variable` conviction, two argument constraints on one of its
  variables that no term satisfies at once: `assert` stores the rule and holds it inert,
  and `try-assert` refuses it.  Nor is a declaration's `:arg-position` (a position past
  its predicate's bound length) or `:arg-constraint-kind` (a `genlArg` on an
  `instance_relation_predicate`): `assert` stores the declaration, a stranded one
  constrains nothing (docs/taxonomy.md, \"A declaration the arity strands\"), and
  `try-assert` refuses it.

  The stages run in `assert`'s order and stop at the first that finds anything, since
  each later one reads the KB assuming the earlier ones held.  A rule is checked the
  way `assert` checks it — every rule the polycanonicalization stores, which is one per
  alternative of a disjunctive antecedent times one per conjunct of a conjunctive
  consequent — and an `exceptWhen` is checked the same way, every one of those rules
  wrapped in the exception, with the exception's closure read against each rule's own
  antecedents.

  Three things `assert` does that `check` deliberately does not.  It does not mint a
  constant for a ground reifiable NAT, which is a write: an application that already has
  a term is checked as that term, and one that has none is read as the constant `assert`
  would mint, holding its function's `result` types (`checks/*entry-mints?*`) — what a
  rule would conclude of the new constant is not read.  A ground application in the
  context slot is checked as the `cx/` context `assert` stores in, minted or not
  (`nat/context-for-check`).  It does not evaluate an
  imperative.  And it does not chain, so a refusal raised while the assertion's rules
  fire, a `:pattern-too-costly` from an `exceptWhen` query, is `assert`'s alone; `assert`
  then takes back what the call wrote (`undoing-refusal`).  Everything else is the same
  code on the same KB."
  ([kb sentence] (check kb sentence 'CxUniverse nil))
  ([kb sentence context] (check kb sentence context nil))
  ([kb sentence context opts]
   ;; The writability refusal is first because `check-writable!` is first in `assert` —
   ;; ahead of the shape guards, so that `*bulk-load?*` cannot be the way into a state
   ;; whose dedup walk is already gone.
   ;; a whole-form `(set/monotonic S)` is `S` at `:strength :monotonic`, as in `assert`
   (let [[sentence opts peel-problem] (sx/strength-peel sentence opts)]
     (or (unrecovered-problems kb "assert")
         (some-> peel-problem vector)
         (shape-problems sentence context opts)
         (some-> (direction-opt-problem sentence opts) vector)
         ;; ...and the other wrapper `assert` peels before it splits: a strength stated on
         ;; an `exceptWhen` query, for the exception's own defeat class.  The same walk
         ;; refuses it and `(set/inert …)` anywhere else on the wrapper chain.
         (some-> (sx/exception-strength-problem sentence) vector)
         ;; From here on, the sentence `assert` would act on: the `:direction` opt
         ;; expressed as its wrapper (a no-op without one), the cardinality surface
         ;; normalized to its constraint rule, and the exception's strength peeled off,
         ;; exactly as `assert` does before it splits or stores anything.  None can throw:
         ;; `shape-problems` above answered for a malformed cardinality bound, and
         ;; `direction-opt-problem` and `exception-strength-problem` for the other two.
         (let [;; the context slot as `assert` stores it: its `cx/` constant, unminted
               context  (nat/context-for-check kb context)
               sentence (apply-direction-opt sentence opts)
               sentence (rules/normalize-solve-surface sentence)
               sentence (first (sx/peel-exception-strength sentence))]
           (cond
             (sx/do-form? sentence)
             [{:type :not-checkable :sentence sentence
               :message (str "a do/ imperative is an instruction, not a sentence — "
                             "check reports what it would assert, and this asserts nothing")}]

             ;; `(ist Ctx S)` is not stored — it finds or creates S in Ctx, so that is
             ;; what there is to check
             (= sx/ist-functor (first sentence))
             (if-let [[ctx s] (entry/ist-parts sentence)]
               (check kb s ctx opts)
               [(entry/ist-shape-problem sentence)])

             :else
             (let [[exc inner] (rules/split-exceptWhen sentence)]
               (cond
                 (and exc (sx/sentex-handle? inner))
                 (first-problems
                  [#(vec (exceptWhen-handle-problems kb inner exc))
                   #(exceptWhen-naming-problems kb exc context)
                   ;; the rest of `assert-exceptWhen-meta!`'s checks, in its order
                   #(some-> (problem (fn []
                                       (checks/check-no-imperative
                                        (sx/exceptWhen-meta exc (sx/handle-id inner)))
                                       (checks/check-no-defeat
                                        (sx/exceptWhen-meta exc (sx/handle-id inner)))
                                       (checks/check-exceptWhen-stratified
                                        kb (sx/handle-id inner) exc context)))
                            vector)])

                 exc
                 (first-problems
                  [#(some-> (rules/exceptWhen-not-a-rule exc inner) vector)
                   #(first-problems
                     (for [form (exceptWhen-rule-forms exc inner)]
                       (fn []
                         (some-> (problem (fn []
                                            (entry/check-rule-sentence kb form context)
                                            (sx/check-exception-closed
                                             (rules/antecedents (rules/inner-rule form)) exc)))
                                 vector))))
                   #(exceptWhen-naming-problems kb exc context)
                   #(check kb inner context opts)])

                 (rules/rule-sentence? (rules/inner-rule sentence))
                 (rule-problems kb sentence context)

                 ;; the application-input check first and over the sentence as written,
                 ;; where `assert` asks it, before the reify pass; then the fact as `assert`
                 ;; would store it, an application with a term read as that term and one
                 ;; without read as the constant `assert` would mint
                 :else
                 (or (some-> (problem (fn [] (check-reified-inputs! kb sentence context))) vector)
                     (binding [checks/*entry-mints?* true]
                       (fact-problems kb (nat-read/reify-existing kb sentence context) context)))))))))))

(defn- bad-handle-message
  "The refusal text for a non-handle passed where one handle belongs — shared between
  `the-handle` (which throws it) and `check-edit` (which reports it as a problem), so
  check and do disagree on nothing but the delivery."
  [handle fn-name]
  (if (sequential? handle)
    (str fn-name ": got " (count handle) " handles, not one — a rule with a"
         " conjunctive consequent is stored as one rule per conjunct and"
         " `assert` returns a handle for each.  Map over them.")
    (str fn-name ": " (pr-str handle) " is not a sentex handle")))

(defn- the-handle
  "`handle` as a handle, `nil` as itself, or a refusal saying what it got instead.

  The vector arm is the one that matters.  `assert` returns a **vector** of handles
  for a rule with a conjunctive consequent — it is split into one rule per conjunct —
  so `(retract! kb (assert kb rule ctx))`, the composition of the API's own two calls,
  hands a vector to a fn expecting one handle.  Unrefused, the record lookup misses and
  the caller gets `{:removed-sentexes 0}`, or `false`, or nil: a silent no-op that looks
  exactly like \"there was nothing to do\".

  **`nil` passes through**, and is not the same mistake.  `handle-of` answers nil for a
  sentence the KB does not hold, so `(in? kb (handle-of kb s ctx))` is an ordinary
  composition whose answer is `false` — there is no handle, so it is not
  believed.  Refusing it would turn a question with a correct answer into an error.
  What each caller does with nil is its own business; this only declines to invent one."
  [handle fn-name]
  (cond
    (integer? handle) handle
    (nil? handle)     nil
    :else
    (throw (ex-info (bad-handle-message handle fn-name)
                    {:type :bad-handle :handle handle}))))

(defn- add-entry-shape-problem
  "The `:shape` problem one `:add` entry has before its content is even looked at, or
  nil.  One fn read by both entry points — `entry-problems` reports it and `edit` throws it —
  so the dry run and the write refuse the same entry: a 4-element entry is refused
  whole rather than applied with the junk silently dropped, and a non-sequential one
  is a typed refusal rather than a bare destructure error."
  [entry]
  (cond
    (not (sequential? entry))
    {:type :shape :message (str "each :add entry must be [sentence context] or "
                                "[sentence context opts], got " (pr-str entry))}
    (not (<= 2 (count entry) 3))
    {:type :shape :message (str "each :add entry needs 2 or 3 elements, got "
                                (count entry) ": " (pr-str entry))}))

(defn- entry-problems
  "`check` of one `[sentence context opts?]` entry, with the entry's own shape checked
  first."
  [kb entry]
  (if-let [p (add-entry-shape-problem entry)]
    [p]
    (let [[sentence context opts] entry] (check kb sentence context opts))))

(def edit-batch-keys
  "Every key an `edit` batch may carry, read by `edit`, `check-edit`, `preview` and
  `edit-with-consequences` alike.  Public for the reason `assert-opt-keys` is: it is the
  answer to \"is this a real key?\"."
  #{:add :remove})

(defn- edit-batch-problem
  "The problem an `edit` batch is refused for, or nil — the value `check-edit` reports and
  `check-edit-batch!` throws, so the dry run predicts the write."
  [batch]
  (cond
    (not (map? batch))
    {:type :unknown-option :mismatch :not-a-map :batch batch :options (vec (sort edit-batch-keys))
     :message (str "an edit batch must be a map of "
                   (str/join ", " (map pr-str (sort edit-batch-keys)))
                   ", got " (pr-str batch))}
    :else
    (or (when-let [unknown (seq (sort-by pr-str (remove edit-batch-keys (keys batch))))]
          {:type :unknown-option :mismatch :unknown-key :unknown (vec unknown) :options (vec (sort edit-batch-keys))
           :message (str "unknown edit batch key" (when (next unknown) "s") " "
                         (str/join ", " (map pr-str unknown))
                         " — an edit batch reads "
                         (str/join ", " (map pr-str (sort edit-batch-keys)))
                         ".  A key nothing reads writes nothing and reports success,"
                         " and check-edit predicts no problem with it.")})
        ;; a known key holding something no entry can be pulled from — `{:add 5}` —
        ;; would raise a bare seq error out of both entry points' iteration (over the daemon,
        ;; a 500 with no `:type`), so it is a `:shape` refusal here, where both read
        (some (fn [k]
                (let [v (get batch k)]
                  (when (and (some? v) (not (sequential? v)))
                    {:type :shape k v
                     :message (str k " must be a sequence of "
                                   (if (= :add k)
                                     "[sentence context opts?] entries"
                                     "handles")
                                   ", got " (pr-str v))})))
              (sort edit-batch-keys)))))

(defn- check-edit-batch!
  "Refuse a batch that is not a map, and a batch key nothing reads.

  Both are silent otherwise, and the silence is the dangerous kind: a `{:keys [add
  remove]}` destructure of `{:adds [...]}` binds nil twice, so `edit` writes nothing and
  reports `{:added [] :removed {:removed-sentexes 0 …}}` — a success — while `check-edit`,
  the dry run whose whole job is to predict that, reports **no problems at all**.  Over
  the daemon it is a `200 {:ok true}` for a write that did not happen.

  `:adds` / `:removes` is the likely spelling, since `edit` *returns* `:added` /
  `:removed` and `preview` returns `:believed-added` / `:believed-removed` — feeding a
  result back in is indistinguishable from a no-op success."
  [batch]
  (when-let [p (edit-batch-problem batch)]
    (throw (ex-info (:message p) (dissoc p :message)))))

(defn check-edit
  "`check` over a whole `edit` batch — `{:add [[sentence context opts?] …] :remove
  [handle …]}`, the shape `edit` takes — storing nothing.

  Returns a vector of problems, empty when the batch is admissible.  Each is what
  `check` returns plus where it came from: `:in` (`:add` / `:remove`), `:index` (the
  position in that vector) and `:entry` (what was there), so a caller can point at the
  line rather than at the batch.  An `:add` is checked against the KB **as it stands**
  — an entry admissible only because an earlier entry in the same batch would have
  landed first is reported, since nothing here is stored.  A `:remove` is checked for
  being a handle at all (`:bad-handle`, the same refusal `edit` throws — a vector of
  handles included), for naming an actually stored one (`:unknown-handle`), and for the
  teardown refusal `edit!` makes of a handle with no TMS node (`teardown-refusal`); a nil
  entry reports nothing, because `edit` treats nil as nothing to remove.

  Two refusals are about the batch or the KB rather than any line in it, and each is
  reported alone: `:unknown-option` for a batch key nothing reads, and `:unrecovered-kb`
  for a KB `edit!` will refuse before reading the batch at all."
  ;; `batch` is destructured in the body rather than in the parameter vector: the
  ;; published `:arglists` is what a generated client reads to name the argument, and a
  ;; `{:keys [...]}` there names nothing.
  [kb batch]
  (if-let [p (or (unrecovered-problems kb "edit!")
                 (some-> (edit-batch-problem batch) vector))]
    ;; reported rather than thrown: this is the dry run, and a batch whose keys nothing
    ;; reads — or a KB that will refuse the whole batch before reading any of it — is
    ;; exactly what it exists to catch before `edit` silently writes nothing
    p
    (let [{:keys [add remove]} batch]
      (into (into [] (mapcat (fn [i entry]
                               (map #(assoc % :in :add :index i :entry entry)
                                    (entry-problems kb entry)))
                             (range) add))
            (keep-indexed
             (fn [i h]
               (cond
                 ;; nil is what `edit` treats as nothing to remove — `handle-of` of an
                 ;; absent sentence — so it is not a problem here either
                 (nil? h) nil
                 (not (integer? h))
                 {:in :remove :index i :entry h :type :bad-handle
                  :message (bad-handle-message h "edit")}
                 (nil? (p/get-sentex (:records kb) h))
                 {:in :remove :index i :entry h :type :unknown-handle
                  :message (str "no sentex is stored under handle " h)}

                 :else
                 (some-> (teardown-refusal kb h "edit!")
                         (assoc :in :remove :index i :entry h))))
             remove)))))

;; ---- batched assertion: settle once, not per assert ----------------------
;; Every `assert` settles belief (resolve contradictions, evaluate exceptions) after
;; storing.  Settle recomputes belief from current
;; state, so a bulk load pays that reconciliation N times for one final answer.
;; Deferring it to the end is safe *because* belief is order-independent: chaining
;; still runs per assert, so the one closing settle sees the same stored state a
;; per-assert settle would have.

(defn- batch-settle-inputs
  "What a `with-deferred-settle` batch's `:settle` frame records: whether the batch was
  written under `*bulk-load?*`, and whether a write in it would have seeded chaining from
  the `genlCx` moves its own settle drained (`settle/*batch-seeds-moves*`)."
  []
  {:bulk-load?  *bulk-load?*
   :seed-moves? (if-let [v settle/*batch-seeds-moves*] @v special/*seed-moves?*)})

(defn- closing-settle
  "The settle that closes a `with-deferred-settle` batch, under the inputs its `:settle`
  frame records (`in`, `batch-settle-inputs`), or under the batch in force when `in` is
  nil.  A batch written under `*bulk-load?*` draws no argument types over the `genlCx`
  moves it settles (`special/*entail-moves?*`), and a batch none of whose writes chained
  seeds no chaining from them (`special/*seed-moves?*`), as a settle per write would not."
  [kb in]
  (let [{:keys [bulk-load? seed-moves?]} (or in (batch-settle-inputs))]
    (binding [special/*entail-moves?*      (not bulk-load?)
              special/*release-withheld?* (and special/*release-withheld?* (not bulk-load?))
              special/*seed-moves?*        seed-moves?]
      (settle/settle kb))))

(defmacro with-deferred-settle
  "Run `body` — a batch of `assert` / `assert-rule` / `ist` calls on `kb` — with
  belief settled **once** at the end instead of after every assertion.

  A plain `assert` settles the JTMS before returning (resolve contradictions,
  evaluate `exceptWhen`); a bulk load therefore pays that
  reconciliation once per fact.  Under this macro each assertion still stores and
  forward-chains, but the `settle` is deferred, and one `settle` runs after `body`.
  The result is identical belief — settle is computed from current state, not
  accumulated, and beliefs are order-independent — for one reconciliation instead of
  N.  The closing settle chains from the `genlCx` moves it settles only when a write of
  the batch chained, so a batch of `{:chain? false}` writes chains nothing, as a settle
  per write would not.  Returns `body`'s value.

    (v/with-deferred-settle kb
      (doseq [f facts] (v/assert kb f 'CxSome))
      (v/assert-rule kb ante conseq 'CxSome))

  The taxonomy's **depth potential** is deferred with it (`taxonomy/*defer-depths?*`).
  Repairing it as each `genl` / `genlCx` edge arrives is proportional to that
  edge's descendants, so a batch that lifts high nodes re-walks their subtrees over
  and over — a cost that depends on the order the edges arrive in, which is exactly
  what a batch is entitled not to pay.  A deferred insert lifts only the edge's own
  source instead (`taxonomy/local-lift`), which keeps the potential sound for the
  parent-before-child order a hierarchy usually arrives in; an order that does break
  it leaves the relation loose, and the closing settle repairs every depth in one pass.

  A read taken **inside** `body` reads the batch unsettled, which is what deferring the
  settle means: belief for what the body just stored is what the closing settle computes,
  so a mid-batch `ask?` / `isa?` / `disjoint?` can answer through something that settle
  then defeats, blocks or sweeps.  Ask after the batch closes.

  Only the **assert** path is deferred: a `retract!` inside `body` settles eagerly
  (reviving a defeated default is not part of an assert batch).  Nesting composes —
  an inner `with-deferred-settle` is a no-op wrapper and the outermost one settles.
  Not a transaction: a throw mid-batch leaves what was already stored in place; the
  KB is still consistent (settle only did not run), so re-running or settling by
  hand recovers a clean state.  The depth potential is the one thing repaired even
  then — see below."
  [kb & body]
  ;; `outermost?` reads the flag *before* re-binding it, so a nested block sees the
  ;; enclosing `true` and skips its own settle — only the outermost one reconciles.
  `(let [kb#        ~kb
         outermost# (not *defer-settle?*)]
     ;; the write record a report reads, open before the batch's first write
     (binding [observe/*write-record*      (settle/write-record kb#)
               ;; whether a write of the batch would have seeded chaining from its moves
               settle/*batch-seeds-moves* (if outermost#
                                            (volatile! false)
                                            settle/*batch-seeds-moves*)]
       (let [res# (try
                    (binding [*defer-settle?* true
                              tax/*defer-depths?* true]
                      ~@body)
                    (catch Throwable t#
                      ;; The settle below will not run, so nothing else would ever
                      ;; repair a potential this batch left loose — and a loose
                      ;; relation makes every later `genl?` / `sees?` walk unpruned,
                      ;; for the life of the KB if nothing writes to it again.  A
                      ;; cancelled load (the catalog aborts one by throwing from its
                      ;; progress callback) leaves a KB that stays queryable, so this
                      ;; is a live path, not a hypothetical.  Repairing is cheap and
                      ;; cannot throw; belief is deliberately left unsettled, which
                      ;; is the documented state an aborted batch leaves behind.
                      (when outermost# (tax/restore-depths (reasoning/taxonomy kb#)))
                      (throw t#)))]
         ;; the closing settle is a write of its own: on a KB with an operation log it is
         ;; recorded as a `:settle` frame after the batch's writes (`vaelii.impl.oplog`)
         (when outermost#
           (dur/call-as-write
            :settle
            #(oplog/run-op kb# :settle :replay [] #'batch-settle-inputs
                           (fn [in#] (#'closing-settle kb# in#)))))
         res#))))

(defn assert-many
  "Assert every sentence in `sentences` (into one shared `context`, optional shared
  `opts`) with belief settled **once** at the end — the collection form of
  `with-deferred-settle`.  Returns the vector of handles, in input order (a sentence
  that expands to several — a conjunctive-consequent rule — contributes its vector,
  so the result is `mapv`-shaped, one entry per input sentence).

  For a bulk fact/rule load this is the fast path: N asserts, one settle.

  `:max-ms` and `:stop?` bound the whole call, read before each sentence with the heap
  mark (`chain/check-stop!`).  The sentence either one interrupts is
  rolled back as `assert` rolls one back, the sentences before it stay, settled, and the
  call throws `:interrupted` with `:stored`, their handles (docs/inference.md, *Stopping
  a run*)."
  ([kb sentences context] (assert-many kb sentences context nil))
  ([kb sentences context opts]
   (let [each   (some-> opts (dissoc :max-ms :stop? :progress-every-ms) not-empty)
         stored (volatile! [])
         cut    (volatile! nil)]
     ;; the closing settle's re-chains derive under the call's :max-depth and
     ;; :max-term-depth, as each assert's own run does
     (chain/call-with-stop
      (select-keys opts [:max-depth :max-term-depth])
      #(with-deferred-settle kb
         ;; the bound covers the asserts and not the closing settle, so the sentences
         ;; stored before an interrupted one keep their whole closure
         (try
           (chain/call-with-stop
            opts
            ;; under `:chain? false` an assert runs no agenda loop, which reads both
            (fn [] (doseq [sentence sentences]
                     (chain/check-stop!)
                     (vswap! stored conj (assert kb sentence context each)))))
           (catch clojure.lang.ExceptionInfo e
             (if (= :interrupted (:type (ex-data e))) (vreset! cut e) (throw e))))))
     (if-let [e @cut]
       (throw (ex-info (ex-message e) (assoc (ex-data e) :stored @stored) e))
       @stored))))

(defn bulk-assert-facts!
  "Load a large batch of **known well-formed, pairwise-distinct** ground facts into
  `context` on the fast path: `assert` under `*bulk-load?*` (skips the per-fact
  definitional checks — including the `arg` store query — the dedup trie-walk, and
  provenance) inside one `with-deferred-settle` (one belief reconciliation at the end),
  with `{:chain? false}` so no forward inference runs.  This is `assert-many` stripped
  of the machinery a trusted corpus import does not need — a corpus load, or the bench
  wload/w8x/w5x premise setup.

  Returns the vector of sentex handles, in input order.  The facts are stored, indexed
  and believed as loading them one-by-one with plain `assert {:chain? false}` stores
  them, because the skipped work validates or dedups.  The one difference is the
  argument-type entailments, which ride on the skipped checks: run `record-arg-types`
  after the load and the KB holds what the per-fact load holds.  The caller owns the
  two preconditions the mode trades on: every fact is well-formed (the checks would
  have passed) and no two are the same **canonical** sentence in the same context (the
  dedup would have missed).  The one canonicalization the caller cannot pre-compute — a
  symmetric literal against its stored mirror, since telling `(siblingOf Bob Ann)` from a
  stored `(siblingOf Ann Bob)` needs the `(symmetric P)` mark — this path still dedups: a
  symmetric functor keeps the trie probe (one taxonomy read per row), so a mirror resolves
  to the one stored handle rather than a second record.  Use plain `assert` / `assert-many`
  when the well-formedness or the plain-distinctness precondition is in doubt.

  `opts` flows to each `assert` (e.g. `:strength :monotonic`); `:chain?` is forced
  false, so no stored rule fires over the loaded facts.  `record-arg-types` and then
  `forward-chain` reach the KB a chained per-fact load holds, and both read the whole KB
  (docs/storage.md, \"Loading a changing snapshot over a fixed base\").

  `:max-ms` and `:stop?` bound the whole call, read before each fact with the memory
  guard's heap mark (`chain/check-stop!`).  On a stop the fact in flight is rolled back,
  the facts before it stay and are settled, and the call throws `:interrupted` with
  `:stored`, their handles, as `assert-many` does (docs/inference.md, *Stopping a run*).

  **`:on-progress` is the load's rate, and it is the only thing this entry point reports.**
  The callback is handed `{:phase :loading :done n :elapsed-ms ms :facts-per-sec r}`
  every 100,000 facts and `{:phase :done :total n :elapsed-ms ms :facts-per-sec r}`
  once the closing settle has run — so the last event covers the whole load, settle
  included, and is the number to compare across runs.  The key is `assert`'s own
  (`assert-opt-keys`), where it names the *chaining* callback; here it cannot mean that,
  since `:chain? false` is forced and no chaining runs, so it is read at this entry point and
  not passed down.  What one fact costs, phase by phase: docs/storage.md, \"What a bulk
  load costs\"."
  ([kb facts context] (bulk-assert-facts! kb facts context nil))
  ([kb facts context opts]
   ;; the `assoc` waits for `assert`'s own opts guard: run on a non-map it threw a
   ;; bare cast error where every other entry point answers `:unknown-option`
   (check-assert-opts! opts)
   (let [on-progress (:on-progress opts)
         bound       (select-keys opts [:max-ms :stop? :progress-every-ms])
         opts        (-> opts (dissoc :on-progress :max-ms :stop? :progress-every-ms)
                         (assoc :chain? false))
         t0          (System/nanoTime)
         event       (fn [m done]
                       (let [ms (/ (- (System/nanoTime) t0) 1e6)]
                         (on-progress (assoc m :elapsed-ms ms
                                             :facts-per-sec (if (pos? ms)
                                                              (/ (double done) (/ ms 1000.0))
                                                              0.0)))))
         stored      (volatile! (transient []))
         cut         (volatile! nil)
         one!        (fn [f]
                       (chain/check-stop!)
                       (vswap! stored conj! (assert kb f context opts)))]
     (binding [*bulk-load?* true]
       (with-deferred-settle kb
         ;; the bound covers the asserts and not the closing settle, so the facts stored
         ;; before the stop are settled
         (try
           (chain/call-with-stop
            bound
            #(with-open [r (progress/start ::bulk-assert-facts
                                           "bulk load: assert the facts"
                                           (when (counted? facts) (count facts)))]
               ;; the counting arm only when somebody is listening: a load with no
               ;; callback pays nothing for the option it did not pass
               (if on-progress
                 (let [n (volatile! 0)]
                   (run! (fn [f]
                           (one! f)
                           (let [i (vswap! n inc)]
                             (progress/tick! r)
                             (when (zero? (rem i 100000))
                               (event {:phase :loading :done i} i))))
                         facts))
                 (run! (fn [f] (one! f) (progress/tick! r)) facts))))
           (catch clojure.lang.ExceptionInfo e
             (if (= :interrupted (:type (ex-data e))) (vreset! cut e) (throw e))))))
     (let [hs (persistent! @stored)]
       (when-let [e @cut]
         (throw (ex-info (ex-message e) (assoc (ex-data e) :stored hs) e)))
       ;; after `with-deferred-settle` returns, so the closing reconciliation is inside
       ;; the rate rather than outside it
       (when on-progress (event {:phase :done :total (count hs)} (count hs)))
       hs))))

(defn record-arg-types
  "Record the argument-type memberships and `genl` edges the stored facts entail, over a
  store loaded without them — a dump import, a `*bulk-load?*` load or
  `bulk-assert-facts!` — and settle.  Returns `{:facts n :recorded n :violations n}`:
  the facts read, the records created, and the derivations the ledger reports.

  `assert` derives these as each fact arrives (docs/argtypes.md), and `recover` rebuilds
  belief from the stored justifications without deriving any, so a store loaded around
  `assert` holds its facts and none of what their declarations say about them.  One run
  after the load, on the recovered or reindexed KB, records them: the store then holds
  what loading the same facts one by one holds, and a later write draws nothing over a
  term it touches that the store did not already hold.  Idempotent, so a second run
  records nothing.  Under `VAELII_ASSERTIVE_ARG_TYPES=0` nothing is derived and nothing
  is recorded.  It runs no forward chaining from what it records: `forward-chain` after
  it fires the stored rules over the memberships.

  The facts are drawn per declared functor in content order, each functor's by handle,
  and the run ends with nothing owed (`arg-types-owed`).  `record-arg-types!` draws the
  same facts in the same order and can stop, resume and set a fact aside."
  [kb]
  (let [res (argpass/run-all kb)]
    (viol/report kb (:violations res))
    (settle/settle kb)
    (argpass/clear-owed! kb)
    {:facts (:facts res) :recorded (:recorded res) :violations (count (:violations res))}))

(defn record-arg-types!
  "`record-arg-types` as a run that can stop and resume, for a store where the pass takes
  hours: each fact's checks run under a budget, a stop lands at a fact boundary, and what
  the pass still owes is kept in the store (`arg-types-owed`), so the next call resumes
  it, under this engine or a later one.  docs/argtypes.md, \"The pass over a stored KB\".

  `opts`:

    `:resume?`           default true: carry on from what the store says is owed, or from
                         the start when nothing is.  false starts from the start.
    `:budget-ms`         default 2000: how long one fact's checks may run.  A fact past
                         it is **set aside** — recorded as owed with the part of the checks
                         that ran out (`:phase`) — and the pass moves on.  nil: no budget.
    `:retry-deferred?`   default false: once the sweep has ended, draw each fact set
                         aside again, under this call's `:budget-ms`.
    `:stop?`             a function of no arguments; truthy stops the pass at the next
                         fact.  `request-stop!` and a shutdown stop it the same way.
    `:on-progress`       called at most every `:progress-every-ms` (default 1000) with
                         `{:phase :done :total :recorded :deferred}`.  `:phase` is
                         `:arg-types` (facts drawn of every fact the declared functors
                         hold), `:releases` (the withheld mints owed by the settles of an
                         open or a recover, `release-withheld!`), `:deferred` (facts set
                         aside, drawn again), `:settle` and `:done`.  A throw from it stops
                         the pass as a stop does, and is rethrown once the pass has
                         committed: a browser job's cancel.
    `:commit-every-ms`   default 30000: how long the pass draws between two commits.

  **A commit** files the violations drawn, settles, forces the stores to disk and then
  writes the owed record, so a stop, a cancel or a throw leaves a settled KB and a
  record no further on than the mints on disk.  A process killed between two commits
  loses no stored mint: once belief is rebuilt (`recover`, or `settle-record-edits!`),
  the next call redraws from the last commit, which adds nothing to what was drawn
  after it.  An owed record written after the records the store holds — a store
  restored from an older copy — is refused (`:owed-record-ahead`).

  Returns `{:drawn :done :total :recorded :violations :deferred :stopped :complete?}`:
  facts drawn by this call, facts drawn of `:total`, records created, violations filed,
  facts set aside still owed, nil or why it stopped (`:requested`, `:shutdown`,
  `:cancelled`), and whether nothing is owed now.  Refuses a KB without belief
  (`:unrecovered-kb`)."
  ([kb] (record-arg-types! kb nil))
  ([kb opts]
   (opts/check! opts #{:resume? :budget-ms :retry-deferred? :stop? :on-progress
                       :progress-every-ms :commit-every-ms}
                "record-arg-types!"
                "A key nothing reads would run the pass at a setting nobody chose.")
   (opts/check-values! opts "record-arg-types!")
   (check-writable! kb "record-arg-types!")
   (argpass/run-pass! kb (cond-> (or opts {})
                           (not (contains? opts :budget-ms)) (assoc :budget-ms argpass/default-budget-ms)))))

(defn request-stop!
  "Ask the `record-arg-types!` pass running over `kb` to stop at its next fact boundary,
  from any thread.  True when a pass was running, false when none was; a request is not
  held for a later pass."
  [kb]
  (argpass/request-stop! kb))

(defn arg-types-owed
  "What the argument-type pass still owes over `kb`, or nil when nothing: `{:facts :total
  :swept? :deferred}` — the facts drawn and counted at its last commit, whether its sweep
  over the declared functors has ended, and the facts set aside, each `{:fact :functor
  :reason :phase :budget-ms :ms}`.  A removal from the records of a KB without belief
  (`edit-records!`) makes the whole pass owed; `record-arg-types` and a
  `record-arg-types!` run that completes leave nothing owed."
  [kb]
  (argpass/owed kb))

(defn owed-releases
  "How many departures and arrivals the settles of an open, a recover, an upgrade or a
  bulk load left owed: the general argument-type mints a departed specific membership had
  withheld are not drawn until `release-withheld!` runs, so the KB may miss them.  A close
  and a reopen keep the count (docs/argtypes.md, \"Nothing records a withheld mint\")."
  [kb]
  (special/owed-releases kb))

(defn release-withheld!
  "Draw the mints the owed departures and arrivals (`owed-releases`) can have withheld,
  chain from them and settle.  Returns `{:terms n :released n :ms n}`: the terms whose
  mints were drawn again, the records drawn and the wall time.  Nothing runs it
  implicitly; a second run draws nothing."
  [kb]
  (let [t0 (System/nanoTime)
        r  (special/release-withheld! kb)]
    (settle/settle kb)
    (when (seq (:new r))
      (settle/rechain-seeds kb (special/minted-seeds kb (:new r)))
      (settle/settle kb))
    {:terms (:terms r) :released (:released r) :ms (long (/ (- (System/nanoTime) t0) 1e6))}))

(def ^:private forward-chain-opt-keys
  "Every key `forward-chain` hands the chaining fixpoint (`chain/chain-all`'s
  destructure) — the key set `check-forward-chain-opts!` holds an opts map to."
  #{:max-depth :max-term-depth :max-derivations :max-ms :on-progress :progress-every-ms
    :stop? :on-stop})

(defn- check-forward-chain-opts!
  "Refuse an opts key `forward-chain` does not read, and a non-nil non-map `opts` —
  `check-assert-opts!`'s reasoning at this entry point.  Every key here sets a *bound* or
  reports progress on one, so the silent-default failure is a run with no ceiling:
  `{:max-derivation n}` reads as no key at all and the chain runs unbounded, which on a
  KB with a productive rule set is precisely what the option was written to prevent."
  [opts]
  (opts/check! opts forward-chain-opt-keys "forward-chain"
               (str "An option nothing reads takes the default in silence,"
                    " which for a bound means running unbounded."))
  ;; and the value domains beside the key set: a string `:max-depth` / `:max-derivations`
  ;; reaches the fixpoint's arithmetic and throws bare, and a non-fn `:on-progress` a bare
  ;; cast on the first report — both refused here as `:unknown-option` instead
  ;; (`opts/bound-domains`)
  (opts/check-values! opts "forward-chain"))

(defn- progress-interrupts
  "`on-progress` as `forward-chain` hands it to the run under `:on-stop :rollback`: a throw
  out of it becomes `:interrupted` with `:bound :on-progress`, carrying the throw as its
  cause, so the caller's cancel takes the rollback every other bound takes."
  [on-progress]
  (fn [m]
    (try (on-progress m)
         (catch Throwable t (chain/interrupted! :on-progress t)))))

(defn forward-chain
  "Run forward chaining to a fixpoint over every believed sentex, then settle
  belief (resolve contradictions).  Returns {:derived n :truncated? bool}, with `:bound`
  naming what ended a run kept under `:on-stop :keep`: `:max-derivations`, `:max-ms` or
  `:stop?`.

  `opts`: `{:max-depth n :max-term-depth n :max-derivations n}` bound the run
  (`default-chain-opts`); a run in which `:max-term-depth` refused firings also returns
  `:term-cut`, their count.  A run in which `:max-depth` refused a firing is not stopped:
  it returns `:truncated? true` with no `:bound`.
  `:on-progress` is a callback the fixpoint calls about four times a second
  (`:progress-every-ms`) with `{:derived n :pending n}`, the only progress report from a
  phase that otherwise says nothing for minutes.  It may throw to stop the run.

  `:max-ms` bounds the call by wall-clock milliseconds, and `:stop?` is a function of no
  arguments, asked at most every `:progress-every-ms`, whose truthy answer ends the call.
  `:on-stop` says what a stop leaves (docs/inference.md, *Stopping a run*):

  - `:rollback`, the default: a run that `:max-ms`, `:stop?`, `:max-derivations` or an
    `:on-progress` throw ends throws `:interrupted` with `:bound` naming it, the throw as
    the cause for `:on-progress`, and leaves the KB as the call found it, the handle
    counter aside.
  - `:keep`: the run keeps what it placed, is settled, and returns `:truncated? true`; an
    `:on-progress` throw is rethrown as raised after the settle.  A kept run is
    incomplete: under `:default` rules it can leave a conclusion believed whose defeater
    the run did not derive.  A later `forward-chain` with no bound completes the closure.

  A nearly full heap (`caches/heap-critical?`) ends the run with `:interrupted :bound
  :heap` and the rollback under either value, except during a replay of the logged
  frame (`oplog/*replaying?*`), which takes no heap stop.

  An `opts` key this fn does not read is **refused** (`:unknown-option`): every key
  here bounds the run or reports on it, so a misspelt one is a run with no ceiling."
  ([kb] (forward-chain kb nil))
  ([kb opts]
   (check-forward-chain-opts! opts)
   (let [keep?  (= :keep (:on-stop opts))
         cb     (:on-progress opts)
         thrown (volatile! nil)
         opts   (cond-> (dissoc opts :on-stop)
                  (and cb keep?)       (assoc :on-progress
                                              (fn [m] (try (cb m)
                                                           (catch Throwable t
                                                             (vreset! thrown t)
                                                             (throw t)))))
                  (and cb (not keep?)) (assoc :on-progress (progress-interrupts cb)))
         result (undoing-refusal
                 kb opts
                 (fn []
                   ;; every record the run creates is above the mark
                   (entry/take-write-mark! kb)
                   (let [result (binding [chain/*keep-on-stop* keep?]
                                  (try (chain/chain-all kb (jtms/in-datums (reasoning/tms kb))
                                                        opts)
                                       (catch Throwable t
                                         (if (identical? t @thrown) nil (throw t)))))]
                     ;; a replay runs the frame without the clock, and so past where a
                     ;; kept run cut
                     (when (and keep? (:oplog kb) (or @thrown (chain/stop-reached?)))
                       (oplog/mark-unusable! (:oplog kb) [:interrupted :forward-chain]))
                     (chain/call-unbounded #(settle/settle kb))
                     result)))]
     (if-let [t @thrown] (throw t) result))))

;; ---- the query family: which one to reach for ---------------------------
;; Five entry points answer a goal, and the axis that separates them is **how much
;; rule expansion each is willing to do**.  Pick by what you are asking:
;;
;;   query / query?     THE DEFAULT.  One entry point with one dial: no `:max-depth` and it
;;                      is `ask`; a `:max-depth` and it is the node engine, bounded
;;                      at that many rewrites.  Sentence or vector goal.
;;                      → binding maps
;;   ask / ask?         The prover registry alone — facts, the taxonomy closures,
;;                      transitivity, disjointness, inverse/symmetric metadata,
;;                      evaluable arithmetic, NAF, arg type inference.  Expands
;;                      **no rule**, so its cost is a property of the goal.
;;                      → binding maps
;;   prove / provable?  The *unbounded* backward chainer: rule expansion over the
;;                      registry, so a literal it does not rewrite answers as `ask`
;;                      answers it, terminating on the data rather than on a
;;                      bound.  Takes a VECTOR goal = a conjunctive query whose
;;                      shared variables join.  → a vector of binding maps
;;   sentexes-matching  "What *stored, believed* literals match this pattern?"  No
;;                      inference, no subtype expansion — a belief-filtered index
;;                      read.  Use to retrieve facts, not to reason.  → sentex maps
;;   lookup / escalate  Diagnostics, not routine querying: answer at one explicit
;;   / explain-levels   level of the 8-level stack, find the cheapest level that
;;                      answers, or show what every level yields.  → level maps
;;
;; **Only two things backchain**, and they differ in what stops them: `prove` and
;; level 7 stop when the data runs out, the node engine (`query` with a depth) stops
;; at the depth.  Nothing else in this file expands a rule — which is what lets the
;; closed-world readers run the registry from inside a relabel loop.
;;
;; Result shapes differ by family: `sentexes-matching` and the extent/term readers return
;; **sentex maps** (`{:id :sentence :context ...}`); `query` / `ask` / `prove`
;; return **binding maps** (`{?x val ...}`); `lookup` returns
;; **level-result maps** (`{:level :handle :sentence :context :bindings}`).

;; ---- one spelling, one meaning, at every read entry point -----------------------
;;
;; A **top-level vector is a conjunction**.  That is the rule the query family already
;; runs on (`quasiquote/prepare-conjunction-for-read`, `plan/explain`, the `::goal` spec: `seq?`, or a vector
;; of them), and the write entry point states it as its own refusal — `[likes Tom Ann]` is not
;; a sentence, because the same spelling is a join at `query` / `prove`
;; (`sentence-shape-problem`).
;;
;; The read entry points split into two families and the rule has to reach both, since it is
;; the *pair* that made one spelling answer two ways.  `ask` / `ask?` /
;; `sentexes-matching` / `handle-of` read **one sentence**: handed a vector they
;; canonicalized it to the list it looks like, so `[likes Tom Ann]` was answered `true`
;; where `prove` and `query` joined over three symbols and answered nothing — and,
;; the other way round, a real conjunction `[(dog ?y) (parentOf Tom ?y)]` flattened into
;; a sentence nothing matches and came back **false**, which is the same defect wearing
;; the answer a caller is least likely to question.  So a vector is refused at those
;; entry points, and at the conjunction entry points every conjunct has to be a sentence.  Either way
;; the answer is a `:shape` refusal rather than a number nobody can check.
;;
;; `lookup` is the one read that means a third thing by a vector — at level 0 it is an
;; index path (its own docstring says so) — and is deliberately not guarded here.

(defn- sentence-spelled-as-a-vector
  "The list a vector goal was meant to be, when that is what it plainly is — every
  member a term rather than a sentence, which is `[likes Tom Ann]`.  Nil for a vector
  that holds sentences, since `((p ?x) (q ?x))` is not what its author meant by
  `[(p ?x) (q ?x)]` and a refusal that says otherwise sends them backwards."
  [goal]
  (when (and (seq goal) (not-any? seq? goal))
    (apply list goal)))

(defn- disjunctive-goal-problem
  "The `:shape` problem a goal carrying an `or` is refused with, or nil.

  **A query is not expanded, and a rule is** — the asymmetry is the whole of this
  refusal.  A disjunctive rule *antecedent* is polycanonicalized once, at the write
  entry point, into one stored rule per alternative (`rules/expand-rule`); a disjunctive goal
  would have to be expanded at every read, into a union of conjunctive queries, and
  `quasiquote/prepare-conjunction-for-read` normalizes to **one** conjunction that every reader downstream
  takes as one: the planner orders it once (`query-plan` shows *the* chosen order), the
  node engine walks one frontier, `abduce` grants over one goal, and `read-in-context`
  resolves one placement.  A union is a different shape for all five, and answering it
  at `prove` alone while `query-plan` and `abduce` refused it would be a disjunction
  that means something different at each entry point — worse than one that means nothing at
  any.

  So the union is the caller's to take, and it is two lines: run the query once per
  alternative and concatenate.  Where the disjunction is knowledge rather than a
  one-off question it belongs in a rule, which *is* expanded — assert
  `(implies (or A B) C)` and ask for `C`.

  A function's correspondences are not a written `or`: the conjunctions they give
  (`quasiquote/goal-alternatives`) are merged by `prove`, `provable?` and `query`, and the
  readers that report on one search refuse more than one as `:shape` (docs/nat.md)."
  [goal]
  (when-let [d (sx/some-form sx/disjunction? goal)]
    {:type :shape :goal goal :disjunction d
     :message (str "or cannot stand in a goal: " (pr-str d)
                   " — a read normalizes to one conjunction, which the planner orders"
                   " once and every engine walks as one, so a disjunctive goal would"
                   " have to be a union of queries rather than a query.  Run the query"
                   " once per alternative and concatenate the answers, or assert the"
                   " disjunction as a rule antecedent — a rule is stored one per"
                   " alternative — and ask for its conclusion instead")}))

(defn- sentence-goal-problem
  "The `:shape` problem a read entry point that takes **one sentence** refuses a top-level
  vector — or a goal carrying an `or` — with, or nil.  `ask`, `ask?`, `ask-within`, `sentexes-matching` and
  `handle-of` read one, so the vector spelling would mean at this entry point what it means at
  no other — and it comes in both directions, a sentence written as a vector and a real
  conjunction handed to an entry point that cannot join.  The message names which one arrived.

  The `or` refusal rides along because every entry point that runs this one takes a goal, and
  `disjunctive-goal-problem` says why a goal is the one place a disjunction is not
  expanded."
  [goal]
  (or
   (disjunctive-goal-problem goal)
   (when (vector? goal)
     {:type :shape :goal goal
      :message (if-let [as-list (sentence-spelled-as-a-vector goal)]
                 (str "the goal must be a list, not a vector: " (pr-str goal)
                      " — a vector is how `query` and `prove` spell a conjunction, so this"
                      " spelling asks one sentence here and a join over " (count goal)
                      " there.  Write the sentence as a list: " (pr-str as-list))
                 (str "this entry point reads one sentence, and " (pr-str goal)
                      " is a conjunction — a vector goal is its " (count goal)
                      " members joined on the variables they share.  Ask it with `query`"
                      " or `prove`, which join, or ask one of its conjuncts here"))})))

(defn- conjunction-goal-problem
  "The `:shape` problem a read entry point that takes a **conjunction** refuses a vector goal
  whose conjuncts are not sentences with, or nil.  `prove`, `query`, `query-plan`,
  `prove-within` and `abduce` join a vector's members as separate goals, so a sentence
  written as a vector — `[likes Tom Ann]` — is three goals, none of them a sentence and
  none of them anything the KB can hold, and the join answered nothing at all.  An empty
  vector stays legal: it is the empty conjunction, and it proves trivially.

  The test is `some`, not `when-some` over the first offender, because **`nil` is a
  conjunct too**.  `when-some` reads the *value* found, so a `nil` member and no member
  at all are one answer to it, and `[(dog ?x) nil]` would pass the guard and then answer
  nothing — a real conjunct silently zeroed, which is exactly the number nobody can check
  the guard exists to refuse.  `false` and `[]` are caught either way; `nil` is the only
  spelling the value test loses.

  The `or` refusal rides along for the reason it rides on `sentence-goal-problem`: a
  conjunct may disjoin as easily as a whole goal may, and `disjunctive-goal-problem`
  says why neither is expanded."
  [goal]
  (or
   (disjunctive-goal-problem goal)
   (when (and (vector? goal) (some #(not (seq? %)) goal))
     (let [bad (first (remove seq? goal))]
       {:type :shape :goal goal :conjunct bad
        :message (str "a vector goal is a conjunction, so every conjunct must be a"
                      " sentence: " (pr-str bad) " is not, in " (pr-str goal) "."
                      (if-let [as-list (sentence-spelled-as-a-vector goal)]
                        (str "  Write one sentence as a list: " (pr-str as-list))
                        "  Write each conjunct as a list."))}))))

(defn- ist-goal
  "`[goal context]` for a read whose goal may be an `(ist Ctx S)` — the sentence to ask,
  and the context to ask it in.  An `(ist Ctx S)` goal asks S in Ctx, the named context
  winning over `context` as it does at `assert` (docs/contexts.md#ist-find-or-create-in-a-context).
  Refuses a wrong-arity `ist` with `ist-shape-problem`'s `:shape`, and an `(ist …)`
  conjunct of a vector goal with `:not-well-formed`.  A `lookup` index path is a vector of
  keywords and symbols, so the conjunct scan reads no literal in it.

  The context is reified in read mode (dedup, never mint): a `(CxTimeFn …)` resolves to
  the `cx/` constant `assert` minted, and a never-seen one to the `no-match` symbol, which
  answers empty (docs/context-nat.md)."
  [kb goal context]
  (letfn [(reic [ctx] (nat/maybe-reify-context kb ctx false))]
    (cond
      (vector? goal)
      (do (when-let [bad (first (filter #(and (sequential? %) (seq %)
                                              (= sx/ist-functor (first %)))
                                        goal))]
            (throw (ex-info (str "an (ist Ctx S) conjunct would ask one literal of a join in"
                                 " its own context: " (pr-str bad) " — ask the whole"
                                 " conjunction in Ctx instead, or make S visible where it"
                                 " is asked")
                            {:type :not-well-formed :sentence bad :goal goal})))
          [goal (reic context)])

      (and (sequential? goal) (seq goal) (= sx/ist-functor (first goal)))
      (if-let [[ctx s] (entry/ist-parts goal)]
        [s (reic ctx)]
        (check-shape! (entry/ist-shape-problem goal)))

      :else [goal (reic context)])))

(defn- checked-ist-goal
  "`ist-goal`, refusing a query context left after the `ist` resolution with
  `:unsupported-context`: for an entry point that does not go through `read-in-context`,
  where a query context would reach the engine as a context nothing is stored in and
  answer empty."
  [kb goal context]
  (let [[goal ctx :as resolved] (ist-goal kb goal context)]
    (when (nm/query-context? ctx)
      (throw (ex-info (str ctx " is a query context, and this read does not resolve one — "
                           "it would reach the engine as an ordinary context nothing is "
                           "asserted in, and answer empty.  The reads that take one are "
                           "query, ask, prove, sentexes-matching and their ? variants.")
                      {:type :unsupported-context :context ctx :goal goal})))
    resolved))

(defn- stored-context
  "The context `assert` stores `sentence` in when it is written in `context`
  (`assert-entry/storage-context`), for a read that looks a sentence up where it is
  stored: CxUniverse for a forced-decontextualized predicate.  A variable, a query
  context and a non-symbol are returned as given, so the read's own context check
  refuses or resolves them."
  [kb sentence context]
  (if (and (symbol? context) (not (sx/variable? context)) (not (nm/query-context? context)))
    (entry/storage-context kb (nm/functor (rules/inner-rule sentence)) context)
    context))

(def ^:private wildcard-context
  "The marker every unscoped retrieval matches a sentex's context slot against, whatever
  variable the caller named the context (`captured-marker-problem`)."
  '?ctx)

(defn- captured-marker-problem
  "The `:shape` problem a goal spelling `?ctx` is refused with on an unscoped read, or nil:
  retrieval would bind that variable to the context slot rather than to its argument.  A
  named context reads such a goal correctly, and renaming the context variable leaves the
  goal's `?ctx` captured (docs/contexts.md#the-query-contexts-reading-modes-wearing-a-contexts-spelling)."
  [goals]
  (when (contains? (or (sx/symbols-where sx/variable? goals) #{}) wildcard-context)
    {:type :shape :goal goals
     :message (str wildcard-context " is the marker an unscoped read matches the context "
                   "slot against, so a goal cannot also use it as a variable — it would "
                   "come back bound to the context rather than to its argument.  Rename "
                   "it, or name a context to read in.")}))

(defn- read-context-shape-problem
  "The `:shape` problem a read is refused with when its context is not one, or nil.

  The read side takes **more** than the write side — a variable stands for the reader to be
  found, and the three query contexts name a way of reading — and all of those are symbols,
  so one `symbol?` covers them and the fast path pays a type test.  What is left is the
  compound, admitted only when it reifies: a ground application whose head CxUniverse
  believes a `(result F context)` of (`nat/readable-context-application?`).  A write admits
  every ground application, and stores it in a `cx/` context no read names until the
  declaration is believed.

  Unrefused it answered **empty**.  `(CxTimeFn ?t)` is not ground so it names no context,
  `(CxBogusFn Q)` is declared to denote none, and a read at something that names no
  context finds nothing — silently, and looking exactly like a true negative."
  [kb context]
  (when-not (or (symbol? context) (nat/readable-context-application? kb context))
    {:type :shape :context context
     :message (if (nat/context-application? context)
                (str "the context " (pr-str context) " is read only while " nat-read/universal-context " believes "
                     (pr-str (list 'result (first context) nat/context-type))
                     ", and it does not")
                (str "the context to read in must be a symbol — a context, a variable, or a "
                     "query context — or a ground application headed by a symbol "
                     "(CxTimeFn …), got " (pr-str context)))}))

(defn- read-in-context
  "Run `run-at`, a read as a fn of the context to run it in, resolving a query context
  first so the engine never sees one (docs/contexts.md#the-query-contexts-reading-modes-wearing-a-contexts-spelling):

  - `CxEverything` reads at the wildcard under `res/*belief-blind*`;
  - `CxNothing` is passed through unchanged;
  - `CxInference` and a variable context take the joint reading (`vantage/answers`, or
    `vantage/fan-distinct` under `:records?`).

  `goals-of` is the conjunction as prepared at a given context, and only a joint read or
  the wildcard calls it.  `:expands-rules?` says the read may expand a rule."
  [kb goals-of context run-at {:keys [records? expands-rules?]}]
  (check-shape! (read-context-shape-problem kb context))
  (letfn [(unscoped-goals []
            ;; every branch below that reads at the marker comes through here, so the
            ;; refusal cannot be forgotten by one of them
            (doto (goals-of wildcard-context) (#(check-shape! (captured-marker-problem %)))))
          (joint [witness]
            (let [gs (unscoped-goals)]
              (if records?
                (vantage/fan-distinct kb gs run-at)
                (:answers (vantage/answers kb gs run-at
                                           {:expands-rules? expands-rules?
                                            :witness        witness
                                            :prepared-at    goals-of})))))]
    (case context
      CxEverything (do (unscoped-goals)
                       (res/blind-seq (binding [res/*belief-blind* true]
                                        (run-at wildcard-context))))
      CxNothing    (run-at 'CxNothing)
      CxInference  (joint 'CxInference)
      (if (sx/variable? context)
        (joint context)
        (run-at context)))))

(defn- read-alternatives
  "Answer `goal` by `read-alt`, a read as a fn of `goals-in` (the goal prepared at a
  context, `read-in-context`'s `goals-of`), once per conjunction the goal reads through
  the correspondences (`quasiquote/goal-alternatives`, docs/nat.md, The corresponding
  predicate).  One conjunction answers as `read-alt` does.  Several merge their answers:
  each projected onto the variables every conjunction binds, distinct, at most
  `max-results` (nil: every one).  `context` is the read's."
  [kb goal context max-results read-alt]
  (let [alts     (quasiquote/goal-alternatives kb goal context)
        goals-in (fn [alt] #(quasiquote/prepare-goal-for-read kb alt %))]
    (if (= 1 (count alts))
      (read-alt (goals-in (first alts)))
      (let [vars (reduce #(into #{} (filter %2) %1)
                         (set (sx/form-variables (first alts)))
                         (map #(set (sx/form-variables %)) (rest alts)))
            proj (fn [a] (if (contains? a :bindings)
                           (update a :bindings select-keys vars)
                           (select-keys a vars)))]
        (cond->> (distinct (mapcat #(map proj (read-alt (goals-in %))) alts))
          max-results (take max-results)
          true        vec)))))

(defn sentexes-matching
  "*Believed* sentexes matching `sentence` in `context` (context defaults to ?ctx).
  Literal (no subtype expansion); use `isa?` / rules for taxonomic queries, or `ask`
  for full inference (see the query-family guide above).  Belief-sensitive: a
  stored-but-disbelieved sentex (a defeated default) is excluded — use
  `sentex`/`find-sentexes` for raw introspection.

  Returns a seq of **sentex maps**.  The stable contract is the map keys — `:id`
  (the handle), `:sentence` (a negative literal's is `(not S)`), `:context`, and for a
  rule `:antecedent` / `:consequent` / `:engines` / `:effect` — so key into the result.  The concrete record type
  (`vaelii.impl.types.sentex/LiteralSentex` / `RuleSentex`) is an internal detail: do not `instance?`-
  test it or rely on it, only its keys.

  **The seq is lazy, over live state.**  Matches are fetched as it is walked, which is
  what lets a consumer bound an open pattern — `(take n (sentexes-matching kb '(?p T ?y)))`
  fetches n records, not the term's whole neighbourhood — and it means a seq held
  across a write yields what is stored when it is walked.  `vec` it to fix the answer;
  the daemon's wire does so for every remote caller.  Beside a writer thread the answer
  is still not one state's: the walk reads the index postings and then belief per
  candidate, so a write landing between the two reads can leave out a match every state
  held (docs/storage.md, \"The single-writer contract\").

  A ground reifiable NAT in the goal is reified to its existing constant first (dedup,
  never mint), so it matches the stored atomic form; an unknown NAT matches nothing.

  An `(ist Ctx S)` sentence asks S in Ctx, the named context winning over `context`
  (`ist-goal`).  A named context reads a `forced_decontextualized_predicate`'s facts in
  CxUniverse, where `assert` stores them (`stored-context`).  A **vector** pattern is
  refused (`:shape`): this entry point reads one sentence, and a vector is a conjunction
  at `query` / `prove`."
  ([kb sentence] (sentexes-matching kb sentence '?ctx))
  ([kb sentence context]
   (check-shape! (sentence-goal-problem sentence))
   (let [[sentence context] (ist-goal kb sentence context)
         sentence           (nat-read/maybe-reify-for-read kb sentence context)
         context            (stored-context kb sentence context)]
     (read-in-context kb (fn [_] [sentence]) context
                      #(kb/sentexes-matching kb sentence %)
                      {:records? true}))))

(defn ist
  "The ist operation: find or create sentence `s` in context `ctx`, returning its
  handle.  `(ist ctx s)` given to `assert` does the same — ist is never stored."
  [kb ctx s]
  (assert kb s ctx))

(defn- lookup-context-shape-problem
  "The `:shape` problem `handle-of` refuses a context with, or nil — read after the `ist`
  resolution, so a ground context-function application has been reified to its constant
  (or to the `no-match` symbol) and a query context has been refused already.  What is
  left to refuse is a non-symbol — nil, a number, a non-ground `(CxFn …)` or one no
  believed `(result CxFn context)` declares — and a variable, which on a read means \"in
  some context\" and so names no one stored sentex."
  [context]
  (cond
    (not (symbol? context))
    {:type :shape :context context
     :message (str "handle-of looks a sentence up in one context, and the context must be a"
                   " symbol naming it, or a ground application of a function some reader"
                   " believes a (result F context) of, got " (pr-str context))}

    (sx/variable? context)
    {:type :shape :context context
     :message (str "handle-of answers the one sentex stored in a context, and " context
                   " is a variable, which names every context.  Name the context, or ask"
                   " sentexes-matching, which reads a variable context")}))

(defn- exceptWhen-handle
  "The handle of the meta-sentex the `exceptWhen` halves `exc` and `inner`
  (`rules/split-exceptWhen`) store in `context`, or nil: the rule found as `assert`
  stores it, and the exception aligned to it as `assert` aligns it
  (`entry/aligned-exception`).  nil for a rule `assert` stores as several, whose
  exceptions are one meta-sentex each."
  [kb exc inner context]
  (let [[h vm] (if (sx/sentex-handle? inner)
                 (let [h (sx/handle-id inner)] [h (:varmap (p/get-sentex (:records kb) h))])
                 (let [[form more] (rules/expand-rule inner)]
                   (when-not more
                     (when-let [h (kb/find-sentex-handle kb form context)]
                       [h (:varmap (res/kb-sentex kb (rules/inner-rule form) context))]))))]
    (when vm
      (kb/find-sentex-handle kb (sx/exceptWhen-meta (entry/aligned-exception exc vm) h) context))))

(defn handle-of
  "The handle of the sentex already storing `sentence` in `context`, or **nil**.

  The non-creating counterpart to `ist`.  `ist` is find-*or-create*, so using it to
  ask whether something is stored silently asserts it — and then retracting \"it\"
  retracts a sentex the caller just made.  This asks without writing, which is what
  you want to turn a sentence into a handle for `retract!`, `in?`, `why`, or
  `supporting-justifications`.

  Storage, not belief: a stored-but-defeated sentex still has a handle and is
  returned.  Test belief with `in?`, or use `sentexes-matching` (which filters it).

  Either spelling of a **ground** symmetric literal finds the one sentex the pair is
  stored as, `(siblingOf Ann Bob)` and `(siblingOf Bob Ann)` alike — the sort is what the
  store and the lookup both go through, and a row written before the `(symmetric P)`
  declaration was re-spelled by it (docs/canonicalization.md).

  An `(exceptWhen <query> <rule>)` sentence answers the handle of the exception's own
  meta-sentex, the handle `assert` returns for it, so `retract!` on it removes the
  exception and leaves the rule (docs/exceptions.md).  A whole-form `(set/monotonic S)`
  answers the handle of `S`, the sentex `assert` stores for it, inside an `ist` too.

  Being ist's counterpart, it reads an `(ist Ctx S)` sentence the way `ist` writes one:
  S is looked up in Ctx, which wins over `context` (`ist-goal`).  A fact on a
  `forced_decontextualized_predicate` is looked up in CxUniverse, where `assert` stores it
  whatever context it names (`stored-context`).  A ground reifiable NAT
  in `sentence` is resolved to its stored constant first (dedup, never mint), as
  `sentexes-matching` resolves one — `ist` stores the constant, so the lookup has to
  ask for it.  And it refuses the vector spelling of a sentence for the reason `assert`
  does — one entry point cannot answer for a spelling the entry point it counterparts
  refuses to store.

  **A sentence or a context that is not one is refused, not answered nil** (`:shape`).  Nil
  means \"not stored\", and a caller reads it as a fact about the KB: a number, a map or a
  string in the sentence slot, or a context that is nil, a number or a variable, asks
  nothing the store could hold, and answering nil for it reports a malformed request as an
  absence.  A variable context is refused because it names every context and this read
  answers one handle; `sentexes-matching` is the read that takes one.  Both are checked
  after the `(ist Ctx S)` resolution, so the context an `ist` sentence names is the one
  held to it."
  [kb sentence context]
  (check-shape! (sentence-goal-problem sentence))
  (let [[sentence context] (checked-ist-goal kb (first (sx/peel-strength sentence nil)) context)
        sentence           (first (sx/peel-strength sentence nil))]
    (check-shape! (sentence-shape-problem sentence))
    (check-shape! (lookup-context-shape-problem context))
    (let [s       (nat-read/maybe-reify-for-read kb sentence context)
          context (stored-context kb s context)]
      ;; spelled as `context` reads it: a permuting mark it does not believe sorts nothing
      (binding [res/*spelled-by* (res/reader-spelled-by kb s context)]
        (let [[exc inner] (rules/split-exceptWhen (first (sx/peel-exception-strength s)))]
          (if exc
            (exceptWhen-handle kb exc inner context)
            (kb/find-sentex-handle kb s context)))))))

(defn handles
  "Every live sentex handle in the KB — premises and anything forward-derived alike,
  read straight off the record store.  The whole-KB counterpart to the context- and
  query-scoped readers (`sentexes-in-context`, `sentexes-matching`): where those answer
  \"what is here that I asked about,\" this answers \"what is here at all,\" the enumeration
  a content-addressing or audit pass folds over.  Storage, not belief — a stored-but-
  defeated sentex still has a handle and is returned; filter with `in?` for belief.

  **A set to read, not one to build on**: `contains?`, `count`, `seq` and `sort` all
  answer it, and a caller wanting `conj` / `disj` / `clojure.set` converts with `(set …)`
  first — a store large enough for the shape to cost anything answers a compressed
  handle set rather than a `PersistentHashSet` (`vaelii.impl.handle-set`)."
  [kb]
  (p/sentex-ids (:records kb)))

(defn sentex-handle
  "The `(sentexHandle <id>)` term that **names** the sentex stored at handle `n`.  A
  meta-sentex predicates about another sentex by carrying this term in an argument —
  `(exceptWhen <query> (sentexHandle H))` names the rule it qualifies, and a target-
  following predicate (`target_following_predicate`) names the claim its reply hangs on —
  so retracting the named sentex can cascade to the meta.  The inverse is `handle-id`."
  [n]
  (sx/sentex-handle n))

(defn sentex-handle?
  "Is `form` a `(sentexHandle <id>)` term — the naming wrapper `sentex-handle` builds?"
  [form]
  (sx/sentex-handle? form))

(defn handle-id
  "The sentex id a `(sentexHandle <id>)` term names, or nil when `form` is not one.  The
  inverse of `sentex-handle`, so the two round-trip."
  [form]
  (sx/handle-id form))

(defn assert-inert
  "Store `sentence` in `context` as an **inert** sentex — indexed and persisted (so it
  is inspectable via `sentexes-in-context` and survives `recover`) but **not a JTMS
  premise**: never believed, never chained, never scanned for contradictions.  Returns
  the handle.

  This is the primitive behind a solve's materialized labeling (docs/solving.md): a
  *recorded truth value*, not a claim about the base KB.  Because every belief-filtered
  read — `sentexes-matching`, `in?`, and the `settle` nogood scan — sees only IN
  sentexes, an inert
  `(not head)` sitting in a context that sees a believed `head` forms **no** nogood and
  moves **no** belief.  So many labelings coexist and the always-true KB is untouched,
  with no per-context (ATMS) belief needed — coexistence falls out of not premising.

  Only the shape, naming and groundness invariants are enforced (a materialized head is
  already well-formed); no constraint / wff / equality / chaining runs.  An open sentence
  is refused (`:not-ground`) as at `assert`: a stored sentence is closed, and a stored
  literal holding a variable would answer a `CxEverything` read as a fact.  An
  `(ist Ctx S)` sentence stores S in Ctx, as `assert` does; stored as written, the `ist`
  form is a record no read resolves, since every read takes the form apart first.  A
  ground reifiable NAT is resolved to its stored constant first (dedup, never mint), as
  `handle-of` and `sentexes-matching` resolve one, so the inert record keys on the atomic
  form every read reifies to rather than the compound none of them do; a NAT with no
  stored constant is refused (`:unminted-nat`), since minting a `natFormula` is a belief-
  carrying side effect this entry point never has.  A **rule** is refused
  (`:not-indexable`) — a labeling labels atoms, and the reason is below.  `assert-inert`
  is additive, so no `!`; drop it with `retract!` on the returned handle.  A new record
  carries `:inert true` in its provenance, which tells it apart from a record a failed
  write left (`unsupported`).

  A KB whose derived state was never built refuses this exactly as it refuses `assert`
  (`:unrecovered-kb`).  Not premising is what makes an inert sentex harmless to belief;
  it is still *stored and indexed*, so a derived index that opened empty mints it a
  second handle for content the store already holds, which no later pass can merge."
  [kb sentence context]
  (check-writable! kb "assert-inert")
  ;; `assert`'s own shape guards, in its precedence — context, then sentence.  Without
  ;; them this entry point stores what every other entry point refuses: `nm/literals` of a
  ;; non-sequential sentence finds no literals to check, so a string or nil passes
  ;; vacuously and is stored as an object no query can ever match, and a non-symbol
  ;; context throws `:naming` where `assert` and `check` say `:shape`.
  ;; this entry point persists and indexes too, so it owes every one of them — including the
  ;; durable-log constraint `check-sentence-shape!` closes with
  (check-shape! (context-shape-problem context))
  (check-sentence-shape! sentence)
  ;; a `(set/monotonic …)` or `(set/inert …)` on the wrapper chain, refused as at `assert`
  (check-shape! (sx/exception-strength-problem sentence))
  (if (and (sequential? sentence) (= sx/ist-functor (first sentence)))
    ;; `(ist Ctx S)` is not stored, at this entry point as at `assert`: it names the context
    ;; S holds in, and the record is S in Ctx.  Stored as written it was a record with
    ;; the `ist` functor that `handle-of`, `contexts-of` and every read resolved past.
    (if-let [[ctx s] (entry/ist-parts sentence)]
      (assert-inert kb s ctx)
      (check-shape! (entry/ist-shape-problem sentence)))
    (let [;; a ground application in the context slot keys on the `cx/` constant `assert`
          ;; minted for it (dedup, never mint), refused as an unminted NAT below is
          context (if (nat/context-application? context)
                    (or (nat/existing-context kb context)
                        (throw (ex-info (str "a context application with no stored constant"
                                             " cannot be stored inert: " (pr-str context)
                                             " names a context this KB has not minted, and"
                                             " assert-inert never mints — assert a fact in it"
                                             " first (which mints)")
                                        {:type :unminted-nat :sentence sentence
                                         :context context})))
                    context)]
      (nm/check! (:naming kb) sentence context)
      ;; a stored sentence is closed (`checks/check-ground`, the same refusal `assert`
      ;; makes): an inert literal holding a variable is a record every belief-blind read
      ;; answers as a fact, and a labeling's materialized truth values are ground atoms
      (checks/check-ground kb sentence context)
      ;; ...and the one refusal that is this entry point's own.  A rule fires because
      ;; `index-rule-sentex` put its predicates in the rule index, and that runs where a
      ;; rule sentex is *created* — `assert-rule-sentence`'s new branch, and the generator
      ;; mint.  So a rule stored here is one no chainer can reach, and it stays that way:
      ;; asserting the same rule afterwards resolves to this handle, takes the existing
      ;; branch and does not index it either, which leaves a *believed* rule that silently
      ;; never fires.  That is `check-generator`'s reasoning about the accepted-and-inert
      ;; rule, at this entry point — and nothing this primitive exists for wants one, a
      ;; labeling's materialized truth values being atoms and their negations.
      ;;
      ;; **Two inertnesses, and the message names the other one**, because the caller who
      ;; lands here usually wants it: `set/inertRule` is a rule that is believed, indexed
      ;; and browsable and fires neither way — the spelling for a rule kept as
      ;; *documentation*, a transitivity a cached closure computes instead
      ;; (docs/taxonomy.md).  This entry point's inertness is the sentex's: not a premise,
      ;; so never believed at all.
      (when (rules/rule-sentence? (rules/inner-rule sentence))
        (throw (ex-info (str "a rule cannot be stored inert: nothing indexes it, so no"
                             " chainer can reach it, and a later assert of the same rule"
                             " resolves to the stored sentex and does not index it either."
                             "  For a rule kept as documentation — stored, indexed and"
                             " browsable, firing neither forwards nor backwards — assert"
                             " set/inertRule (or {:direction :inert}), which is the other"
                             " inertness: the rule is believed and never fires")
                        {:type :not-indexable :sentence sentence :context context})))
      ;; Store the read-mode reify (dedup, never mint), so an inert record of a NAT-
      ;; bearing sentence keys on the same constant `assert`, `handle-of` and
      ;; `sentexes-matching` all resolve to.  A raw compound is one no belief-filtered
      ;; read reifies to, and it would sit beside the twin a later `assert` mints.  A NAT with no stored constant is refused (`:unminted-nat`): minting
      ;; asserts a `natFormula` premise, the belief-carrying side effect this entry point
      ;; never has, and a labeling materializes atoms that already exist so it never lands
      ;; here (`nat-read/resolve-for-read`).
      (if-let [reified (nat-read/resolve-for-read kb sentence context)]
        (let [[h _ new?] (kb/find-or-create-sentex kb reified context)]
          ;; the :inert mark tells a new inert record apart from a record a failed write
          ;; left (`unsupported`); a sentence already stored keeps its own provenance
          (when new?
            (p/put-provenance (:records kb) h
                              (assoc (p/get-provenance (:records kb) h) :inert true)))
          h)
        (throw (ex-info (str "a reifiable NAT with no stored constant cannot be stored"
                             " inert: " (pr-str sentence) " names a term this KB has not"
                             " minted, and assert-inert never mints — assert the NAT-bearing"
                             " fact first (which mints), or materialize the atom that exists")
                        {:type :unminted-nat :sentence sentence :context context}))))))

(defn contexts-of
  "The contexts in which `sentence` is stored **and believed** — a read through
  `sentexes-matching`, so the context of a defeated or unsupported sentex is not listed.
  `handle-of` per context answers storage regardless of belief."
  [kb sentence]
  (distinct (map :context (sentexes-matching kb sentence '?ctx))))

(defn context-of-agent
  "The canonical context for `agent` — `Alice` ↦ `CxAgentAlice`.  The engine
  projects an agent's modal beliefs into this context (`modal_predicate`, docs/belief.md);
  a coordination layer can reuse it as the agent's write boundary — everything the agent
  asserts lands in its own context, lifted under a shared one by `genlCx`.  The forward
  half of a bijection; the inverse is `agent-of-context`, and the two round-trip."
  [agent]
  (modal/context-of-agent agent))

(defn agent-of-context
  "The agent an agent context belongs to — `CxAgentAlice` ↦ `Alice` — or nil when `ctx`
  is not an agent context.  The inverse of `context-of-agent`."
  [ctx]
  (modal/agent-of-context ctx))

(defn provenance
  "The provenance map recorded for `handle` — `{:creator … :created … …}` — or nil if
  none.  `assert` records `:creator` / `:created` when a sentex is first created;
  `add-provenance` layers on application fields.  Removed when the record is retracted.
  The store's own bookkeeping — the spellings a permuting mark folded into the row — is
  kept beside these fields and not returned."
  [kb handle]
  (not-empty (dissoc (p/get-provenance (:records kb) (the-handle handle "provenance"))
                     integrate/spellings-key)))

(defn add-provenance
  "Merge `m` into `handle`'s provenance map (creating it if absent), returning the
  merged map.  For application-defined bookkeeping layered onto the creation record —
  source, confidence, review state — without touching `:creator` / `:created` unless
  `m` names them.  Provenance is metadata, not belief, so this is additive with no `!`.

  A nil `handle` records nothing and returns nil — there is no record to attach to,
  and `provenance` of nil answers nil, so the write and the read stay in agreement.  A
  non-handle (a vector of handles included) is refused (`:bad-handle`) rather than
  written under a key `provenance` would refuse to read back.

  **Not one of the entry points an unrecovered KB refuses**, and deliberately: what
  `check-writable!` protects is content whose definitional checks would pass vacuously
  and whose dependency sweep cannot be computed, and provenance is neither.  It annotates
  a record that already exists, no check reads it, nothing rests on it, and re-running
  `recover` neither needs nor changes it — so annotating a store you are inspecting is
  exactly the thing to be able to do while its belief is unbuilt."
  [kb handle m]
  (when-some [h (the-handle handle "add-provenance")]
    (let [cur (p/get-provenance (:records kb) h)]
      ;; `m` cannot reach the store's own entry, which `provenance` does not show either
      (p/put-provenance (:records kb) h (merge cur (dissoc m integrate/spellings-key)))
      (dissoc (merge cur m) integrate/spellings-key))))

(defn sentexes-naming
  "Every **stored** sentex whose sentence nests `(sentexHandle handle)` — the
  meta-sentexes naming `handle` — a defeated or unsupported one included.  One
  term-index read.  Pass `{:believed? true}` to keep only what the JTMS believes (O(n)
  in the answer).  An opts key this fn does not read is refused (`:unknown-option`).
  Empty for a nil handle; a non-handle is refused (`:bad-handle`).  A lazy seq over live
  state, as `sentexes-in-context` is — `vec` it for a snapshot."
  ([kb handle] (sentexes-naming kb handle nil))
  ([kb handle opts]
   (check-extent-opts! opts "sentexes-naming")
   (if-some [h (the-handle handle "sentexes-naming")]
     (believed-filter kb opts (records-of kb (reads/as-stored-naming-handle (:index kb) h)))
     ())))

(def ^:dynamic *query-engine*
  "Which backward executor `prove` and `prove-within` run:

    :dfs        the goal-stack DFS (`res/prove-from`) — the default
    :inference  the node engine (`vaelii.impl.inference`), a frontier of whole
                conjunctions ordered by cost
    :hybrid     the node engine, except at `:max-depth` 0, where no node is ever
                expanded past the root and the session and its queue would be pure
                overhead

  The default is `:dfs`.  Two engines
  that disagree are worse than one engine that is slow, and they *do* disagree past the
  node engine's depth bound: it terminates on that bound where the DFS terminates on the
  data, so a derivation deeper than the node engine's depth bound is found by one and
  not the other — and that bound has no default, so `:inference` requires the caller to
  choose one (`*query-options*` `:max-depth`, or `inference/*max-depth*`).  Within the
  bound the two return the same answer set, which is what `inference_parity_test` holds
  them to.

  **Bind it around the *consumption*, not just the call.**  The read entry points answer with
  lazy seqs, so a `binding` frame popped before the first element is realized leaves the
  root value — `:dfs` — deciding which engine runs, silently and with nothing to report
  that the choice did not take; `res/blind-seq` is the same hazard written down for
  `*belief-blind*`.  Force the read inside the frame (`doall`, `into []`) or keep the
  whole consumer in it."
  :dfs)

(defn- inference-engine?
  "Does the selector route this run to the node engine?"
  [max-depth]
  (case *query-engine*
    :inference true
    ;; the node engine cannot start without a depth bound and has no default, so
    ;; `:hybrid` reads a missing one as "the caller has not chosen" and takes the
    ;; engine that needs no choosing
    :hybrid (let [d (or max-depth inference/*max-depth*)]
              (boolean (and d (pos? (long d)))))
    false))

(def ^:dynamic *query-options*
  "How the node engine searches, when `*query-engine*` routes a query to it.  Ignored by
  the DFS, which has one order and no choice to make.

    {:strategy :depth-first}   a tactician, or a strategy map (`vaelii.impl.tactics`)
    {:portfolio? true}         race several orderings and union their answers
    {:auto? true}              pick one from the structure of the query

  nil — the default — is the shipped ordering, and adds no work to leave alone.  Every
  tactician returns the same answer set (docs/inference.md), so this is a **latency**
  choice: an exhaustive run expands the same nodes whatever the order, and an ordering
  can only pay a consumer that stops early.  `:portfolio?` and `:auto?` reach only
  `prove`; a race has no partial answer to hand back, so `prove-within` takes the
  strategy and drives the ordinary stream.

  **Bind it around the *consumption*, not just the call**, for `*query-engine*`'s reason:
  the read entry points answer with lazy seqs, and a frame popped before realization leaves the
  root value — nil, the shipped ordering — searching, with nothing to say the ordering did
  not take (`res/blind-seq` documents the same hazard for `*belief-blind*`)."
  nil)

(def query-opt-keys
  "Every key `query` / `query?` read — its own dial and the node engine's, which is where
  the rest go (`inference/solutions`): `:max-depth`, `:proof?`, `:strategy`,
  `:portfolio?`, `:auto?` and `:racers`.  A key off this set is refused
  (`:unknown-option`) rather than handed on, for `assert-opt-keys`' reason: the node
  engine reads what it knows and ignores the rest, so `{:max-deph 3}` or `{:proof true}`
  would answer facts-only with nothing to say it had.  `:first-result?` is a **strategy**
  key, not a query one — `{:strategy {:first-result? true}}` — as are the signs and
  weights in `vaelii.impl.tactics/defaults`.  Public so a caller can ask whether a key is
  real before being told by a refusal."
  #{:max-depth :proof? :strategy :portfolio? :auto? :racers})

(def search-tree-opt-keys
  "Every key `search-tree` reads: the depth, the search ordering, and the two bounds only a
  debugger read takes — the node-expansion budget and the wall clock.

  **Not `query`'s key set plus those two**, though the two entry points run the same search.  A
  debugger read is a fixed mode of it: `search-tree` runs under `:proof? true` and reaches
  the node engine's session directly, never the portfolio path, so `:proof?`, `:portfolio?`,
  `:auto?` and `:racers` are keys it overwrites or never looks at.  Admitting one would
  re-create at this entry point the failure the key set closes at `query`'s — `{:proof? false}`
  accepted and the proof returned anyway.  Public for `query-opt-keys`' reason."
  #{:max-depth :strategy :node-budget :max-ms})

(def compare-tacticians-opt-keys
  "Every key `compare-tacticians` reads: `search-tree`'s two bounds and the depth, plus
  `:tacticians` — the subset of orderings to run.

  **`:strategy` is not on it.**  This entry point sets the ordering per row, which is the whole
  point of running several, so a caller's `:strategy` would be accepted and discarded —
  the silent default the key sets exist to refuse.  Name the orderings with `:tacticians`
  instead.  Public for `query-opt-keys`' reason."
  #{:max-depth :tacticians :node-budget :max-ms})

(def ask-opt-keys
  "Every key `ask` / `ask?` reads — the wall clock, and nothing else.

  **`:max-depth` is not on it**, and its absence is the entry point saying what it is: nothing in
  the prover registry expands a rule, so there is no transformation depth to bound and a
  `:max-depth` here would be a bound accepted and never consulted.  Bounding *which*
  provers run is `ask-within`'s `:max-cost` (docs/anytime.md).  Public for
  `query-opt-keys`' reason."
  #{:max-ms})

(def escalate-opt-keys
  "Every key `escalate` reads — the wall clock, and nothing else.  It is checked between
  levels and inside level 7's search, and a climb it stops before anything answered
  says `:status :timeout` rather than that nothing answers (docs/levels.md).  Public for
  `query-opt-keys`' reason."
  #{:max-ms})

(def prove-opt-keys
  "Every key `prove` / `provable?` reads: the wall clock, and the rule-expansion depth.

  The two bound different things and only one of them suspends.  `:max-ms` is a
  **deadline** — the search stops where it is, and a stop is a refusal here rather than a
  short answer.  `:max-depth` is a **pruning** bound: the space under it is genuinely
  exhausted, so the answer is complete for that depth and nothing is refused
  (docs/anytime.md).  Public for `query-opt-keys`' reason."
  #{:max-ms :max-depth})

(defn- check-search-opts!
  "The key set and then the value domains one bounded read entry point owes.  The key check
  runs first because a misspelt key is not a bad value — it is a key that is not there;
  then `opts/check-values!` reads the one domain table every bounded entry point shares
  (`opts/bound-domains`), which for a search means `:max-ms` and `:max-depth`.  A bound
  nobody could have meant reads as no bound, and an unbounded search answered as though it
  were the bounded one is a search at a setting nobody chose."
  [opts opt-keys entry-point]
  (opts/check! opts opt-keys entry-point
               (str "A bound nothing reads is an unbounded search in silence, on an entry point"
                    " whose whole point is that the search stops."))
  (opts/check-values! opts entry-point))

(defn- bound-exhausted!
  "The refusal a bounded read owes when its budget ran out before the search did.

  A `:timeout` answer is a **prefix** of the answer set, and `prove` / `ask` return the
  answer set — so handing the prefix back is the one reading that is certainly wrong: it
  is indistinguishable from the whole of a KB that knows less.  `ask?` / `provable?` are
  worse still, since the prefix is empty and `false` is a claim about the KB rather than
  about the clock.  So the bound reports, and a caller that wants the partial has
  `ask-within` / `prove-within`, which return it with a `:status` saying what it is
  (docs/anytime.md)."
  [entry-point bound status elapsed-ms]
  (throw (ex-info (str entry-point " did not finish inside the bound it was given — "
                       (pr-str bound) ", " status " after "
                       (long (or elapsed-ms 0)) " ms.  Widen the bound, or ask through"
                       " ask-within / prove-within, which hand back what was found so"
                       " far with a :status saying it is a prefix")
                  {:type :budget-exhausted :entry-point entry-point :bound bound
                   :status status :elapsed-ms elapsed-ms})))

(defn- exhaustive-within
  "A bounded read's solutions when the search ran dry inside the bound, else the refusal.
  What `prove` and `ask` want, both of which answer with the whole solution set."
  [entry-point bound {:keys [results status elapsed-ms]}]
  (if (= :complete status)
    results
    (bound-exhausted! entry-point bound status elapsed-ms)))

(defn- decisive-within
  "The same for an existence question: whatever was found when anything was — one
  solution settles `true` however much of the space is left — an empty answer when the
  source ran dry, and the refusal otherwise.  Never an empty answer meaning *we stopped
  looking*."
  [entry-point bound {:keys [results status elapsed-ms]}]
  (cond
    (seq results)        results
    (= :complete status) results
    :else                (bound-exhausted! entry-point bound status elapsed-ms)))

(defn- query-options
  "`*query-options*` as the node engine's opts map, with `max-depth` folded in."
  [max-depth]
  (cond-> (cond (nil? *query-options*)     {}
                (keyword? *query-options*) {:strategy *query-options*}
                :else                      *query-options*)
    max-depth (assoc :max-depth max-depth)))

(defn- query-depth
  "How deep a read expands rules: the caller's `opts`, else `*query-options*`
  `:max-depth`.  nil — no depth in either — is the no-rule-expansion answer, and the one
  thing this must never do is invent a number (`query`'s docstring for why).

  `*query-options*` is the channel `prove` reads too, so a caller who has bound a depth
  for one read does not have to learn a second place to bind it for another.
  `inference/*max-depth*` is not read here: it is the node engine's own bound, the one
  the query-engine sweep sets so `prove` can run there, and a read with no depth of its
  own answers from the registry whichever engine `prove` is routed to.

  `opt-keys` is the calling entry point's key set and `entry point` its name — `query-opt-keys`,
  `search-tree-opt-keys`, `compare-tacticians-opt-keys`.  Each entry point passes what it
  actually reads rather than a superset: a key set wider than the entry point is a key accepted
  and then overwritten, which is the silent default this check exists to refuse."
  [opts opt-keys entry-point]
  ;; A non-map `opts`, a key nothing reads and a non-positive `:max-depth` all read as
  ;; "no depth", which is not an error condition but a *different question* — the
  ;; no-rule-expansion answer, returned as if it were the bounded one the caller asked
  ;; for.  `(query kb g c :oops)`, `{:max-deph 3}` and `{:max-depth -3}` would each do
  ;; that silently.  Refused for `assert`'s reason: an answer taken at a setting nobody
  ;; chose is indistinguishable downstream from one taken at a setting somebody did.
  (opts/check! opts opt-keys entry-point
               (str "An option nothing reads takes the default in silence, which here"
                    " is a search at a setting nobody chose — a misspelt depth answers"
                    " facts-only as though no rule could reach the goal."))
  ;; the value domains, from the one table every bounded entry point shares
  ;; (`opts/bound-domains`): `:max-depth` here, and for `search-tree` /
  ;; `compare-tacticians` the `:max-ms` and `:node-budget` their key sets add.  A depth
  ;; that is not a non-negative integer reads as no depth at all, which is that same
  ;; facts-only answer taken at a setting nobody chose.
  (opts/check-values! opts entry-point)
  (or (:max-depth opts)
      (when (map? *query-options*) (:max-depth *query-options*))))

(defn- registry-leaf
  "What a backward search answers a literal it does not rewrite with: the prover registry
  (`provers/solve-goal`), so an antecedent or a goal is answerable by transitivity, an
  evaluable, a calculus or an inferred argument type as well as by a stored fact, and the
  cost model that leaf is planned by.  `prove` and `query` both run on it, so a rule
  expansion never answers less than `ask` does for the same literal.  Merged into the
  DFS's bounds and the node engine's opts alike."
  [kb context]
  {:leaf-solver  provers/solve-goal
   :est-override (provers/registry-est-override kb context)})

(defn- backward-within
  "One bounded run of the backward chainer over `goals` in `context`, as the anytime
  partial-result contract (`vaelii.impl.budget`).

  **The same two engines `prove` itself routes between**, and routed by the same
  selector, so a bound cannot change which one answers: the DFS through `res/prove-from`,
  whose stack is the continuation, or the node engine through `inference/search-within`,
  whose session is.  `prove-within` builds its own contract on exactly these two, and
  this exists beside it rather than through it because `prove` resolves a **query
  context** first (`read-in-context`) and `prove-within` refuses one — so a `CxEverything`
  or a variable context has to keep answering here whether a bound is named or not.

  `budget` may carry `:max-results`, which is not a caller's key: it is how the two
  existence entry points stop at the first answer instead of searching a space they have already
  decided."
  [kb goals context budget]
  (if (inference-engine? (:max-depth budget))
    (inference/search-within
     (inference/session kb goals context (merge (query-options (:max-depth budget))
                                                (registry-leaf kb context)))
     budget)
    (let [rules-fn (fn [g] (provers/candidate-rules kb g context))
          leaf     (registry-leaf kb context)
          start    (System/nanoTime)
          {:keys [solutions status]}
          (res/prove-from kb rules-fn context (merge (budget/prove-bounds budget) leaf)
                          (res/initial-prove-stack kb goals context (:est-override leaf)) [])]
      ;; the contract's own assembler, so the two arms report elapsed time the same way;
      ;; no continuation, because this entry point hands back a whole answer or a refusal
      (budget/from-batch solutions status start nil))))

(defn- prove-capped
  "`prove`'s body, stopping each engine once `max-results` solutions are in hand (nil:
  every one).  `provable?` asks it for one."
  [kb goal context opts max-results]
  (check-shape! (conjunction-goal-problem goal))
  (check-search-opts! opts prove-opt-keys "prove")
  (let [[goal context] (ist-goal kb goal context)
        cap #(cond-> % max-results (assoc :max-results max-results))]
    (read-alternatives
     kb goal context max-results
     (fn [goals-in]
       (read-in-context
        kb goals-in context
        (fn [ctx]
          (let [goals (goals-in ctx)]
            (cond
              ;; a bound: the same two engines, driven through the resumable core so the
              ;; run can stop at a depth and a clock — and refuse rather than hand back
              ;; the prefix it stopped on
              (seq opts)
              (exhaustive-within "prove" opts (backward-within kb goals ctx opts))

              (inference-engine? nil)
              (inference/solutions kb goals ctx
                                   (cap (merge (query-options nil) (registry-leaf kb ctx))))

              :else
              (res/prove kb (fn [g] (provers/candidate-rules kb g ctx)) goals ctx
                         (cap (registry-leaf kb ctx))))))
        ;; unbounded rule expansion, so an antecedent fact is not one of `goals` and its
        ;; context never reaches a placement: outside post-hoc's domain by construction
        {:expands-rules? true})))))

(defn prove
  "Backward-chain in `context` with the simple recur DFS prover; returns a vector of
  solution binding maps.  Type-aware (specificity) and context-aware (only what is
  visible from `context`).  A literal no rule rewrites is answered by the prover
  registry (`registry-leaf`), so `prove` finds at least what `ask` finds for it: a
  `genl` pair two edges apart, an evaluable, a symmetric mirror.

  `goal` is either a single sentence — `(grandparentOf Tom ?who)` — or a **vector**
  of sentences, which is a **conjunctive query**:

    (prove kb '[(parentOf ?x ?y) (dog ?y)] 'CxMantle)

  Conjuncts are solved with bindings threaded across them, so a variable shared
  between conjuncts **joins** them: `?y` above must be both the child and a dog.
  Each solution binds every variable of every conjunct.  An empty vector proves
  trivially (one empty solution).

  **Conjuncts are reordered for cost** (`vaelii.impl.plan`) — so you don't hand-order
  them.  The most selective literal is run first, measured from the
  count-aware trie and the argument roots, and each pick re-estimates the rest under
  the variables it binds (sideways information passing), so ordering adapts as the
  join proceeds.  A rule's antecedents are planned the same way at each expansion.

  Ordering is a **cost** decision and never a semantic one: a conjunction is
  commutative, so every write order returns the same answer set.  The two literals
  whose position is operational rather than logical are fixed in place — evaluables
  (`evaluate` / `lessThan` / `greaterThan`) never outrun what binds them, and a
  rule's recursive literal stays last so right-recursion is preserved.  Solution
  *order* within the returned vector is not part of the contract.

  **One solution per derivation, so equal binding maps repeat.**  A goal reachable
  two ways — a stored fact that forward chaining already materialized *and* the rule
  that concludes it, or two rules with the same consequent — comes back twice, with
  the two maps equal.  `(count (prove …))` is therefore a count of proofs, not of
  answers: wrap it in `distinct` for an answer set, or reach for `query` / `ask`,
  which project to the goal's variables and answer each binding once.

  **It agrees with belief.**  Expanding a rule reaches conclusions `ask` cannot, but never
  a conclusion belief has settled *against*: an answer whose sentence names a stored sentex
  the JTMS holds **defeated** — a default beaten by a monotonic negation — is not returned,
  and does not feed a rule above it either.  Retract the defeater and it is answered again
  (docs/inference.md, \"Answers belief has already decided against\").

  `query-plan` on the same vector shows the chosen order and why.  An `(ist Ctx S)` goal
  proves S in Ctx, the named context winning over `context`; one standing as a *conjunct*
  is refused, a join having no per-literal context (`ist-goal`).  A conjunct that is not
  a sentence is refused too (`:shape`) — `[likes Tom Ann]` is the sentence spelling of a
  vector, which is three goals here and nothing the KB can hold.

  **`opts` is a bound, and without one there is none.**  `{:max-ms n :max-depth n}`
  (`prove-opt-keys`) is the whole key set, and the two bound different things:

      (prove kb goal ctx {:max-depth 2})   ≤2 rule expansions — a complete answer
                                           for that depth, since the space under it
                                           is genuinely exhausted
      (prove kb goal ctx {:max-ms 250})    a deadline — and a deadline this entry point
                                           **reaches** is `:budget-exhausted`, never
                                           a short answer

  The asymmetry is the point. A depth *prunes*, so what comes back is the whole of what
  the depth admits; a clock *suspends*, so what comes back is a prefix, and a prefix
  returned as an answer set is indistinguishable from the whole of a KB that knows less.
  A caller that wants the prefix asks through `prove-within`, which hands it back with a
  `:status` saying what it is (docs/anytime.md). Absent, the search terminates on the
  data, as it always has: the per-path loop guard and the term-growth ceiling are what
  make that true, and neither is a bound the caller named."
  ([kb goal] (prove kb goal '?ctx nil))
  ([kb goal context] (prove kb goal context nil))
  ([kb goal context opts] (prove-capped kb goal context opts nil)))

(defn provable?
  "Is `goal` provable in `context`?  Takes the same single-sentence or vector-of-
  sentences conjunction as `prove`; a conjunction is provable iff all its conjuncts
  are, under one consistent binding of their shared variables.

  One solution settles the question, so the search stops at the first and the rest of the
  space is never searched, bounded or not.  `opts` is `prove`'s bound (`prove-opt-keys`).
  **A bound it exhausts is `:budget-exhausted`, never `false`** —
  `false` is a claim about the KB, and a clock that ran out is a claim about the clock.
  A depth prunes rather than suspends, so `{:max-depth 2}` answers `false`, and it
  means no derivation within two rewrites, which is a question a caller may ask."
  ([kb goal] (provable? kb goal '?ctx nil))
  ([kb goal context] (provable? kb goal context nil))
  ([kb goal context opts]
   ;; before the `seq` test: `(seq :oops)` throws a bare IllegalArgumentException, where
   ;; `prove` refuses the same non-map opts by name — this entry point mirrors that one
   (check-search-opts! opts prove-opt-keys "provable?")
   (if (seq opts)
     (do (check-shape! (conjunction-goal-problem goal))
         (let [[goal context] (ist-goal kb goal context)
               ;; the cap is this entry point's, not the caller's: it is what makes an existence
               ;; question cost one answer rather than the whole space
               budget   (assoc opts :max-results 1)]
           (boolean
            (seq (read-alternatives
                  kb goal context 1
                  (fn [goals-in]
                    (read-in-context
                     kb goals-in context
                     (fn [ctx]
                       (decisive-within "provable?" opts
                                        (backward-within kb (goals-in ctx) ctx budget)))
                     {:expands-rules? true})))))))
     (boolean (seq (prove-capped kb goal context nil 1))))))

(defn ask
  "Answer `goal` in `context` with the pluggable prover engine — the stored facts,
  the taxonomy closures, transitivity, disjointness, the predicate metadata, the
  evaluables, NAF, arg type inference, and any prover the application added.
  Returns solution binding maps projected to the goal's variables.

  **No rule expansion.**  Nothing in the registry backchains, so `ask` answers from
  what the KB stores or has cached and never opens a proof search.  That is what makes
  its cost a property of the goal rather than of the rule graph, and it is why the
  closed-world readers (`exceptWhen`, `unknown`, `thereExists`, the aggregates) can run
  the same registry from inside a relabel loop.  A `set/backwardRule`'s conclusion
  exists only while a backchainer is looking for it, so `ask` does not see one: reach
  for `query` with a `:max-depth`, or `prove`.

  An `(ist Ctx S)` goal asks S in Ctx, the named context winning over `context`
  (`ist-goal`).  **One sentence, never a vector**: no prover in the registry joins, so a
  conjunction belongs to `query` / `prove` and the vector spelling is refused (`:shape`)
  rather than flattened into a sentence and answered `false`.

  **`opts` is a wall clock and nothing else** (`ask-opt-keys`): `{:max-ms n}`. Expanding
  no rule does not make a read cheap — a `:compute` prover walks a closure or censuses an
  extent — so the bound is what a caller reaches for when the goal's own cost is the
  worry. Naming one realizes the answer stream under it rather than returning it lazily,
  which is what a clock over a lazy seq means, and a clock this entry point **reaches** is
  `:budget-exhausted` rather than the prefix it stopped on. `ask-within` is the entry point that
  hands the prefix back, with `:max-cost` besides — the qualitative lever that drops the
  expensive tier rather than interrupting it (docs/anytime.md)."
  ([kb goal] (ask kb goal '?ctx nil))
  ([kb goal context] (ask kb goal context nil))
  ([kb goal context opts]
   (check-shape! (sentence-goal-problem goal))
   (check-search-opts! opts ask-opt-keys "ask")
   (let [[goal context] (ist-goal kb goal context)]
     (read-in-context kb #(vector (quasiquote/prepare-goal-for-read kb goal %)) context
                      (fn [ctx]
                        (let [answers #(quasiquote/ask-prepared kb goal ctx)]
                          (if (seq opts)
                            (exhaustive-within "ask" opts (budget/collect (answers) opts answers))
                            (answers))))
                      nil))))

(defn ask?
  "Is `goal` answerable via the prover engine?  `ask`'s caveats are this one's too —
  in particular it expands no rule.

  `opts` is `ask`'s wall clock, spent the way `provable?` spends `prove`'s: the stream is
  realized only as far as its first solution, and **a clock that runs out with nothing
  found is `:budget-exhausted` rather than `false`**."
  ([kb goal] (ask? kb goal '?ctx nil))
  ([kb goal context] (ask? kb goal context nil))
  ([kb goal context opts]
   ;; before the `seq` test, for `provable?`'s reason: a non-map opts is a typed refusal
   ;; at `ask`, and `(seq :oops)` would throw bare here
   (check-search-opts! opts ask-opt-keys "ask?")
   (if (seq opts)
     (do (check-shape! (sentence-goal-problem goal))
         (let [[goal context] (ist-goal kb goal context)]
           (boolean
            (seq (read-in-context
                  kb #(vector (quasiquote/prepare-goal-for-read kb goal %)) context
                  (fn [ctx]
                    (let [answers #(quasiquote/ask-prepared kb goal ctx)]
                      (decisive-within "ask?" opts
                                       (budget/collect (answers) (assoc opts :max-results 1)
                                                       answers))))
                  nil)))))
     (boolean (seq (ask kb goal context))))))

(defn- query-node-opts
  "The node engine's opts for a depth-`d` read in `context`: `*query-options*` and the
  caller's `opts`, plus the depth and the two things that make the engine answer what
  `query` means — the registry as its leaf (so an antecedent is answerable by *any*
  prover: transitivity, an evaluable, a calculus, an inferred argument type) and the
  cost model that leaf is planned by.  `query-at` and `query-status-at` both build the
  same run from it."
  [kb context d opts]
  (merge (query-options nil) opts {:max-depth d} (registry-leaf kb context)))

(defn- query-at
  "`query`'s answer from **one** named context: the whole of its body, once the depth
  has been read and the goal resolved.

  Split out because `CxInference` asks it once per reader (`vaelii.impl.vantage`), and a
  read that answers *from a vantage* has to be a function of that vantage.  The context
  reaches four places in here — the goal preparation (`goals-in`), the node engine, the registry's
  cost model and the candidate-rule lookup — so standing somewhere else is not a
  substitution into the argument but a different call.  `max-results` stops the node
  engine once that many answers are in hand (nil: every one); the registry reads are lazy
  and need no cap."
  [kb goals-in context d opts max-results]
  (let [goals (goals-in context)]
    (cond
      ;; a depth: the node engine, whose leaf is the registry — so an antecedent is
      ;; answerable by *any* prover (transitivity, an evaluable, a calculus, an inferred
      ;; argument type) and the engine is left doing only what it is for, which is
      ;; expanding rules.  `prove`'s leaf is the stored facts instead, which is the whole
      ;; difference between the two.
      (and d (pos? (long d)))
      (inference/solutions kb goals context
                           (cond-> (query-node-opts kb context d opts)
                             max-results (assoc :max-results max-results)))

      ;; No depth and one literal: the registry answers it directly, and lazily to the
      ;; first result.  The goal is already prepared, which is the whole of what `ask`
      ;; would add before handing it over.
      (= 1 (count goals))
      (provers/ask kb (first goals) context)

      ;; No depth and a **conjunction**: still the registry and still no rule, but the
      ;; conjuncts have to join, and one `ask` per literal cannot thread a binding across
      ;; them.  The recursive chainer at depth 0 is exactly that — the registry as its
      ;; leaf, the bound admitting no rewrite — so the shapes agree on their answers and
      ;; differ only in the dial.  Lazy, like the single-literal case.
      :else
      (res/prove-seq kb #(provers/candidate-rules kb % context) goals context
                     (assoc (registry-leaf kb context) :max-depth 0)))))

(defn- query-capped
  "`query`'s body, with `query-at`'s `max-results`."
  [kb goal context opts max-results]
  (check-shape! (conjunction-goal-problem goal))
  (let [[goal context] (ist-goal kb goal context)
        d (query-depth opts query-opt-keys "query")]
    (read-alternatives
     kb goal context max-results
     (fn [goals-in]
       (read-in-context kb goals-in context
                        #(query-at kb goals-in % d opts max-results)
                        {:expands-rules? (boolean (and d (pos? (long d))))})))))

(defn query
  "Answer `goal` in `context` — the public entry point — as a seq of **binding maps**
  (`{?x val …}`) projected onto the goal's own variables.

  `goal` is a sentence, or a **vector** of them: a conjunctive query whose shared
  variables join, exactly as `prove` takes.

  `opts` makes one decision, and it is **how deep to expand rules**:

      (query kb goal ctx)                   no rule expansion — the registry alone
      (query kb goal ctx {:max-depth 3})    the node engine, ≤3 rewrites deep

  **There is no default depth.**  A bound decides which derivations
  exist, so a number chosen here would be this namespace quietly answering a question
  that belongs to the application: find the smallest depth that answers yours and pass
  it.  Without one the answer is whatever needs no rule, which is a real answer and not
  a degenerate case — most of a common-sense KB's reads are stored facts and cached
  closures.

  The depth may also come from `*query-options*` `:max-depth`, which is where `prove`
  reads it from too — so one dynamic binding sets the depth for every read in its scope.
  `opts` wins over it.  It has no default, so a depth bound nowhere stays the
  no-rule-expansion answer rather than a number nobody chose.

  **`{:proof? true}`** changes the result shape to `[{:bindings … :proof …}]`, one
  **justification tree** per answer — the derivation the search took, reading the way
  `why` does (`:goal` / `:via` / `:because`).  `why` explains a *stored* belief by
  reading the JTMS; this explains an *ephemeral* one by reading the search, and the two
  are deliberately one shape.  Needs a depth, since without one no rule was expanded and
  there is no derivation to show.

  Everything else in `opts` is the node engine's, defaulting from `*query-options*` —
  `:strategy` (`vaelii.impl.tactics`), `:portfolio?`, `:auto?`, `:racers` — and is
  ignored where no depth sends the query there.  That is the whole key set
  (`query-opt-keys`); a key off it is refused (`:unknown-option`) rather than handed on,
  since the engine would ignore it and `{:max-deph 3}` would answer facts-only with
  nothing to say so.  A non-map `opts` and a `:max-depth` that is not a natural number
  are refused the same way.

  **A depth reaches further, never against belief.**  An answer a rule expansion produced
  whose sentence names a stored sentex the JTMS holds **defeated** is not returned at any
  depth, and does not feed a rule above it either — so a depth answers more than the
  registry alone and never disagrees with `ask` about which side of a settled clash holds
  (docs/inference.md, \"Answers belief has already decided against\").

  Two things this is not.  `prove` is the *unbounded* backward chainer: it terminates
  on the data rather than on a bound, so it answers a chain deeper than any depth you
  would have guessed, at the cost of facts-and-rules only.  `sentexes-matching` is the
  belief-filtered index read, and returns sentexes rather than bindings."
  ([kb goal] (query kb goal '?ctx nil))
  ([kb goal context] (query kb goal context nil))
  ([kb goal context opts] (query-capped kb goal context opts nil)))

(defn query?
  "Is `goal` answerable under `opts`?  `query`, asked for one answer: the search stops at
  the first."
  ([kb goal] (query? kb goal '?ctx nil))
  ([kb goal context] (query? kb goal context nil))
  ([kb goal context opts]
   ;; the `dissoc` waits for the map: run on a non-map it threw a bare cast error
   ;; before `query`'s own guard could type the refusal, so the two entry points disagreed
   ;; on the one input class `query?` exists to mirror
   (boolean (seq (query-capped kb goal context (cond-> opts (map? opts) (dissoc :proof?)) 1)))))

(defn- timed-realize
  "Realize `xs`, timing it: `[vector first-answer-ns total-ns]`, `first-answer-ns` nil
  when `xs` is empty.  A `query-status` over the facts-only reads, which come back as
  lazy seqs the way `query` returns them."
  [xs]
  (let [start (System/nanoTime)]
    (loop [s (seq xs), acc (transient []), first-ns nil]
      (if s
        (recur (next s) (conj! acc (first s)) (or first-ns (- (System/nanoTime) start)))
        [(persistent! acc) first-ns (- (System/nanoTime) start)]))))

(defn- query-status-at
  "`query-status`'s report from **one** concrete context.  The node engine when a depth
  expands rules (`inference/search-report`, which is where truncation and the phase
  timings come from), the facts-only reads otherwise — realized here so the report can
  time them, since a depth-0 read is a complete answer to its own question and a depth
  never cut it."
  [kb goal context d opts]
  (if (and d (pos? (long d)))
    (let [goals (quasiquote/prepare-conjunction-for-read kb goal context)
          {:keys [answers truncated? time-to-first-answer-ms total-time-ms stats unenumerated
                  unenumerated-in-guards]}
          (inference/search-report kb goals context (query-node-opts kb context d opts))]
      {:answers                 answers
       :count                   (count answers)
       :status                  (cond truncated?          :truncated
                                      (seq unenumerated) :incomplete
                                      :else              :complete)
       :truncated?              truncated?
       :unenumerated            unenumerated
       :unenumerated-in-guards  unenumerated-in-guards
       :depth                   d
       :time-to-first-answer-ms time-to-first-answer-ms
       :total-time-ms           total-time-ms
       :stats                   stats})
    (let [[[answers first-ns total-ns] {:keys [unenumerated unenumerated-in-guards]}]
          (provers/with-unenumerated #(timed-realize (query-at kb (fn [ctx] (quasiquote/prepare-conjunction-for-read kb goal ctx))
                                                               context d opts nil)))]
      {:answers                 answers
       :count                   (count answers)
       :status                  (if (seq unenumerated) :incomplete :complete)
       :truncated?              false
       :unenumerated            unenumerated
       :unenumerated-in-guards  unenumerated-in-guards
       :depth                   d
       :time-to-first-answer-ms (when first-ns (/ (double first-ns) 1e6))
       :total-time-ms           (/ (double total-ns) 1e6)})))

(defn query-status
  "`query`'s answers, plus a **report** of the run — what a bare `query` cannot say.  Its
  first purpose is the one silent failure `:max-depth` otherwise has: a query truncated at
  the depth bound returns the same empty (or short) seq as a query whose goal is genuinely
  unprovable, so a bound set one too low reads as \"no\" rather than \"not deep enough.\"
  This distinguishes them.

  The report is a map:

      {:answers                 [{?x v} …]   `query`'s own answers, realized
       :count                   n
       :status                  :complete | :truncated | :incomplete
       :truncated?              bool         = (= status :truncated)
       :unenumerated            [P …]        transitive predicates whose closure a goal
                                             asked with both arguments open did not
                                             enumerate
       :unenumerated-in-guards  [P …]        those recorded inside an `unknown` or
                                             `exceptWhen` evaluation (docs/inference.md)
       :depth                   d | nil      the depth bound the read ran under
       :time-to-first-answer-ms t | nil      nil when there are no answers
       :total-time-ms           t
       :stats                   {…}}         node-engine counters, present at a depth

  **`:truncated?` is conservative.**  `true` means the depth bound stopped at least one
  rewrite the search would otherwise have taken — the answers *may* be incomplete; `false`
  with an empty `:unenumerated` guarantees they are every answer this KB entails at that
  depth.  A branch cut at the bound may still have been answered by a shallower one (a
  converging rule graph reaches a subgoal at several depths), so `true` is not proof an
  answer was lost — it is the signal
  to try a deeper bound, and to stop when `:truncated?` clears and the answer set holds
  still.  A facts-only read (no depth, or `:max-depth 0`) is never truncated: expanding no
  rule is a complete answer to the question it asks (`query`'s docstring for why that is a
  real answer and not a degenerate one).  It can still be `:incomplete`.

  **`:incomplete` is the other case where the answers may not be every answer.**  A goal `(P ?x ?y)` over a
  `transitive` `P`, at the top or as a rule antecedent solved with both ends still open,
  is answered by `P`'s extent and not its closure (docs/taxonomy.md), so the answers may
  lack a derived pair.  `:unenumerated` names each such `P`, and `:status` is
  `:incomplete` when it is non-empty and the bound cut nothing.  Binding one end per
  source enumerates the closure.

  `:stats` is the node engine's `tree-stats` — `:expanded` / `:nodes` / `:frontier` /
  `:dropped` / `:solutions` / `:max-depth` (the deepest rewrite taken) — present only where
  a depth sent the read to that engine.  `:depth`, `:opts` and the goal shape are `query`'s;
  the key set (`query-opt-keys`) and the depth resolution are the same, so a `query` and a
  `query-status` of the same call answer the same set.

  **A concrete context only.**  A report is one search over one context's frontier, so a
  variable context (`?ctx`) or a query context (`CxEverything` / `CxInference` / `CxNothing`)
  is refused (`:unsupported-context`): those fan a read across several readers, with no one
  frontier to report truncation off.  Reach for `query` there.  `:portfolio?` / `:auto?`
  picking a race is dropped for the same reason — a report drives one ordering."
  ([kb goal context] (query-status kb goal context nil))
  ([kb goal context opts]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)]
     (when (or (sx/variable? context) (nm/query-context? context))
       (throw (ex-info (str context " is a query or variable context, and query-status runs"
                            " in one concrete context — a report is one search over one"
                            " frontier, and a fanned read has none to report truncation off."
                            "  Name the context, or read with query, which does resolve one.")
                       {:type :unsupported-context :context context})))
     (check-shape! (read-context-shape-problem kb context))
     (let [d (query-depth opts query-opt-keys "query-status")]
       (query-status-at kb goal context d opts)))))

(def ^:private abduce-ops
  "The `ops` map `vaelii.impl.abduce` takes (its ns docstring says why).  `assert` and
  `edit!` as vars, because both are defined below this point."
  {:rules-fn provers/candidate-rules :assert #'assert :edit #'edit!})

(defn abduce
  "What would have to be true for `goal` to be provable in `context`.

  Runs `prove`'s backward search and **hypothesizes** the dead-ended subgoals a
  `(abducible_predicate P)` grant visible from `context` allows, each as a `:default`
  premise in a scratch context hung below `context`.  Answers

      {:solutions   [binding-map …]     `prove`'s, unprojected, under the hypotheses
       :hypotheses  [{:sentence :context :handle} …]   irredundant; empty = proved outright
       :refused     [sentence …]        dead ends the abducibility check would not assume, when none proved
       :context     CxAbductionX
       :status      :complete | :capped}

  `opts`: `:max-hypotheses` (default 8), `:max-depth` (8), and `:keep?`.  Without `:keep?`
  the scratch context is torn down before returning, so the KB is left as it was found
  and every `:handle` is nil; with it the context stands until `abduce-discard!`.
  A vector goal is a conjunction, as for `prove`.  Refuses an unknown or ill-typed option
  (`:unknown-option`), a vector member that is not a sentence (`:shape`) and a variable
  context (`:not-ground`).  A `:keep?` call is refused (`:too-many-kept`) while the KB
  already holds `vaelii.impl.abduce/max-kept` kept contexts; the refusal names them under
  `:contexts`.  See docs/abduction.md."
  ([kb goal] (abduce kb goal 'CxUniverse nil))
  ([kb goal context] (abduce kb goal context nil))
  ([kb goal context opts]
   (check-bound-opts! opts #{:max-hypotheses :max-depth :keep?} "abduce")
   (opts/check-values! opts "abduce")
   (check-shape! (conjunction-goal-problem goal))
   ;; the hypotheses need a context to be stored in, and `?ctx`, which every other query
   ;; fn reads as "any context", names none
   (when-not (and (symbol? context) (not (sx/variable? context)))
     (throw (ex-info (str "abduce needs a concrete context to hang its hypotheses below,"
                          " got " (pr-str context)
                          " — name a context symbol; a variable names none")
                     {:type :not-ground :context context})))
   (abduce/run kb (quasiquote/prepare-conjunction-for-read kb goal context)
               context opts abduce-ops)))

(defn abduce-discard!
  "Discard an abduction's scratch context — every hypothesis in it, and everything they
  licensed.  Takes the result of a `{:keep? true}` `abduce` (or the context symbol
  itself) and answers `{:removed-sentexes n :removed-justifications n}`.  Idempotent, and
  unnecessary after a plain `abduce`, which discards on its own way out."
  [kb result]
  (abduce/discard! kb (if (map? result) (:context result) result) abduce-ops))

(defn- instance-reads
  "The two reads `subsumption-reading`'s shared-instance check makes: `:members`, the
  terms a facts-only `(t ?x)` query answers for type `t`, and `:isa?`, whether term `x`
  is an instance of type `t` at `context`.  Memoized per type and per `[x t]` for one
  audit, which writes nothing between its pairs."
  [kb context]
  {:members (memoize (fn [t] (into [] (map #(get % '?x))
                                   (query kb (list t '?x) context {:max-depth 0}))))
   :isa?    (memoize (fn [x t] (isa? kb x t context)))})

(defn- subsumption-reading
  "`{:statuses ss :witness w :via t}` for types `a` and `b`: `ss` is the set
  `subsumption-statuses` returns, and `w` names what put `:orthogonal` in it — `:declared`,
  `:shared-instance`, `:shared-spec` (a shared subtype with a known `(nonempty t)`) or
  `:unwitnessed-spec` (a shared subtype not known nonempty) — with `t` the instance or the
  subtype it found (nil for `:declared`).  `w` and `t` are nil when `ss` holds no `:orthogonal`.
  `rd` holds the shared-instance check's two reads (`instance-reads`)."
  [kb a b context rd]
  (let [a<b (genl? kb a b)
        b<a (genl? kb b a)
        sep (disjoint? kb a b context)
        ;; the declaration, read facts-only like the shared instance below.  Asked in one
        ;; spelling: `orthogonal` is symmetric, so the goal folds onto the stored order.
        declared? (boolean (seq (query kb (list 'orthogonal a b) context {:max-depth 0})))
        open?     (and (not a<b) (not b<a) (not sep))
        ;; The shared-instance check is facts-only, forced with `{:max-depth 0}` so it
        ;; expands no rule under a caller's `*query-options*` depth: a node-engine search
        ;; of `(a ?x)` over the whole starter, once per taxonomy-open pair, hangs.  Of
        ;; several shared instances the content-least is reported, not the first the
        ;; index returns.
        instance  (when (and open? (not declared?))
                    (nm/min-by-content-key
                     identity
                     (filter #((:isa? rd) % b) ((:members rd) a))))
        ;; A shared subtype counts only when it is not provably empty: a type below two
        ;; separated types, which `disjoint?` reports separated from itself, or
        ;; a type for which a facts-only read answers `(empty c)`.  `wff` refuses a stated
        ;; `(disjoint c c)`.  A facts-only read answers a stated claim and one core.txt's
        ;; `transitiveInArg` declarations carry along `genl`.  A shared subtype with a
        ;; known `(nonempty c)` is the witness; the others mark
        ;; the pair as an overlap with no witness.  Of several, the one with the most
        ;; subtypes is reported, so the audit names the widest shared subtype rather than
        ;; a leaf below it.
        stored?   #(boolean (seq (query kb (list % %2) context {:max-depth 0})))
        [spec ne] (when (and open? (not declared?) (nil? instance))
                    (let [sb  (specs kb b)
                          cs  (nm/by-print-key
                               (filter #(and (contains? sb %) (not= % a) (not= % b)
                                             (not (disjoint? kb % % context))
                                             (not (stored? 'empty %)))
                                       (specs kb a)))
                          nes (filter #(stored? 'nonempty %) cs)
                          pick #(apply max-key (fn [c] (count (specs kb c))) %)]
                      (cond (seq nes) [(pick nes) true]
                            (seq cs)  [(pick cs) false])))
        [w t]     (cond declared? [:declared nil]
                        instance  [:shared-instance instance]
                        ne        [:shared-spec spec]
                        spec      [:unwitnessed-spec spec])]
    {:statuses (cond-> #{}
                 (and a<b b<a)       (conj :coextensional)
                 (and a<b (not b<a)) (conj :genl)
                 (and b<a (not a<b)) (conj :spec)
                 sep                 (conj :disjoint)
                 w                   (conj :orthogonal))
     :witness  w
     :via      t}))

(defn subsumption-statuses
  "The set of applicable subsumption relationships between types `a` and `b`: any subset
  of `#{:coextensional :genl :spec :disjoint :orthogonal}`. A consistent pair yields a
  singleton; an inconsistent pair (e.g. both genl-related and disjoint) yields multiple;
  a pair with no provable relationship yields the empty set.

  `genl?` reads the global cached closure. `disjoint?` and the `:orthogonal` witnesses
  are read from `context` (default `CxUniverse`, the root context), because
  a read sees only its own context and that context's `genlCx` ancestors, and a
  `siblingDisjointException` exempts its pair only where it is seen; a caller whose
  declarations or instances live in a narrower context passes it so they are visible.
  `:orthogonal` has three witnesses: a stated `(orthogonal a b)` (either spelling, the
  predicate being symmetric), which a stored `(siblingDisjointException a b)` answers
  through `(genl siblingDisjointException orthogonal)`; a member of `a` that is also a
  member of `b`; or a type that is a subtype of both and is not provably empty at
  `context` — a type separated from itself or with a known `(empty t)` shows no overlap. The
  declaration and the shared instance are facts-only reads (`{:max-depth 0}`), so the
  status is the same under every query engine. The shared subtypes are read from the
  global `specs` closures, as `genl?` is.

  The declaration stands alone: a declared pair that is also genl-related or separated
  yields both statuses, which `subsumption-status` reads as `:inconsistent`. An exception
  over a pair a mark separates exempts it, so that pair reads `:orthogonal` alone. The
  shared instance and the shared subtype each settle only a pair the taxonomy and the
  separations leave open.

  `:coextensional` is two distinct types each `genl` the other — a `genl` cycle, which
  `wff` refuses at assertion, so it appears only from a belief-state cycle or an equality
  merge, never from a plainly-asserted hierarchy."
  ([kb a b] (subsumption-statuses kb a b 'CxUniverse))
  ([kb a b context] (:statuses (subsumption-reading kb a b context (instance-reads kb context)))))

(defn subsumption-status
  "The subsumption relationship of type `a` to type `b`, one of:
  `:coextensional` (each is `genl` the other), `:genl` (`(genl a b)` holds — `a` is a
  subtype of `b`), `:spec` (`(genl b a)` holds — `a` is a supertype of `b`), `:disjoint`
  (provably no shared instance), `:orthogonal` (a stated `(orthogonal a b)`, or neither
  subsumes the other and not disjoint, but a shared instance the registry answers without
  rule expansion exists, or a shared subtype not provably empty),
  `:unknown` (none of the above is provable), or `:inconsistent` (multiple contradictory
  relationships hold, e.g. both genl-related and disjoint).

  Wraps `subsumption-statuses`: an empty set is `:unknown`, a singleton is that status,
  and two or more contradictory statuses is `:inconsistent`. `context` is the vantage
  `:disjoint` and `:orthogonal` are read from (default `CxUniverse`); see
  `subsumption-statuses`."
  ([kb a b] (subsumption-status kb a b 'CxUniverse))
  ([kb a b context]
   (let [ss (subsumption-statuses kb a b context)]
     (case (count ss)
       0 :unknown
       1 (first ss)
       :inconsistent))))

(defn disjointness-audit
  "The `subsumption-status` of every unordered pair of distinct types **visible from
  `context`**: the genl nodes `context` sees, less each `relation?` at `context`.
  Returns
  `{:types n :pairs n :by-status {status count …} :pairs-data [{:a t :b t :status s :statuses ss} …]}`. `genl?` reads the global closure and `disjoint?` reads the closure
  visible from `context`, and the shared-instance query runs only for a pair the
  taxonomy and disjoint declarations leave open — forced facts-only (`{:max-depth 0}`),
  so the N² sweep expands no rule.
  `context` is the vantage the swept type set, `disjoint?` and the `:orthogonal`
  witnesses are all read from (default `CxWell`, which sees every non-opt-in middle context — every
  context below it, and no opt-in theory). A type a context sees only through an
  opt-in theory `context` does not see is outside both the sweep and the coverage it
  reports, by construction: visibility is one reading, not two. Each entry carries both
  the resolved `:status` keyword and the raw `:statuses` set from `subsumption-statuses`,
  so contradictions are visible without re-querying. The `:unknown` pairs are the
  candidates for a missing `disjoint` or `orthogonal` assertion; a declared `orthogonal`
  pair reads `:orthogonal`, never `:unknown`. An entry whose `:statuses` holds
  `:orthogonal` also carries `:witness` — `:declared`, `:shared-instance`, `:shared-spec`
  or `:unwitnessed-spec` — and, for the last three, `:via`, the instance or the subtype
  found. A shared subtype with a known `(nonempty t)` is a `:shared-spec`, and a shared
  subtype not known nonempty is an `:unwitnessed-spec`."
  ([kb] (disjointness-audit kb 'CxWell))
  ([kb context]
   ;; `by-print-key`, never bare `sort`: a type node need not be a symbol.  A NAT — a
   ;; function term standing for a collection an imported ontology has no atomic name for —
   ;; is a list, and `compare` throws on one rather than ordering it, so the N² sweep threw
   ;; a bare `ClassCastException` on such a KB.  `disjoint-line` orders the same nodes the
   ;; same way.
   ;; A relation is a genl node when `genl` specializes it by another — (genl performedBy
   ;; doneBy), (genl partition covering) — but it has no instances to share or keep
   ;; apart, so every pair it entered could only read :unknown.
   (let [ts   (into [] (remove #(relation? kb % context)) (nm/by-print-key (types kb context)))
         n    (count ts)
         rd   (instance-reads kb context)
         data (with-open [r (progress/start ::disjointness-audit
                                            "disjointness audit: read the type pairs"
                                            (quot (* n (dec n)) 2))]
                (persistent!
                 (reduce
                  (fn [acc i]
                    (reduce
                     (fn [a j]
                       (let [{ss :statuses w :witness t :via}
                             (subsumption-reading kb (nth ts i) (nth ts j) context rd)]
                         (progress/tick! r)
                         (conj! a (cond-> {:a        (nth ts i)
                                           :b        (nth ts j)
                                           :statuses ss
                                           :status   (case (count ss)
                                                       0 :unknown
                                                       1 (first ss)
                                                       :inconsistent)}
                                    w (assoc :witness w)
                                    t (assoc :via t)))))
                     acc (range (inc i) n)))
                  (transient []) (range n))))]
     {:types     n
      :pairs     (count data)
      :by-status (frequencies (map :status data))
      :pairs-data data})))

(defn query-plan
  "How a goal would be answered, at whichever of the two scales the goal has.

  A **single sentence** gives the provers applicable to it with their per-prover
  estimates — which methods could answer it, what each expects to cost, and **which of
  them actually run**.  Applicable is not consulted: when one prover may answer the
  goal alone the engine runs it alone, so every other entry carries `:runs? false` and
  a `:shadowed-by` naming what displaced it.  And a prover claiming to be complete can
  *still* not run alone, when a source none of them reads bears on this goal — those
  entries carry `:guarded-by` naming it, which is what makes a union diagnosable
  rather than merely visible.

  A **vector** — the conjunctive query `prove` takes — gives the *join plan* instead:
  the conjuncts in the order they will run, each a map of `:goal`, `:bound-before` (the
  variables bound when it starts), `:est-matches` (the sound upper bound on its fan-out
  under those bindings), `:est-rows` (the expected size of its own relation),
  `:est-prefix` (the expected rows of the plan through it), `:block` (the group of
  literals it ran with) and the flags `:deferred?`, `:recursive?` and `:isolated?` (a
  cartesian factor held to the back).  docs/inference.md, \"Conjunctive query planning\",
  reads them.

    (query-plan kb '[(dog ?y) (parentOf Tom ?y)] 'CxMantle)
    ;; => ({:goal (parentOf Tom ?y) :est-matches 2 :bound-before #{}    ...}
    ;;     {:goal (dog ?y)          :est-matches 1 :bound-before #{?y}  ...})"
  ([kb goal] (query-plan kb goal '?ctx))
  ([kb goal context]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (checked-ist-goal kb goal context)]
     (if (vector? goal)
       (plan/explain kb goal context)
       (provers/plan kb goal context)))))

(defn search-tree
  "The backward search for `goal` in `context`, as data — every node the frontier reached,
  not only the path that answered.  `query-plan` is the plan; this is the run that plan
  predicted, one step later: where `query {:proof? true}` returns the proof that *worked*,
  this returns the whole tree it worked in — the frontier, what each node cost, and what
  got dropped before it was expanded.  The read behind the inference debugger.

  Needs a depth (`{:max-depth n}`, or `*query-options*` `:max-depth`), the
  same as `query` under `:proof? true` and for the same reason: with no rule expanded there
  is no search to show.  It runs the search `query` runs — the registry as the leaf, so an
  antecedent is answerable by any prover — so the tree and the answers match `query`'s.

  Bounded so a large KB cannot turn one read into an unbounded search: the depth bound, a
  node-expansion budget (`:node-budget`, default `inference/default-node-budget`), and an
  optional wall-clock `:max-ms` that reports `:timeout` rather than hanging.  With
  `:max-depth` and `:strategy` those four are the whole key set (`search-tree-opt-keys`) —
  a debugger read is a fixed mode of `query`'s search, so `query`'s remaining keys are ones
  this entry point overwrites or never reads; a key outside it is refused (`:unknown-option`),
  as at `query`.

  Returns `{:goals :context :strategy :status :bounded? :answers :nodes :stats
  :unenumerated :unenumerated-in-guards}`; `:status` is `:complete`, `:bounded` or `:timeout`, and each answer
  carries the `:node` it came off.  `:unenumerated` is `query-status`'s: the transitive
  predicates whose closure a goal asked with both arguments open did not enumerate.
  Reads-only, like every query in this engine."
  ([kb goal] (search-tree kb goal '?ctx nil))
  ([kb goal context] (search-tree kb goal context nil))
  ([kb goal context opts]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (checked-ist-goal kb goal context)
         d     (query-depth opts search-tree-opt-keys "search-tree")
         goals (quasiquote/prepare-conjunction-for-read kb goal context)]
     (inference/search-tree kb goals context
                            (query-node-opts kb context d opts)))))

(defn compare-tacticians
  "Run `goal` in `context` under several **tacticians** — the node engine's search
  orderings — each to completion, and return one row per tactician: the search it ran, its
  wall-clock, its `:status`, its `:unenumerated` and its answer set.  What the debugger
  tables side by side.  A row reads `:incomplete` where it would read `:complete` when a
  both-open goal over a transitive predicate went unenumerated (docs/anytime.md).

  Every tactician only reorders the frontier, so the answer sets **must be identical**;
  the point of running them side by side is that a caller can verify it rather than trust
  it, and see the latency each ordering pays for the same answers.  A row whose answers
  differ from the others is a bug the completeness sweep says cannot happen — surfaced,
  not swallowed.

  `opts` is `compare-tacticians-opt-keys`: `search-tree`'s two bounds and its depth, plus
  `:tacticians` — the subset to run (`inference/default-compare-tacticians` otherwise) —
  and **not** `:strategy`, which this entry point sets per row and would otherwise accept and
  discard.  Needs a depth for the same reason `search-tree` does, and is bounded the same
  three ways; `:status` and `:ms` are per row."
  ([kb goal] (compare-tacticians kb goal '?ctx nil))
  ([kb goal context] (compare-tacticians kb goal context nil))
  ([kb goal context opts]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (checked-ist-goal kb goal context)
         d     (query-depth opts compare-tacticians-opt-keys "compare-tacticians")
         goals (quasiquote/prepare-conjunction-for-read kb goal context)]
     (inference/compare-tacticians kb goals context
                                   (query-node-opts kb context d opts)))))

(defn add-prover
  "Register an additional prover on `kb`: a value `prover` builds, or a record implementing
  `vaelii.impl.types.prover/Prover`."
  [kb prover]
  (swap! (:provers kb) conj prover) kb)

(defn prover
  "A prover built from plain fns, the value `add-prover` registers.  Every fn takes
  `[kb goal context]`.

      (prover {:applicable? (fn [kb goal context] …)   ; does this prover answer the goal?
               :solve       (fn [kb goal context] …)}) ; a seq of binding maps

  A prover whose answers are read from **stored facts** gives `:solve-with-support` in
  place of `:solve`, with the two sets that go with it, and a forward rule that fired on
  one of its answers is withdrawn when a fact the answer named is retracted:

    :solve-with-support  a seq of `[bindings support]`, `support` the handles (`:id` of a
                         `sentexes-matching` result) of the facts the answer was read from.
                         `solve` answers its bindings, in its order.
    :support-functors    the predicates it answers with support, a non-empty set
    :support-sources     the predicates it reads to answer them, a set: a fact on one of
                         them re-joins the rules over a support functor, whichever arrived
                         first

  Three readings take a constant or a fn: `:est-bindings` (a non-negative number; 1 for a
  ground goal and unbounded for an open one by default), `:cost` (`:lookup`, `:compute` or
  `:search`; `:compute` by default) and `:completeness` (0 to 100; 50 by default, so the
  stored facts answer beside it).

  Refused with `:unknown-option`: a key outside these eight, a missing `:applicable?`, both
  or neither of the two solve keys, a support key without its companions, and a value
  outside its domain, which a fn's return is checked against at each call too.  A support
  element that is not a handle is refused as the answer is read (docs/inference.md, *What a
  computed answer rests on*)."
  [spec]
  (provers/fn-prover spec))

(defn add-evaluatable
  "Register a plain Clojure fn `f` as the evaluatable predicate/function `pred` on `kb` —
  the one-liner for a *computed* relation, so a caller wanting one need not hand-write a
  five-method `vaelii.impl.types.prover/Prover`.  Two shapes, chosen by `opts`:

  * a **check** predicate — `(add-evaluatable kb 'evenSum (fn [a b] (even? (+ a b))))`
    makes `(evenSum 2 4)` hold and `(evenSum 1 2)` fail; every argument must be ground;
  * a **result-binding** function — `(add-evaluatable kb 'sumOf + {:result :first})`
    binds `(sumOf ?r 2 3)` to `?r = 5`; the output slot `:result` names may be a variable
    to bind or a value to check, and the rest are the ground inputs `f` receives.

  `opts` (a map, or nil) is `provers/evaluatable`'s — `:result`, `:arity`, `:cost` and
  `:completeness`, whose defaults (`:lookup`, 100) suit a purely computed relation.  A key
  off that four is **refused** (`:unknown-option`): `provers/evaluatable` reads those and
  nothing else, so a misspelt `:reslt` or `:copmleteness` would take its default in
  silence — a check predicate where a result-binding was meant, or the authoritative-
  computation claim where a KB also stores facts under the predicate.  The
  fn is a real fn value the caller supplies, so this evaluates no KB data through
  `clojure.core/eval`.  Composes with `add-prover` and returns `kb`; the wrapped fn then
  answers a direct `ask` / `query` goal and — the node engine's leaf being the registry —
  discharges a conjunct or rule antecedent inside a `query` with a `:max-depth`, where it
  appears as a `:leaf` of the derivation.  Forward materialization reaches it
  too: a forward rule's antecedent over `pred` is computed through the registry
  (`chain/deferred-antecedent?`).  The DFS `prove`, whose leaf is the stored facts, does
  not reach it (docs/inference.md)."
  ([kb pred f] (add-evaluatable kb pred f nil))
  ([kb pred f opts]
   (opts/check! opts #{:result :arity :cost :completeness} "add-evaluatable"
                (str "An option nothing reads takes the default in silence, which for a"
                     " computed relation means a shape or a cost tier the caller did not"
                     " choose."))
   (add-prover kb (provers/evaluatable pred f opts))))

(defn register-modal-predicate
  "Grant `pred` belief-style projection: after this, `(pred agent sentence)` is answered
  by proving `sentence` in `agent`'s context, exactly as `believes` is (see
  docs/belief.md).  A thin convenience over asserting the `(modal_predicate pred)` marker
  — the grant is an ordinary belief, so it follows retraction and, read scoped, is a
  *policy of the context* that holds it: with no `context` it is granted in `CxUniverse`
  where the default `believes` grant lives, so every ordinary query context sees it;
  pass a `context` to scope the grant to the theory that wants it.  Returns `kb`.

  Bare, like every other adder on this surface: it asserts one marker sentex and
  `retract!` of that marker takes the grant back, so there is nothing here the KB cannot
  undo (the `!` list is in docs/api.md)."
  ([kb pred] (register-modal-predicate kb pred sx/root-context))
  ([kb pred context] (assert kb (list 'modal_predicate pred) context) kb))

;; ---- the optional reasoners ---------------------------------------------
;; Eleven reasoners ship without being registered, and until one is, its vocabulary is
;; ordinary content: a KB stores `(before A B)` and `(before B C)`, retrieves both, and
;; does not derive `(before A C)`.  That is the right default — an algebra's fixpoint is
;; not free, and most KBs use none of them — but the *provers* live in `vaelii.impl.*`,
;; and `vaelii.core` is the only namespace anything outside this repo may name.  So
;; without a named list here, opting in means reaching past the boundary, and a subsystem
;; nobody can ask for is one nobody has.
;;
;; Named by keyword and resolved at runtime, so requiring this namespace does not drag
;; in eight leaf algebras — the same discipline `calculus-vars` and `imperative` use.

(def ^:private reasoner-vars
  "The reasoners a KB can register, and the var holding each one's constructor.  Six are
  the relation algebras `calculi` describes; `:duration` and `:metric-time` are the
  quantitative pair over the same intervals and instants (docs/duration.md,
  docs/stp.md), `:sign` is the qualitative arithmetic over quantities nobody has put
  a figure on (docs/sign.md), and `:calendar` is the clock behind the calendar
  constructors — a calendar term's endpoints and the orderings they give, computed from
  its fields and stored nowhere (docs/time.md).  `:includes-instant` reads a temporal
  thing against a moment off the point network, answering `(includesInstant X t)` and its
  negation (docs/time.md).  `:brave-cautious` is the odd one out — not
  an algebra but the ASP brave/cautious reader over the current dilemmas, answering
  `(bravely S)` / `(cautiously S)` as a read and storing nothing (docs/labeling.md)."
  '{:rcc8        vaelii.impl.space/spatial-prover
    :cardinal    vaelii.impl.orientation/orientation-prover
    :relative    vaelii.impl.relative/relative-prover
    :distance    vaelii.impl.distance/distance-prover
    :allen       vaelii.impl.interval/allen-prover
    :point       vaelii.impl.point/point-prover
    :duration    vaelii.impl.duration/duration-prover
    :metric-time vaelii.impl.stp/stp-prover
    :sign        vaelii.impl.sign/sign-prover
    :calendar    vaelii.impl.calendar/calendar-prover
    :includes-instant vaelii.impl.point/includes-instant-prover
    :brave-cautious vaelii.impl.asp.prover/brave-cautious-prover})

(defn reasoners
  "The names of the optional reasoners, sorted — what `add-reasoner` takes.  `calculi`
  describes the six that are relation algebras in full; the other five are the
  quantitative reasoners, the calendar clock and the instant-inclusion reader, and
  `:brave-cautious` is the ASP dilemma reader (docs/labeling.md)."
  []
  (vec (sort (keys reasoner-vars))))

(defn reasoner
  "The prover named by keyword — a value for `add-prover`, or for a caller assembling a
  registry of its own.  `add-reasoner` is the ordinary way in."
  [nm]
  (if-let [sym (reasoner-vars nm)]
    ((requiring-resolve sym))
    ;; `:unknown-option` for `the-calculus`'s reason: naming a reasoner that does not exist is a
    ;; bad argument from a caller, never something a sentence can be checked into
    (throw (ex-info (str "no such reasoner: " nm " — want one of "
                         (str/join ", " (map pr-str (reasoners))))
                    {:type :unknown-option :mismatch :bad-value :reasoner nm :known (reasoners)}))))

(defn add-reasoner
  "Register one or more shipped reasoners on `kb` by name, returning `kb`.

      (doto (open-kb {}) (add-reasoner :allen :rcc8))

  Registration is the whole of the opt-in, and it is per-KB: an unregistered algebra's
  facts are stored and retrieved as ordinary facts and added no work.  Registering
  changes what is *derivable*, not what is stored — the entailed relation is computed
  from the network the stored facts constrain, carries the handles it rests on as its
  support, and so can be forward-chained on and retracted through like any other
  antecedent (docs/qcn.md).

  Idempotent per name: registering one twice would have the goal claimed twice and
  answered identically, so the second is dropped rather than paid for.  Sameness is the
  prover **value**, not its class — the six algebras share one record type and differ
  only in the calculus they carry, so a class check would register the first and silently
  drop the other five."
  [kb & names]
  (let [want (mapv reasoner names)                      ; resolve all before mutating any,
        have (set @(:provers kb))]                      ; so a bad name registers nothing
    (doseq [pr want :when (not (contains? have pr))]
      (add-prover kb pr)))
  kb)

;; ---- qualitative constraint reasoning -----------------------------------
;; Registering a calculus prover is enough to *use* a relation algebra — `ask` answers
;; a goal about one pair — and not enough to *see* one.  What an algebra actually
;; computes is the whole network a context's facts constrain, and a subsystem readable
;; only a pair at a time cannot be browsed, diagnosed, or shown its own contradiction.
;; These four reads expose it (docs/qcn.md).
;;
;; They are **reads**: nothing here registers a prover, and a calculus answers whether
;; or not its prover is registered, because a network is a property of the stored facts
;; rather than of the query engine.  A calculus is named by keyword and its namespace
;; resolved at runtime, so requiring this namespace does not drag in six leaf algebras
;; — the discipline `imperative` uses to keep the ASP backend optional.

(def ^:private calculus-vars
  "The shipped qualitative calculi: the keyword naming one, and the var holding it."
  '{:rcc8     vaelii.impl.space/rcc8
    :cardinal vaelii.impl.orientation/cardinal
    :relative vaelii.impl.relative/relative
    :distance vaelii.impl.distance/qualitative-distance
    :allen    vaelii.impl.interval/allen
    :point    vaelii.impl.point/instants})

(defn- the-calculus
  "The calculus named by `nm`, or a throw naming the ones there are."
  [nm]
  (if-let [sym (calculus-vars nm)]
    @(requiring-resolve sym)
    ;; `:unknown-option`, not a type of its own: naming a calculus that does not exist is a bad
    ;; argument from a caller, never something a sentence can be checked into, and the
    ;; `:type` vocabulary is what the editor renders a *check problem* as.
    (throw (ex-info (str "no such qualitative calculus: " nm
                         " — want one of " (str/join ", " (sort (keys calculus-vars))))
                    {:type :unknown-option :mismatch :bad-value :calculus nm
                     :known (vec (sort (keys calculus-vars)))}))))

(defn calculi
  "The shipped qualitative calculi as data — one map apiece, naming the calculus, the
  base relations it distinguishes (jointly exhaustive and pairwise disjoint, so exactly
  one holds of any two terms), the identity it puts on the diagonal, and the predicates
  it claims.  The vocabulary each ships is loaded either way; the prover is opt-in."
  []
  (vec (for [nm (sort (keys calculus-vars))
             :let [c (the-calculus nm)]]
         {:calculus   nm
          :base       (:universe (:algebra c))
          :identity   (:identity (:algebra c))
          :predicates (into (sorted-set) (:predicates c))})))

(defn- check-context-read!
  "Refuse a query context at a read that does not resolve one, naming `entry-point`
  (`:unsupported-context`): `checked-ist-goal`'s refusal for an entry point that takes no
  goal.  Unrefused, a network read answers `{:nodes [] :consistent? true}`."
  [context entry-point]
  (when (nm/query-context? context)
    (throw (ex-info (str context " is a query context, and " entry-point " does not resolve one — "
                         "it would reach the engine as an ordinary context nothing is "
                         "asserted in, and answer as though the KB were empty and "
                         "consistent.  Name a context, or read with query / ask / prove / "
                         "sentexes-matching, which do resolve one.")
                    {:type :unsupported-context :context context}))))

(defn qualitative-network
  "The constraint network `calculus` computes over everything **believed and visible**
  in `context`: every pair of terms its predicates relate, tightened by path
  consistency to the base relations still possible between them.

    {:calculus :rcc8  :context CxWell
     :nodes [A B C]   :consistent? true
     :constraints {[A B] #{:ntpp} [B A] #{:ntppi} …}}

  A pair constrained to one relation is determined; a pair with several is genuinely open;
  an unrecorded pair is unknown (every base relation).  When the believed facts are
  unsatisfiable `:consistent?` is false, `:constraints` is the network **as stated**
  rather than a tightened one, and `:unsatisfiable` names the pairs no model satisfies
  as written — empty when only composition found the clash, which is the case with no
  single pair to blame.

  When a network the calculus reads is unsatisfiable — the metric or the point network
  under `:allen` — `:unsatisfiable-sources` names it, one map per unsatisfiable component
  of the source holding an interval's endpoint:

    {:source :metric :pairs [[P Q] …] :cycle [P Q R] :support [handle …]}

  `:pairs` are that network's pairs unsatisfiable as written, `:cycle` the instants on a
  negative cycle (`:metric` only), `:support` the facts behind them.  A metric problem
  refused for spanning more than one dimension names its `:dimensions` in place of
  `:pairs` and `:cycle`.  The interval pairs emptied to make the component unsatisfiable
  are not in `:unsatisfiable` (docs/qcn.md, \"A network can have a second reader\").

  A variable context reads every context's facts into one diagnostic network, off which
  no goal is answered (docs/qcn.md, \"Which networks it joins against\")."
  [kb calculus context]
  (check-context-read! context "qualitative-network")
  (let [calc  (the-calculus calculus)
        net   (qkb/network kb calc context)
        ns'   (qkb/nodes net)
        pc    (qkb/tighten kb calc context net nil)
        bad?  (= :inconsistent pc)]
    (cond-> {:calculus    calculus
             :context     context
             ;; a node may be a NAT and a pair always is a vector, so both are keyed
             ;; through the guarded printer rather than through `str`
             :nodes       (nm/by-print-key ns')
             :consistent? (not bad?)
             :constraints (if bad? net pc)}
      bad? (assoc :unsatisfiable (nm/by-print-key (qkb/unsatisfiable-as-written
                                                   kb calc context)))
      bad? (merge (when-let [srcs (qkb/reported-sources kb calc context)]
                    {:unsatisfiable-sources srcs})))))

(defn possible-relations
  "The base relations `calculus` still allows between `a` and `b`, given everything
  believed in `context` — the set `ask` checks a goal against, exposed directly.  A
  singleton is a determined arrangement; the full set is total ignorance; `#{}` means
  `a` or `b` lies in an unsatisfiable component of the network, and no goal naming it is
  answered there.

  A variable context reads every context's facts into one diagnostic network, which is
  not the set `ask` checks against (docs/qcn.md, \"Which networks it joins against\")."
  [kb calculus context a b]
  (check-context-read! context "possible-relations")
  (qkb/possible (the-calculus calculus) kb context a b))

(defn qualitative-scenario
  "One concrete arrangement consistent with everything believed in `context` —
  `{[a b] → relation}`, one base relation per pair — or nil when the believed facts are
  unsatisfiable.  Which arrangement is a function of the facts alone, never of the
  order they arrived, so it is repeatable and comparable across KBs.

  Path consistency leaves a *set* per pair; this picks one member of every set at once,
  which is the difference between \"nothing rules this out\" and \"here is a world\".

  **A variable context is not a reader here.**  The arrangement is then drawn from the
  union network — every context's facts in one — where two incomparable contexts compose
  for nobody, so it is a diagnostic reading of everything stored rather than a world any
  reader sees (docs/qcn.md)."
  [kb calculus context]
  (some-> (scenario/scenario (the-calculus calculus) kb context) scenario/relations))

(defn qualitative-scenarios
  "Up to `limit` distinct arrangements, as `qualitative-scenario` renders one.  The
  number of scenarios is exponential in the node count, so the bound is required rather
  than optional — an unbounded enumeration is not something to reach for by accident."
  [kb calculus context limit]
  ;; typed, not a cast error: over the daemon a string limit answered
  ;; `500 :internal-error` where the sibling `find-terms :limit` refusal is typed.
  ;; Unconditional, unlike the two optional caps: here the bound is required, so an
  ;; absent one is a bad value rather than a request for no cap.
  (check-limit! limit "qualitative-scenarios limit")
  (mapv scenario/relations
        (scenario/scenarios (the-calculus calculus) kb context {:limit limit})))

;; ---- resource-bounded / anytime inference -------------------------------
;; The query paths are lazy, so a budget is the *consumer* discipline of realizing
;; the answer stream under a bound and reporting whether it ran dry (`:complete`) or
;; was cut short (`:timeout` / `:capped`) — and resumption is free, because the
;; unrealized tail (or, for `prove`, the DFS goal stack) *is* the continuation.  A
;; budget is a map of optional bounds; the partial-result contract is documented in
;; vaelii.impl.budget.

(defn ask-within
  "Anytime `ask`: answer `goal` in `context`, but bounded by `budget` — a map of any
  of `{:max-ms n :max-results n :max-cost <tier>}`.  Returns the partial-result
  contract `{:results :status :count :elapsed-ms :resume :unenumerated
  :unenumerated-in-guards}` (see vaelii.impl.budget): `:results` are the solutions
  realized in *this* step, `:status` is `:complete` / `:incomplete` / `:timeout` /
  `:capped`, and `:resume` (nil when `:complete` or `:incomplete`) continues the same
  search under a fresh budget via `resume`.  `:incomplete` is a run that ran dry after a
  both-open goal over a transitive predicate named in `:unenumerated` (docs/anytime.md).

  `:max-ms` and `:max-results` bound how much of the (lazy) answer stream is
  realized; `:max-cost` is qualitative — it drops every prover whose `cost` tier is
  above the ceiling *before* the stream is built (`:lookup` < `:compute` <
  `:search`), so `{:max-cost :lookup}` answers from cached closures and the index but
  runs no closure fixpoint and no backward search.  A `:max-cost` that is not one of
  those three throws (`:type :unknown-option`) rather than being read as no ceiling: a caller
  writing `:cheap` for `:lookup` is asking to *exclude* the expensive tier, and
  quietly running it is the one reading of a typo that is certainly wrong.

  Same answers as `ask` when the budget is generous enough to run dry — the goal
  prepared the same way included (`prepare-goal-for-read`), so a NAT or a retired
  spelling is the same question here that it is there.  A bounded run is a strict
  prefix of `ask`'s stream, so concatenating `:results` across `resume` steps
  reconstructs it."
  ([kb goal budget] (ask-within kb goal '?ctx budget))
  ([kb goal context budget]
   ;; `ask`'s entry point, since this is `ask` bounded: a goal it refuses cannot be one this
   ;; answers, or the budget would decide which spelling is legal
   (check-shape! (sentence-goal-problem goal))
   ;; the budget against `ask`'s half of the key set: `:max-ms` / `:max-results` /
   ;; `:max-cost`, and not `:max-depth` / `:max-term-growth`, which bound a rule expansion
   ;; `ask` does not do (`budget/ask-budget-keys`).  `collect` below re-checks against the
   ;; union, so a `resume` under either entry point still passes; this is the split the
   ;; entry point owes.  Value checks ride along, so a string `:max-ms` is `:unknown-option`
   ;; and not the bare cast it would be inside `deadline`.
   (budget/check-budget! budget budget/ask-budget-keys "ask-within")
   (let [[goal context] (checked-ist-goal kb goal context)
         goal    (quasiquote/prepare-goal-for-read kb goal context)
         ;; a variable context reads each handle at its own context, as `ask` does
         ;; the stream is lazy, so the collector is bound per pull (`collecting-seq`), and
         ;; one collector serves every step and the rebuilt stream a restart pulls
         una     (provers/unenumerated-collector)
         answers #(provers/collecting-seq
                   una
                   (fn []
                     (if (sx/variable? context)
                       (binding [exc/*unscoped-own* true]
                         (exc/own-seq (provers/ask-capped kb goal context (:max-cost budget))))
                       (provers/ask-capped kb goal context (:max-cost budget)))))]
     (budget/reporting-unenumerated (budget/collect (answers) budget answers)
                                    #(provers/unenumerated-report una)))))

(defn- run-prove-step
  "One bounded step of the DFS prover, wrapped in the anytime contract.  The
  continuation captures the *remaining* goal stack, so `resume` picks the search up
  exactly where it stopped rather than restarting it.

  The budget's keys are listed here as well as in `budget/collect`, because this is the one
  consumer that does not go through `collect` — the DFS arm reads its bounds directly,
  and a `resume` hands each step a fresh budget of its own to hold to the key set.

  The bounds map is **`budget/prove-bounds`** and never one written here, for the reason
  that fn exists: the key set and the translation are two halves of one claim, and a bound
  listed there but not built here passes `check-budget!` and is then dropped — a caller
  raising `:max-term-growth` told nothing, and answered under the shipped ceiling."
  [kb context budget stack una]
  (budget/check-budget! budget)
  (let [rules-fn (fn [g] (provers/candidate-rules kb g context))
        bounds   (merge (budget/prove-bounds budget) (registry-leaf kb context))
        start    (System/nanoTime)
        {:keys [solutions status stack]} (binding [provers/*unenumerated* una]
                                           (res/prove-from kb rules-fn context bounds stack []))]
    (budget/from-batch solutions status start
                       (fn [b] (run-prove-step kb context b stack una)))))

(defn prove-within
  "Anytime `prove`: run the depth-first backward chainer over `goal` (a sentence or a
  conjunction vector, as `prove`) in `context`, bounded by `budget` — a map of any of
  `{:max-ms n :max-results n :max-depth n :max-term-growth n}`.  Returns the same
  partial-result contract as `ask-within`, `:incomplete` and `:unenumerated` included,
  and `resume` continues from the unfinished goal stack (docs/anytime.md).

  `:max-depth` bounds *transformation* depth — the number of rule expansions the
  search may stack — so a runaway or merely deep proof yields a `:timeout` /
  `:capped` partial you can inspect and then `resume` with a larger budget.

  `:max-term-growth` is the DFS's **other** termination guard and the one a caller
  raises rather than lowers: a rule that wraps its subgoal in one more compound per
  expansion is cut when the nesting runs `res/default-max-term-growth` levels past the
  deepest term its own path has met, so an answer sitting further out than that is
  reachable only by naming a larger ceiling.  Absent, the shipped one holds — the bound
  is a guard rather than a budget, so leaving it out is not asking for no ceiling.

  (`:max-cost` bounds `ask`'s prover tiers, and is ignored here: `:max-depth` bounds the
  search.)"
  ([kb goal budget] (prove-within kb goal '?ctx budget))
  ([kb goal context budget]
   (check-shape! (conjunction-goal-problem goal))
   ;; the budget against `prove`'s half of the key set — `:max-ms` / `:max-results` /
   ;; `:max-depth` / `:max-term-growth`, and not `:max-cost`, an `ask` concept `prove`
   ;; ignores (`budget/prove-budget-keys`).  **Before `inference-engine?` reads
   ;; `:max-depth`**: the node-engine selector takes `(long max-depth)`, so a string depth
   ;; is a bare cast here unless the value check has already refused it, and the node arm
   ;; never reaches `search-within`'s own `check-budget!`.
   (budget/check-budget! budget budget/prove-budget-keys "prove-within")
   (let [[goal context] (checked-ist-goal kb goal context)
         goals (quasiquote/prepare-conjunction-for-read kb goal context)]
     (if (inference-engine? (:max-depth budget))
       ;; the node engine's continuation is the session itself — the frontier behind
       ;; it is a value the session holds, and so is its collector — and the bounds are
       ;; checked per node expansion rather than per yielded solution
       ;; (`inference/search-within`), so a wide unproductive stretch cannot run past
       ;; the deadline
       (let [sess (inference/session kb goals context
                                     (merge (query-options (:max-depth budget))
                                            (registry-leaf kb context)))]
         (budget/reporting-unenumerated (inference/search-within sess budget)
                                        #(inference/unenumerated sess)))
       ;; the DFS's continuation is the goal stack, so the collector rides the closure
       (let [una (provers/unenumerated-collector)]
         (budget/reporting-unenumerated
          (run-prove-step kb context budget
                          (res/initial-prove-stack kb goals context
                                                   (:est-override (registry-leaf kb context)))
                          una)
          #(provers/unenumerated-report una)))))))

(defn resume
  "Continue a `:timeout` / `:capped` partial result from `ask-within` / `prove-within`
  under a fresh `budget`, returning the next partial result, whose `:unenumerated` holds
  every step's.  A `:complete` or `:incomplete` result has no continuation and is
  returned unchanged (docs/anytime.md), so

    (loop [r (ask-within kb goal ctx budget)]
      (consume (:results r))
      (when (:resume r) (recur (resume r budget))))

  terminates when the search is exhausted."
  [partial budget]
  (budget/resume partial budget))

;; ---- the lookup-to-query stack ------------------------------------------
;; Eight named levels of escalating machinery over one goal, so the cost of an
;; answer is legible: level 0 is a raw index read, level 7 is `ask`.  See
;; vaelii.impl.levels for what each level adds.

(defn lookup
  "Answer `goal` in `context` using exactly the machinery of `level`:

    0 :raw      handles at an index location  4 :typed    + genl spec walk
    1 :extent   one literal context           5 :closed   + transitive closure
    2 :local    + unification                 6 :solved   full provers, no rules
    3 :visible  + genlCx inheritance          7 :proved   full stack

  A lazy seq of {:level :handle :sentence :context :bindings}; a field the level
  cannot supply is nil.  A result read off the store carries its handle: every result
  of levels 0-4, and the level-4 matches level 5 includes.  A closure answer at level 5
  and every answer of levels 6-7 is derived and carries none.  Each
  level adds one mechanism to the one below, so an answer that appears at level n
  and not at n-1 is attributable to that mechanism.

  At level 0 a *vector* goal is taken as an index path directly; anywhere else the
  goal is a sentence."
  ([kb level goal] (lookup kb level goal '?ctx))
  ([kb level goal context]
   (let [[goal context] (checked-ist-goal kb goal context)]
     (lvl/lookup kb level goal context))))

(defn escalate
  "The cheapest level that answers `goal` — climb the stack from `floor` and stop at
  the first level with results.  Returns {:level :name :results :tried}; `:results`
  is that level's lazy seq, so the climb costs one result per level tried.  Nothing
  answers → :level nil.  `:unenumerated` is present when the stopping level's probe
  answered a both-open goal over a transitive predicate from its extent (docs/levels.md).

  `floor` defaults to 2, the first level that answers a *goal* rather than a
  question about storage: level 1 ignores the goal's arguments and level 0 ignores
  belief, so either can report a hit it cannot verify.  Pass 0 to include them.

  `opts` is `escalate-opt-keys`: `{:max-ms n}`, a deadline on the climb.  A climb it
  stops before any level answered comes back `{:level nil :status :timeout}`, which is
  not a nothing-answers result.  Beside `opts`, a nil `floor` is the default floor."
  ([kb goal] (escalate kb goal '?ctx))
  ([kb goal context]
   (let [[goal context] (checked-ist-goal kb goal context)]
     (lvl/escalate kb goal context)))                ; `levels/query-floor` owns the default
  ([kb goal context floor]
   (let [[goal context] (checked-ist-goal kb goal context)]
     (lvl/escalate kb goal context floor)))
  ([kb goal context floor opts]
   (check-search-opts! opts escalate-opt-keys "escalate")
   (let [[goal context] (checked-ist-goal kb goal context)]
     (lvl/escalate kb goal context (if (nil? floor) lvl/query-floor floor) opts))))

(defn explain-levels
  "What every level yields for `goal`: a seq of {:level :name :count}.  The level at
  which the count first rises is the machinery the answer depends on.  A diagnostic —
  it counts, so unlike `lookup` it realizes every level fully.  A row carries
  `:unenumerated` when its count lacks the closure pairs of a both-open goal over a
  transitive predicate (docs/levels.md).

  This explains the *retrieval stack*, not belief: it says which machinery reaches a
  sentence, not why the KB holds it.  For that, see `why` / `why-not`, which walk the
  justification graph."
  ([kb goal] (explain-levels kb goal '?ctx))
  ([kb goal context]
   (let [[goal context] (checked-ist-goal kb goal context)]
     (lvl/explain kb goal context))))

(defn levels
  "The stack as data: {:level :name :below :adds} per level."
  [] lvl/level-table)

(defn- clash-grounds?
  "Does `opts` ask a clash report for its `:grounds`?  Yes unless `{:grounds? false}`.
  An opts key the reports do not read is refused, as at the extent readers."
  [opts fn-name]
  (opts/check! opts #{:grounds?} fn-name
               "An option nothing reads takes the default in silence, which here means the grounds are read.")
  (opts/check-values! opts fn-name)
  (not (false? (:grounds? opts))))

(defn- contradictions-read
  "The unranked dilemmas `contradictions` reports for `context`: KB-wide for a nil or
  variable one."
  [kb context]
  (if (or (nil? context) (sx/variable? context))
    (clashes/contradictions-of kb)
    (clashes/contradictions-at kb context)))

(defn conflicts
  "The contradictions the last settle could not satisfy — the reported 'solve result'.

  This is **irreducible clashes among known-true content** and nothing else: two
  `:monotonic` beliefs that cannot both hold, where the engine has no grounds to
  prefer either.  Both stay believed — defeating one would be the engine deciding
  which of your premises to discard — so this is where that decision is handed back.
  A coexisting pair at `:default` is *not* here: that is a represented dilemma, and
  `contradictions` reports it.  Calling a dilemma a conflict would say the engine
  failed at something it deliberately declines to do.

  **Same entry shape as `contradictions`**, down to `:kind` and both sides'
  justifications — the two readings differ in *why* the pair was left standing, not in
  what a caller needs in order to act on it, and this is the case where there is most
  to do.  Each entry is read off a stored `(contradicts (sentexHandle h) …)` the engine
  placed for the nogood, read at each context it is placed in; the entry's `:sentence`
  composes `contradicts` over the member sentences.

  **The list is ordered by content** — each entry by its sides' sentences and contexts,
  the same rule that orders the sides within one entry — so `(first (conflicts kb))` is
  an answer about the knowledge and not about which pair was typed first.

  **`{:grounds? false}` leaves `:grounds` off**, as it does for `contradictions`."
  ;; each arity reads the clashes itself rather than calling another through the var, so
  ;; a caller that rebinds `conflicts` to count its scans counts one per call
  ([kb] (clashes/with-grounds kb (clashes/ranked (clashes/conflicts-of kb))))
  ([kb opts]
   (let [rs (clashes/ranked (clashes/conflicts-of kb))]
     (if (clash-grounds? opts "conflicts") (clashes/with-grounds kb rs) rs))))

(defn contradictions
  "The coexisting pairs the last settle left standing — **represented dilemmas**, not
  failures.

  Three sources, one shape.  A **rebuttal**: two rules concluding opposite literals with
  neither naming the other's case (the Nixon diamond) is a genuine dilemma — both
  arguments are equally good, both sides stay believed at `:default`, and deciding it
  would be an arbitrary pick dressed up as an inference.  A **definitional clash**:
  disjointness, functionality or asymmetry, each of which convicts by naming a second
  believed sentex, so an equal defeasible pair is a dilemma for the same reason.  And an
  **inherited clash**: a stored claim against a known-true claim that reached its tuple by
  argument preservation, where the second side was never stored at all.  So the engine
  represents it and hands the ranking to the application.

  Each entry is
  `{:nogood #{h ..} :handles [h ..] :priority int :kind kw-or-nil
    :sentence (contradicts ..)
    :sides [{:handle :sentence :context :defeat-class :justifications [...]} ...]
    :grounds [{:handle :sentence :context} ...]}`,
  carrying every member's handle and every side's justifications — the material an
  argument is made from — and, under `:grounds`, the declarations a definitional clash is
  convicted through, in content order, with no `genl` edge: an edge an argument
  declaration minted is named by the sentence it was minted from (docs/nmtms.md, \"The
  clash reports\").  `:kind` names what the members clash on — the constraint a
  definitional clash violated (`:disjoint` / `:functional` / `:asymmetric` /
  `:anti-transitive` / `:anti-symmetric`, and `:irreflexive` in `conflicts`), or
  `:inherited` — and is nil for a rebuttal; `:priority` ranks a
  definitional clash (3–4) above a rebuttal (1–2), and an inherited clash is a rebuttal.

  **`:kind :inherited` carries one key more**, `:inherited`, and it is the one part of a
  clash that is not a stored sentex and so cannot be a side: `{:sentence :context :claim
  handle :via [handle …]}` — the claim nobody wrote, the context it was read in, the
  sentex it was inherited from, and what licensed carrying it there.  Every one of those
  handles is a member too, so the sides carry them with their own justifications.  What
  the pair means and what belief does about it: `docs/inherit.md`.

  **Two members is the common case, not the contract.**  A rebuttal and the pairwise
  constraints name two sides; an `anti_transitive` chain names **three** — the two steps
  and the direct step, which cannot all hold (docs/nmtms.md) — so a reader that
  destructures `:handles` as a pair is reading a coincidence.

  A dilemma is what *rebutting* defeat leaves behind.  **Undercutting** — \"this rule
  does not apply here\" — is written as an `exceptWhen` on the rule, which blocks
  rather than rebuts and produces no pair at all (see docs/exceptions.md).

  **The list is ordered by content** — each entry by its sides' sentences and contexts,
  the same rule that orders the sides within one entry — so `(first (contradictions kb))`
  is an answer about the knowledge and not about which pair was typed first.

  **Each entry is read off a stored `contradicts`.**  The engine places `(contradicts
  (sentexHandle h) …)` for a nogood at the maximal common descendants of its members'
  and grounds' contexts.  The no-context arity reads every such placement at the context
  it is placed in, keeps it where that context believes and sees it, and reports each
  nogood whose verdict there is a tie: what the settle left standing in the KB as a whole,
  which is not what any one context reads.

  **`(contradictions kb context)` reports what stands for one reader.**  It keeps a
  nogood when `context` believes and sees one of its `contradicts` placements, finds a tie
  between its members' classes, and believes and sees every member.  A `contradicts` rests
  on every member, so a member `context` does not believe hides it there: a dilemma one
  of whose members rests on a loser `context` sees is not its dilemma, and neither is
  one whose separation `context` excepts.  A conflict whose members `context`'s excepts
  lower to two defaults is its dilemma, and a reader below two placements that defeated
  different members believes both members and keeps the entry (docs/nmtms.md,
  \"Vantages that disagree\").  A nil or variable context is the KB-wide reading.  The
  read costs the lesser of what `context` sees and the stored `contradicts`.

  **`:vantages` names what each placement context decided**, `{context handle}`, and is
  present only on an entry whose placements defeat different members.  A reader below two
  of those contexts believes every member; a reader below one of them reads that
  context's verdict.

  **`{:grounds? false}` leaves `:grounds` off every entry.**  The grounds are read now, a
  taxonomy walk per definitional clash, and over a corpus with tens of thousands of
  clashes that walk is most of the read.  A caller that lists the
  clashes rather than arguing them asks without it."
  ;; as in `conflicts`, no arity calls another through the var
  ([kb] (clashes/with-grounds kb (clashes/ranked (clashes/contradictions-of kb))))
  ([kb context]
   (clashes/with-grounds kb (clashes/ranked (contradictions-read kb context))))
  ([kb context opts]
   (let [rs (clashes/ranked (contradictions-read kb context))]
     (if (clash-grounds? opts "contradictions") (clashes/with-grounds kb rs) rs))))

;; Classifying a dilemma is an opt-in solve producing *persistent* inert contexts:
;; `(do/label CxDilemma Into)` then `(do/classify Into)` (docs/solving.md).  Do not
;; attach a classification axis to the TMS at settle instead: that makes the KB
;; compute a global forced/supportable/excluded map over every contested node, eagerly
;; and unpersisted, for a question most callers never ask.  Representing dilemmas is
;; separate and unconditional — that is `contradictions`, above.

(defn settle-stats
  "Instrumentation for the `exceptWhen` fixpoint in `settle`.

  `{:iterations n :passes n :histogram {n count}}` — `:iterations` counts the passes of
  the last settle in which the blocked set actually **moved** (0 = nothing blocked,
  1 = one pass sufficed, ≥2 = the fixpoint genuinely iterated), `:passes` the total
  loop passes including the confirming one, and `:histogram` the distribution of
  `:iterations` over every settle since `reset-settle-stats!`.

  What it measures is how much of the fixpoint realistic content actually uses: how
  often a settle iterates past its first productive pass (docs/exceptions.md)."
  [kb]
  @(reasoning/settle-stats kb))

(defn reset-settle-stats!
  "Clear the settle instrumentation, including the histogram."
  [kb]
  (reset! (reasoning/settle-stats kb) {:iterations 0 :passes 0 :histogram {}}) kb)

(defn caches
  "What this process is holding beside the stores — every derived structure the engine
  caches, ranked by entries.  One row apiece:

    {:cache :literal-matches :label \"Literal matches\" :scope :kb
     :entries 3841 :limit 4096 :unit \"literals\"
     :hits 91204 :misses 12038 :hit-rate 0.883 :counters :kb
     :recompute-ns 4210388811 :retired 0 :compared 0 :spurious 0 :evicted 0
     :clearable? true :note \"…\"}

  **`:scope` and `:counters` say what a number is about, separately.**  `:scope` is
  `:kb` for a cache hanging off this KB and `:process` for a static one every KB in the
  JVM shares; `:counters` says the same of `:hits` / `:misses`, and they can differ: the
  closure neighbours count per process over entries no KB holds.  Reading a process
  figure as a per-KB one would attribute another KB's work to this one.

  A cache a derived-state row counts carries that row's tally: `:recompute-ns`, the time
  its misses spent recomputing, and `:retired`, `:compared` and `:spurious`, which count
  while the derived-state instrument runs (docs/caches.md, \"Counting the register\").

  **`:unit` is required too.**  One cache counts literals, another networks, another
  symbols, so the entry columns are not comparable and a page that lines them up without
  saying so compares nothing.

  A nil `:entries` is a cache that cannot be counted from outside — the scope-bound ones,
  bound for the length of one chaining run or one search step — and `:note` says which.
  They are listed rather than omitted, so the answer is complete rather than merely
  finite.  A cache in a namespace this process never loaded is absent: no metric-time
  reasoner, no metric-closure row.

  An `:error` on a row is a cache whose own read threw, reported as one that could not
  answer rather than as one that is empty.  It costs that row and no other: a diagnostic
  is worth most while something is already wrong, so it must not be the next thing to
  break.

  Every read is O(1) — a count off a map the engine already holds, never a walk of the
  KB — so this is safe to poll.  `clear-caches` empties the ones that offer it."
  [kb]
  (caches-impl/rows kb))

(defn clear-caches
  "Drop every cache that offers a clear, and say what went:
  `{:cleared [{:cache :label :entries}…] :entries total}`.

  **Not `!`, and that is the point of it.**  Every entry is derived, the next read
  recomputes it, and no belief moves — so this is a measuring instrument rather than an
  edit: clear, ask the same question again, and watch the miss the second ask no longer
  gets to skip.  It is safe beside a running load for the same reason.

  **Scoped to `kb`.**  Every entry dropped is one of this KB's, and no other KB in the
  process loses an entry, a counter or a belief.

  `opts` is `{:counters? true}`, and it is the one thing here that reaches wider than
  `kb`: a cache whose `:counters` are `:process` counts the mechanism rather than a
  store, so zeroing its hit and miss counters zeroes the rate every KB in this JVM
  reports — a measurement two readers may be in the middle of.  It is off by default,
  and the reply then carries `:counters-reset` naming what was zeroed and what it held.
  The same option zeroes this KB's own tallies, listed under `:tallies-reset`.
  Ask for it when you are about to re-run the question and want the rate read off zero;
  leave it alone when you only want the entries gone.  `caches`' `:counters` column says
  which rows the option is about.

  The structural caches are left alone — the symbol pool, the compiled relation algebras
  — because dropping those costs the sharing they exist for and buys no measurement.
  `caches`' `:clearable?` says which rows this touches, and a `:cleared` entry carrying
  `:error` is one whose clear threw, which costs that cache and no other."
  ([kb] (clear-caches kb nil))
  ([kb opts]
   (check-bound-opts! opts #{:counters?} "clear-caches")
   ;; `:counters?` is a boolean the impl reads as truthy, so `{:counters? \"yes\"}` would
   ;; zero the process counters under a value that only looks like `true` — refused here
   ;; as `:unknown-option` (`opts/bound-domains`)
   (opts/check-values! opts "clear-caches")
   (caches-impl/clear-caches kb opts)))

(defn cache-profile
  "The cache tuning in force, process-wide: `{:scale <multiplier> :overrides {cache-id
  limit}}`.  Every count-bounded cache holds its shipped default limit multiplied by
  `:scale`, unless `:overrides` sets it to an absolute number.  `set-cache-scale` and
  `set-cache-limit` change it; `caches` shows the effective limit each cache enforces."
  []
  (caches-impl/profile))

(defn set-cache-scale
  "Multiply every count-bounded cache's shipped limit by `x`, on a **running** process, and
  return the profile.  `1.0` restores the shipped bounds; below 1 shrinks the caches for a
  small heap, above 1 grows them for a bulk load.  A per-cache floor keeps a small scale
  from taking a cache below the point where it saves nothing.

  Process-wide and not per-KB, as `set-log-level` is: two KBs in one JVM share one set of
  process caches, and every per-KB cache reads the one scale.  `VAELII_CACHE_SCALE` sets the
  value a process starts with; this is the same dial from a REPL.  Refused by name when `x`
  is not a number, or is below zero (`:type :unknown-option`)."
  [x]
  (when-not (and (number? x) (>= (double x) 0.0))
    (throw (ex-info (str "cache scale must be a number 0 or more, not " (pr-str x))
                    {:type :unknown-option :mismatch :bad-value :scale x})))
  (caches-impl/set-scale x))

(defn set-cache-limit
  "Override cache `id`'s bound with `n` regardless of the scale, or clear the override when
  `n` is nil, and return the profile.  `id` is a `:cache` keyword from `caches`, `n` a
  positive whole number.  An override is absolute — the scale does not move it — for a caller who has
  measured one cache and wants a bound the global scale would not give it.  Refused by name
  when `id` is not a keyword, or `n` is neither nil nor a positive whole number
  (`:type :unknown-option`).

  An `id` that names **no currently-registered cache** is *warned*, not refused, and the
  override is recorded anyway.  A refusal would be wrong here: the register fills lazily (a
  cache registers when its namespace loads, and a qualitative calculus may not be loaded
  yet), so a bound set for a cache before its namespace loads is a legitimate request the
  cache picks up on registration.  The warning is what a typo — the far likelier reading —
  surfaces under, since an override for an id nothing ever registers sits inert in the
  overrides forever otherwise.

  An override for a **registered cache no override moves** is refused (`:unknown-option`): a
  nil-bound cache, which has no count to override, and the symbol pool and the
  scoped-closure budget, whose bounds are dynamic vars outside the profile (docs/caches.md).
  The register knows those caches, so no load order makes the override apply later, and
  recording it would report a bound nothing enforces.  Clearing one with nil is accepted and changes nothing."
  [id n]
  (when-not (keyword? id)
    (throw (ex-info (str "cache id must be a keyword from `caches`, not " (pr-str id))
                    {:type :unknown-option :mismatch :bad-value :cache id})))
  (when-not (or (nil? n) (and (integer? n) (pos? n)))
    (throw (ex-info (str "cache limit must be a positive whole number or nil, not " (pr-str n))
                    {:type :unknown-option :mismatch :bad-value :limit n})))
  (when-let [why (and (some? n) (caches-impl/override-problem id))]
    (throw (ex-info (str "cache " (pr-str id) " takes no override — its bound is " why
                         ", so an override would be recorded and enforced nowhere."
                         "  An override moves the caches whose bound `set-cache-scale` scales (docs/caches.md)")
                    {:type :unknown-option :mismatch :bad-value :cache id :limit n})))
  ;; an override (not a clear) for an id no cache has registered: recorded, since a
  ;; not-yet-loaded cache picks it up, but warned since a typo is the likelier reading and would otherwise
  ;; sit inert forever
  (when (and (some? n) (not (caches-impl/registered? id)))
    (trove/log! {:level :warn :id ::cache-limit-unknown-id
                 :msg (str "set-cache-limit overrides " (pr-str id) ", which names no cache"
                           " registered in this process yet — a typo, unless its namespace"
                           " has not loaded; the override is recorded and applies if it does")
                 :data {:cache id :limit n}}))
  (caches-impl/set-limit id n))

(defn install-memory-guard!
  "Attach a listener to the JVM's garbage collectors that moves the cache profile's
  `:pressure` with how full the old generation is: over the high mark it shrinks the
  caches, under the low mark it grows them back.  Returns nil.

  `:kbs` is a thunk answering the live KBs whose per-KB caches the trim reaches.  The
  engine holds no list of open KBs, so a process serving several supplies its own
  list here.  Idempotent: a second call replaces the thunk and attaches no second
  listener.  Nothing attaches the guard at engine load, so a library embedding carries no
  listener it did not ask for.  `!` because it attaches to the process's collectors.
  [docs/caches.md](docs/caches.md)"
  [{:keys [kbs] :as opts}]
  (check-bound-opts! opts #{:kbs} "install-memory-guard!")
  (caches-impl/install-memory-guard! {:kbs kbs})
  nil)

(defn switch-value
  "The value of the build switch spelled `spelling` — a `VAELII_*` environment variable or a
  `vaelii.*` system property — read against its domain now, as `open-kb`'s check reads
  it.  A value outside the domain is refused (`:unknown-option`, `:mismatch :bad-value`),
  and so is a name the build reads no switch under (`:mismatch :unknown-key`).  Either
  refusal names the switch under `:switch`, and under `:property`, the older key, which
  holds the same name for an environment variable as for a system property.

  The switch table is `vaelii.impl.config/switches`, and
  [docs/operations.md](docs/operations.md) tabulates it, so a caller outside the engine
  reads `VAELII_DEV` or `VAELII_PROFILER_PORT` with the engine's parse instead of
  re-parsing the environment."
  [spelling]
  (if-let [row (first (filter #(some #{spelling} (:names %)) config/switches))]
    ((:reader row))
    (throw (ex-info (str (pr-str spelling) " is not a switch this build reads")
                    {:type :unknown-option :mismatch :unknown-key :switch spelling :property spelling
                     :options (vec config/switch-names)}))))

(defn violations
  "The definitional constraints a *derived* conclusion would have broken during the
  last forward-chaining run, and what a bounded pass did not reach.  Each is

    {:violation <kind> :sentence S :context C :rule handle :run n :detail {…}}

  **`:sentence` and `:context` are not on every entry.** An entry about a *term*, a
  *pair*, a *budget*, a whole *network* or one *antecedent literal* names no one dropped
  sentence: all the bounded-work notices below carry neither key, and the three network
  reports and `:post-join-ambiguous` carry a `:context` with `:sentence` nil.  So a
  consumer reads both with `when-let` rather
  than unconditionally. `:message` is under `:detail` on every kind but `:non-confluent`
  and `:aggregate`, which carry it at the top level.

  ## The kinds

  The three tables below are the full list of kinds, and `violation_kinds_test` holds them to
  the code: it scans the sources for every kind the engine can file, and fails on a kind
  with no row here, on a row here naming a kind nothing files, and on a `:detail` column
  that is not the keys the entry builds.  A detail cell naming no key belongs to a kind
  whose entry is a *check's* problem map rather than the filing site's own, so its keys
  are the check's and vary with what it found.

  ### Dropped — the conclusion is not stored

  A rule fired, or the engine minted content on its own behalf, and what came out could
  not be admitted: no sentex, no justification, and `why-not` reduced to `:not-stored`.

  | entry | means | detail |
  |---|---|---|
  | `:arg-type` / `:arg-genl` | an argument fails a declared constraint — `arg`'s type, or `genlArg`'s subtype floor.  A rule's conclusion convicted at its own argument is stored and held instead, as `:inert-argument`; one convicted at a function application's input is dropped here | `:arg` `:expected` `:position` `:message` |
  | `:inter-arg-type` | an `interArg` conditional constraint, or an `interArgs` / `interArgAndRest` homogeneity constraint, whose trigger argument holds and whose target argument does not | `:arg` `:expected` `:position` `:trigger` `:trigger-type` `:trigger-position` `:message` |
  | `:disjoint` | an application whose result type is disjoint from a type its argument position demands, before its constant is minted, so no second sentex stands for the pair | the check's problem map |
  | `:not-stratified` | a derived `genl` / `genlCx` edge would put a cycle through negation in the rule set, or a minted generator would feed one | `:cycle` `:message` |
  | `:not-well-formed` | a minted sentence a special predicate's own structure check refuses | `:problems` `:message` |
  | `:naming` | a minted sentence breaking a naming invariant — the spellings in docs/naming.md | `:message` |
  | `:no-placement` | the join completed and no context sees the rule, every antecedent fact, and the `genl` edges the match climbed | `:rule-context` `:fact-contexts` `:subsumed` `:would-place` `:message` |
  | `:mint-refused` | a conclusion naming a reifiable application with no constant yet, whose mint the assert path refused — a sentence the mint writes about the new constant that `assert` refuses | `:refusal` `:message` |
  | `:post-join-ambiguous` | a post-join antecedent — an aggregate, or a computed literal reading one — answered **two ways**, so a firing taking either would conclude a different fact per arrival order.  Filed once per distinct disagreement, since the literal is re-solved on every firing attempt | `:literal` `:solutions` `:message` |
  | `:not-range-restricted` / `:not-indexable` / `:disjunction-too-wide` / `:not-assertible` / `:exception-not-closed` / `:naf-not-closed` / `:quantifier-not-local` | a rule a **generator** minted that the rule checks refuse — the list both storage entry points read, so a mint owes what an author's rule owes.  `:disjunction-too-wide` is the one a *written* rule rarely reaches: an `or` the assert entry point admits is expanded away, so what is left for a mint to file is a generated rule over the alternative cap (docs/canonicalization.md) | the refusal's own keys, and `:message` |

  An **arbitrable** clash is not dropped: a rule's conclusion, an argument-type mint, a
  decontextualization lift's copy and an equality merge's twin are stored, and the
  settle places the clash, which is what gives the loser a `why-not`.

  ### Reported — nothing was dropped

  | entry | means | detail |
  |---|---|---|
  | `:non-confluent` | two schematic equations disagree about a shared term; the normal form stays deterministic, so nothing is dropped | `:with` `:message` |
  | `:inert-argument` | a stored fact, asserted or concluded by a rule, whose argument fails a declared argument type as `assert` reads it — a value under `arg`, a symbol under the constraint-only reading, a `quotedArg` kind — held in the `:out` forced set, so it is never believed (docs/argtypes.md).  Read off the held facts at each call, not filed: the entry stands while the fact is stored and convicted, and carries no `:run` | the check's problem map |
  | `:inert-rule` | a stored rule, asserted or minted, one of whose variables two argument constraints hold to separated types, so no term fills it: `:detail` is the `:arg-variable` conviction.  The rule is held in the `:out` forced set, so it is never believed and fires nothing (docs/argtypes.md).  Read off the held rules at each call, as `:inert-argument` is | `:variable` `:expected` `:message` |
  | `:forced-conclusion` | a stored firing concluding a forced-monotonic literal, or its denial, from a rule whose antecedents are not all forced-monotonic or that has an `unknown`, `exceptWhen` or `set/defaultRule`: the firing is held void at some reader, so it supports nothing there, and `:not-forced-monotonic` names the rule's antecedent predicates that are not forced-monotonic (docs/nmtms.md).  Read off the stored firings at each call, not filed: the entry stands while the firing is stored and convicted, `:sentence` is the conclusion's stored spelling, and the entry carries no `:run` | `:not-forced-monotonic` `:message` |
  | `:aggregate` | an aggregate prover cannot reduce an extent — values that are not numbers of one dimension, or bounds only partially ordered.  Filed once per distinct error, since a count is recomputed rather than cached | `:message` `:values` |
  | `:qualitative-inconsistency` | the qualitative network visible from a context is unsatisfiable, so no goal naming a node of an unsatisfiable component is answered there | `:calculus` `:message` `:nodes` `:pairs` `:sources` |
  | `:metric-temporal-mixed-dimensions` | the `temporalDistance` facts visible from a context span more than one dimension, so it gets no metric network at all | `:message` `:dimensions` `:units` |
  | `:metric-temporal-inconsistency` | the metric temporal constraints visible from a context cannot all be satisfied | `:message` `:unit` `:nodes` `:pairs` `:cycle` |
  | `:sign-inconsistency` | the sign facts visible from a context leave some quantity with no possible sign at all, so no sign goal is answered there | `:message` `:quantities` |

  A disjointness clash between two memberships each admissible where it was written is
  not filed here.  The settle places it at the contexts that see the pair whole, and
  `contradictions` or `conflicts` answers it; `exposed-clashes` names every
  jointly-visible pair on demand.

  ### Bounded — the pass did not cover everything

  So a cap never reads as full coverage. Two kinds, separate because a reader acts on
  them differently, and each one entry per edge rather than one per trigger.

  | entry | means | detail |
  |---|---|---|
  | `:context-edge-exposure-truncated` | a `genlCx` edge's own **merge**-deriving sweep, over `functional` / `functionalInArg` / `anti_symmetric`, was cut short, so pairs beyond the budget go **unmerged for this edge** | `:context` `:mark` `:budget` `:message` |
  | `:genl-edge-revival-truncated` | a revived `genl` edge's **merge**-deriving sweep over its spec subtree, under a `functional` / `functionalInArg` / `anti_symmetric` mark, was cut short, so facts past the budget that arrived while the edge was OUT go **unmerged** | `:edge` `:context` `:budget` `:message` |

  `:context-edge-exposure-truncated` is the one entry here filed from an assert rather
  than a settle — eagerly, from the `genlCx`-edge assert that triggers
  `special/equate-under-context-edge` — and its residual is narrower than every other
  row's for it.  A merge this row's sweep does not reach is not derived by anything else
  afterward, since nothing re-triggers on a `genlCx` edge that has already landed.
  `:genl-edge-revival-truncated` is filed from a settle, by the sweep it runs for a
  revived `genl` edge (`special/revived-declaration-sweeps`), and no later settle
  re-examines a merge past its cut.

  Why a truncation is one entry per edge rather than per trigger, and what the instance
  budget bounds: docs/taxonomy.md and docs/exceptions.md.

  The ledger **accumulates** — each entry carries the `:run` id of the chaining run
  that filed it, so a bulk load's drops are still here at the end — and is capped at
  the newest 1000.  Every drop is also logged at `:warn` as it happens.  Retracting
  the ingredient of an entry does not withdraw it.  `clear-violations!` empties it.
  The `:forced-conclusion` entries follow the ledger's, in content order, and are read
  off the stored firings (`checks/forced-conclusion-entries`): neither the cap nor
  `clear-violations!` removes one.  The `:inert-argument` and `:inert-rule` entries follow
  those, in content order, read off the held facts and rules
  (`checks/held-argument-entries`), and neither the cap nor `clear-violations!` removes
  one either."
  [kb]
  (-> @(reasoning/violations kb)
      (into (checks/forced-conclusion-entries kb))
      (into (checks/held-argument-entries kb))))

(defn filed-violations
  "The filed ledger alone: the entries `violations` begins with, in its order, without the
  `:forced-conclusion`, `:inert-argument` and `:inert-rule` entries it reads off the stored
  firings and held sentexes.  A deref that reads no record, where `violations` fetches
  every held sentex and convicted firing from the record store."
  [kb]
  @(reasoning/violations kb))

(defn clear-violations!
  "Empty the accumulated dropped-conclusion ledger.  `!` because it destroys the
  diagnostic record — the drops themselves are long final.  The `:forced-conclusion`
  entries `violations` reads off the stored firings stay, since they are stored state
  and not ledger entries."
  [kb]
  (reset! (reasoning/violations kb) []) kb)

(defn exposed-clashes
  "Every disjointness clash the KB currently makes jointly visible: a term holding two
  types some context can see as disjoint, where each membership was admissible where
  it was written.  Entries in `violations`' shape (`{:violation :disjoint :detail
  {:term :held :visible-from :message}}`), computed on demand and **not** filed.

  `settle` files none of these: a pair a reader sees whole is decided there and answered
  by `contradictions` or `conflicts`.  This answers about every pair, decided or not,
  since the question asked is what the KB makes visible.  Reads only; nothing is
  stored and belief does not move."
  [kb]
  (clashes/exposed-clashes kb))

(defn specified-violations
  "The audit result for one binary `(predAllSpecified pred indep)` integrity requirement
  in `context`, always carrying a `:status`: `{:status :audited :violations #{x…}}` —
  every member x of `indep` for which no believed `(pred x y)` carries a
  **determinate** filler y satisfying `pred`'s derived slot contract, an empty set
  where the requirement holds — or `{:status :gap :gap :missing-slot-typing …}` where
  `pred` carries no visible slot typing at the audited position.  Discriminate on
  `:status`, not on key presence: `(:violations gap-result)` is nil, and nil reads as
  a clean audit to `empty?`/`seq` — exactly the silent pass the gap exists to prevent.
  The gap is a declaration-contract diagnostic, reported explicitly rather than
  silently audited unconstrained; it covers the denotation-typing declarations only
  (`arg` / `argAndRest` / `args`, their type-level twins, and a
  `type_relation_predicate` membership) — a slot typed solely by `quotedArg`, the
  mention twin, still reads as untyped here.

  The required filler type is **derived** from `pred`'s argument contract, never restated,
  and read through the argnum chokepoint (`res/arg-constraints-at`): each visible
  `(arg cp n t)`, or `(argAndRest cp m t)` / `(args cp t)` reaching `n` — over every
  constraining predicate `cp`, `pred` plus the super-predicates its `genl` closure
  reaches, the same union the assert-time checker reads — requires membership in `t`,
  each visible `genlArg`, `argAndRestGenl` or `argsGenl` reaching `n` requires being a
  subtype of `t`, a `type_relation_predicate` membership requires the filler to be
  visibly a type at every position, and the constraints compose conjunctively, as the
  assert-time checker composes them.

  `arg-pos` selects the twin.  `:second` is `predAllSpecified`, whose audited filler sits
  at `pred`'s second position; `:first` is `predSpecifiedAll`, whose filler sits first and
  whose quantified instance sits second.  It defaults to `:second`.

  A filler is indeterminate exactly when it is an `indeterminate_term` — a skolem constant,
  or a member of a kind declared with `(genl NewKind indeterminate_term)`.  An *Exists*
  placeholder an author asserted is determinate and a skolemised witness is not, which is
  what makes this the antagonist of `predAllExists` ([predall.md](../docs/predall.md)).

  **Computed on demand and not filed.**  The declaration generates no rule and fires nothing
  on assert, so a KB carrying one is audited when a caller asks and never otherwise.  Cost
  is the contract derivation once per call (two declaration reads per constraining
  predicate, plus one membership read), then one read per member of `indep` plus one read
  **per derived constraint** per candidate filler — the subtype arms walking the `genl`
  closure, not a flat membership probe — so this is a sweep to run at a checkpoint rather
  than per write."
  ([kb pred indep context] (specified-violations kb pred indep context :second))
  ([kb pred indep context arg-pos]
   (predall/specified-violations kb pred indep context arg-pos)))

(defn all-specified-violations
  "Audit every binary `predAllSpecified` and `predSpecifiedAll` declaration visible in
  `context`, and every *Exists* declaration (`exists-violations`, keyed `[functor pred a
  b]`), and return `{[functor pred indep] result…}` — each result carrying a `:status`,
  either `{:status :audited :violations #{…}}` or a `{:status :gap …}` diagnostic
  (`:missing-slot-typing`, or `:legacy-ternary-declaration` for a stored pre-migration
  ternary sentex the bulk import path can carry past the assert-time refusal).  A `:legacy-ternary-declaration` gap is keyed by its whole stale argument
  tuple, `[functor pred a b]`, so it displaces neither the migrated declaration it
  shares a prefix with nor another stale sentex over the same predicate.  Declarations
  that hold are omitted and gaps never are, so an empty map is a clean sweep a gap
  cannot fake.

  This public aggregate and `kb-integrity` both consume the same focused
  per-declaration audit stream; only this wrapper returns its complete aggregate map."
  [kb context]
  (predall/all-specified-violations kb context))

(defn exists-violations
  "The audit result for one *Exists* declaration in `context`, `{:status :audited
  :violations #{x…}}`: for `(predAllExists pred indep dep)` each member x of `indep` with no
  believed `(pred x y)` whose y is a member of `dep`; for `(predExistsAll pred dep indep)`
  each member x of `indep` with no believed `(pred y x)` whose y is a member of `dep`; for
  `(predExistsInstance pred indep fixed)` and `(predInstanceExists pred fixed dep)` the
  fixed term when no such tuple bears to it or from it.  The cell's placeholder for the
  subject is a filler, and so is any member, an `indeterminate_term` included, since the
  declaration asks for existence.  Throws `:bad-args` for any other sentence.

  **Computed on demand and not filed**, like `specified-violations`: the declaration
  derives nothing, and the audit is one read per member of the universal collection plus
  one membership read per candidate filler ([predall.md](../docs/predall.md))."
  [kb declaration context]
  (predall/exists-violations kb declaration context))

(defn functional-at-instant-violations
  "The per-instant functionality clashes of one `(functional_at_instant f)` declaration in
  `context`, as a set of maps `{:function f :subject s :instant t :values #{v…} :kind k}`
  — one per moment `t` at which more than one distinct value of the fluent function `f`
  holds for one subject `s`.  `:kind` is `:merge` when the clashing values are all symbols
  (the pair `functional` would merge into one thing) and `:contradiction` otherwise (two
  numbers or strings `functional` refuses outright).

  Computed on demand and not filed; the candidate moments are the `time_point` members
  `ask` answers in `context` (docs/time.md, \"Functionality at an instant\")."
  [kb f context]
  (fluent/functional-at-instant-violations kb f context))

(defn all-functional-at-instant-violations
  "Audit every `(functional_at_instant f)` declaration visible in `context`, and return
  `{f #{violation…} …}` — declarations that clash nowhere are omitted, so an empty map is
  a clean sweep."
  [kb context]
  (fluent/all-functional-at-instant-violations kb context))

(defn kb-integrity
  "Run the bounded, read-only integrity sweep in `context`.

  `candidate-terms` is a finite set of ground terms (`:bad-args` otherwise).  Answers
  `{:status :audited :candidate-count n}` when no pass finds anything, `:status :gap` with
  the non-empty categories among `:definition-inconsistencies`,
  `:all-specified-violations`, `:type-specified-violations`, `:rigidity-correspondence`,
  `:genl-arg-widening`, `:not-under-thing`, `:implicit-genl`, `:implicit-arity-class`,
  `:orthogonal-over-separation`, `:rule-macro`, `:undeclared-arity`,
  `:uncorresponded-function`, `:stranded-declaration`, `:rule-clash`, `:twin-genls`,
  `:derivable-stated-edge`, `:disjoint-could-be-partition`, `:missing-arg`,
  `:taxonomy-island`, `:rule-clash-review` and `:rule-macro-review`, or `:status
  :truncated` with its `:reason`, the `:pass` it stopped in and the findings kept when a
  bound runs out.  Every answer carries `:work`, the units spent, and `:elapsed-ms`.
  `options` takes `:max-work`, `:max-ms` and `:max-results`, and `:categories`, a set of
  category keys to run.  The seven review-only categories `:twin-genls`,
  `:derivable-stated-edge`, `:disjoint-could-be-partition`, `:missing-arg`,
  `:taxonomy-island`, `:rule-clash-review` and `:rule-macro-review` run only when
  `:categories` names them; a rule-macro or rule-clash finding an `acknowledgedFinding`
  names is reported under its review category with the reason.  `kb-quality`'s
  `:taxonomy`, `:declarations` and `:clashes` count the same checks over the whole KB.
  Stores and files nothing.  See docs/integrity.md."
  ([kb candidate-terms context]
   (integrity/kb-integrity kb candidate-terms context nil))
  ([kb candidate-terms context options]
   (integrity/kb-integrity kb candidate-terms context options)))

(defn chain-stats
  "Chaining-run instrumentation: `{:runs n :last {:derived n :truncated? bool}}`.

  `:last` is the most recent run's result whatever triggered it — a plain `assert`
  chains too but returns only its handle, so `:truncated?` here (plus the :warn log)
  is how a depth- or derivation-capped run becomes visible without calling
  `forward-chain` by hand."
  [kb]
  @(reasoning/chain-stats kb))

(defn chain-report
  "Per forward rule, what forward chaining did with it — how many firings it **placed**,
  how many it **refused** and why, or whether it did nothing at all.  Where `chain-stats`
  is the run's headline counters, this is the per-rule breakdown behind them: the read the
  ontological engineer's *which of my rules actually do anything* wants.

  `O(rules)`, off the rule index and the state a run leaves standing — the refusal ledger
  (re-decided against current belief) and the justification graph — so it needs no
  instrumentation and reflects the KB as it is now, not a snapshot of one run. Each row is
  `{:rule :sentence :believed? :placed :void :refused :refusals :status}`, `:void` the
  firings the forced-monotonic set holds void; see
  `vaelii.impl.chain/rule-firing-report`.  The `:no-placement` and other violations a
  firing files are read separately through `violations`, keyed by the same `:rule` handle."
  [kb]
  (chain/rule-firing-report kb))

(defn last-program
  "The last edge `Program` handed to the solver — the contested assumptions and the
  nogoods among them — or nil if no tie has ever been arbitrated.

  `do/labeling` records it, and `vaelii.impl.asp.label/classify` reads it (docs/asp.md,
  \"Two things keep `classify` from reporting a tie as forced\")."
  [kb]
  @(reasoning/program kb))

(def ^:private solver-vars
  "The shipped edge solvers by name, and the var holding each.  Resolved at runtime, so
  naming the ASP backend here does not put clingo/JNA on every KB's load path."
  '{:stub vaelii.impl.solve/local-solver
    :asp  vaelii.impl.asp.edge/edge-solver})

(defn set-solver
  "Install the solver a labeling (docs/labeling.md) solves a dilemma's program with when
  no ASP backend is reachable, returning `kb`.  A settle hands no nogood to a solver.
  Takes a **name** —

    :stub  (the default) a deterministic local stub: greedy, one contradiction at a
           time, so two overlapping pairs can cost two defeats where one would do
    :asp   the real answer-set backend — globally optimal, order-independent, and what
           `conflicts` / `last-program` / brave-cautious classification are for
           (docs/asp.md).  Degrades on its own: native clingo, else the clasp
           subprocess, else the stub

  — or any `vaelii.impl.types.solve/Solver` value, for an application with a backend of its
  own.  A name is what the public surface needs: the shipped backends are
  `vaelii.impl.*` values, so without this the only way to ask for the real one is to
  reach past the boundary for it."
  [kb solver]
  (reset! (:solver kb)
          (if (keyword? solver)
            (if-let [sym (solver-vars solver)]
              @(requiring-resolve sym)
              (throw (ex-info (str "no such solver: " solver " — want one of "
                                   (str/join ", " (map pr-str (sort (keys solver-vars))))
                                   ", or a vaelii.impl.types.solve/Solver value")
                              {:type :unknown-option :mismatch :bad-value :solver solver
                               :known (vec (sort (keys solver-vars)))})))
            solver))
  kb)

(defn- target-following-meta?
  "Is `sx` a **target-following meta-sentex** — a sentex whose predicate is declared
  `target_following_predicate`?  Such a sentex names another sentex by handle and must not
  outlive it, so a teardown that removes the named target removes it too.

  The mark is read unscoped: a teardown removes stored sentexes, which every reader
  shares."
  [kb sx]
  (let [s (:sentence sx)]
    (and (sequential? s)
         (symbol? (first s))
         (tax/has-prop? (reasoning/taxonomy kb) :target-following (first s)))))

(defn- following-metas-naming
  "The handles of still-stored target-following meta-sentexes that name handle `h` — the
  metas a teardown of `h` must sweep, read by `reads/as-stored-naming-handle`.
  `find-sentexes` narrows a compound on its atoms, and the only atom here is
  `sentexHandle`, so it would fetch every sentex naming any handle."
  [kb h]
  (into []
        (comp (keep #(p/get-sentex (:records kb) %))
              (filter #(target-following-meta? kb %))
              (map :id))
        (reads/as-stored-naming-handle (:index kb) h)))

(defn- retract-following-metas!
  "The cascade that keeps a **target-following meta-sentex** from outliving the sentex it
  names.  After a teardown, retract every marked meta naming a handle that left the
  store, looping to a fixpoint — a retracted meta is itself a sentex another meta may
  name (an endorsement of an endorsement).  Reads the removal sink to learn what left:
  the dependency sweep's removals, the settle's, and this cascade's own — the same record
  `nat-maint/collect-orphans!` reads — so it is complete without every removal path reporting
  to it.

  A no-op unless the KB declares a `target_following_predicate`: the sink is bound only
  then (or when a reifiable function needs it), and an empty `:target-following` set short-circuits.  The
  engine's own meta-sentexes (`except` / `exceptWhen`) do not carry the mark, so their
  orphan-on-retraction behavior (`meta_sentex_test`) is untouched."
  [kb sink]
  (when (and sink (seq (props kb :target-following)))
    (loop [seen #{}]
      (let [fresh (into [] (remove seen) (map :id @sink))]
        (when (seq fresh)
          (let [metas (into #{} (mapcat #(following-metas-naming kb %)) fresh)
                live  (into [] (filter #(p/get-sentex (:records kb) %)) metas)]
            (when (seq live)
              (let [rs (mapv #(retract-storage! kb %) live)]
                (settle-after-teardown! kb (settle/rechain-owed kb @(reasoning/recheck kb))
                                        (distinct (mapcat :seeds rs))
                                        (mapcat :rederive rs))))
            (recur (into seen fresh))))))))

(defn- teardown-sink
  "The removal record `retract!` and `edit!` bind for their duration — every sentex that
  leaves the store while they run, collected at the removal choke point
  (`integrate/*removed-sink*`): the dependency sweep's removals, the settle's, and the
  cascades' own.

  Built only when something reads one: a reified constant (`nat/any-reified-constants?`,
  the orphan sweep), a `target_following_predicate` (the meta cascade), a placed read and
  a refusal waiting on an argument conviction (`special/argument-refusals?`, the settle's
  release of it).  With none of them the sweeps are no-ops, and recording a cascade for
  nothing to read is pure retention, so the presence check answers nil and the choke
  point collects nothing."
  [kb]
  (integrate/removal-sink (or (nat/any-reified-constants? kb)
                              (seq (props kb :target-following))
                              (exc/placed-reads? kb)
                              (special/argument-refusals? kb))))

(defn- finish-teardown!
  "The four sweeps a teardown owes once its settle has run, in the order both write entry points
  run them:

  * the **meta cascade** — a `target_following_predicate` sentex must not outlive the
    sentex it names, and what left the store is what `sink` recorded;
  * the **orphan sweep** — a reified constant no live use references any more, whose
    `natFormula` map would otherwise dangle a raw `nat/` symbol;
  * the **structural-genlCx revival** — a teardown can put a `contextArgSubrelation`
    declaration or a stored R-evidence fact back IN (retracting a monotonic defeater
    above it), and the producer runs on assert only, so an edge never built while the
    declaration was OUT would stay absent with nothing to revive.  Rebuilt against the
    settled belief (docs/context-nat.md), and run only when the KB declares one;
  * the **formula positions** — a rule holding a variable-functor application is held or
    released as the `formula` declarations believed now read its positions, so a removed
    declaration or `genl` edge among `removed`, the facts the teardown removed,
    re-decides the rules on its predicates (`nat-maint/reconcile-formula-positions`).

  The second and third run only beside a `sink`: `teardown-sink` answers nil only when
  `nat/any-reified-constants?` is false, and both run only when it is true, so a KB with
  no reified constant reads that presence check once per teardown and not three times.

  One fn because `retract!` and `edit!` must not drift: a batch that swept a meta the
  single retraction did not — or the reverse — would leave the same knowledge in two
  states depending on how it was taken out."
  [kb sink removed]
  (retract-following-metas! kb sink)
  (when sink
    (nat-maint/collect-orphans! kb sink retract!)
    (nat-maint/reconcile-revivals! kb))
  (nat-maint/reconcile-formula-positions kb removed))

(defn- rolled-back
  "The refusal an atomic batch rethrows once the KB is back the way it was found:
  the original `ex-data` plus `:rolled-back true` and `:in` / `:index` / `:entry` naming
  the batch line that raised it — `check-edit`'s vocabulary, so a caller points at the
  line rather than at the batch either way.  The original hangs off it as the **cause**,
  so the stack that raised it survives.

  Only an `ExceptionInfo` carries `ex-data` to add to.  Anything else is rethrown
  exactly as raised: the rollback ran the same, and wrapping an arbitrary `Throwable` in
  an `ex-info` would hide its class from the handler that knows what to do with it."
  [t [where index entry]]
  (if (instance? clojure.lang.ExceptionInfo t)
    (ex-info (ex-message t)
             (assoc (ex-data t) :rolled-back true :in where :index index :entry entry)
             t)
    t))

(defn retract!
  "Retract premise support for a handle, tear down solely-supported sentexes and
  justifications (keeping anything re-derivable via other witnesses), and reverse
  their taxonomy / rule-index effects. Returns counts.

  An **inert** sentex (`assert-inert`) was never a TMS datum, so the dependency
  sweep cannot find it; it is torn down directly through the removal choke point
  instead.  That is complete on its own — nothing rests on an inert sentex (it
  licenses no justification) and belief cannot move, so no settle is needed; the
  re-check the choke point queues is vacuous and drains at the next settle.

  **A stored premise the TMS has no node for is neither of those**, and is refused
  (`:unrecovered-premise`) — see `retract-storage!`."
  [kb handle]
  (check-writable! kb "retract!")
  ;; A teardown settles more than once — revive, re-derive, settle again — and the orphan
  ;; sweep retracts inside it.  A change feed delivered per settle would report a datum
  ;; that went OUT in the first pass and revived in the second as a removal followed by
  ;; an addition, when the retraction's net effect on it was nothing.  So the whole
  ;; operation is one event (`feed/with-one-event`).
  (feed/with-one-event kb
    ;; the sweeps below are scoped to what this teardown removed, so the removals are
    ;; recorded as they happen — the dependency sweep's, the settle's, and the sweeps' own
    (let [sink (teardown-sink kb)]
      (binding [integrate/*removed-sink* sink
                observe/*write-record*   (settle/write-record kb)]
        (let [handle (the-handle handle "retract!")
              _      (when-let [problem (checks/forcing-retraction-problem kb handle "retract!")]
                       (throw (ex-info (:message problem) (dissoc problem :message))))
              {:keys [datum? seeds rederive] :as result} (retract-storage! kb handle)]
          (when datum?
            (settle-after-teardown! kb (settle/rechain-owed kb @(reasoning/recheck kb)) seeds rederive))
          (finish-teardown! kb sink (:sentences result))
          (dissoc result :datum? :seeds :rederive :sentences))))))

;; ---- the records no premise and no justification supports ----------------------
;; docs/storage.md, "A record no premise and no justification supports".

(defn unsupported
  "The stored records the last `recover` found with no premise mark, no justification and
  no `:inert` mark, as `{:n n :handles [h …]}`, ascending, re-checked against the KB now:
  a handle since premise-marked, concluded, marked `:inert` or retracted is left out.  The
  re-check reads the network and no store.  Such a record stays OUT.  The count can
  include an `assert-inert` record written before `assert-inert` marked its records;
  `mark-inert!` marks one.  `remove-unsupported!` deletes them."
  [kb]
  (let [tms (reasoning/tms kb)
        hs  (filterv #(jtms/unsupported? tms %) (:unsupported @(:unrecovered kb)))]
    {:n (count hs) :handles hs}))

(defn- attested-unsupported
  "The unsupported handles `opts` names for `op`: those among `:handles`, else the
  reported ones in `:contexts`, else every reported one under `:force? true`.  With none
  of the three, refused (`:unsupported-unattested`)."
  [kb op allowed {:keys [handles contexts force?] :as opts}]
  (opts/check! opts allowed op
               (str "An option nothing reads leaves the call unattested, which " op
                    " refuses."))
  (let [unsupported? #(recovery/unsupported-handle? kb %)]
    (cond
      (some? handles)  (into [] (comp (filter unsupported?) (distinct))
                             (sort (map #(the-handle % op) handles)))
      (some? contexts) (let [cs (set contexts)]
                         (filterv #(contains? cs (:context (p/get-sentex (:records kb) %)))
                                  (:handles (unsupported kb))))
      (true? force?)   (:handles (unsupported kb))
      :else
      (let [msg (str op " deletes or marks stored records, so it takes the caller's"
                     " evidence: {:handles hs} naming the records a failed write left, or"
                     " {:force? true} to act on every record (unsupported kb) reports")]
        (throw (ex-info msg {:type :unsupported-unattested :operation op
                             :options (vec (sort allowed))}))))))

(defn remove-unsupported!
  "Delete the unsupported records `opts` names (`unsupported`), with their postings, each
  through `retract!`, and return `{:unsupported-removed n :handles [h …]}`.

  `{:handles hs}` removes the unsupported records among `hs`: the handles the caller's own
  record of its writes marks failed.  A handle that is not an unsupported record is left
  as it is.  `{:force? true}` removes every record `unsupported` reports, which includes
  an unmarked `assert-inert` record written before `assert-inert` marked its records.
  With neither, refused (`:unsupported-unattested`): opening a KB never deletes a record,
  and this call deletes only what its caller attests.  docs/storage.md."
  [kb opts]
  (check-writable! kb "remove-unsupported!")
  (let [hs (attested-unsupported kb "remove-unsupported!" #{:handles :force?} opts)]
    (run! #(retract! kb %) hs)
    (swap! (:unrecovered kb) update :unsupported #(into [] (remove (set hs)) %))
    {:unsupported-removed (count hs) :handles hs}))

(defn mark-inert!
  "Write `:inert true` into the provenance of the unsupported records `opts` names, and
  return `{:marked n :handles [h …]}`.  `{:handles hs}` marks the unsupported records
  among `hs`, `{:contexts cs}` those `unsupported` reports in a context of `cs`.  With
  neither, refused (`:unsupported-unattested`).  For an `assert-inert` record written
  before `assert-inert` marked its records: a marked record is no longer counted by
  `unsupported`.  docs/storage.md."
  [kb opts]
  (check-writable! kb "mark-inert!")
  (let [hs  (attested-unsupported kb "mark-inert!" #{:handles :contexts} opts)
        rec (:records kb)]
    (doseq [h hs]
      (p/put-provenance rec h (assoc (p/get-provenance rec h) :inert true)))
    (swap! (:unrecovered kb) update :unsupported #(into [] (remove (set hs)) %))
    {:marked (count hs) :handles hs}))

(def edit-opt-keys
  "Every key `edit!` and `edit-with-consequences!` read for the batch as a whole: the
  caller's bound on the adds' chaining (`chain/call-with-stop`).  An add's own opts are
  `assert`'s."
  #{:max-ms :stop? :progress-every-ms})

(defn- apply-edit!
  "`edit!`'s body, which both its arities call.  The two-argument arity calling the
  `edit!` var would be a second write inside the first, and a nested write is no unit a
  shutdown may stop (`dur/as-unit`)."
  [kb batch]
  (check-writable! kb "edit!")
  (check-edit-batch! batch)
  (let [{:keys [add remove]} batch]
    ;; The whole batch is held to `check-edit`'s answer before anything is applied, so
    ;; the dry run predicts the entry point and a refusal never leaves a half-applied batch:
    ;; an entry's shape (thrown here, reported there, one fn both read), then every
    ;; `:remove` handle — `:bad-handle` for a non-handle, `:unknown-handle` for an
    ;; integer naming nothing stored.
    (doseq [entry add]
      (check-shape! (add-entry-shape-problem entry)))
    (doseq [h remove]
      (when-some [h (the-handle h "edit")]
        (when (nil? (p/get-sentex (:records kb) h))
          (throw (ex-info (str "no sentex is stored under handle " h)
                          {:type :unknown-handle :handle h})))))
    ;; one event for the batch, for `retract!`'s reason: the teardown settles twice and
    ;; a feed reports what the batch changed, not what it did on the way
    (feed/with-one-event kb
      ;; and one removal record for the batch, for `retract!`'s reason: the orphan sweep
      ;; asks about the constants this batch stopped referencing, and nothing else — and
      ;; runs only under the same presence check, so a KB that reifies nothing records
      ;; nothing.
      ;;
      ;; Read **before** the adds, and a batch may declare the KB's first reifiable
      ;; function among them: the presence check is then false here and true at the
      ;; sweep, which leaves a nil sink and sends it down the whole-KB arm.  That is the stricter
      ;; question and the right one — a batch that has just made reification possible has
      ;; no region-scoped claim to make — and it costs the batch that does it one sweep.
      (let [sink (teardown-sink kb)]
        (binding [integrate/*removed-sink* sink
                  observe/*write-record*   (settle/write-record kb)]
          (let [audit    (atom {})
                mark     (volatile! nil)
                baseline (batch-baseline kb)
                ;; where the batch is, for the refusal to name once it has been undone
                at       (volatile! nil)
                ;; **The refusable phase**, and the whole of it: the adds, which are what
                ;; an engine check refuses, and then every removal's refusal asked while
                ;; nothing has been removed.  A throw anywhere in here is put back at the
                ;; handles it wrote (`rollback-batch!`) and rethrown saying so.
                added
                (try
                  (binding [entry/*premise-audit* audit
                            entry/*write-mark*    mark
                            viol/*batch-entries*  (:filed baseline)
                            *defer-settle?* true
                            chain/*rollback-scope* true]
                    ;; a shutdown may stop this phase, which the catch takes back whole
                    (dur/as-unit
                     (fn []
                       (let [added (into [] (map-indexed
                                             (fn [i entry]
                                               (vreset! at [:add i entry])
                                               (let [[sentence context opts] entry]
                                                 (assert kb sentence context (or opts {})))))
                                         add)]
                         (doseq [[i h] (map-indexed vector remove)]
                           (vreset! at [:remove i h])
                           (when-some [h (the-handle h "edit")]
                             (when-let [problem (teardown-refusal kb h "edit!")]
                               (throw (ex-info (:message problem) (dissoc problem :message))))))
                         added))))
                  (catch Throwable t
                    (rollback-batch! kb (assoc baseline :audit audit :suspended nil
                                               :mark mark))
                    (throw (rolled-back t @at))))
                ;; **The committed phase.**  Nothing here refuses: the removals were
                ;; cleared above, and what a settle or a teardown sweep raises past this
                ;; point is a fault rather than a refusal — there is no undo for a swept
                ;; record, so the batch does not pretend to one.  A shutdown's stop request
                ;; is off here (`dur/as-unit` covers the phase above only), so a shutdown
                ;; waits for this phase.
                ;; the caller's bound ends here: nothing past this point is undone
                removed
                (binding [*defer-settle?* true]
                  (chain/call-unbounded
                   #(reduce (fn [acc h]
                              (let [r (retract-storage! kb (the-handle h "edit"))]
                                (-> acc
                                    (update :sentences into (:sentences r))
                                    (update :removed-sentexes   + (:removed-sentexes r))
                                    (update :removed-justifications + (:removed-justifications r))
                                    (update :seeds into (:seeds r))
                                    (update :rederive into (:rederive r)))))
                            {:removed-sentexes 0 :removed-justifications 0 :seeds []
                             :rederive [] :sentences []}
                            remove)))]
            (chain/call-unbounded
             (fn []
               (settle-after-teardown! kb (settle/rechain-owed kb @(reasoning/recheck kb))
                                       (distinct (:seeds removed)) (:rederive removed))
               (finish-teardown! kb sink (:sentences removed))))
            {:added added :removed (dissoc removed :seeds :rederive :sentences)}))))))

(defn edit!
  "Apply a batch of assertions and retractions in **one settle**.

    `add`    — a seq of `[sentence context]` (or `[sentence context opts]`), asserted
               in order **first**;
    `remove` — a seq of handles, retracted **after**.

  Adds land before removes, and the whole batch settles once at the end, so a datum
  the removed premises solely-supported but an added one re-derives keeps a witness
  through the dependency-directed sweep — belief that survives the edit is never swept
  and rebuilt, and never flickers OUT and back.  The final state equals running the
  asserts and retracts singly; the win is skipping the intermediate tear-down and the
  N per-op settles.

  **All-or-nothing.**  A refusal `check-edit` cannot see — a naming policy, a `disjoint`
  clash, an `argIsa` violation, a `functional` slot already filled, a stratification
  refusal — is raised by the engine on the entry that trips it, and by then the entries
  before it have landed.  So the batch is rolled back at the handles it wrote: every add
  retracted (which collects what it derived, by the ordinary dependency-directed sweep),
  every premise mark undone, every strength it raised put back, the diagnostic ledgers
  and the refusal record restored.  Belief and the handle set are then exactly what
  they were before the call.  **The handle counter is the one thing that moves** —
  handles are minted in assertion order and never reissued — which is what a `preview`
  already leaves behind, and nothing reads a handle as a fact about the KB.

  All-or-nothing is against a refusal, not against a reader: a reader on another thread
  sees each add and each removal as it lands.  The batch's effect as one change is the
  one `watch` event it produces, or `edit-with-consequences`.

  The refusal is rethrown with its own `ex-data` plus `:rolled-back true` and
  `:in` / `:index` / `:entry` naming the batch line that raised it, the original hung off
  it as the cause.  A throw that is not an `ex-info` is rethrown exactly as raised; the
  rollback ran the same.

  **A removal is the half no rollback can put back**, so every `:remove` is asked for its
  refusal (`teardown-refusal` — the unrecovered-premise and unrecovered-KB cases
  `retract!` throws) while nothing has been removed yet, after the adds and before the
  first teardown.  Past that point the batch is committed and the removals, the settle
  and the teardown sweeps run to the end.

  **A rolled-back batch changes nothing a listener is told about.**  The rollback runs
  with the change feed off, so it accumulates no region and the one event this entry point
  delivers has nothing to say (docs/feed.md).

  Returns `{:added <one entry per add, `assert`-shaped> :removed {:removed-sentexes n
  :removed-justifications n}}`.  To also learn what the batch turned out to *mean* — the
  belief it added and took away — use `edit-with-consequences`, which is this plus the
  diff.

  What `check-edit` reports for the batch's own structure, this entry point refuses **before
  applying anything**: a malformed `:add` entry is `:shape` (never applied with the
  junk dropped), and a `:remove` handle naming nothing stored is `:unknown-handle` —
  where `retract!` of one is an ordinary zero-count answer, a *batch* naming one is a
  half-applied write waiting to happen, so the whole batch is refused while nothing
  has landed.  (A nil `:remove` entry stays nothing-to-remove, matching `handle-of` of
  an absent sentence.)

  `opts` takes `edit-opt-keys`.  `:max-ms` and `:stop?` bound the adds' chaining: either
  one ending it, before the first removal, refuses the batch (`:interrupted`) and rolls it
  back as a refusal is; past that point the batch runs to its end (docs/inference.md,
  *Stopping a run*).

  **An unrecovered KB refuses the whole batch** (`:unrecovered-kb`), before anything is
  applied.  This entry point's headline guarantee is a JTMS claim — belief that survives the
  edit is never swept and rebuilt — and over an empty network there is no belief for it
  to be about; what is left is \"assert these unchecked, delete those unswept\"."
  ;; `batch` is destructured in the body rather than in the parameter vector, for the
  ;; reason `check-edit` states: the published `:arglists` is what a generated client
  ;; reads to name the argument, and a `{:keys [...]}` there names nothing. Its three
  ;; siblings (`check-edit`, `preview`, `edit-with-consequences`) already take it
  ;; positionally; this is the one that did not.
  ([kb batch] (apply-edit! kb batch))
  ([kb batch opts]
   (check-bound-opts! opts edit-opt-keys "edit!")
   (opts/check-values! opts "edit!")
   (chain/call-with-stop opts #(apply-edit! kb batch))))

(defn in?
  "Is the sentex handle believed as the context it is stored in reads it: JTMS IN, and
  not hidden there by a placed `defeat` in force there or by resting only on a handle one
  hides (docs/nmtms.md, \"A read with no reader\")?  Visibility `except`s are not applied.

  When this answers true but a contextual read cannot see the sentex, call
  `belief-status` to inspect the exception condition and the assertion-context
  inheritance condition."
  [kb handle]
  (exc/believed-own? kb (the-handle handle "in?")))

(defn believed?
  "Is `handle` JTMS IN and not withdrawn from `context` — hidden by the `(except ...)`
  cascade visible from it, the target of a placed `defeat` in force there, or resting
  only on such a handle (docs/nmtms.md, \"A defeat is scoped to its vantage\")?

  This is contextual belief force only.  It deliberately does not require `context`
  to inherit the sentex's assertion context; `belief-status` reports that final
  visibility condition separately.  nil and unknown handles answer false; a non-handle is
  refused with `:bad-handle`, exactly as `in?`."
  [kb handle context]
  (let [h (the-handle handle "believed?")]
    (boolean (and (jtms/in? (reasoning/tms kb) h)
                  (not (exc/excepted? kb h context))))))

(defn belief-status
  "Explain `handle`'s belief and visibility from `context` as a deterministic map.

  Separates storage, raw JTMS IN, context-visible exception force, withdrawal from
  `context`, assertion-context inheritance, and the two terminal answers `:believed?` /
  `:visible?`.  `:exceptions` is ordered by assertion context and content; nested
  meta-exceptions are under `:excepted-by`.  `:withdrawn?` is true when `context` reads
  the handle as withdrawn for any reason: an except, a placed defeat `context` sees, or
  resting only on a withdrawn handle; `why-not` names the defeat.
  nil and unknown handles report absent storage and raw belief; a dangling exception
  may still appear in `:exceptions` / `:excepted?`. Malformed handles are refused with
  `:bad-handle`."
  [kb handle context]
  (let [h       (the-handle handle "belief-status")
        stored  (when-some [h h] (p/get-sentex (:records kb) h))
        raw-in? (boolean (jtms/in? (reasoning/tms kb) h))
        {:keys [exceptions excepted?]} (exc/exception-status kb h context)
        ;; A directly excepted handle is already answered by the forest above, and a
        ;; scoped defeat reads the scoped supporter entries alone.  Resting only on a withdrawn
        ;; handle is possible for a non-premise only — a premise keeps its label in the
        ;; region fixpoint — so only that case asks the full per-reader withdrawal, which
        ;; walks every except the reader sees.
        withdrawn? (boolean
                    (and (some? h)
                         (or excepted?
                             (boolean (when-let [hid (exc/belief-hidden-fn kb context)] (hid h)))
                             (and (not (jtms/premise? (reasoning/tms kb) h))
                                  (exc/excepted? kb h context)))))
        believed? (boolean (and raw-in? (not excepted?) (not withdrawn?)))
        assertion-context (:context stored)
        path (when stored
               (some->> (tax/reach-support (reasoning/taxonomy kb) :genlCx
                                           context assertion-context context)
                        (mapv (fn [[supporter-h supporter-context]]
                                {:handle supporter-h :context supporter-context}))))]
    {:handle h
     :view-context context
     :stored? (boolean stored)
     :in? raw-in?
     :assertion-context assertion-context
     :exceptions exceptions
     :excepted? excepted?
     :withdrawn? withdrawn?
     :inherited-path path
     :believed? believed?
     :visible? (boolean (and believed? (some? path)))}))

(defn believed
  "The subset of `handles` `in?` answers true for, as a set — `in?` asked of many
  handles at once.  What the batch form saves is the **call**, which for a
  remote client (`vaelii.host.serve`) is a whole round-trip.  A page listing n rows
  asks once instead of n times.

  Handle order does not survive (a set), because belief is a property of each handle
  and nothing here ranks them; an unknown or torn-down handle is simply absent."
  [kb handles]
  (let [tms (reasoning/tms kb)
        hid (exc/own-hidden-fn kb)]
    (into #{} (filter #(and (jtms/in? tms %) (not (and hid (hid %))))) handles)))

;; ---- introspection (used by the web browser) ----------------------------

(defn sentex
  "The sentex for a handle as a **map**, or nil.  Same shape contract as `sentexes-matching`'s
  elements: `:id` (the handle), `:sentence`, `:context`, and for a rule
  `:antecedent` / `:consequent` / `:engines` / `:defeasible` / `:effect`.  Key into it; the
  concrete `vaelii.impl.types.sentex/LiteralSentex` / `RuleSentex` record class is internal and not
  part of the contract.  nil (`handle-of` of an absent sentence) answers nil; a
  non-handle (a vector of handles included) is refused (`:bad-handle`)."
  [kb handle]
  (when-some [h (the-handle handle "sentex")]
    (p/get-sentex (:records kb) h)))

(defn canonical-sentex
  "The canonical sentex for `sentence` in `context`, **without storing it** — the un-stored
  counterpart of `sentex`.  It is built through the store's own constructor, so a symmetric
  predicate's arguments are sorted against this KB's taxonomy, comparisons are folded, and
  variables are renamed to canonical form: the exact form `assert` would key on.  Same map
  shape and contract as `sentex` (`:sentence` / `:context`; key into it, the
  record class is internal), but with no `:id`, since nothing was written.

  For turning a sentence into its content identity — a stable key or content-address that
  is a function of the assertion, not of whether or where it landed — independent of a
  handle: `(canonical-sentex kb S C)` digests to the same value on every KB that shares the
  taxonomy, whereas `sentex` needs the sentence to already be stored.

  A ground reifiable NAT resolves to its stored constant, never minting, so the result
  agrees with `handle-of`.  A NAT this KB has not minted stays a compound (docs/nat.md,
  Read path)."
  [kb sentence context]
  (res/kb-sentex kb (or (nat-read/resolve-for-read kb sentence context) sentence) context))

(defn justification
  "The justification for an id, or nil — nil in, nil out; a non-id is refused
  (`:bad-handle`).

  Read from the **record store**, not the network: a justification is a record, and
  the network keeps only the part belief is computed from (`jtms/graph-just` — the
  firing's variable bindings are not among it)."
  [kb jid]
  (when-some [j (the-handle jid "justification")]
    (p/get-justification (:records kb) j)))

(defn premise?
  "Is the sentex at `handle` a **premise** — asserted in its own right rather than
  derived?  A premise rests on nothing, so no justification names it as a conclusion
  and retracting its supports cannot take it OUT; a derived sentex is the other case,
  and `supporting-justifications` is what shows why.  False for a handle the TMS has
  no node for."
  [kb handle] (jtms/premise? (reasoning/tms kb) (the-handle handle "premise?")))

(defn defeat-class
  "The current defeat-class of a believed handle (:monotonic / :default), or nil when
  it is OUT — the effective strength of the belief after settling.  nil for a nil
  handle too; a non-handle is refused (`:bad-handle`)."
  [kb handle]
  (when-some [h (the-handle handle "defeat-class")]
    (jtms/defeat-class (reasoning/tms kb) h)))

(defn- in-content-order
  "`justifications` ordered by `kb/justification-content-key` through `nm/sort-by-content-key`,
  which builds that key **once per justification** and short-circuits below two.

  Both properties pay for themselves here.  Each key build is a `get-sentex` per antecedent
  plus the structural key it assembles, and **the TMS lists every justification a rule
  licenses under the rule's node** (`jtms/rests-on`), so `dependent-justifications` on a
  rule lists its entire firing history: at 100k firings the decorated sort pays 100k key builds against
  the ~3.3M a per-comparison key fn would, and the store lookups behind them fall by the
  same factor.  And a derived fact usually rests on **one** justification, so the whole
  content key is pure overhead on every hop of a proof walk (`why`, w10 retrieval,
  `web/swept-by`) that only ever wanted the one — which the below-two guard skips."
  [kb justifications]
  (nm/sort-by-content-key (kb/justification-content-key kb) justifications))

(defn supporting-justifications
  "Justifications that conclude `handle` (its supporting justifications), in
  **content** order — the informant's own sentence, then the antecedent sentences
  (`kb/justification-content-key`).  `jtms/supports` is a set of allocation-ordered
  ids, so an unsorted answer would say which derivation happened to land first;
  `preview`'s named reason, `why`'s `:support` and a clash report's `:justifications`
  all read through here, and each is a surface the same knowledge must answer
  identically on whatever order it arrived in.  Empty for a nil handle; a non-handle
  is refused (`:bad-handle`)."
  [kb handle]
  (if-some [h (the-handle handle "supporting-justifications")]
    (in-content-order kb (keep #(justification kb %) (jtms/supports (reasoning/tms kb) h)))
    ()))

(defn dependent-justifications
  "Justifications that use `handle` as an antecedent — what rests on it, which is what
  an impact analysis before a `retract!` asks for.  In **content** order, by the key
  `supporting-justifications` reads through: `jtms/dependents` is the same
  allocation-ordered id set as `jtms/supports`, so two assertion orders of one KB would
  otherwise list the same dependents in opposite orders.  Empty for a nil handle; a
  non-handle is refused (`:bad-handle`).

  A rule handle's dependents are every firing it licensed, so this is the call the
  content key is built once per element for (`in-content-order`)."
  [kb handle]
  (if-some [h (the-handle handle "dependent-justifications")]
    (in-content-order kb (keep #(justification kb %) (jtms/dependents (reasoning/tms kb) h)))
    ()))

(defn justification-verdicts
  "The verdict `context` reads on each justification of `handle`, as `{justification-id
  reason}`: `:supports` where every handle it rests on is believed there, else
  `:antecedent-out`, unless the network blocks it (`:blocked`, its rule's `exceptWhen`
  holds) or holds it void (`:void`), `context`'s forced-monotonic reading holds it void
  (`:void`), a guard defeat in force at `context` covers it (`:guard`, docs/naf.md), or
  it is a `nogood` justification of a placement `context` exempts (`:exempt`).

  Belief here is `why`'s reading, with the excepts not applied: a handle IN and named by
  no defeat in force at `context` is believed there exactly when it is a premise or one
  of its justifications reads `:supports`.  `why` puts the verdict at each node's context
  on its `:support` entries, and `why-not` on its `:support`.
  Empty for a nil handle; a non-handle is refused (`:bad-handle`)."
  [kb handle context]
  (if-some [h (the-handle handle "justification-verdicts")]
    (exc/justification-verdicts kb h context)
    {}))

(defn blocked-justifications
  "The ids of the justifications the network currently holds **blocked**: a block their
  rule carries holds (a closed extent, a withdrawn `different`), so the JTMS holds
  them invalid and they confer nothing — even with every antecedent IN
  (docs/exceptions.md).

  A *different* condition from an antecedent being OUT, and the one no per-handle read
  reports.  A blocked justification's antecedents can all be believed, so a reader
  judging support from belief alone calls it supporting when it supports nothing; that
  reader is usually rendering a proof tree, which is why this answers with the whole set
  rather than taking one id — one read per page instead of one per justification, and the
  same answer whether the KB is in this process or behind the daemon.

  The set is replaced whole by each settle (`jtms/set-blocked`), so it is the state as of
  the last one, and it is empty on a KB whose rules carry no exceptions."
  [kb]
  (jtms/blocked (reasoning/tms kb)))

;; ---- describe: what the KB holds about one term ---------------------------
;; `genls`, `props`, `inverse-of`, the extent counts and the argument declarations each
;; answer one question about a term, and a reader who has just arrived at a term wants
;; all of them.  Asking one at a time is a dozen calls plus an assembly the caller has to
;; get right — which types bind this predicate's arguments, which predicates admit this
;; type — so the assembly is here, keyed by the term's own `term-role`, and the browser's
;; term page renders what this returns rather than computing a second one (docs/web.md).
;;
;; **Every list is bounded and says so.**  On an imported ontology `thing` has 110,128
;; subtypes and one collection is disjoint from 79,638 types, so a reader that renders
;; what it is handed has to be handed a truncated list *and* the size of the whole answer.
;; Two envelopes carry that: `{:terms :total :exact? :sorted?}` for a list of terms and
;; `{:rows :total :exact? :sorted?}` for a list of maps.  `:total` is the size of the
;; whole answer, `:exact?` says whether that size is a count or a bound, and `:sorted?`
;; says whether the truncated list is in name order or in the closure's own — fifty
;; alphabetically-first being a different claim from fifty of them.

(def describe-opt-keys
  "Every key `describe` reads, and the key set a key off it is refused against
  (`:unknown-option`): `:limit`, how many entries one of its bounded lists carries and
  how many supertypes its predicates-for-type walk probes."
  #{:limit})

(def default-describe-limit
  "How many entries one of `describe`'s bounded lists carries when the caller names no
  `:limit`.  The browser's term page lists this many per line, so the default is the
  page's own number and the page shows exactly what `describe` answered."
  50)

(def ^:private describe-sortable
  "How many terms a bounded list realizes in order to **sort** them.  Name order is worth
  reading and adds no work at the size a hand-written schema has; ordering 110,000
  subtypes to show fifty of them is not, so past this the list is in the closure's own
  order and the answer says `:sorted? false` rather than implying an order it does not
  have."
  1000)

(def ^:private describe-scan
  "How many sentexes the per-predicate mention count walks off the inverted term index
  before it stops and reports `:exact? false`.  The count *is* the read — there is no
  O(1) form of it — so the bound is a scan limit, and the result reports whether the walk
  reached it."
  4000)

(defn- bounded-terms
  "A term set as one of `describe`'s bounded lists.  The total is exact — the closure
  holds the set, so counting it is free — and only the sort and the list length are bounded."
  [ts limit]
  (let [total  (count ts)
        sorted (<= total describe-sortable)]
    {:terms   (into [] (take limit) (cond->> ts sorted nm/by-print-key))
     :total   total
     :exact?  true
     :sorted? sorted}))

(defn- bounded-rows
  "A row list as the other bounded shape: content-ordered by `keyfn`, truncated at
  `limit`, `:exact?` saying whether `:total` counted everything or stopped at a scan."
  [rows keyfn limit exact?]
  (let [ordered (nm/sort-by-content-key keyfn rows)]
    {:rows    (into [] (take limit) ordered)
     :total   (count ordered)
     :exact?  exact?
     :sorted? true}))

(defn- visible-matches
  "Believed sentexes matching `pattern` **visible from** `context`.  A declaration is
  inherited down the `genlCx` ancestor set and `sentexes-matching` answers one context at a time,
  so a scoped read is that reader's ancestor set walked; an unscoped one passes straight
  through.  The ancestor set is walked in name order, so the answer does not depend on which
  context the closure happened to enumerate first."
  [kb pattern context]
  (if (scoped-read? context)
    (mapcat #(sentexes-matching kb pattern %) (nm/by-print-key (context-up kb context)))
    (sentexes-matching kb pattern context)))

(defn- visible-here?
  "Is a stored sentex visible from `context` — the pattern-free half of `visible-matches`,
  for a read that came off an extent root rather than off a goal."
  [kb sx context]
  (or (not (scoped-read? context)) (sees? kb context (:context sx))))

(defn- comments-on
  "The `(comment term \"…\")` strings visible from `context`, in content order — the KB's
  documentation of the term, stated in the KB's own representation."
  [kb term context]
  (->> (visible-matches kb (list 'comment term '?text) context)
       (keep #(nth (:sentence %) 2 nil))
       distinct
       nm/by-print-key
       vec))

(def ^:private declaration-tails
  "The argument tail each argument-constraint kind takes after the predicate it is about.
  A table rather than a chain, because the kinds differ in *arity* as well as in functor —
  `interArg` names two positions and two types (docs/argtypes.md)."
  '{arg       (?n ?type)
    genlArg   (?n ?type)
    quotedArg (?n ?type)
    interArg  (?n ?type ?m ?utype)
    interArgEqual (?n ?value ?m ?utype)
    argArg    (?n ?m)})

(defn- declarations-on
  "One predicate's argument declarations visible from `context`, each as
  `{:kind :sentence :context}`, content-ordered.  Read from the asking context's ancestor set
  rather than from the whole KB: which types bind a predicate's arguments is a policy of
  the context that declares them, so two theories over one vocabulary may differ and both
  be right (docs/argtypes.md)."
  [kb pred context]
  (->> (for [[kind tail] declaration-tails
             sx          (visible-matches kb (list* kind pred tail) context)]
         {:kind (keyword kind) :sentence (:sentence sx) :context (:context sx)})
       distinct
       (nm/sort-by-content-key (juxt :sentence :context))
       vec))

(def ^:private describe-props
  "The algebraic metadata `describe` reports of a predicate under `:props`.  The four
  *grants* — closed extent, abducible, modal, decontextualized — are reported as their
  own booleans instead: each is a permission a context gives rather than a property of
  the relation, and reading one out of a set of property names loses that."
  [:transitive :symmetric :asymmetric :reflexive :functional])

(defn- granted?
  "Is a one-place grant — `(modal_predicate P)` and anything shaped like it — visible from
  `context`?  A grant is a stored sentex rather than a cached property, so it is read
  where it is stated and follows retraction like any other (docs/belief.md)."
  [kb marker term context]
  (boolean (seq (visible-matches kb (list marker term) context))))

(defn- disjoint-partners
  "The **maximally-general** types `term` is separated from: every type a visible
  declaration puts it apart from, before the separation is pushed down `genl`.

  `tax/separating-partners` is the enumeration, which is the same frame `disjoint?` is
  the membership test of, so the two cannot disagree — and it covers all three ways a
  separation is declared, `(disjoint a b)`, a shared `disjoint_metatype`, and standing
  beside a sibling under a `(sibling_disjoint C)` parent.  Belief and context scoping are
  the frame's.

  **Read off the index rather than by probing the store.**  Asking for the stored
  `(disjoint ?y x)` and `(disjoint x ?y)` sentexes of each of the term's supertypes is
  two pattern reads per supertype — 4.3 ms for `dog`, whose up-closure is eight, against
  0.014 ms here, and it is the term page's single largest cost.  It also missed the
  sibling arm, which stores no pair to find.

  Filtered to the nodes of the genl hierarchy, which is what keeps this a subset of the
  closure `disjoint-line` builds out of it: `specs` is reflexive, so a partner appears in
  its own closure exactly when the same filter admits it there."
  [kb context term]
  (let [known (types kb)]
    ;; `by-print-key`, never bare `sort`: a type node need not be a symbol.  A NAT —
    ;; a function term standing for a collection an imported ontology has no atomic
    ;; name for — is a list, and `compare` throws on one rather than ordering it.
    (nm/by-print-key
     (into #{} (filter known)
           (tax/separating-partners (reasoning/taxonomy kb) term context)))))

(defn- disjoint-line
  "The types disjoint from a term, as the spec closures of the `partners`
  `disjoint-partners` read — every type the separation reaches, not only the types it was
  declared between."
  [kb context partners limit]
  (let [known    (types kb)
        ;; the sum of the partners' closure sizes over-counts their union (an overlap
        ;; twice), which is exactly what makes it a sound bound on it, and it decides
        ;; whether building the union is affordable at all
        bound    (reduce + 0 (map #(count (specs kb % context)) partners))
        walk     (comp (mapcat #(specs kb % context)) (filter known) (distinct))]
    (if (<= bound describe-sortable)
      (let [all (into [] walk partners)]
        {:terms   (into [] (take limit) (nm/by-print-key all))
         :total   (count all)
         :exact?  true
         :sorted? true})
      ;; one past the limit, in partner-name order: enough to know whether there is
      ;; more, and O(limit) rather than O(union) because the closures are in memory
      (let [head (into [] (comp walk (take (inc limit))) partners)]
        (if (<= (count head) limit)
          {:terms (nm/by-print-key head) :total (count head) :exact? true :sorted? true}
          {:terms   (into [] (take limit) head)
           :total   bound
           :exact?  false
           :sorted? false})))))

(defn- predicates-for-type
  "The predicates whose argument declarations admit `t`: every believed `(arg P n U)` or
  `(genlArg P n U)` visible from `context` whose declared type `U` is a supertype of `t`.

  Read off the declaration's own **argument root** — position 3 is where the declared
  type sits — so the cost is the number of declarations naming one of `t`'s supertypes
  and not the number of declarations in the KB.  Bounded on the walk as well as on the
  answer: past `limit` supertypes the probe stops and `:exact?` says so."
  [kb t context limit]
  (let [up     (nm/by-print-key (genls kb t context))
        probed (into [] (take limit) up)
        rows   (distinct
                (for [u     probed
                      sx    (sentexes-with-arg kb 3 u {:believed? true})
                      :let  [s (:sentence sx)
                             f (nm/functor s)]
                      :when (and ('#{arg genlArg} f)
                                 (= 4 (count s))
                                 (visible-here? kb sx context))]
                  {:predicate (second s) :position (nth s 2) :kind (keyword f) :type u}))]
    (bounded-rows rows (juxt :predicate :position :type) limit (<= (count up) limit))))

(defn- mention-counts
  "The predicates `x` appears under, with how many stored sentexes each — read off the
  inverted term index, which is the only index that answers \"where is this term used\"
  without knowing the position first.  There is no O(1) form of the per-predicate count,
  so the read stops at `describe-scan` sentexes and says `:exact? false` where that limit
  cut the walk.  A negation counts under the predicate it negates, never under `not`."
  [kb x context limit]
  (let [seen (into [] (take (inc describe-scan)) (find-sentexes kb x))
        cut? (> (count seen) describe-scan)
        body (fn [s] (if (and (sequential? s) (= 'not (nm/functor s))) (second s) s))
        rows (->> (take describe-scan seen)
                  (filter #(visible-here? kb % context))
                  (keep #(nm/functor (body (sx/sentence-of %))))
                  frequencies
                  (map (fn [[p n]] {:predicate p :count n})))]
    (bounded-rows rows :predicate limit (not cut?))))

(defn- described-role
  "Which of `describe`'s four shapes `term` takes, read from `context`.  A variable, a
  number and a context are decided by `term-role`'s spelling read.  Otherwise stored
  content decides: a `relation?` is a predicate, and any other node of the `genl`
  hierarchy is a type.  A term with neither falls back to the spelling, a display read
  only.  The browser's term colouring decides a node of the hierarchy the same way."
  [kb term context]
  (let [r (term-role term)]
    (cond
      (#{:variable :number :context} r) r
      (relation? kb term context)       :predicate
      (contains? (types kb) term)       :type
      :else                             r)))

(defn- computed-spec-of
  "The contexts a reified context is a **computed** spec of: the `(genlCx C ?super)`
  sentexes nobody asserted, which a `contextArgSubrelation` declaration materialized from
  the two contexts' arguments (docs/context-nat.md).  Absent for a context somebody wrote
  down, which is every context in the shipped topology."
  [kb term context limit]
  (bounded-terms (->> (visible-matches kb (list 'genlCx term '?super) context)
                      (remove #(premise? kb (:id %)))
                      (keep #(nth (:sentence %) 2 nil))
                      (into #{}))
                 limit))

(defn describe
  "Everything the KB holds about one term, as one map, keyed by the term's own role
  (`term-role`) — the read behind \"what can I ask about `X`?\".

  Four shapes, and every one of them carries `:term`, `:role`, `:context`, the KB's own
  `:comment` strings for the term, and the three closure lines the taxonomy answers:
  `:genls` (supertypes), `:specs` (subtypes) and `:disjoint`.  Predicates live in the same
  `genl` hierarchy types do, so those three are a predicate's parents and children as well
  as a type's.  On top of that:

  | `:role` | also carries |
  |---|---|
  | `:predicate` | `:arity`, the exact length that binds it, its own or one inherited through `genl` (nil where none binds or the KB has been told two), `:arity-via`, the predicate that length is bound on, `:arg-declarations`, `:props`, `:inverse`, `:extent-count`, and the four grants `:closed-extent?` `:abducible?` `:modal?` `:decontextualized?` |
  | `:type` | `:predicates-for-type` — which predicates' argument declarations admit it — and `:instance-count` |
  | `:individual` | `:types` (asserted, not their supertypes) and `:predicates`, the predicates it appears under with a count each |
  | `:context` | `:up` / `:down` (the `genlCx` ancestor sets), `:sentex-count`, and `:computed-spec-of` where the context is a reified NAT |

  Any other role — a variable, a number, a lexeme, a sense, a spelling that declares none
  — answers the common shape and nothing else, rather than guessing which of the four it
  meant.  Stored content overrides `term-role`'s spelling read twice: a `relation?` at
  `context` is a predicate, and any other node of the `genl` hierarchy is a type
  (`described-role`).

  **Everything declaration-shaped is read from `context`'s `genlCx` ancestor set**, never from
  the whole KB: an `arg` declaration, a `modal_predicate` grant and a `comment` are each a
  policy of the context that states them, so `describe` at `CxWell` and at `CxUniverse` are
  two different — and both correct — answers.  The taxonomy closures are scoped the same
  way.  `?ctx`, the default, reads every context, which is the unscoped reading the browser
  shows.

  **Every list is truncated, with its size beside it.**  A term list reads
  `{:terms :total :exact? :sorted?}` and a row list `{:rows :total :exact? :sorted?}`:
  `:total` is the size of the whole answer, `:exact?` is false where that size is a bound
  rather than a count, and `:sorted?` is false where the list is in the closure's own
  order because sorting it was not worth the walk.  `:limit` (`default-describe-limit`) is
  how many entries a returned list holds, and `describe-opt-keys` is the key set.

  `:extent-count` and `:instance-count` are **stored** counts (`count-with-functor`'s
  contract): O(1), and so possibly ahead of what `sentexes-matching` answers.  The
  per-predicate mention counts are the one read that is neither — they walk the term index
  and stop, which is what `:exact?` reports on that row list.

  `props` and `has-prop?` answer the metadata `:props` leaves out (`:reifiable` /
  `:unreifiable` classify a function, `:forced-decontextualized` a stronger form of one of
  the grants, `:forced-monotonic` the set whose literals are never a loser).  docs/api.md, docs/troubleshooting.md."
  ([kb term] (describe kb term '?ctx {}))
  ([kb term context] (describe kb term context {}))
  ([kb term context opts]
   (opts/check! opts describe-opt-keys "describe"
                (str "A limit this entry point does not read is a limit the caller asked for,"
                     " did not get, and is told nothing about."))
   ;; the value refusal every cap owes (`check-limit!`): a string reached `take` and
   ;; threw a bare cast error — over the daemon a 500 — and a zero or negative limit
   ;; answered every list empty under a `:total` that looked like an answer
   (when-some [n (:limit opts)]
     (check-limit! n "describe :limit"))
   (let [limit (or (:limit opts) default-describe-limit)
         role  (described-role kb term context)
         up    (genls kb term context)
         ptns  (disjoint-partners kb context term)
         tx    (reasoning/taxonomy kb)
         base  {:term     term
                :role     role
                :context  context
                :comment  (comments-on kb term context)
                :genls    (bounded-terms (disj up term) limit)
                :specs    (bounded-terms (disj (specs kb term context) term) limit)
                ;; the **declared** edges beside the closures they generate, one `genl`
                ;; step and not reflexive.  A reader arriving at a term wants what it was
                ;; told — `dog` is a `mammal` — where the closure is what a subsumption
                ;; check needs and, at `thing`, is 110,128 names.  O(degree) off the same
                ;; adjacency the closure walk is built on.
                :genls-direct (bounded-terms (tax/direct-genls tx term context) limit)
                :specs-direct (bounded-terms (tax/direct-specs tx term context) limit)
                :disjoint (disjoint-line kb context ptns limit)
                ;; both readings, because they answer different questions and the
                ;; partners are already in hand.  `:disjoint` is every type the
                ;; separation reaches, which is what a membership check is against;
                ;; `:disjoint-maximal` is the handful of types it was declared between,
                ;; which is what a reader asking "what is this NOT" can hold in their
                ;; head — one collection in the OpenCyc import is disjoint from 79,638
                ;; types and separated from 43 of them.
                :disjoint-maximal (bounded-terms (set ptns) limit)}]
     (case role
       :predicate
       (let [len (arity/relation-length kb term)]
         (assoc base
                :arity             (:exact len)
                :arity-via         (when (:exact len) (:via len))
                :arg-declarations  (declarations-on kb term context)
                :props             (into (sorted-set)
                                         (filter #(has-prop? kb % term context))
                                         describe-props)
                :inverse           (inverse-of kb term context)
                :extent-count      (count-with-functor kb term)
                :closed-extent?    (has-prop? kb :closed-extent term context)
                :abducible?        (has-prop? kb :abducible term context)
                :modal?            (granted? kb 'modal_predicate term context)
                :decontextualized? (has-prop? kb :decontextualized term context)))

       :type
       (assoc base
              :predicates-for-type (predicates-for-type kb term context limit)
              :instance-count      (count-with-functor kb term))

       :individual
       (assoc base
              :types      (vec (nm/by-print-key (types-of kb term context)))
              :predicates (mention-counts kb term context limit))

       :context
       (cond-> (assoc base
                      :up           (bounded-terms (context-up kb term) limit)
                      :down         (bounded-terms (context-down kb term) limit)
                      :sentex-count (count-in-context kb term))
         (reified-term? term) (assoc :computed-spec-of
                                     (computed-spec-of kb term context limit)))

       base))))

;; ---- why: the justification graph down to premises ------------------------
;; `supporting-justifications` gives one hop.  `why` walks the whole way down to
;; premises, which is what "why does the KB believe this?" actually asks.

(defn readable-sentence
  "A sentex's sentence with the author's variable names restored — pass a sentex map
  (from `sentex` / `sentexes-matching`).  A rule is stored canonically numbered (`?var0`, `?var1`,
  …), which reads as gibberish; this applies its `:varmap` back so it displays as
  written (`?x`, `?y`).  A fact has no varmap and is returned unchanged; nil in, nil
  out.  Used by `why` and by any display of a stored rule."
  [sx]
  (when sx (sx/authored-sentence sx)))

(defn sentence-of
  "A sentex map's canonical sentence: a literal's `:sentence`, or for a rule the
  `(implies <antecedent> <consequent>)` form built from its `:antecedent` and
  `:consequent` — a rule map carries no `:sentence` of its own.  The variables are the
  canonical `?var0 ?var1 …`; `readable-sentence` gives the author's names instead.  nil
  in, nil out."
  [sx]
  (when sx (sx/sentence-of sx)))

(defn- why-node
  "One node of `why`'s graph: `handle`'s sentence, its context and its belief there,
  and for a believed derived node its justifications with their antecedent handles.
  `reader` is the walk's `exc/verdict-reader`."
  [kb reader handle]
  (let [sx   (sentex kb handle)
        base {:handle handle :sentence (readable-sentence sx) :context (:context sx)}
        read (delay (reader handle (:context sx)))]
    (cond
      (nil? sx)                 (assoc base :stored? false)
      ;; belief as the node's own context reads it, which is what `why-not` answers for
      ;; the same handle (`res/believed-at?`): a sentex IN in the network and withdrawn
      ;; where it is stored has no support to show
      (not (:believed? @read)) (assoc base :believed? false)
      (premise? kb handle)      (assoc base :believed? true :defeat-class (defeat-class kb handle)
                                       :premise? true :strength (:strength sx))
      :else
      (let [vs (:verdicts @read)]
        (assoc base :believed? true :defeat-class (defeat-class kb handle) :premise? false
               :support
               (mapv (fn [j]
                       (let [inf (:informant j)]
                         ;; the record names the rule in `:informant` alone, so the
                         ;; antecedents are the facts
                         (cond-> {:justification (:id j)
                                  :informant     inf
                                  :strength      (:strength j :monotonic)
                                  :verdict       (get vs (:id j))
                                  :because       (vec (:antecedents j))}
                           (integer? inf) (assoc :rule (readable-sentence (sentex kb inf))))))
                     (supporting-justifications kb handle)))))))

(defn why
  "Why does the KB believe `handle`?  The justification graph reachable from `handle`,
  as data:

    {:root h
     :nodes {h  {:handle h :sentence S :context C :believed? true :defeat-class :default
                 :premise? false
                 :support [{:justification jid :informant <rule handle or symbol>
                            :rule <the rule's sentence> :strength :monotonic
                            :verdict :supports :because [h1 h2 …]}]}
             h1 {…} h2 {…} …}}

  `:nodes` holds one node per reachable handle, and `:because` names antecedents by
  handle, so a node two justifications share appears once and the result grows with the
  reachable graph rather than with the number of paths through it.  A cycle in the
  justification graph is a cycle in `:nodes`.  The walk is iterative and has no depth
  bound.

  A **premise** is `:premise? true`, with the `:strength` it was asserted at, and has no
  `:support`.  A derived node's `:support` is its justifications in content order, and
  `:because` is each justification's antecedents.  The rule handle is lifted out of the
  antecedents into `:rule`, its variables in the author's names (`readable-sentence`).

  Each `:support` entry's `:verdict` is the reason the node's context reads on that
  justification (`justification-verdicts`): `:supports` for one that carries the node
  there, and a believed node can list one a guard defeat covers (`:guard`) or one its
  rule's exception blocks (`:blocked`) beside it.

  Belief is read at each node's **own context**, the reading `why-not` answers with.  A
  stored node that is not believed there (an `except`, or a scoped defeat at a vantage its
  context sees) is a leaf `{:believed? false}`; ask `why-not` for the reason
  (docs/nmtms.md).  An unknown handle (nil included) is a node `{:stored? false}`."
  [kb handle]
  (let [root   (the-handle handle "why")
        reader (exc/verdict-reader kb)]
    (loop [work [root] nodes {}]
      (if (empty? work)
        {:root root :nodes nodes}
        (let [h (peek work), work (pop work)]
          (if (contains? nodes h)
            (recur work nodes)
            (let [node (why-node kb reader h)]
              (recur (into work (mapcat :because) (:support node))
                     (assoc nodes h node)))))))))

(defn- contradicted-by-entries
  "`why-not`'s `:contradicted-by` entries for the sentex maps `sxs`, in content order.
  Printed through `nm/print-key`, so an ambient `*print-length*` cannot elide two long
  opposing sentences to one prefix."
  [kb sxs]
  (->> sxs
       (nm/sort-by-content-key (juxt #(nm/print-key (:sentence %)) #(str (:context %))) compare)
       (mapv (fn [o] {:handle (:id o) :sentence (readable-sentence o)
                      :context (:context o)
                      :defeat-class (defeat-class kb (:id o))}))))

(defn- excepted-argument
  "The argument for `sentence` in `context` that some excepted rule built and then
  discarded, or nil: each believed watched rule concluding the goal's predicate, seeded by
  unifying the goal with its consequent and joined against believed facts, whose exception
  holds in `context` (the query's).  `:exception` is a bare sentence for one conjunct and
  a vector for several.  The completion reported is the content-least by
  `nm/min-by-content-key` over the rule's sentence, the ground exception and the `:via`
  sentences, a structural key, so the answer does not follow the rule index's handle
  order."
  [kb sentence context]
  (->> (for [rh   (rules/direct-concluders (:index kb) (nm/functor sentence))
             :let [rsx (p/get-sentex (:records kb) rh)]
             :when (and rsx (rules/rule? rsx) (reads/watched-rule? (:index kb) rh) (in? kb rh))
             :let  [rule (chain/rule-fields-of kb rh rsx)
                    b0   (res/unify (:consequent rule) sentence)]
             :when b0
             {:keys [bindings handles]} (chain/solve-rule kb (:antecedents rule) b0)
             :when (not (chain/different-blocks? kb (:different rule) bindings context))
             except (provers/rule-exceptions kb rh context)
             :when (chain/exception-holds? kb except bindings context)]
         (let [ground (mapv #(sx/canon (res/substitute % bindings)) except)]
           [[(sx/sentence-of rsx) ground
             (mapv #(:sentence (p/get-sentex (:records kb) %)) handles)]
            {:rule rh
             :exception (if (= 1 (count ground)) (first ground) ground)
             :via (vec handles)}]))
       (nm/min-by-content-key first)
       second))

(defn- why-not-handle
  "`why-not` of a stored handle — the original arity, factored out so the sentence
  arity can delegate to it."
  [kb handle]
  (let [sx       (sentex kb handle)
        base     {:handle handle :sentence (readable-sentence sx) :context (:context sx)}
        excepted (delay (excepted-argument kb (:sentence base) (:context sx)))]
    (cond
      (nil? sx)         (assoc base :believed? false :reason :not-stored)
      ;; belief as the sentex's own context reads it: IN, and not withdrawn there by a
      ;; scoped defeat (`res/believed-at?`)
      (res/believed-at? kb handle (:context sx)) (assoc base :believed? true)
      ;; a firing an exception blocks is stored with a guard defeat
      ;; (docs/exceptions.md), and excepted is the more specific answer than the rest
      (some? @excepted)
      (merge (assoc base :believed? false :reason :excepted) @excepted)
      ;; Checked before `:defeated` and before `:unsupported`, because it is the more
      ;; specific answer and neither of the others is true of it: a superseded
      ;; spelling lost no argument and kept all of its support — it was *restated*
      ;; under the representative its terms now merge to.
      (jtms/superseded? (reasoning/tms kb) handle)
      (assoc base :believed? false :reason :superseded
             ;; rewritten from the **sentex's own context**, which is the only context
             ;; that supersedes it (`special/migrate-into`: `(= reader (:context sentex))`),
             ;; so the representative named is the one that context elected.  The unscoped
             ;; rewrite would name the global election, which diverges when a `rewriteOf`
             ;; outside this context's ancestor set re-elected the head — then `:sentence` names a
             ;; spelling this context never elected and `:handle` misses, while the
             ;; `:rewrites` map beside them is the correct scoped one, and the report
             ;; contradicts itself (docs/equality.md's context-scoped supersession).
             :superseded-by (let [r (kb/rewrite-goal kb (sx/sentence-of sx) (:context sx))]
                              {:sentence r
                               :handle   (kb/find-sentex-handle kb r (:context sx))
                               :rewrites (jtms/supersession (reasoning/tms kb) handle)}))
      ;; the loser of a placed nogood whose defeat is in force at its own context: the
      ;; other members of each such nogood, and the defeats
      (seq (exc/defeats-of kb handle (:context sx)))
      (let [ds (exc/defeats-of kb handle (:context sx))]
        (assoc base :believed? false :reason :defeated
               :contradicted-by (contradicted-by-entries
                                 kb (into [] (comp (mapcat #(apply concat (exc/defeat-member-sets kb %)))
                                                   (distinct)
                                                   (remove #{handle})
                                                   (keep #(sentex kb %)))
                                          ds))
               :grounds (clashes/defeat-grounds kb ds)
               :defeats ds))
      ;; IN in the network and removed from belief at its own context by a placed defeat
      ;; that context sees, of it or of what it rests on
      (and (jtms/in? (reasoning/tms kb) handle)
           (seq (exc/defeats-hiding kb handle (:context sx))))
      (assoc base :believed? false :reason :withdrawn
             :withdrawn-by (mapv (fn [d]
                                   (let [o (sentex kb (kb/defeat-target (:sentence (sentex kb d))))]
                                     {:handle (:id o) :sentence (readable-sentence o)
                                      :context (:context o) :vantage (:context (sentex kb d))
                                      :defeat d}))
                                 (exc/defeats-hiding kb handle (:context sx))))
      ;; held OUT by the labeller: a tuple whose length breaks its functor's, or a fact
      ;; whose argument fails its declared type (docs/nmtms.md); or a rule held unbelieved
      ;; by an open application its context respells nowhere (docs/nat.md)
      (let [tms (reasoning/tms kb)] (or (jtms/forced? tms :out handle) (jtms/forced? tms :held handle)))
      (let [b (clashes/inert-binding kb sx)
            v (checks/held-conviction kb sx)]
        (cond-> (assoc base :believed? false :reason :inert)
          b (assoc :binding b)
          v (assoc :conviction v)))
      :else
      (let [vs      (exc/justification-verdicts kb handle (:context sx))
            void?   #(= :void (get vs (:id %)))
            js      (supporting-justifications kb handle)
            support (vec (for [j (remove void? js)]
                           {:justification (:id j)
                            :informant (:informant j)
                            :verdict   (get vs (:id j))
                            :missing   (vec (remove #(in? kb %) (jtms/rests-on j)))}))]
        (if-let [void (seq (filter void? js))]
          ;; a firing the forced-monotonic set convicts (the `:void` forced set): the rule,
          ;; and the antecedent predicates a declaration would make forced-monotonic
          (assoc base :believed? false :reason :forced-conclusion :support support
                 :convicted (mapv (fn [j]
                                    (let [r (sentex kb (:informant j))]
                                      {:justification (:id j) :informant (:informant j)
                                       :rule          (readable-sentence r)
                                       :not-forced-monotonic
                                       (if (jtms/forced? (reasoning/tms kb) :void (:id j))
                                         (checks/unforced-antecedents kb r)
                                         (checks/unforced-antecedents
                                          kb r (exc/forced-reading kb (:context sx))))}))
                                  void))
          (assoc base :believed? false :reason :unsupported
                 :premise? (premise? kb handle) :support support))))))

;; ---- why-not's near misses: the rules that nearly concluded it ------------
;; `:not-stored` is the emptiest answer `why-not` has: nothing is stored, so there is no
;; handle, no support and no defeat to report, and a reader whose rule was *supposed* to
;; conclude this is told only that it did not.  What the reader wants next is which rule
;; came closest and which of its antecedents the KB has not been told — and that is a
;; question about a search that was never run, so `:nearest` runs one.
;;
;; **Opt-in, and bounded.**  `why-not` is a diagnostic anybody may call in a loop over a
;; conflict list, and a backward search per call would change what the entry point costs; so the
;; search runs only when `:nearest` asks for it, under a depth bound and a wall clock the
;; caller can move.

(def why-not-opt-keys
  "Every key `why-not`'s sentence arity reads.  `:nearest n` asks for the n rules that came
  closest and is the switch that runs a search at all; `:max-depth` and `:max-ms` are that
  search's bounds.  A key off the key set is refused (`:unknown-option`) — a misspelt
  `:nearset` would answer the ordinary `why-not` and read exactly like a goal no rule
  concludes."
  #{:nearest :max-depth :max-ms})

(def default-nearest-depth
  "How many rule rewrites `{:nearest n}` searches through when the caller names no
  `:max-depth`.  Three, because a near miss is a rule whose antecedents are nearly all
  there, and one that needs four chained rewrites to reach the goal is not near anything a
  reader is going to fix by asserting one fact.  The node engine's termination *is* the
  depth bound (docs/inference.md), so this is a real ceiling and not a hint: a rule further
  down is not reported, and `:max-depth` is how a caller who knows their KB says so."
  3)

(def default-nearest-ms
  "The wall clock `{:nearest n}` gives its search when the caller names no `:max-ms`.  Two
  seconds — long enough for a schema-sized KB to empty its frontier, short enough that a
  diagnostic called on a large one answers rather than hangs.  A run that hits it reports
  `:status :timeout` under `:nearest-search` rather than pretending the frontier emptied."
  2000)

(defn- dead-frontier
  "The nodes of a `search-tree` that answered nothing — neither the node itself nor
  anything below it.  One pass in **reverse allocation order**: a parent is allocated
  before its children, so walking backwards marks every productive ancestor before it is
  reached."
  [nodes]
  (let [seed (into #{} (comp (filter #(seq (:results %))) (map :id)) nodes)
        live (reduce (fn [live n]
                       (if (and (live (:id n)) (some? (:parent-id n)))
                         (conj live (:parent-id n))
                         live))
                     seed
                     (reverse nodes))]
    (remove #(live (:id %)) nodes)))

(defn- antecedent-status
  "A rule's antecedents, under the bindings the goal forces on its consequent, split into
  a set the KB satisfies **jointly** and the rest.

  The antecedents are taken in the rule's canonical order, and each is joined onto the
  ones satisfied before it with `query` and no depth, so no rule expands and this cannot
  recurse into the search that produced the node.  One that joins goes to `:satisfied`,
  one that does not to `:missing`.  So the satisfied set holds under one binding of the
  variables the goal leaves open, and `:missing` is empty only when the whole body joins.
  The set is maximal, not maximum: adding any missing antecedent breaks the join.

  An antecedent the registry **refuses** — a shape it will not take a goal in — counts as
  missing rather than throwing: this is the entry point a reader reaches for when something has
  already gone wrong, and it may not be the second thing that fails.

  What comes back is written in the rule's **own** variable names, not the canonical
  `?var0` numbering it is stored under: a reader matching `:missing` against the rule they
  wrote should not have to translate it first (`readable-sentence` does the same for the
  rule's sentence)."
  [kb antecedents b0 context varmap]
  (-> (reduce (fn [acc a]
                (let [g    (sx/canon (res/substitute a b0))
                      ok   (try (boolean (seq (query kb (conj (:joined acc) g) context)))
                                (catch clojure.lang.ExceptionInfo _ false))
                      show (cond-> g varmap (sx/originalize varmap))]
                  (cond-> (update acc (if ok :satisfied :missing) conj show)
                    ok (update :joined conj g))))
              {:satisfied [] :missing [] :joined []}
              antecedents)
      (dissoc :joined)))

(defn- nearest-misses
  "The `n` rules that came closest to concluding `sentence` in `context`, read off a bounded
  node-engine search.

  Every dead frontier node carries the one rewrite that produced it — the literal it
  replaced and the rule it applied — so the rules that *could* have concluded the goal are
  what the frontier already holds, and no second enumeration of the rule index is needed.
  For each, the goal is unified with the rule's consequent and the antecedents are then
  judged under those bindings.

  Ranked by how many antecedents are satisfied, most first, and every tie broken on
  **content** — the rule's sentence, then what is missing, then the bindings — never on the
  rule's handle, which is assertion order (docs/defenses.md)."
  [kb sentence context n max-depth max-ms]
  (try
    (let [tree  (search-tree kb sentence context {:max-depth max-depth :max-ms max-ms})
          nodes (:nodes tree)
          dead  (dead-frontier nodes)
          rows  (distinct
                 (for [nd    dead
                       :let  [rh (get-in nd [:rewrite :rule])
                              gl (get-in nd [:rewrite :goal])]
                       :when (integer? rh)
                       :let  [rsx (sentex kb rh)]
                       :when (and rsx (rules/rule? rsx))
                       :let  [rule (chain/rule-fields-of kb rh rsx)
                              b0   (res/unify (:consequent rule) gl)]
                       :when b0
                       :let  [vm (:varmap rsx)
                              {:keys [satisfied missing]}
                              (antecedent-status kb (:antecedents rule) b0 context vm)]]
                   {:rule          rh
                    :rule-sentence (readable-sentence rsx)
                    :satisfied     satisfied
                    :missing       missing
                    ;; the rule's own variable names here too, so `:bindings` reads
                    ;; against the rule as written and can be handed back to `query`
                    :bindings      (into {} (map (fn [[k t]] [(get vm k k) t])) b0)}))
          rank  (nm/sort-by-content-key
                 (juxt #(- (count (:satisfied %)))
                       :rule-sentence
                       :missing
                       #(vec (nm/sort-by-content-key first (map vec (:bindings %)))))
                 rows)]
      {:nearest        (vec (take n rank))
       :nearest-search {:engine     :node-engine
                        :status     (:status tree)
                        :max-depth  max-depth
                        :max-ms     max-ms
                        :nodes      (count nodes)
                        :dead       (count dead)
                        :candidates (count rows)}})
    (catch clojure.lang.ExceptionInfo e
      {:nearest        []
       :nearest-search {:engine :node-engine
                        :status :refused
                        :max-depth max-depth
                        :max-ms max-ms
                        :type (:type (ex-data e))
                        :message (ex-message e)}})))

(defn- inherited-sentex-handle
  "The handle of a sentex for `sentence` stored in a context `context` inherits from, or
  nil when no context it sees stores one.

  `why-not`'s sentence arity probes `context` itself first; this is what it asks next, so
  that a sentence stored in a general context and read from a specific one is explained
  rather than reported as `:not-stored`, which is the answer `ask?` and `believed?` — both
  of which walk the `genlCx` ancestor set — would contradict.

  **The most specific candidate answers.** Several visible contexts can store the sentence,
  and the one a reader is asking about is the nearest: a candidate another candidate sees
  is dropped, and a tie among the rest is broken on content (`nm/print-key`), never on a
  handle."
  [kb sentence context]
  (when-not (or (nil? context) (sx/variable? context))
    (let [tax   (reasoning/taxonomy kb)
          cands (into [] (keep (fn [c]
                                 (when (not= c context)
                                   (when-let [h (kb/find-sentex-handle kb sentence c)] [c h]))))
                      (tax/context-up tax context))
          most  (into [] (remove (fn [[c _]]
                                   (some (fn [[c2 _]] (and (not= c c2) (tax/sees? tax c2 c)))
                                         cands)))
                      cands)]
      (peek (first (sort-by (comp nm/print-key first) (seq (or (seq most) cands))))))))

(defn why-not
  "Why does the KB *not* believe `handle`?  The complement of `why`, as data:

    {:handle h :sentence S :context C :believed? false :reason <keyword> …}

  | `:reason` | means | carries |
  |---|---|---|
  | `:not-stored` | no sentex has this handle | — |
  | `:superseded` | an equality merge restated it under its class representative; it lost no argument and retracting the equality gives it straight back | `:superseded-by` `:rewrites` |
  | `:defeated` | the target of a placed `defeat` in force at its own context, whose handles `:defeats` names and whose nogoods convict through the declarations `:grounds` names, as a clash report's do | `:contradicted-by` `:defeats` `:grounds` |
  | `:withdrawn` | IN in the network, and not believed at its own context because every justification rests on a handle a placed `defeat` in force there hides; each `:withdrawn-by` entry names that handle, its context, the `:defeat` and the defeat's context under `:vantage` (docs/nmtms.md) | `:withdrawn-by` |
  | `:inert` | a tuple whose length breaks its functor's, or a fact whose argument fails its declared argument type, stored and held OUT (docs/nmtms.md). `:conviction` is the argument check's problem map, the one `try-assert` throws as `:definitional-clash` (docs/argtypes.md). `:binding` names the length the tuple breaks, `{:length n}` or `{:min m}`, the predicate `:via` binds it and the binding handles under `:grounds` (docs/taxonomy.md, \"Arity\") | `:binding` for a tuple, `:conviction` for an argument |
  | `:forced-conclusion` | not a premise, and a supporting justification is a firing held void, at its own context, for concluding a forced-monotonic literal from antecedents that are not forced-monotonic (docs/nmtms.md). Each `:convicted` entry names the `:rule` and, under `:not-forced-monotonic`, the antecedent predicates a `forced_monotonic_predicate` declaration would make forced-monotonic; `:support` lists the other justifications as `:unsupported` does | `:convicted` `:support` |
  | `:unsupported` | not a premise, and no supporting justification reads `:supports` at its own context: each entry's `:verdict` is `justification-verdicts`' reason, and `:missing` lists the handles it rests on that are OUT in the network | `:support` with `:verdict` and `:missing` |
  | `:excepted` | a rule applied and its `exceptWhen` query held: under forward chaining its conclusion is stored with a guard defeat, through `:monotonic` and `:default` blockers alike (docs/exceptions.md) | `:rule` `:exception` `:via` |
  | `:closed-extent` | *(sentence arity only)* nothing stored or derived says so, **and** `(closed_extent_predicate P)` is visible here, or a `(closedExtentForArg P n v)` whose position `n` the sentence fills with `v` — so the KB is not silent about it, it says the extent is complete and this is not in it | — |

  A believed handle yields `{:believed? true}` and no `:reason`.  An empty `:support`
  under `:unsupported` means it never had a justification at all.  A nil handle is
  `:not-stored` — the answer for a sentence the KB does not hold — while a non-handle
  (a vector of handles included) is refused (`:bad-handle`), as `why` refuses it.

  **`:contradicted-by` is read off the placed nogoods.**  It names the other members of
  every placed `contradicts` holding a `nogood` justification on the same antecedents as
  a defeat of the handle (`exc/defeat-member-sets`), including a nogood that does not
  convict at that context.

  A stored-but-disbelieved handle is checked for an exception first: excepted is the
  more specific answer than the rest.

  **The sentence arity** `(why-not kb sentence context)` exists because `exceptWhen`
  produces an answer no handle can carry: a conclusion blocked through `:monotonic` facts
  is never stored, so there is nothing to pass to the handle arity.  A stored sentence
  delegates to that arity.  A sentence `context` stores
  nothing for is looked for in the contexts `context` inherits from, most specific first
  (`inherited-sentex-handle`), since `ask?` and `believed?` answer from those too.  Neither
  stored, inherited nor excepted is `:not-stored`.  It takes an `(ist Ctx S)` sentence, asking after S in Ctx and
  reporting it under that context (`ist-goal`).

  **`{:nearest n}` answers the emptiest case.**  `:not-stored` says nothing is there, which
  is exactly the answer a reader whose rule was supposed to conclude the goal cannot use.
  The fourth arity `(why-not kb sentence context {:nearest n})` runs a **bounded backward
  search** and reports, under `:nearest`, the n rules that came closest — each as
  `{:rule :rule-sentence :satisfied :missing :bindings}`, ranked by how many antecedents
  are satisfied and tied on content.  `:satisfied` holds under one binding of the variables
  the goal leaves open, so `:missing` is empty only when the whole body joins.  `:missing` is the list to read: it is the antecedent
  the KB has not been told.

  It costs a search, which is why it is **off by default**: `why-not` is called in a loop
  over a conflict list, and a backward search per call would change what the entry point costs.
  The bounds are `:max-depth` (`default-nearest-depth`) and `:max-ms`
  (`default-nearest-ms`), both overridable, and `:nearest-search` reports which of them
  bit — `:status` is `search-tree`'s `:complete` / `:bounded` / `:timeout`, or `:refused`
  where the search would not start.  `why-not-opt-keys` is the key set.

  **The frontier is the node engine's, whatever `*query-engine*` is bound to.**  The DFS
  prover holds its unfinished proofs on the JVM stack and unwinds them as it goes, so it
  has no dead frontier left to read once it has failed; the node engine's state is a value
  that outlives the search, and `search-tree` is the read of it (docs/inference.md).  So a
  goal the DFS reaches and the node engine does not — one needing more rewrites than
  `:max-depth` allows — has no near miss reported, and `:nearest-search`'s `:status` and
  `:max-depth` are what say so.  `:nearest` is attached to `:not-stored` alone: every
  other reason already names the thing that stopped it.

  docs/exceptions.md, docs/equality.md, docs/troubleshooting.md."
  ([kb handle] (why-not-handle kb (the-handle handle "why-not")))
  ([kb sentence context]
   (let [[sentence context] (checked-ist-goal kb sentence context)
         ;; the stored spelling of a ground reifiable NAT is its constant, looked up where
         ;; `assert` stores it (`handle-of`)
         s (nat-read/maybe-reify-for-read kb sentence context)
         h (kb/find-sentex-handle kb s (stored-context kb s context))]
     (if h
       (why-not-handle kb h)
       (if-let [exc (excepted-argument kb sentence context)]
         (merge {:handle h :sentence sentence :context context :believed? false
                 :reason :excepted}
                exc)
         (if-let [h (or h (inherited-sentex-handle kb sentence context))]
           (why-not-handle kb h)
           {:handle nil :sentence sentence :context context :believed? false
            ;; a closed extent is the *more specific* answer than "nobody said so": the
            ;; KB is not silent about this sentence, it says the extent is complete and
            ;; this is not in it — which is what makes `(not S)` derivable (docs/naf.md)
            :reason (if (provers/closed-extent-for? kb sentence context)
                      :closed-extent
                      :not-stored)})))))
  ([kb sentence context opts]
   (opts/check! opts why-not-opt-keys "why-not"
                (str "A misspelt :nearest reads as no request at all, and the ordinary"
                     " :not-stored answer is exactly what a goal no rule concludes gives."))
   ;; the value refusal beside the key check: `{:nearest "3"}` read as no request
   ;; answers the ordinary `:not-stored`, which is the silence the key set exists to
   ;; refuse.  `0` stays legal and asks for nothing; nil is the absent key.
   (when-some [n (:nearest opts)]
     (when-not (nat-int? n)
       (throw (ex-info (str "why-not :nearest must be a non-negative integer, got " (pr-str n))
                       {:type :unknown-option :mismatch :bad-value :nearest n}))))
   (let [base (why-not kb sentence context)
         n    (:nearest opts)]
     (if (and (number? n) (pos? (long n)) (= :not-stored (:reason base)))
       (merge base (nearest-misses kb (:sentence base) (:context base) (long n)
                                   (or (:max-depth opts) default-nearest-depth)
                                   (or (:max-ms opts) default-nearest-ms)))
       base))))

;; ---- preview: what a batch would do, without leaving it done -------------
;; docs/preview.md.

(defn- preview-support
  "`preview`'s `:justification` for `handle`: the content-least supporting
  justification's informant, strength and antecedent sentences, and `:rule` when the
  informant is a handle.  Nil when no justification supports `handle`."
  [kb handle]
  (when-let [j (first (supporting-justifications kb handle))]
    (let [inf   (:informant j)
          rule? (integer? inf)]
      (cond-> {:informant   inf
               :strength    (:strength j :monotonic)
               :antecedents (mapv #(readable-sentence (sentex kb %)) (:antecedents j))}
        rule? (assoc :rule (readable-sentence (sentex kb inf)))))))

(defn- diff-order
  "A belief-diff entry's content key: its sentence then its context, printed with the
  print bounds off so an ambient `*print-length*` cannot tie two entries
  (`clashes/report-order`'s key; docs/preview.md, \"The answer\")."
  [e]
  (binding [*print-length* nil *print-level* nil]
    [(pr-str (:sentence e)) (pr-str (:context e))]))

(defn- preview-added-entry [kb handle]
  (let [sx (sentex kb handle)]
    {:handle        handle
     :sentence      (readable-sentence sx)
     :context       (:context sx)
     :premise?      (boolean (premise? kb handle))
     :justification (preview-support kb handle)}))

(defn- preview-removed-entry [kb handle]
  (let [sx (sentex kb handle)
        w  (why-not kb handle)
        d  (dissoc w :handle :sentence :context :believed? :reason)]
    (cond-> {:handle   handle
             :sentence (readable-sentence sx)
             :context  (:context sx)
             :reason   (:reason w)}
      (seq d) (assoc :detail d))))

(defn- preview-forget-dead-handles
  "Blank the `:handle` of each entry whose sentex the rollback took away."
  [kb entries]
  (mapv (fn [e] (cond-> e (nil? (p/get-sentex (:records kb) (:handle e)))
                        (assoc :handle nil)))
        entries))

(defn preview
  "What would this batch do to the KB — **without** leaving it done.

  `batch` is `edit`'s shape, `{:add [[sentence context opts?] …] :remove [handle …]}`.
  The adds are asserted, the removes are suspended, belief settles once, the difference
  is read off, and every write is taken back at the handles it made.  Returns

    {:believed-added   [{:sentence S :context C :handle h|nil :premise? bool
                         :justification {:informant i :strength k :rule S
                                         :antecedents [S …]}} …]
     :believed-removed [{:sentence S :context C :handle h :reason kw :detail {…}} …]
     :refused          [ …`check-edit` shape… ]
     :violations       [ …`violations` shape… ]
     :contradictions   [ …`contradictions` shape… ]
     :bounded?         bool
     :owed-releases    n
     :release-path     :deferred | :swept}

  with each half in content order, `:handle` nil for content the batch created,
  `:reason` as `why-not`'s, and the standing dilemmas subtracted from `:contradictions`.
  A `:refused` line is skipped and the rest of the batch previewed.

  `opts` takes `:max-depth`, `:max-term-depth` and `:max-derivations` (chaining) and `:max-results` (a
  positive integer capping each half); `:bounded?` is true when one of them cut the
  answer.  `:release-withheld?` true runs the withheld-mint release sweep in the preview's
  settle (`:release-path :swept`); by default the settle keeps the releases owed
  (`special/*release-withheld?*`), `:owed-releases` counts them, the diff omits the mints
  and the contradictions they would draw, and the rollback discards the debt.  An unknown
  key and a cap that is not a positive integer are refused
  (`:unknown-option`), and so is an unrecovered KB (`:unrecovered-kb`), as `edit!`
  refuses it.  The handle counter and the `chain-stats` / `settle-stats` counters stay
  moved.  Holds the single writer for its duration.  Under `oplog/replay!` it runs the
  writes and the rollback alone, reads neither belief nor the dilemmas, and returns nil.
  docs/preview.md."
  ([kb batch] (preview kb batch nil))
  ([kb batch opts]
   ;; a batch `edit` refuses outright is refused here too
   (check-writable! kb "preview")
   (check-edit-batch! batch)
   (check-bound-opts! opts #{:max-depth :max-term-depth :max-derivations :max-results
                             :release-withheld?} "preview")
   (when-some [n (:max-results opts)] (check-limit! n "preview :max-results"))
   (let [tms        (reasoning/tms kb)
         refused    (check-edit kb batch)
         bad-add    (into #{} (comp (filter #(= :add (:in %))) (map :index)) refused)
         bad-remove (into #{} (comp (filter #(= :remove (:in %))) (map :index)) refused)
         baseline   (batch-baseline kb)
         filed      (:filed baseline)
         audit      (atom {})
         mark       (volatile! nil)
         touched    (atom #{})
         suspended  (atom [])
         thrown     (atom [])
         truncated? (atom false)
         chain-opts (select-keys opts [:max-depth :max-term-depth :max-derivations])
         limit      (:max-results opts)
         sweep?     (boolean (:release-withheld? opts))
         ;; a replayed preview reproduces the handles it allocated; its answer went to the
         ;; caller that logged it
         report?    (not oplog/*replaying?*)
         result     (atom nil)]
     (when sweep? (swap! (reasoning/mint-queues kb) dissoc :defer-next))
     (try
       ;; the feed is off for the batch here and for the rollback in `rollback-batch!`
       (with-bindings {#'feed/*enabled?* false
                       #'settle/*sweep?* false
                       ;; the suspensions, and the rollback's re-marks, flip labels no
                       ;; settle made
                       #'settle/*relabelled-before?* true
                       #'settle/*touched-sink* (when report? touched)
                       #'observe/*write-record* (when report? (java.util.IdentityHashMap.))
                       #'viol/*batch-entries* filed
                       #'special/*release-withheld?* sweep?}
         (binding [entry/*premise-audit* audit
                   entry/*write-mark*    mark
                   *defer-settle?* true]
           (doseq [[i entry] (map-indexed vector (:add batch))
                   :when (not (bad-add i))
                   :let [[sentence context entry-opts] entry]]
             (try
               (assert kb sentence context (merge entry-opts chain-opts))
               (catch clojure.lang.ExceptionInfo e
                 (swap! thrown conj (assoc (select-keys (ex-data e) [:type])
                                           :in :add :index i :entry entry
                                           :message (ex-message e)))))
             (when (:truncated? (:last @(reasoning/chain-stats kb))) (reset! truncated? true)))
           ;; suspended, not retracted (docs/preview.md, "The mechanism")
           (doseq [[i h] (map-indexed vector (:remove batch))
                   :when (and (not (bad-remove i)) (jtms/premise? tms h))]
             (swap! suspended conj [h (jtms/premise-strength tms h)])
             (jtms/suspend-premise tms h)
             ;; a real removal queues the re-checks at the removal entry point; a
             ;; suspension queues them here
             (recheck-suspended kb h)))
         ;; no re-chain seeds: a suspension removes no sentex, and the conclusion a
         ;; suspended edge licensed goes OUT, which `:believed-removed` reports
         (settle-after-teardown! kb (settle/rechain-owed kb @(reasoning/recheck kb)) nil)
         ;; built now: content the batch created does not survive the rollback, and
         ;; `why-not`'s answer for a datum the batch put OUT holds only while it is in force
         (when report?
           (let [region  (sort @touched)
                 in-now  #(when-let [sx (p/get-sentex (:records kb) %)]
                            (res/believed-at? kb % (:context sx)))]
             (reset! result
                     {:believed-added   (mapv #(preview-added-entry kb %) (filter in-now region))
                      :believed-removed (mapv #(preview-removed-entry kb %)
                                              (clojure.core/remove in-now region))
                      :refused          (into refused @thrown)
                      :violations       (viol/filed-by-batch kb filed)
                      ;; the standing dilemmas are subtracted after the rollback
                      :contradictions   (clashes/opened kb (-> @touched
                                                               (into (keys @audit))
                                                               (into (map first) @suspended)))
                      :bounded?         @truncated?
                      :owed-releases    (- (special/owed-releases kb)
                                           (count (:owed (:queues baseline))))
                      :release-path     (if sweep? :swept :deferred)}))))
       (finally
         (binding [settle/*relabelled-before?* true
                   special/*release-withheld?* false]
           (rollback-batch! kb (assoc baseline :audit audit :suspended @suspended
                                      :mark mark)))))
     ;; belief before, read on the restored KB (docs/preview.md, "Cost")
     (when report?
       (let [believed-before? #(res/believed-at? kb (:handle %) (:context %))
             ;; content order before the cap, so the cap picks by content; the key is built
             ;; once per entry (`nm/sort-by-content-key`)
             cap (fn [xs] (cond->> (nm/sort-by-content-key diff-order compare xs)
                            (pos-int? limit) (take limit)))
             added   (into [] (clojure.core/remove believed-before?) (:believed-added @result))
             removed (into [] (filter believed-before?) (:believed-removed @result))]
         (assoc @result
                :contradictions   (clashes/standing-removed kb (:contradictions @result))
                :believed-added   (preview-forget-dead-handles kb (cap added))
                :believed-removed (preview-forget-dead-handles kb (cap removed))
                :bounded?         (boolean (or (:bounded? @result)
                                               (and (pos-int? limit)
                                                    (or (> (count added) limit)
                                                        (> (count removed) limit)))))))))))

(defn- moved-handles
  "Which handles of a relabelled `region` gained belief and which lost it, as
  `[added removed]` in content order (`diff-order`), ranked here because the callers cap
  these vectors.  `was-in` is the part of the region believed when a relabel first
  touched it (`jtms/touched-in`).  A handle with no record left is dropped.  The one
  delta `edit-with-consequences!` and the change feed both read (docs/preview.md,
  \"Where the diff comes from\")."
  [kb region was-in]
  (let [ordered (->> region
                     (keep (fn [h]
                             (when-let [sx (p/get-sentex (:records kb) h)]
                               {:handle h :sentence (readable-sentence sx) :context (:context sx)})))
                     (nm/sort-by-content-key diff-order compare))
        in-now  (fn [{:keys [handle context]}] (res/believed-at? kb handle context))
        was?    #(was-in (:handle %))]
    [(into [] (comp (clojure.core/remove was?) (filter in-now) (map :handle)) ordered)
     (into [] (comp (filter was?) (clojure.core/remove in-now) (map :handle)) ordered)]))

(defn edit-with-consequences!
  "`edit`, plus what the batch turned out to **mean** — the belief it added and the
  belief it took away, in `preview`'s entry shapes.  Returns `edit`'s
  `{:added :removed}` with `:believed-added`, `:believed-removed` and `:bounded?` merged
  in.

  The removed half omits what the dependency-directed sweep deleted, which has no record
  left to describe; `preview` names it.  `opts` takes `:max-results n`, capping each half
  as `preview`'s does, and `edit!`'s `edit-opt-keys`; an unknown key and a cap that is not
  a positive integer are refused (`:unknown-option`).  docs/preview.md, \"The other
  direction\"."
  ([kb batch] (edit-with-consequences! kb batch nil))
  ([kb batch opts]
   (check-bound-opts! opts (conj edit-opt-keys :max-results) "edit-with-consequences")
   (when-some [n (:max-results opts)]
     (check-limit! n "edit-with-consequences :max-results"))
   (let [touched (atom #{})
         was-in  (atom #{})
         result  (binding [settle/*touched-sink*    touched
                           settle/*touched-in-sink* was-in]
                   (edit! kb batch (not-empty (dissoc opts :max-results))))
         limit   (:max-results opts)
         cap     (fn [xs] (cond->> xs (pos-int? limit) (take limit)))
         [added removed] (moved-handles kb @touched @was-in)]
     (assoc result
            :believed-added   (mapv #(preview-added-entry kb %) (cap added))
            :believed-removed (mapv #(preview-removed-entry kb %) (cap removed))
            :bounded?         (boolean (and (pos-int? limit)
                                            (or (> (count added) limit)
                                                (> (count removed) limit))))))))

;; ---- the change feed: telling an application that belief moved ------------
;;
;; An application that has to *ask* whether belief changed is wrong in the two
;; directions polling is always wrong in: it misses whatever happened between two asks,
;; and it costs the most on the KBs where the least is moving.  Nothing here computes
;; anything new to fix that — the information already exists and was being discarded.
;; Every settle knows the region it relabelled and which of that region was believed
;; when it first touched it, `moved-handles` above already turns that pair into a delta,
;; and `preview` already renders one.  A feed is that answer handed to a listener
;; instead of dropped.
;;
;; **Belief, not storage.**  Delivery hangs off the settle (`settle/settle`'s tail, via
;; `feed/deliver!`), never off the store choke points, and the difference is not
;; cosmetic: an `assert` stores a sentex whose label several later justifications
;; settle, and a store event would therefore announce content the KB does not believe
;; and stay silent when it later does.  `vaelii.impl.observe`'s observers *do* fire on
;; storage, because an alpha memory mirrors the stored fact set; belief does not.
;;
;; **What a listener cannot be told.**  Only a stored sentex is a TMS datum, so only a
;; stored sentex can enter or leave belief and be reported.  An answer that exists only
;; while a prover is computing it — an evaluable, an aggregate, `unknown`, an `arg`
;; type inference, a `set/backwardRule`'s conclusion — is nobody's belief and no relabel
;; carries it, which is why `watch` refuses a goal of that shape rather than watching it
;; silently for nothing.  The same limit `preview` and `edit-with-consequences` have.
;;
;; See docs/feed.md.

(defn- watch-match
  "The bindings `goal` takes on the sentex at `handle`, or nil when it does not answer.

  Matched with `res/match1`, which is the same subsumption a rule antecedent gets: a
  goal `(animal ?x)` is answered by a stored `(dog Muffet)` through the `genl` closure,
  and a goal `(parentOf ?x ?y)` by a stored `(fatherOf Tom Bob)`.  One cached closure
  lookup, so this stays a *filter over the region* rather than the re-run of a query
  that would make every mutation cost a query per listener.

  Context-scoped like every other read, on **both** halves of the match: the sentex must
  sit in a context the watch's own can see up the `genlCx` ancestor set, *and* the subsumption
  that connects the goal's predicate to the stored one is walked only through the `genl`
  edges that context can see — so a watch does not fire through a predicate-genl edge
  stated where it cannot see it, which is the edge `ask` from that context would not walk
  either.  A **variable** context watches every context and binds to the one that
  answered, which is the `'?ctx` convention `ask` already takes; it is unscoped on both
  halves alike."
  [kb goal context handle]
  (when-let [sx (p/get-sentex (:records kb) handle)]
    (let [any? (sx/variable? context)]
      (when (or any? (sees? kb context (:context sx)))
        (when-let [b (res/match1 kb goal (sx/sentence-of sx) (when-not any? context))]
          (cond-> b any? (assoc context (:context sx))))))))

(defn- watch-goal-problem
  "Why `goal` cannot be answered from a moved region, or nil when it can.

  Every one of these is a goal whose truth is a function of something the region does
  not hold, so matching it against the region's entries would be quietly wrong rather
  than merely incomplete — and being quietly wrong is the one thing a feed must not be.
  A conjunction joins against facts the batch never touched — **in either spelling**, the
  vector one and the `(and …)` one, which mean the same goal and are refused in the same
  words; an aggregate and a NAF literal are properties of a whole answer set, which a
  fact *leaving* belief can flip with nothing about the flip in the region; a
  `thereExists` is the same; an evaluable is computed and never stored.  `ist` is refused because a watch already has a context
  argument and would otherwise match nothing at all — no stored sentence has that
  functor, and neither has an `or`: a disjunction is a union of queries, and a watch
  matches one entry against one goal, so a registered one would fire never."
  [goal]
  (cond
    (vector? goal)
    "a conjunctive goal joins against facts outside the region a settle moved"

    (not (and (sequential? goal) (seq goal)))
    "a goal must be a sentence"

    ;; the same conjunction written with the connective rather than as a vector.  It is
    ;; the arm above and the `or` arm below at once: it joins against facts outside the
    ;; region, *and* no stored sentence has `and` for a functor, so a watch registered on
    ;; one fires never — which is the silent-nothing every arm here exists to refuse.
    (sx/some-form sx/conjunction? goal)
    (str "an `and` is a join against facts outside the region a settle moved, and no"
         " stored sentence unifies with a conjunction, so a watch on one would fire"
         " never — register one watch per conjunct")

    (sx/some-form sx/disjunction? goal)
    (str "an `or` is a union of queries rather than one query, and no stored sentence"
         " unifies with a disjunction, so a watch on one would fire never — register"
         " one watch per alternative")

    (and (symbol? (first goal)) (= sx/ist-functor (first goal)))
    "an `ist` names a context, and a watch takes its context as an argument"

    (sx/there-exists? goal)
    "a `thereExists` is a property of the whole answer set, not of one entry"

    (sx/deferred-literal? goal)
    (str "`" (first goal) "` is computed rather than stored, so no relabel carries it")))

(defn- moved-entries
  "The `{:believed-added :believed-removed}` a listener receives, from two handle
  vectors.  A `delay`, because the entries are the expensive half — a supporting
  justification and a `why-not` apiece — and a KB whose only listeners are standing
  queries never wants them: those filter to their own matches first and render only
  those."
  [kb added removed]
  (delay {:believed-added   (mapv #(preview-added-entry kb %) added)
          :believed-removed (mapv #(preview-removed-entry kb %) removed)}))

(defn- notify-listener!
  "Hand one listener its share of an event.  A standing query gets only the entries its
  goal answers, each with the `:bindings` that answered, and is not called at all when
  none of them do; a plain listener gets the whole diff.

  A listener that **throws** is logged and skipped: the settle that produced this event
  is already committed, so aborting here would leave the KB settled and the remaining
  listeners uninformed — the failure of one consumer is not a reason to lose the write
  or to punish its neighbours.  Two throws are not skipped that way: a
  `VirtualMachineError` is rethrown, and an `InterruptedException` sets the thread's
  interrupt flag again before it is logged and skipped (docs/feed.md)."
  [kb {:keys [f goal context token]} added removed entries]
  (try
    (if goal
      (let [prepared (quasiquote/prepare-goal-for-read kb goal context)
            matched  (fn [handles build]
                       (into [] (keep (fn [h]
                                        (when-let [b (watch-match kb prepared context h)]
                                          (assoc (build kb h) :bindings b))))
                             handles))
            in       (matched added preview-added-entry)
            out      (matched removed preview-removed-entry)]
        (when (or (seq in) (seq out))
          (f {:believed-added in :believed-removed out})))
      (f @entries))
    (catch VirtualMachineError e (throw e))
    (catch Throwable t
      (when (instance? InterruptedException t)
        (.interrupt (Thread/currentThread)))
      (trove/log! {:level :warn :id ::listener-threw
                   :msg   (str "a change-feed listener threw; skipping it: "
                               (ex-message t))
                   :error t
                   :data  {:token token :goal goal :context context}})
      nil)))

(defn- dispatch-feed!
  "Turn one settle's relabelled region into an event and deliver it, in registration
  order.  The `feed/install-dispatch!` extension point's other end.

  The diff is computed **once**, before any listener runs, which is what makes the
  content of a batch independent of delivery order: a listener that writes cannot change
  what its neighbours are told about *this* event, only produce a further one.  An event
  whose two halves are both empty is not delivered at all — a re-asserted sentex, or any
  mutation that moved no label, is not news."
  [kb region was-in]
  (let [ls (feed/listeners kb)]
    (when (seq ls)
      (let [[added removed] (moved-handles kb region was-in)]
        (when (or (seq added) (seq removed))
          (let [entries (moved-entries kb added removed)]
            ;; A listener may write, and its write settles — which would fold its region
            ;; into whatever sink the *original* caller bound, so an
            ;; `edit-with-consequences` would report a listener's assertions as
            ;; consequences of the batch.  A listener's writes are its own; the sinks are
            ;; closed for the duration and reopen for the caller's next settle.  A write a
            ;; listener makes lands inside the operation whose settle this is, so it marks
            ;; the KB's operation log unusable (`vaelii.impl.oplog`).
            (binding [settle/*touched-sink*    nil
                      settle/*touched-in-sink* nil
                      oplog/*listener?*        true]
              (doseq [l ls] (notify-listener! kb l added removed entries)))))))))

(defn watch
  "Be told when belief moves, instead of asking again.

  Two shapes, both returning a **token** for `unwatch`:

    (watch kb f)                  every belief change
    (watch kb goal context f)     a standing query — only what answers `goal`

  `f` is called with one argument, `{:believed-added [...] :believed-removed [...]}` in
  `preview`'s entry shapes, so an application renders a preview and a feed with one
  renderer.  A standing query's entries carry `:bindings` too, and `f` is not called at
  all when nothing its goal answers moved.  `context` scopes the goal up the
  `genlCx` ancestor set; a variable (`'?ctx`) watches every context and binds the one that
  answered.

  **The unit is the settle: one settle, one call.**  A batch under
  `with-deferred-settle` / `assert-many` / `edit` settles once, so its event is exactly
  what `edit-with-consequences` reports for the same batch — a conclusion derived and
  then defeated inside the batch appears in neither.  The entry points that settle more
  than once hold the feed and deliver one call: `retract!`, `edit!`, and an `assert`
  that mints a constant before the sentence it serves, which delivers none when it is
  refused.

  **`f` runs on the writing thread**, synchronously, after the settle and never inside
  it.  So it may read a settled KB and may write; a write produces its own event,
  delivered once the current round finishes.  A listener that writes on *every* event is
  an infinite loop, and delivery gives up after 64 rounds with a warning rather than
  hanging the writer.  One that throws is logged and skipped.  A listener doing real work
  should hand the event to a queue and return: this engine has one writer, and a slow
  listener slows it.

  **Four things never arrive**, and `preview` is what answers each: a mutation that moved
  no label; anything during a `preview`, `recover` or `reindex`; a retraction and every
  datum its sweep *deleted*, which have no record left to describe; and a spelling an
  equality merge displaced.  `edit-with-consequences` has the last two gaps identically —
  docs/feed.md.

  **Cost** is per relabelled region, never per stored sentex and never a re-run of the
  goal (`lein perf`'s `feed-listener-scaling`).  A KB with no listener pays one deref per
  settle.

  A goal whose answer is not a function of the region is **refused** (`:type
  :not-watchable`): a conjunction, an aggregate, `unknown`, `thereExists`, an evaluable,
  an `ist`.  Reach for those with `query` on a plain listener — the event says belief
  moved, the query says what it is now."
  ([kb f] (watch kb nil nil f))
  ([kb goal context f]
   ;; `fn?` (or a var naming one) rather than `ifn?`, because a *symbol* is `ifn?` and the
   ;; mistake this catches is `(watch kb '(dog ?x))` — the three-argument form written
   ;; with two.  Under `ifn?` that registers the goal as the listener and fails much
   ;; later, at the first delivery, having told the caller nothing was wrong.
   (when-not (or (fn? f) (var? f))
     (throw (ex-info (str "watch needs a function to call, got " (pr-str f)
                          " — (watch kb f) for every belief change, (watch kb goal"
                          " context f) for one goal")
                     {:type :not-watchable :f f})))
   (when goal
     (when-let [why (watch-goal-problem goal)]
       (throw (ex-info (str "watch cannot answer this goal: " why)
                       {:type :not-watchable :goal goal :reason why})))
     ;; A context that names nothing sees nothing, so the watch would match forever and
     ;; report never — the same silent-nothing the goal checks above exist to refuse.
     (when-not (symbol? context)
       (throw (ex-info (str "watch needs a context to scope its goal, or a variable for "
                            "every context; got " (pr-str context))
                       {:type :not-watchable :goal goal :context context
                        :reason "a goal watch is scoped, like every other read"}))))
   ;; installed on first use rather than at load, so a program that never watches never
   ;; puts a function behind the extension point — and `feed/deliver!`'s nil check then means
   ;; "nobody has ever watched this process", which is the cheapest possible answer
   (feed/install-dispatch! dispatch-feed!)
   (feed/register! kb (cond-> {:f f} goal (assoc :goal goal :context context)))))

(defn unwatch
  "Stop calling the listener `token` names; true if there was one.  Idempotent — a
  token already dropped removes nothing and says so.

  Called off the writer's thread, the listener can be called once more after this
  returns, for an event whose delivery read the registry before it (docs/feed.md)."
  [kb token]
  (feed/unregister! kb token))

(defn watchers
  "What is currently listening, in registration order: `{:token t}` for a plain
  listener, plus `:goal` and `:context` for a standing query.  The functions themselves
  are left out — a token is what `unwatch` takes, and a listener is not a value to
  compare."
  [kb]
  (mapv #(select-keys % [:token :goal :context]) (feed/listeners kb)))

;; ---- the log dial --------------------------------------------------------

(defn log-level
  "The level the engine's own logging prints at, or **nil** when the engine has
  installed no backend — which is the state a process is in until `set-log-level` is
  called or `VAELII_LOG_LEVEL` is set.  Nil is not `:info`: it says the level is
  whatever `taoensso.trove/*log-fn*` already holds, which is Trove's console backend at
  `:info` unless the host application installed one of its own."
  []
  (logging/current-level))

(defn set-log-level
  "Set how much the engine says, on a **running** process, and return the level.  One of
  `:error :warn :info :debug :trace`, quietest first; anything else is refused by name
  (`:type :unknown-option`) rather than read as the nearest legal value.

  Public here rather than in `impl` for the reason the diagnostics are: an operator
  holds a KB and a REPL, not a namespace map.  The process that most needs a different
  level is the one that cannot be restarted to get it — a daemon a week into a run, on a
  durable KB that pays `recover` on the way back up — and the level a process started
  with is the answer to a question nobody had yet.

  Process-wide and not per-KB: two KBs in one JVM share one `*log-fn*`.  It is also the
  one setting here that changes the **process** rather than a KB, which is why
  `vaelii.host.serve`'s op table does not carry it: every op in that table acts on the
  KB the daemon owns, the daemon's bearer token is optional on the loopback default, and
  an op that turns on `:trace` is a caller spending the operator's disk from the far end
  of a socket.  A daemon's level is the one its process started with
  (`VAELII_LOG_LEVEL`), or this call from its own REPL.

  `log-level` reads it back, so a caller that turns the dial up for one investigation
  can put it where it was."
  [level]
  (logging/set-level level))

;; ---- persistence / recovery ---------------------------------------------

;; (The taxonomy rebuild — `stored-declarations` and the per-functor replay — lives
;; in `vaelii.impl.special` now, as the `:rebuild` column of the special-predicate
;; table: it was the third hand-mirrored enumeration of the same functors, and the
;; table makes a rebuild arm that drifts from its integrate arm a load-time error.)

(defn recover
  "Rebuild the in-memory JTMS and taxonomy from the persistent stores (records and
  all indexes are already in the store).  Call after constructing a KB against
  an existing store — e.g. after a restart.  Derivation depths reset to 0 (they only
  bound future forward chaining).

  What the taxonomy ends up holding is a **composition**, and the contract is the whole
  of it rather than either half.  The JTMS is rebuilt first, so there is belief to read.
  The taxonomy then replays every **stored** special-predicate sentex rather than the
  believed ones — `:support` must record every asserting sentex, or a disbelieved
  supporter would be lost and clearing its defeat could never revive the entry
  (docs/taxonomy.md) — so that replay over-reads by construction, and the reconcile
  against belief immediately after it is what narrows the caches to what the KB entails.
  Belief is settled last.

  The rebuild orchestration lives in `vaelii.impl.recovery`, which sits below this
  namespace so the dump importer can recover a freshly loaded store through the same code
  without reaching up (docs/namespaces.md, \"The layering\")."
  [kb]
  (recovery/recover kb))

(defn reindex
  "Rebuild the index store — the trie, secondary roots, rule index, exception index,
  and term index — wholesale from the stored sentexes, then `recover`.  The repair for
  a torn record/index write and the migration for an index layout change; see
  `vaelii.impl.reindex`.  Returns {:sentexes n :rules n}.

  This is the repair a **derived** index needs and `recover` alone is not: an index
  rebuilt from the records is what makes `assert` find a stored sentence again, so it is
  what makes such a KB writable (`*write-unrecovered?*`)."
  [kb]
  (let [result (reindex/reindex kb)]
    (recover kb)
    (kb/note-hazards! kb {:no-index false})
    result))

;; ---- editing the records of a KB without belief --------------------------------
;; docs/storage.md, "Editing the records of a KB without belief".

(defn edit-records!
  "Apply a batch of premise removals and rule direction changes to the records of a KB
  **without belief**, and return what it did.  No check, no dependency sweep and no
  settle runs; `settle-record-edits!` settles any number of batches with one rebuild.

    `:remove`    — a seq of handles.  A record is deleted with its postings, unless a
                   justification the batch leaves standing concludes it, which then only
                   loses its premise mark;
    `:direction` — `{handle direction}`, a rule's new `:forward` / `:backward` /
                   `:forward-only` / `:inert` / `:both`, written into its record.

  Every justification resting on a deleted record, and every firing of a rule the batch
  takes off `:forward`, is deleted, except a rule firing resting on a deleted `genl` or
  `genlCx` edge, which `settle-record-edits!` reads and deletes.  Derived records left
  without support are not:
  `:seeds` in the answer names where the settle sweeps from.  A removal naming no stored
  record counts under `:absent`, so the same batch run again after a crash completes it.

  Returns `{:removed n :unpremised n :absent n :redirected n :justifications-removed n
  :seeds [h …]}`.  Refuses a KB with belief (`:belief-built`); an `except`, `defeat` or
  `exceptWhen` removal (`:record-edit-unsupported`); and a direction on a handle that is
  not a stored derive rule, or on a removed one (`:unknown-option`, `:unknown-handle`),
  all before anything is written.  docs/storage.md, \"Editing the records of a KB without
  belief\"."
  [kb batch]
  (let [h   #(the-handle % "edit-records!")
        res (record-edit/apply! kb (cond-> batch
                                     (contains? batch :remove)
                                     (update :remove #(into [] (map h) %))
                                     (contains? batch :direction)
                                     (update :direction #(into {} (map (fn [[k d]] [(h k) d])) %))))]
    ;; a removed membership or edge may have withheld a general mint anywhere, so the
    ;; argument-type pass is owed from the start (`arg-types-owed`)
    (when (some #(pos? (long (get res % 0))) [:removed :unpremised :redirected :justifications-removed])
      (argpass/owe-all! kb))
    res))

(defn settle-record-edits!
  "Settle what `edit-records!` batches left: build belief over the edited records
  (`reindex` when the index was never built, else `recover` when belief was not), delete
  the stored justifications the rebuild found resting on a record the store does not hold,
  sweep the consequence closure of their conclusions and of `:seeds` as a retraction
  sweeps it, chain each forward rule among `:seeds` over the stored facts, and re-chain
  the antecedents of the deleted rule firings, which a second route may still license.
  Then, unless `:arg-types? false`, `record-arg-types` draws the argument-type mints a
  removal released: a general mint a removed membership or `genl` edge had withheld.

  `opts`: `:seeds`, the union of the batches' `:seeds`; `:arg-types?`, default true;
  `:on-progress`, called with `{:phase :done :total}` as each step begins, in units fixed
  before the phase starts:

    `:reindex`   0 of 1, then the recover's steps;
    `:recover`   the recover's steps (`:step`, `:label`), of 7, and while a step runs,
                 `:sub`, `{:id :label :done :total}` of the loop it is in (`:id` its
                 progress-line keyword), once a second;
    `:sweep`     its steps (`:step` `:unrooted`, `:sweep`, `:settle`, `:chain`,
                 `:rechain`, `:settle-chain`), of 6, the chain's `:derived` and
                 `:pending` beside;
    `:arg-types` 0 of 1, under `:arg-types? true`.

  A throw from `:on-progress` lands at the next phase boundary and is rethrown there; the
  KB is then settled as far as the phases before it, and a second call finishes.

  Under `:arg-types? false` the KB is settled and on disk when this returns, and the pass
  is owed (`arg-types-owed`) whenever an edit or this sweep removed anything:
  `record-arg-types!` then runs it.  The believed sentences are then those the same
  removals and direction changes through `edit!` leave, modulo handles.  Returns
  `{:rebuilt :reindex|:recover|nil :unrooted n :removed-sentexes n :removed-justifications n
  :rules-chained n :rechained n :arg-types {…}}`, or `:arg-types-owed? bool` in place of `:arg-types`.
  docs/storage.md, \"Editing the records of a KB without belief\"."
  ([kb] (settle-record-edits! kb nil))
  ([kb opts]
   (opts/check! opts #{:seeds :arg-types? :on-progress} "settle-record-edits!"
                "A key nothing reads would leave its sweep or its mints undone.")
   (opts/check-values! opts "settle-record-edits!")
   (let [on-progress (:on-progress opts)
         cancel      (volatile! nil)
         report!     (fn [m]
                       (when (and on-progress (nil? @cancel))
                         (try (on-progress m) (catch Throwable t (vreset! cancel t)))))
         boundary!   (fn [] (when-let [t @cancel] (throw t)))
         hz          (kb/write-hazards kb)
         rebuilt     (binding [recovery/*on-recover-step*
                               (when on-progress #(report! (assoc % :phase :recover)))]
                       (cond (:no-index hz)
                             (do (report! {:phase :reindex :done 0 :total 1}) (reindex kb) :reindex)
                             (or (:no-belief hz) (:stale-belief hz))
                             (do (recover kb) :recover)))
         _           (boundary!)
         seeds       (keep #(the-handle % "settle-record-edits!") (:seeds opts))
         swept       (record-edit/sweep! kb seeds (when on-progress report!))
         _           (boundary!)
         arg-types?  (get opts :arg-types? true)
         res         (cond-> (assoc swept :rebuilt rebuilt)
                       arg-types?
                       (assoc :arg-types (do (report! {:phase :arg-types :done 0 :total 1})
                                             (record-arg-types kb))))]
     (if arg-types?
       res
       (do (when (and (nil? (argpass/read-owed kb))
                      (or (seq seeds)
                          (some #(pos? (long (get swept % 0)))
                                [:unrooted :removed-sentexes :removed-justifications])))
             (argpass/owe-all! kb))
           (dur/fsync-registered!)
           (assoc res :arg-types-owed? (some? (argpass/read-owed kb))))))))

(defn write-hazards
  "What makes a write into `kb` wrong, as a map of the hazards that hold:
  `{:no-belief true}` when its belief network was never rebuilt from the records,
  `{:no-index true}` when its index was never rebuilt either, both, `{:stale-belief true}`
  while belief is rebuilt behind an installed image (`:recover? :background`), or `{}`.  The write
  entry points refuse on a non-empty answer (`:unrecovered-kb`), so a caller rendering a
  write form can refuse first.  `recover` retires `:no-belief` and `reindex` retires both.
  A hazard over an empty store reads as absent."
  [kb]
  (kb/write-hazards kb))

(defn rebuild-progress
  "Where the belief rebuild behind `kb`'s installed image (`:recover? :background`) has got
  to, or nil when none runs — the state `write-hazards` reports as `{:stale-belief true}`.
  A rebuild that threw stays reported, with `:failed`, until `recover` rebuilds belief on
  the calling thread; the KB meanwhile answers from the image and refuses writes.

    :step :of :label         the step running now, 1-based (0 before the first), the step
                             count, and the step's phrase, e.g. \"settling belief\"; after
                             a throw, the step the rebuild was in
    :failed                  after a throw: `{:at :class :message}`, when (epoch ms), the
                             exception's class name, and its message
    :started-at :elapsed-ms  when the rebuild began (epoch ms), and how long ago, or how
                             long it ran before the throw
    :image                   the installed image's `:source` digest and `:written-at`, and
                             its `:recover` step timings when the image records them
    :source                  the running build's source digest, which differs from the
                             image's and is why belief is being rebuilt
    :expected-ms :fraction   when the image records its recover: that recover's total
                             milliseconds, and the share of it the steps done so far took

  Each step is also logged at `:info` as it begins."
  [kb]
  (recovery/rebuild-progress kb))

(def ^:private store-state-keys
  "The keys `store-state` answers."
  #{:readable? :network? :believes? :recoverable?})

(defn store-state
  "What `kb`'s record store and belief network hold, as a map of booleans:

    :readable?     one stored record reads back as a sentex (true for an empty store).
                   False for a store written by a build whose record classes this one
                   does not resolve, and every read of such a store answers empty; the
                   map then adds `:thawed-keys`, the keys that record read back with
    :network?      the belief network holds a node for at least one handle
    :believes?     the belief network holds at least one IN node
    :recoverable?  the store holds a premise mark or a justification, which is what
                   `recover` rebuilds belief from

  `ks` names the keys to compute and defaults to all four, so a caller asking one question
  pays for one probe.  A key outside the four is refused (`:unknown-option`).

  A KB loaded without belief has `:network?` false, and so does a KB value holding no
  belief network at all.  `:believes?` false over a non-empty store is a KB whose answers
  are all empty, and `:recoverable?` says which repair applies: `recover` when true, a
  reload when false.

  `:readable?` fetches one record.  The id probes behind `:readable?` and `:recoverable?`
  take constant time on a store implementing `Tallying`, as the in-memory, disk and
  overlay stores do; any other store answers each probe with the first element of its id
  set."
  ([kb] (store-state kb store-state-keys))
  ([kb ks]
   (when-let [bad (seq (remove store-state-keys ks))]
     (throw (ex-info (str "store-state answers " (pr-str (sort store-state-keys))
                          ", not " (pr-str (vec bad)))
                     {:type :unknown-option :mismatch :unknown-key :unknown (vec bad)
                      :options (vec (sort store-state-keys))})))
   (let [rs   (:records kb)
         ;; a KB value holding no belief reads as holding no network: the catalog asks
         ;; this of a `{:records …}` map before any KB is opened over the store
         tms  (some-> (:reasoning kb) deref :tms)
         want (set ks)]
     (cond-> {}
       (want :readable?)
       (merge (let [h   (cap/some-sentex-id rs)
                    r   (when h (p/get-sentex rs h))
                    ok? (or (nil? h) (some? (:sentence r)) (some? (:antecedent r)))]
                (cond-> {:readable? ok?}
                  (not ok?) (assoc :thawed-keys (some-> r keys vec)))))
       (want :network?)
       (assoc :network? (boolean (some-> tms jtms/any-node?)))
       (want :believes?)
       (assoc :believes? (boolean (some-> tms jtms/any-belief?)))
       (want :recoverable?)
       (assoc :recoverable? (boolean (or (cap/some-premise-id rs)
                                         (cap/some-justification-id rs))))))))

(defn clear!
  "Wipe the KB's durable stores — every record and every index entry, and the
  argument-type pass's owed record — the backend-agnostic counterpart to `recover`:
  `recover` rebuilds the in-memory JTMS / taxonomy *from* the stores, this empties the
  stores.  `!` because it destroys stored knowledge irreversibly.

  It does **not** reset the in-memory JTMS / taxonomy, so call it on a freshly-opened
  KB (an empty in-memory state) or immediately before reloading content — the form a
  reset-and-reload uses.  Returns the KB."
  [kb]
  (p/clear-records! (:records kb))
  (p/clear-index! (:index kb))
  ;; a hazard is a claim about the records that were there, and there are none now.  This
  ;; is the one place that knows a wipe happened: `write-hazards` reads emptiness without
  ;; retiring anything, because an importer's declaration arrives while the store is still
  ;; empty and a read that retired it there would release it for the whole load
  (kb/note-hazards! kb {:no-belief false :no-index false})
  ;; the stores moved without going past either per-sentex choke point, so the clock a
  ;; resident derived structure is keyed by has to be bumped by hand here
  (observe/note-change)
  ;; the clock covers the resident *values*, which are rebuilt on the next read
  (some-> (reasoning/qcn kb) (reset! {}))
  ;; ...and the qualitative join baselines, which outlive a clock tick (docs/qcn.md, "The
  ;; network is resident, and the clock is what makes that sound")
  (some-> (reasoning/qcn-joined kb) (reset! {}))
  ;; ...and the refusal record, for the same reason and a stronger one: it is keyed by
  ;; rule handle and retired at the rule's own departure, which a wholesale wipe of the
  ;; stores never reaches.  Every entry names handles this call just deleted.
  (some-> (reasoning/refused kb) (reset! {}))
  ;; ...and the supersession moves waiting for the next settle, for the third form of
  ;; the same reason: every datum they name is a handle this call just deleted
  (some-> (reasoning/supersessions kb) (reset! nil))
  ;; ...and the mint queues, which would be *wrong* rather than merely stale: their
  ;; entries are handles, the wipe resets the handle counter, and a reload would hand
  ;; handle 42 to a new sentex an old entry still names.
  (some-> (reasoning/mint-queues kb) (reset! {}))
  ;; ...and the argument-type pass's owed record, a file beside the stores that names a
  ;; position among the deleted records and a mark the reset counter falls below
  (argpass/clear-owed! kb)
  ;; ...and back to undetermined, not to "recovered".  This is the reset-and-reload
  ;; shape's own call, and what follows it may be an `import-dump` that lands records
  ;; and skips the recover — so the write-side question has to be re-asked over what
  ;; arrives next, rather than answered "no" by a wipe that emptied the store.
  (some-> (:unrecovered kb) (reset! {}))
  kb)

(defn seal
  "Seal `kb`'s operation log (`open-kb`'s `:oplog?`): write the index image and the
  reasoning image, name them in `seal.nippy`, and start the log's next generation, so an
  open after a crash restores from these images and replays only the operations after
  this call (docs/storage.md, \"The operation log\").  Returns `{:sealed true :generation g
  :watermark w :ms t}`.

  Returns `{:sealed false :reason r}` and changes nothing when `r` is `:not-applicable` (no
  log), `:in-operation` (called inside a write, from a change-feed listener),
  `:settle-deferred` (inside `with-deferred-settle`) or `:settle-running`.  A KB whose
  images cannot be written (a registered prover or solver, or a network that does not cover
  the records) answers that reason and marks the log unusable, so the next open rebuilds
  from the records.  A log that stopped on a failed write or fsync refuses with
  `:store-unusable`.  Call it from the thread that writes `kb`."
  [kb]
  (seal/seal! kb))

(defn close!
  "Release a durable KB's directory: flush and close the record store, drop it from the
  durability daemon, and **release the exclusive file lock**.  Returns the KB.

  A `{:backend :disk-log :dir …}` KB takes an exclusive `FileLock` on its directory when it
  opens, and without this the lock is held until the JVM exits — so a long-running
  process could not hand the directory to another process, reopen it elsewhere, or
  release it after a load it no longer needs.  `clear!` is the other half of the pair
  and answers a different question: `clear!` destroys the *content* and leaves the
  store open, this keeps the content and lets go of the store.

  **The stores belong to the directory, not the KB value**: two KBs opened over one
  directory share them, so closing either closes both, and neither may be used
  afterwards.

  On a `fork` this releases the fork's **own** writable directory — the one `{:backend
  :disk-log :dir …}` in its opts named — and never the base's.  A base is mounted read-only
  and shared by every fork taken over it, so it is nobody's fork to close; release it by
  closing the KB it was opened as.

  On a KB with no directory (every in-memory backend, and an ephemeral fork) it releases
  only RAM, so it is safe to call unconditionally in a `finally`.  The KB must not be used
  afterwards; open it again to read the same directory.

  A durable records backend that is not the disk store — the `:sqlite` adapter, which
  holds a JDBC connection rather than a directory — releases its resource here too: any
  record store that is `java.io.Closeable` is closed.  The disk store is torn down by
  `close-dir!` above and is not `Closeable`, so this fires once, for such a backend, and
  never twice.

  **What holding a KB open costs, and what this releases.**  A durable KB holds the
  directory's exclusive lock and its file handles until this runs; an in-memory KB holds
  its records in a process-global space registry keyed by its `:space`, shared with any
  other KB over that space and released by `clear!`, not here.  The exception is a space
  the engine allocated for the KB and handed to no caller — an ephemeral `fork`'s own half,
  a `kb-diff` side read from a path — which this drops.  A **disk-backed KB with a
  derived index** (`:disk-dense`, `:disk-columnar`, `:disk-memory`) also holds that index
  in a RAM registry keyed by the directory; this drops it, so a process opening durable KBs
  in a loop does not keep one derived index per directory it has finished with (the index
  is rebuilt from the records on the next open regardless).  A KB driven through the
  incremental matcher (`rete/track!` or `VAELII_RETE=1`) holds a RAM alpha index too; this
  drops it (`rete/forget-kb!`) for any backend, and that registry keys each KB weakly, so a
  KB dropped without `close!` is reclaimed by GC and its alpha with it — the drop here is
  the prompt release, not the only one.  It also empties the nogood readers' process-wide
  memos (`decide/drop-memos`), which hold the last KB read, so a closed KB's records and
  index are collectable once its caller drops it.

  **The change feed ends here too**: every listener `watch` registered on this KB value is
  dropped, so `watchers` answers empty.  A listener registered on another KB value over
  the same directory is that value's to drop."
  [kb]
  (feed/unregister-all! kb)
  ;; the RAM caches first, and unconditionally: they are dropped for every backend (an
  ;; in-memory KB has no directory to close but can still have been tracked or hold a
  ;; derived index), and they hold only RAM, so releasing them cannot fail the close of the
  ;; durable half below.  The alpha index the incremental matcher held, and the RAM derived
  ;; index a disk-backed KB built (nil unless the index was derived and the records durable).
  (rete/forget-kb! kb)
  (kb/release-index-space! (:index-space kb))
  (kb/release-engine-space! (:engine-space kb))
  (when-let [dir (:dir kb)]
    (disk/close-dir! dir))
  ;; after the directory's close, whose image writer seals a KB that records an operation
  ;; log (`vaelii.impl.seal`) and so still appends to it
  (some-> (:oplog kb) oplog/close-log!)
  (when (instance? java.io.Closeable (:records kb))
    (.close ^java.io.Closeable (:records kb)))
  ;; after the close-time image writes, which read the memos and refill them with this KB
  (decide/drop-memos)
  kb)

(defn import!
  "Read an export dump from `dir` into the (empty) `kb`, and return a summary — the
  inverse of `export!`, which is the only reason this is here: a round trip whose two
  halves are not both public is not a round trip.

  `opts`: `{:belief? true|:stored|false :report-every n :on-progress f :drop-principal?
  bool}`.  With `:belief? true` (the default) the dump lands in the state a restart
  produces — records, justifications and premise marks stored, index rebuilt, belief
  recovered.  With
  `:belief? false` every sentex is stored and indexed but no justification stream is read
  and nothing is recovered: browsable, findable and countable, but not belief-queryable.
  That is the path for a corpus past what an in-RAM JTMS scales to.

  `:belief? :stored` is the middle, and it is what a corpus that cannot afford `recover`
  *today* wants: everything `true` stores is stored — justifications, premise marks,
  provenance, the index — and only the recover is left for later, as its own job over the
  finished store.  For a dump in a **foreign** dialect it is the only mode that keeps them
  at all: the records-only path carries no strength onto a foreign record and marks no
  premise, so a later `recover` over that store believes nothing.

  `:on-progress` is called every `:report-every` frames (default 500000) with
  `{:phase :done :total}`.  A key this fn does not read is refused (`:unknown-option`), as
  at `export!`, and so is an unrecognised `:belief?` value — anything truthy would
  otherwise mean `true`.

  A dump in a foreign dialect needs the reader plugin that declares it
  (`vaelii.impl.foreign`); one this build cannot read is refused by name.

  A dump refused for its own content leaves `kb` as empty as it found it, so the retry
  needs no `clear!`: a handle named twice, a frame naming a class, and a frame no reader
  decodes are refused mid-stream, and the import empties the store before it throws.  A
  callback that throws, a torn stream or a store failure leaves `kb` holding what had
  already landed.

  Provenance lands as the dump wrote it.  `:drop-principal? true` drops each map's
  `:principal`, the key a daemon records from its token table
  ([docs/operations.md](docs/operations.md#the-token-table)); `koinii.deref/pull!` passes it.

  Two counts in the summary are disagreements between the dump and this build, and
  neither stops the load: `:naming` is what got stored under a name `assert` would
  refuse, and `:refused` is what was skipped.  A frame is skipped when it could not be
  **built** at all — a rule whose structure a since-widened check now rejects — and when
  `assert` refuses it and its record would answer wrongly: an open literal, a rule whose
  antecedent functor is a variable, which holds a bare variable as a literal, a `do/`
  imperative or an `or` no expansion removes, or which is not range-restricted, a special
  predicate's declaration its well-formedness check refuses (the checks that read stored
  content excepted), a non-finite measure, an `exceptWhen` over a fact, a sentex in a query
  context.  A skipped frame
  goes
  with whatever rests on it, and is reported; `:sentexes` and `:frames` differ by those,
  by `:collapsed`, and by the further forms `:expanded` counts.  An `(ist Ctx S)` frame is
  stored as S in Ctx, which is what `assert` stores.

  `true` and `:stored` land two frames with one canonical form on one handle at the
  stronger strength, and count the second in `:collapsed`.  `false` stores one record per
  frame, so such a pair lands as two records.  A rule frame `assert` expands (an `or`
  antecedent, an `and` consequent) is the exception on every path: it is stored as the
  rules `assert` stores, one per form, and counted in `:expanded` as `{:frames n :records
  n}`.  A dump `export!` wrote holds no such pair;
  one reaches the import from a hand-edited dump, another dialect's or another build's, or
  as an `(ist Ctx S)` frame beside S in Ctx ([docs/naming.md](docs/naming.md))."
  ([kb dir] (import! kb dir {}))
  ([kb dir opts] (io-import/import-dump kb dir opts)))

(defn read-manifest
  "The EDN manifest in file `f` — a dump's or a store's `meta.edn` / `format.edn` — read
  under a byte bound.  Refused as `:manifest-too-large` past the bound, and as
  `:malformed-manifest` for content the EDN reader cannot parse, so a caller probing a
  directory it knows nothing about reads a bounded number of bytes and can tell
  \"not a KB\" from \"a broken one\"."
  [f]
  (io-import/read-edn-manifest f))

(defn store-backend
  "The `:backend` to pass `open-kb` for the store in `dir`, read off its files, or nil when
  `dir` holds no store: `:disk-snapshot` for a mapped index image, `:disk-log` for a
  write-ahead-logged index, `:disk-columnar` for records with no index file, `:sqlite` for
  the SQLite adapter's file, and `:pg-disk-log` or `:pg-snapshot` for a local index or its
  images whose records are on a server (the open reads that server off the directory's
  records identity when no `:pg` is given).  An open under the wrong backend throws
  nothing and returns an empty KB, so a caller opening a directory it did not write reads
  the backend here rather than naming one."
  [dir]
  (disk/store-backend dir))

(defn load-foreign!
  "Load the directory at `path` into `kb` through the foreign reader plugin registered
  for `kind` (`:cyc-corpus`, for one), passing `opts` to it, and return what the reader
  returns.  A build with no plugin for `kind`, or one whose reader loads no directory, is
  refused by name (`:no-foreign-reader`).  A foreign **dump** needs none of this —
  `import!` reads one through the same plugin.  [docs/foreign.md](docs/foreign.md)"
  [kb kind path opts]
  ((foreign/directory-loader! kind) kb path opts))

(defn export!
  "Write `kb` out as a portable **export dump** in `dir` and return a summary:

      {:variant :records :sentexes n :justifications n :provenance n
       :index-entries n :bytes n :elapsed-ms n :dir \"…\"}

  A dump is a directory of **field-map frames** — no frame carries a class name — so it
  survives a backend change, an index-representation change, and a record class rename,
  none of which the durable store's own directory survives.  What it holds is what the
  record store holds, because everything else is derived: the index is a cache
  (`reindex`), belief and the taxonomy are recomputed (`recover`).  Read back with
  `import!`.

  `opts`: `{:variant :records|:records+index :compression :gzip|:xz|:none :chunk-size n
  :provenance? bool :belief? bool :on-progress f}` (defaults `:records`, `:gzip`, 10000,
  true, true).  `:belief? true` also writes the KB's reasoning image, which an import of the
  same records installs in place of `recover` ([docs/storage.md](docs/storage.md)).
  `:records+index` writes the index too, as a cache a reader replays only if it can prove
  it describes the records beside it.  `:provenance? false` drops the per-handle
  annotation — an open map with no size bound, measured at 57% of one large imported
  KB's dump — which the importer already treats as optional, so what is left is a
  complete KB rather than a partial one.  `:on-progress` is called with `{:phase :done :total}` at each chunk
  boundary; a callback that **throws** is how a caller cancels, which leaves a directory
  with no `meta.edn` — and so not a loadable dump.  A key this fn does not read is
  refused (`:unknown-option`): each one changes what the dump *is*, so a misspelt key
  writes a dump other than the one asked for under a summary that looks right.

  `dir` must be absent or empty: a dump merged into another dump is not a dump.  Export
  from a KB nobody is writing — the walk fetches record by record, and there is no
  snapshot to walk instead.

  `!` although it destroys nothing here: it writes a directory tree outside the process,
  which is not something the KB can take back."
  ([kb dir] (export/export! kb dir {}))
  ([kb dir opts] (export/export! kb dir opts)))

;; ---- the text KB: a KB as the format its ontology is authored in ---------
;;
;; A dump is a KB's **state** and text is a KB's **content**, so the two are different
;; entry points rather than one entry point with a `:format` flag.  Nothing `export!` takes means
;; anything here — there are no frames to chunk, no compression to pick, no provenance
;; and no index — and the way back is not `import!` but `assert`, since a text KB is
;; **re-asserted** rather than restored.  One entry point whose options half applied and whose
;; inverse changed with a flag would be two entry points wearing one name.

(defn export-text!
  "Write `kb`'s premises and inert sentexes as a **text KB** — one `<Context>.txt` per
  context, in exactly the format the shipped ontology is authored in and `load-text!`
  reads — and return a summary:

      {:contexts n :sentences n :skipped n :files [\"CxUniverse.txt\" …]
       :bytes n :elapsed-ms n :dir \"…\"}

  `opts` narrows what is written: `{:context C}` for that one context's file, `{:ancestor-set C}`
  for `C` and every context it **sees** — the slice a reload needs for `C`'s own content
  to mean what it meant.  Neither, and every context holding a premise or an inert sentex
  is written.  A key this fn does not read is refused (`:unknown-option`), since a
  misspelt narrowing writes the whole KB under a summary that looks right.  `dir` must be
  absent or empty.

  **No derived sentex.**  A derived sentex is what the engine concluded, so writing it would
  store as a premise what the KB believes as a conclusion, and the reload would hold it
  against the retraction of everything it followed from.  Chaining puts it back, which is
  the point.  Each premise keeps its `:strength` — `:monotonic` as a `(set/monotonic S)`
  wrapper, `:default` as nothing, the entry point's own fallback — and each rule its
  `set/*Rule` / `set/defaultRule` wrappers and its `exceptWhen`, so a reload yields the
  same canonical sentexes at the same strengths and the same beliefs.  An inert sentex
  (`assert-inert`) is written as `(set/inert S)`, which `load-text!` stores inert again.
  Telling an inert sentex from a derived one reads the TMS, so a KB whose belief is not
  built refuses the export (`:unrecovered-kb`) when it stores a sentex that is neither.

  **Content order, never handle order**, and no timestamp or writer in the text: two KBs
  holding the same knowledge write byte-identical files whatever order they were built in
  (docs/defenses.md).

  `:skipped` counts the records there is no text for — an `(except H)` or another meta
  naming a sentex **by handle**, which is a fact about this store and means something
  else, or nothing, in the KB that reads the file back.  For those, and for handle
  identity in general, the entry point is `export!`.

  `!` although it destroys nothing here: it writes a directory tree outside the process,
  which is not something the KB can take back.  docs/kbs.md."
  ([kb dir] (text/write-kb! kb dir {}))
  ([kb dir opts] (text/write-kb! kb dir (or opts {}))))

(defn load-text!
  "Read a **text KB** into `kb` — a directory of `Cx….txt` files, or one such file — and
  return a summary:

      {:contexts n :sentences n :files [\"CxUniverse.txt\" …] :elapsed-ms n :path \"…\"}

  The inverse of `export-text!`, and the entry point `lein cli load` is.  **The file name is the
  context**: `CxKinship.txt` asserts into `CxKinship`, and a sentence for another context
  says so with `(ist Cx S)` as it would anywhere else.  Forms are read with
  `clojure.edn`, so a KB file is data and can never run code, and `;;` comments and blank
  lines added no work.

  Every form is asserted through the ordinary write path — same checks, same
  canonicalization, same chaining — so this is `assert` over a file rather than a restore,
  and the KB it lands in need not be empty.  Two forms are not sentences and are peeled
  first: `(set/monotonic S)` asserts `S` known-true, and `(set/inert S)` stores `S`
  through `assert-inert`, which refuses a rule.  `:default` is written as nothing, being
  the entry point's own fallback.

  A whole directory is **one order-insensitive pass**: a form refused because content
  further down has not arrived yet is retried, since file names sort alphabetically and
  one context's content can rest on another's.  A form that survives a round which changed
  nothing is re-asserted without the catch, so a genuinely ill-formed one throws —
  carrying the error it has once everything that could have helped it is stored.  The
  **context topology goes in first** whatever order it arrived in: a firing with no
  placement context is *dropped* rather than refused, so a `genlCx` edge arriving after
  the fact it would have placed is the one thing retrying cannot fix.

  `!` because it writes knowledge into the KB.  docs/kbs.md."
  [kb source]
  (check-writable! kb "load-text!")
  (let [t0 (System/nanoTime)
        {:keys [files entries path]} (text/entries source)
        n  (text/load-entries! (fn [sentence context o] (assert kb sentence context (or o {})))
                               (fn [sentence context] (assert-inert kb sentence context))
                               entries)]
    {:contexts   (count (distinct (map second entries)))
     :sentences  n
     :files      files
     :elapsed-ms (long (/ (- (System/nanoTime) t0) 1000000))
     :path       path}))

;; ---- kb-diff: what two KBs disagree about --------------------------------
;; Two KBs holding the same knowledge are equal *as knowledge* and share not one handle:
;; handles are allocated in assertion order, so a re-load renumbers everything and a diff
;; keyed on one would report a KB as wholly changed for having been loaded twice.  The key
;; here is therefore content — the canonical sentence, its context and its strength — which
;; is the same key `assert` dedups on, so two KBs told the same thing in any order compare
;; equal (docs/canonicalization.md, docs/defenses.md).

(defn- diff-side
  "One side of a `kb-diff` as a KB.  A **string** is a path to a text KB — a directory of
  `Cx….txt` files or one such file — read into a fresh in-RAM KB on an engine space
  (`mem/engine-space`), so two paths never land in one store, and conj'd onto the
  volatile `opened` for `kb-diff` to close; anything else is already a KB."
  [opened x]
  (if (string? x)
    (let [k (open-kb {:backend :memory :space (mem/engine-space :diff)})]
      (vswap! opened conj k)
      (load-text! k x)
      k)
    x))

(defn- diff-rows
  "Every stored sentex of `kb` as a diff row, lazily — one record fetched per step, since
  the larger side is walked rather than indexed.  `:premise?` separates what somebody
  asserted from what the engine concluded, and both are compared: a conclusion that stopped
  following is a difference between two KBs even though nobody wrote it either time."
  [kb]
  (keep (fn [h]
          (when-let [sx (sentex kb h)]
            {:sentence  (sx/sentence-of sx)
             :context   (:context sx)
             :strength  (:strength sx)
             :premise?  (premise? kb h)
             :believed? (believed? kb h (:context sx))}))
        (handles kb)))

(defn- diff-key
  "The content address a row is matched on: the canonical sentence, the context it holds
  in, and the class it was asserted at.  Strength is part of the key rather than a field
  compared afterwards because a fact restated `:monotonic` is a different claim, not the
  same one differently believed."
  [r]
  [(:sentence r) (:context r) (:strength r)])

(defn- paired-moves
  "Pair the leftovers of the two sides into moves: the same sentence at the same strength,
  in a different context.  Pairs are formed in **context order** on each side, so a
  sentence that moved from two contexts to two others pairs the same way whichever KB was
  the larger one and whatever order either was built in.  A move that also changed the
  strength is not one — it reports as a removal and an addition, which is what it is."
  [a-left b-left]
  (let [group  (fn [rs] (group-by (juxt :sentence :strength) rs))
        ga     (group a-left)
        gb     (group b-left)
        order  #(nm/sort-by-content-key :context %)
        shared (nm/sort-by-content-key identity (filter (set (keys ga)) (keys gb)))]
    (reduce
     (fn [[moves ra rb] k]
       (let [as (order (ga k))
             bs (order (gb k))
             n  (min (count as) (count bs))]
         [(into moves (map (fn [x y] {:sentence (:sentence x) :from (:context x)
                                      :to (:context y) :strength (:strength x)
                                      :premise? (:premise? x)})
                           (take n as) (take n bs)))
          (into ra (drop n as))
          (into rb (drop n bs))]))
     [[] (vec (mapcat val (apply dissoc ga shared))) (vec (mapcat val (apply dissoc gb shared)))]
     shared)))

(defn- diff-sides
  "`kb-diff` over two open KBs."
  [ka kbb]
  (let [a-first? (<= (sentex-count ka) (sentex-count kbb))
        [small large] (if a-first? [ka kbb] [kbb ka])
        idx  (persistent!
              (reduce (fn [m r] (assoc! m (diff-key r) r)) (transient {}) (diff-rows small)))
        step (fn [[matched belief left] r]
               (if-let [s (idx (diff-key r))]
                 [(conj! matched (diff-key r))
                  (if (= (:believed? s) (:believed? r))
                    belief
                    (conj belief (-> (dissoc r :believed?)
                                     (assoc :believed-in-a (:believed? (if a-first? s r))
                                            :believed-in-b (:believed? (if a-first? r s))))))
                  left]
                 [matched belief (conj left r)]))
        [matched belief large-left] (reduce step [(transient #{}) [] []] (diff-rows large))
        matched     (persistent! matched)
        small-left  (into [] (remove #(matched (diff-key %))) (vals idx))
        [a-left b-left] (if a-first? [small-left large-left] [large-left small-left])
        [moved a-gone b-new] (paired-moves a-left b-left)
        by-content  #(nm/sort-by-content-key (juxt :sentence :context) %)]
    {:added          (by-content b-new)
     :removed        (by-content a-gone)
     :moved          (nm/sort-by-content-key (juxt :sentence :from :to) moved)
     :belief-changed (by-content belief)}))

(defn kb-diff
  "What two KBs disagree about, as content: `{:added :removed :moved :belief-changed}`.

  Each side is a KB, or a **string** naming a text KB — a directory of `Cx….txt` files or
  one such file — which is read into an in-RAM KB of its own (`load-text!`).  So
  `(kb-diff kb \"exports/yesterday\")` compares a live KB with a text export, and
  `lein cli diff <a> <b>` compares two exports.

  | key | holds |
  |---|---|
  | `:added` | in `b` and not in `a` |
  | `:removed` | in `a` and not in `b` |
  | `:moved` | the same sentence at the same strength, in a different context |
  | `:belief-changed` | the same sentex on both sides, believed on one and not the other |

  An `:added` / `:removed` row is `{:sentence :context :strength :premise? :believed?}`, a
  `:belief-changed` row carries `:believed-in-a` / `:believed-in-b` instead of `:believed?`,
  and a `:moved` row reads `{:sentence :from :to :strength :premise?}`.

  **Keyed on content, never on a handle.**  The address is the sentence *as stored* — which
  is `canonical-sentex`'s form, since canonicalization happens at the write entry point — plus the
  context and the strength.  Handles are allocated in assertion order, so a diff keyed on
  one would report a KB reloaded from its own export as wholly changed; this reports it as
  identical.  Every list is ordered by content for the same reason, so two runs of one
  comparison print the same thing and a `diff` of two runs means something.

  **Premises and derived sentexes alike**, told apart by `:premise?` on every row: a
  conclusion that stopped following from its premises is a difference between two KBs even
  though nobody asserted it either time, and a reader wanting only what was *written* filters
  on the flag.

  **What it does not compare**: justifications (which rule concluded a derived sentex, and
  from what), provenance (creator, timestamps, application fields), and handles — the three
  things that are facts about how a KB was *built* rather than about what it holds.  Two KBs
  can therefore diff empty and still differ in every one of them; `why` is the read for the
  first, `provenance` for the second, and the third is deliberately not a question.

  O(|a| + |b|): the **smaller** side is indexed by content key and the larger is walked as a
  lazy seq, one record fetched per step.  The four lists are realized, being ordered.

  A KB read from a string side is closed before this returns, which drops its space; a KB
  the caller passed stays open."
  [a b]
  (let [opened (volatile! [])]
    (try
      (diff-sides (diff-side opened a) (diff-side opened b))
      (finally (run! close! @opened)))))

;; ---- four-valued epistemic status --------------------------------------
;; `argue` reads both a sentence and its explicit negation and reports where belief
;; stands between them, with a small argumentation stub for the both-provable case.  It
;; is a read built entirely on `ask`/`query`/`why`, so it lives here on the public
;; surface rather than under `impl` — a caller (a coordination layer adjudicating a
;; dispute, a UI coloring a claim) wants the verdict without reconstructing it.

(defn- argue-results
  "Query results for `goal` in `context` — a seq of binding maps (an empty map for a
  ground goal), or nil if not provable.  Rules fire only with `:max-depth`.  A ground
  goal has one answer at most, so its search stops at the first."
  [kb goal context opts]
  (seq (if (:max-depth opts)
         (query-capped kb goal context opts
                       (when-not (sx/some-symbol? sx/variable? goal) 1))
         (ask kb goal context))))

(defn- argue-justification
  "The `why` graph for `sentence` in `context` when it is stored and believed, else nil."
  [kb sentence context]
  (when-let [h (handle-of kb sentence context)]
    (when (in? kb h)
      (why kb h))))

(defn- argue-derivation
  "The search's own derivation of `goal` in `context` — `query`'s `{:proof? true}` tree —
  or nil.  The complement of `argue-justification`: that one reads the JTMS and explains a
  **stored** belief, this one reads the search and explains an **ephemeral** one, which is
  the only explanation a side a rule derived has.  Different reads from different places,
  so `argue` reports them under different keys rather than as two shapes of one.

  Three conditions, each of them a way the tree would otherwise be a lie:

  - a **positive** depth.  At 0 no rule expanded and `query` takes the registry arm, which
    has no proof to return — the extra search would cost a query and find nothing.
  - a **ground** goal.  A pattern answers once per binding and `query` returns one tree per
    answer, so a single tree taken off the front explains one answer the caller cannot
    identify, over the canonical variables rather than over its bindings.
  - `results` are reused when the caller already asked for proofs, since the answers then
    carry their own and re-running the search would only find them again.

  A goal a *prover* answered rather than a rule reaches here too, and its tree is the one
  node the search took (`:via :leaf`): true, and as much as the search knows."
  [kb goal context opts results]
  (let [d (:max-depth opts)]
    (when (and (nat-int? d)
               (pos? (long d))
               (not (sx/some-symbol? sx/variable? goal)))
      (if (:proof? opts)
        (:proof (first results))
        (:proof (first (query-capped kb goal context (assoc opts :proof? true) 1)))))))

(defn- argue-defeat-class
  "The JTMS defeat-class (`:monotonic` / `:default`) of `sentence` in `context`, or nil."
  [kb sentence context]
  (let [w (argue-justification kb sentence context)]
    (get-in w [:nodes (:root w) :defeat-class])))

(defn- argue-resolve-contradiction
  "Argumentation stub for the both-provable case: a `:monotonic` justification beats a
  `:default` one.  Returns `:true` if the positive side wins, `:false` if the negative
  side wins, or nil if the clash cannot be resolved this way (leaving `:contradiction`).
  Monotonic-vs-default is the whole of it: specificity, recency, authority and
  user-defined preference orderings decide nothing here, so a pair those two classes
  cannot separate stays the `:contradiction` the engine represents."
  [kb asent context]
  (let [pos (argue-defeat-class kb asent context)
        neg (argue-defeat-class kb (list 'not asent) context)]
    (cond
      (and (= pos :monotonic) (= neg :default)) :true
      (and (= pos :default) (= neg :monotonic)) :false
      :else nil)))

(defn argue
  "Four-valued epistemic status of a ground assertion.  Queries both `asent` and its
  explicit negation `(not asent)` and returns a map:

      {:verdict     :true | :false | :unknown | :contradiction
       :for         <results for asent, when provable>
       :against     <results for (not asent), when provable>
       :for-why     <`why`'s graph for asent, when stored and believed>
       :against-why <`why`'s graph for (not asent), when stored and believed>
       :for-derivation     <the search's proof tree, when a rule answered instead>
       :against-derivation <the same, for (not asent)>}

  **Two kinds of explanation, under two keys.**  `:for-why` is `why`'s JTMS graph and
  explains a *stored* belief; `:for-derivation` is `query`'s `{:proof? true}` tree and
  explains an *ephemeral* one, which is the only explanation a side a rule derived has.
  They read differently — `:goal` / `:via` / `:because` against `:root` / `:nodes` —
  and a side carries at most one of them, so a caller reads
  whichever key is there rather than discriminating inside a single key.  A derivation
  needs a positive depth and a ground `asent`; `argue-derivation` says why.

  Without opts it uses `ask` (ground facts + prover registry, no rule expansion);
  callers who want rules to fire MUST pass `{:max-depth N}` explicitly — a silent
  default depth would turn a derivable fact into a false `:unknown`.

  `opts` is `query`'s key set (`query-opt-keys`) and a key off it is refused
  (`:unknown-option`), checked **here** rather than downstream: the branch below reaches
  `query` only when `:max-depth` is present, so a misspelt depth that never reached the
  key check would take the `ask` arm and answer the very false `:unknown` the paragraph
  above says must not happen.

  When both sides are provable the verdict is `:contradiction` unless the argumentation
  stub resolves it: a `:monotonic` justification wins over a `:default` one (the engine
  itself leaves both standing — paraconsistent tolerance, docs/nmtms.md)."
  ([kb asent context] (argue kb asent context nil))
  ([kb asent context opts]
   (opts/check! opts query-opt-keys "argue"
                (str "An option nothing reads takes the default in silence, which here is"
                     " the no-rule-expansion read — a misspelt depth answers :unknown for"
                     " a sentence a rule derives."))
   (let [neg       (list 'not asent)
         for-r     (argue-results kb asent context opts)
         against-r (argue-results kb neg context opts)
         pos?      (boolean (seq for-r))
         neg?      (boolean (seq against-r))
         ;; the JTMS's answer: a stored, believed side only
         for-j     (argue-justification kb asent context)
         against-j (argue-justification kb neg context)
         ;; and the search's, for a side a rule answered rather than the store.  A
         ;; fallback rather than a second opinion: where the JTMS has a justification it
         ;; is the better answer, and asking for a tree nobody reads costs a whole query
         for-d     (when (and pos? (not for-j))
                     (argue-derivation kb asent context opts for-r))
         against-d (when (and neg? (not against-j))
                     (argue-derivation kb neg context opts against-r))
         base      (cond-> {}
                     pos?      (assoc :for for-r)
                     neg?      (assoc :against against-r)
                     for-j     (assoc :for-why for-j)
                     against-j (assoc :against-why against-j)
                     for-d     (assoc :for-derivation for-d)
                     against-d (assoc :against-derivation against-d))]
     (cond
       (and pos? (not neg?)) (assoc base :verdict :true)
       (and neg? (not pos?)) (assoc base :verdict :false)
       (and (not pos?) (not neg?)) (assoc base :verdict :unknown)
       :else (if-let [resolved (argue-resolve-contradiction kb asent context)]
               (assoc base :verdict resolved)
               (assoc base :verdict :contradiction))))))

;; ---- the operation log ----------------------------------------------------
;; Every public write entry point above is routed through `vaelii.impl.oplog/run-op`, so a
;; KB with an operation log records each outermost write as the call that made it.  The
;; routing wraps the vars rather than each body: an entry point added above and missing
;; from `write-ops` is a write the log does not record.

(defn- op-inputs
  "What a frame records beyond an operation's arguments: the clock `:created` is read
  from, the creator, and the dynamic bindings that change what a write stores.  An
  `abduce` also records the token its scratch context is named by."
  [op]
  (cond-> {:clock                (*clock*)
           :creator              *creator*
           :bulk-load?           *bulk-load?*
           :write-unrecovered?   *write-unrecovered?*
           :defer-settle?        *defer-settle?*
           :defer-depths?        tax/*defer-depths?*
           :assertive-arg-types? argument/*assertive-arg-types?*
           :sweep?               settle/*sweep?*}
    (= :abduce op) (assoc :token (abduce/new-token))))

(defn- with-op-inputs
  "Run `thunk` with the bindings `inputs` records, or under the bindings in force when
  `inputs` is nil — which is how a write nested inside a recorded operation runs."
  [inputs thunk]
  (if (nil? inputs)
    (thunk)
    (binding [*clock*                         (constantly (:clock inputs))
              *creator*                       (:creator inputs)
              *bulk-load?*                    (:bulk-load? inputs)
              *write-unrecovered?*            (:write-unrecovered? inputs)
              *defer-settle?*                 (:defer-settle? inputs)
              tax/*defer-depths?*             (:defer-depths? inputs)
              argument/*assertive-arg-types?*   (:assertive-arg-types? inputs)
              settle/*sweep?*                 (:sweep? inputs)
              abduce/*token*                  (:token inputs)]
      (thunk))))

(defn- unbounded-args
  "`args` with the caller's bound (`:max-ms`, `:stop?`, `:progress-every-ms`) taken out of
  every option map: a logged write completed, so its replay takes no clock."
  [args]
  (mapv #(if (map? %) (dissoc % :max-ms :stop? :progress-every-ms) %) args))

(defn- logged
  "Write entry point `g`, routed through the operation log as `op` of `class` and counted
  as a write in flight (`dur/call-as-write`), which a shutdown waits for.  A KB with no log
  retires its directory's seal (`seal/retire-unlogged!`) and calls `g` directly.  A write
  a shutdown or the caller's bound stopped (`:shutdown-abort`, `:interrupted`) marks the
  log unusable: its frame describes a write that did not complete as logged.  The frame
  holds `args` without the caller's bound (`unbounded-args`), so a replay runs the write
  to its end."
  [op class g]
  (fn [kb & args]
    (dur/call-as-write
     op
     (fn []
       (if (nil? (:oplog kb))
         (do (seal/retire-unlogged! kb)
             (apply g kb args))
         (try
           (oplog/run-op kb op class (unbounded-args args) #(op-inputs op)
                         (fn [inputs] (with-op-inputs inputs #(apply g kb args))))
           (catch clojure.lang.ExceptionInfo e
             (when (and (#{:shutdown-abort :interrupted} (:type (ex-data e)))
                        (not oplog/*in-op?*))
               (oplog/mark-unusable! (:oplog kb) [(:type (ex-data e)) op]))
             (throw e))))))))

(def ^:private write-ops
  "Every public write entry point, as `name -> [op class]`.  The classes are
  `vaelii.impl.oplog`'s: `:replay` is recorded, `:seal` and `:config` mark the log
  unusable.

  Keywords, not vars, for `read-ops`' reason: the source identity walks every symbol of a
  top-level form that defines no var, so a var here would put every write entry point
  into the digest, and an edit to `import!` would discard every reasoning image.  The
  writes that derive belief in a session are roots of the digest by name
  (`vaelii.impl.source-identity/roots`, every `:replay` op here).  A `:seal` write's
  whole effect is the records it leaves, which the image's records fingerprint covers."
  {:assert                   [:assert :replay]
   :try-assert               [:try-assert :replay]
   :assert-rule              [:assert-rule :replay]
   :assert-many              [:assert-many :replay]
   :bulk-assert-facts!       [:bulk-assert-facts :replay]
   :assert-inert             [:assert-inert :replay]
   :add-provenance           [:add-provenance :replay]
   :forward-chain            [:forward-chain :replay]
   :record-arg-types         [:record-arg-types :replay]
   :record-arg-types!        [:record-arg-types-resumable :seal]
   :release-withheld!        [:release-withheld :replay]
   :register-modal-predicate [:register-modal-predicate :replay]
   :retract!                 [:retract :replay]
   :remove-unsupported!      [:remove-unsupported :replay]
   :mark-inert!              [:mark-inert :replay]
   :edit-records!            [:edit-records :seal]
   :settle-record-edits!     [:settle-record-edits :seal]
   :edit!                    [:edit :replay]
   :edit-with-consequences!  [:edit-with-consequences :replay]
   :preview                  [:preview :replay]
   :abduce                   [:abduce :replay]
   :abduce-discard!          [:abduce-discard :replay]
   :clear-violations!        [:clear-violations :replay]
   :import!                  [:import :seal]
   :clear!                   [:clear :seal]
   :recover                  [:recover :seal]
   :reindex                  [:reindex :seal]
   :load-text!               [:load-text :seal]
   :set-solver               [:set-solver :config]
   :add-prover               [:add-prover :config]
   :add-evaluatable          [:add-evaluatable :config]
   :add-reasoner             [:add-reasoner :config]})

(defn- op-var
  "The var of `vaelii.core` a `write-ops` or `read-ops` key names."
  [k]
  (ns-resolve 'vaelii.core (symbol (name k))))

(doseq [[k [op class]] write-ops]
  (alter-var-root (op-var k) (fn [g] (logged op class g))))

#_{:clj-kondo/ignore [:unused-private-var]}
(def ^:private replay-dispatch
  "Operation name -> the function `oplog/replay!` runs a frame of it through, read by
  `wiring/replay-op`: each operation's entry point, plus the closing settle of a
  `with-deferred-settle` batch, which is recorded without an entry point of its own.  A
  frame naming `:stamp-inert` runs through `mark-inert!`: an `ops.log` a development build
  wrote holds `:mark-inert` under that keyword."
  (assoc (into {} (map (fn [[k [op _]]] [op (op-var k)])) write-ops)
         :stamp-inert #'mark-inert!
         :settle (fn [kb]
                   (oplog/run-op kb :settle :replay [] (constantly nil)
                                 (fn [in] (closing-settle kb in))))))

;; ---- reads during a background rebuild's install ----------------------------
;; A KB opened with `:recover? :background` answers from an earlier build's reasoning image
;; while belief is rebuilt beside it, and the install then replaces the KB's `Reasoning` value
;; with one `vreset!` (`vaelii.impl.recovery`).  Every read entry point in `read-ops` runs
;; against `kb/read-copy`, which, while the install is pending, is a copy of the KB holding
;; the belief the read began with.  A public read therefore reads the image's belief or the
;; rebuilt belief whole, even when the install lands while it runs, and a lazy sequence it
;; returns reads the same belief when it is realized.  A KB with no install pending is passed
;; through unchanged after one atom read.

(defmacro ^:private read-copy-fn
  "A fn calling `g` with its own arguments, the first replaced by `kb/read-copy` of it.  Up
  to five arguments after the KB, `g` is called directly; beyond that, through `apply`."
  [g]
  (let [kb    (gensym "kb")
        fixed (for [n (range 6) :let [args (vec (repeatedly n #(gensym "a")))]]
                `([~kb ~@args] (~g (kb/read-copy ~kb) ~@args)))
        five  (vec (repeatedly 5 #(gensym "a")))
        more  (gensym "more")]
    `(fn ~@fixed
       ([~kb ~@five & ~more] (apply ~g (kb/read-copy ~kb) ~@five ~more)))))

(defn- on-read-copy
  "Read entry point `g`, run against `kb/read-copy` of its KB."
  [g]
  (read-copy-fn g))

(def ^:private read-ops
  "The names of every public read entry point whose first argument is a KB and that reads
  its belief, its derived state or its stores.  `background_rebuild_test` fails on a public
  fn taking a KB first that is in none of this set, `write-ops` and the test's list of
  the rest.

  Keywords, not vars.  The source identity (`vaelii.impl.source-identity`) walks every
  symbol of a top-level form that defines no var, so a var here would put every read
  into the digest a reasoning image is written with, and an edit to `why` would discard
  every image.  A read that recover does call is reached through that call's own symbol."
  #{:all-functional-at-instant-violations :all-specified-violations :argue :ask
    :ask-within :ask? :belief-status :believed :believed? :blocked-justifications
    :canonical-sentex :chain-report :chain-stats :check :check-edit :common-genls :common-specs
    :compare-tacticians :conflicts :context-down :context-up :contexts :contexts-of
    :contradictions :count-in-context :count-with-arg :count-with-functor
    :defeat-class :dependent-justifications :deprecated? :describe
    :direct-genls :direct-specs :disjoint-metatypes :disjoint? :disjointness-audit :equiv-class :escalate
    :exists-violations :filed-violations
    :explain-levels :export! :export-text! :exposed-clashes :find-sentexes
    :find-sentexes-all :find-terms :functional-at-instant-violations :genl? :genls
    :handle-of :handles :has-prop? :in? :inverse-of :isa? :ist :justification
    :justification-verdicts
    :kb-integrity :kb-quality :last-program :lookup :max-common-specs :max-context-children
    :max-specs :metatype-members :min-common-genls :min-context-parents :min-genls
    :owed-releases :arg-types-owed :covers-of :separating-covers
    :possible-relations
    :premise? :props :provable? :prove :prove-within :provenance
    :qualitative-network :qualitative-scenario :qualitative-scenarios :query
    :query-plan :query-status :query? :relation? :relation-arity :representative :same-class?
    :search-tree
    :sees? :sentex :sentex-count :sentexes-in-context :sentexes-matching
    :sentexes-naming :sentexes-with-arg :sentexes-with-functor :settle-stats
    :specified-violations
    :stored-first-args
    :specs :store-state :subsumption-status :subsumption-statuses
    :supporting-justifications :term-count :term-expression :terms :types :types-of
    :unsupported :violations :vocabulary-audit :why :why-not})

(doseq [op read-ops]
  (alter-var-root (op-var op) on-read-copy))

(defn -main
  "`lein run` — open a KB on the configured stores, say which ones answered, and
  exit.  A smoke test for the build rather than a way to use the engine: nothing is
  loaded and nothing is served, so the process ends where it started.  `lein browser`
  is the one to work in, `lein cli` runs a single command, and `lein run -m
  vaelii.web` serves the browser (docs/operations.md)."
  [& _]
  (let [kb (open-kb)]
    (trove/log! {:level :info :id ::banner
                 :msg  "Vaelii — contextualized common-sense knowledge base."
                 :data {:record-store (type (:records kb)) :index-store (type (:index kb))}})
    (trove/log! {:level :info :id ::repl
                 :msg  "Start a REPL with `lein repl` (loads namespace vaelii.core)."})))
