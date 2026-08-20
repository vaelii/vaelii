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
  signpost, not the roster — docs/api.md is that, and its \"Choosing a query
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
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches-impl]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.context-nat :as context-nat]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.belief-snapshot :as belief-snap]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.imperative :as imperative]
            [vaelii.impl.inference :as inference]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.levels :as lvl]
            [vaelii.impl.logging :as logging]
            [vaelii.impl.modal :as modal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.quality :as quality]
            [vaelii.impl.quasiquote :as quasiquote]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.scenario :as scenario]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.skolem :as skolem]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.violations :as violations]
            [vaelii.impl.vocabulary :as vocab]
            [vaelii.impl.wiring :as wiring :refer [*defer-settle?*]])
  (:gen-class))

;; recover and reindex are defined at the bottom of this namespace (they rebuild
;; through everything above them), and open-kb's :recover? :auto needs both — a
;; genuine forward reference: construction sits below the whole engine stack
;; (vaelii.impl.kb), so the two functions are injected rather than required.
(declare recover reindex)

(defn open-kb
  "Construct a KB.  Every option is optional; `(open-kb {})` is records and index in RAM.

  | opt | what it picks | default |
  |---|---|---|
  | `:backend` | a records×index pair, spelled `<records>-<index>` | `:memory` |
  | `:records` / `:index` | one axis of that pair on its own | from `:backend` |
  | `:space` | which in-RAM stores this KB shares | `0` |
  | `:dir` | the directory a `:disk` half lives in | derived from the space |
  | `:base` / `:overlay` | the two halves of an `:overlay` fork | — |
  | `:tms` | `:dense` or `:reference` truth-maintenance representation | `:dense` |
  | `:naming` | `:strict` / `:warn` / `:off` — what the front door does with a name | `:strict` |
  | `:constraints` | `:refuse` / `:arbitrate` — what a definitional clash does | the process default |
  | `:recover?` | `:auto` (or `true`) / `:warn` / `false` — what a non-empty store gets | `:auto` |

  The seven legal backends and why the eighth is refused: docs/storage.md.  The naming
  policy and what no setting moves: docs/naming.md.  The constraint policies and when
  each is the one to want: docs/exceptions.md.  `fork` is the ergonomic spelling of
  `:overlay` and takes its base from a live KB; the raw form takes `:base` opts instead,
  which is what mounts a base this process has no KB open over.

  **An option this fn does not read is refused** rather than ignored, and the space
  number is why: a misspelt `:space` is a key nothing looks at, so the KB would
  quietly open on the default space and two KBs meant for separate stores would share
  one — each one's flush emptying the other.  `vaelii.impl.kb/opt-keys` is the roster.

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
  answer quietly wrong for one forgotten call.  `:recover? :auto` repairs that on
  construction (`reindex` first when the index is derived and therefore opened empty),
  which costs one pass over the stored records.  It is the default because the failure
  it prevents is a *wrong answer* rather than an error: `false` and `[]` are legitimate
  results, so no caller can tell them apart, and a warning is a log line a configured
  level can drop.  `:warn` only logs; `false` is silent, for a caller managing recovery
  itself.  `true` is an alias for `:auto`, since a `?`-suffixed option reads as a
  boolean; anything else is refused (`:type :unknown-option`), because the dispatch
  cannot tell an unrecognized setting from `:warn` and would hand back the empty TMS
  the caller asked to avoid.

  **And such a KB does not accept writes.**  What `:warn` and `false` leave is a state a
  read can survive — an empty answer is one you can ask again — and a write cannot: the
  definitional checks all pass vacuously over an empty network and nothing re-runs them,
  so the store keeps content it would have refused.  So the write doors refuse it by name
  (`:unrecovered-kb`), and `*write-unrecovered?*` is the opt that accepts one anyway.
  `false` stays silent about the *read* side and says the write side once, at `:info`:
  a caller managing recovery itself already knows the queries answer nothing, and cannot
  be expected to know the refusal is waiting.

  The KB value's slots — the prover registry, the solver, the ledgers, the caches — are
  documented on the record in `vaelii.impl.kb`."
  ([] (open-kb {}))
  ([opts] (kb/open-kb opts recover reindex)))

(defn fork
  "A private, writable KB over this one's stores — a **fork**.  Reads resolve fork-first
  and fall through to `kb`, writes land only in the fork, and **`kb` is never written**,
  so several forks may share one base and evolve independently.

  `opts` names the fork's *own* storage, as an ordinary opts map (`:backend :memory` by
  default — an ephemeral hypothesis on a space nothing else uses; `{:backend :disk
  :dir …}` gives a durable one, which can be remounted over the same base later and
  serves the merged view it was left in).  `:tms` selects the fork's truth-maintenance
  representation and, unlike the front-door policies below, does **not** inherit: an
  unnamed `:tms` takes the engine default (`:dense`), not the base's rep.  That is safe
  because the two are belief-identical (`jtms_dense_oracle_test`), so a fork holds the same
  beliefs whichever representation it rebuilds them in.

  **The fork's belief is rebuilt, not inherited.**  Belief is not storage — it is a
  derived graph over the records — so the fork is `recover`ed over the merged view rather
  than layered over the base's network.  That is one pass over the merged records, which
  is what `recover` costs anywhere.

  The base is frozen by the mount, not copied: nothing is written and nothing is
  duplicated, so the cost of taking a fork is the recovery and not the base.  The index
  must be one written over the `KvBackend` seam (`:memory`, `:dense`, `:disk`); a
  `:columnar` index is refused, since a KV decorator would fork its roots and leave its
  native trie behind.

  **The front-door policies are inherited**, `:naming` and `:constraints` both, unless
  `opts` names one.  A fork is a hypothesis over the base's own content, and a fork that
  quietly held it to different conventions — or that refused a clash the base would have
  arbitrated — would answer a different question from the one the caller asked."
  ([kb] (fork kb {}))
  ([kb opts]
   (let [own    (dissoc opts :tms :naming :constraints)
         ;; a RAM overlay that names no :space would land on the shared process
         ;; default (space 0) — two such forks would see each other's writes, and a
         ;; plain open-kb in the same JVM would see both — so any opts naming neither
         ;; a :space nor a :dir take the fresh fork space, exactly as no opts do;
         ;; naming one explicitly stays the remount spelling
         own    (cond
                  (not (seq own))              (mount/fresh-overlay-opts)
                  (or (:space own) (:dir own)) own
                  :else                        (merge (mount/fresh-overlay-opts) own))
         forked (kb/open-kb {:records  :overlay
                             :index    :overlay
                             :base-stores {:records (:records kb) :index (:index kb)}
                             :overlay  own
                             :tms      (:tms opts :dense)
                             :naming   (:naming opts (:naming kb :strict))
                             :constraints (:constraints opts (:constraints kb))
                             :recover? false}
                            recover reindex)]
     (recover forked)
     forked)))

(def default-chain-opts
  "max-depth bounds derivation depth to catch productive infinite recursion;
  max-derivations is a hard backstop on a single chain run."
  chain/default-chain-opts)

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
;; earlier: *which terms are there at all*.  They read the index's term roster — the set
;; of names the inverted term index is keyed by, maintained beside its postings — so the
;; cost is the size of the **vocabulary**, never the size of the KB.

(defn terms
  "Every term the index is keyed by — the KB's vocabulary: each predicate, individual,
  type, and context name mentioned by a stored sentex, at any nesting depth.  Sorted by
  name, so the answer is stable and reads the same in-process and over the wire (a
  sorted set would lose its order to EDN; a vector keeps it).

  Read from the term roster, so it is O(terms), not O(sentexes) — and the sort is the
  only superlinear part, which `find-terms` pays over its hits alone.  A *ground
  compound* subterm keys the term index too (`find-sentexes` takes one), but it is a
  sentence fragment rather than a name, so it is not part of the vocabulary.

  Terms are what is **stored**: a defeated or unsupported sentex keeps its names here,
  exactly as it keeps its extent in the secondary roots."
  [kb]
  (vec (sort (p/terms (:index kb)))))

(defn term-count
  "How many distinct terms the KB's vocabulary holds — one set-size read, O(1), nothing
  fetched.  The cardinality of `terms`, and like it a count of what is stored."
  [kb]
  (p/term-count (:index kb)))

(defn sentex-count
  "How many sentexes the KB holds, in total — the count the count-aware trie keeps at its
  root, so O(1) and nothing fetched.

  A count of what is **stored**, like the `count-*` trio: a defeated or unsupported
  sentex is included, as is a rule and a metadata declaration.  Summing `count-in-context`
  over `contexts` is not the same number — that counts only what is in a context the
  *taxonomy* knows, so content in a context no `genlCx` edge mentions is invisible
  to it."
  [kb]
  (p/count-at (:index kb) []))

(defn- check-bound-opts!
  "Refuse an opts key `fn-name` does not read (its roster is `opt-keys`), and a
  non-nil non-map `opts` — `check-assert-opts!`'s reasoning at the two consequence
  doors.  Every key either of them reads is a bound on the run or on the answer, so
  the silent-default failure is a cap silently off: `{:max-result 5}` reads as no key
  at all and the diff comes back uncapped, with `:bounded?` false as though the whole
  answer had been asked for."
  [opts opt-keys fn-name]
  (opts/check! opts opt-keys fn-name
               (str "An option nothing reads takes the default in silence,"
                    " which for a bound means running or answering uncapped.")))

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
    :regex (let [re (if (instance? java.util.regex.Pattern q) q (re-pattern (str q)))]
             (fn [^String s] (boolean (re-find re s))))
    (throw (ex-info (str "unknown :match " (pr-str match) " — want :prefix, :substring, or :regex")
                    {:type :unknown-option :match match}))))

(defn find-terms
  "The vocabulary terms whose name matches `q`, sorted by name.  This is the search a
  term picker wants: it filters the **term roster**, so it costs the size of the
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
   ;; the roster first: a misspelt `:mtch` or `:case-sensitve?` silently ran the
   ;; default search, and a prefix answer where substring was asked for reads as
   ;; \"no such term\" — in the browser's own search box, over the wire
   (check-bound-opts! opts #{:match :case-sensitive? :limit} "find-terms")
   ;; then the `:match`-style value refusal: a known key holding a value it cannot
   ;; mean.  Unchecked, a string limit reaches `take` and raises a bare cast error —
   ;; over the daemon's `:find-terms` op, a 500 with no `:type` on it.  An explicit
   ;; nil is no limit, which the `if-let` below already reads it as.
   (when-some [n (:limit opts)]
     (when-not (pos-int? n)
       (throw (ex-info (str "find-terms :limit must be a positive integer, got "
                            (pr-str n))
                       {:type :unknown-option :limit n}))))
   (let [match? (term-matcher q opts)
         hits   (sort (filter #(match? (str %)) (p/terms (:index kb))))]
     (vec (if-let [n (:limit opts)] (take n hits) hits)))))

;; ---- secondary roots: extent + cardinality from the other directions ----
;; The trie is ordered [pred args… ctx] and narrows only left-to-right, so it can
;; count "predicate P" but not "context C" or "X in argument position 2".

(defn- records-of [kb handles]
  (->> handles (map #(p/get-sentex (:records kb) %)) (filter some?)))

;; ## Stored vs believed — read this before comparing an extent with a count
;;
;; The three `count-*` readers read set cardinalities: no records fetched, no belief
;; consulted.  Two are one read outright — `count-in-context` and `count-with-functor`
;; each size a single posting — and `count-with-arg` is one read *per predicate holding
;; the term at that position*, since the argument postings are scoped by predicate: it
;; reads the slot roster and sums a cardinality over it, which is one key in the
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
  `check-assert-opts!`'s reasoning at these doors.  The one option is the belief
  filter, so the silent-default failure is the filter silently *off*: `{:believed
  true}` reads as no key at all and the stored extent comes back whole, defeated
  defaults included, indistinguishable from a believed extent that happens to have
  nothing defeated in it."
  [opts fn-name]
  (opts/check! opts extent-opt-keys fn-name
               (str "An option nothing reads takes the default in silence, which here"
                    " means the stored extent — defeated defaults included — where the"
                    " believed one was asked for.")))

(defn- believed-filter
  "Apply the extent fns' `{:believed? true}` option: keep only sentexes the JTMS
  currently believes.  O(n) in the extent — the caller opted into it."
  [kb opts sentexes]
  (if (:believed? opts)
    (filter #(jtms/in? (:tms kb) (:id %)) sentexes)
    sentexes))

(defn sentexes-in-context
  "Every **stored** sentex asserted in `context` (its extent, rules included) — a
  defeated or unsupported one included.  Pass `{:believed? true}` to keep only what
  the JTMS currently believes; that costs a TMS lookup per handle (O(n)), unlike the
  unfiltered read.  An opts key this fn does not read is refused (`:unknown-option`),
  so a misspelt filter never silently answers the stored extent."
  ([kb context] (sentexes-in-context kb context nil))
  ([kb context opts]
   (check-extent-opts! opts "sentexes-in-context")
   (believed-filter kb opts (records-of kb (p/sentexes-in-context (:index kb) context)))))

(defn count-in-context
  "How many sentexes are **stored** in `context` — one set-size read, O(1), nothing fetched.

  Counts stored-not-believed sentexes too (a defeated default still occupies the
  context), so this can exceed `(count (sentexes-matching kb pattern context))`, which filters
  belief.  For the believed count use
  `(count (sentexes-in-context kb context {:believed? true}))` — necessarily O(n),
  since belief lives in the TMS and not in the index."
  [kb context] (p/count-in-context (:index kb) context))

(defn sentexes-with-functor
  "Every **stored** fact sentex whose functor is `pred`, any arity, either polarity —
  a defeated or unsupported one included.  Pass `{:believed? true}` to keep only what
  the JTMS believes (O(n) in the extent).  An opts key this fn does not read is
  refused (`:unknown-option`)."
  ([kb pred] (sentexes-with-functor kb pred nil))
  ([kb pred opts]
   (check-extent-opts! opts "sentexes-with-functor")
   (believed-filter kb opts (records-of kb (p/sentexes-with-functor (:index kb) pred)))))

(defn count-with-functor
  "How many fact sentexes with functor `pred` are **stored** — one set-size read, O(1).

  Counts stored-not-believed sentexes too, so it can exceed
  `(count (sentexes-matching kb (list pred ...) '?ctx))`.  The believed count is
  `(count (sentexes-with-functor kb pred {:believed? true}))` and is O(n)."
  [kb pred] (p/count-with-functor (:index kb) pred))

(defn sentexes-with-arg
  "Every **stored** fact sentex holding `term` at 1-based argument position `pos` —
  a defeated or unsupported one included.  Pass `{:believed? true}` to keep only what
  the JTMS believes (O(n) in the extent).  An opts key this fn does not read is
  refused (`:unknown-option`)."
  ([kb pos term] (sentexes-with-arg kb pos term nil))
  ([kb pos term opts]
   (check-extent-opts! opts "sentexes-with-arg")
   (believed-filter kb opts (records-of kb (p/sentexes-with-arg (:index kb) pos term)))))

(defn count-with-arg
  "How many fact sentexes hold `term` at argument position `pos`, as **stored** — cheap,
  one O(1) set-size read per predicate declaring an argument at that slot.

  Counts stored-not-believed sentexes too.  The believed count is
  `(count (sentexes-with-arg kb pos term {:believed? true}))` and is O(n)."
  [kb pos term] (p/count-with-arg (:index kb) pos term))

(defn types-of
  "The types asserted of individual `x` — functors of unary sentexes (T x), found
  via the term index.  Scoped to memberships visible from `context` (default:
  any context)."
  ([kb x] (kb/types-of kb x))
  ([kb x context] (kb/types-of kb x context)))

(defn disjoint?
  "Are types `a` and `b` provably disjoint (via disjoint declarations, closed
  under genl)?  With a `context`, only declarations and genl edges visible from
  it count — the vantage every definitional check now judges from."
  ([kb a b] (kb/disjoint? kb a b))
  ([kb a b context] (kb/disjoint? kb a b context)))

(defn term-role
  "The naming role of `term`, for display / classification — one of `:variable` (`?x`),
  `:number`, `:lexeme`, `:context`, `:individual`, `:predicate`, `:sense`, `:type`, or
  nil (a string, or a symbol matching no convention).  Reads the naming invariants
  (`vaelii.impl.naming`) that `assert` enforces, so a caller — a UI coloring a term, a
  tool grouping one — can classify it by the same rules the engine validates by.

  Decided most-specific first, and each step earns its place: `:lexeme` is first because
  a namespace decides it outright and the name half is not ours to read; a context name
  is also CapitalCamel, so `:context` wins over `:individual`; and a sense is a type, so
  `:sense` is reported before the `:type` it is a kind of."
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

(defn reified-term?
  "Is `term` a **reified non-atomic term** — the opaque constant a ground `(F a…)`
  under a `reifiableFunction` was minted as (docs/nat.md)?  A pure test on the
  symbol's reserved namespace, so a display layer can ask it of every term it renders
  and pay a read only where the answer is true.

  The constant is an implementation of *term identity*, not a name anybody wrote, so
  nothing should show one to a reader: this is the gate, and `term-expression` is what
  to render instead."
  [term]
  (nat/reified-nat-symbol? term))

(defn term-expression
  "The functional expression a reified term denotes — `(FruitFn AppleTree)` for the
  constant minted from it — or nil for an ordinary term, and for a reified one whose
  `(termOfUnit K E)` map is not believed.

  **One hop.**  An argument that is itself a reified term comes back as its constant,
  so a caller rendering each term individually (linking it, colouring it) recurses and
  keeps every level addressable; a caller wanting the whole thing flat calls again on
  what it finds.  One index read per call, belief-filtered like any other."
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
  With a `context`, only edges visible from it are walked (docs/taxonomy.md)."
  ([kb t] (tax/genls (:taxonomy kb) t))
  ([kb t context] (tax/genls (:taxonomy kb) t context)))

(defn specs
  "The subtypes of type `t`, reflexively — `t` itself plus everything that reaches
  it by `genl`.  A set; `#{t}` when `t` is not a node in the type hierarchy.  This
  is the fan-out that lets an antecedent `(animal ?x)` match a stored `(dog Muffet)`.
  With a `context`, only edges visible from it are walked."
  ([kb t] (tax/specs (:taxonomy kb) t))
  ([kb t context] (tax/specs (:taxonomy kb) t context)))

(defn genl?
  "Is `sub` a (reflexive-transitive) subtype of `super`?  Types, not individuals —
  for an individual's type membership use `isa?`.  With a `context`, only edges
  visible from it count."
  ([kb sub super] (tax/genl? (:taxonomy kb) sub super))
  ([kb sub super context] (tax/genl? (:taxonomy kb) sub super context)))

(defn types
  "Every type currently in the genl hierarchy — the nodes of the closure, i.e. every
  type named by some believed `genl` edge."
  [kb] (tax/types (:taxonomy kb)))

(defn contexts
  "Every context currently in the genlCx hierarchy — the nodes of the closure."
  [kb] (tax/contexts (:taxonomy kb)))

(defn context-up
  "The contexts `c` inherits from, reflexively — `c` plus everything it *sees* via
  `genlCx`.  A sentex in any of these is visible from `c`."
  [kb c] (tax/context-up (:taxonomy kb) c))

(defn context-down
  "The contexts that inherit from `c`, reflexively — `c` plus every context that
  sees it."
  [kb c] (tax/context-down (:taxonomy kb) c))

(defn sees?
  "Does context `k` see assertions made in context `y`?  True iff `y` is in `k`'s
  genlCx up-closure (reflexively, so a context sees itself)."
  [kb k y] (tax/sees? (:taxonomy kb) k y))

(defn has-prop?
  "Does `pred` carry the metadata property `kind` — one of `:transitive`,
  `:symmetric`, `:asymmetric`, `:reflexive`, `:functional`, `:decontextualized`,
  `:forced-decontextualized`, `:abducible`, `:reifiable`, `:unreifiable`?  Declared
  by the corresponding sentex, e.g. `(symmetric siblingOf)`.

  A predicate carries all but the last two: `:reifiable` / `:unreifiable` are a
  *function*'s kind, declared by `(reifiableFunction F)`, and read by the reify pass
  (`vaelii.impl.nat`).

  Argument-position *preservation* is not here: `(transitiveInArg P n R)` is per
  position, so like `arg` it is an ordinary stored sentex read through
  `matches-visible` rather than a cached predicate property (`vaelii.impl.inherit`).

  With a `context`, the declaration must be visible from it."
  ([kb kind pred] (tax/has-prop? (:taxonomy kb) kind pred))
  ([kb kind pred context] (tax/has-prop? (:taxonomy kb) kind pred context)))

(defn props
  "The set of predicates carrying metadata property `kind` (see `has-prop?`)."
  [kb kind] (tax/props (:taxonomy kb) kind))

(defn inverse-of
  "The predicate declared inverse to `pred` by an `(inverse P Q)` sentex, or nil.
  The relation is stored both ways, so `(inverse-of kb Q)` answers `P`.  With a
  `context`, the declaration must be visible from it."
  ([kb pred] (tax/inverse-of (:taxonomy kb) pred))
  ([kb pred context] (tax/inverse-of (:taxonomy kb) pred context)))

(defn disjoint-metatypes
  "The declared disjoint metatypes — each a type whose member types are pairwise
  disjoint by `(disjointMetatype M)`.  The clique is *consulted*, not materialized: no
  `(disjoint a b)` pair is stored, so to render the induced pairs, take
  `metatype-members` of each and pair them yourself."
  [kb] (tax/disjoint-metatypes (:taxonomy kb)))

(defn metatype-members
  "The member types of disjoint metatype `m` — the set whose every pair `disjoint?`
  holds of, closed under genl."
  [kb m] (tax/metatype-members (:taxonomy kb) m))

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
  — the terms `CxCore` declares — so an ordinary domain predicate is simply not in
  scope.  `vocabulary-audit` is the whole picture, and what keeps this one honest."
  [term] (vocab/classify term))

(defn vocabulary-audit
  "Every term `CxCore` declares in `kb`, classified — `{:enforced [[term why] …]
  :inert [[term why] …] :unclassified [term …] :retired [term …] :contradicted [term
  …]}`.

  `:unclassified` is the finding this exists to surface: a declaration that landed in the
  grammar without anybody deciding whether the engine reads it.  `:retired` is the mirror,
  a claim about a term the KB no longer declares.  `:contradicted` needs no judgement at
  all — a term the special-predicate table gives an arm to and the roster calls inert.

  Empty in all three on the shipped ontology, and a test holds it there."
  [kb] (vocab/audit kb))

;; ---- the knowledge, as against the engine -------------------------------
;; `settle-stats`, `chain-stats` and `violations` all report on a *run*: how many
;; iterations, how many conclusions, what was dropped.  None of them is a reading about
;; the KB, so an author of a large one has no answer to "is any of this any good" — and
;; the five questions below are the ones they actually ask.

(defn kb-quality
  "Five readings about the **knowledge** — one map, five keys, each a distribution rather
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
                               :arity :via :message} …]}
               ; argument constraints naming a position their predicate does not have.
               ; :message is the one the check itself wrote, so this map and `check`'s
               ; answer say the same thing in the same words

  Data, not a printer: `quality-report` renders this same map, so nothing can print a
  figure the data does not hold.  **Not a gate either** — a threshold on somebody's
  ontology is not a build failure.

  **`:declarations` is why this reader and not `violations`.**  `(arg parentOf 3 t)` is
  admitted while `parentOf` has no declared length — the highest position a declaration
  names is a lower bound on the arity, not a claim about it — and goes inert when a length
  arrives, whether declared of the predicate or inherited from a super.  It is not
  refused, because refusing it would make the *binding's* arrival order decide what the KB
  holds. A wrong-length **fact** is a different animal and does reach the ledger
  (`:arity`, see `violations`): it is content an `assert` admitted because it could not
  have known, so there is a *newly* only the settle can report. A stranded declaration
  constrains nothing, refuses nothing and mints nothing, and reads the same an hour later
  — a census question, not a settle one.

  `opts`: `:limit` caps each listed set (default 25 — the counts are the headline, and a
  30,000-entry list is not one); `:on-progress` is called with `{:phase :done :total}` as
  each phase advances and may **throw to cancel**, the reading being of current state so a
  half-finished one is discarded rather than repaired.  An unknown option is refused
  (`:unknown-option`), like every other bound on a run.

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
  `O(terms + rules + firings + genl edges + declarations × super-predicates)`: the
  **vocabulary**, walked once, and never the KB.  The product is the one term that is not
  flat — a declaration whose predicate inherits its length costs a read per predicate
  above it, where one carrying its own costs a map read — and `vaelii.impl.quality` says
  how.

  **Read without a snapshot**, like every other reader here: a write landing mid-report can
  leave a count and a list disagreeing by one (a rule enumerated and then retracted is
  dropped from the listed set and stays in the total).  A reading of a moving KB, not a
  transaction over a still one."
  ([kb] (kb-quality kb nil))
  ([kb opts]
   (check-bound-opts! opts #{:limit :on-progress} "kb-quality")
   (when-some [n (:limit opts)]
     (when-not (pos-int? n)
       (throw (ex-info (str "kb-quality :limit must be a positive integer, got " (pr-str n))
                       {:type :unknown-option :limit n}))))
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
;; `genl` has `genls` / `specs` / `genl?` and `genlCx` has `context-up` /
;; `sees?`; the equality partition gets the same treatment, or an application cannot
;; see what merged.  `deprecated?` in particular is what makes the `rewriteOf` /
;; `sameAs` distinction observable at all — both produce the same class, and only the
;; deprecation tells them apart (docs/equality.md, "Public surface").

(defn representative
  "The term standing for `term`'s equivalence class — `term` itself when nothing has
  merged it, so this is total and never nil.

  With a `context`, only the merges that context inherits count — the equality
  analogue of `genls` / `specs` taking one, and for the same reason: an equality is a
  sentex, so it holds where it is visible.  Dropping an edge can *split* a class, so
  the scoped answer is not a filter of the global one but its own election."
  ([kb term] (tax/representative (:taxonomy kb) term))
  ([kb term context]
   (res/representative-in kb (res/visible-supporter-fn kb context) term)))

(defn same-class?
  "Do `a` and `b` denote the same thing?  The complement of a provable
  `(different a b)`: distinct symbols denote distinct individuals until an equality
  sentex says otherwise.  Scoped by `context` like `representative`."
  ([kb a b] (tax/same-class? (:taxonomy kb) a b))
  ([kb a b context] (= (representative kb a context) (representative kb b context))))

(defn equiv-class
  "Every term known equal to `term`, itself included.  `#{term}` when nothing has
  merged it — an unseen term is its own singleton class.  Scoped by `context` like
  `representative`."
  ([kb term] (tax/equiv-class (:taxonomy kb) term))
  ([kb term context]
   (if-let [vis (and (tax/merged? (:taxonomy kb) term)
                     (res/visible-supporter-fn kb context))]
     (first (tax/scoped-class (:taxonomy kb) term vis))
     (tax/equiv-class (:taxonomy kb) term))))

(defn deprecated?
  "Did a believed `rewriteOf` name `term` the dispreferred side?  False for a `sameAs`
  or `equals` member: those merge without retiring either name.  Scoped by `context`
  like `representative` — a retirement holds where it is visible, so a context outside
  the `rewriteOf`'s cone is told nothing and keeps the name."
  ([kb term] (tax/deprecated? (:taxonomy kb) term))
  ([kb term context]
   (tax/deprecated? (:taxonomy kb) term (res/visible-supporter-fn kb context))))

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
  - provenance stamping (`stamp-provenance!`) — belief never reads provenance, so a
    bulk premise carries none.

  It does **not** touch what gets stored, indexed, or believed: the same sentex lands
  for the same fact, so the KB answers identically to a per-fact load (same query
  results + `count-with-functor`).  Bind it only around a load whose facts are known
  well-formed and pairwise distinct; normal `assert` (the default) keeps every
  guarantee.  Pair it with `with-deferred-settle` (one settle at the end) and
  `{:chain? false}` for the full fast path — `bulk-assert-facts!` does all three."
  false)

;; ---- writing into a KB whose derived state was never built ---------------

(def ^:dynamic *write-unrecovered?*
  "Accept writes into a KB opened over a store whose derived state was never built —
  `{:recover? false}` or `:warn` over a populated store, or an `import-dump` with
  `:belief? false` / `:belief? :stored`.  False by default, which **refuses** them
  (`:type :unrecovered-kb`); the repair is `recover`, or `reindex` when the index is
  derived and so opened empty.

  Refusal rather than the naming door's store-it-and-warn, because the two failures do
  not cost the same.  A write into an unrecovered KB is wrong in ways nothing later
  catches:

  - **Every definitional check passes vacuously.**  All ten arms of the constraint
    check read `kb/memberships` and `checks/declaration-reader`, both of which filter on
    `jtms/in?`; with no nodes there are no types and no declarations, so arity, arg,
    genlArg, interArg, declaration-consistency, disjointness, functionality and
    asymmetry all match nothing and the assert lands.  Nothing re-runs them: `recover`
    does not, and its closing settle binds `settle/*rebuilding?*`, which turns the
    exposure pass off.  A store can accumulate content its own constraints forbid,
    indefinitely, with every instrument green.
  - **Two writes land under the wrong key.**  `res/kb-sentex` sorts a symmetric
    predicate's arguments only when the taxonomy says the predicate is symmetric, so
    `(siblingOf Bob Ann)` is stored where a recovered KB writes `(siblingOf Ann Bob)`;
    and a `:forced-decontextualized` predicate lands in the caller's context instead of
    `CxUniverse`.
  - **On a derived index, dedup misses everything.**  `assert` dedups through
    `p/lookup`, so every assert mints a fresh handle for a sentence already stored — and
    `reindex` cannot merge the two, because they are two records.

  A naming violation is recoverable; an un-canonicalized duplicate is not.  So this is
  the opt that names what it gives up, and binding it says the caller has read the list.
  It does **not** cover a `retract!` whose dependency sweep cannot be computed — that
  one is refused whatever this says, since its result is not merely risky but unknown
  (`:type :unrecovered-premise`).  `*bulk-load?*` is deliberately not this opt: it skips
  the very dedup walk that is already missing, which would turn the duplicate risk into
  a certainty."
  false)

(defn- writable-problem
  "The refusal a write into this KB earns, as a value, or nil when there is none.  One
  statement of the policy, read by every write door — `assert`, `assert-inert`,
  `retract!`, `edit!` and `preview` — so no door can hold a different one, and a value
  rather than a throw so the same words serve the accept-anyway warning."
  [kb where]
  (when-let [hz (seq (kb/write-hazards kb))]
    (let [hz      (into {} hz)
          index?  (:no-index hz)
          belief? (:no-belief hz)]
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
            " unchecked — its docstring lists what that gives up.")})))

(defn- unrecovered-problems
  "`writable-problem` as `check` reports problems, or nil — the reading half of the gate
  below.  `check` answers \"would `assert` succeed, and if not why\", so a refusal the
  door makes before any other is a problem the report has to carry, or a caller validating
  a batch is told every line is fine and then refused on the first one.

  Nil under `*write-unrecovered?*`, since `assert` lands the write there and `check`
  answers about `assert` rather than about the KB."
  [kb where]
  (when-not *write-unrecovered?*
    (some-> (writable-problem kb where) vector)))

(defn- check-writable!
  "The write doors' one gate: refuse an unrecovered KB by name, or — under
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
  ;; importer never reaches this door — it writes at the dump's own handles, around the
  ;; assert path — which is what keeps its declaration standing for the whole load.
  (kb/discharge-over-empty-store! kb)
  (when (seq (kb/write-hazards kb))
    (if *write-unrecovered?*
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

;; ---- premise marking, and the one hook `preview` needs -------------------

(def ^:dynamic ^:private *premise-audit*
  "When bound to an atom, every premise mark on the assert path first records the
  datum's **prior** premise state here — `{handle {:premise? bool :strength kw}}`,
  first writer wins.  That is the whole of what `preview` needs to put a KB back the
  way it found it: a handle it marked and that did not exist before is retracted, one
  that existed as a non-premise is un-marked, and one that was already a premise gets
  its original strength back.  Nil, and free, on every ordinary assert."
  nil)

(defn- put-premise-mark
  "Write the premise mark on sentex `h` at exactly `strength` — the network's node and
  the record store's slot, which the assert path always moves together.  One function so
  neither half can be marked without the other: the network is what labelling reads and
  the record is what `recover` rebuilds the network from, so a KB whose two halves
  disagreed would answer one thing until it restarted and another afterwards.

  Callers say `mark-premise` instead.  This is the raw write, and the only caller that
  wants it is the one *restoring* a mark it recorded — `preview-rollback!`, putting back a
  class the KB already held rather than stating one."
  [kb h strength]
  (jtms/add-premise (:tms kb) h strength)
  (p/mark-premise (:records kb) h strength))

(defn- mark-premise
  "Mark sentex `h` a premise, at the **stronger** of the class it already stands at and
  the `strength` offered.  One function so the audit above has one hook rather than
  three, and so neither half can be marked without the other (`put-premise-mark`).

  **Resolved from content, never from arrival order** — the rule
  `reconcile-rule-slots!` states for a re-asserted rule's slots, at the fact door, where
  it decides belief rather than what a caller reads back.  A re-assert carrying no
  `:strength` states nothing about the class: the `:default` it falls back to is the
  door's fallback and not the caller's claim, so reading that silence as a *downgrade*
  made the same knowledge in two orders reach two sets of beliefs.  Asserting
  `(flies Tweety)` known-true, re-asserting it bare, then asserting the known-true
  negation left the original **defeated**; the same three sentences without the bare
  re-assert in the middle left it believed and the pair an irreducible clash.
  `strength/max` is commutative and idempotent, so the orders agree and a third
  assertion changes nothing.

  Narrowing a class is `retract!` and re-assert, exactly as it is for a rule's
  `:direction`, `:defeasible` and `:strength` (docs/canonicalization.md).  A handle that
  is not a premise stands at nothing — `jtms/premise-strength` reads nil, which ranks 0
  — so it takes the offered class whole, and a retraction therefore leaves no class
  behind for the next assertion to inherit."
  [kb h strength]
  (when-let [audit *premise-audit*]
    (let [tms (:tms kb)]
      (swap! audit (fn [m]
                     (if (contains? m h)
                       m
                       (assoc m h {:premise? (jtms/premise? tms h)
                                   :strength (jtms/premise-strength tms h)}))))))
  (put-premise-mark kb h (strength/max (jtms/premise-strength (:tms kb) h) strength)))

(defn- check-rule-sentence
  "Every pre-storage check a rule must pass, as a step that writes nothing —
  `checks/check-rule!`, the list both storage doors read (the other being a generator
  firing, `chain/place-conclusion`).  A generator's own three are in that list rather
  than beside it, because a *minted* rule can be a generator too (docs/generators.md)
  and a check only this door ran would be one the fixpoint could store around."
  [kb sentence context]
  (checks/check-rule! kb sentence context))

(defn- join-direction
  "The direction a rule stated two ways holds in: the **least restrictive** of the two.

  `:inert` is the bottom (it runs in neither engine), `:forward` and `:backward` are
  incomparable, and `:both` is what either of them joined with the other — or with
  `:both` — comes to.  A join rather than a pick, because the two spellings are two
  claims about the same rule and a rule that may run forwards *and* may run backwards
  may do both."
  [a b]
  (cond
    (= a b)      a
    (= :inert a) b
    (= :inert b) a
    :else        :both))

(defn- reconcile-rule-slots!
  "Bring a re-asserted rule's `:direction` / `:defeasible` to the value the two
  assertions jointly state, and re-chain it if that newly lets it run forwards.

  These two slots are not in the sentex identity key — a rule is one rule however its
  direction is spelled — so `find-or-create-sentex` hands back the stored record and the
  second spelling would otherwise be dropped.  Dropping it is **arrival-order
  dependent**: a bare `implies` after a `set/inertRule` would stay inert and never fire,
  and after a `set/defaultRule` stay defeasible and lose to a monotonic rival it should
  tie with — the same two assertions reaching two sets of beliefs, which
  `docs/nmtms.md` does not permit.

  So the slots are resolved from **content** instead: the least restrictive direction
  (`join-direction`), and strict over defeasible — a rule asserted once without
  `set/defaultRule` is a rule somebody stated as holding outright.  Both are commutative
  and idempotent, so the two orders agree and a third assertion changes nothing.

  The record moves, and so does the one derived copy of the defeasibility slot: the
  justifications already fired through this rule carry its contribution as their
  `:strength`, read off the record at fire time (`chain/rule-view-of`), so a
  defeasible→strict resolution must reach them or belief keeps the arrival order this
  fn exists to remove — facts asserted *between* the two spellings would hold
  conclusions at `:default` that the same assertions in the other order hold at
  `:monotonic`.  `jtms/restrength-informant` updates that slot and relabels the
  affected region.  The direction join needs no such reach-back: it only ever *adds*
  capability (`join-direction` is a join, never a meet), backward capability is read
  off the record at query time, and new forward capability is the `chain-all` below.

  The trie key does not carry these slots, and `index-rule-sentex` indexes predicates
  rather than direction, so nothing is re-indexed."
  [kb h stored sentence context opts]
  (let [incoming (res/kb-sentex kb sentence context)
        dir      (join-direction (:direction stored) (:direction incoming))
        def?     (when (and (:defeasible stored) (:defeasible incoming)) true)]
    (when (or (not= dir (:direction stored))
              (not= (boolean def?) (boolean (:defeasible stored))))
      (let [s' (assoc stored :direction dir :defeasible def?)]
        (p/put-sentex (:records kb) s')
        (when (not= (boolean def?) (boolean (:defeasible stored)))
          ;; Both copies of the conferred strength, together — the record store's
          ;; justification records (what `supporting-justifications` shows and what
          ;; `recover` rebuilds the network from) and the network's graph copy (what
          ;; labelling reads), the same both-halves rule `mark-premise` states.
          (let [strength (if def? :default :monotonic)
                tms      (:tms kb)]
            (doseq [jid (jtms/dependents tms h)
                    :let [j (p/get-justification (:records kb) jid)]
                    :when (and j (= h (:informant j)) (not= strength (:strength j)))]
              (p/put-justification (:records kb) (assoc j :strength strength)))
            (jtms/restrength-informant tms h strength)))
        ;; newly forward-capable: it has never been joined over the facts already stored
        (when (and (:chain? opts true)
                   (rules/forward-sentex? s')
                   (not (rules/forward-sentex? stored)))
          (chain/chain-all kb [h] opts))
        (when-not *defer-settle?* (settle/settle kb))))))

(defn- assert-rule-sentence
  "Assert a rule **as written** — any `set/*Rule` wrapper included, since the sentex
  constructor canonicalizes it into the record's `:direction` / `:defeasible`.  The
  well-formedness checks run on the bare rule inside the wrappers.

  Idempotent: a re-asserted rule resolves to the existing sentex.  Where the two
  spellings disagree about direction or defeasibility, the slots are resolved from
  content rather than from which arrived first — see `reconcile-rule-slots!`.

  **`opts :strength` reaches the record here exactly as it does at the fact door**, and
  it is the rule's *own* defeat class — whether a contradicting default can defeat the
  rule itself.  What a firing confers on its conclusion is a different question with a
  different authority: `chain/rule-view-of` reads it off `:defeasible`, so a rule stored
  at `:monotonic` still concludes at its weakest antecedent unless it is bare.  Nothing
  in the engine defeats a rule, so the slot is one that reads back rather than one that
  moves belief — `docs/nmtms.md` states the absence.

  **Re-marking on the existing branch is the mark itself, not only its class.**  A rule
  can be stored and not be a premise — a generator's stamped rule is a *conclusion*,
  resting on the generator's justification — and asserting it is a second and
  independent ground for it, exactly as asserting an already-derived fact is at the
  other door.  Left unmarked, `assert` answered with a handle for a rule that the next
  retraction of the generator took away with it.

  All three slots resolve alike, and from **content**: `:direction` and `:defeasible`
  in `reconcile-rule-slots!`, `:strength` below by taking the stronger.  A re-assert
  carrying no `:strength` states nothing about the class — the `:default` it falls back
  to is the door's fallback, not the caller's claim — so reading that silence as a
  downgrade would leave `defeat-class` answering differently for the same two assertions
  in the two orders.  No belief moves either way, nothing defeating a rule; this is what
  a caller reads back.  Narrowing any of the three is `retract!` and re-assert."
  [kb sentence context opts]
  (check-rule-sentence kb sentence context)
  (let [strength   (get opts :strength :default)
        [h s new?] (kb/find-or-create-sentex kb sentence context strength)]
    (if new?
      (do
        (mark-premise kb h strength)
        (special/index-rule-sentex kb h s)
        ;; defeasible or not, a forward-capable rule seeds the one agenda: `chain`
        ;; joins it over existing facts (process-datum -> fire-rule) at its own strength
        (when (and (:chain? opts true) (rules/forward-sentex? s))
          (chain/chain-all kb [h] opts))
        (when-not *defer-settle?* (settle/settle kb)))
      (do
        (reconcile-rule-slots! kb h s sentence context opts)
        ;; `find-or-create-sentex` hands back the stored record and drops the strength
        ;; the second assertion carried, the same way it drops the direction the
        ;; reconcile above puts back — and the mark is worth making for a second reason
        ;; than the class: a stored rule need not be a premise at all (a generator's
        ;; stamped rule is a *conclusion*, resting on the generator's justification), and
        ;; asserting one is an independent ground for it, exactly as asserting an
        ;; already-derived fact is at the fact door.
        ;;
        ;; **Resolved from content, like the two slots above it.**  `strength/max` takes
        ;; the stronger, so the two orders agree and a third assertion changes nothing —
        ;; the rule `reconcile-rule-slots!` holds for `:direction` and `:defeasible`, and
        ;; it holds here for the same reason: a re-assert carrying no `:strength` states
        ;; nothing about the class, so reading that silence as a downgrade made
        ;; `defeat-class` answer differently for the same two assertions in either order.
        ;; Narrowing one is `retract!` and re-assert, as it is for the other two.  A
        ;; record with no class yet — nil, so not a premise — ranks 0 and takes the
        ;; incoming class.
        (let [resolved (strength/max (:strength s) strength)]
          (when (not= resolved (:strength s))
            (mark-premise kb h resolved)
            ;; the mark relabels, and a door that moves a label settles before it
            ;; returns.  A class move alone moves none, nothing in the engine defeating
            ;; a rule — but the *first* mark of a rule that was only ever concluded puts
            ;; it IN, and that revives whatever it licenses.
            (when-not *defer-settle?* (settle/settle kb))))))
    h))

;; A `set/defaultRule` wrapper sets `:defeasible` on the record, so the one rule path
;; below handles every flavour — do not add a second entry point per flavour.

(defn- assert-exceptWhen-meta!
  "Store one exceptWhen exception against the rule at `rule-handle` as a
  belief-following `(exceptWhen <aligned-query> (sentexHandle rule-handle))`
  meta-sentex, and return its handle.

  `exc` is the exception's conjunct literals in the *author's* variable names (as
  written beside the rule), and `author-vm` is the canonical→author varmap of the rule
  **as written in this assert** — not the rule's stored varmap, which carries whatever
  names the rule was *first* asserted with, so a re-reference under new variable names
  would misalign.  The query is mapped to the rule's canonical variables through it, so
  a firing's bindings substitute straight in; an exception variable no antecedent binds
  is refused (`:exception-not-closed`), as is one that would close a cycle through
  negation (`check-exceptWhen-stratified`).  Storing it posts the re-check index
  (`index-exceptWhen-meta`) and settles, so any conclusion the new exception now blocks
  is swept before this returns."
  [kb rule-handle exc author-vm context opts]
  (let [rsx (p/get-sentex (:records kb) rule-handle)]
    (when-not (and rsx (rules/rule? rsx))
      (throw (ex-info (str "exceptWhen names handle " rule-handle ", which is not a rule")
                      {:type :not-well-formed :handle rule-handle :exception (vec exc)})))
    (let [author  (into #{} (vals author-vm))                       ; the rule's author variables
          inv     (into {} (map (fn [[cv av]] [av cv])) author-vm)  ; {?x ?var0}
          exc-vars (distinct (mapcat #(filter sx/variable? (tree-seq sequential? seq %)) exc))
          loose   (remove author exc-vars)]
      (when (seq loose)
        (throw (ex-info (str "exception is not closed: " (pr-str (vec loose))
                             " unbound by the rule's antecedents")
                        {:type :exception-not-closed :unbound (vec loose)
                         :exception (vec exc) :rule rule-handle})))
      (let [aligned (sx/sort-conjuncts (map #(sx/canon (res/substitute % inv)) exc))
            meta-s  (sx/exceptWhen-meta aligned rule-handle)]
        ;; Each conjunct is held to the naming invariants, like every other literal a
        ;; rule carries.  `check-rule-sentence` runs `nm/check!` on `rules/inner-rule`,
        ;; which has already peeled the query off, and nothing else reached it — so
        ;; `nm/literals`' `:exception` role and the "exceptWhen exception" wording in
        ;; `literal-roles` existed with nothing on the assert path calling them, and
        ;; `(exceptWhen (lives_in ?x cold_place) …)` stored the snake_case-arity-2
        ;; literal `docs/naming.md` says is refused.  The store holding what the front
        ;; door refuses is the shape of corruption these checks exist to stop.
        (run! #(nm/check! (:naming kb) % context) aligned)
        (checks/check-no-imperative meta-s)
        (checks/check-exceptWhen-stratified kb rule-handle (keep nm/functor aligned) context)
        (let [strength   (get opts :strength :default)
              [h s new?] (kb/find-or-create-sentex kb meta-s context strength)]
          (when new?
            (mark-premise kb h strength)
            (integrate/sentex-added kb s h)          ; index-exceptWhen-meta + queue the re-check
            (when-not *defer-settle?* (settle/settle kb)))  ; sweep what the new exception now blocks
          h)))))

(defn- ist-parts
  "The `[context sentence]` an `(ist Ctx S)` names, or nil when the form is not one — a
  bare `(ist Ctx)` included.

  `assert` and `check` both read the form here, so a malformed `ist` is one refusal on
  both paths.  Reaching into it positionally is how the two would disagree: `check`
  taking a default and reporting `:shape` while `assert` takes none and throws a bare
  `IndexOutOfBoundsException`, which carries no `:type` for a caller to discriminate on
  and names nothing a writer can act on."
  [sentence]
  (when (and (sequential? sentence)
             (= sx/ist-functor (first sentence))
             (= 3 (count sentence)))
    [(second sentence) (nth sentence 2)]))

(defn- ist-shape-problem
  "The `:shape` problem a malformed `ist` is refused with — a value for `check`, and the
  `ex-info` `assert` throws."
  [sentence]
  {:type :shape :sentence sentence
   :message (str "an (ist Ctx S) names a context and a sentence, got " (pr-str sentence))})

;; `(ist Ctx S)` handed to `assert` recurses into `assert` with the inner sentence
;; (`assert-one` below), and `assert` is defined after it — a genuine forward
;; reference, and the only one here: query and settle live below this namespace, in
;; impl.kb and impl.settle.
(declare assert)

(defn- assert-one
  "Assert a single sentence (any conjunctive-consequent rule is split into one rule
  per conjunct by `assert` before reaching here).  Returns the sentex handle."
  [kb sentence context opts]
  (cond
    ;; A `do/` imperative is an instruction, not a fact: nothing is stored, and what
    ;; comes back is the action's result (docs/labeling.md).  First, so no naming or
    ;; well-formedness check ever sees a form that is not a sentence.
    (sx/do-form? sentence)
    (imperative/run kb sentence context)

    ;; (ist Ctx S) is not stored — it finds or creates S in Ctx (ist semantics)
    (and (sequential? sentence) (= sx/ist-functor (first sentence)))
    (if-let [[ctx s] (ist-parts sentence)]
      (assert kb s ctx opts)
      (let [p (ist-shape-problem sentence)]
        (throw (ex-info (:message p) (dissoc p :message)))))

    ;; Every rule flavour takes one path: a bare `(implies ..)` (a :both rule) and
    ;; any `set/*Rule` wrapping of one.  The wrapper is not stripped here — it is
    ;; canonicalized into the record's :direction / :defeasible by the sentex
    ;; constructor.  Routing through the checked rule path also gets
    ;; range-restriction and rule indexing, rather than storing a plain premise.
    (rules/rule-sentence? (rules/inner-rule sentence))
    (assert-rule-sentence kb sentence context opts)

    :else
    ;; A virtual wrapper (`set/*Rule`, `set/defaultRule`, `exceptWhen`) is meaningful
    ;; only around an implication, but the sentex constructor peels it off whatever it
    ;; wraps — so `(set/defaultRule (dog Felix))` *stores* the bare `(dog Felix)`.
    ;; Peel it here too, so the checks below run on the sentence that will actually be
    ;; stored.  Checking the wrapper instead let a fact walk past every definitional
    ;; check: the functor is `set/defaultRule` and the sole argument is a list, so
    ;; naming, arg, disjointness and functionality all matched nothing and passed
    ;; vacuously, and the stripped fact landed in the store unchecked.
    ;;
    ;; A *forced* universal predicate (e.g. genlCx) has its extent placed in
    ;; CxUniverse by force — no justification, the fact simply lives there.
    (let [sentence (rules/inner-rule sentence)
          pred    (nm/functor sentence)
          ;; the global property read on purpose: this decides where the sentex is
          ;; *stored*, and storage cannot vary by the writer's visibility — scoping
          ;; the lift by what could see the declaration would be circular
          context (if (and pred (tax/has-prop? (:taxonomy kb) :forced-decontextualized pred))
                    special/universal-context context)]
      ;; Bulk load skips every check below: each only *validates* (none writes), and
      ;; the caller has guaranteed the corpus is well-formed — including the arg
      ;; store query in `constraint-checks`, the dominant per-fact cost (*bulk-load?*).
      ;; The checks yield one *value* forward: what the argument constraints entail
      ;; about this sentence's arguments.  It is computed here — where the declarations
      ;; are already being read — and materialized below, because at this point the
      ;; sentex does not exist yet and there is no handle to justify a derived type
      ;; against.  Empty unless assertive argument types are on.
      (let [ents (when-not *bulk-load?*
                   (nm/check! (:naming kb) sentence context)
                   (checks/check-ground kb sentence context)
                   (when-let [ps (seq (special/wff-problems (:taxonomy kb) sentence))]
                     (throw (ex-info (str "not well-formed: " (str/join "; " ps))
                                     {:type :not-well-formed :sentence sentence})))
                   ;; the rule-set half of well-formedness, for the *other* thing that can
                   ;; close a cycle through negation: a genl / genlCx edge arriving
                   ;; underneath rules already stored (docs/exceptions.md).  Before anything
                   ;; is written and before the taxonomy is touched, so a refusal leaves
                   ;; nothing behind.
                   (checks/check-edge-stratified kb sentence context)
                   (checks/constraint-checks kb sentence context))
            strength (get opts :strength :default)
            ;; Bulk load skips the dedup trie-walk: a distinct corpus never hits an
            ;; existing sentex, so `create-sentex` directly is the same result the
            ;; `find-or-create` miss branch would take.
            ;; the record is born carrying its strength, so `mark-premise` below has
            ;; nothing to re-store — see `kb/create-sentex`
            [h s _]  (if *bulk-load?*
                       (let [[h s] (kb/create-sentex kb sentence context strength)] [h s true])
                       (kb/find-or-create-sentex kb sentence context strength))]
        (mark-premise kb h strength)
        ;; The add-side choke point: the sentex is reflected into every cache
        ;; through the special-predicate table and the exception re-check is queued
        ;; — one call, so no assert path can forget either half.  An equality
        ;; sentex reaches the closure there and migrates what it displaces;
        ;; everything else returns nil.  The three slots it returns are the caller's
        ;; to apply: the twins are chaining seeds, the supersessions are belief, and
        ;; and the violations are reported after `chain-all` so they carry its run id.
        (let [eq (integrate/sentex-added kb s h)
              ;; a fact naming a term the closure has *already* displaced is restated
              ;; on arrival, exactly as a fact asserted before the merge is restated
              ;; by it — otherwise migration would depend on which came first
              own  (when (kb/rewritable-sentex? kb s) (special/migrate-sentex kb s))
              ;; ...and the equality a `functional` declaration now infers instead of
              ;; throwing, which merges in its turn
              fnl  (special/derive-functional-equalities kb sentence context h)
              ;; ...and the same inference from the declaration's side, so a
              ;; `(functional P)` arriving after P's facts merges what they already
              ;; licensed rather than only what follows it
              fex  (special/equate-existing kb sentence)
              ;; ...and from the third side: a `genl` edge between predicates brings
              ;; stored sub-predicate facts under a `functional` mark above them
              fdn  (special/equate-under-edge kb sentence)
              ;; ...and the antisymmetric merge, in the same three arrival orders: a fact
              ;; meeting its converse under an `(antiSymmetric P)` mark, the declaration
              ;; meeting the facts, and the `genl` edge bringing them under a mark above
              asym (special/derive-antisymmetric-equalities kb sentence context h)
              axe  (special/antisym-equate-existing kb sentence)
              axd  (special/antisym-equate-under-edge kb sentence)
              mig  (merge-with into {:new [] :superseded [] :violations []}
                               eq own fnl fex fdn asym axe axd)]
          ;; Only when this assert actually merged something.  The reconcile re-examines
          ;; every entry the closure currently displaces, and an assert that merged
          ;; nothing cannot change one: an entry stops being displaced when its terms
          ;; stop rewriting (the closure shrank) or when its restatement stops being
          ;; stored (a deletion), and an assert does neither.  Ungated it is O(merged)
          ;; per assertion — on OpenCyc, 1,489 merges re-examined 780,000 times.
          (when (seq (:superseded mig))
            (special/refresh-supersessions kb (:superseded mig)))
          ;; the CxUniverse copy, if the predicate is decontextualized — a
          ;; deduction off this sentex and the declaration, so it is a chaining seed
          ;; of its own, and it reports rather than throws when it cannot be admitted
          (let [lift  (special/deduce-lifts kb sentence h context)
                ;; ...and the types the argument constraints entail about this
                ;; sentence's arguments, each a deduction off this sentex and the
                ;; declaration that licensed it.  Both directions, because a
                ;; declaration must reach the facts already stored exactly as it
                ;; reaches the facts that follow: `deduce-arg-types` is this sentence
                ;; meeting the declarations, `entail-existing` is this sentence *being*
                ;; a declaration and meeting the facts.
                args  (special/deduce-arg-types kb ents h context)
                back  (special/entail-existing kb sentence h)
                ;; ...and the third order of the same three ingredients: a `genl` edge
                ;; between predicates brings stored sub-predicate facts under the
                ;; declarations already written above them
                down  (special/entail-under-edge kb sentence)
                mig   (update mig :violations into
                              (concat (:violations lift) (:violations args)
                                      (:violations back) (:violations down)))
                seeds (-> [h]
                          (into (:new mig))
                          (into (:new lift))
                          (into (:new down))
                          ;; a minted type makes this fact matchable at a type it did
                          ;; not have, so it goes on the agenda for the same reason the
                          ;; genl seeds below do — a rule on `(animal ?x)` must fire off
                          ;; a type the entailment minted, within this same assert
                          (into (:new args))
                          (into (:new back))
                          ;; a new genl edge makes stored facts matchable at a
                          ;; supertype they did not have — they go back on the agenda,
                          ;; or the same knowledge would derive different things in
                          ;; different arrival orders
                          (into (special/subsumption-seeds kb sentence))
                          ;; ...and a new genlCx edge makes stored facts visible to
                          ;; a rule that could not see them, which is the same failure
                          ;; through the other closure
                          (into (special/visibility-seeds kb sentence)))]
            (when (:chain? opts true) (chain/chain-all kb seeds opts))
            ;; **After** the chain, so the entry carries the run that just ran: a
            ;; violation a merge created — the twin that would have made one individual
            ;; both a dog and a cat — is this assert's to report, and
            ;; `violations/report` stamps each entry with `(:runs @chain-stats)`
            ;; (docs/equality.md, "Interactions — Disjointness").  The ledger itself
            ;; accumulates and is emptied only by `clear-violations!`.
            (violations/report kb (:violations mig))))
        ;; `*defer-settle?*` is bound only while a rule firing mints a skolem NAT
        ;; mid-fixpoint (`skolemize-conclusion`): the nested `(termOfUnit K E)` assert
        ;; is monotonic bookkeeping and the enclosing firing settles once when it
        ;; completes, so settling here per mint is redundant churn (docs/skolem.md).
        (when-not *defer-settle?* (settle/settle kb))
        h))))

;; ---- provenance ---------------------------------------------------------
;; A per-handle bookkeeping map (creator + creation date, plus whatever an
;; application adds) kept beside the record, never as fields on it (see
;; protocols/RecordStore).  Belief never reads it, so a wall-clock `:created` cannot
;; affect order independence.

(def ^:dynamic *creator*
  "The creator stamped into a sentex's provenance on `assert` when opts carries no
  `:creator`.  nil by default; bind it per session / import / user."
  nil)

(def ^:dynamic *clock*
  "A 0-arg fn returning the `:created` stamp `assert` records (epoch milliseconds by
  default).  Bind it in tests to pin the value; belief never reads provenance, so a
  wall-clock default does not touch order independence."
  (fn [] (System/currentTimeMillis)))

(defn- stamp-provenance!
  "Record creation provenance for the handle(s) `assert` produced.  First-writer-wins
  on `:creator` / `:created` — a re-asserted sentex keeps its original stamp — while
  an application's extra `:provenance` fields are merged in on any assert.  Called
  once per public `assert`, so derived and lifted sentexes (which never go through it)
  are not stamped as asserted."
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
            (nil? cur)   (p/put-provenance rec h (merge {:creator creator :created @now} extras))
            (seq extras) (p/put-provenance rec h (merge cur extras)))))))
  nil)

;; ---- non-atomic terms: the write-path reify + mint -----------------------
;; The write-mode reify (mint + result-type materialization + collision merge) lives in
;; `vaelii.impl.nat`, storing through the assert path via `vaelii.impl.wiring` — so all NAT
;; reification is in one namespace.  What stays here is dropping an orphaned reified NAT on
;; retract; skolemizing an existential head is `vaelii.impl.skolem`.
;;
;; `retract!` and `edit` are both forward-referenced and both defined far below, because
;; the write path and the query family are interleaved in this file:
;; `remove-orphaned-nats!` calls `retract!`, and `abduce` is handed `edit` to discard a
;; scratch context with.

(declare retract! edit!)

(defn- prepare-goal-for-read
  "Bring a `prove` / `query` goal (a sentence, or a vector of them = a conjunction)
  into the form the stored content is in, so a lookup can meet it: **reify** ground
  NATs to their existing constants, then **rewrite** terms to their equality-class
  representatives and schematic normal forms (`kb/rewrite-goal`).

  This is the parity every read path holds to, and the backward chainers need it as
  much as the rest: without the rewrite step a goal naming a merged spelling — or one
  an oriented equation would normalize — is answered by `sentexes-matching`/`ask` but
  silently missed by `prove`/`query`, and the same knowledge answers path-dependently.
  It is the **top** goal that is normalized, exactly as `sentexes-matching`/`ask`
  normalize theirs; stored facts are already in normal form (migration), so subgoals a
  rule expansion generates need no further rewriting — the same reliance `ask` makes.
  `rewrite-goal` exempts
  `different`, whose arguments must stay un-rewritten to read class membership.

  Rewritten by the merges `context` sees, since that is where the goal is asked."
  [kb goal context]
  (letfn [(prep [g] (kb/rewrite-goal kb (nat/maybe-reify-for-read kb (quasiquote/maybe-reduce kb g)) context))]
    (if (vector? goal) (mapv prep goal) (prep goal))))

;; ---- the assert opts roster ---------------------------------------------

(def assert-opt-keys
  "Every key `assert` / `assert-rule` reads.  Public for the same reason
  `kb/opt-keys` is: it is the answer to \"is this a real option?\", and a caller that
  can ask does not have to find out from a wrong answer.

  `:strength` is the assumption class, `:chain?` whether to forward-chain, `:direction`
  the programmatic spelling of a `set/*Rule` wrapper, `:creator` / `:provenance` the
  stamp; the rest flow to `chain/chain-all`."
  #{:strength :chain? :direction :creator :provenance
    :max-depth :max-derivations :on-progress :progress-every-ms})

(defn- context-shape-problem
  "The `:shape` problem a context slot of the wrong shape is refused with, or nil.  A
  context is a bare symbol — or a **context-function application** `(CxTimeFn …)` that
  actually reifies to its `cx/` constant before anything downstream reads it
  (docs/context-nat.md).

  The compound is admitted only when reification *would yield a symbol*: its head is a
  **declared** `contextDenotingFunction` and the application is ground
  (`nat/context-denoting-ground-nat?`).  This is a shape invariant — a stored sentex's
  context is always a symbol — so it must not depend on the naming policy: an undeclared
  `(CxBogusFn …)` or a non-ground `(CxTimeFn CxMonad ?x)` never reifies, would store a raw
  list as the context, and is refused here whatever `:naming` is set to (a lexical
  `Cx*Fn`-only check passed it to the naming door, which `:naming :off` then waves
  through)."
  [kb context]
  (when-not (or (symbol? context)
                (nat/context-denoting-ground-nat? kb context))
    {:type :shape :context context
     :message (str "the context must be a bare symbol or a ground application of a declared "
                   "context-denoting function (CxTimeFn …), got " (pr-str context))}))

(defn- sentence-shape-problem
  "The `:shape` problem a would-be assertion is refused with before it is even a sentence,
  or nil.

  A sentence is an s-expression.  Anything else names nothing the checks below can read:
  a string is the shape a failed EDN read hands back (`impl.cli`'s `read-arg`, the
  daemon's `:args`), and `nil` is what an absent one is.  Unrefused, both would
  *store* — indexed, marked a premise and believed, as an object no query can ever
  match — while a symbol, a number or a map reaches `nth` and throws a bare
  `UnsupportedOperationException` that carries no `:type`.

  **A list, and not a vector**, which is the second arm and the sharper one: a vector is
  `sequential?` too, and `sentex/canon` flattens it to the list it looks like, so
  `[likes Tom Ann]` stored the sentence `(likes Tom Ann)` and every write-side check
  passed.  The read doors do not read it that way.  A vector goal is a **conjunctive
  query** (docs/api.md), so `query` and `prove` handed the same spelling back join over
  the sentence's own elements as separate goals and answer nothing, silently, while
  `ask` and `sentexes-matching` canonicalize and find the fact — one spelling, two
  doors, opposite answers, no error from either.  The read side cannot be made to
  **accept** it — the conjunctive vector is what every query door means by one, and one
  spelling cannot mean two things — so the spelling that collides is refused here.  It
  is refused *there* too, by `sentence-goal-problem` and `conjunction-goal-problem`
  below: refusing at one door and canonicalizing at the others left the split live on
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
                   " — a vector is how every read door spells a conjunction, so this"
                   " spelling would store one sentence and ask for a join over "
                   (count sentence) ".  Write " (pr-str (apply list sentence)))}))

(defn- check-shape!
  "Throw the `:shape` refusal `check` reports for a context or sentence that is not one.

  Called in `shape-problems`' own precedence — context, then opts, then sentence — so the
  two doors refuse the same input for the same reason."
  [problem]
  (when problem
    (throw (ex-info (:message problem) (dissoc problem :message)))))

(defn- connective-shape-problem
  "The `:not-well-formed` problem a malformed connective frame is refused with, or nil
  — `sx/connective-problems` as one problem map, read by both doors right after the
  sentence shape so a `(not A B)`, a truncated `implies` or a bare-symbol rule
  literal is refused before it can store as an opaque fact or throw untyped."
  [sentence]
  (when-let [ps (seq (sx/connective-problems sentence))]
    {:type :not-well-formed :sentence sentence
     :message (str "not well-formed: " (str/join "; " ps))}))

(defn- quantity-shape-problem
  "The `:not-well-formed` problem a non-finite measure magnitude is refused with, or
  nil.  `##Inf` and `##NaN` are `number?`s, so `(QuantityIntervalFn 0 ##Inf Second)`
  stored cleanly — and then every duration and metric goal in the context threw a raw
  NumberFormatException out of the magnitude arithmetic, with no `:type` and no way
  back but retraction.  A magnitude must be finite to be a measure; a variable
  magnitude stays legal, since a rule antecedent binds it."
  [sentence]
  (when (sequential? sentence)
    (let [bad (fn [x] (and (number? x) (not (Double/isFinite (double x)))))
          q?  #{'QuantityFn 'QuantityIntervalFn}]
      (when-some [t (sx/some-form (fn [form]
                                    (and (sequential? form) (seq form)
                                         (q? (first form)) (some bad (rest form))))
                                  sentence)]
        {:type :not-well-formed :sentence sentence
         :message (str "not well-formed: a measure magnitude must be finite, got "
                       (pr-str t))}))))

(def ^:private direction-values
  "What a `:direction` opt may say — the three `set/*Rule` wrappers' values plus
  `:both`, which is what a bare `(implies …)` already is and so has no wrapper."
  (into #{:both} (vals sx/rule-direction-wrappers)))

(defn- direction-opt-problem
  "The problem an `opts :direction` carries, as a value, or nil when it is applicable.

  One fn read by both doors: `apply-direction-opt` throws what this returns and
  `check` reports it, so a `:direction` refusal is never one `check` cannot predict.

  Three refusals.  A value outside `direction-values` would otherwise wrap nothing
  (`rules/wrap-direction` returns the sentence untouched for a value it does not know)
  and the rule would store `:both` and forward-chain — the silent default the option's
  own validation exists to stop, reachable by the plural typo `:backwards`.  A
  direction on something that is not a rule names nothing.  And one that disagrees
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
          {:type :unknown-option :direction d :options (vec (sort direction-values))
           :message (str "unknown :direction " (pr-str d) " — assert takes "
                         (str/join ", " (map pr-str (sort direction-values)))
                         ".  A value nothing reads would wrap nothing, storing :both"
                         " and forward-chaining a rule that asked not to.")}

          (not (rules/rule-sentence? inner))
          {:type :unknown-option :direction d :sentence sentence
           :message (str ":direction " (pr-str d) " on a sentence that is not a rule"
                         " — a direction says when a rule is run, and " (pr-str sentence)
                         " concludes nothing.")}

          ;; already wrapped and agreeing — `assert-rule` wraps and then calls through
          ;; here with the same opts, so this is the ordinary path, not a special case
          (= written d) nil

          (some? written)
          {:type :unknown-option :direction d :written written :sentence sentence
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
  exists to avoid — the silent-default failure the roster's own docstring says the
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
  (when (map? opts)
    (when (and (contains? opts :strength)
               (not (strength/assertable? (:strength opts))))
      (throw (ex-info (str "unknown :strength " (pr-str (:strength opts)) " — assert takes "
                           (str/join ", " (map pr-str (sort strength/assertable)))
                           ".  Defeasibility past those two is stated with exceptWhen"
                           " on the rule, not with a class.")
                      {:type :unknown-option :strength (:strength opts)
                       :options (vec (sort strength/assertable))})))))

(defn assert
  "Assert `sentence` in `context` (default 'CxUniverse) as a JTMS premise: enforce
  naming, arg, and disjointness constraints, persist, index (trie + term index),
  mark IN, integrate into the taxonomy / rule index, then forward-chain.  A
  virtual set/forwardRule|backwardRule|inertRule wrapper directs the enclosed
  rule.  `opts` flows to chaining ({:max-depth ..}, {:chain? false}) and carries the
  assumption `:strength` (:default, the common case, or :monotonic for known-true
  content that no default may defeat and that is never sent to a solver).  A
  contradiction is resolved softly at settle time, never thrown.  A rule that
  concludes a conjunction is polycanonicalized into one rule per conjunct — then this
  returns the vector of their handles; otherwise it returns the single sentex handle.

  Records **provenance** for the created sentex: `:creator` (from `opts :creator`, else
  `*creator*`) and `:created` (from `*clock*`), plus any `opts :provenance` map merged
  in — read with `provenance`, extended with `add-provenance`.

  An `opts` key this fn does not read is **refused** (`:unknown-option`), as is a
  `:strength` outside `{:default :monotonic}` — see `assert-opt-keys`.  Both would
  otherwise store the sentence at a defeat class the caller did not ask for, which
  nothing downstream can tell from one that was asked for.

  **The sentence is a list, and a vector is refused** (`:shape`).  A vector is what
  every read door spells a *conjunction* with, so the one spelling would store a
  sentence and query a join — see `sentence-shape-problem`.

  **A KB whose belief was never built refuses this** (`:unrecovered-kb`), since every
  definitional check below would pass vacuously and the store would keep the result —
  `*write-unrecovered?*` is the opt that names what accepting one gives up."
  ([kb sentence] (assert kb sentence 'CxUniverse nil))
  ([kb sentence context] (assert kb sentence context nil))
  ([kb sentence context opts]
   ;; Before the shape guards and so before `*bulk-load?*` can skip anything: bulk mode
   ;; turns off the dedup walk this state has already lost, so it must not be the way
   ;; into it.
   (check-writable! kb "assert")
   ;; In `shape-problems`' precedence, so `check` and `assert` refuse the same input for
   ;; the same reason: a sentence that is not an s-expression would store in silence,
   ;; and one that is not sequential throws bare, with no `:type` to discriminate on.
   ;; The vector arm is the same failure at one remove — it stores, and then the read
   ;; doors read the spelling as a conjunction.
   (check-shape! (context-shape-problem kb context))
   (check-assert-opts! opts)
   (check-shape! (sentence-shape-problem sentence))
   (check-shape! (connective-shape-problem sentence))
   (check-shape! (quantity-shape-problem sentence))
   ;; Every leaf must survive the durable log: a non-serializable value (a function, an
   ;; atom) stores in memory and throws at write time on the first disk backend, so the
   ;; same assert would succeed or fail by backend.  Refused here, before anything is
   ;; stored, exactly as `shape-problems` reports it to `check`.
   (checks/check-encodable sentence)
   ;; Reify ground reifiable NATs to their opaque constants *before* anything else —
   ;; before `expand-consequent`, WFF, and the constraint checks — so the compound
   ;; never reaches the index and the minted constant's materialized types are in
   ;; place for the checks below (docs/nat.md).  Gated, so a KB with no
   ;; reifiableFunction is unaffected.
   (let [;; A context-denoting NAT `(CxTimeFn …)` in the context slot reifies to its `cx/`
         ;; constant here — the context-slot twin of the sentence reify below, since the
         ;; context argument is not on the sentence walk (docs/context-nat.md).  A no-op
         ;; unless the KB declares a contextDenotingFunction and this is a ground one.
         context  (nat/maybe-reify-context kb context)
         sentence (apply-direction-opt sentence opts)
         ;; a directly-asserted ground `(Quasiquote …)` reduces to its `(Quote E)` mention
         ;; form here, *before* the reify pass below turns `(Quote E)` into its constant —
         ;; so it never reaches the index as a raw structural compound.  Gated (docs plan).
         sentence (quasiquote/maybe-reduce kb sentence)
         sentence (nat/maybe-reify-nats kb sentence (:chain? opts true))
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
               mh (assert-exceptWhen-meta! kb h exc (:varmap (p/get-sentex (:records kb) h))
                                           context opts)]
           (stamp-provenance! kb mh opts)
           mh)
         ;; An inline-rule exceptWhen.  Run the whole-rule checks (naming,
         ;; range-restriction, stratification with the exception's negative edge,
         ;; exception closure, and the naming of the exception's own literals) on the
         ;; *wrapped* form before anything is stored, so a refused exception leaves no
         ;; bare rule behind — `assert-exceptWhen-meta!` checks again, but it runs
         ;; after the rule is stored and chaining, so a refusal only it made would
         ;; leave the bare rule believed and firing unguarded, with no handle returned
         ;; to retract it by.  Then store the rule(s) and attach the exception to
         ;; **each** — aligned against that conjunct's *own* canonicalization: a
         ;; conjunctive consequent splits into one rule per conjunct, and a self-join
         ;; tie group can be numbered differently by each (the consequent breaks the
         ;; tie), so one shared varmap would misalign the exception on a conjunct
         ;; whose numbering differs.
         (let [_       (check-rule-sentence kb sentence context)
               _       (sx/check-exception-closed (rules/antecedents (rules/inner-rule inner)) exc)
               ;; as written rather than aligned — naming reads functors and argument
               ;; spellings, which alpha-renaming does not touch
               _       (run! #(nm/check! (:naming kb) % context) exc)
               rule-hs (assert kb inner context opts)
               hs      (if (sequential? rule-hs) rule-hs [rule-hs])
               ;; the per-conjunct rule forms, in the same order `assert` stored them
               forms   (rules/expand-consequent inner)
               meta-hs (mapv (fn [h form]
                               (assert-exceptWhen-meta!
                                kb h exc
                                (:varmap (res/kb-sentex kb (rules/inner-rule form) context))
                                context opts))
                             hs forms)]
           (stamp-provenance! kb meta-hs opts)
           (if (= 1 (count meta-hs)) (first meta-hs) meta-hs)))
       ;; a rule with a head existential `(exists ?y C)` will skolemize when it
       ;; fires; declare its reifiable function *now*, before chaining, so a rule
       ;; that fires during its own assert already finds it (docs/skolem.md)
       (let [_ (when (skolem/has-existential-head? sentence)
                 (skolem/ensure-skolem-function kb))
             forms (rules/expand-consequent sentence)
             h     (if (next forms)
                     ;; A conjunctive consequent is ONE rule the caller wrote, stored as
                     ;; several.  Check every conjunct before storing any, so the split
                     ;; stays invisible: the whole rule is asserted or none of it is.
                     ;; Without this a refusal on a later conjunct left the earlier ones
                     ;; stored and firing.
                     (do (run! #(check-rule-sentence kb % context) forms)
                         (mapv #(assert-one kb % context opts) forms))
                     (assert-one kb (first forms) context opts))]
         (stamp-provenance! kb h opts)
         (when (and (nat/any-reifiable-functions? kb) (sequential? sentence))
           ;; A rename is an equality assert; its migration can collapse two NATs onto
           ;; one expression.  Restore the 1:1 constant↔expression invariant by merging
           ;; the collisions (only after an equality).
           (when (kb/equality-sentence? sentence)
             (nat/merge-colliding-nats! kb sentence))
           ;; A `functionCorrespondingPredicate` makes an application and a predicate
           ;; fact two spellings of one claim, so a value asserted after its
           ;; application was minted — or a declaration asserted after both — leaves
           ;; two terms standing for one object.  Equate them, or the KB's answer
           ;; depends on which arrived first (docs/nat.md).
           (nat/reconcile-correspondence! kb sentence)
           ;; Structural genlCx: a fact stored into a `Cx*Fn` context, or a
           ;; `contextArgSubrelation` declaration, may entail new genlCx edges between
           ;; sibling NAT contexts — materialize them, justified so they belief-follow
           ;; (docs/context-nat.md).  Inside the reifiable gate (a free in-memory read):
           ;; a `contextDenotingFunction` is a reify-kind, so any KB with a context NAT to
           ;; order already passes it, and one without any reifiable function has no cx/
           ;; context and nothing to reconcile — so the `any-context-subrelations?` index
           ;; read the producer gates on is never paid by a KB that reifies nothing.
           (context-nat/reconcile-genlCx! kb sentence context))
         h)))))

(defn assert-rule
  "Assert a rule (a sentex whose sentence is an implication) in `context`.
  `opts` may carry `:direction` (:forward | :backward | :inert | :both, default
  :both) — or use a set/*Rule virtual predicate with `assert`."
  ([kb antecedents consequent] (assert-rule kb antecedents consequent 'CxUniverse nil))
  ([kb antecedents consequent context] (assert-rule kb antecedents consequent context nil))
  ([kb antecedents consequent context opts]
   (rules/check-range-restricted antecedents consequent)
   ;; `:direction` is just the programmatic spelling of a set/*Rule wrapper — wrap
   ;; and hand it to the one rule path, where the sentex constructor turns it into
   ;; the record's :direction.  assert also splits a conjunctive consequent.
   (let [sentence (rules/wrap-direction (rules/rule-sentence antecedents consequent)
                                        (:direction opts :both))]
     (assert kb sentence context opts))))

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
  own check fns, so the two doors refuse the same input for the same reason with the
  same `:type`.  Nil when all three hold.

  The opts roster is checked here as well, so `check` answers for the *request* and not
  only for the sentence: an entry whose `:strength` is misspelt is admissible knowledge
  asserted at the wrong class, which is exactly what a batch critic exists to catch
  before it lands."
  [kb sentence context opts]
  (or (some-> (context-shape-problem kb context) vector)
      (some-> (problem (fn [] (check-assert-opts! opts))) vector)
      (some-> (sentence-shape-problem sentence) vector)
      (some-> (connective-shape-problem sentence) vector)
      (some-> (quantity-shape-problem sentence) vector)
      (some-> (problem (fn [] (checks/check-encodable sentence))) vector)))

(defn- fact-problems
  "The checks `assert-one` runs over a non-rule sentence, as values.  The virtual
  wrapper is peeled and a forced-decontextualized predicate's context substituted exactly as
  the assert path does, so what is checked is the sentence that would be stored."
  [kb sentence context]
  (let [sentence (rules/inner-rule sentence)
        pred     (nm/functor sentence)
        ;; the global property read, as on the assert path: storage placement
        context  (if (and pred (tax/has-prop? (:taxonomy kb) :forced-decontextualized pred))
                   special/universal-context context)]
    (first-problems
     [#(for [p (nm/blocking-problems (:naming kb) sentence context)]
         {:type :naming :sentence sentence :context context
          :message (str "naming invariant: " p)})
      #(some-> (problem (fn [] (checks/check-ground kb sentence context))) vector)
      #(for [p (special/wff-problems (:taxonomy kb) sentence)]
         {:type :not-well-formed :sentence sentence :message (str "not well-formed: " p)})
      #(some-> (problem (fn [] (checks/check-edge-stratified kb sentence context))) vector)
      #(some-> (problem (fn [] (checks/constraint-checks kb sentence context))) vector)])))

(defn- rule-problems
  "The pre-storage checks a rule must pass — per conjunct of its consequent, since
  `assert` checks every conjunct of a polycanonicalized rule before storing any of
  them.  Covers the imperative ban, range-restriction, naming, and stratification."
  [kb sentence context]
  (first-problems
   (for [form (rules/expand-consequent sentence)]
     #(some-> (problem (fn [] (check-rule-sentence kb form context))) vector))))

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
      (let [author (into #{} (vals (:varmap rsx)))
            loose  (remove author (distinct (mapcat #(filter sx/variable? (tree-seq sequential? seq %))
                                                    exc)))]
        (when (seq loose)
          [{:type :exception-not-closed :unbound (vec loose) :rule h
            :message (str "exception is not closed: " (pr-str (vec loose))
                          " unbound by the rule's antecedents")}])))))

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
    :not-range-restricted  a rule variable the antecedents never bind
    :not-indexable         a rule antecedent literal whose predicate is a variable
    :not-stratified        a cycle through negation the rule or edge would close
    :not-assertible        a `do/` imperative inside a rule
    :arg-type              an arg constraint on an argument
    :disjoint              a type membership the taxonomy separates
    :functional            a second, irreconcilable value for a functional slot
    :asymmetric            the converse of a claim a declared-asymmetric relation made

  plus `:unrecovered-kb`, which is about neither the request nor the knowledge but the
  KB: every write door refuses one whose belief was never built over the store it opened,
  and it refuses before reading the sentence at all, so it is reported alone and first.
  Absent under `*write-unrecovered?*`, where `assert` lands the write.

  Plus three that are about the *request* rather than the knowledge: `:shape` (the
  context is not a symbol, the sentence is not an s-expression, or it is a vector —
  which is how a read door spells a conjunction), `:unknown-option`
  (`opts` is not a map, an `opts` key `assert` does not read, a `:strength` that is
  not an assertable class, or a `:direction` that is unknown, on a non-rule, or
  contradicting the wrapper the sentence already carries — see `assert-opt-keys`) and
  `:not-checkable` (a top-level `do/` imperative — an instruction, which `check` will
  not run to find out what it does).

  Two of the definitional problems are **constraint-policy-dependent**, because
  `assert` is.  Under `:refuse` — the default — `check` reports a `:disjoint` or
  `:functional` clash, since `assert` would throw one.  Under `:arbitrate` it reports an
  *arbitrable* clash as nothing at all: `assert` admits the sentence and leaves `settle`
  to weigh the pair it forms, so there is no problem at the door to report.

  **Arbitrable is narrower than clashing**, and that is the half to read twice.  A clash
  against **known-true** content is refused under either policy — admitting it would
  store what the KB can never believe — so `check` reports one there whatever
  `:constraints` says.  `:asymmetric` reads the opposing class that way in *both*
  policies and is not policy-dependent at all.  What holds throughout is the promise
  this docstring opens with: `check` predicts what `assert` would do.

  The stages run in `assert`'s order and stop at the first that finds anything, since
  each later one reads the KB assuming the earlier ones held.  A rule is checked the
  way `assert` checks it — every conjunct of a conjunctive consequent — and an
  `exceptWhen` is checked as the wrapped rule plus the exception's closure.

  Two things `assert` does that `check` deliberately does not: it does not reify a
  ground reifiable NAT (that mints a constant, which is a write), and it does not
  evaluate an imperative.  Everything else is the same code on the same KB."
  ([kb sentence] (check kb sentence 'CxUniverse nil))
  ([kb sentence context] (check kb sentence context nil))
  ([kb sentence context opts]
   ;; The writability refusal is first because `check-writable!` is first in `assert` —
   ;; ahead of the shape guards, so that `*bulk-load?*` cannot be the way into a state
   ;; whose dedup walk is already gone.
   (or (unrecovered-problems kb "assert")
       (shape-problems kb sentence context opts)
       (some-> (direction-opt-problem sentence opts) vector)
       ;; From here on, the sentence `assert` would act on: the `:direction` opt
       ;; expressed as its wrapper (a no-op without one), exactly as `assert` does
       ;; before it splits or stores anything.  Cannot throw — the problem stage
       ;; above already answered for every refusal `apply-direction-opt` makes.
       (let [sentence (apply-direction-opt sentence opts)]
         (cond
           (sx/do-form? sentence)
           [{:type :not-checkable :sentence sentence
             :message (str "a do/ imperative is an instruction, not a sentence — "
                           "check reports what it would assert, and this asserts nothing")}]

           ;; `(ist Ctx S)` is not stored — it finds or creates S in Ctx, so that is
           ;; what there is to check
           (= sx/ist-functor (first sentence))
           (if-let [[ctx s] (ist-parts sentence)]
             (check kb s ctx opts)
             [(ist-shape-problem sentence)])

           :else
           (let [[exc inner] (rules/split-exceptWhen sentence)]
             (cond
               (and exc (sx/sentex-handle? inner))
               (first-problems
                [#(vec (exceptWhen-handle-problems kb inner exc))
                 #(exceptWhen-naming-problems kb exc context)])

               exc
               (first-problems
                [#(rule-problems kb sentence context)
                 #(some-> (problem (fn [] (sx/check-exception-closed
                                           (rules/antecedents (rules/inner-rule inner)) exc)))
                          vector)
                 #(exceptWhen-naming-problems kb exc context)
                 #(check kb inner context opts)])

               (rules/rule-sentence? (rules/inner-rule sentence))
               (rule-problems kb sentence context)

               :else
               (fact-problems kb sentence context))))))))

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
  composition whose honest answer is `false` — there is no handle, so it is not
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
  nil.  One fn read by both doors — `entry-problems` reports it and `edit` throws it —
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
    {:type :unknown-option :batch batch :options (vec (sort edit-batch-keys))
     :message (str "an edit batch must be a map of "
                   (str/join ", " (map pr-str (sort edit-batch-keys)))
                   ", got " (pr-str batch))}
    :else
    (or (when-let [unknown (seq (sort-by pr-str (remove edit-batch-keys (keys batch))))]
          {:type :unknown-option :unknown (vec unknown) :options (vec (sort edit-batch-keys))
           :message (str "unknown edit batch key" (when (next unknown) "s") " "
                         (str/join ", " (map pr-str unknown))
                         " — an edit batch reads "
                         (str/join ", " (map pr-str (sort edit-batch-keys)))
                         ".  A key nothing reads writes nothing and reports success,"
                         " and check-edit predicts no problem with it.")})
        ;; a known key holding something no entry can be pulled from — `{:add 5}` —
        ;; would raise a bare seq error out of both doors' iteration (over the daemon,
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
  result back in reads as a no-op success."
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
  handles included) and for naming an actually stored one (`:unknown-handle`); a nil
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
                  :message (str "no sentex is stored under handle " h)}))
             remove)))))

;; ---- batched assertion: settle once, not per assert ----------------------
;; Every `assert` settles belief (resolve contradictions, evaluate exceptions,
;; refresh supersession) after storing.  Settle recomputes belief from current
;; state, so a bulk load pays that reconciliation N times for one final answer.
;; Deferring it to the end is safe *because* belief is order-independent: chaining
;; still runs per assert, so the one closing settle sees the same stored state a
;; per-assert settle would have.

(defmacro with-deferred-settle
  "Run `body` — a batch of `assert` / `assert-rule` / `ist` calls on `kb` — with
  belief settled **once** at the end instead of after every assertion.

  A plain `assert` settles the JTMS before returning (resolve contradictions,
  evaluate `exceptWhen`, refresh supersession); a bulk load therefore pays that
  reconciliation once per fact.  Under this macro each assertion still stores and
  forward-chains, but the `settle` is deferred, and one `settle` runs after `body`.
  The result is identical belief — settle is computed from current state, not
  accumulated, and beliefs are order-independent — for one reconciliation instead of
  N.  Returns `body`'s value.

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
         outermost# (not *defer-settle?*)
         res#       (try
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
                        (when outermost# (tax/restore-depths (:taxonomy kb#)))
                        (throw t#)))]
     (when outermost# (settle/settle kb#))
     res#))

(defn assert-many
  "Assert every sentence in `sentences` (into one shared `context`, optional shared
  `opts`) with belief settled **once** at the end — the collection form of
  `with-deferred-settle`.  Returns the vector of handles, in input order (a sentence
  that expands to several — a conjunctive-consequent rule — contributes its vector,
  so the result is `mapv`-shaped, one entry per input sentence).

  For a bulk fact/rule load this is the fast path: N asserts, one settle."
  ([kb sentences context] (assert-many kb sentences context nil))
  ([kb sentences context opts]
   (with-deferred-settle kb
     (mapv #(assert kb % context opts) sentences))))

(defn bulk-assert-facts!
  "Load a large batch of **known well-formed, pairwise-distinct** ground facts into
  `context` on the fast path: `assert` under `*bulk-load?*` (skips the per-fact
  definitional checks — including the `arg` store query — the dedup trie-walk, and
  provenance) inside one `with-deferred-settle` (one belief reconciliation at the end),
  with `{:chain? false}` so no forward inference runs.  This is `assert-many` stripped
  of the machinery a trusted corpus import does not need — a corpus load, or the bench
  wload/w8x/w5x premise setup.

  Returns the vector of sentex handles, in input order.  The result is **identical** to
  loading the same facts one-by-one with plain `assert {:chain? false}` — same stored
  sentexes, same index, same beliefs, same `count-with-functor` — because the skipped
  work only validates or dedups; it never changes what is stored.  The caller owns the
  two preconditions the mode trades on: every fact is well-formed (the checks would
  have passed) and no two are the same sentence in the same context (the dedup would
  have missed).  Use plain `assert` / `assert-many` when either is in doubt.

  `opts` flows to each `assert` (e.g. `:strength :monotonic`); `:chain?` is forced
  false — a rule/consequent that needs forward firing is not a bulk-fact load.

  **`:on-progress` is the load's rate, and it is the only thing this door reports.**
  The callback is handed `{:phase :loading :done n :elapsed-ms ms :facts-per-sec r}`
  every 100,000 facts and `{:phase :done :total n :elapsed-ms ms :facts-per-sec r}`
  once the closing settle has run — so the last event covers the whole load, settle
  included, and is the number to compare across runs.  The key is `assert`'s own
  (`assert-opt-keys`), where it names the *chaining* callback; here it cannot mean that,
  since `:chain? false` is forced and no chaining runs, so it is read at this door and
  not passed down.  What one fact costs, phase by phase: docs/storage.md, \"What a bulk
  load costs\"."
  ([kb facts context] (bulk-assert-facts! kb facts context nil))
  ([kb facts context opts]
   ;; the `assoc` waits for `assert`'s own opts guard: run on a non-map it threw a
   ;; bare cast error where every other door answers `:unknown-option`
   (check-assert-opts! opts)
   (let [on-progress (:on-progress opts)
         opts        (-> opts (dissoc :on-progress) (assoc :chain? false))
         t0          (System/nanoTime)
         event       (fn [m done]
                       (let [ms (/ (- (System/nanoTime) t0) 1e6)]
                         (on-progress (assoc m :elapsed-ms ms
                                             :facts-per-sec (if (pos? ms)
                                                              (/ (double done) (/ ms 1000.0))
                                                              0.0)))))
         hs          (binding [*bulk-load?* true]
                       (with-deferred-settle kb
                         ;; the counting arm only when somebody is listening: a load with
                         ;; no callback pays nothing for the option it did not pass
                         (if on-progress
                           (let [n (volatile! 0)]
                             (mapv (fn [f]
                                     (let [h (assert kb f context opts)
                                           i (vswap! n inc)]
                                       (when (zero? (rem i 100000))
                                         (event {:phase :loading :done i} i))
                                       h))
                                   facts))
                           (mapv #(assert kb % context opts) facts))))]
     ;; after `with-deferred-settle` returns, so the closing reconciliation is inside
     ;; the rate rather than outside it
     (when on-progress (event {:phase :done :total (count hs)} (count hs)))
     hs)))

;; ---- non-atomic terms: orphan removal on retract -------------------------
;; The rename collision-merge (`nat/merge-colliding-nats!`) lives with the rest of the
;; reify in `vaelii.impl.nat`; what stays here is orphan removal, because it rides the
;; `retract!` sweep and reads its `*in-orphan-removal?*` re-entry guard.

(def ^:dynamic ^:private *in-orphan-removal?*
  "Bound true while `remove-orphaned-nats!` retracts orphaned reified NAT bookkeeping, so the
  nested `retract!`s do not re-enter the sweep."
  false)

(defn- remove-orphaned-nats!
  "Remove every reified constant no live use references any more — its `termOfUnit`
  map and materialized result types would otherwise dangle a raw `nat/` symbol.

  `sink` is the teardown's removal record (`integrate/*removed-sink*`), or nil to ask
  the whole KB.  With one, each round's candidates are the constants the sentexes
  removed since the last round named, and the cost is the region's rather than the KB's
  whole `termOfUnit` population's.

  **A removal is what makes a candidate, and belief is what settles one** — the two are
  not the same question and this arm does not treat them as one.  A use that merely stops
  being *believed* is not a use that went: a defeated premise is still in the store, still
  names its constant, and a relabel can restore it.  Collecting on that reading would
  delete the map while a stored sentence names the constant, and the restoring relabel
  would dangle the very `nat/` symbol the sweep exists to prevent — so a constant no
  removal named is not a candidate however its uses are labelled.  `orphan?` still reads
  belief, because that is the right question about a candidate: whether what is *left*
  referencing it is only its own bookkeeping.

  Loops to a fixpoint either way, since removing one orphan can orphan a nested one —
  the constant standing in the removed expression.  **The region grows with the loop**:
  the retractions below append to the same sink, so what one round's removals stopped
  referencing is exactly the next round's candidate set, and a cascade is found by the
  same rule that found the first orphan.  The guard bounds a pathological chain; the
  empty round is what normally ends it."
  [kb sink]
  (binding [*in-orphan-removal?* true]
    (loop [mark 0 guard 0]
      (let [removed (when sink @sink)
            orphans (if sink
                      (nat/orphaned-among kb (nat/constants-named-by (subvec removed mark)))
                      (nat/orphaned-constants kb))
            ;; realized before the first retraction below, not while it runs: what
            ;; counts as an orphan's bookkeeping is read off the bookkeeping itself,
            ;; so a set computed lazily is a set computed partly against a KB this
            ;; loop has already torn pieces out of
            handles (vec (distinct (mapcat #(nat/bookkeeping-handles kb %) orphans)))]
        (when (and (seq handles) (< guard 64))
          (doseq [h handles] (retract! kb h))
          (recur (count removed) (inc guard)))))))

(def ^:private forward-chain-opt-keys
  "Every key `forward-chain` hands the chaining fixpoint (`chain/chain-all`'s
  destructure) — the roster `check-forward-chain-opts!` holds an opts map to."
  #{:max-depth :max-derivations :on-progress :progress-every-ms})

(defn- check-forward-chain-opts!
  "Refuse an opts key `forward-chain` does not read, and a non-nil non-map `opts` —
  `check-assert-opts!`'s reasoning at this door.  Every key here is a *bound* or the
  window into one, so the silent-default failure is a run with no ceiling:
  `{:max-derivation n}` reads as no key at all and the chain runs unbounded, which on a
  KB with a productive rule set is precisely what the option was written to prevent."
  [opts]
  (opts/check! opts forward-chain-opt-keys "forward-chain"
               (str "An option nothing reads takes the default in silence,"
                    " which for a bound means running unbounded.")))

(defn forward-chain
  "Run forward chaining to a fixpoint over every believed sentex, then settle
  belief (resolve contradictions).  Returns {:derived n :truncated? bool}.

  `opts`: `{:max-depth n :max-derivations n}` bound the run, and `:on-progress` is a
  callback the fixpoint calls about four times a second (`:progress-every-ms`) with
  `{:derived n :pending n}` —
  the one window into a phase that otherwise says nothing for minutes.  It may throw to
  abort the run (a loader cancelling), in which case belief is left unsettled and the KB
  holds the conclusions the run had already placed.

  An `opts` key this fn does not read is **refused** (`:unknown-option`): every key
  here bounds the run or reports on it, so a misspelt one is a run with no ceiling."
  ([kb] (forward-chain kb nil))
  ([kb opts] (check-forward-chain-opts! opts)
             (let [result (chain/chain-all kb (jtms/in-datums (:tms kb)) opts)]
               (settle/settle kb)
               result)))

;; ---- the query family: which one to reach for ---------------------------
;; Five entry points answer a goal, and the axis that separates them is **how much
;; rule expansion each is willing to do**.  Pick by what you are asking:
;;
;;   query / query?     THE DEFAULT.  One door with one dial: no `:max-depth` and it
;;                      is `ask`; a `:max-depth` and it is the node engine, bounded
;;                      at that many rewrites.  Sentence or vector goal.
;;                      → binding maps
;;   ask / ask?         The prover registry alone — facts, the taxonomy closures,
;;                      transitivity, disjointness, inverse/symmetric metadata,
;;                      evaluable arithmetic, NAF, arg type inference.  Expands
;;                      **no rule**, so its cost is a property of the goal.
;;                      → binding maps
;;   prove / provable?  The *unbounded* backward chainer: facts and rules only, no
;;                      special provers, terminating on the data rather than on a
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
;; **sentex maps** (`{:id :sentence :context :truth ...}`); `query` / `ask` / `prove`
;; return **binding maps** (`{?x val ...}`); `lookup` returns
;; **level-result maps** (`{:level :handle :sentence :context :bindings}`).

;; ---- one spelling, one meaning, at every read door -----------------------
;;
;; A **top-level vector is a conjunction**.  That is the rule the query family already
;; runs on (`goal-conjunction`, `plan/explain`, the `::goal` spec: `seq?`, or a vector
;; of them), and the write door states it as its own refusal — `[likes Tom Ann]` is not
;; a sentence, because the same spelling is a join at `query` / `prove`
;; (`sentence-shape-problem`).
;;
;; The read doors split into two families and the rule has to reach both, since it is
;; the *pair* that made one spelling answer two ways.  `ask` / `ask?` /
;; `sentexes-matching` / `handle-of` read **one sentence**: handed a vector they
;; canonicalized it to the list it looks like, so `[likes Tom Ann]` was answered `true`
;; where `prove` and `query` joined over three symbols and answered nothing — and,
;; the other way round, a real conjunction `[(dog ?y) (parentOf Tom ?y)]` flattened into
;; a sentence nothing matches and came back **false**, which is the same defect wearing
;; the answer a caller is least likely to question.  So a vector is refused at those
;; doors, and at the conjunction doors every conjunct has to be a sentence.  Either way
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

(defn- sentence-goal-problem
  "The `:shape` problem a read door that takes **one sentence** refuses a top-level
  vector with, or nil.  `ask`, `ask?`, `ask-within`, `sentexes-matching` and
  `handle-of` read one, so the vector spelling would mean at this door what it means at
  no other — and it comes in both directions, a sentence written as a vector and a real
  conjunction handed to a door that cannot join.  The message names which one arrived."
  [goal]
  (when (vector? goal)
    {:type :shape :goal goal
     :message (if-let [as-list (sentence-spelled-as-a-vector goal)]
                (str "the goal must be a list, not a vector: " (pr-str goal)
                     " — a vector is how `query` and `prove` spell a conjunction, so this"
                     " spelling asks one sentence here and a join over " (count goal)
                     " there.  Write the sentence as a list: " (pr-str as-list))
                (str "this door reads one sentence, and " (pr-str goal)
                     " is a conjunction — a vector goal is its " (count goal)
                     " members joined on the variables they share.  Ask it with `query`"
                     " or `prove`, which join, or ask one of its conjuncts here"))}))

(defn- conjunction-goal-problem
  "The `:shape` problem a read door that takes a **conjunction** refuses a vector goal
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
  spelling the value test loses."
  [goal]
  (when (and (vector? goal) (some #(not (seq? %)) goal))
    (let [bad (first (remove seq? goal))]
      {:type :shape :goal goal :conjunct bad
       :message (str "a vector goal is a conjunction, so every conjunct must be a"
                     " sentence: " (pr-str bad) " is not, in " (pr-str goal) "."
                     (if-let [as-list (sentence-spelled-as-a-vector goal)]
                       (str "  Write one sentence as a list: " (pr-str as-list))
                       "  Write each conjunct as a list."))})))

(defn- ist-goal
  "`[goal context]` for a read whose goal may be an `(ist Ctx S)` — the sentence to ask,
  and the context to ask it in.

  `ist` reads here for the reason it writes at `assert`: `(ist Ctx S)` names the context
  S is about, so a read resolves it exactly as the write door does, **the named context
  winning over the argument**.  `(sentexes-matching kb '(ist CxA (p ?x)) 'CxB)`
  asks CxA, as `(assert kb '(ist CxA S) 'CxB)` writes CxA; resolving
  it the other way would answer about a context the caller did not name, and the two
  doors would disagree about what one form means.

  **Every read taking a sentence and a context takes one**, which is the whole rule and
  is why there is no list to remember: `sentexes-matching`, `handle-of`, `ask`, `prove`,
  `query`, `query-plan`, the two anytime forms, `why-not`'s sentence arity, and the three
  level diagnostics.  The reads that take neither cannot: `contexts-of` and
  `find-sentexes` take no context and ask *which* contexts hold a sentence, so a form
  naming one is not a question they have, and `isa?` / `genls` take a context but their
  subject is a **term** rather than a sentence.

  `lookup`'s level 0 takes a vector as an index path rather than as a conjunction, and
  needs no exemption: a path's elements are keywords and symbols, so none of them is a
  sequential form the conjunct scan below can mistake for a literal.

  Two shapes are refused rather than answered empty, both because the alternative is a
  read that reports nothing and looks like an answer.  A wrong arity is `assert`'s own
  `:shape`, one refusal on every door (`ist-shape-problem`).  An `(ist …)` **conjunct** of
  a join is `:not-well-formed`: conjuncts share their bindings, so a per-conjunct context
  is the antecedent question wearing a different frame, and it has the same answer — ask
  the whole conjunction in Ctx, or make S visible where the rest of it is asked
  (`sentex/ist-read-problem`)."
  [kb goal context]
  ;; The resolved context is reified read-mode (dedup, never mint): a `(CxTimeFn …)` slot
  ;; on a read door resolves to the `cx/` constant the write door minted, so a query
  ;; scoped to a NAT context meets the facts stored there — the read/write symmetry the
  ;; context-arg reify at `assert` owes its other half (docs/context-nat.md).  A never-seen
  ;; NAT context resolves to the `no-match` sentinel, so the read is scoped to nothing and
  ;; answers empty rather than minting a context to ask about.
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
      (if-let [[ctx s] (ist-parts goal)]
        [s (reic ctx)]
        (check-shape! (ist-shape-problem goal)))

      :else [goal (reic context)])))

(defn sentexes-matching
  "*Believed* sentexes matching `sentence` in `context` (context defaults to ?ctx).
  Literal (no subtype expansion); use `isa?` / rules for taxonomic queries, or `ask`
  for full inference (see the query-family guide above).  Belief-sensitive: a
  stored-but-disbelieved sentex (a defeated default) is excluded — use
  `sentex`/`find-sentexes` for raw introspection.

  Returns a seq of **sentex maps**.  The stable contract is the map keys — `:id`
  (the handle), `:sentence`, `:context`, `:truth`, and for a rule `:antecedent` /
  `:consequent` / `:direction` — so key into the result.  The concrete record type
  (`vaelii.impl.sentex/AtomicSentex` / `RuleSentex`) is an internal detail: do not `instance?`-
  test it or rely on it, only its keys.

  A ground reifiable NAT in the goal is reified to its existing constant first (dedup,
  never mint), so it matches the stored atomic form; an unknown NAT matches nothing.

  An `(ist Ctx S)` sentence asks S in Ctx, the named context winning over `context`
  (`ist-goal`).  A **vector** pattern is refused (`:shape`): this door reads one
  sentence, and a vector is a conjunction at `query` / `prove`."
  ([kb sentence] (sentexes-matching kb sentence '?ctx))
  ([kb sentence context]
   (check-shape! (sentence-goal-problem sentence))
   (let [[sentence context] (ist-goal kb sentence context)]
     (kb/sentexes-matching kb (nat/maybe-reify-for-read kb sentence) context))))

(defn ist
  "The ist operation: find or create sentence `s` in context `ctx`, returning its
  handle.  `(ist ctx s)` given to `assert` does the same — ist is never stored."
  [kb ctx s]
  (assert kb s ctx))

(defn handle-of
  "The handle of the sentex already storing `sentence` in `context`, or **nil**.

  The non-creating counterpart to `ist`.  `ist` is find-*or-create*, so using it to
  ask whether something is stored silently asserts it — and then retracting \"it\"
  retracts a sentex the caller just made.  This asks without writing, which is what
  you want to turn a sentence into a handle for `retract!`, `in?`, `why`, or
  `supporting-justifications`.

  Storage, not belief: a stored-but-defeated sentex still has a handle and is
  returned.  Test belief with `in?`, or use `sentexes-matching` (which filters it).

  A **ground** symmetric literal also probes its mirror, so `(siblingOf Ann Bob)`
  finds a stored `(siblingOf Bob Ann)`.

  Being ist's counterpart, it reads an `(ist Ctx S)` sentence the way `ist` writes one:
  S is looked up in Ctx, which wins over `context` (`ist-goal`).  And it refuses the
  vector spelling of a sentence for the reason `assert` does — one door cannot answer
  for a spelling the door it counterparts refuses to store."
  [kb sentence context]
  (check-shape! (sentence-goal-problem sentence))
  (let [[sentence context] (ist-goal kb sentence context)]
    (kb/find-sentex-handle kb sentence context)))

(defn handles
  "Every live sentex handle in the KB — premises and anything forward-derived alike,
  read straight off the record store.  The whole-KB counterpart to the context- and
  query-scoped readers (`sentexes-in-context`, `sentexes-matching`): where those answer
  \"what is here that I asked about,\" this answers \"what is here at all,\" the enumeration
  a content-addressing or audit pass folds over.  Storage, not belief — a stored-but-
  defeated sentex still has a handle and is returned; filter with `in?` for belief."
  [kb]
  (p/sentex-ids (:records kb)))

(defn sentex-handle
  "The `(sentexHandle <id>)` term that **names** the sentex stored at handle `n`.  A
  meta-sentex predicates about another sentex by carrying this term in an argument —
  `(exceptWhen <query> (sentexHandle H))` names the rule it qualifies, and a target-
  following predicate (`targetFollowingPredicate`) names the claim its reply hangs on —
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

  Only the shape and naming invariants are enforced (a materialized head is already
  well-formed); no constraint / wff / equality / chaining runs.  A **rule** is refused
  (`:not-indexable`) — a labeling labels atoms, and the reason is below.  `assert-inert`
  is additive, so no `!`; drop it with `retract!` on the returned handle.

  A KB whose derived state was never built refuses this exactly as it refuses `assert`
  (`:unrecovered-kb`).  Not premising is what makes an inert sentex harmless to belief;
  it is still *stored and indexed*, so a derived index that opened empty mints it a
  second handle for content the store already holds, which no later pass can merge."
  [kb sentence context]
  (check-writable! kb "assert-inert")
  ;; `assert`'s own shape guards, in its precedence — context, then sentence.  Without
  ;; them this door stores what every other door refuses: `nm/literals` of a
  ;; non-sequential sentence finds no literals to check, so a string or nil passes
  ;; vacuously and is stored as an object no query can ever match, and a non-symbol
  ;; context throws `:naming` where `assert` and `check` say `:shape`.
  (check-shape! (context-shape-problem kb context))
  (check-shape! (sentence-shape-problem sentence))
  (check-shape! (connective-shape-problem sentence))
  (check-shape! (quantity-shape-problem sentence))
  ;; this door persists and indexes too, so the same durable-log constraint holds
  (checks/check-encodable sentence)
  (nm/check! (:naming kb) sentence context)
  ;; ...and the one refusal that is this door's own.  A rule fires because
  ;; `index-rule-sentex` put its predicates in the rule index, and that runs where a rule
  ;; sentex is *created* — `assert-rule-sentence`'s new branch, and the generator mint.
  ;; So a rule stored here is one no chainer can reach, and it stays that way: asserting
  ;; the same rule afterwards resolves to this handle, takes the existing branch and does
  ;; not index it either, which leaves a *believed* rule that silently never fires.  That
  ;; is `check-generator`'s reasoning about the accepted-and-inert rule, at this door —
  ;; and nothing this primitive exists for wants one, a labeling's materialized truth
  ;; values being atoms and their negations.
  ;;
  ;; **Two inertnesses, and the message names the other one**, because the caller who
  ;; lands here usually wants it: `set/inertRule` is a rule that is believed, indexed and
  ;; browsable and fires neither way — the spelling for a rule kept as *documentation*,
  ;; a transitivity a cached closure computes instead (docs/taxonomy.md).  This door's
  ;; inertness is the sentex's: not a premise, so never believed at all.
  (when (rules/rule-sentence? (rules/inner-rule sentence))
    (throw (ex-info (str "a rule cannot be stored inert: nothing indexes it, so no"
                         " chainer can reach it, and a later assert of the same rule"
                         " resolves to the stored sentex and does not index it either."
                         "  For a rule kept as documentation — stored, indexed and"
                         " browsable, firing neither forwards nor backwards — assert"
                         " set/inertRule (or {:direction :inert}), which is the other"
                         " inertness: the rule is believed and never fires")
                    {:type :not-indexable :sentence sentence :context context})))
  (first (kb/find-or-create-sentex kb sentence context)))

(defn contexts-of
  "The contexts in which `sentence` is asserted."
  [kb sentence]
  (distinct (map :context (sentexes-matching kb sentence '?ctx))))

(defn context-of-agent
  "The canonical context for `agent` — `Alice` ↦ `CxAgentAlice`.  The engine
  projects an agent's modal beliefs into this context (`modalPredicate`, docs/belief.md);
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
  none.  `assert` stamps `:creator` / `:created` when a sentex is first created;
  `add-provenance` layers on application fields.  Removed when the record is retracted."
  [kb handle]
  (p/get-provenance (:records kb) (the-handle handle "provenance")))

(defn add-provenance
  "Merge `m` into `handle`'s provenance map (creating it if absent), returning the
  merged map.  For application-defined bookkeeping layered onto the creation record —
  source, confidence, review state — without touching `:creator` / `:created` unless
  `m` names them.  Provenance is metadata, not belief, so this is additive with no `!`.

  A nil `handle` records nothing and returns nil — there is no record to attach to,
  and `provenance` of nil answers nil, so the write and the read stay in agreement.  A
  non-handle (a vector of handles included) is refused (`:bad-handle`) rather than
  written under a key `provenance` would refuse to read back.

  **Not one of the doors an unrecovered KB refuses**, and deliberately: what
  `check-writable!` protects is content whose definitional checks would pass vacuously
  and whose dependency sweep cannot be computed, and provenance is neither.  It annotates
  a record that already exists, no check reads it, nothing rests on it, and re-running
  `recover` neither needs nor changes it — so annotating a store you are inspecting is
  exactly the thing to be able to do while its belief is unbuilt."
  [kb handle m]
  (when-some [h (the-handle handle "add-provenance")]
    (p/put-provenance (:records kb) h
                      (merge (p/get-provenance (:records kb) h) m))))

(defn- candidate-rules
  "Rules that could conclude `goal`, restricted to the backward-capable ones (the
  consequent index is complete, so it also holds forward-only and inert rules).

  A rule concluding a **spec** of the goal's predicate answers it too — a `(dog ?x)`
  conclusion satisfies an `(animal ?y)` goal — so the candidates are the intersection
  `specs(pred) ∩ rules-by-consequent` (`res/concluding-rule-handles`), the backward
  dual of forward chaining fanning a fact over its supertypes; `res/subsuming-unify`
  then binds the goal variable to the subtype instance.

  Each carries its `exceptWhen` guard, so `query` and `prove` build the argument
  and then discard it when the exception holds — the same decision forward chaining
  makes before placing a conclusion.  Blocking is a property of the rule, not an
  artifact of which chainer ran.

  A rule the asking context cannot see is not a candidate (`res/rule-visible-from?`):
  a rule is a sentex, inherited by the ordinary `genlCx` up-cone like everything
  else.  Nor is a rule the KB no longer believes (`res/rule-believed?`) — the
  consequent index posts on storage, so belief is asked of the record here exactly as
  forward chaining asks it of a trigger."
  [kb goal context]
  (->> (res/concluding-rule-handles kb (nm/functor goal) context)
       (map #(p/get-sentex (:records kb) %))
       (filter rules/backward-sentex?)
       (filter #(res/rule-believed? kb (:id %)))
       (filter #(res/rule-visible-from? kb context (:context %)))
       (map #(provers/parse-rule kb % context))))

(defn- goal-conjunction
  "Normalize `prove`'s goal argument into the vector of goals the DFS prover takes.

  The two shapes are told apart **structurally**, not by inspecting contents: a goal
  is a sentence, i.e. a seq/list like `(dog ?x)`; a conjunction is a **vector** of
  them, `[(dog ?x) (parentOf ?x ?y)]`.  Nothing else can be confused for either — a
  sentence is never a vector (`sentex/canon` normalizes stored and substituted
  sentences to `PersistentList` precisely so this stays true)."
  [goal]
  (if (vector? goal) goal [goal]))

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
  them to."
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
    {:auto? true}              pick one from the shape of the query

  nil — the default — is the shipped ordering, and costs nothing to leave alone.  Every
  tactician returns the same answer set (docs/inference.md), so this is a **latency**
  choice: an exhaustive run expands the same nodes whatever the order, and an ordering
  can only pay a consumer that stops early.  `:portfolio?` and `:auto?` reach only
  `prove`; a race has no partial answer to hand back, so `prove-within` takes the
  strategy and drives the ordinary stream."
  nil)

(defn- query-options
  "`*query-options*` as the node engine's opts map, with `max-depth` folded in."
  [max-depth]
  (cond-> (cond (nil? *query-options*)     {}
                (keyword? *query-options*) {:strategy *query-options*}
                :else                      *query-options*)
    max-depth (assoc :max-depth max-depth)))

(defn- query-depth
  "How deep a read expands rules: the caller's `opts`, else whatever a dynamic binding
  names.  nil — no depth anywhere — is the no-rule-expansion answer, and the one thing
  this must never do is invent a number (`query`'s docstring for why).

  The two dynamic channels are the ones `*query-engine*` already documents for routing a
  `prove` to the node engine, so a caller who has bound a depth for one read does not
  have to learn a second place to bind it for another."
  [opts]
  ;; A non-map `opts` and a non-positive `:max-depth` both read as "no depth", which is
  ;; not an error condition but a *different question* — the no-rule-expansion answer,
  ;; returned as if it were the bounded one the caller asked for.  `(query kb g c :oops)`
  ;; and `{:max-depth -3}` both did that silently.  Refused for `assert`'s reason: an
  ;; answer taken at a setting nobody chose is indistinguishable downstream from one
  ;; taken at a setting somebody did.  The key *roster* stays open, since the docstring
  ;; hands everything it does not name to the node engine.
  (when (and (some? opts) (not (map? opts)))
    ;; `:got` and not `:options`: every other door puts the *roster* under `:options`
    ;; (`opts/check!`), and this one has no roster to put there — the docstring hands
    ;; every key it does not name to the node engine — so naming the value that way
    ;; hands a caller reading the roster the thing it was refused for.
    (throw (ex-info (str "query options must be a map, got " (pr-str opts))
                    {:type :unknown-option :got opts})))
  (when (and (contains? opts :max-depth)
             (some? (:max-depth opts))
             (not (nat-int? (:max-depth opts))))
    (throw (ex-info (str "query :max-depth must be a non-negative integer, got "
                         (pr-str (:max-depth opts))
                         " — 0 permits no rule expansion (facts only), a real answer a"
                         " caller may ask for by name; a negative or non-integer depth"
                         " reads as no depth at all, which is that same answer taken at"
                         " a setting nobody chose.")
                    {:type :unknown-option :max-depth (:max-depth opts)})))
  (or (:max-depth opts)
      (when (map? *query-options*) (:max-depth *query-options*))
      inference/*max-depth*))

(defn prove
  "Backward-chain in `context` with the simple recur DFS prover; returns a vector of
  solution binding maps.  Type-aware (specificity) and context-aware (only facts
  visible from `context`).

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
  whose position is operational rather than logical are pinned — evaluables
  (`evaluate` / `lessThan` / `greaterThan`) never outrun what binds them, and a
  rule's recursive literal stays last so right-recursion is preserved.  Solution
  *order* within the returned vector is not part of the contract.

  **One solution per derivation, so equal binding maps repeat.**  A goal reachable
  two ways — a stored fact that forward chaining already materialized *and* the rule
  that concludes it, or two rules with the same consequent — comes back twice, with
  the two maps equal.  `(count (prove …))` is therefore a count of proofs, not of
  answers: wrap it in `distinct` for an answer set, or reach for `query` / `ask`,
  which project to the goal's variables and answer each binding once.

  `query-plan` on the same vector shows the chosen order and why.  An `(ist Ctx S)` goal
  proves S in Ctx, the named context winning over `context`; one standing as a *conjunct*
  is refused, a join having no per-literal context (`ist-goal`).  A conjunct that is not
  a sentence is refused too (`:shape`) — `[likes Tom Ann]` is the sentence spelling of a
  vector, which is three goals here and nothing the KB can hold."
  ([kb goal] (prove kb goal '?ctx))
  ([kb goal context]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)
         goal  (prepare-goal-for-read kb goal context)
         goals (goal-conjunction goal)]
     (if (inference-engine? nil)
       (inference/solutions kb goals context (query-options nil))
       (res/prove kb (fn [g] (candidate-rules kb g context)) goals context)))))

(defn provable?
  "Is `goal` provable in `context`?  Takes the same single-sentence or vector-of-
  sentences conjunction as `prove`; a conjunction is provable iff all its conjuncts
  are, under one consistent binding of their shared variables."
  ([kb goal] (provable? kb goal '?ctx))
  ([kb goal context] (boolean (seq (prove kb goal context)))))

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
  rather than flattened into a sentence and answered `false`."
  ([kb goal] (ask kb goal '?ctx))
  ([kb goal context]
   (check-shape! (sentence-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)]
     (provers/ask kb (prepare-goal-for-read kb goal context) context))))

(defn ask?
  "Is `goal` answerable via the prover engine?  `ask`'s caveats are this one's too —
  in particular it expands no rule."
  ([kb goal] (ask? kb goal '?ctx))
  ([kb goal context] (boolean (seq (ask kb goal context)))))

(defn query
  "Answer `goal` in `context` — the front door — as a seq of **binding maps**
  (`{?x val …}`) projected onto the goal's own variables.

  `goal` is a sentence, or a **vector** of them: a conjunctive query whose shared
  variables join, exactly as `prove` takes.

  `opts` makes one decision, and it is **how deep to expand rules**:

      (query kb goal ctx)                   no rule expansion — the registry alone
      (query kb goal ctx {:max-depth 3})    the node engine, ≤3 rewrites deep

  **There is no default depth, deliberately.**  A bound decides which derivations
  exist, so a number chosen here would be this namespace quietly answering a question
  that belongs to the application: find the smallest depth that answers yours and pass
  it.  Without one the answer is whatever needs no rule, which is a real answer and not
  a degenerate case — most of a common-sense KB's reads are stored facts and cached
  closures.

  The depth may also come from `*query-options*` `:max-depth` or `inference/*max-depth*`,
  which is where `prove` reads it from too — so one dynamic binding sets the depth for
  every read in its scope.  `opts` wins over both.  Neither has a default, so a depth
  bound nowhere stays the no-rule-expansion answer rather than a number nobody chose.

  **`{:proof? true}`** changes the result shape to `[{:bindings … :proof …}]`, one
  **justification tree** per answer — the derivation the search took, reading the way
  `why` does (`:goal` / `:via` / `:because`).  `why` explains a *stored* belief by
  reading the JTMS; this explains an *ephemeral* one by reading the search, and the two
  are deliberately one shape.  Needs a depth, since without one no rule was expanded and
  there is no derivation to show.

  Everything else in `opts` is the node engine's, defaulting from `*query-options*` —
  `:strategy` (`vaelii.impl.tactics`), `:portfolio?`, `:auto?`, `:first-result?` — and
  is ignored where no depth sends the query there.

  Two things this is not.  `prove` is the *unbounded* backward chainer: it terminates
  on the data rather than on a bound, so it answers a chain deeper than any depth you
  would have guessed, at the cost of facts-and-rules only.  `sentexes-matching` is the
  belief-filtered index read, and returns sentexes rather than bindings."
  ([kb goal] (query kb goal '?ctx nil))
  ([kb goal context] (query kb goal context nil))
  ([kb goal context opts]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)
         d     (query-depth opts)
         goals (goal-conjunction (prepare-goal-for-read kb goal context))]
     (cond
       ;; a depth: the node engine, whose leaf is the registry — so an antecedent is
       ;; answerable by *any* prover (transitivity, an evaluable, a calculus, an inferred
       ;; argument type) and the engine is left doing only what it is for, which is
       ;; expanding rules.  `prove`'s leaf is the stored facts instead, which is the whole
       ;; difference between the two.
       (and d (pos? (long d)))
       (inference/solutions kb goals context
                            (merge (query-options nil) opts
                                   {:max-depth    d
                                    :leaf-solver  provers/solve-goal
                                    ;; the cost model that leaf is answered by, so the
                                    ;; node engine's inline join plans on what a conjunct
                                    ;; will actually cost rather than on what the index
                                    ;; counts — the pair `prove-seq` is handed below
                                    :est-override (provers/registry-est-override kb context)}))

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
                      {:max-depth    0
                       :leaf-solver  provers/solve-goal
                       :est-override (provers/registry-est-override kb context)})))))

(defn query?
  "Is `goal` answerable under `opts`?  `query`, asked for one answer."
  ([kb goal] (query? kb goal '?ctx nil))
  ([kb goal context] (query? kb goal context nil))
  ([kb goal context opts]
   ;; the `dissoc` waits for the map: run on a non-map it threw a bare cast error
   ;; before `query`'s own guard could type the refusal, so the two doors disagreed
   ;; on the one input class `query?` exists to mirror
   (boolean (seq (query kb goal context (cond-> opts (map? opts) (dissoc :proof?)))))))

(def ^:private abduce-ops
  "Everything `vaelii.impl.abduce` needs from this namespace and does not name: the
  candidate chooser it searches with, and the `assert` / `edit` it mints and discards
  hypotheses through — see that namespace's \"the seam\" note for why abduction can be
  handed these where a NAT mint cannot.

  `assert` and `edit` as **vars** rather than values, because both are defined below this
  point; `candidate-rules` is above it and needs no such thing."
  {:rules-fn candidate-rules :assert #'assert :edit #'edit!})

(defn abduce
  "What would have to be true for `goal` to be provable in `context`.

  `prove` answers whether a goal follows.  This answers what it is *missing*: it runs
  the same backward search, watches where the proof dead-ends, and **hypothesizes** the
  missing subgoal — as an ordinary `:default` premise in a scratch context hung
  below `context`, so the assumption sees everything the question could see and nothing
  that existed before can see the assumption.

      {:solutions   [binding-map …]     under the hypotheses, not instead of them
       :hypotheses  [{:sentence :context :handle} …]
       :refused     [sentence …]        dead ends the gate would not assume
       :context     CxAbductionX
       :status      :complete | :capped}

  An empty `:hypotheses` means the goal was proved outright.  Otherwise the solutions hold
  **given** those sentences — which is why they come back together, and why there is no
  arity that returns the solutions alone.  They are `prove`'s solutions either way,
  unprojected, so they carry a rule's canonical variables; and because a hypothesis is
  minted through the whole `assert` pipeline, chaining included, a goal a rule concludes
  is usually answered *twice* over — once as the fact that firing stored in the scratch
  context, once by the rule expanded over the hypothesis.

  **A predicate is hypothesized only if it was granted.**  `(abduciblePredicate P)`
  is what makes a `(P …)` assumable, read from the asking context's `genlCx`
  up-cone; nothing else is, ever.  A hypothesis must also be **ground**, must pass every
  check an assertion passes, and must not contradict anything believed where it lands.
  An abducer without those explains everything and is worth nothing.

  It is **defeasible**, needing no rule of its own: a `:monotonic` fact that contradicts
  a hypothesis defeats it through the ordinary path, and what the hypothesis licensed
  goes OUT with it.

  `opts` carries the caps — `:max-hypotheses` (default 8) and `:max-depth` (8), the rule
  depth past which a dead end is left alone — plus **`:keep?`**.  Without it the scratch
  context is torn down before returning, so **a call whose result you ignore leaves the
  KB as it found it**; with it the context stands, the handles are real, and you discard
  it with `abduce-discard!`.  Committing a hypothesis to a context that outlives the
  scratch is deliberately yours to do: abduction proposes.

  The hypothesis set is **irredundant** — no single member can be dropped and still
  answer the goal — which is not the same as minimum.  See docs/abduction.md."
  ([kb goal] (abduce kb goal 'CxUniverse nil))
  ([kb goal context] (abduce kb goal context nil))
  ([kb goal context opts]
   ;; the caps are bounds and `:keep?` decides whether the scratch context survives,
   ;; so a misspelt key is a run at defaults nobody chose — or handles the caller
   ;; meant to keep, torn down before returning
   (check-bound-opts! opts #{:max-hypotheses :max-depth :keep?} "abduce")
   ;; the same conjunction `prove` takes, so the same reading of a vector
   (check-shape! (conjunction-goal-problem goal))
   ;; `:not-ground`, the type an open sentence already refuses under: the hypotheses
   ;; have to be stored somewhere, and `?ctx` — which every other query fn reads as
   ;; "any context" — names none.
   (when-not (and (symbol? context) (not (sx/variable? context)))
     (throw (ex-info "abduce needs a concrete context to hang its hypotheses below"
                     {:type :not-ground :context context})))
   (abduce/run kb (goal-conjunction (prepare-goal-for-read kb goal context))
               context opts abduce-ops)))

(defn abduce-discard!
  "Discard an abduction's scratch context — every hypothesis in it, and everything they
  licensed.  Takes the result of a `{:keep? true}` `abduce` (or the context symbol
  itself) and answers `{:removed-sentexes n :removed-justifications n}`.

  Idempotent, and unnecessary after a plain `abduce`, which discards on its own way out.
  One `edit`, so the dependency-directed sweep takes the derived content with the
  premises it rested on."
  [kb result]
  (abduce/discard! kb (if (map? result) (:context result) result) abduce-ops))

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
  the conjuncts in the order they will actually run, the variables already bound when
  each starts, and **what decided its position**.

  Three numbers, because the decision turns on three.  `:est-matches` is the sound
  upper bound on this literal's own fan-out under the bindings in hand — what proves a
  literal cannot multiply.  `:est-rows` is the expected size of the relation it
  denotes, on its own.  `:est-prefix` is the expected size of the whole plan up to and
  including it, which is the number a join was actually costed in: a literal placed
  early on a small `:est-matches` whose `:est-prefix` then jumps is the cost model
  being wrong about a *join* rather than about a literal.

  And the flags: an operational pin (`:deferred?` / `:recursive?`), being a cartesian
  factor held to the back (`:isolated?` — sharing no variable with the rest *and* able
  to multiply it; a literal matching at most once leads instead), and `:block`, the
  group of literals it moved with.  Literals sharing a variable are one block and run
  together, and a whole block can be held back the way a single literal is.

    (query-plan kb '[(dog ?y) (parentOf Tom ?y)] 'CxMantle)
    ;; => ({:goal (parentOf Tom ?y) :est-matches 2 :bound-before #{}    ...}
    ;;     {:goal (dog ?y)          :est-matches 1 :bound-before #{?y}  ...})

  Note the second literal is estimated *under the binding the first produced*, which
  is why the pair does not read as a sorted list of independent costs."
  ([kb goal] (query-plan kb goal '?ctx))
  ([kb goal context]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)]
     (if (vector? goal)
       (plan/explain kb goal context)
       (provers/plan kb goal context)))))

(defn search-tree
  "The backward search for `goal` in `context`, as data — every node the frontier reached,
  not only the path that answered.  `query-plan` is the plan; this is the run that plan
  predicted, one step later: where `query {:proof? true}` returns the proof that *worked*,
  this returns the whole tree it worked in — the frontier, what each node cost, and what
  got dropped before it was expanded.  The read behind the inference debugger.

  Needs a depth (`{:max-depth n}`, or `*query-options*` / `inference/*max-depth*`), the
  same as `query` under `:proof? true` and for the same reason: with no rule expanded there
  is no search to show.  It runs the search `query` runs — the registry as the leaf, so an
  antecedent is answerable by any prover — so the tree and the answers match `query`'s.

  Bounded so a large KB cannot turn one read into an unbounded search: the depth bound, a
  node-expansion budget (`:node-budget`, default `inference/default-node-budget`), and an
  optional wall-clock `:max-ms` that reports `:timeout` rather than hanging.  Everything
  else in `opts` is the node engine's, `query`'s `:strategy` included.

  Returns `{:goals :context :strategy :status :bounded? :answers :nodes :stats}`;
  `:status` is `:complete`, `:bounded` or `:timeout`, and each answer carries the `:node`
  it came off.  Reads-only, like every query in this engine."
  ([kb goal] (search-tree kb goal '?ctx nil))
  ([kb goal context] (search-tree kb goal context nil))
  ([kb goal context opts]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)
         d     (query-depth opts)
         goals (goal-conjunction (prepare-goal-for-read kb goal context))]
     (inference/search-tree kb goals context
                            (merge (query-options nil) opts
                                   {:max-depth    d
                                    :leaf-solver  provers/solve-goal
                                    :est-override (provers/registry-est-override kb context)})))))

(defn compare-tacticians
  "Run `goal` in `context` under several **tacticians** — the node engine's search
  orderings — each to completion, and return one row per tactician: the search it ran, its
  wall-clock, and its answer set.  What the debugger tables side by side.

  Every tactician only reorders the frontier, so the answer sets **must be identical**;
  the point of running them side by side is that a caller can verify it rather than trust
  it, and see the latency each ordering pays for the same answers.  A row whose answers
  differ from the others is a bug the completeness sweep says cannot happen — surfaced,
  not swallowed.

  `opts` is `search-tree`'s, plus `:tacticians` — the subset to run
  (`inference/default-compare-tacticians` otherwise).  Needs a depth for the same reason
  `search-tree` does, and is bounded the same three ways; `:status` and `:ms` are per row."
  ([kb goal] (compare-tacticians kb goal '?ctx nil))
  ([kb goal context] (compare-tacticians kb goal context nil))
  ([kb goal context opts]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)
         d     (query-depth opts)
         goals (goal-conjunction (prepare-goal-for-read kb goal context))]
     (inference/compare-tacticians kb goals context
                                   (merge (query-options nil) opts
                                          {:max-depth    d
                                           :leaf-solver  provers/solve-goal
                                           :est-override (provers/registry-est-override kb context)})))))

(defn add-prover
  "Register an additional prover (implementing vaelii.impl.provers/Prover) on `kb`."
  [kb prover]
  (swap! (:provers kb) conj prover) kb)

(defn register-modal-predicate!
  "Grant `pred` belief-style projection: after this, `(pred agent sentence)` is answered
  by proving `sentence` in `agent`'s context, exactly as `believes` is (see
  docs/belief.md).  A thin convenience over asserting the `(modalPredicate pred)` marker
  — the grant is an ordinary belief, so it follows retraction and, read scoped, is a
  *policy of the context* that holds it: with no `context` it is granted in `CxCore`
  where the default `believes` grant lives, so every ordinary query context sees it;
  pass a `context` to scope the grant to the theory that wants it.  Returns `kb`."
  ([kb pred] (register-modal-predicate! kb pred 'CxCore))
  ([kb pred context] (assert kb (list 'modalPredicate pred) context) kb))

;; ---- the optional reasoners ---------------------------------------------
;; Eight reasoners ship without being registered, and until one is, its vocabulary is
;; ordinary content: a KB stores `(before A B)` and `(before B C)`, retrieves both, and
;; does not derive `(before A C)`.  That is the right default — an algebra's fixpoint is
;; not free, and most KBs use none of them — but the *provers* live in `vaelii.impl.*`,
;; and `vaelii.core` is the only namespace anything outside this repo may name.  So
;; without a roster here, opting in means reaching past the boundary, and a subsystem
;; nobody can ask for is one nobody has.
;;
;; Named by keyword and resolved at runtime, so requiring this namespace does not drag
;; in eight leaf algebras — the same discipline `calculus-vars` and `imperative` use.

(def ^:private reasoner-vars
  "The reasoners a KB can register, and the var holding each one's constructor.  Six are
  the relation algebras `calculi` describes; `:duration` and `:metric-time` are the
  quantitative pair over the same intervals and instants (docs/duration.md,
  docs/stp.md)."
  '{:rcc8        vaelii.impl.space/spatial-prover
    :cardinal    vaelii.impl.orientation/orientation-prover
    :relative    vaelii.impl.relative/relative-prover
    :distance    vaelii.impl.distance/distance-prover
    :allen       vaelii.impl.interval/allen-prover
    :point       vaelii.impl.point/point-prover
    :duration    vaelii.impl.duration/duration-prover
    :metric-time vaelii.impl.stp/stp-prover})

(defn reasoners
  "The names of the optional reasoners, sorted — what `add-reasoner` takes.  `calculi`
  describes the six that are relation algebras in full; these two are the rest of the
  roster."
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
                    {:type :unknown-option :reasoner nm :known (reasoners)}))))

(defn add-reasoner
  "Register one or more shipped reasoners on `kb` by name, returning `kb`.

      (doto (open-kb {}) (add-reasoner :allen :rcc8))

  Registration is the whole of the opt-in, and it is per-KB: an unregistered algebra's
  facts are stored and retrieved as ordinary facts and cost nothing.  Registering
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
                    {:type :unknown-option :calculus nm
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

(defn qualitative-network
  "The constraint network `calculus` computes over everything **believed and visible**
  in `context`: every pair of terms its predicates relate, tightened by path
  consistency to the base relations still possible between them.

    {:calculus :rcc8  :context CxWell
     :nodes [A B C]   :consistent? true
     :constraints {[A B] #{:ntpp} [B A] #{:ntppi} …}}

  A pair constrained to one relation is pinned; a pair with several is genuinely open;
  an unrecorded pair is unknown (every base relation).  When the believed facts are
  unsatisfiable `:consistent?` is false, `:constraints` is the network **as stated**
  rather than a tightened one, and `:unsatisfiable` names the pairs no model satisfies
  as written — empty when only composition found the clash, which is the case with no
  single pair to blame."
  [kb calculus context]
  (let [calc  (the-calculus calculus)
        net   (qkb/network kb calc context)
        ns'   (qkb/nodes net)
        pc    (qkb/tighten kb calc context net nil)
        bad?  (= :inconsistent pc)]
    (cond-> {:calculus    calculus
             :context     context
             :nodes       (vec (sort-by str ns'))
             :consistent? (not bad?)
             :constraints (if bad? net pc)}
      bad? (assoc :unsatisfiable (vec (sort-by str (qcn/unsatisfiable-pairs
                                                    net (:algebra calc))))))))

(defn possible-relations
  "The base relations `calculus` still allows between `a` and `b`, given everything
  believed in `context` — the set `ask` checks a goal against, exposed directly.  A
  singleton is a pinned arrangement; the full set is total ignorance; `#{}` means the
  network is unsatisfiable and no goal of that calculus is answered there."
  [kb calculus context a b]
  (qkb/possible (the-calculus calculus) kb context a b))

(defn qualitative-scenario
  "One concrete arrangement consistent with everything believed in `context` —
  `{[a b] → relation}`, one base relation per pair — or nil when the believed facts are
  unsatisfiable.  Which arrangement is a function of the facts alone, never of the
  order they arrived, so it is repeatable and comparable across KBs.

  Path consistency leaves a *set* per pair; this picks one member of every set at once,
  which is the difference between \"nothing rules this out\" and \"here is a world\"."
  [kb calculus context]
  (some-> (scenario/scenario (the-calculus calculus) kb context) scenario/relations))

(defn qualitative-scenarios
  "Up to `limit` distinct arrangements, as `qualitative-scenario` renders one.  The
  number of scenarios is exponential in the node count, so the bound is required rather
  than optional — an unbounded enumeration is not something to reach for by accident."
  [kb calculus context limit]
  ;; typed, not a cast error: over the daemon a string limit answered
  ;; `500 :internal-error` where the sibling `find-terms :limit` refusal is typed
  (when-not (pos-int? limit)
    (throw (ex-info (str "qualitative-scenarios limit must be a positive integer, got "
                         (pr-str limit))
                    {:type :unknown-option :limit limit})))
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
  contract `{:results :status :count :elapsed-ms :resume}` (see
  vaelii.impl.budget): `:results` are the solutions realized in *this* step,
  `:status` is `:complete` / `:timeout` / `:capped`, and `:resume` (nil when
  `:complete`) continues the same search under a fresh budget via `resume`.

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
   ;; `ask`'s door, since this is `ask` bounded: a goal it refuses cannot be one this
   ;; answers, or the budget would decide which spelling is legal
   (check-shape! (sentence-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)]
     (budget/collect (provers/ask-capped kb (prepare-goal-for-read kb goal context)
                                         context (:max-cost budget))
                     budget))))

(defn- run-prove-step
  "One bounded step of the DFS prover, wrapped in the anytime contract.  The
  continuation captures the *remaining* goal stack, so `resume` picks the search up
  exactly where it stopped rather than restarting it.

  The budget is rostered here as well as in `budget/collect`, because this is the one
  consumer that does not go through `collect` — the DFS arm reads its bounds directly,
  and a `resume` hands each step a fresh budget of its own to hold to the roster."
  [kb context budget stack]
  (budget/check-budget! budget)
  (let [rules-fn (fn [g] (candidate-rules kb g context))
        bounds   {:deadline    (budget/deadline budget)
                  :max-results (:max-results budget)
                  :max-depth   (:max-depth budget)}
        start    (System/nanoTime)
        {:keys [solutions status stack]} (res/prove-from kb rules-fn context bounds stack [])]
    (budget/from-batch solutions status start
                       (fn [b] (run-prove-step kb context b stack)))))

(defn prove-within
  "Anytime `prove`: run the depth-first backward chainer over `goal` (a sentence or a
  conjunction vector, as `prove`) in `context`, bounded by `budget` — a map of any of
  `{:max-ms n :max-results n :max-depth n}`.  Returns the same partial-result
  contract as `ask-within`, and `resume` continues from the unfinished goal stack.

  `:max-depth` bounds *transformation* depth — the number of rule expansions the
  search may stack — so a runaway or merely deep proof yields a `:timeout` /
  `:capped` partial you can inspect and then `resume` with a larger budget.
  (`:max-cost` is an `ask` concept — `prove` runs only facts and rules — and is
  ignored here.)"
  ([kb goal budget] (prove-within kb goal '?ctx budget))
  ([kb goal context budget]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context] (ist-goal kb goal context)
         goals (goal-conjunction (prepare-goal-for-read kb goal context))]
     (if (inference-engine? (:max-depth budget))
       ;; the node engine's continuation *is* the unrealized tail of its result
       ;; stream, and the frontier behind it is a value the session holds — so a
       ;; bounded run needs nothing this engine does not already have
       (budget/collect (inference/search-seq
                        (inference/session kb goals context
                                           (query-options (:max-depth budget))))
                       budget)
       (run-prove-step kb context budget
                       (res/initial-prove-stack kb goals context))))))

(defn resume
  "Continue a `:timeout` / `:capped` partial result from `ask-within` / `prove-within`
  under a fresh `budget`, returning the next partial result.  A `:complete` result
  has no continuation and is returned unchanged, so

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
    3 :visible  + genlCx inheritance     7 :proved   full stack

  A lazy seq of {:level :handle :sentence :context :bindings}; a field the level
  cannot supply is nil (levels 5-7 derive answers, so they carry no handle).  Each
  level adds one mechanism to the one below, so an answer that appears at level n
  and not at n-1 is attributable to that mechanism.

  At level 0 a *vector* goal is taken as an index path directly; anywhere else the
  goal is a sentence."
  ([kb level goal] (lookup kb level goal '?ctx))
  ([kb level goal context]
   (let [[goal context] (ist-goal kb goal context)]
     (lvl/lookup kb level goal context))))

(defn escalate
  "The cheapest level that answers `goal` — climb the stack from `floor` and stop at
  the first level with results.  Returns {:level :name :results :tried}; `:results`
  is that level's lazy seq, so the climb costs one result per level tried.  Nothing
  answers → :level nil.

  `floor` defaults to 2, the first level that answers a *goal* rather than a
  question about storage: level 1 ignores the goal's arguments and level 0 ignores
  belief, so either can report a hit it cannot verify.  Pass 0 to include them."
  ([kb goal] (escalate kb goal '?ctx))
  ([kb goal context]
   (let [[goal context] (ist-goal kb goal context)]
     (lvl/escalate kb goal context)))                ; `levels/query-floor` owns the default
  ([kb goal context floor]
   (let [[goal context] (ist-goal kb goal context)]
     (lvl/escalate kb goal context floor))))

(defn explain-levels
  "What every level yields for `goal`: a seq of {:level :name :count}.  The level at
  which the count first rises is the machinery the answer depends on.  A diagnostic —
  it counts, so unlike `lookup` it realizes every level fully.

  This explains the *retrieval stack*, not belief: it says which machinery reaches a
  sentence, not why the KB holds it.  For that, see `why` / `why-not`, which walk the
  justification graph."
  ([kb goal] (explain-levels kb goal '?ctx))
  ([kb goal context]
   (let [[goal context] (ist-goal kb goal context)]
     (lvl/explain kb goal context))))

(defn levels
  "The stack as data: {:level :name :below :adds} per level."
  [] lvl/level-table)

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
  to do.  Nothing here is stored: a clash is recomputed from current belief each settle
  and `(contradicts X Y)` is a report form, never a sentex.

  **The list is ordered by content** — each entry by its sides' sentences and contexts,
  the same rule that orders the sides within one entry — so `(first (conflicts kb))` is
  an answer about the knowledge and not about which pair was typed first."
  [kb]
  (settle/ranked @(:conflicts kb)))

(defn contradictions
  "The coexisting pairs the last settle left standing — **represented dilemmas**, not
  failures.

  Two sources, one shape.  A **rebuttal**: two rules concluding opposite literals with
  neither naming the other's case (the Nixon diamond) is a genuine dilemma — both
  arguments are equally good, both sides stay believed at `:default`, and deciding it
  would be an arbitrary pick dressed up as an inference.  And a **definitional clash**:
  disjointness, functionality or asymmetry, each of which convicts by naming a second
  believed sentex, so an equal defeasible pair is a dilemma for the same reason.  So
  the engine represents it and hands the ranking to the application.

  Each entry is
  `{:nogood #{h1 h2} :handles [h1 h2] :priority int :kind kw-or-nil
    :sentence (contradicts ..)
    :sides [{:handle :sentence :context :defeat-class :justifications [...]} ...]}`,
  carrying both handles and both sides' justifications — the material an argument is
  made from.  `:kind` names the constraint a definitional clash violated
  (`:disjoint` / `:functional` / `:asymmetric`) and is nil for a rebuttal;
  `:priority` ranks a definitional clash (3–4) above a rebuttal (1–2).

  A dilemma is what *rebutting* defeat leaves behind.  **Undercutting** — \"this rule
  does not apply here\" — is written as an `exceptWhen` on the rule, which blocks
  rather than rebuts and produces no pair at all (see docs/exceptions.md).

  **The list is ordered by content** — each entry by its sides' sentences and contexts,
  the same rule that orders the sides within one entry — so `(first (contradictions kb))`
  is an answer about the knowledge and not about which pair was typed first."
  [kb]
  (settle/ranked @(:contradictions kb)))

;; Classifying a dilemma is an opt-in solve producing *persistent* inert contexts:
;; `(do/label CxDilemma Into)` then `(do/classify Into)` (docs/solving.md).  Do not
;; stamp a classification axis onto the TMS at settle instead: that makes the KB
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
  @(:settle-stats kb))

(defn reset-settle-stats!
  "Clear the settle instrumentation, including the histogram."
  [kb]
  (reset! (:settle-stats kb) {:iterations 0 :passes 0 :histogram {}}) kb)

(defn caches
  "What this process is holding beside the stores — every derived structure the engine
  caches, ranked by entries.  One row apiece:

    {:cache :literal-matches :label \"Literal matches\" :scope :kb
     :entries 3841 :limit 4096 :unit \"literals\"
     :hits 91204 :misses 12038 :hit-rate 0.883 :counters :process
     :clearable? true :note \"…\"}

  **`:scope` and `:counters` say what a number is about, separately.**  `:scope` is
  `:kb` for a cache hanging off this KB and `:process` for a static one every KB in the
  JVM shares; `:counters` says the same of `:hits` / `:misses`, and they genuinely
  differ — the literal cache's entries are this KB's and its counters are global, since
  they measure the mechanism rather than a store.  Reading a process figure as a per-KB
  one would attribute another KB's work to this one.

  **`:unit` is load-bearing too.**  One cache counts literals, another networks, another
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
   (caches-impl/clear-caches kb opts)))

(defn violations
  "The definitional constraints a *derived* conclusion would have broken during the
  last forward-chaining run, and what a bounded pass did not reach.  Each is

    {:violation <kind> :sentence S :context C :rule handle :run n :detail {…}}

  **`:sentence` and `:context` are not on every entry.** An entry about a *term*, a
  *pair*, a *budget* or a whole *network* names no one dropped sentence: the
  disjointness exposure report, whose subject is the term holding both types, and all
  five bounded-work notices below carry neither key, and the three network reports carry
  a `:context` with `:sentence` nil.  So a consumer reads both with `when-let` rather
  than unconditionally. `:message` is under `:detail` on every kind but `:non-confluent`
  and `:aggregate`, which carry it at the top level.

  ## The kinds

  The three tables below are the whole roster, and `violation_roster_test` holds them to
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
  | `:arg-type` / `:arg-genl` | an argument fails a declared constraint — `arg`'s type, or `genlArg`'s subtype floor | `:arg` `:expected` `:position` `:message` |
  | `:inter-arg-type` | an `interArg` conditional constraint whose trigger argument holds and whose target argument does not | `:arg` `:expected` `:position` `:trigger` `:trigger-type` `:trigger-position` `:message` |
  | `:arg-position` | a *declaration* constrains an argument the predicate's declared length does not have | `:predicate` `:position` `:arity` `:via` `:message` |
  | `:arg-constraint-kind` | a declaration disagrees with the predicate's `relationKind` — `genlArg` on an instance relation, `arg` on a type relation | `:predicate` `:message` |
  | `:arity` | a conclusion whose length disagrees with the arity the predicate declares or inherits | the check's problem map |
  | `:disjoint` | a membership putting a term in two types declared disjoint | the check's problem map |
  | `:functional` / `:asymmetric` | a second filler for a functional slot, or both directions of an asymmetric predicate | the check's problem map |
  | `:irreflexive` | a self tuple `(P a a)` of a predicate declared `irreflexive` — a lone tuple with no pair to weigh, so it refuses rather than arbitrates | the check's problem map |
  | `:anti-symmetric` | both directions of an `antiSymmetric` predicate whose two arguments no equality could merge (two numbers, a compound) — the mergeable case derives `(equals a b)` instead | the check's problem map |
  | `:not-stratified` | a derived `genl` / `genlCx` edge would put a cycle through negation in the rule set, or a minted generator would feed one | `:cycle` `:message` |
  | `:not-well-formed` | a minted sentence a special predicate's own structure check refuses | `:problems` `:message` |
  | `:naming` | a minted sentence breaking a naming invariant — the spellings in docs/naming.md | `:message` |
  | `:no-placement` | the join completed and no context sees the rule, every antecedent fact, and the `genl` edges the match climbed | `:rule-context` `:fact-contexts` `:subsumed` `:would-place` `:message` |
  | `:not-range-restricted` / `:not-indexable` / `:not-assertible` / `:exception-not-closed` / `:naf-not-closed` / `:quantifier-not-local` / `:quantified-conjunction` | a rule a **generator** minted that the rule checks refuse — the list both storage doors read, so a mint owes what an author's rule owes | the refusal's own keys, and `:message` |

  An **arbitrable** clash is not dropped when a *rule* concluded it: a firing has no
  caller to refuse, so the conclusion is placed and this settle weighs the pair, which is
  what gives the loser a `why-not`.  The three arbitrable kinds above — `:disjoint`,
  `:functional`, `:asymmetric` — are filed by the paths that decline to mint instead: the
  decontextualization lift's copy, the equality migration's twin, and a hypothesis
  `abduce` will not assume.

  ### Reported — nothing was dropped

  | entry | means | detail |
  |---|---|---|
  | `:disjoint` | two memberships each admissible where stated, jointly visible as disjoint | `:term` `:held` `:visible-from` `:message` |
  | `:functional` / `:asymmetric` | two claims each admissible where stated, jointly visible as a clash — `:refuse` only | `:pred` `:clash` `:visible-from` `:message` |
  | `:arity` | an arity **binding** arrived after facts it convicts — a declaration, the `genl` edge that inherits one from a super-predicate, or the `genlCx` edge that brings either into a stored fact's sight; the facts stand | `:predicate` `:expected` `:count` `:sample` `:declared-after` `:truncated` `:budget` `:via` `:message` |
  | `:non-confluent` | two schematic equations disagree about a shared term; the normal form stays deterministic, so nothing is dropped | `:with` `:message` |
  | `:aggregate` | an aggregate prover cannot reduce an extent — values that are not numbers of one dimension, or bounds only partially ordered.  Filed once per distinct error, since a count is recomputed rather than cached | `:message` `:values` |
  | `:qualitative-inconsistency` | the qualitative network visible from a context is unsatisfiable, so no goal of that calculus is answered there | `:calculus` `:message` `:nodes` `:pairs` |
  | `:metric-temporal-mixed-dimensions` | the `temporalDistance` facts visible from a context span more than one dimension, so it gets no metric network at all | `:message` `:dimensions` `:units` |
  | `:metric-temporal-inconsistency` | the metric temporal constraints visible from a context cannot all be satisfied | `:message` `:unit` `:nodes` `:pairs` `:cycle` |

  The first two rows are the **cross-context reports**: a pair neither writer could see,
  named rather than decided, with belief untouched. Under `:arbitrate` they do not appear
  — there the pair is weighed and answered by `contradictions` instead. `:clash` is the
  two `[sentence context]` halves in printed order, so the same knowledge in either
  arrival order files one identical entry.

  ### Bounded — the pass did not cover everything

  So a cap never reads as full coverage. Five kinds, separate because a reader acts on
  them differently, and each one entry per settle rather than one per trigger.

  | entry | means | detail |
  |---|---|---|
  | `:exposure-truncated` | the disjointness exposure sweep was cut short, so clashes its unswept triggers implicate went **unreported** | `:triggers` `:sample` `:budget` `:message` |
  | `:arbitration-truncated` | the arbitration sweep was cut short, so content those declarations implicate went **undecided** — a pair that would have been defeated stands believed until a later settle surfaces it | `:triggers` `:sample` `:budget` `:message` |
  | `:arity-truncated` | the retroactive arity reach was cut short — it sweeps the whole spec subtree a binding descends to and the cone a `genlCx` edge opens, and past the budget the predicates it never reached, and the ones it never got as far as looking *for*, hold facts neither refused nor named | `:predicates` `:sample` `:edges` `:edge-sample` `:budget` `:message` |
  | `:arity-report-truncated` | the arity reach files at most **8** entries for a pass, the content-first 8 of the predicates it convicted, so one binding over a wide subtree cannot evict every other violation from the ledger | `:predicates` `:filed` `:facts` `:sample` `:message` |
  | `:constraint-exposure-truncated` | one cross-context constraint pass found **more clashing pairs than it will file** — a functional slot filled from N contexts one vantage sees is N−1 pairs off a single arriving fact, against a ledger keeping the newest 1000 — or left a `genlCx` edge unswept | `:pairs` `:filed` `:cap` `:unswept` `:sample` `:budget` `:message` |

  The first three are sweeps cut short.  `:arity-report-truncated` is not one: everything
  it counts was swept, examined and convicted, and only the entry naming it was withheld
  — *found, examined and not named*, which is a different thing to act on.
  `:constraint-exposure-truncated` says which of the two it met, a cut walk or the entry
  cap, and can say both.  Nothing past a cap went undecided; it is visible, counted and
  unreported.  The three sweeps do not cover the same triggers either — a `functional` or
  `asymmetric` **declaration** reaches back over stored content on the deciding path and
  on no other — and `:arity-truncated` counts `:predicates` rather than `:triggers`
  because its budget is spent walking a subtree.

  Why a retroactive `:arity` reach reports rather than decides, why a truncation is one
  entry per settle rather than per trigger, and what the instance budget bounds:
  docs/taxonomy.md and docs/exceptions.md.

  The ledger **accumulates** — each entry carries the `:run` id of the chaining run
  that filed it, so a bulk load's drops are still here at the end — and is capped at
  the newest 1000.  Every drop is also logged at `:warn` as it happens.  It is
  append-only about exposures too: retracting the ingredient does not withdraw the
  entry, and one that leaves and revives files again.  `clear-violations!` empties it."
  [kb]
  @(:violations kb))

(defn clear-violations!
  "Empty the accumulated dropped-conclusion ledger.  `!` because it destroys the
  diagnostic record — the drops themselves are long final."
  [kb]
  (reset! (:violations kb) []) kb)

(defn exposed-clashes
  "Every disjointness clash the KB currently makes jointly visible: a term holding two
  types some context can see as disjoint, where each membership was admissible where
  it was written.  Entries in `violations`' shape (`{:violation :disjoint :detail
  {:term :held :visible-from :message}}`), computed on demand and **not** filed.

  `settle` reports the same clashes as they *arise* — what the change just made newly
  visible — which is the incremental question and the one an author wants while
  writing.  This is the standing question, and it is the one to ask of a KB that
  arrived all at once: an import rebuilds belief rather than changing it, so nothing
  is newly anything and the settle pass sits it out (see `settle/*rebuilding?*`).
  Reads only; nothing is stored and belief does not move."
  [kb]
  (settle/exposed-clashes kb))

(defn chain-stats
  "Chaining-run instrumentation: `{:runs n :last {:derived n :truncated? bool}}`.

  `:last` is the most recent run's result whatever triggered it — a plain `assert`
  chains too but returns only its handle, so `:truncated?` here (plus the :warn log)
  is how a depth- or derivation-capped run becomes visible without calling
  `forward-chain` by hand."
  [kb]
  @(:chain-stats kb))

(defn chain-report
  "Per forward rule, what forward chaining did with it — how many firings it **placed**,
  how many it **refused** and why, or whether it did nothing at all.  Where `chain-stats`
  is the run's headline counters, this is the per-rule breakdown behind them: the read the
  ontological engineer's *which of my rules actually do anything* wants.

  `O(rules)`, off the rule index and the state a run leaves standing — the refusal ledger
  (re-decided against current belief) and the justification graph — so it needs no
  instrumentation and reflects the KB as it is now, not a snapshot of one run. Each row is
  `{:rule :sentence :believed? :placed :refused :refusals :status}`; see
  `vaelii.impl.chain/rule-firing-report`.  The `:no-placement` and other violations a
  firing files are read separately through `violations`, keyed by the same `:rule` handle."
  [kb]
  (chain/rule-firing-report kb))

(defn last-program
  "The last edge `Program` handed to the solver — the contested assumptions and the
  nogoods among them — or nil if no tie has ever been arbitrated.

  This is the *question* the solver was asked; `conflicts` is the part of the answer
  that could not be satisfied, and the TMS holds the rest.  It is recorded rather
  than recomputed because resolving a tie removes the evidence for it: the defeated
  side stops matching, so the nogood is no longer derivable (see the KB record).

  `vaelii.impl.asp.edge/classify` reads it to say which of the current beliefs were
  *forced* and which were an arbitrary pick among equally good alternatives."
  [kb]
  @(:program kb))

(def ^:private solver-vars
  "The shipped edge solvers by name, and the var holding each.  Resolved at runtime, so
  naming the ASP backend here does not put clingo/JNA on every KB's load path."
  '{:stub vaelii.impl.solve/local-solver
    :asp  vaelii.impl.asp.edge/edge-solver})

(defn set-solver
  "Install the edge solver used to arbitrate default/default contradictions, returning
  `kb`.  Takes a **name** —

    :stub  (the default) a deterministic local stub: greedy, one contradiction at a
           time, so two overlapping pairs can cost two defeats where one would do
    :asp   the real answer-set backend — globally optimal, order-independent, and what
           `conflicts` / `last-program` / brave-cautious classification are for
           (docs/asp.md).  Degrades on its own: native clingo, else the clasp
           subprocess, else the stub

  — or any `vaelii.impl.solve/Solver` value, for an application with a backend of its
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
                                   ", or a solve/Solver value")
                              {:type :unknown-option :solver solver
                               :known (vec (sort (keys solver-vars)))})))
            solver))
  kb)

(defn- retract-storage!
  "The storage teardown behind `retract!` and `edit`, with **no settle**.  A datum
  runs the dependency-directed sweep (which decides what else falls with it); an
  inert sentex (never a TMS datum) is torn down directly through the removal choke
  point.  Returns `{:removed-sentexes n :removed-justifications n :datum? bool
  :seeds [handle]}` — `:datum?` tells the caller whether belief could have moved and a
  settle is owed, and `:seeds` what the removal owes a re-chain (a subsumption or a
  sighting whose named witness left but whose reachability survives —
  `special/resubsumption-seeds`)."
  [kb handle]
  (if (jtms/known-datum? (:tms kb) handle)
    (do (p/unmark-premise! (:records kb) handle)         ; no longer an asserted premise
        (let [{:keys [removed-sentexes removed-justifications]} (jtms/retract! (:tms kb) handle)
              ;; fetch each swept record BEFORE tearing it down — the JTMS returns handles,
              ;; and `sentex-removed!` is what deletes the record
              gone (into [] (keep #(p/get-sentex (:records kb) %)) removed-sentexes)
              ;; ...and read the re-chain seeds while the taxonomy still holds the
              ;; departing edges, since it is their spec subtree the seeds come from
              seeds (special/resubsumption-seeds kb gone)]
          ;; the removal choke point: disintegrate + unindex + delete + re-check queued,
          ;; one call — the same teardown the excepted-conclusion sweep runs, stated once
          (doseq [sx gone]
            (integrate/sentex-removed! kb sx))
          (doseq [jid removed-justifications]
            (p/delete-justification! (:records kb) jid))
          {:removed-sentexes   (count removed-sentexes)
           :removed-justifications (count removed-justifications)
           :datum?             true
           :seeds              seeds}))
    ;; "No TMS datum" is two different facts, and only one of them licenses the direct
    ;; teardown below.  An **inert** sentex (`assert-inert`) was never premised and
    ;; never derived, so no justification names it and nothing rests on it — the
    ;; teardown is complete.  A **stored premise whose network was never built** looks
    ;; identical to the node test and is the opposite case: the store's own
    ;; justifications may rest on it, and the sweep that would decide what falls with it
    ;; cannot run over a network that does not exist.  Taking the inert branch there
    ;; deletes one record, reports `{:removed-sentexes 1}`, and leaves every justification
    ;; naming it pointing at nothing — a store a later `recover` reads as a conclusion
    ;; whose antecedent is gone, OUT forever with no instrument reporting it.
    ;;
    ;; The store answers the premise half per handle: a premise is a sentex whose
    ;; `:strength` is non-nil (`kb/create-sentex`), which is also what `p/premise-ids` is
    ;; rebuilt from at open.  So that one is refused rather than guessed, and refused
    ;; **whatever `*write-unrecovered?*` says** — that opt accepts a write whose
    ;; consequences are known and unchecked, and this one's are not known at all.
    ;;
    ;; A **derived** sentex is the third fact the node test cannot see, and carries no
    ;; strength to be told apart by: a forward-chained record is not premised, so
    ;; `p/premise-ids` does not name it, and over an unbuilt network it reads exactly like
    ;; an inert one — while the store holds the justifications that concluded it and the
    ;; ones naming it as an antecedent.  Nothing per-handle separates the two, the store
    ;; keeping no index from a handle to the justifications that cite it, so the question
    ;; is asked of the **KB** instead: where the network was never built, no record here
    ;; can be shown to be the inert one, and the teardown is refused for all of them.
    ;; Where it was built, a record with no node genuinely is inert and the teardown is
    ;; complete.  `write-hazards` is the same reader the door upstream uses, so the two
    ;; refuse on one fact rather than on two tests that can disagree.
    (if-let [sx (p/get-sentex (:records kb) handle)]
      (cond
        (some? (:strength sx))
        (throw (ex-info (str "handle " handle " is a stored premise this KB has no TMS"
                             " node for, so the dependency sweep a retraction owes"
                             " cannot be computed — the store may hold justifications"
                             " resting on it.  Call (recover kb) (or (reindex kb) when"
                             " the index is derived) and retract then.")
                        {:type :unrecovered-premise :handle handle
                         :strength (:strength sx)}))

        (seq (kb/write-hazards kb))
        (throw (ex-info (str "handle " handle " has no TMS node in a KB whose belief was"
                             " never built, so whether anything rests on it cannot be"
                             " computed — an inert sentex and a derived one read alike"
                             " here, and only the derived one leaves justifications"
                             " naming a record this would delete.  Call (recover kb) (or"
                             " (reindex kb) when the index is derived) and retract then.")
                        {:type :unrecovered-kb :handle handle
                         :hazards (kb/write-hazards kb)}))

        :else
        (do (integrate/sentex-removed! kb sx)
            {:removed-sentexes 1 :removed-justifications 0 :datum? false :seeds []}))
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
    `seeds`, the facts `special/resubsumption-seeds` puts back on the agenda.

  The seed re-chain files no `:no-placement`, and `chain/*report-no-placement?*` says
  why: it is re-asking firings the removal already swept, so one it cannot place is the
  retraction restated to the caller who made it."
  [kb released seeds]
  (settle/settle kb)
  (when (or (seq released) (seq seeds))
    (when (seq released) (settle/rechain-exception-rules kb released))
    (when (seq seeds)
      (binding [chain/*report-no-placement?* false] (settle/rechain-seeds kb seeds)))
    (settle/settle kb)))

(defn- collect-orphaned-nats!
  "Sweep a reified NAT orphaned by a teardown — its termOfUnit map and materialized types
  would dangle a raw `nat/` symbol (docs/nat.md).  Gated on the KB declaring a reifiable
  function at all, and suppressed while already removing orphans.

  Two arms, and which one a caller takes turns on whether it can name the region the
  teardown touched:

  * **`retract!` and `edit!` pass their removal record** — every sentex that left the
    store while they ran, collected at the removal choke point
    (`integrate/*removed-sink*`), the settle's own sweep included.  A constant no removal
    named is not a candidate, at the cost of the region instead of the cost of the KB's
    whole NAT population; `remove-orphaned-nats!` says why a merely *defeated* use is not
    a use that went, and why collecting on one would be the dangling symbol rather than
    the fix for it.
  * **`preview-rollback!` passes nothing and asks the whole KB.**  It is putting a KB
    back rather than taking something out of one: the batch it undoes ran with the settle
    sweep off (`settle/*sweep?*`) and reached this sweep at no point, so what the rollback
    faces is a KB shaped by a suppressed pass rather than one teardown's region, and the
    claim it owes — the KB is as it was found — is about all of it.  A preview is a
    diagnostic run once per batch, so the whole-KB cost is one it can carry.

  **The two arms therefore ask different questions, not one question at two costs.**  The
  region arm asks what a teardown's removals orphaned; the whole-KB arm asks which
  constants are orphaned *now*, which is the stronger reading and the one a restore owes."
  ([kb] (collect-orphaned-nats! kb nil))
  ([kb sink]
   (when (and (not *in-orphan-removal?*) (nat/any-reifiable-functions? kb))
     (remove-orphaned-nats! kb sink))))

(defn- target-following-meta?
  "Is `sx` a **target-following meta-sentex** — a sentex whose predicate is declared
  `targetFollowingPredicate`?  Such a sentex names another sentex by handle and must not
  outlive it, so a teardown that removes the named target removes it too."
  [kb sx]
  (let [s (:sentence sx)]
    (and (sequential? s)
         (symbol? (first s))
         (has-prop? kb :target-following (first s)))))

(defn- following-metas-naming
  "The handles of still-stored target-following meta-sentexes that name handle `h` — the
  metas a teardown of `h` must sweep.  Found through the handle term's own index key
  (`find-sentexes` on `(sentexHandle h)`), then filtered to the marked predicates."
  [kb h]
  (into []
        (comp (filter #(target-following-meta? kb %)) (map :id))
        (kb/find-sentexes kb (sx/sentex-handle h))))

(defn- retract-following-metas!
  "The cascade that keeps a **target-following meta-sentex** from outliving the sentex it
  names.  After a teardown, retract every marked meta naming a handle that left the
  store, looping to a fixpoint — a retracted meta is itself a sentex another meta may
  name (an endorsement of an endorsement).  Reads the removal sink to learn what left:
  the dependency sweep's removals, the settle's, and this cascade's own — the same record
  `collect-orphaned-nats!` reads — so it is complete without every removal path reporting
  to it.

  A no-op unless the KB declares a `targetFollowingPredicate`: the sink is bound only
  then (or when a reifiable function needs it), and an empty roster short-circuits.  The
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
              (let [seeds (reduce (fn [acc mh] (into acc (:seeds (retract-storage! kb mh))))
                                  [] live)]
                (settle-after-teardown! kb (vec (keys @(:recheck kb))) (distinct seeds))))
            (recur (into seen fresh))))))))

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
    ;; the orphan sweep is scoped to what this teardown removed, so the removals are
    ;; recorded as they happen — the dependency sweep's, the settle's, and the sweep's own.
    ;; Gated on the same reifiable-function read the sweep itself is: with none declared
    ;; the sweep is a no-op, and recording a cascade for it to not read is pure retention
    (let [sink (integrate/removal-sink (or (nat/any-reifiable-functions? kb)
                                           (seq (props kb :target-following))))]
      (binding [integrate/*removed-sink* sink]
        (let [handle (the-handle handle "retract!")
              {:keys [datum? seeds] :as result} (retract-storage! kb handle)]
          (when datum?
            (settle-after-teardown! kb (vec (keys @(:recheck kb))) seeds))
          ;; sweep the meta-sentexes that named anything this teardown removed — the
          ;; cascade a reply-edge naming its target rides (`targetFollowingPredicate`).
          (retract-following-metas! kb sink)
          (collect-orphaned-nats! kb sink)
          ;; Structural genlCx: a teardown can *revive* a `contextArgSubrelation`
          ;; declaration or a stored R-evidence fact (retracting a monotonic defeater above
          ;; it), and the producer runs only on assert — so an edge never built while the
          ;; declaration was OUT would stay absent with nothing to revive.  Rebuild them
          ;; against the settled belief (docs/context-nat.md).  Gated internally on the KB
          ;; declaring a `contextArgSubrelation` at all.
          (context-nat/reconcile-revivals! kb)
          (dissoc result :datum? :seeds))))))

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
  N per-op settles.  Not a transaction: a throw mid-batch leaves what was already
  stored in place (the KB stays consistent — only the settle did not run — so settling
  by hand recovers it).

  Returns `{:added <one entry per add, `assert`-shaped> :removed {:removed-sentexes n
  :removed-justifications n}}`.  To also learn what the batch turned out to *mean* — the
  belief it added and took away — use `edit-with-consequences`, which is this plus the
  diff.

  What `check-edit` reports for the batch's own structure, this door refuses **before
  applying anything**: a malformed `:add` entry is `:shape` (never applied with the
  junk dropped), and a `:remove` handle naming nothing stored is `:unknown-handle` —
  where `retract!` of one is an ordinary zero-count answer, a *batch* naming one is a
  half-applied write waiting to happen, so the whole batch is refused while nothing
  has landed.  (A nil `:remove` entry stays nothing-to-remove, matching `handle-of` of
  an absent sentence.)

  **An unrecovered KB refuses the whole batch** (`:unrecovered-kb`), before anything is
  applied.  This door's headline guarantee is a JTMS claim — belief that survives the
  edit is never swept and rebuilt — and over an empty network there is no belief for it
  to be about; what is left is \"assert these unchecked, delete those unswept\"."
  ;; `batch` is destructured in the body rather than in the parameter vector, for the
  ;; reason `check-edit` states: the published `:arglists` is what a generated client
  ;; reads to name the argument, and a `{:keys [...]}` there names nothing. Its three
  ;; siblings (`check-edit`, `preview`, `edit-with-consequences`) already take it
  ;; positionally; this is the one that did not.
  [kb batch]
  (check-writable! kb "edit!")
  (check-edit-batch! batch)
  (let [{:keys [add remove]} batch]
    ;; The whole batch is held to `check-edit`'s answer before anything is applied, so
    ;; the dry run predicts the door and a refusal never leaves a half-applied batch:
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
      ;; is gated the same way, so a KB that reifies nothing records nothing.
      ;;
      ;; Read **before** the adds, and a batch may declare the KB's first reifiable
      ;; function among them: the gate is then false here and true at the sweep, which
      ;; leaves a nil sink and sends it down the whole-KB arm.  That is the stricter
      ;; question and the right one — a batch that has just made reification possible has
      ;; no region-scoped claim to make — and it costs the batch that does it one sweep.
      (let [sink (integrate/removal-sink (or (nat/any-reifiable-functions? kb)
                                             (seq (props kb :target-following))))]
        (binding [integrate/*removed-sink* sink]
          (let [[added removed]
                (binding [*defer-settle?* true]
                  [(mapv (fn [[sentence context opts]] (assert kb sentence context (or opts {}))) add)
                   (reduce (fn [acc h]
                             (let [r (retract-storage! kb (the-handle h "edit"))]
                               (-> acc
                                   (update :removed-sentexes   + (:removed-sentexes r))
                                   (update :removed-justifications + (:removed-justifications r))
                                   (update :seeds into (:seeds r)))))
                           {:removed-sentexes 0 :removed-justifications 0 :seeds []}
                           remove)])]
            (settle-after-teardown! kb (vec (keys @(:recheck kb))) (distinct (:seeds removed)))
            (retract-following-metas! kb sink)
            (collect-orphaned-nats! kb sink)
            ;; rebuild any structural genlCx edge a removal in this batch revived — the
            ;; producer runs on assert only, so a declaration or R-evidence fact that
            ;; flipped OUT→IN needs its edge built here (docs/context-nat.md); as in
            ;; `retract!`, gated on the KB declaring a `contextArgSubrelation`.
            (context-nat/reconcile-revivals! kb)
            {:added added :removed (dissoc removed :seeds)}))))))

(defn in?
  "Is the sentex handle raw structural JTMS IN, before contextual exceptions?"
  [kb handle]
  (jtms/in? (:tms kb) (the-handle handle "in?")))

(defn believed?
  "Is `handle` JTMS IN after the `(except ...)` cascade visible from `context`?

  This is contextual belief force only.  It deliberately does not require `context`
  to inherit the sentex's assertion context; `belief-status` reports that final
  visibility gate separately.  nil and unknown handles answer false; a non-handle is
  refused with `:bad-handle`, exactly as `in?`."
  [kb handle context]
  (let [h (the-handle handle "believed?")]
    (boolean (and (jtms/in? (:tms kb) h)
                  (not (res/excepted? kb h context))))))

(defn belief-status
  "Explain `handle`'s belief and visibility from `context` as a deterministic map.

  Separates storage, raw JTMS IN, context-visible exception force, assertion-context
  inheritance, and the two terminal answers `:believed?` / `:visible?`.  `:exceptions`
  is ordered by assertion context and content; nested meta-exceptions are under
  `:excepted-by`.
  nil and unknown handles report absent storage and raw belief; a dangling exception
  may still appear in `:exceptions` / `:excepted?`. Malformed handles are refused with
  `:bad-handle`."
  [kb handle context]
  (let [h       (the-handle handle "belief-status")
        stored  (when-some [h h] (p/get-sentex (:records kb) h))
        raw-in? (boolean (jtms/in? (:tms kb) h))
        {:keys [exceptions excepted?]} (res/exception-status kb h context)
        believed? (boolean (and raw-in? (not excepted?)))
        assertion-context (:context stored)
        path (when stored
               (some->> (tax/reach-support (:taxonomy kb) :genlCx
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
     :inherited-path path
     :believed? believed?
     :visible? (boolean (and believed? (some? path)))}))

(defn believed
  "The subset of `handles` raw structural JTMS IN, as a set — `in?` asked of many
  handles at once.  IN is a label already computed on the JTMS node, so this is one map
  read per handle either way; what the batch form saves is the **call**, which for a
  remote client (`vaelii.impl.serve`) is a whole round-trip.  A page listing n rows
  asks once instead of n times.

  Handle order does not survive (a set), because belief is a property of each handle
  and nothing here ranks them; an unknown or torn-down handle is simply absent."
  [kb handles]
  (into #{} (filter #(jtms/in? (:tms kb) %)) handles))

;; ---- introspection (used by the web browser) ----------------------------

(defn sentex
  "The sentex for a handle as a **map**, or nil.  Same shape contract as `sentexes-matching`'s
  elements: `:id` (the handle), `:sentence`, `:context`, `:truth`, and for a rule
  `:antecedent` / `:consequent` / `:direction` / `:defeasible`.  Key into it; the
  concrete `vaelii.impl.sentex/AtomicSentex` / `RuleSentex` record class is internal and not
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
  shape and contract as `sentex` (`:sentence` / `:context` / `:truth`; key into it, the
  record class is internal), but with no `:id`, since nothing was written.

  For turning a sentence into its content identity — a stable key or content-address that
  is a function of the assertion, not of whether or where it landed — independent of a
  handle: `(canonical-sentex kb S C)` digests to the same value on every KB that shares the
  taxonomy, whereas `sentex` needs the sentence to already be stored."
  [kb sentence context]
  (res/kb-sentex kb sentence context))

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
  [kb handle] (jtms/premise? (:tms kb) (the-handle handle "premise?")))

(defn defeat-class
  "The current defeat-class of a believed handle (:monotonic / :default), or nil when
  it is OUT — the effective strength of the belief after settling.  nil for a nil
  handle too; a non-handle is refused (`:bad-handle`)."
  [kb handle]
  (when-some [h (the-handle handle "defeat-class")]
    (jtms/defeat-class (:tms kb) h)))

(defn- in-content-order
  "`justifications` ordered by `kb/justification-content-key` through `nm/sort-by-content-key`,
  which builds that key **once per justification** and short-circuits below two.

  Both properties earn their keep here.  Each key build is a `get-sentex` per antecedent
  plus the structural key it assembles, and a **rule handle is an antecedent of every
  justification it licenses**, so `dependent-justifications` on one lists that rule's
  entire firing history: at 100k firings the decorated sort pays 100k key builds against
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
    (in-content-order kb (keep #(justification kb %) (jtms/supports (:tms kb) h)))
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
    (in-content-order kb (keep #(justification kb %) (jtms/dependents (:tms kb) h)))
    ()))

;; ---- why: the justification graph as a proof tree ------------------------
;; `supporting-justifications` gives one hop.  `why` walks the whole way down to
;; premises, which is what "why does the KB believe this?" actually asks.

(defn readable-sentence
  "A sentex's sentence with the author's variable names restored — pass a sentex map
  (from `sentex` / `sentexes-matching`).  A rule is stored canonically numbered (`?var0`, `?var1`,
  …), which reads as gibberish; this applies its `:varmap` back so it displays as
  written (`?x`, `?y`).  A fact has no varmap and is returned unchanged; nil in, nil
  out.  Used by `why` and by any display of a stored rule."
  [sx]
  (when sx
    (if-let [vm (:varmap sx)]
      (sx/originalize (:sentence sx) vm)
      (:sentence sx))))

(defn- opposite-sentence
  "The literal that directly contradicts `sentence`: its negation, or — if it is
  already a negation — what it negates."
  [sentence]
  (if (and (sequential? sentence) (= 'not (first sentence)))
    (second sentence)
    (list 'not sentence)))

(def ^:private why-max-depth
  "How deep `why` expands a proof tree before it stops and says so, absent a
  `:max-depth` option.

  `seen` guards a *cycle*, which is a different thing from depth: a derivation chain
  down a long transitive closure has no repeated handle and is bounded only by the
  KB.  `why*` walks that chain over an explicit work stack rather than the JVM stack,
  so the cap does not save the reader from an overflow — nothing overflows — it bounds
  the **size of the proof tree returned**: a chain thousands deep would otherwise build
  a datum thousands deep that a browser or a caller then has to hold and render."
  256)

(defn- check-why-opts!
  "Refuse a non-map `opts`, a key `why` does not read, and a `:max-depth` that is not
  a natural number — the `check-assert-opts!` reasoning at this door: an option
  nothing reads takes the default in silence."
  [opts]
  (opts/check! opts #{:max-depth} "why")
  (when-some [d (:max-depth opts)]
    (when-not (nat-int? d)
      (throw (ex-info (str "why's :max-depth must be a natural number, got " (pr-str d))
                      {:type :unknown-option :max-depth d :options [:max-depth]})))))

(defn- why*
  "The proof tree under `handle`, built over an **explicit** work stack so the JVM
  stack stays O(1) in the tree's depth.  Recursing it would overflow on a chain down
  a long transitive closure — which repeats no handle, so the cycle guard never fires
  and only the KB bounds the depth (`why-bounds-its-depth` pins the case).

  Two-phase.  An `:open` frame computes one node; an internal one allocates a child
  frame per antecedent — a fresh integer id apiece — and pushes a `:close` frame
  *beneath* those children (the stack is LIFO, so `:close` runs only once every
  descendant has stored its result).  `:close` reads the children back out of
  `results` and reassembles them in content order, so the order the stack happened to
  visit the tree in never reaches the output."
  [kb handle0 max-depth]
  (let [results (java.util.HashMap.)               ; frame id → node map
        work    (java.util.ArrayDeque.)
        n       (volatile! 0)
        fresh   #(vswap! n inc)
        root    (fresh)]
    (.push work [:open root handle0 #{} 0])
    (while (not (.isEmpty work))
      (let [frame (.pop work)]
        (case (nth frame 0)
          :open
          (let [[_ id handle seen depth] frame
                sx   (sentex kb handle)
                base {:handle handle :sentence (readable-sentence sx) :context (:context sx)}]
            (cond
              (nil? sx)                          (.put results id (assoc base :stored? false))
              (>= (long depth) (long max-depth)) (.put results id (assoc base :truncated? true))
              ;; The justification graph can cycle (two rules deriving each other, a
              ;; datum re-derived through its own consequence).  A node already on the
              ;; current path is reported as a back-edge instead of being expanded again
              ;; — the tree stays finite and the cycle stays visible rather than pruned.
              (contains? seen handle)            (.put results id (assoc base :cycle? true))
              (not (in? kb handle))              (.put results id (assoc base :believed? false))

              (premise? kb handle)
              (.put results id (assoc base :believed? true
                                      :defeat-class (defeat-class kb handle)
                                      :premise? true :strength (:strength sx)))

              :else
              (let [seen'  (conj seen handle)
                    depth' (inc (long depth))
                    justs  (mapv (fn [j]
                                   (let [inf   (:informant j)
                                         rule? (integer? inf)
                                         ;; the rule handle is an antecedent of every
                                         ;; justification it licenses, so it would
                                         ;; otherwise recur as one of the "facts" — lift
                                         ;; it out and report it as the rule
                                         antes (if rule? (remove #(= inf %) (:antecedents j))
                                                   (:antecedents j))]
                                     {:justification (:id j)
                                      :informant     inf
                                      :strength      (:strength j :monotonic)
                                      :rule?         rule?
                                      :rule          (when rule? (readable-sentence (sentex kb inf)))
                                      :children      (mapv (fn [ante] [(fresh) ante]) antes)}))
                                 (supporting-justifications kb handle))]
                (.push work [:close id (assoc base :believed? true
                                              :defeat-class (defeat-class kb handle)
                                              :premise? false)
                             justs])
                (doseq [j justs, [child-id ante] (:children j)]
                  (.push work [:open child-id ante seen' depth'])))))

          :close
          (let [[_ id base justs] frame
                support (mapv (fn [j]
                                (cond-> {:justification (:justification j)
                                         :informant     (:informant j)
                                         :strength      (:strength j)
                                         :because       (mapv (fn [[cid _]] (.get results cid))
                                                              (:children j))}
                                  (:rule? j) (assoc :rule (:rule j))))
                              justs)]
            (.put results id (assoc base :support support))))))
    (.get results root)))

(defn why
  "Why does the KB believe `handle`?  A **proof tree**, as data:

    {:handle h :sentence S :context C :believed? true :defeat-class :default
     :premise? false
     :support [{:justification jid :informant <rule handle or symbol>
                :rule <the rule's sentence> :strength :monotonic
                :because [ <the same map, recursively, per antecedent> ]}]}

  Recursion terminates at **premises**, which are marked `:premise? true` (with the
  assumption `:strength` they were asserted at) and carry no `:support` — a premise
  rests on nothing, so there is nothing below it.

  Rule sentences are `originalize`d, so variables read as the author wrote them
  (`?x`, not the canonical `?var0`).  The rule handle is lifted out of the
  justification's antecedents into `:rule` rather than recurred into as if it were a
  fact.

  **Cycles are guarded**: the justification graph may contain them, and a handle
  already on the current path is emitted as `{:cycle? true}` instead of being
  expanded again.

  A handle that is stored but not believed yields `{:believed? false}` — ask
  `why-not` for the reason.  An unknown handle (nil included) yields
  `{:stored? false}`.

  **Depth is bounded** — at 256 by default, or at `opts`' `:max-depth` — and a branch
  that reaches the bound is emitted as `{:truncated? true}` rather than expanded.
  `:cycle?` guards a repeated handle, which is a different failure: a chain down a
  long transitive closure repeats nothing and is bounded only by the size of the KB.
  The walk is iterative — an explicit work stack, not JVM recursion — so the cap
  bounds the *size of the proof tree returned* rather than the depth of the reader's
  stack: nothing overflows, and a truncated tree is re-asked whole with a larger
  `:max-depth`.  A nil or absent `:max-depth` is the default.  An `opts` key `why`
  does not read is refused (`:unknown-option`), as is a non-map `opts` —
  `check-assert-opts!`'s reasoning at this door."
  ([kb handle] (why kb handle nil))
  ([kb handle opts]
   (check-why-opts! opts)
   (why* kb (the-handle handle "why") (or (:max-depth opts) why-max-depth))))

(defn- why-not-handle
  "`why-not` of a stored handle — the original arity, factored out so the sentence
  arity can delegate to it."
  [kb handle]
  (let [sx   (sentex kb handle)
        base {:handle handle :sentence (readable-sentence sx) :context (:context sx)}]
    (cond
      (nil? sx)         (assoc base :believed? false :reason :not-stored)
      (in? kb handle)   (assoc base :believed? true)
      ;; Checked before `:defeated` and before `:unsupported`, because it is the more
      ;; specific answer and neither of the others is true of it: a superseded
      ;; spelling lost no argument and kept all of its support — it was *restated*
      ;; under the representative its terms now merge to.
      (jtms/superseded? (:tms kb) handle)
      (assoc base :believed? false :reason :superseded
             ;; rewritten from the **sentex's own context**, which is the only context
             ;; that supersedes it (`special/migrate-into`: `(= reader (:context sentex))`),
             ;; so the representative named is the one that context elected.  The unscoped
             ;; rewrite would name the global election, which diverges when a `rewriteOf`
             ;; outside this context's cone re-elected the head — then `:sentence` names a
             ;; spelling this context never elected and `:handle` misses, while the
             ;; `:rewrites` map beside them is the correct scoped one, and the report
             ;; contradicts itself (docs/equality.md's context-scoped supersession).
             :superseded-by (let [r (kb/rewrite-goal kb (:sentence sx) (:context sx))]
                              {:sentence r
                               :handle   (kb/find-sentex-handle kb r (:context sx))
                               :rewrites (jtms/supersession (:tms kb) handle)}))
      (jtms/defeated? (:tms kb) handle)
      (assoc base :believed? false :reason :defeated
             ;; content-ordered: the matcher promises the set, not the order, and the
             ;; order it happens to yield moves with the retrieval sweeps
             :contradicted-by (->> (sentexes-matching kb (opposite-sentence (:sentence sx)) '?ctx)
                                   (nm/sort-by-content-key (juxt #(pr-str (:sentence %)) #(str (:context %)))
                                                           compare)
                                   (mapv (fn [o] {:handle (:id o) :sentence (readable-sentence o)
                                                  :context (:context o)
                                                  :defeat-class (defeat-class kb (:id o))}))))
      :else
      (assoc base :believed? false :reason :unsupported
             :premise? (premise? kb handle)
             :support (vec (for [j (supporting-justifications kb handle)]
                             {:justification (:id j)
                              :informant (:informant j)
                              :missing   (vec (remove #(in? kb %) (:antecedents j)))}))))))

(defn- excepted-argument
  "The argument for `sentence` in `context` that some excepted rule built and then
  discarded, or nil.

  This is the backward reading of a blocked firing: take the rules that could conclude
  the goal's predicate, keep the ones carrying an `exceptWhen`, unify the goal with the
  consequent to seed the bindings, complete them by joining the antecedents against
  believed facts, and report the first completion whose exception holds.

  The exception is checked in the **query's** context, which is where the caller is
  asking from and where a conclusion would have been placed.  The ground exception is
  returned as a bare sentence when the rule states one conjunct and as a vector when it
  states several, matching how it was written.

  The completion reported is the **content-least** — the rule's sentence, then the
  ground exception — never the first the rule index happened to yield: two excepted
  rules concluding one goal would otherwise make the whole answer a function of which
  was asserted first."
  [kb sentence context]
  (->> (for [rh   (rules/direct-concluders (:index kb) (nm/functor sentence))
             :let [rsx (p/get-sentex (:records kb) rh)]
             :when (and rsx (rules/rule? rsx) (p/exception-rule? (:index kb) rh) (in? kb rh))
             :let  [rule (chain/rule-view-of kb rh rsx)
                    b0   (res/unify (:consequent rule) sentence)]
             :when b0
             {:keys [bindings handles]} (chain/solve-rule kb (:antecedents rule) b0)
             except (provers/rule-exceptions kb rh)
             :when (chain/exception-holds? kb except bindings context)]
         (let [ground (mapv #(sx/canon (res/substitute % bindings)) except)]
           [(pr-str [(:sentence rsx) ground])
            {:rule rh
             :exception (if (= 1 (count ground)) (first ground) ground)
             :via (vec handles)}]))
       (sort-by first)
       first
       second))

(defn why-not
  "Why does the KB *not* believe `handle`?  The complement of `why`, as data:

    {:handle h :sentence S :context C :believed? false :reason <keyword> …}

  | `:reason` | means | carries |
  |---|---|---|
  | `:not-stored` | no sentex has this handle | — |
  | `:superseded` | an equality merge restated it under its class representative; it lost no argument and retracting the equality gives it straight back | `:superseded-by` `:rewrites` |
  | `:defeated` | the JTMS is forcing it OUT — contradiction resolution ruled against it | `:contradicted-by` |
  | `:unsupported` | not a premise, and every supporting justification has an antecedent that is OUT | `:support` with `:missing` |
  | `:excepted` | *(sentence arity only)* a rule applied and its `exceptWhen` query held, so it concluded nothing | `:rule` `:exception` `:via` |

  A believed handle yields `{:believed? true}` and no `:reason`.  An empty `:support`
  under `:unsupported` means it never had a justification at all.  A nil handle is
  `:not-stored` — the answer for a sentence the KB does not hold — while a non-handle
  (a vector of handles included) is refused (`:bad-handle`), as `why` refuses it.

  **`:contradicted-by` is recomputed, not recorded.**  The engine does not keep which
  decision defeated a datum — `settle` erases the evidence it decided from, since the
  loser stops matching and the nogood stops being derivable — so this is a strong hint
  rather than a verdict, and it is empty once the winner is retracted.  `last-program`
  is the nearest thing to the actual record, and only for a tie that reached the solver.

  **The sentence arity** `(why-not kb sentence context)` exists because `exceptWhen`
  produces an answer no handle can carry: a blocked conclusion is never stored, so
  there is nothing to pass to the handle arity.  A stored sentence delegates to that
  arity, except that a stored-but-disbelieved one is checked for an exception first —
  excepted is the more specific answer than unsupported.  Neither stored nor excepted
  is `:not-stored`.  It takes an `(ist Ctx S)` sentence, asking after S in Ctx and
  reporting it under that context (`ist-goal`).  docs/exceptions.md, docs/equality.md."
  ([kb handle] (why-not-handle kb (the-handle handle "why-not")))
  ([kb sentence context]
   (let [[sentence context] (ist-goal kb sentence context)
         h (kb/find-sentex-handle kb sentence context)]
     (if (and h (in? kb h))
       (why-not-handle kb h)
       (if-let [exc (excepted-argument kb sentence context)]
         (merge {:handle h :sentence sentence :context context :believed? false
                 :reason :excepted}
                exc)
         (if h
           (why-not-handle kb h)
           {:handle nil :sentence sentence :context context
            :believed? false :reason :not-stored}))))))

;; ---- preview: what a batch would do, without leaving it done -------------
;;
;; `edit` applied and `retract!`'d is not a preview: the retraction sweeps, and what a
;; sweep deletes can only be *re-derived*, at fresh handles.  So a preview writes
;; nothing it cannot take back at the same handles.  Two arrangements make that true:
;;
;;   - an `:add` is really asserted, and rolled back through the premise marks it made
;;     (`*premise-audit*`).  Everything it derived hangs off one of those premises, so
;;     retracting them collects the lot by the ordinary dependency-directed sweep;
;;   - a `:remove` is **not** retracted.  It is `jtms/suspend-premise` — a retraction's
;;     effect on belief with the deletion left out — because belief is the whole of
;;     what a preview is asked about, and a suspended premise goes straight back.
;;
;; and for the same reason `settle`'s own sweep is off for the duration
;; (`settle/*sweep?*`), so an added `exceptWhen` blocks a conclusion without deleting
;; it.  The rollback settles with the sweep back on, which is what collects a
;; conclusion the preview's *removals* brought into being.
;;
;; The diff is taken over the **affected region** (`settle/*touched-sink*`), never over
;; the believed set: belief before is read *after* the rollback, when the KB is back at
;; baseline, so the two readings need no snapshot between them and the cost is the
;; region's rather than the KB's.

(defn- preview-support
  "One level of why `handle` is believed: the informant, the rule it names when that
  informant is a stored rule, and the antecedent sentences.  One level and not `why`'s
  tree, because a preview reports a whole batch's consequences and a tree apiece would
  be a proof search apiece.  Nil for a premise, which is its own reason."
  [kb handle]
  (when-let [j (first (supporting-justifications kb handle))]
    (let [inf   (:informant j)
          rule? (integer? inf)]
      (cond-> {:informant   inf
               :strength    (:strength j :monotonic)
               ;; the rule handle is an antecedent of every justification it licenses,
               ;; so lift it out and report it as the rule rather than as a fact
               :antecedents (mapv #(readable-sentence (sentex kb %))
                                  (cond->> (:antecedents j)
                                    rule? (clojure.core/remove #(= inf %))))}
        rule? (assoc :rule (readable-sentence (sentex kb inf)))))))

(defn- diff-order
  "One belief-diff entry's place in a reading, as content: its sentence then its context
  — `settle/report-order`'s key, and here for the same reason.

  **A handle is not a place in a reading.**  Handles are allocated in assertion order, so
  ordering either half of a diff by one makes the reading a fact about how the KB was
  loaded; and both halves are **capped** (`:max-results`), which turns that from a
  cosmetic ordering into *which entries the caller is shown*.  The browser's proposal
  panel caps at 50, so the same batch against the same knowledge would show a different
  fifty depending on the order the KB arrived in."
  [e]
  ;; print vars bound off: both halves are capped, so a tie two elided long
  ;; sentences fall into decides *which entries the caller is shown*
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

(defn- preview-rollback!
  "Put the KB back: restore the premises the preview suspended, undo the premise marks
  it made — retracting outright what it created, un-marking what it merely re-asserted
  — then settle (with the sweep back on) and restore the diagnostic ledgers.

  A handle in both sets is a batch that removed a premise and re-asserted the same
  sentence; the audit saw it *after* the suspend and so believes it was never a
  premise, which is why the suspended set wins.

  The change feed stays off here (`feed/*enabled?*`), as it was for the batch: this is
  the half that would send the *reverse* of every change that one sent, and a listener
  told belief moved and then that it moved back learned nothing."
  [kb {:keys [audit suspended violations program refused]}]
  (let [tms     (:tms kb)
        records (:records kb)
        held    (set (map first suspended))]
    (binding [feed/*enabled?* false
              *premise-audit* nil
              *defer-settle?* true]
      (doseq [[h strength] suspended]
        (jtms/add-premise tms h strength)
        ;; the premise is evidence again, so every exception it bears on is a
        ;; question again — the mirror of the queueing the suspension did
        (when-let [sx (p/get-sentex records h)]
          (special/recheck-on-sentence kb (:sentence sx))))
      (doseq [[h {:keys [premise? strength]}] @audit
              :when (not (held h))]
        (cond
          ;; `put-premise-mark`, not `mark-premise`: the mark this restores is the one
          ;; the audit recorded *before* the batch, and the batch may have raised the
          ;; class.  `mark-premise` resolves by content and would keep the raised one,
          ;; which is right for an assertion and wrong for an undo — the preview leaves
          ;; the KB as it found it, and a class it raised is a change like any other.
          premise?                 (put-premise-mark kb h strength)
          (p/get-sentex records h) (retract-storage! kb h))))
    ;; No re-chain seeds: the rollback is putting the KB back, so re-deriving what a
    ;; withdrawn subsumption or sighting still licenses would be re-deriving content the
    ;; preview created — at handles the audit can no longer take back.
    (binding [feed/*enabled?* false]
      (settle-after-teardown! kb (vec (keys @(:recheck kb))) nil)
      ;; the whole-KB arm, not a region: the batch ran with the settle sweep off and
      ;; reached the orphan sweep at no point, so the baseline claim is about all of it
      (collect-orphaned-nats! kb))
    (reset! (:violations kb) violations)
    (reset! (:program kb) program)
    ;; ...and the refusal record, which the batch writes to as well as reads.  A firing
    ;; the batch's own content refused recorded the handles it rested on, and the
    ;; rollback has just taken those handles away — so left alone the record carries
    ;; entries naming nothing, dropped only whenever their rule is next queued.  The
    ;; re-chain above re-records what the *baseline* refuses, so this is the entries the
    ;; preview invented rather than the ones it consumed; restored wholesale like the two
    ;; ledgers, and free, since the record is a persistent map and the snapshot is a
    ;; reference.
    (reset! (:refused kb) refused)))

(defn- preview-forget-dead-handles
  "Blank the `:handle` of any entry whose sentex the rollback took away.  Content the
  batch *created* has no handle once the preview is over, and reporting the number it
  briefly held would hand a caller a handle that now names nothing — or, after enough
  churn, something else."
  [kb entries]
  (mapv (fn [e] (cond-> e (nil? (p/get-sentex (:records kb) (:handle e)))
                        (assoc :handle nil)))
        entries))

(defn preview
  "What would this batch do to the KB — **without** leaving it done.

  `batch` is `edit`'s shape, `{:add [[sentence context opts?] …] :remove [handle …]}`.
  The adds are asserted, the removes stop being premises, belief settles once, the
  difference is read off, and then every write is taken back.  Returns

    {:believed-added   [{:sentence S :context C :handle h|nil :premise? bool
                         :justification {:informant i :rule S :antecedents [S …]}} …]
     :believed-removed [{:sentence S :context C :handle h :reason kw :detail {…}} …]
     :refused          [ …`check-edit` shape… ]
     :violations       [ …`violations` shape… ]
     :contradictions   [ …`contradictions` shape… ]
     :bounded?         bool}

  The **removed** half is the interesting one, and the one a naive implementation
  misses: it is where defeat, supersession and the dependency-directed sweep show up,
  and its `:reason` is `why-not`'s.  `:handle` is nil for content the batch *created* —
  after the rollback no such sentex exists, and a number naming nothing is worse than
  nothing.  `:contradictions` is here for a related reason: asserting the negation of a
  believed default withdraws nothing (a defeasible tie is represented, not arbitrated),
  so without it the most obvious thing a reviewer can do would report nothing at all.
  Standing dilemmas are subtracted.  A `:refused` entry is skipped and the rest of the
  batch is previewed without it.

  `opts` bounds the run — `:max-depth` / `:max-derivations` to chaining, `:max-results`
  on each half of the diff — and `:bounded?` says one of them bit, so a partial answer
  never reads as a complete one.  A key this fn does not read is refused
  (`:unknown-option`): every key is a bound, so a misspelt one is a cap silently off.

  **The KB is left byte-identical**: same live sentexes, same justifications, same
  handles.  What does move is the handle counter (a preview mints handles and they are
  not reissued) and the `chain-stats` / `settle-stats` counters, which record work that
  genuinely ran.

  Cost is the batch's own cost plus the rollback, which is a second settle.  The diff is
  taken over the **relabelled region**, never over the believed set, so nothing here
  scans the KB.  Not concurrent: a preview is a write followed by its undo, so it holds
  the single writer for its duration.  docs/preview.md.

  **An unrecovered KB refuses this too** (`:unrecovered-kb`), for the reason a dry run
  exists at all.  A preview implements a `:remove` as a premise *suspension*, gated on
  `jtms/premise?` — false for every stored handle in a KB with no network — so it would
  skip the removal and report that nothing changes, while `edit!` on the same batch is
  the operation that cannot be taken back.  A verification step that is silent about
  exactly the dangerous case is worse than no verification step, because a caller who
  has one trusts it.  So this door refuses where `edit!` refuses, and the two agree."
  ([kb batch] (preview kb batch nil))
  ([kb batch opts]
   ;; refused outright, as `edit` refuses it: previewing a batch `edit` would not run
   ;; answers a question about content that could never land
   (check-writable! kb "preview")
   (check-edit-batch! batch)
   (check-bound-opts! opts #{:max-depth :max-derivations :max-results} "preview")
   (let [tms        (:tms kb)
         refused    (check-edit kb batch)
         bad-add    (into #{} (comp (filter #(= :add (:in %))) (map :index)) refused)
         bad-remove (into #{} (comp (filter #(= :remove (:in %))) (map :index)) refused)
         ledger     @(:violations kb)
         standing   @(:contradictions kb)
         program    @(:program kb)
         ;; the refusal record is derived state the batch writes to, so the rollback
         ;; needs the value it started from — `preview-rollback!` says why
         refusals   @(:refused kb)
         audit      (atom {})
         touched    (atom #{})
         suspended  (atom [])
         thrown     (atom [])
         truncated? (atom false)
         chain-opts (select-keys opts [:max-depth :max-derivations])
         limit      (:max-results opts)
         result     (atom nil)]
     (try
       ;; The change feed is off for the batch — and separately off for the rollback, in
       ;; `preview-rollback!`, which is the half that would send the *reverse* of every
       ;; change this half sent.  An application told that belief moved and then that it
       ;; moved back learned nothing and has probably already acted.
       (binding [feed/*enabled?* false
                 settle/*sweep?* false
                 settle/*touched-sink* touched]
         (binding [*premise-audit* audit
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
             (when (:truncated? (:last @(:chain-stats kb))) (reset! truncated? true)))
           ;; suspended, not retracted: the belief half of a removal, which is the
           ;; half a preview is about and the only half that can be undone in place
           (doseq [[i h] (map-indexed vector (:remove batch))
                   :when (and (not (bad-remove i)) (jtms/premise? tms h))]
             (swap! suspended conj [h (jtms/premise-strength tms h)])
             (jtms/suspend-premise tms h)
             ;; a real removal queues the exception re-check from the removal choke
             ;; point; a suspension has to queue it by hand, or an exception the datum
             ;; was the only evidence for would never be re-asked and the rule it
             ;; blocks would never fire again
             (when-let [sx (p/get-sentex (:records kb) h)]
               (special/recheck-on-sentence kb (:sentence sx)))))
         ;; No re-chain seeds: a preview suspends rather than retracts, so no `genl` or
         ;; `genlCx` sentex left the store and no subsumption or sighting lost its named
         ;; witness to a removal.  A *suspended* one still deactivates the edge, and the
         ;; conclusion it licensed goes OUT rather than being swept — which is precisely
         ;; the `:believed-removed` line the preview exists to report.
         (settle-after-teardown! kb (vec (keys @(:recheck kb))) nil)
         ;; Everything the batch could have moved is in the relabelled region, and the
         ;; entries have to be built **now** — content the batch created will not
         ;; survive the rollback to be described afterwards, and `why-not`'s answer for
         ;; a datum this batch put OUT is only true while the batch is in force.
         (let [region  (sort @touched)
               in-now  #(jtms/in? tms %)]
           (reset! result
                   {:believed-added   (mapv #(preview-added-entry kb %) (filter in-now region))
                    :believed-removed (mapv #(preview-removed-entry kb %)
                                            (clojure.core/remove in-now region))
                    :refused          (into refused @thrown)
                    :violations       (into [] (drop (count ledger)) @(:violations kb))
                    ;; The dilemmas the batch would *open*.  Asserting the negation of a
                    ;; believed default withdraws nothing — both sides stay believed at
                    ;; `:default` and the pair is represented (docs/nmtms.md) — so a
                    ;; caller reading only the two diff halves would be told the line
                    ;; simply arrived, which is the one thing that did not happen.
                    :contradictions   (settle/ranked
                                       (clojure.core/remove (set standing)
                                                            @(:contradictions kb)))
                    :bounded?         @truncated?})))
       (finally
         (preview-rollback! kb {:audit audit :suspended @suspended
                                :violations ledger :program program
                                :refused refusals})))
     ;; Belief **before** is read here, on a KB the rollback has put back at baseline —
     ;; so the two readings need no snapshot between them, and a candidate that is
     ;; believed now was believed all along and is no news either way.  A handle the
     ;; rollback took away reads as not believed, which is exactly right: it did not
     ;; exist before.
     (let [believed-before? #(jtms/in? (:tms kb) (:handle %))
           ;; content order before the cap, never after: the cap is what makes the order
           ;; decide *which* entries the caller sees (`diff-order`).  Sorting the built
           ;; entries rather than the region costs no extra read — every entry in the
           ;; region is built above, the rollback having taken away the KB they describe
           ;; `diff-order` builds two `pr-str` under a print-guard frame — once per entry
           ;; now (`nm/sort-by-content-key`), not per comparison, as the sibling `believed-diff`
           ;; already keys it; the `[pr-str pr-str]` key orders under `compare`
           cap (fn [xs] (cond->> (nm/sort-by-content-key diff-order compare xs)
                          (pos-int? limit) (take limit)))
           added   (into [] (clojure.core/remove believed-before?) (:believed-added @result))
           removed (into [] (filter believed-before?) (:believed-removed @result))]
       (assoc @result
              :believed-added   (preview-forget-dead-handles kb (cap added))
              :believed-removed (preview-forget-dead-handles kb (cap removed))
              :bounded?         (boolean (or (:bounded? @result)
                                             (and (pos-int? limit)
                                                  (or (> (count added) limit)
                                                      (> (count removed) limit))))))))))

(defn- moved-handles
  "Which of a relabelled `region` gained belief and which lost it — `[added removed]`,
  each in **content** order (`diff-order`).

  Not handle order: handles are allocated in assertion order, and both halves are capped
  by the callers, so ordering on one would decide *which* entries a caller is shown from
  how the KB happened to be loaded.  The rank is taken here rather than after the entries
  are built because the cap is applied to these handles — ranking downstream would leave
  the cap picking from an arrival-ordered list.  It costs no extra read: the liveness test
  fetches every record already, so the key is taken off the record it was going to
  discard.

  `was-in` is the part of the region that was already believed when a relabel first
  touched it (`jtms/touched-in`), so region + before-labels + belief-now **is** the
  delta, and it is proportional to what moved rather than to what is stored.  A snapshot
  of the believed set would be O(KB) per write.

  A datum the dependency-directed sweep **deleted** is in the region with no record left
  to describe, so it is dropped rather than guessed at: what is reported is belief that
  went away and is still stored — defeated, superseded, unsupported.

  One function because two callers must agree: a consequence report and a feed event are
  the same question about the same region, and an application that got different answers
  from them would have no way to tell which was the KB's."
  [kb region was-in]
  (let [keyed   (into [] (keep (fn [h]
                                 (when-let [sx (p/get-sentex (:records kb) h)]
                                   {:handle h
                                    :order  [(pr-str (readable-sentence sx))
                                             (pr-str (:context sx))]})))
                      region)
        ordered (mapv :handle (sort-by :order keyed))
        in-now  #(jtms/in? (:tms kb) %)]
    [(into [] (clojure.core/remove was-in) (filter in-now ordered))
     (into [] (filter was-in) (clojure.core/remove in-now ordered))]))

(defn edit-with-consequences!
  "`edit`, plus what the batch turned out to **mean** — the belief it added and the
  belief it took away, in `preview`'s entry shapes.  Returns `edit`'s
  `{:added :removed}` with `:believed-added` and `:believed-removed` merged in.

  This is the *after* to `preview`'s *before*, and it answers the question a commit
  leaves open: `edit` reports the handles it stored, which is what the caller already
  said, and says nothing about what followed from it.

  **Where the diff comes from.** Not a snapshot of the believed set — that would be
  O(KB) per write.  Every relabel records the region it touched (`jtms/touched`) and
  which of that region was already believed when it first touched it
  (`jtms/touched-in`); the window spans everything since the last settle finished, so
  for a batch it covers the whole deferred phase and its one settle.  Region plus
  before-labels plus belief now is the delta, and it is proportional to what the batch
  moved rather than to what is stored.

  `preview` cannot use this and does not need to: its rollback puts the KB back, so it
  reads belief-before off the restored KB instead.  This has no rollback to read after,
  which is exactly why the labels have to be captured on the way through.

  **What the removed half cannot say.** A datum the dependency-directed sweep *deleted*
  has no record left to describe, so it is omitted rather than guessed at: what is
  listed is belief that went away and is **still stored** — defeated, superseded,
  unsupported.  A `:remove` sweeps, so ask `preview` what a removal would take with it;
  it suspends instead of retracting and can still name every casualty.  An add-only
  batch (the common one, and the proposal panel's) has no such gap.

  `opts` is `{:max-results n}`, capping each half as `preview`'s does; a key this fn
  does not read is refused (`:unknown-option`)."
  ([kb batch] (edit-with-consequences! kb batch nil))
  ([kb batch opts]
   (check-bound-opts! opts #{:max-results} "edit-with-consequences")
   (let [touched (atom #{})
         was-in  (atom #{})
         result  (binding [settle/*touched-sink*    touched
                           settle/*touched-in-sink* was-in]
                   (edit! kb batch))
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
  sit in a context the watch's own can see up the `genlCx` cone, *and* the subsumption
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
        (when-let [b (res/match1 kb goal (:sentence sx) (when-not any? context))]
          (cond-> b any? (assoc context (:context sx))))))))

(defn- watch-goal-problem
  "Why `goal` cannot be answered from a moved region, or nil when it can.

  Every one of these is a goal whose truth is a function of something the region does
  not hold, so matching it against the region's entries would be quietly wrong rather
  than merely incomplete — and being quietly wrong is the one thing a feed must not be.
  A conjunction joins against facts the batch never touched; an aggregate and a NAF
  literal are properties of a whole answer set, which a fact *leaving* belief can flip
  with nothing about the flip in the region; a `thereExists` is the same; an evaluable
  is computed and never stored.  `ist` is refused because a watch already has a context
  argument and would otherwise match nothing at all — no stored sentence has that
  functor."
  [goal]
  (cond
    (vector? goal)
    "a conjunctive goal joins against facts outside the region a settle moved"

    (not (and (sequential? goal) (seq goal)))
    "a goal must be a sentence"

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
  or to punish its neighbours."
  [kb {:keys [f goal context token]} added removed entries]
  (try
    (if goal
      (let [prepared (prepare-goal-for-read kb goal context)
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
    (catch Throwable t
      (trove/log! {:level :warn :id ::listener-threw
                   :msg   (str "a change-feed listener threw; skipping it: "
                               (ex-message t))
                   :data  {:token token :goal goal :context context}})
      nil)))

(defn- dispatch-feed!
  "Turn one settle's relabelled region into an event and deliver it, in registration
  order.  The `feed/install-dispatch!` seam's other end.

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
            ;; closed for the duration and reopen for the caller's next settle.
            (binding [settle/*touched-sink*    nil
                      settle/*touched-in-sink* nil]
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
  `genlCx` cone; a variable (`'?ctx`) watches every context and binds the one that
  answered.

  **The unit is the settle: one settle, one call.**  A batch under
  `with-deferred-settle` / `assert-many` / `edit` settles once, so its event is exactly
  what `edit-with-consequences` reports for the same batch — a conclusion derived and
  then defeated inside the batch appears in neither.

  **`f` runs on the writing thread**, synchronously, after the settle and never inside
  it.  So it may read a settled KB and may write; a write produces its own event,
  delivered once the current round finishes.  A listener that writes on *every* event is
  an infinite loop, and delivery gives up after 64 rounds with a warning rather than
  hanging the writer.  One that throws is logged and skipped.  A listener doing real work
  should hand the event to a queue and return: this engine has one writer, and a slow
  listener slows it.

  **Four things never arrive**, and `preview` is what answers each: a mutation that moved
  no label; anything during a `preview`, `recover` or `reindex`; a datum the sweep
  *deleted*, which has no record left to describe; and a spelling an equality merge
  displaced.  `edit-with-consequences` has the last two gaps identically —
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
     (throw (ex-info "watch needs a function to call (a goal watch takes a context too)"
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
   ;; puts a function behind the seam — and `feed/deliver!`'s nil check then means
   ;; "nobody has ever watched this process", which is the cheapest possible answer
   (feed/install-dispatch! dispatch-feed!)
   (feed/register! kb (cond-> {:f f} goal (assoc :goal goal :context context)))))

(defn unwatch
  "Stop calling the listener `token` names; true if there was one.  Idempotent — a
  token already dropped removes nothing and says so."
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
  `:disk` KB that pays `recover` on the way back up — and the level a process started
  with is the answer to a question nobody had yet.

  Process-wide and not per-KB: two KBs in one JVM share one `*log-fn*`.  It is also the
  one setting here that changes the **process** rather than a KB, which is why
  `vaelii.impl.serve`'s op table does not carry it: every op in that table acts on the
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

(defn- recovered-supersessions
  "Every stored sentex the rebuilt equality closure displaces, as `refresh-supersessions`
  wants it.

  Recovery cannot read supersession back — it is derived from the closure, and recovery
  lands with the map empty (a fresh network holds none), exactly as it lands unblocked.
  Left that way, *both* spellings of every merged fact would be believed, which is a
  worse state than the merge simply being forgotten.  So the displaced sentexes are
  nominated once here and `supersession-map` filters them down to the ones whose twin
  is genuinely stored.

  Two sources, matching the two ways `rewrite-term` displaces a sentence: a **symbol
  merge** (walk the equality classes for every member's sentexes) and a **schematic
  rewrite** (a stored sentex the rule's LHS head reaches whose normal form differs).
  `supersession-map` re-derives the actual displacement — `rewrite-term` normalizes both
  — so this only has to name candidates.

  It names them by **class membership alone**, without asking whether the global
  election displaces the term.  Displacement is the *reader's*, and the global answer is
  not a superset of the scoped ones: a term can be the head of its whole class and still
  be retired inside a context whose visible edges elect someone else, when the
  `rewriteOf` that made it preferred is one that context cannot see.  Filtering here
  on the global read would drop exactly those, and recovery would come back believing
  both spellings."
  [kb]
  (concat
   (for [[a _] (tax/equality-edges (:taxonomy kb))
         t     (tax/equiv-class (:taxonomy kb) a)
         sx    (find-sentexes kb t)
         :when (kb/rewritable-sentex? kb sx)]
     [(:id sx) {}])
   (for [{:keys [lhs]} (tax/rewrite-rules (:taxonomy kb))
         sx (find-sentexes kb (first lhs))
         :when (kb/rewritable-sentex? kb sx)]
     [(:id sx) {}])))

(defn- rebuild-tms
  "Rebuild the network from the store: a node per stored sentex, a premise per rostered
  handle, and a justification per stored justification.  Belief is the composition of the
  region relabels the adds run, not a separate whole-graph pass.

  **No whole-graph relabel closes this.**  `add-justification` relabels its consequence's
  affected region as it lands, and a region relabel over the affected closure is equal to a
  global one (`jtms/relabel-region*`); premises are marked before any justification, so each
  add already reads its antecedents' final belief.  The region relabels therefore compose to
  the fixpoint a whole-graph `jtms/relabel` computes, and a global pass on top of them only
  recomputes what is already settled — measured at a third of `rebuild-tms` on a disk corpus
  (`scale-100m.md`, the recover decomposition's step 4).

  **And no reset of blocking or supersession either — recovery lands unblocked because it
  starts fresh.**  A network opened for recovery is empty, blocked and superseded sets
  included, so the region relabels above already label unblocked.  Neither is stored
  (docs/nmtms.md), so a rebuild cannot read either back; it need not clear them because the
  two are re-derived **wholesale** rather than merged — `recheck-every-exception` queues
  every exception-bearing rule and the settle *replaces* the blocked set (`jtms/set-blocked`),
  and `refresh-supersessions` replaces the supersession map — so not even a `core/reindex`
  over a live network can carry a stale one past the settle.

  **A justification naming a sentex this store does not hold is left out**, and this is
  the one path that can meet one.  Everywhere else a justification is built by a firing,
  whose antecedents are records the caller has in hand; here they are numbers off a
  store, and a store can hold a justification whose records are gone — `delete-sentex!`
  is on the protocol, and another dialect's loader is under no obligation to be
  consistent.  `add-justification` does not refuse one: the reference representation
  grows a phantom node for the missing datum and the dense one is not specified there
  (`vaelii.impl.dense-jtms`), and a justification *concluding* the phantom makes it IN —
  so the KB comes back believing a handle it cannot show anyone, and everything derived
  from it.  Skipped and counted instead, which is the policy `io.import` takes at the
  other end of the same store.

  The informant is deliberately not checked: it is not a node reference — `add-just*`
  builds adjacency for antecedents and `out` only — so a retired informant costs the
  network nothing."
  [kb]
  (let [tms     (:tms kb)
        rec     (:records kb)
        ;; `sentex-ids` is *the live handle set* by the RecordStore contract, and
        ;; `premise-ids` a subset of it — every backend's `mark-premise` guards on the
        ;; record existing before rostering the handle (memory.clj, disk record-store).
        ;; So neither loop re-reads the whole record to prove it is there: the node loop
        ;; trusts the set, and the premise loop tests membership in it (O(1), no fetch)
        ;; rather than fetching a frame per premise only to check for nil.  A fetch here
        ;; costs ~1 s of a 313k `recover` on disk and hours over a network store, all of
        ;; it to re-derive a fact the enumerator already answered.  A **justification** is
        ;; the one thing a store can hold over a sentex it does not (a `delete-sentex!`, a
        ;; foreign loader under no consistency obligation) — that loop keeps `stored?`.
        live    (p/sentex-ids rec)
        stored? (fn [h] (or (not (integer? h)) (some? (p/get-sentex rec h))))
        skipped (volatile! 0)]
    (doseq [id live]
      (jtms/ensure-node tms id 0))
    (doseq [id (p/premise-ids rec) :when (contains? live id)]
      (jtms/add-premise tms id (p/premise-strength rec id)))
    (doseq [id (p/justification-ids rec) :let [d (p/get-justification rec id)] :when d]
      (if (and (stored? (:consequence d)) (every? stored? (:antecedents d)))
        (jtms/add-justification tms d)
        (vswap! skipped inc)))
    (when (pos? (long @skipped))
      (trove/log! {:level :warn :id ::justifications-unrooted
                   :msg  (str @skipped " stored justifications name a sentex this store"
                              " does not hold and are left out of the network")
                   :data {:skipped @skipped}}))
    tms))

(defn- belief-certificate
  "The disbelief this recover settled, as data for `belief-snapshot/save!`: the
  content-keyed OUT sentexes, and whether the KB is **clean** — no definitional clash has a
  strength-differentiated loser (a member that is OUT while it stands in a clash pair).  A
  clash whose members are both IN (an equal-strength dilemma) has no loser and does not
  make the KB unclean; only a member the scan actually defeated does, and only such a KB
  must pay the scan on its next open.  The OUT set over-approximates cleanliness safely: an
  OUT sentex that happens to sit in a clash pair for an unrelated reason is counted a loser,
  which only forces the honest full recover rather than skipping it."
  [kb]
  (let [tms     (:tms kb)
        recs    (:records kb)
        clash   (some-> (:clashes kb) deref)
        pairs   (:pairs clash)
        members (into #{} cat (or pairs #{}))
        out-ids (into [] (remove #(jtms/in? tms %)) (p/sentex-ids recs))
        losers  (filterv #(contains? members %) out-ids)
        out     (into [] (keep (fn [id]
                                 (when-let [s (p/get-sentex recs id)]
                                   [(:sentence s) (:context s)])))
                      out-ids)]
    {:clean?       (zero? (count losers))
     :out-count    (count out-ids)
     :clash-count  (count (or pairs #{}))
     :clash-losers (count losers)
     :out          out}))

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
  Belief is settled last."
  [kb]
  ;; A **belief certificate** left by an earlier clean recover (`belief-snapshot/usable?`,
  ;; off by default) lets this one skip the closing settle's definitional-clash scan and
  ;; rederive identical belief.  The decision is taken once, against the records' current
  ;; fingerprint, and threads two ways: it turns the scan off in the settle below, and it
  ;; says not to rewrite a certificate this open just trusted.  Off, `fast?` is false and
  ;; this is byte-for-byte the recover it always was.
  (let [fast? (belief-snap/usable? (:records kb))]
    ;; The scoped closure memo (`tax/*scoped-memo-budget*`) is sized for steady-state, whose
    ;; hot working set is a few recently-touched contexts.  A cold rebuild is the opposite:
    ;; it reads the whole corpus from every context at once — OpenCyc induces 561 vissets by
    ;; the budget's own census — so the default 128 flushes and re-walks `specs` closures
    ;; forever, which the clash pass then pays per membership.  Widen it for the rebuild so
    ;; the whole context set stays memoised; this is pure cache size (docstring: "a heap, not
    ;; a wrong answer"), and the cap only bounds retention, so the memory is the working set
    ;; either way — the 561 closures the walk computes regardless, kept instead of redone.
    (binding [tax/*scoped-memo-budget* (max (long tax/*scoped-memo-budget*) 8192)]
      (rebuild-tms kb)
      ;; The rebuild replays every stored `genl` / `genlCx` edge, so it is a bulk load
      ;; and pays what one pays: repairing the depth potential per edge costs that edge's
      ;; descendants.  Defer it and repair once, exactly as `with-deferred-settle` does —
      ;; and repair *here* rather than leaning on the settle below, so the intervening
      ;; rebuilds never read a loose relation.  The reconcile shares that one repair, which
      ;; is why it sits inside the same deferral: dropping an edge can dissolve a component.
      (binding [tax/*defer-depths?* true]
        (special/rebuild-taxonomy kb)
        ;; Now narrow the replayed caches to belief, and **unconditionally**.  The
        ;; region-scoped arm of `refresh-beliefs` reconciles what a settle moved, and the
        ;; unsupported edge moves nothing: a record carrying no premise mark and no
        ;; justification is OUT from the moment `rebuild-tms` makes its node, so no defeat,
        ;; block or supersession ever names it and no region ever reaches it — while the
        ;; replay has already made it answer `genls`.  (The *defeated* edge is narrowed
        ;; either way, since its opposition is an event the settle reacts to.)  Recovery is
        ;; exactly the caller holding no region that the `nil` arm exists for, and it costs
        ;; one belief lookup per stored declaration — what the replay above just paid.
        ;; Before the settle rather than after it, so everything the settle reads — nogoods,
        ;; placement, exception queries — reads a taxonomy that already agrees with belief;
        ;; the settle's own reconcile then keeps the two together across whatever it moves.
        (tax/refresh-beliefs (:taxonomy kb) #(jtms/in? (:tms kb) %)))
      (tax/restore-depths (:taxonomy kb))
      ;; Nothing about an exception is stored, so blocking cannot be read back: recovery lands
      ;; unblocked (a fresh network holds no blocks, and the settle below re-derives them) and the
      ;; window in between believes an excepted conclusion.  Queue every exception-bearing rule so the settle
      ;; below re-evaluates and withdraws them.  This is recovery, not a store mutation,
      ;; so it is a deliberate explicit trigger rather than the choke-point seam: no
      ;; sentence arrived or left — the whole in-memory blocking state did.
      (special/recheck-every-exception kb)
      ;; ...and the same for supersession, which is derived from the equality closure and
      ;; is likewise not readable back from the store.  Seeded before the settle, since
      ;; `refresh-supersessions` only re-examines the entries it already holds.
      (special/refresh-supersessions kb (recovered-supersessions kb))
      ;; the P/¬P coincidence set is derived from storage and no store holds it, so rebuild
      ;; it before the settle below reads it (`settle/negation-nogoods`)
      (kb/rebuild-opposed! kb)
      ;; ...and the visibility roster, for the same reason and one more: a **fork** rebuilds
      ;; its belief over the merged view rather than inheriting it (`fork`), so without this
      ;; a fork would answer its base's excepts off a roster of its own that nothing filled.
      ;; Before the settle for the same reason too — `justification-excepted?` reads it.
      (kb/rebuild-excepted! kb)
      ;; The first cache reconcile ran before the visibility roster existed, so it
      ;; could narrow only against JTMS belief. Re-run through the common transition
      ;; boundary now that recovery can also answer which declarations are excepted.
      (special/reconcile-belief-change! kb)
      ;; ...and the settle that finishes the rebuild is told it *is* one, so the exposure
      ;; pass stays out of it: what it reports is what a change newly made jointly visible,
      ;; and a restore changes nothing (`settle/*rebuilding?*`).  On the certified fast path
      ;; the clash scan is off for the same settle: a clean KB's scan defeats nothing, so the
      ;; rest of this settle rederives the same belief without it (`*skip-constraint-nogoods*`).
      (binding [settle/*rebuilding?* true
                settle/*skip-constraint-nogoods* fast?]
        (settle/settle kb)
        ;; The **refusal** record is the other in-memory state no store holds: a firing
        ;; refused at derive time left no justification, so replaying the stored ones cannot
        ;; put it back, and a KB restarted with refusals standing would answer a later
        ;; release differently from one that never restarted.  Re-firing the rules that can
        ;; refuse re-records what they refuse, and it runs after the settle above because a
        ;; refusal is a claim about what the KB *believes*.  A re-fire that placed something
        ;; the narrowed re-chain had not owes a second settle.
        (let [{:keys [derived]} (chain/rerecord-refusals! kb)]
          (when (pos? (long (or derived 0))) (settle/settle kb))))
      ;; The slow recover just settled belief from scratch, so leave a certificate: the next
      ;; cold open over these same records can then take the fast path.  Only the slow path
      ;; writes one — the fast path already trusted a valid one — and only a disk KB with the
      ;; switch on (`belief-snapshot/writable?`), so a KB with nowhere to put it, or the switch
      ;; off, never even computes the disbelief.
      (when (and (not fast?) (belief-snap/writable? (:records kb)))
        (belief-snap/save! (:records kb) (belief-certificate kb)))
      ;; Belief now exists over whatever the store holds, so the write doors stop refusing
      ;; on that count.  Only that count: a **derived** index is not rebuilt here — `recover`
      ;; reads it rather than writing it — so a KB recovered over one still mints a second
      ;; handle per assert, and `reindex` is the call that clears the other half.
      (kb/note-hazards! kb {:no-belief false})
      kb)))

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

(defn clear!
  "Wipe the KB's durable stores — every record and every index entry — the
  backend-agnostic counterpart to `recover`: `recover` rebuilds the in-memory JTMS /
  taxonomy *from* the stores, this empties the stores.  `!` because it destroys stored
  knowledge irreversibly.

  It does **not** reset the in-memory JTMS / taxonomy, so call it on a freshly-opened
  KB (an empty in-memory state) or immediately before reloading content — the shape a
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
  ;; resident derived structure stamps itself with has to be bumped by hand here
  (observe/note-change)
  ;; the clock covers the resident *values*, which are rebuilt on the next read
  (some-> (:qcn kb) (reset! {}))
  ;; ...and the qualitative join baselines, which it does not: they live in their own
  ;; map beside the network cache and outlive a clock tick on purpose
  ;; (`qcn-kb/note-joined`), so the wipe is the one thing that reaches them.  Hygiene
  ;; rather than the correctness argument — a baseline describing a KB that no longer
  ;; exists is already safe, since the handles it recorded are gone and a missing handle
  ;; is what makes the next delta `:all` — but a wipe is exactly the moment to stop
  ;; carrying it.
  (some-> (:qcn-joined kb) (reset! {}))
  ;; ...and the refusal record, for the same reason and a stronger one: it is keyed by
  ;; rule handle and retired at the rule's own departure, which a wholesale wipe of the
  ;; stores never reaches.  Every entry names handles this call just deleted.
  (some-> (:refused kb) (reset! {}))
  ;; ...and the stamp the supersession reconcile narrows against, for the third form of
  ;; the same reason: it describes an equality closure over records this call just
  ;; deleted, and a stamp that still compares equal would carry entries naming them.
  ;; Clearing it says "reconcile everything", which is the answer for a wiped store.
  (some-> (:supersessions kb) (reset! nil))
  ;; ...and the visibility roster, which is the one of these that would be *wrong* rather
  ;; than merely stale: its entries are handles, the wipe resets the handle counter, and
  ;; a reload would hand handle 42 to a new sentex the old roster still says is hidden.
  ;; `:opposed` keys on bodies and cannot mistake one fact for another this way, which is
  ;; why it is not here and this is.
  (some-> (:excepted kb) (reset! {}))
  ;; ...and back to undetermined, not to "recovered".  This is the reset-and-reload
  ;; shape's own call, and what follows it may be an `import-dump` that lands records
  ;; and skips the recover — so the write-side question has to be re-asked over what
  ;; arrives next, rather than answered "no" by a wipe that emptied the store.
  (some-> (:unrecovered kb) (reset! {}))
  kb)

(defn close!
  "Release a durable KB's directory: flush and close the record store, drop it from the
  durability daemon, and **release the exclusive file lock**.  Returns the KB.

  A `{:backend :disk :dir …}` KB takes an exclusive `FileLock` on its directory when it
  opens, and without this the lock is held until the JVM exits — so a long-running
  process could not hand the directory to another process, reopen it elsewhere, or
  release it after a load it no longer needs.  `clear!` is the other half of the pair
  and answers a different question: `clear!` destroys the *content* and leaves the
  store open, this keeps the content and lets go of the store.

  **The stores belong to the directory, not the KB value**: two KBs opened over one
  directory share them, so closing either closes both, and neither may be used
  afterwards.

  On a `fork` this releases the fork's **own** writable directory — the one `{:backend
  :disk :dir …}` in its opts named — and never the base's.  A base is mounted read-only
  and shared by every fork taken over it, so it is nobody's fork to close; release it by
  closing the KB it was opened as.

  A no-op on a KB with no directory (every in-memory backend, and an ephemeral fork), so
  it is safe to call unconditionally in a `finally`.  The KB must not be used
  afterwards; open it again to read the same directory.

  A durable records backend that is not the disk store — the `:sqlite` adapter, which
  holds a JDBC connection rather than a directory — releases its resource here too: any
  record store that is `java.io.Closeable` is closed.  The disk store is torn down by
  `close-dir!` above and is not `Closeable`, so this fires once, for such a backend, and
  never twice."
  [kb]
  (when-let [dir (:dir kb)]
    (disk/close-dir! dir))
  (when (instance? java.io.Closeable (:records kb))
    (.close ^java.io.Closeable (:records kb)))
  kb)

(defn import!
  "Read an export dump from `dir` into the (empty) `kb`, and return a summary — the
  inverse of `export!`, which is the only reason this is here: a round trip whose two
  halves are not both public is not a round trip.

  `opts`: `{:belief? true|:stored|false :report-every n :on-progress f}`.  With
  `:belief? true` (the default) the dump lands in the state a restart produces — records,
  justifications and premise marks stored, index rebuilt, belief recovered.  With
  `:belief? false` every sentex is stored and indexed but no justification stream is read
  and nothing is recovered: browsable, findable and countable, but not belief-queryable.
  That is the path for a corpus past what an in-RAM JTMS scales to.

  `:belief? :stored` is the middle, and it is what a corpus that cannot afford `recover`
  *today* wants: everything `true` stores is stored — justifications, premise marks,
  provenance, the index — and only the recover is left for later, as its own job over the
  finished store.  For a dump in a **foreign** dialect it is the only mode that keeps them
  at all: the records-only path carries no strength onto a foreign record and rosters no
  premise, so a later `recover` over that store believes nothing.

  `:on-progress` is called every `:report-every` frames (default 500000) with
  `{:phase :done :total}`.  A key this fn does not read is refused (`:unknown-option`), as
  at `export!`, and so is an unrecognised `:belief?` value — anything truthy would
  otherwise mean `true`.

  A dump in a foreign dialect needs the reader plugin that declares it
  (`vaelii.impl.foreign`); one this build cannot read is refused by name.

  Two counts in the summary are disagreements between the dump and this build, and
  neither stops the load: `:naming` is what got stored that `assert` would refuse, and
  `:refused` is what could not be **built** at all — a rule whose structure a
  since-widened check now rejects.  The second is skipped, along with whatever rests on
  it, and reported; `:sentexes` and `:frames` differ by those plus `:collapsed`."
  ([kb dir] (import! kb dir {}))
  ([kb dir opts] (wiring/import-dump kb dir opts)))

(defn export!
  "Write `kb` out as a portable **export dump** in `dir` and return a summary:

      {:variant :records :sentexes n :justifications n :provenance n
       :index-entries n :bytes n :elapsed-ms n :dir \"…\"}

  A dump is a directory of **field-map frames** — no frame carries a class name — so it
  survives a backend change, an index-representation change, and a record class rename,
  none of which the `:disk` store's own directory survives.  What it holds is what the
  record store holds, because everything else is derived: the index is a cache
  (`reindex`), belief and the taxonomy are recomputed (`recover`).  Read back with
  `import!`.

  `opts`: `{:variant :records|:records+index :compression :gzip|:xz|:none :chunk-size n
  :provenance? bool :on-progress f}` (defaults `:records`, `:gzip`, 10000, true).
  `:records+index` writes the index too, as a cache a reader replays only if it can prove
  it describes the records beside it.  `:provenance? false` drops the per-handle
  annotation — an open map with no size bound, measured at 57% of the converted engine
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

;; ---- four-valued epistemic status --------------------------------------
;; `argue` reads both a sentence and its explicit negation and reports where belief
;; stands between them, with a small argumentation stub for the both-provable case.  It
;; is a read built entirely on `ask`/`query`/`why`, so it lives here on the public
;; surface rather than under `impl` — a caller (a coordination layer adjudicating a
;; dispute, a UI coloring a claim) wants the verdict without reconstructing it.

(defn- argue-results
  "Query results for `goal` in `context` — a seq of binding maps (an empty map for a
  ground goal), or nil if not provable.  Rules fire only with `:max-depth`."
  [kb goal context opts]
  (seq (if (:max-depth opts)
         (query kb goal context opts)
         (ask kb goal context))))

(defn- argue-justification
  "The full `why` map for `sentence` in `context` when it is stored and believed, else nil."
  [kb sentence context]
  (when-let [h (handle-of kb sentence context)]
    (when (in? kb h)
      (why kb h))))

(defn- argue-defeat-class
  "The JTMS defeat-class (`:monotonic` / `:default`) of `sentence` in `context`, or nil."
  [kb sentence context]
  (:defeat-class (argue-justification kb sentence context)))

(defn- argue-resolve-contradiction
  "Argumentation stub for the both-provable case: a `:monotonic` justification beats a
  `:default` one.  Returns `:true` if the positive side wins, `:false` if the negative
  side wins, or nil if the clash cannot be resolved this way (leaving `:contradiction`).
  Resolves monotonic-vs-default only — specificity, recency, authority and user-defined
  preference orderings are not yet implemented."
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
       :for-why     <justification for asent, when stored and believed>
       :against-why <justification for (not asent), when stored and believed>}

  Without opts it uses `ask` (ground facts + prover registry, no rule expansion);
  callers who want rules to fire MUST pass `{:max-depth N}` explicitly — a silent
  default depth would turn a derivable fact into a false `:unknown`.

  When both sides are provable the verdict is `:contradiction` unless the argumentation
  stub resolves it: a `:monotonic` justification wins over a `:default` one (the engine
  itself leaves both standing — paraconsistent tolerance, docs/nmtms.md)."
  ([kb asent context] (argue kb asent context nil))
  ([kb asent context opts]
   (let [neg       (list 'not asent)
         for-r     (argue-results kb asent context opts)
         against-r (argue-results kb neg context opts)
         pos?      (boolean (seq for-r))
         neg?      (boolean (seq against-r))
         for-j     (argue-justification kb asent context)
         against-j (argue-justification kb neg context)
         base      (cond-> {}
                     pos?      (assoc :for for-r)
                     neg?      (assoc :against against-r)
                     for-j     (assoc :for-why for-j)
                     against-j (assoc :against-why against-j))]
     (cond
       (and pos? (not neg?)) (assoc base :verdict :true)
       (and neg? (not pos?)) (assoc base :verdict :false)
       (and (not pos?) (not neg?)) (assoc base :verdict :unknown)
       :else (if-let [resolved (argue-resolve-contradiction kb asent context)]
               (assoc base :verdict resolved)
               (assoc base :verdict :contradiction))))))

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
