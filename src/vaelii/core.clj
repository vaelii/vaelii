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
            [vaelii.impl.context-nat :as context-nat]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.defining :as defining]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.except :as exc]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.fluent :as fluent]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.inference :as inference]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.integrity :as integrity]
            [vaelii.impl.io.digest :as digest]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.io.import :as io-import]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
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
            [vaelii.impl.overlay.rebase :as rebase]
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
            [vaelii.impl.rewrite-query :as rewrite-query]
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

;; `recover` and `reindex` are defined at the bottom of this namespace, and `open-kb`'s
;; `:recover? :auto` needs both, so they are injected into construction
;; (`vaelii.impl.kb`).  `finish-pending-rebase!` and `finish-follow!`, which `open-kb` and
;; `fork` run on a durable fork, write through entry points defined below `open-kb`.
(declare recover reindex finish-pending-rebase! finish-follow!)

(defn- releasing-on-throw
  "Call `construct`, which opens the KB `opts` describes.  When it throws after the durable
  stores resolve, close only the directories this call newly opened, writing no image, drop
  the engine space `opts` names (`mem/engine-space`, which no caller holds), and rethrow.
  A directory already open before the call stays open."
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
        (kb/release-engine-space!
         (some #(when (mem/engine-space? %) %) [(:space opts) (:space (:overlay opts))]))
        (throw t)))))

(defn open-kb
  "Construct a KB.  Every option is optional; `(open-kb {})` is records and index in RAM.

  | opt | what it picks | default |
  |---|---|---|
  | `:backend` | a records×index pair, `<records>-<index>` | `:memory` |
  | `:records` / `:index` | one axis of that pair | from `:backend` |
  | `:space` | which in-RAM stores this KB shares | `0` |
  | `:dir` | the directory of a durable half | derived from the space |
  | `:base` / `:overlay` | the two halves of an `:overlay` fork | — |
  | `:tms` | `:dense` or `:reference` | `:dense` |
  | `:naming` | `:strict` / `:warn` / `:off` | `:strict` |
  | `:recover?` | `:trust` / `:auto` (or `true`) / `:background` / `:warn` / `false` | `:trust` |
  | `:oplog?` | `true` (or `:each`) / `:tick` / `false` | `false` |
  | `:reasoners` | the shipped reasoners to register, or `:stored` | none |
  | `:fork-dirs` | durable forks' directories, whose handles this base never issues | none |

  An unread option is refused (`:unknown-option`), and an unrecovered KB refuses writes
  (`:unrecovered-kb`; `*write-unrecovered?*` accepts them).  docs/storage.md, \"Opening a KB\"."
  ([] (open-kb {}))
  ([opts]
   (let [plain (fn [o]
                 (let [k (recovery/register-fresh-store! (kb/open-kb o recover reindex rebase/follow-base!))]
                   (doto (kb/register-reasoners! k (kb/reasoners-of k))
                     finish-pending-rebase!
                     finish-follow!)))
         mode  (kb/oplog-mode opts)]
     (releasing-on-throw opts (if mode
                                #(seal/open! opts plain {:fsync mode})
                                #(plain opts))))))

(defn fork
  "A private, writable KB over this one's stores (a **fork**).  Reads resolve fork-first and
  fall through to `kb`; writes land only in the fork.

  `opts` is the fork's own storage (default `{:backend :memory}`, dropped by `close!`;
  `{:backend :disk-log :dir …}` is durable).  `:tms` takes the engine default when unnamed;
  `:naming` and the registered reasoners inherit from `kb`.  A `:columnar` index is refused.
  Mount and remount rules: docs/overlay.md."
  ([kb] (fork kb {}))
  ([kb opts]
   (let [own    (dissoc opts :tms :naming)
         ;; A RAM overlay naming no :space would land on the shared default (space 0), so
         ;; opts naming neither a :space nor a :dir take the fresh fork space; naming one
         ;; explicitly stays the remount spelling.
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
                 :reasoners (kb/reasoners-of kb)
                 :recover? false}]
     (releasing-on-throw spec #(let [k (doto (kb/open-kb spec recover reindex rebase/follow-base!) recover)]
                                 (doto (kb/register-reasoners! k (kb/reasoners-of k))
                                   finish-follow!))))))

(def default-chain-opts
  "The bounds a chaining run takes when `opts` names none: `:max-term-depth`, the
  termination bound for term-building recursion, and `:max-derivations`, the cap on one
  run's writes.  `:max-depth` has no default (docs/inference.md, \"Forward chaining\")."
  chain/default-chain-opts)

;; ---- the content order ---------------------------------------------------
;; The engine's own order is public so an application ranks its answers by it: breaking a
;; tie on a handle, allocated in assertion order, would make the ranking a fact about how
;; the KB was loaded.

(defn sort-by-content
  "`coll` ordered by `(keyfn element)` under `cmp`, the engine's **content** order, for
  ranking sentexes, sentences or terms instead of `sort-by` on a printed key or a handle.

  `cmp` defaults to the structural comparator the engine's orders use; pass `compare` when
  the key is already a `Comparable` tuple.  A `keyfn` that returns a handle makes the
  ranking depend on load order: key on `:sentence` / `:context` (docs/nmtms.md)."
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

(defn defining-contexts
  "The maximal contexts of ordinary believed assertions about term. Literal Quote,
  nested-sentence mentions and skeletal-only assertions do not define a term. Throws
  :incomplete-defining-contexts when a believed support cannot be classified."
  [kb term]
  (defining/defining-contexts kb term))

;; ---- the vocabulary: enumerate and search the terms themselves ----------
;; `find-sentexes` goes from a term to the sentexes mentioning it; these answer *which
;; terms are there*, from the index's term-name set, so the cost is the size of the
;; **vocabulary**, never of the KB.

(defn terms
  "Every term the index is keyed by: each predicate, individual, type and context name
  mentioned by a stored sentex, at any nesting depth, as a vector sorted by name.  Cost is
  O(terms).  A ground compound subterm is not a name and is not listed.  Defeated and
  unsupported sentexes keep their names here (docs/indexing.md)."
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

(def ^:private opt-silences
  "Per kind of entry point, the clause `opts/check!` appends to an `:unknown-option`
  refusal: what the default taken in silence would have done.  The kinds are `:bound` (a
  cap or deadline), `:extent` (the belief filter), `:assert` (`:strength`), `:chain` (a
  chaining ceiling) and `:search` (a prove/ask deadline).  docs/api.md, \"An option key nothing reads\"."
  {:bound  (str "An option nothing reads takes the default in silence, which for a bound"
                " means running or answering uncapped.")
   :extent (str "An option nothing reads takes the default in silence, which here means the"
                " stored extent — defeated defaults included — where the believed one was"
                " asked for.")
   :assert (str "An option nothing reads takes the default in silence, which for :strength"
                " means storing a default where known-true was meant.")
   :chain  (str "An option nothing reads takes the default in silence, which for a bound"
                " means running unbounded.")
   :search (str "A bound nothing reads is an unbounded search in silence, on an entry point"
                " whose whole point is that the search stops.")})

(defn- check-opts!
  "Refuse a non-map `opts` and any key outside `opt-keys` (`opts/check!`, with the `kind`
  clause from `opt-silences`), then, for every kind but `:bound`, the value domains
  (`opts/check-values!`).  `fn-name` names the entry point in the message."
  [kind opts opt-keys fn-name]
  (opts/check! opts opt-keys fn-name (opt-silences kind))
  (when-not (= :bound kind)
    (opts/check-values! opts fn-name)))

(defn- check-limit!
  "Refuse a cap that is not a positive integer (`:unknown-option`), `where` naming the
  entry point and the spelling it arrived under (`\"find-terms :limit\"`).  A caller with an
  optional cap tests for the key first (`when-some`): an absent cap is no cap."
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
  than `budget` characters.  The scan-wide counter `scan` is shared by every candidate of
  one `find-terms` and refused past `scan-budget` with the same `:type` and `:scope :scan`."
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
  "The first `n` of `(sort xs)` without sorting `xs`: a bounded selection in one pass,
  O(m log n) for m hits.  Identical to the full sort and take, ties included (each
  candidate carries its position, and the order is `compare` then position).  The heap's
  initial capacity is a small floor, not `n`, because `n` is a caller's `:limit`."
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
  "The vocabulary terms whose name matches `q`, sorted by name.  Cost is the size of the
  vocabulary.

  `opts`:

    :match           :prefix (default) | :substring | :regex
    :case-sensitive? false by default; ignored by :regex (use `(?i)`)
    :limit           keep the first n of the sorted answer; a non-positive-integer is
                     refused (`:unknown-option`)

  `q` is a string or symbol, or under `:regex` a compiled `Pattern` in-process.  An
  unparsable regex throws; a pattern past its step budget throws `:pattern-too-costly`."
  ([kb q] (find-terms kb q nil))
  ([kb q opts]
   ;; the key set first: a misspelt `:mtch` or `:case-sensitve?` silently ran the
   ;; default search, and a prefix answer where substring was asked for reads as
   ;; \"no such term\" — in the browser's own search box, over the wire
   (check-opts! :bound opts #{:match :case-sensitive? :limit} "find-terms")
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
  The seq reads live state; `vec` it for a snapshot.  The daemon's wire does so for every
  remote reader."
  [kb handles]
  (->> handles (map #(p/get-sentex (:records kb) %)) (filter some?)))

;; ## Stored vs believed
;; The three `count-*` readers read set cardinalities: no records fetched, no belief
;; consulted.  They count what is **stored**, including a sentex the JTMS holds OUT, so
;; `(count (sentexes-matching ...))` and `(count-with-functor ...)` can disagree.  The
;; extent fns take an optional `{:believed? true}`, a record fetch plus a TMS lookup per
;; handle, O(n); there is no O(1) believed count.

(def ^:private extent-opt-keys
  "Every key the extent readers (`sentexes-in-context` / `sentexes-with-functor` /
  `sentexes-with-arg`) read."
  #{:believed?})

(defn- believed-filter
  "Apply the extent fns' `{:believed? true}` option: keep only sentexes believed as their
  own context reads them (`res/believed-at?`) — IN in the network, and not withdrawn from
  that context by a scoped defeat.  O(n) in the extent — the caller opted into it."
  [kb opts sentexes]
  (if (:believed? opts)
    (filter #(res/believed-at? kb (:id %) (:context %)) sentexes)
    sentexes))

(defn sentexes-in-context
  "Every **stored** sentex asserted in `context` (its extent, rules included), a defeated
  or unsupported one included.  Pass `{:believed? true}` to keep only what the JTMS
  believes, at a TMS lookup per handle.  An opts key this fn does not read is refused
  (`:unknown-option`).  The result is a lazy seq over live state (see `records-of`); `vec`
  it for a snapshot."
  ([kb context] (sentexes-in-context kb context nil))
  ([kb context opts]
   (check-opts! :extent opts extent-opt-keys "sentexes-in-context")
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
   (check-opts! :extent opts extent-opt-keys "sentexes-with-functor")
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
   (check-opts! :extent opts extent-opt-keys "sentexes-with-arg")
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
  "The naming role of `term`: `:variable` (`?x`), `:number`, `:lexeme`, `:context`,
  `:individual`, `:predicate`, `:sense`, `:type`, or nil (a string, or a symbol matching
  no convention).  Reads the naming invariants `assert` enforces (docs/naming.md).  The
  most specific role wins: `:lexeme` before `:context` before `:individual`, and `:sense`
  before `:type`."
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
;; The cached genl / genlCx closures and the predicate metadata delegate to
;; `vaelii.impl.taxonomy`, each a map lookup over in-memory sets.  Reads only: `assert` /
;; `retract!` maintain edges and metadata, and there is no public mutator.

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
  a supertype of one of these.  Read over every believed edge, whatever installed it: a
  stated `(genl dog animal)` beside `dog ⊂ mammal ⊂ animal` leaves `animal` out.  Two
  parents that subsume each other are both members.  Not reflexive.  A set; `#{}` when `t`
  is not a node.  With a `context`, only edges visible from it count; the short arity
  reads the KB-wide edge set, as `genls` does."
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
  member of `types` and have no other such member strictly below them.  Not reflexive: for
  `dog` and `mammal` under `dog ⊂ mammal ⊂ animal` the set is `#{animal}`.  One distinct
  type gives `min-genls` of it.  A set.  With a `context`, only edges visible from it
  count; the short arity reads the KB-wide edge set.  `(minCommonGenl ?x t1 t2 …)` asks
  the same question as a query."
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
  "Does `pred` carry the metadata property `kind`?  `vaelii.impl.predicates/prop-kinds`
  enumerates the kinds (docs/api.md).  A kind outside the list answers false.

  With a `context`, the declaration must be visible from it, except `:symmetric`,
  `:commutative` and the two forced-monotonic kinds (docs/nmtms.md).  The 3-arity reads the
  KB-wide declarations.  `transitiveInArg` is read through `matches-visible`
  (docs/inherit.md)."
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
;; parentOf 2)` is well-formed, stored and believed whether or not it is enforced, so the
;; answer is published.

(defn interpreted
  "What the engine does with vocabulary term `term`: `{:enforced \"where\"}`,
  `{:inert \"why\"}`, or nil.  `:enforced` means a code path reads the term and the KB
  refuses, derives or answers differently because of it; the string names the path.
  `:inert` means nothing does, and the string says why.  Nil means the term is not one
  core.txt comments, so an ordinary domain predicate is out of scope.  `vocabulary-audit`
  classifies every declared term."
  [term] (vocab/classify term))

(defn vocabulary-audit
  "Every term core.txt comments in `kb`, classified: `{:enforced [[term why] …]
  :inert [[term why] …] :unclassified [term …] :retired [term …] :contradicted [term
  …]}`.  `:unclassified` is a declaration nobody classified, `:retired` a classification
  of a term the KB no longer declares, `:contradicted` a term the special-predicate table
  gives an arm to and the classification calls inert.  The three are empty on the shipped
  ontology."
  [kb] (vocab/audit kb))

;; ---- the knowledge, as against the engine -------------------------------
;; `settle-stats`, `chain-stats` and `violations` report on a *run*; none reads the KB.
;; The seven questions below are the ones an author of a large KB asks.

(defn kb-quality
  "Seven readings about the knowledge, one map with the keys `:rules`, `:extents`,
  `:chains`, `:taxonomy`, `:declarations`, `:subsumption` and `:clashes`, each a
  distribution rather than a number (shapes: docs/quality.md, \"The result map\").  Data,
  not a printer: `quality-report` renders it.

  `opts`: `:limit` caps each listed set (default 25); `:on-progress` is called with
  `{:phase :done :total}` and may throw to cancel; an unknown option is refused
  (`:unknown-option`).  Extents count what is stored, not what is believed."
  ([kb] (kb-quality kb nil))
  ([kb opts]
   (check-opts! :bound opts #{:limit :on-progress} "kb-quality")
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
  Not the complement of a provable `(different a b)`: both read false of an unmerged
  `indeterminate_term` (docs/predall.md).  `(not (same-class? …))` answers \"not known to
  be the same thing\"."
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
  "When true, `assert` runs in **bulk-load mode** for a caller-guaranteed well-formed,
  pairwise distinct premise load.  `assert-one` skips the definitional checks, the
  `find-sentex-handle` dedup walk and provenance recording; no argument-type entailment is
  drawn (`record-arg-types` records them afterwards).  A refusal or a bound the caller
  set still throws and rolls back (`undoing-refusal`).  `with-deferred-settle` and
  `{:chain? false}` complete the fast path; `bulk-assert-facts!` does all three."
  false)

;; ---- writing into a KB whose derived state was never built ---------------

(def ^:dynamic *write-unrecovered?*
  "When true, accepts writes into a KB opened over a store whose derived state was never
  built (`{:recover? false}` or `:warn` over a populated store, or an `import-dump` with
  `:belief? false` / `:stored`).  False by default, which refuses them (`:unrecovered-kb`);
  the repair is `recover`, or `reindex` when the index is derived.  Binding it accepts
  unchecked, possibly mis-keyed and duplicated writes (docs/storage.md, \"Why a write into
  an unrecovered KB is refused\").  `:unrecovered-premise` and `:stale-belief` refuse
  whatever this says.  `*bulk-load?*` is a different switch."
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
  "`writable-problem` as `check` reports problems, or nil.  Nil under
  `*write-unrecovered?*`, except `:stale-belief`, which the opt does not cover."
  [kb where]
  (when-let [p (writable-problem kb where)]
    (when (or (not *write-unrecovered?*) (some #{:stale-belief} (:hazards p)))
      [p])))

(defn- check-writable!
  "The write entry points' one check: refuse an unrecovered KB by name, or, under
  `*write-unrecovered?*`, let the write through and log once per KB what it gave up.  The
  hazard is read before the problem is built, so the accepted-write path allocates
  nothing."
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

;; Rule assertion is *idempotent*: an α-equivalent rule dedups to the stored handle and
;; resolves its engines, defeasibility and strength from content, widening only
;; (`assert-entry/reconcile-rule-slots!`, docs/inference.md).  To narrow a rule's
;; direction or defeasibility, retract it and assert the narrower spelling.

;; ---- provenance ---------------------------------------------------------
;; A per-handle bookkeeping map (creator + creation date, plus application fields) kept
;; beside the record (protocols/RecordStore).  Belief never reads it, so a wall-clock
;; `:created` cannot affect order independence.

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
;; The write-mode reify lives in `vaelii.impl.nat`, the post-assert reconciliation and
;; orphan sweep in `vaelii.impl.nat-maintenance`, and skolemizing an existential head in
;; `vaelii.impl.skolem`.  `retract!` and `edit` are forward-referenced because the write
;; path and the query family are interleaved here: `finish-teardown!` and
;; `rollback-batch!` hand `retract!` to the orphan sweep, `rehome-forced-extent!` uses
;; `edit!`, and `abduce` is handed `edit`.

(declare retract! edit!)

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
  context is a bare symbol or a ground application `(CxTimeFn …)` that reifies to its
  `cx/` constant (docs/context-nat.md; `nat/context-application?`).  The test reads the
  form alone, so it does not depend on `:naming` or on declaration order.  A query
  context (`nm/query-contexts`) is refused whatever `:naming` says (docs/contexts.md)."
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
  "The `:shape` problem a would-be assertion is refused with before it is a sentence, or
  nil.  A sentence is an s-expression that is a list: a string, a symbol, a number, a map
  or nil is refused, and a vector is refused because it canonicalizes to the list it
  looks like while every read entry point means a conjunctive query by it (docs/api.md,
  \"a top-level vector\").  A bare `(sentexHandle N)` is refused because it names a
  stored sentex and states nothing, and a `.` outside a rest marker by `sx/dot-problem`.
  `check`, `assert` and `assert-inert` read this one fn, so what `check` predicts is what
  both writes do."
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
                   (count sentence) ".  Write " (pr-str (apply list sentence)))}

    (sx/sentex-handle? sentence)
    {:type :shape :sentence sentence
     :message (str (pr-str sentence) " names a stored sentex and states nothing")}

    :else (sx/dot-problem :sentence sentence)))

(defn- check-shape!
  "Throw the `:shape` refusal `check` reports for a context or sentence that is not one.

  Called in `shape-problems`' own precedence — context, then opts, then sentence — so the
  two entry points refuse the same input for the same reason."
  [problem]
  (when problem
    (throw (ex-info (:message problem) (dissoc problem :message)))))

(defn- disjunction-shape-problem
  "The problem an `or` the polycanonicalization cannot expand away is refused with, or
  nil: `rules/disjunction-problems` as one problem map.  Both entry points read it right
  after the connective frames, because the expansion runs before the rule checks and a
  rule too wide to split must be refused before the split."
  [sentence]
  (first (rules/disjunction-problems sentence)))

(defn- check-sentence-shape!
  "The five refusals a would-be assertion earns before any check reads the KB: an
  s-expression that is a list rather than a vector, whole connective frames, every `or`
  expandable by the polycanonicalization, a well-formed structural term, and every leaf
  surviving the durable log.  In `shape-problems`' order, which is `assert`'s.  Both
  `assert` and `assert-inert` run all five, so neither stores what the other refuses.  The
  context guard stays at the call sites."
  [sentence]
  (check-shape! (sentence-shape-problem sentence))
  (check-shape! (sx/connective-problem sentence))
  (check-shape! (disjunction-shape-problem sentence))
  (check-shape! (checks/term-shape-problem sentence))
  ;; Every leaf must survive the durable log: a non-serializable value (a function, an
  ;; atom) stores in memory and throws at write time on the first disk backend, so the
  ;; same assert would succeed or fail by backend.  Refused here, before anything is
  ;; stored, exactly as `shape-problems` reports it to `check`.
  (checks/check-encodable sentence))

(def ^:private direction-values
  "What a `:direction` opt may say — the `set/*Rule` wrappers' values plus `:both`, which
  is what a bare `(implies …)` already is and so has no wrapper."
  (into #{:both} (vals sx/rule-direction-wrappers)))

(defn- direction-opt-problem
  "The problem an `opts :direction` carries, as a value, or nil when it is applicable.
  `apply-direction-opt` throws what this returns and `check` reports it.

  Four refusals: a value outside `direction-values`; a direction on a non-rule; a
  direction on a choice or constraint rule, which never chains; and a direction that
  disagrees with a wrapper the sentence already carries."
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
  of, or refuse it (`direction-opt-problem`).  `assert-rule` spells it this way already."
  [sentence opts]
  (let [d (:direction opts)]
    (if (nil? d)
      sentence
      (do (check-shape! (direction-opt-problem sentence opts))
          (let [[written] (sx/peel-rule-wrapper sentence)]
            (if (some? written) sentence (rules/wrap-direction sentence d)))))))

(defn- check-assert-opts!
  "Refuse an opts key `assert` does not read (`:unknown-option`), and a `:strength` that is
  not an assertable class (`:default` or `:monotonic`).  Either would store the sentence
  at a defeat class the caller did not ask for.  Undercutting is `exceptWhen`'s job
  (`vaelii.impl.strength`)."
  [opts]
  ;; A non-nil non-map `opts` is refused here rather than ignored, so that `check` and
  ;; `assert` agree: `shape-problems` runs this same fn, and a guard that only
  ;; looked inside a map would let `(assert kb s ctx :oops)` sail through taking every
  ;; default while `(check kb s ctx :oops)` said it would not.
  (check-opts! :assert opts assert-opt-keys "assert")
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
  "The refusal a storage teardown of `handle` earns, as a value, or nil.  `retract-storage!`
  throws it and `edit!` asks it of every removal in a batch before the first one runs.

  Refused: a forced-monotonic declaration (`checks/forcing-retraction-problem`); the inert
  rule an argument-type mint is justified under (`special/mint-rule-retraction-problem`); and,
  where the belief network was never built, every handle without a node
  (`:unrecovered-kb`).  `where` names the entry point for the refusal's `:operation`."
  [kb handle where]
  (or
   (checks/forcing-retraction-problem kb handle where)
   (special/mint-rule-retraction-problem kb handle where)
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
  runs the dependency-directed sweep; an inert sentex is torn down directly through the
  removal choke point.  Returns `{:removed-sentexes n :removed-justifications n :datum?
  bool :seeds [handle] :rederive [justification] :sentences [s]}`.  `:datum?` says
  whether a settle is owed, `:seeds` what the removal owes a re-chain
  (`special/resubsumption-seeds`), `:rederive` the derivations that descended through a
  departing `genl` edge (`special/edge-descended-justifications`).  An absent key reads
  as empty."
  [kb handle]
  (if (jtms/known-datum? (reasoning/tms kb) handle)
    (do (p/unmark-premise! (:records kb) handle)         ; no longer an asserted premise
        (let [{:keys [removed-sentexes removed-justifications] :as r} (jtms/retract! (reasoning/tms kb) handle)
              ;; Fetch each swept record BEFORE tearing it down: the JTMS returns handles,
              ;; and `sentex-removed!` deletes the record.  Keep the sweep's order: the
              ;; retracted handle torn down after the n nogoods it sits in costs n²
              ;; (perf's filler-beside-clashing-fillers).
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
    ;; The two refusals this branch owes are `teardown-refusal`'s, which `edit!` asks
    ;; *before* it removes anything, since a removal is the one half no rollback can put
    ;; back.  A batch that reaches here has cleared every removal, so the throw below is a
    ;; `retract!`'s.
    (if-let [sx (p/get-sentex (:records kb) handle)]
      (if-let [problem (teardown-refusal kb handle "retract!")]
        (throw (ex-info (:message problem) (dissoc problem :message)))
        (do (integrate/sentex-removed! kb sx)
            {:removed-sentexes 1 :removed-justifications 0 :datum? false :seeds []
             :sentences (into [] (keep :sentence) [sx])}))
      {:removed-sentexes 0 :removed-justifications 0 :datum? false :seeds []})))

(defn- settle-after-teardown!
  "The settle a teardown owes: relabel to revive any default the removed data were
  defeating, re-derive what the removal released, and relabel again (docs/exceptions.md,
  \"Garbage collection, not defeat\").  `released` (rules whose `exceptWhen` the removal
  released, captured before the first settle), `seeds` (`special/resubsumption-seeds`) and
  `rederive` (argument-type entailments and descended equalities, drawn after the first
  settle) name the re-derivations.  The seed re-chain files no `:no-placement`."
  ([kb released seeds] (settle-after-teardown! kb released seeds nil))
  ([kb released seeds rederive]
   ;; The first settle publishes the belief that `rederive` reads: an equality is found by
   ;; matching the facts that fill a functional slot, including a spelling the departed
   ;; merge gave back.
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
  ledger, the calculi's report markers, the program, the refusal record and the mint
  queues — snapshotted before the batch runs, plus `:filed`, the identity set the batch
  binds `viol/*batch-entries*` to."
  [kb]
  {:violations @(reasoning/violations kb)
   :seen       (some-> (reasoning/qcn kb) deref)
   :program    @(reasoning/program kb)
   :refused    @(reasoning/refused kb)
   :queues     (select-keys @(reasoning/mint-queues kb) [:owed :defer-next])
   :filed      (viol/batch-entries)})

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
  [kb {:keys [audit suspended violations seen program refused sink filed mark queues]}]
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
    (observe/restore-seen! (reasoning/qcn kb) seen)
    (reset! (reasoning/program kb) program)
    ;; the refusal record: an entry the batch's content wrote names handles the rollback
    ;; took away (docs/preview.md, "What the rollback restores")
    (reset! (reasoning/refused kb) refused)
    (swap! (reasoning/mint-queues kb) #(merge (dissoc % :owed :defer-next) queues))))

(defn- rollback-batch!
  "Restore the KB to the state the batch found it in, at the handles it wrote (the handle
  counter stays moved, docs/preview.md).

  Takes `batch-baseline`'s snapshot plus `:audit` (`entry/*premise-audit*`), `:suspended`
  (`[[handle strength] …]`), an optional `:mark` (`entry/*write-mark*`) above which every
  record is removed before the settle, and an optional `:sink` (`integrate/removal-sink`)
  scoping the orphan sweep.  Runs with the change feed off and unbounded."
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
  (`chain/call-with-stop`), and return what `f` returns.  A throw runs `rollback-batch!`
  and is rethrown as raised, a failed rollback attached as suppressed (docs/api.md,
  \"Validating without writing\").  A run the caller's bound ends throws `:interrupted`.
  An enclosing audit (`edit!`, `preview`, an outer `assert`) owns the undo.  A change-feed
  listener holds the feed (`feed/with-one-event`), and a rolled-back event is not
  delivered.  A bound `entry/*write-check*` reads what `f`'s firings concluded
  (`write-checked`)."
  [kb opts f]
  (if entry/*premise-audit*
    (binding [rules/*stratification-memo* (or rules/*stratification-memo* (volatile! nil))
              rules/*negated-keys-memo* (or rules/*negated-keys-memo* (volatile! nil))
              exc/*reader-states* (or exc/*reader-states* (volatile! nil))]
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
                                 special/*producer-moves*
                                 (or special/*producer-moves* (special/producer-moves))
                                 rules/*stratification-memo*
                                 (or rules/*stratification-memo* (volatile! nil))
                                 rules/*negated-keys-memo*
                                 (or rules/*negated-keys-memo* (volatile! nil))
                                 exc/*reader-states*
                                 (or exc/*reader-states* (volatile! nil))
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
  form of the rule's polycanonicalization (`rules/expand-rule`), each wrapped in the
  exception.  `exc` and `inner` are `rules/split-exceptWhen`'s two halves.  `assert` and
  `check` hold every form to the whole-rule checks and the exception's closure before
  anything is stored, since each form is a rule of its own."
  [exc inner]
  (mapv #(list sx/except-wrapper exc %) (rules/expand-rule inner)))

(defn- check-reified-inputs!
  "Refuse a fact whose function applications are given inputs their functions' argument
  declarations forbid, asked of the sentence before the reify pass mints its ground
  reifiable applications (`checks/check-application-inputs`).  Routed as
  `assert-entry/assert-one` routes what it stores: an imperative and a rule are passed
  over, an `(ist Ctx S)` is `S` in `Ctx`, a virtual wrapper is peeled, and a
  forced-decontextualized predicate reads from CxUniverse.  Skipped under `*bulk-load?*`
  and in a KB declaring no `reifiable_function`."
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
  "Assert `sentence` in `context` (default 'CxUniverse) as a JTMS premise: enforce naming,
  arg and disjointness constraints, persist, index, mark IN, integrate into the taxonomy
  and rule index, then forward-chain.  A virtual set/forwardRule|backwardRule|inertRule
  wrapper directs the enclosed rule.  `(set/monotonic S)` around the whole sentence is `S`
  asserted `{:strength :monotonic}`; `(set/inert …)` and `(set/monotonic …)` elsewhere than
  the outermost wrapper are refused (`:shape`).

  `opts`: chaining options (`{:max-depth ..}`, `{:chain? false}`), `:strength` (`:default`
  or `:monotonic`), `:creator`, `:provenance` (a map), and the bounds `:max-ms`, `:stop?`
  and `:max-derivations`; a bound the run reaches refuses the call (`:interrupted`).

  Returns the sentex handle, or a vector of handles when a rule concluding a conjunction
  is polycanonicalized into one rule per conjunct.  A rebuttal or definitional clash is
  stored and settled, not thrown.  Refusals: an unread `opts` key or a `:strength` outside
  the two (`:unknown-option`); a vector sentence (`:shape`); an unrecovered KB
  (`:unrecovered-kb`).  A refusal leaves the KB as found, the handle counter aside."
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
     ;; the same reason: a non-s-expression would store in silence, a non-sequential throws
     ;; with no `:type`, and a vector is read as a conjunction by the read entry points.
     (check-shape! (context-shape-problem context))
     (check-assert-opts! opts)
     (check-sentence-shape! sentence)
     (check-shape! (checks/empty-meet-problem kb sentence context))
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
              ;; The answer-set surface forms (`asp/atMost`, `asp/atLeast`, `asp/minimize`,
              ;; a priority-tagged `set/softConstraint`) are rewritten to the constraint
              ;; rules they are before anything reads their shape; the identity on every
              ;; other sentence (docs/solving.md).
              sentence (rules/normalize-solve-surface sentence)
              ;; `(exceptWhen (set/monotonic <query>) <rule>)` states the **exception's**
              ;; own defeat class, which `opts` cannot (docs/exceptions.md).  Peeled before
              ;; the split; `exc-opts` is what the meta-sentex alone is stored under.
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
              ;; An `(exceptWhen <query> <rule>)` is split into the bare rule and the
              ;; exception, a separate belief-following meta-sentex against the rule's
              ;; handle, so asserting or retracting an exception amends the rule in place
              ;; (docs/exceptions.md).
              [exc inner] (rules/split-exceptWhen sentence)
              inner       (if (and exc (entry/ist-parts inner))
                            (entry/resolve-reference kb sentence inner context (volatile! []))
                            inner)]
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
              ;; An inline-rule exceptWhen.  Run the whole-rule checks on every *wrapped*
              ;; form the rule is stored as (`exceptWhen-rule-forms`) before anything is
              ;; stored, so a refused exception leaves no bare rule behind.  Then store the
              ;; rule(s) and attach the exception to **each**, aligned against that
              ;; conjunct's *own* canonicalization: a self-join tie group can be numbered
              ;; differently per conjunct.
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
                          ;; A disjunctive antecedent or a conjunctive consequent is ONE
                          ;; rule stored as several.  Check every one before storing any,
                          ;; so the whole rule is asserted or none of it.
                          (do (run! #(entry/check-rule-sentence kb % context) forms)
                              (mapv #(entry/assert-one kb % context opts {:assert-fn assert :bulk? *bulk-load?*}) forms))
                          (entry/assert-one kb (first forms) context opts
                                            {:assert-fn assert :bulk? *bulk-load?* :written written}))]
              (after-the-write
               h
               (fn []
                 (record-provenance! kb h opts)
                 (rehome-forced-extent! kb sentence)
                 ;; Collision merge, correspondence, structural genlCx edges and their
                 ;; merges, sequenced below core behind one presence check that a KB
                 ;; reifying nothing never passes (docs/nat.md, docs/context-nat.md).
                 (nat-maint/reconcile-assert kb sentence context opts)))
              h))))))))

(defn- refuse-unsatisfiable-write!
  "Throw `:definitional-clash` with `:violation :unsatisfiable-network` when a registered
  calculus blames a sentex the write premised newly (`entry/*premise-audit*`) or a
  conclusion its firings placed (`fired`) for an unsatisfiable component of its network
  (`qkb/unsatisfiable-write`).  `:clashes-with` names the other blamed sentexes, and
  `:detail` the calculus, the context, the component's nodes and its pairs unsatisfiable
  as written.  `try-assert`'s `entry/*write-check*`, so the throw takes the write back."
  [kb sentence fired]
  (let [new (into (set fired)
                  (keep (fn [[h m]] (when (false? (:premise? m)) h)))
                  (some-> entry/*premise-audit* deref))]
    (when-let [{:keys [calculus context nodes pairs culprits]} (qkb/unsatisfiable-write kb new)]
      (throw (ex-info (str "the " (name calculus) " network visible from " context
                           " would be unsatisfiable over " (nm/print-key (nm/by-print-key nodes)))
                      {:type          :definitional-clash
                       :violation     :unsatisfiable-network
                       :sentence      sentence
                       :entailed-from nil
                       :clashes-with  (nm/sort-by-content-key
                                       #(nm/print-key [(:sentence %) (:context %)]) compare
                                       (keep (fn [h]
                                               (when-let [sx (p/get-sentex (:records kb) h)]
                                                 {:handle h :sentence (sx/sentence-of sx)
                                                  :context (:context sx)}))
                                             (remove new culprits)))
                       :detail        {:calculus calculus :context context
                                       :nodes (nm/by-print-key nodes)
                                       :pairs (nm/by-print-key pairs)}})))))

(defn try-assert
  "`assert`, refusing a sentence that would open a definitional clash with believed
  content visible from `context`.  The refusal is `:definitional-clash`, carrying the kind
  in `:violation` (the fourteen kinds: docs/api.md, \"Refusing a clash\"), the members it
  clashes with in `:clashes-with`, and `:entailed-from` when a mint clashes; the call
  stores nothing.  An `:unsatisfiable-network` is refused after the settle unless `opts`
  carries `:refuse-unsatisfiable? false`.  Every other refusal, argument and return value
  is `assert`'s.  The result depends on what is already stored, and so on arrival
  order."
  ([kb sentence] (try-assert kb sentence 'CxUniverse nil))
  ([kb sentence context] (try-assert kb sentence context nil))
  ([kb sentence context opts]
   ;; a non-map `opts` reaches `assert`, which refuses it
   (when (map? opts) (opts/check-values! (select-keys opts [:refuse-unsatisfiable?]) "try-assert"))
   (let [outer entry/*write-check*]
     (binding [checks/*refuse-clashes?* true
               entry/*write-check*      (if (false? (:refuse-unsatisfiable? opts))
                                          outer
                                          (fn [kb fired]
                                            (when outer (outer kb fired))
                                            (refuse-unsatisfiable-write! kb sentence fired)))]
       (assert kb sentence context
               (if (map? opts) (not-empty (dissoc opts :refuse-unsatisfiable?)) opts))))))

(defn assert-rule
  "Assert a rule (a sentex whose sentence is an implication) in `context`.
  `opts` may carry `:direction` (:forward | :backward | :inert | :both, default
  :backward) — or use a set/*Rule virtual predicate with `assert`.  A generator (a rule
  concluding a rule) defaults to :forward instead — no backward goal asks for a rule."
  ([kb antecedents consequent] (assert-rule kb antecedents consequent 'CxUniverse nil))
  ([kb antecedents consequent context] (assert-rule kb antecedents consequent context nil))
  ([kb antecedents consequent context opts]
   ;; The unrecovered-KB check comes before the range check, so this refuses like every
   ;; other write entry point (`:unrecovered-kb`, not `:not-range-restricted`).
   (check-writable! kb "assert-rule")
   (rules/check-range-restricted antecedents consequent)
   ;; `:direction` is the programmatic spelling of a set/*Rule wrapper: wrap it and hand it
   ;; to the one rule path.  The wrapper then carries the direction, so `:direction` leaves
   ;; the opts: `assert` reads a second statement as a conflict when the two differ.
   (let [sentence (rules/wrap-direction (rules/rule-sentence antecedents consequent)
                                        (:direction opts :backward))]
     (assert kb sentence context (dissoc opts :direction)))))

;; ---- check: would this assert succeed, and why not? ----------------------
;; `check` runs `assert`'s own checks and reports each failure under the `:type` `assert`
;; would have thrown, writing nothing.  Checks that are already values (`nm/problems`,
;; `special/wff-problems`) are read directly; the rest throw and are read back through
;; `problem`.

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
  "What stops a would-be assertion from even being a sentence in a context.  In `assert`'s
  precedence: the context, then the whole opts read (`check-assert-opts!`), then the
  sentence, through `assert`'s own check fns, so both entry points refuse the same input
  with the same `:type`.  Nil when all three hold.  `check` reports a misspelt `:strength`
  here, since the entry is otherwise admissible knowledge asserted at the wrong class."
  [sentence context opts]
  (or (some-> (context-shape-problem context) vector)
      (some-> (problem (fn [] (check-assert-opts! opts))) vector)
      (some-> (sentence-shape-problem sentence) vector)
      ;; A malformed answer-set surface (`asp/atMost` / `asp/atLeast` / `asp/minimize`, or a
      ;; priority-tagged `set/softConstraint`) is reported as a returned problem, so `check`
      ;; predicts the `:not-well-formed` refusal.  `normalize-solve-surface` throws on a bad
      ;; bound, priority or weight, so `problem` catches it.
      (some-> (problem (fn [] (rules/normalize-solve-surface sentence))) vector)
      (some-> (sx/connective-problem sentence) vector)
      (some-> (disjunction-shape-problem sentence) vector)
      (some-> (checks/term-shape-problem sentence) vector)
      (some-> (problem (fn [] (checks/check-encodable sentence))) vector)))

(defn- fact-problems
  "The checks `assert-one` runs over a non-rule sentence, as values.  The virtual
  wrapper is peeled, the references resolved (`assert-entry/resolve-references`) and the
  context is `assert-entry/storage-context`'s, so what is checked is the sentence that
  would be stored."
  [kb sentence context]
  (let [written  (rules/inner-rule sentence)
        sentence (try (entry/resolve-references kb written context)
                      (catch clojure.lang.ExceptionInfo _ written))
        context  (entry/storage-context kb (nm/functor sentence) context)]
    (first-problems
     (cond->>
      [#(some-> (problem (fn [] (entry/resolve-references kb written context))) vector)
       #(for [p (nm/blocking-problems (:naming kb) sentence context)]
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
       #(some-> (problem (fn [] (checks/check-exact-present kb sentence context))) vector)
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
  (vec (for [lit (nat/heads-for-check kb exc context)
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
  "Would `(assert kb sentence context opts)` succeed, and if not, why?  Returns a vector
  of problems, empty when the sentence is admissible, and stores nothing.  Each problem is
  a map with the `:type` `assert` would have thrown, a `:message`, and whatever else that
  check knows.  The stages run in `assert`'s order and stop at the first that finds
  anything; `:unrecovered-kb` is reported alone and first.  `check` mints no NAT, evaluates
  no imperative and does not chain, so a refusal raised while rules fire is `assert`'s
  alone.  Stages and differences from `assert`: docs/api.md, \"Validating without writing\"."
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
         (some-> (checks/empty-meet-problem kb sentence context) vector)
         (some-> (direction-opt-problem sentence opts) vector)
         ;; ...and the other wrapper `assert` peels before it splits: a strength stated on
         ;; an `exceptWhen` query, for the exception's own defeat class.  The same walk
         ;; refuses it and `(set/inert …)` anywhere else on the wrapper chain.
         (some-> (sx/exception-strength-problem sentence) vector)
         ;; From here on, the sentence `assert` would act on: the `:direction` opt as its
         ;; wrapper, the cardinality surface normalized to its constraint rule, and the
         ;; exception's strength peeled off.  None can throw: `shape-problems`,
         ;; `direction-opt-problem` and `exception-strength-problem` answered above.
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
                 (and exc (entry/ist-parts inner))
                 (or (some-> (problem #(entry/resolve-reference kb sentence inner context (volatile! [])))
                             vector)
                     (check kb (list sx/except-wrapper exc
                                     (entry/resolve-reference kb sentence inner context (volatile! [])))
                            context opts))

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
                     (for [form (exceptWhen-rule-forms exc (nat/heads-for-check kb inner context))]
                       (fn []
                         (some-> (problem (fn []
                                            (entry/check-rule-sentence kb form context)
                                            (sx/check-exception-closed
                                             (rules/antecedents (rules/inner-rule form)) exc)))
                                 vector))))
                   #(exceptWhen-naming-problems kb exc context)
                   #(check kb inner context opts)])

                 (rules/rule-sentence? (rules/inner-rule sentence))
                 (rule-problems kb (nat/heads-for-check kb sentence context) context)

                 ;; the application-input check first and over the sentence as written,
                 ;; where `assert` asks it, before the reify pass; then the fact as `assert`
                 ;; would store it, an application with a term read as that term and one
                 ;; without read as the constant `assert` would mint
                 :else
                 (or (some-> (problem (fn [] (check-reified-inputs! kb sentence context))) vector)
                     (binding [checks/*entry-mints?* true]
                       (fact-problems kb (nat-read/reify-existing kb (nat/heads-for-check kb sentence context) context true)
                                      context)))))))))))

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
  "`handle` as a handle, `nil` as itself, or a refusal saying what it got instead.  A
  vector is refused, since `assert` returns a vector for a rule with a conjunctive
  consequent and the record lookup would otherwise miss silently.  `nil` passes through,
  since `handle-of` answers nil for a sentence the KB does not hold."
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
  "Refuse a batch that is not a map, and a batch key nothing reads (`:unknown-option`).
  `{:adds [...]}` would otherwise destructure to nil, write nothing and report success,
  and `check-edit` would report no problems."
  [batch]
  (when-let [p (edit-batch-problem batch)]
    (throw (ex-info (:message p) (dissoc p :message)))))

(defn check-edit
  "`check` over a whole `edit` batch, `{:add [[sentence context opts?] …] :remove
  [handle …]}`, storing nothing.  Returns a vector of problems, empty when the batch is
  admissible.  Each is what `check` returns plus `:in` (`:add` / `:remove`), `:index` and
  `:entry`.  An `:add` is checked against the KB as it stands.  A `:remove` is checked
  for being a handle (`:bad-handle`), naming a stored one (`:unknown-handle`) and the
  `teardown-refusal` of a handle with no TMS node.  `:unknown-option` and
  `:unrecovered-kb` are about the batch and are reported alone."
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
;; Settle recomputes from current state, so a bulk load deferring it is safe: chaining
;; still runs per assert, and the one closing settle sees the same stored state a
;; per-assert settle would.

(def ^:private ^:dynamic *batch-id*
  "A random UUID naming the outermost `with-deferred-settle` batch in force, which each of
  its frames records (`op-inputs`); nil outside a batch."
  nil)

(defn- batch-settle-inputs
  "What a `with-deferred-settle` batch's `:settle` frame records: the batch's id, whether
  the batch was written under `*bulk-load?*`, and whether a write in it would have seeded
  chaining from the `genlCx` moves its own settle drained (`settle/*batch-seeds-moves*`)."
  []
  {:batch       *batch-id*
   :bulk-load?  *bulk-load?*
   :seed-moves? (if-let [v settle/*batch-seeds-moves*] @v special/*seed-moves?*)})

(defn- with-support-observer
  "Run a write with a network-owned, queue-only named-demand listener. Dependency
  traversal waits for the normal value-maintenance drain; departing rows are saved
  before physical deletion. Same-network nesting reuses the listener."
  [kb thunk]
  (let [tms (reasoning/tms kb)
        previous jtms/*support-observer*]
    (if (identical? tms (:tms previous))
      (thunk)
      (binding [jtms/*support-observer*
                {:tms tms :previous previous
                 :active? #(or (nat-read/named-values-reachable? kb)
                               (rewrite-query/possible-consumers? kb))
                 :note (fn [hs departing?]
                         (swap! (reasoning/respell kb) into
                                (map (fn [h]
                                       [:named-proof h
                                        (when departing? (:sentence (p/get-sentex (:records kb) h)))])
                                     hs)))}]
        (thunk)))))

(defn- closing-settle
  "The settle that closes a `with-deferred-settle` batch, under the inputs its `:settle`
  frame records (`in`, `batch-settle-inputs`), or under the batch in force when `in` is
  nil.  A batch written under `*bulk-load?*` draws no argument types over the `genlCx`
  moves it settles (`special/*entail-moves?*`), and a batch none of whose writes chained
  seeds no chaining from them (`special/*seed-moves?*`), as a settle per write would not.
  The re-joins the batch owed run first (`chain/run-batch-rejoins`), and the
  structural genlCx edges the settle's belief moves call for are built last
  (`nat-maint/reconcile-moves!`)."
  [kb in]
  (let [{:keys [bulk-load? seed-moves?]} (or in (batch-settle-inputs))
        owed chain/*batch-rejoins*]
    (with-support-observer
      kb
      #(binding [special/*entail-moves?*      (not bulk-load?)
                 special/*release-withheld?* (and special/*release-withheld?* (not bulk-load?))
                 special/*seed-moves?*        seed-moves?
                 chain/*batch-rejoins*        nil
                 special/*producer-moves*     (special/producer-moves)]
         (chain/run-batch-rejoins kb owed)
         (let [settled (settle/settle kb)]
           (nat-maint/reconcile-moves! kb)
           settled)))))

(defmacro with-deferred-settle
  "Run `body`, a batch of `assert` / `assert-rule` / `ist` calls on `kb`, with belief
  settled **once** at the end instead of after every assertion.  The belief is the same as
  a settle per assertion.  Returns `body`'s value.

    (v/with-deferred-settle kb
      (doseq [f facts] (v/assert kb f 'CxSome))
      (v/assert-rule kb ante conseq 'CxSome))

  A read inside `body` sees the batch unsettled, and a `retract!` inside settles eagerly.
  Nesting composes, and the outermost settles.  Not a transaction: a throw mid-batch
  leaves what was stored in place (docs/api.md, \"Batched assertion\")."
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
                                            settle/*batch-seeds-moves*)
               chain/*batch-rejoins*      (if outermost# (java.util.HashMap.) chain/*batch-rejoins*)
               *batch-id*                 (if outermost# (java.util.UUID/randomUUID) @#'*batch-id*)]
       (let [res# (try
                    (binding [*defer-settle?* true
                              tax/*defer-depths?* true]
                      ~@body)
                    (catch Throwable t#
                      ;; The settle below will not run, so this repairs a potential the
                      ;; batch left loose, which would leave every later `genl?` / `sees?`
                      ;; walk unpruned.  A cancelled load (the catalog aborts one by throwing
                      ;; from its progress callback) reaches this.  Repairing cannot throw;
                      ;; belief is left unsettled.
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
  "Assert every sentence in `sentences` (into one shared `context`, optional shared `opts`)
  with belief settled **once** at the end: the collection form of `with-deferred-settle`.
  Returns the vector of handles in input order (a conjunctive-consequent rule contributes
  its vector).

  `:max-ms` and `:stop?` bound the whole call.  The sentence a bound interrupts is rolled
  back, the sentences before it stay settled, and the call throws `:interrupted` with
  `:stored`, their handles (docs/inference.md, *Stopping a run*)."
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
  `context` on the fast path: `assert` under `*bulk-load?*` inside one
  `with-deferred-settle`, with `{:chain? false}`.  The caller owns both preconditions; use
  `assert-many` when either is in doubt.  A symmetric functor keeps the dedup probe.

  Returns the vector of sentex handles in input order.  No argument-type entailment is
  drawn: run `record-arg-types` after the load, and `forward-chain` for the rules.  `opts`
  flows to each `assert`; `:max-ms` and `:stop?` bound the call as at `assert-many`.
  `:on-progress` is handed `{:phase :loading :done n :elapsed-ms ms :facts-per-sec r}`
  every 100,000 facts and `{:phase :done :total n …}` after the closing settle.  Cost and
  the changing-snapshot load: docs/storage.md, \"What a bulk load costs\"."
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
  store loaded without them (a dump import, a `*bulk-load?*` load or `bulk-assert-facts!`),
  and settle.  Returns `{:facts n :recorded n :violations n}`: the facts read, the records
  created, and the derivations the ledger reports.  Idempotent; nothing is recorded under
  `VAELII_ASSERTIVE_ARG_TYPES=0`.  It runs no forward chaining.  `record-arg-types!` draws
  the same facts and can stop, resume and set a fact aside (docs/argtypes.md)."
  [kb]
  (let [res (argpass/run-all kb)]
    (viol/report kb (:violations res))
    (settle/settle kb)
    (argpass/clear-owed! kb)
    {:facts (:facts res) :recorded (:recorded res) :violations (count (:violations res))}))

(defn record-arg-types!
  "`record-arg-types` as a run that can stop and resume, for a store where the pass takes
  hours.  What the pass owes is kept in the store (`arg-types-owed`), so the next call
  resumes it (docs/argtypes.md, \"The pass over a stored KB\").

  `opts`:

    `:resume?`           default true: carry on from what the store says is owed.
    `:budget-ms`         default 2000: how long one fact's checks may run; a fact past it
                         is set aside (owed, with the `:phase` that ran out).  nil: none.
    `:retry-deferred?`   default false: after the sweep, draw each set-aside fact again.
    `:stop?`             a no-argument function; truthy stops at the next fact.
    `:on-progress`       called at most every `:progress-every-ms` (default 1000) with
                         `{:phase :done :total :recorded :deferred}`; `:phase` is
                         `:arg-types`, `:releases`, `:deferred`, `:settle` or `:done`.  A
                         throw stops the pass and is rethrown once it has committed.
    `:commit-every-ms`   default 30000: how long the pass draws between two commits.

  Returns `{:drawn :done :total :recorded :violations :deferred :stopped :complete?}`;
  `:stopped` is nil or `:requested` / `:shutdown` / `:cancelled`.  Refuses a KB without
  belief (`:unrecovered-kb`) and an owed record written after the records the store holds
  (`:owed-record-ahead`)."
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
  destructure) — the key set `forward-chain` holds an opts map to."
  #{:max-depth :max-term-depth :max-derivations :max-ms :on-progress :progress-every-ms
    :stop? :on-stop})

(defn- progress-interrupts
  "`on-progress` as `forward-chain` hands it to the run under `:on-stop :rollback`: a throw
  out of it becomes `:interrupted` with `:bound :on-progress`, carrying the throw as its
  cause, so the caller's cancel takes the rollback every other bound takes."
  [on-progress]
  (fn [m]
    (try (on-progress m)
         (catch Throwable t (chain/interrupted! :on-progress t)))))

(defn forward-chain
  "Run forward chaining to a fixpoint over every believed sentex, then settle belief.
  Returns `{:derived n :truncated? bool}`, with `:bound` (`:max-derivations`, `:max-ms` or
  `:stop?`) naming what ended a run kept under `:on-stop :keep`.

  `opts`: `:max-depth`, `:max-term-depth` and `:max-derivations` bound the run
  (`default-chain-opts`); `:max-term-depth` refusals return `:term-cut`, their count, and
  a `:max-depth` cut returns `:truncated? true`.  `:on-progress` is called with
  `{:derived n :pending n}` every `:progress-every-ms` and may throw to stop.  `:max-ms`
  bounds the call and `:stop?` is a no-argument function whose truthy answer ends it.
  `:on-stop` (docs/inference.md, *Stopping a run*) is `:rollback` (default: a stopped run
  throws `:interrupted` with `:bound` and leaves the KB as found, the handle counter
  aside) or `:keep` (the run keeps what it placed, is settled, and returns
  `:truncated? true`).  A nearly full heap ends the run with `:interrupted :bound :heap`
  under either, except during an oplog replay.  An unread `opts` key is refused
  (`:unknown-option`)."
  ([kb] (forward-chain kb nil))
  ([kb opts]
   (check-opts! :chain opts forward-chain-opt-keys "forward-chain")
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
;; Five entry points answer a goal; they differ in **how much rule expansion each does**:
;;
;;   query / query?     THE DEFAULT.  No `:max-depth` is `ask`; a `:max-depth` is the node
;;                      engine, bounded at that many rewrites.  Sentence or vector goal.
;;                      → binding maps
;;   ask / ask?         The prover registry alone: facts, taxonomy closures, transitivity,
;;                      disjointness, metadata, evaluables, NAF, arg type inference.
;;                      Expands **no rule**.  → binding maps
;;   prove / provable?  The *unbounded* backward chainer: rule expansion over the registry,
;;                      terminating on the data.  A VECTOR goal is a conjunctive query.
;;                      → a vector of binding maps
;;   sentexes-matching  *Stored, believed* literals matching a pattern: a belief-filtered
;;                      index read, no inference.  → sentex maps
;;   lookup / escalate  Diagnostics: answer at one level of the 8-level stack, find the
;;   / explain-levels   cheapest level that answers, or show every level.  → level maps
;;
;; **Only two things backchain**: `prove` and level 7 stop when the data runs out, the node
;; engine (`query` with a depth) at the depth.  Nothing else expands a rule.
;; Result shapes: **sentex maps** (`{:id :sentence :context ...}`), **binding maps**
;; (`{?x val ...}`) and **level-result maps** (`{:level :handle :sentence :context
;; :bindings}`).

;; ---- one spelling, one meaning, at every read entry point -----------------------
;; A **top-level vector is a conjunction** (`quasiquote/prepare-conjunction-for-read`,
;; `plan/explain`, the `::goal` spec), and the write entry point refuses `[likes Tom Ann]`
;; as a sentence.  `ask` / `ask?` / `sentexes-matching` / `handle-of` read **one sentence**
;; and refuse a vector (`:shape`).  `lookup` is not guarded: at level 0 a vector is an
;; index path.

(defn- sentence-spelled-as-a-vector
  "The list a vector goal was meant to be, when that is what it plainly is — every
  member a term rather than a sentence, which is `[likes Tom Ann]`.  Nil for a vector
  that holds sentences, since `((p ?x) (q ?x))` is not what its author meant by
  `[(p ?x) (q ?x)]` and a refusal that says otherwise sends them backwards."
  [goal]
  (when (and (seq goal) (not-any? seq? goal))
    (apply list goal)))

(defn- disjunctive-goal-problem
  "The `:shape` problem a goal carrying an `or` is refused with, or nil.  A query is not
  expanded and a rule is: the write entry point expands a disjunctive antecedent into one
  rule per alternative (`rules/expand-rule`), but `quasiquote/prepare-conjunction-for-read`
  normalizes a goal to one conjunction that the planner, the node engine, `abduce` and
  `read-in-context` each take as one.  Take the union by running the query once per
  alternative, or assert `(implies (or A B) C)` and ask for `C`.  The conjunctions a
  function's correspondences give (`quasiquote/goal-alternatives`) are not a written `or`
  (docs/nat.md)."
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
  vector, or a goal carrying an `or` or a misplaced `.`, with, or nil.  `ask`, `ask?`,
  `ask-within`, `sentexes-matching` and `handle-of` read one.  The message names which
  spelling arrived.  `disjunctive-goal-problem` says why an `or` is refused."
  [goal]
  (or
   (disjunctive-goal-problem goal)
   (sx/dot-problem :goal goal)
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
  `prove-within` and `abduce` join a vector's members as separate goals, so `[likes Tom
  Ann]` would be three goals.  An empty vector is the empty conjunction and stays legal.  A
  `nil` conjunct is refused like any other non-sentence.  A conjunct carrying an `or` or a
  misplaced `.` is refused as at `sentence-goal-problem`."
  [goal]
  (or
   (disjunctive-goal-problem goal)
   (sx/dot-problem :goal goal)
   ;; `some`, not `when-some` over the first offender: a nil conjunct is a value that
   ;; `when-some` reads as absent, and `[(dog ?x) nil]` would pass and answer nothing.
   (when (and (vector? goal) (some #(not (seq? %)) goal))
     (let [bad (first (remove seq? goal))]
       {:type :shape :goal goal :conjunct bad
        :message (str "a vector goal is a conjunction, so every conjunct must be a"
                      " sentence: " (pr-str bad) " is not, in " (pr-str goal) "."
                      (if-let [as-list (sentence-spelled-as-a-vector goal)]
                        (str "  Write one sentence as a list: " (pr-str as-list))
                        "  Write each conjunct as a list."))}))))

(defn- read-context
  "`[context kb]` a read names `ctx` by: the context reified in read mode (dedup, never
  mint), and `kb`.  A context application nobody has written into reifies to `no-match`,
  which answers empty, unless the producer would order it below a minted context: then
  it is the `cx/` constant its content names, read in a KB holding those edges
  (`context-nat/unwritten-read`).  See docs/context-nat.md."
  [kb ctx]
  (let [k (nat/maybe-reify-context kb ctx false)]
    (or (when (and (= nat-read/no-match k)
                   (not-any? #(nat-read/reifiable-ground-nat? kb %) (rest ctx)))
          (context-nat/unwritten-read kb (apply list ctx)))
        [k kb])))

(defn- ist-goal
  "`[goal context kb]` for a read whose goal may be an `(ist Ctx S)`: the sentence to ask,
  the context to ask it in, and the KB to read it in (`read-context`).  The named context
  wins over `context`, as at `assert` (docs/contexts.md#ist-find-or-create-in-a-context).
  Refuses a wrong-arity `ist` with `ist-shape-problem`'s `:shape`, and an `(ist …)`
  conjunct of a vector goal with `:not-well-formed`."
  [kb goal context]
  (letfn [(reic [ctx] (read-context kb ctx))]
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
          (into [goal] (reic context)))

      (and (sequential? goal) (seq goal) (= sx/ist-functor (first goal)))
      (if-let [[ctx s] (entry/ist-parts goal)]
        (into [s] (reic ctx))
        (check-shape! (entry/ist-shape-problem goal)))

      :else (into [goal] (reic context)))))

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
  "The `:shape` problem a read is refused with when its context is not one, or nil.  The
  read side takes a symbol (a context name, a variable, or a query context) or a ground
  application whose head CxUniverse believes a `(result F context)` of
  (`nat/readable-context-application?`).  A read at a non-context would otherwise answer
  empty, as a true negative does."
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
  `CxEverything` reads at the wildcard under `res/*belief-blind*`, `CxNothing` passes
  through, and `CxInference` and a variable context take the joint reading.  `goals-of` is
  the conjunction as prepared at a given context; only a joint read or the wildcard calls
  it.  `:expands-rules?` says the read may expand a rule."
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
  "*Believed* sentexes matching `sentence` in `context` (default ?ctx).  Literal (no
  subtype expansion); use `ask` for full inference.  `find-sentexes` is the raw read.

  Returns a lazy seq of **sentex maps** over live state (`vec` it for a snapshot) with
  keys `:id` (the handle), `:context`, a literal's `:sentence` (`(not S)` for a negative
  one), and a rule's `:antecedent` / `:consequent` / `:engines` / `:effect` (no `:sentence`).
  Beside a writer thread the answer is not one state's (docs/storage.md, \"The
  single-writer contract\").  A ground reifiable NAT reifies to its existing constant (never
  mints); an `(ist Ctx S)` sentence asks S in Ctx.  A vector pattern is refused (`:shape`)."
  ([kb sentence] (sentexes-matching kb sentence '?ctx))
  ([kb sentence context]
   (check-shape! (sentence-goal-problem sentence))
   (let [[sentence context kb] (ist-goal kb sentence context)
         sentence              (nat-read/maybe-reify-for-read kb sentence context)
         context               (stored-context kb sentence context)]
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

(defn handle-of
  "The handle of the sentex already storing `sentence` in `context`, or **nil**.  The
  non-creating counterpart to `ist`: it turns a sentence into a handle for `retract!`,
  `in?`, `why` or `supporting-justifications`.  Storage, not belief: a stored-but-defeated
  sentex has a handle.

  Either spelling of a ground symmetric literal finds the one stored sentex.  An
  `(exceptWhen <query> <rule>)` answers the exception's meta-sentex handle
  (docs/exceptions.md); a whole-form `(set/monotonic S)` answers `S`'s; an `(ist Ctx S)`
  is read as `ist` writes it; a ground reifiable NAT resolves to its stored constant and a
  reference to its target's handle.  A vector, a non-sentence, and a nil, numeric or
  variable context are refused (`:shape`), since nil means \"not stored\"."
  [kb sentence context]
  (check-shape! (sentence-goal-problem sentence))
  (let [[sentence context] (checked-ist-goal kb (first (sx/peel-strength sentence nil)) context)
        sentence           (first (sx/peel-strength sentence nil))]
    (check-shape! (sentence-shape-problem sentence))
    (check-shape! (lookup-context-shape-problem context))
    (let [s (nat-read/maybe-reify-for-read kb sentence context true)]
      ;; spelled as `context` reads it: a permuting mark it does not believe sorts nothing
      (binding [res/*spelled-by* (res/reader-spelled-by kb s (stored-context kb s context))]
        (when-let [s (try (entry/resolve-references kb s context)
                          (catch clojure.lang.ExceptionInfo e
                            (when-not (= :unresolved-reference (:type (ex-data e))) (throw e))))]
          (entry/stored-handle kb s context))))))

(defn handles
  "Every live sentex handle in the KB, premises and forward-derived alike, read off the
  record store.  The whole-KB counterpart to `sentexes-in-context` and
  `sentexes-matching`.  Storage, not belief: filter with `in?` for belief.

  **A set to read, not one to build on**: `contains?`, `count`, `seq` and `sort` answer
  it; convert with `(set …)` before `conj` / `disj` / `clojure.set`, since a large store
  answers a compressed handle set (`vaelii.impl.handle-set`)."
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
  "Store `sentence` in `context` as an **inert** sentex: indexed and persisted (so
  `sentexes-in-context` shows it and `recover` keeps it) but **not a JTMS premise**: never
  believed, chained or scanned for contradictions.  Returns the handle; `retract!` drops
  it.  A solve's materialized labeling uses it (docs/solving.md).
  `assert`'s reference resolution and its checks on the sentence alone apply.  Refusals:
  an open sentence (`:not-ground`); a reifiable NAT with no stored constant
  (`:unminted-nat`); a rule (`:not-indexable`); a `defeat` (`:derived-only`); a wff
  problem such as `(genl t t)` (`:not-well-formed`); an except naming no sentex
  (`:unknown-handle`); a `do/` form (`:not-assertible`); a reference nothing stores
  (`:unresolved-reference`); an unrecovered KB (`:unrecovered-kb`).  `(ist Ctx S)` stores
  S in Ctx; a new record carries `:inert true` in its provenance."
  [kb sentence context]
  (check-writable! kb "assert-inert")
  ;; `assert`'s own shape guards, in its precedence: context, then sentence.  Without them
  ;; a string or nil sentence is stored as an object no query matches (`nm/literals` finds
  ;; nothing to check), and a non-symbol context throws `:naming` where `assert` and
  ;; `check` say `:shape`.  This entry point persists too, so it owes the durable-log
  ;; constraint `check-sentence-shape!` closes with.
  (check-shape! (context-shape-problem context))
  (check-sentence-shape! sentence)
  (check-shape! (checks/empty-meet-problem kb sentence context))
  ;; a `(set/monotonic …)` or `(set/inert …)` on the wrapper chain, refused as at `assert`
  (check-shape! (sx/exception-strength-problem sentence))
  (when (sx/do-form? sentence)
    (throw (ex-info (str "a do/ imperative is an instruction, not a fact, so nothing stores it"
                         " inert: " (pr-str sentence) " — assert runs it")
                    {:type :not-assertible :sentence sentence :context context})))
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
                    context)
          sentence (entry/resolve-references kb sentence context)]
      (nm/check! (:naming kb) (nat/heads-for-check kb sentence context) context)
      ;; `assert`'s refusals that read the sentence alone: an open sentence, a `defeat`,
      ;; the structural wff arms (a nil taxonomy skips those reading stored edges), and an
      ;; except's target, read from the store as `assert` reads it
      (checks/check-ground kb sentence context)
      (checks/check-no-defeat sentence)
      (special/check-wff nil sentence context)
      (checks/check-except-target kb sentence)
      ;; A rule is indexed where a rule sentex is *created* (`index-rule-sentex`), so a rule
      ;; stored here could never fire, and asserting it afterwards resolves to this handle
      ;; without indexing it (`check-generator`).  The message names `set/inertRule`, the
      ;; spelling for a rule that is believed and browsable but never fires
      ;; (docs/taxonomy.md).
      (when (rules/rule-sentence? (rules/inner-rule sentence))
        (throw (ex-info (str "a rule cannot be stored inert: nothing indexes it, so no"
                             " chainer can reach it, and a later assert of the same rule"
                             " resolves to the stored sentex and does not index it either."
                             "  For a rule kept as documentation — stored, indexed and"
                             " browsable, firing neither forwards nor backwards — assert"
                             " set/inertRule (or {:direction :inert}), which is the other"
                             " inertness: the rule is believed and never fires")
                        {:type :not-indexable :sentence sentence :context context})))
      ;; Store the read-mode reify (dedup, never mint), so an inert record of a NAT-bearing
      ;; sentence keys on the constant `assert`, `handle-of` and `sentexes-matching` resolve
      ;; to.  A NAT with no stored constant is refused (`:unminted-nat`): minting asserts a
      ;; `natFormula` premise, a belief-carrying side effect this entry point never has
      ;; (`nat-read/resolve-for-read`).
      (if-let [reified (nat-read/resolve-for-read kb sentence context true)]
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
  "Merge `m` into `handle`'s provenance map (creating it if absent), returning the merged
  map.  For application bookkeeping (source, confidence, review state) beside the creation
  record; `:creator` / `:created` change only when `m` names them.  A nil `handle` records
  nothing and returns nil.  A non-handle, a vector of handles included, is refused
  (`:bad-handle`).  An unrecovered KB accepts it."
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
   (check-opts! :extent opts extent-opt-keys "sentexes-naming")
   (if-some [h (the-handle handle "sentexes-naming")]
     (believed-filter kb opts (records-of kb (reads/as-stored-naming-handle (:index kb) h)))
     ())))

(def ^:dynamic *query-engine*
  "Which backward executor `prove` and `prove-within` run:

    :dfs        the goal-stack DFS (`res/prove-from`), the default
    :inference  the node engine (`vaelii.impl.inference`)
    :hybrid     the node engine, except at `:max-depth` 0, where no node is expanded past
                the root and the session would be overhead

  `:inference` needs a caller-chosen depth (`*query-options*` `:max-depth`, or
  `inference/*max-depth*`).  Bind it around the *consumption*: a `binding` frame popped
  before the lazy seq is realized leaves `:dfs` deciding."
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
  "How the node engine searches, when `*query-engine*` routes a query to it; the DFS
  ignores it.

    {:strategy :depth-first}   a tactician, or a strategy map (`vaelii.impl.tactics`)
    {:portfolio? true}         race several orderings and union their answers
    {:auto? true}              pick one from the structure of the query

  nil, the default, is the shipped ordering.  `:portfolio?` and `:auto?` reach only
  `prove`.  Bind it around the *consumption* (docs/inference.md)."
  nil)

(def query-opt-keys
  "Every key `query` / `query?` read: `:max-depth`, `:max-ms`, `:proof?`, `:strategy`,
  `:portfolio?`, `:auto?` and `:racers` (the node engine's keys go to `inference/solutions`).  A key off
  this set is refused (`:unknown-option`).  `:first-result?` is a strategy key
  (`{:strategy {:first-result? true}}`), as are the signs and weights in
  `vaelii.impl.tactics/defaults`."
  #{:max-depth :max-ms :proof? :strategy :portfolio? :auto? :racers})

(def search-tree-opt-keys
  "Every key `search-tree` reads: the depth, the search ordering, the node-expansion budget
  and the wall clock.  Not `query`'s key set plus two: `search-tree` runs under `:proof?
  true` and reaches the node engine's session directly, so `:proof?`, `:portfolio?`,
  `:auto?` and `:racers` are keys it overwrites or never reads (docs/api.md, \"Argument-shape
  contracts\")."
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

(def lookup-opt-keys
  "Every key `lookup` reads — the wall clock, and nothing else.  Public for
  `query-opt-keys`' reason."
  #{:max-ms})

(def prove-opt-keys
  "Every key `prove` / `provable?` reads: the wall clock, the rule-expansion depth, and
  whether a depth cut refuses.  `:max-ms` is a **deadline**: a stop is a refusal rather
  than a short answer.  `:max-depth` **prunes**: the answer is complete for that depth.
  `:refuse-depth-cut? true` is for a depth the caller did not choose (the daemon's
  ceiling): a run the depth cut short refuses `:budget-exhausted` with `:status
  :depth-cut`, and it runs the DFS, whose loop check stops a cyclic rule set before the
  depth does (docs/anytime.md).  Public for `query-opt-keys`' reason."
  #{:max-ms :max-depth :refuse-depth-cut?})

(defn- bound-exhausted!
  "The refusal a bounded read owes when its budget ran out before the search did.  A
  `:timeout` answer is a prefix of the answer set, and `prove` / `ask` return the answer
  set, so the bound reports (`:budget-exhausted`) instead of returning the prefix; so does
  a `:depth-cut` under `:refuse-depth-cut?`.  A caller that wants the partial uses
  `ask-within` / `prove-within`, which return it with a `:status` (docs/anytime.md)."
  [entry-point bound status elapsed-ms]
  (throw (ex-info (str entry-point " did not finish inside the bound it was given — "
                       (pr-str bound) ", " status " after "
                       (long (or elapsed-ms 0)) " ms.  Widen the bound, or ask through"
                       " ask-within / prove-within, which hand back what was found so"
                       " far with a :status saying it is a prefix")
                  {:type :budget-exhausted :entry-point entry-point :bound bound
                   :status status :elapsed-ms elapsed-ms})))

(defn- exhaustive-within
  "A bounded read's solutions when the search ran dry inside the bound and no refused depth
  cut it (`:truncated?`), else the refusal.  What `prove` and `ask` want, both of which
  answer with the whole solution set."
  [entry-point bound {:keys [results status elapsed-ms truncated?]}]
  (cond
    (not= :complete status) (bound-exhausted! entry-point bound status elapsed-ms)
    truncated?              (bound-exhausted! entry-point bound :depth-cut elapsed-ms)
    :else                   results))

(defn- decisive-within
  "The same for an existence question: whatever was found when anything was — one
  solution settles `true` however much of the space is left — an empty answer when the
  source ran dry with no refused depth cut, and the refusal otherwise.  Never an empty
  answer meaning *we stopped looking*."
  [entry-point bound {:keys [results status elapsed-ms truncated?]}]
  (cond
    (seq results)           results
    (not= :complete status) (bound-exhausted! entry-point bound status elapsed-ms)
    truncated?              (bound-exhausted! entry-point bound :depth-cut elapsed-ms)
    :else                   results))

(defn- query-options
  "`*query-options*` as the node engine's opts map, with `max-depth` folded in."
  [max-depth]
  (cond-> (cond (nil? *query-options*)     {}
                (keyword? *query-options*) {:strategy *query-options*}
                :else                      *query-options*)
    max-depth (assoc :max-depth max-depth)))

(defn- query-depth
  "How deep a read expands rules: the caller's `opts`, else `*query-options*` `:max-depth`.
  nil, no depth in either, is the no-rule-expansion answer; this never invents a number.
  `inference/*max-depth*` is not read.  `opt-keys` is the calling entry point's key set
  (`query-opt-keys`, `search-tree-opt-keys`, `compare-tacticians-opt-keys`) and `entry
  point` its name."
  [opts opt-keys entry-point]
  ;; A non-map `opts`, a key nothing reads and a non-positive `:max-depth` all read as "no
  ;; depth", a *different question* (the no-rule-expansion answer returned as if it were
  ;; the bounded one).  `(query kb g c :oops)`, `{:max-deph 3}` and `{:max-depth -3}` would
  ;; each do that silently, so they are refused, for `assert`'s reason.
  (opts/check! opts opt-keys entry-point
               (str "An option nothing reads takes the default in silence, which here"
                    " is a search at a setting nobody chose — a misspelt depth answers"
                    " facts-only as though no rule could reach the goal."))
  ;; The value domains, from the one table every bounded entry point shares
  ;; (`opts/bound-domains`): `:max-depth` here, plus `:max-ms` and `:node-budget` for
  ;; `search-tree` / `compare-tacticians`.  A depth that is not a non-negative integer
  ;; reads as no depth, an answer taken at a setting nobody chose.
  (opts/check-values! opts entry-point)
  (or (:max-depth opts)
      (when (map? *query-options*) (:max-depth *query-options*))))

(defn- backward-within
  "One bounded run of the backward chainer over `goals` in `context`, as the anytime
  partial-result contract (`vaelii.impl.budget`), on `prove`'s engine selector: the DFS
  through `res/prove-from` or the node engine through `inference/search-within`.  It exists
  beside `prove-within` because `prove` resolves a query context first (`read-in-context`)
  and `prove-within` refuses one.  `budget` may carry `:max-results`, which the existence
  entry points use to stop at the first answer, and `:refuse-depth-cut?`, which runs the
  DFS and adds its `:truncated?` flag."
  [kb goals context budget]
  (let [refuse? (:refuse-depth-cut? budget)
        budget  (dissoc budget :refuse-depth-cut?)]
    (if (and (not refuse?) (inference-engine? (:max-depth budget)))
      (inference/search-within
       (inference/session kb goals context (merge (query-options (:max-depth budget))
                                                  (provers/registry-bounds kb context)))
       budget)
      (let [rules-fn  (fn [g] (provers/candidate-rules kb g context))
            leaf      (provers/registry-bounds kb context)
            truncated (when refuse? (atom false))
            start     (System/nanoTime)
            {:keys [solutions status]}
            (res/prove-from kb rules-fn context
                            (cond-> (merge (budget/prove-bounds budget) leaf)
                              truncated (assoc :truncated truncated))
                            (res/initial-prove-stack kb goals context (:est-override leaf)) [])]
        ;; the contract's own assembler, so the two arms report elapsed time the same way;
        ;; no continuation, because this entry point hands back a whole answer or a refusal
        (cond-> (budget/from-batch solutions status start nil)
          truncated (assoc :truncated? @truncated))))))

(defn- prove-capped
  "`prove`'s body, stopping each engine once `max-results` solutions are in hand (nil:
  every one).  `provable?` asks it for one."
  [kb goal context opts max-results]
  (check-shape! (conjunction-goal-problem goal))
  (check-opts! :search opts prove-opt-keys "prove")
  (let [[goal context kb] (ist-goal kb goal context)
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
                                   (cap (merge (query-options nil) (provers/registry-bounds kb ctx))))

              :else
              (res/prove kb (fn [g] (provers/candidate-rules kb g ctx)) goals ctx
                         (cap (provers/registry-bounds kb ctx))))))
        ;; unbounded rule expansion, so an antecedent fact is not one of `goals` and its
        ;; context never reaches a placement: outside post-hoc's domain by construction
        {:expands-rules? true})))))

(defn prove
  "Backward-chain in `context` with the DFS prover; returns a vector of solution binding
  maps, type-aware and visible from `context`.  `prove` finds at least what `ask` finds.

  `goal` is a sentence or a **vector** of sentences, a conjunctive query whose shared
  variables join; an empty vector proves trivially.  Conjuncts are reordered for cost
  (`query-plan`), so solution order is not contract.  An `(ist Ctx S)` goal proves S in
  Ctx; as a conjunct it is refused, and so is a non-sentence conjunct (`:shape`).

  **One solution per derivation**: equal binding maps repeat, so use `distinct`, or
  `query` / `ask`.  `opts` is `prove-opt-keys`, `{:max-ms n :max-depth n}`: `:max-depth`
  prunes, and reaching `:max-ms` throws `:budget-exhausted` (docs/anytime.md)."
  ([kb goal] (prove kb goal '?ctx nil))
  ([kb goal context] (prove kb goal context nil))
  ([kb goal context opts] (prove-capped kb goal context opts nil)))

(defn provable?
  "Is `goal` provable in `context`?  Takes `prove`'s goal; a conjunction is provable iff
  all its conjuncts are, under one consistent binding.  The search stops at the first
  solution.  `opts` is `prove`'s bound (`prove-opt-keys`).  A bound it exhausts is
  `:budget-exhausted`, never `false`.  A depth prunes, so `{:max-depth 2}` answers `false`
  for no derivation within two rewrites."
  ([kb goal] (provable? kb goal '?ctx nil))
  ([kb goal context] (provable? kb goal context nil))
  ([kb goal context opts]
   ;; before the `seq` test: `(seq :oops)` throws a bare IllegalArgumentException, where
   ;; `prove` refuses the same non-map opts by name — this entry point mirrors that one
   (check-opts! :search opts prove-opt-keys "provable?")
   (if (seq opts)
     (do (check-shape! (conjunction-goal-problem goal))
         (let [[goal context kb] (ist-goal kb goal context)
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
  "Answer `goal` in `context` with the pluggable prover engine: stored facts, taxonomy
  closures, disjointness, predicate metadata, evaluables, NAF, argument-type inference and
  any prover the application added.  Returns solution binding maps projected to the goal's
  variables.

  **No rule expansion**: a `set/backwardRule`'s conclusion is not seen; use `query` with a
  `:max-depth`, or `prove`.  An `(ist Ctx S)` goal asks S in Ctx.  One sentence: a vector
  is refused (`:shape`).  `opts` is `{:max-ms n}` (`ask-opt-keys`); reaching it is
  `:budget-exhausted`, not a prefix.  `ask-within` hands the prefix back."
  ([kb goal] (ask kb goal '?ctx nil))
  ([kb goal context] (ask kb goal context nil))
  ([kb goal context opts]
   (check-shape! (sentence-goal-problem goal))
   (check-opts! :search opts ask-opt-keys "ask")
   (let [[goal context kb] (ist-goal kb goal context)]
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
   (check-opts! :search opts ask-opt-keys "ask?")
   (if (seq opts)
     (do (check-shape! (sentence-goal-problem goal))
         (let [[goal context kb] (ist-goal kb goal context)]
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

(defn- remaining-clock
  "`opts` with `:max-ms` cut to what is left of the deadline `dl`, so a read that runs
  several searches holds them all to one clock.  A nil `dl` returns `opts`."
  [opts dl]
  (cond-> opts
    dl (assoc :max-ms (max 0 (quot (- (long dl) (long (budget/now))) 1000000)))))

(defn- clocked
  "`(read)`'s answers realized under `opts`' `:max-ms` and capped at `max-results`, or
  `bound-exhausted!`'s refusal naming `entry-point`.  A node-engine run the clock stops
  throws `::inference/timeout`, which `clocked` turns into the same refusal; a portfolio
  racer's throw arrives wrapped in the future's `ExecutionException`."
  [entry-point opts max-results read]
  (let [bound  {:max-ms (:max-ms opts)}
        {:keys [results status elapsed-ms]}
        (try (budget/collect (read) (cond-> bound max-results (assoc :max-results max-results))
                             read)
             (catch Exception e
               (if-let [t (some #(when (::inference/timeout (ex-data %)) (ex-data %))
                                (take-while some? (iterate ex-cause e)))]
                 {:status :timeout :elapsed-ms (:elapsed-ms t)}
                 (throw e))))]
    (if (#{:complete :capped} status)
      results
      (bound-exhausted! entry-point bound status elapsed-ms))))

(defn- query-node-opts
  "The node engine's opts for a depth-`d` read in `context`: `*query-options*` and the
  caller's `opts`, plus the depth and the two things that make the engine answer what
  `query` means — the registry as its leaf (so an antecedent is answerable by *any*
  prover: transitivity, an evaluable, a calculus, an inferred argument type) and the
  cost model that leaf is planned by.  `query-at` and `query-status-at` both build the
  same run from it."
  [kb context d opts]
  (merge (query-options nil) opts {:max-depth d} (provers/registry-bounds kb context)))

(defn- query-at
  "`query`'s answer from **one** named context, once the depth has been read and the goal
  resolved.  `CxInference` asks it once per reader (`vaelii.impl.vantage`), so a read
  from a vantage is a function of that vantage.  `max-results` stops the node engine once
  that many answers are in hand (nil: every one); registry reads are lazy and need no cap.
  Under `opts`' `:max-ms` the answer is `clocked`'s."
  [kb goals-in context d opts max-results]
  (let [goals (goals-in context)
        read
        (fn []
          (cond
            ;; A depth: the node engine, whose leaf is the registry, so an antecedent is
            ;; answerable by *any* prover and the engine only expands rules.  `prove`'s leaf is
            ;; the stored facts instead.
            (and d (pos? (long d)))
            (inference/solutions kb goals context
                                 (cond-> (query-node-opts kb context d opts)
                                   max-results (assoc :max-results max-results)))

            ;; No depth and one literal: the registry answers it directly, and lazily to the
            ;; first result.  The goal is already prepared, which is the whole of what `ask`
            ;; would add before handing it over.
            (= 1 (count goals))
            (provers/ask kb (first goals) context)

            ;; No depth and a **conjunction**: still the registry and no rule, but the conjuncts
            ;; must join, which one `ask` per literal cannot do.  The recursive chainer at depth 0
            ;; is the registry as its leaf with no rewrite admitted, so the shapes agree on their
            ;; answers.  Lazy, like the single-literal case.
            :else
            (res/prove-seq kb #(provers/candidate-rules kb % context) goals context
                           (assoc (provers/registry-bounds kb context) :max-depth 0))))]
    (if (:max-ms opts) (clocked "query" opts max-results read) (read))))

(defn- query-capped
  "`query`'s body, with `query-at`'s `max-results`."
  [kb goal context opts max-results]
  (check-shape! (conjunction-goal-problem goal))
  (let [[goal context kb] (ist-goal kb goal context)
        d  (query-depth opts query-opt-keys "query")
        dl (budget/deadline opts)]
    (read-alternatives
     kb goal context max-results
     (fn [goals-in]
       (read-in-context kb goals-in context
                        #(query-at kb goals-in % d (remaining-clock opts dl) max-results)
                        {:expands-rules? (boolean (and d (pos? (long d))))})))))

(defn query
  "Answer `goal` in `context` as a seq of **binding maps** (`{?x val …}`) projected onto
  the goal's own variables.  `goal` is a sentence, or a **vector** of them: a conjunctive
  query whose shared variables join, as `prove` takes.

  `opts` makes one decision, how deep to expand rules:

      (query kb goal ctx)                   no rule expansion — the registry alone
      (query kb goal ctx {:max-depth 3})    the node engine, ≤3 rewrites deep

  There is no default depth.  Detail: docs/api.md, \"Contract notes: `query`\"."
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
  "Realize `xs`, timing it: `[vector first-answer-ns total-ns timeout?]`, `first-answer-ns`
  nil when `xs` is empty.  A `query-status` over the facts-only reads, which come back as
  lazy seqs the way `query` returns them.  `timeout?` is true when the `budget/now`
  instant `dl` passed between pulls, or inside one at a walk reading `budget/*deadline*`."
  [xs dl]
  (let [start (System/nanoTime)
        done  (fn [acc first-ns timeout?]
                [(persistent! acc) first-ns (- (System/nanoTime) start) timeout?])]
    (loop [xs xs, acc (transient []), first-ns nil]
      (let [s (cond (and dl (>= (long (budget/now)) (long dl))) ::budget/interrupted
                    dl                                         (budget/interruptible dl #(seq xs))
                    :else                                      (seq xs))]
        (cond
          (identical? ::budget/interrupted s) (done acc first-ns true)
          s     (recur (rest s) (conj! acc (first s)) (or first-ns (- (System/nanoTime) start)))
          :else (done acc first-ns false))))))

(defn- query-status-at
  "`query-status`'s report from **one** concrete context.  The node engine when a depth
  expands rules (`inference/search-report`, which is where truncation and the phase
  timings come from), the facts-only reads otherwise — realized here so the report can
  time them, since a depth-0 read is a complete answer to its own question and a depth
  never cut it."
  [kb goal context d opts]
  (if (and d (pos? (long d)))
    (let [goals (quasiquote/prepare-conjunction-for-read kb goal context)
          {:keys [answers truncated? timeout? time-to-first-answer-ms total-time-ms stats
                  unenumerated unenumerated-in-guards]}
          (inference/search-report kb goals context (query-node-opts kb context d opts))]
      {:answers                 answers
       :count                   (count answers)
       :status                  (cond timeout?            :timeout
                                      truncated?          :truncated
                                      (seq unenumerated) :incomplete
                                      :else              :complete)
       :truncated?              truncated?
       :unenumerated            unenumerated
       :unenumerated-in-guards  unenumerated-in-guards
       :depth                   d
       :time-to-first-answer-ms time-to-first-answer-ms
       :total-time-ms           total-time-ms
       :stats                   stats})
    (let [goals-in (fn [ctx] (quasiquote/prepare-conjunction-for-read kb goal ctx))
          [[answers first-ns total-ns timeout?] {:keys [unenumerated unenumerated-in-guards]}]
          (provers/with-unenumerated
            #(timed-realize (query-at kb goals-in context d (dissoc opts :max-ms) nil)
                            (budget/deadline opts)))]
      {:answers                 answers
       :count                   (count answers)
       :status                  (cond timeout?           :timeout
                                      (seq unenumerated) :incomplete
                                      :else              :complete)
       :truncated?              false
       :unenumerated            unenumerated
       :unenumerated-in-guards  unenumerated-in-guards
       :depth                   d
       :time-to-first-answer-ms (when first-ns (/ (double first-ns) 1e6))
       :total-time-ms           (/ (double total-ns) 1e6)})))

(defn query-status
  "`query`'s answers, plus a **report** of the run, so a query truncated at the depth bound
  reads differently from one whose goal is unprovable.

      {:answers                 [{?x v} …]   `query`'s own answers, realized
       :count                   n
       :status                  :complete | :truncated | :incomplete | :timeout
       :truncated?              bool         = (= status :truncated)
       :unenumerated            [P …]        transitive predicates whose closure a goal
                                             with both arguments open did not enumerate
       :unenumerated-in-guards  [P …]        those recorded inside an `unknown` or
                                             `exceptWhen` evaluation
       :depth                   d | nil      the depth bound the read ran under
       :time-to-first-answer-ms t | nil      nil when there are no answers
       :total-time-ms           t
       :stats                   {…}}         node-engine `tree-stats`, at a depth

  `:truncated?` is conservative: true means the depth bound stopped at least one rewrite, so
  the answers may be incomplete; false with an empty `:unenumerated` guarantees every answer
  the KB entails at that depth.  `:incomplete` means `:unenumerated` is non-empty and the
  bound cut nothing.  Opts and
  depth resolution are `query`'s.  A variable or query context is refused
  (`:unsupported-context`).  docs/api.md, \"What an exhausted bound answers\"."
  ([kb goal context] (query-status kb goal context nil))
  ([kb goal context opts]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context kb] (ist-goal kb goal context)]
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
  premise in a scratch context below `context`.  Answers

      {:solutions   [binding-map …]     `prove`'s, unprojected, under the hypotheses
       :hypotheses  [{:sentence :context :handle} …]   irredundant; empty = proved outright
       :refused     [sentence …]        dead ends not assumed, when none proved
       :context     CxAbductionX
       :status      :complete | :capped}

  `opts`: `:max-hypotheses` (default 8), `:max-depth` (8), `:keep?` (the scratch context
  stands until `abduce-discard!`; otherwise every `:handle` is nil).  Refusals:
  `:unknown-option`, `:shape`, `:not-ground` (a variable context), `:too-many-kept`.
  docs/abduction.md."
  ([kb goal] (abduce kb goal 'CxUniverse nil))
  ([kb goal context] (abduce kb goal context nil))
  ([kb goal context opts]
   (check-opts! :bound opts #{:max-hypotheses :max-depth :keep?} "abduce")
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

(def ^:private holds-limit
  "The most ground goals `instance-reads` keeps per context for a change-clock value, cleared
  wholesale past it."
  4096)

(defn- instance-reads
  "The three facts-only reads `integrity/subsumption-reading` makes, through `query` at
  `context` with `{:max-depth 0}`: `:members`, the terms a `(t ?x)` query answers for type
  `t`; `:isa?`, whether term `x` is an instance of type `t`; and `:holds?`, whether a
  ground goal is answered.  The first two are memoized per argument for one audit, which
  writes nothing between its pairs.  `:holds?` is kept per context for one value of the
  change clock, so every audit and `describe` between two writes asks a ground goal once.
  The depth is forced so no rule is expanded under a caller's `*query-options*` depth: a
  node-engine search of `(a ?x)` over the whole starter, once per taxonomy-open pair, hangs."
  [kb context]
  (let [held (observe/clocked (reasoning/qcn kb) [::holds context] (fn [_] (atom {})))]
    {:members (memoize (fn [t] (into [] (map #(get % '?x))
                                     (query kb (list t '?x) context {:max-depth 0}))))
     :isa?    (memoize (fn [x t] (isa? kb x t context)))
     :holds?  (fn [goal]
                (caches-impl/read-through held (caches-impl/limit-of :resident holds-limit) goal
                                          #(boolean (seq (query kb goal context {:max-depth 0})))))}))

(defn- audit-row-reads
  "The prepared taxonomy reads for one audit row with fixed first type `a`. The global
  ancestor and descendant sets answer both directions of subsumption. Only this row
  retains the sets and the contextual separation predicate; other subtype reads use the
  taxonomy's bounded closure cache. Facts-only reads remain those of `rd`."
  [kb context rd a]
  (let [above (genls kb a)
        below (specs kb a)
        sep?  (tax/disjointness-test (reasoning/taxonomy kb) a context)]
    (assoc rd
           :genl? (fn [x y]
                    (cond (= x a) (contains? above y)
                          (= y a) (contains? below x)
                          :else   (genl? kb x y)))
           :specs (fn [t] (if (= t a) below (specs kb t)))
           :disjoint? (fn [x y] (if (= x a) (sep? y) (disjoint? kb x y context))))))

(defn subsumption-statuses
  "The set of applicable subsumption relationships between types `a` and `b`: any subset
  of `#{:coextensional :genl :spec :disjoint :orthogonal}`.  A consistent pair yields a
  singleton, an inconsistent pair several, and a pair with no provable relationship the
  empty set.  `genl?` reads the global cached closure; `disjoint?` and the `:orthogonal`
  witnesses read `context` (default `CxUniverse`).  The instance and subtype reads are
  facts-only, so the status is the same under every query engine.  Witnesses and
  combinations: docs/taxonomy.md."
  ([kb a b] (subsumption-statuses kb a b 'CxUniverse))
  ([kb a b context] (:statuses (integrity/subsumption-reading kb a b context (instance-reads kb context)))))

(defn subsumption-status
  "The subsumption relationship of type `a` to type `b`, one of: `:coextensional` (each is
  `genl` the other), `:genl` (`a` is a subtype of `b`), `:spec` (`a` is a supertype of `b`),
  `:disjoint` (provably no shared instance), `:orthogonal` (see `subsumption-statuses`),
  `:unknown` (none provable) or `:inconsistent` (contradictory relationships hold).
  Wraps `subsumption-statuses`: an empty set is `:unknown`, a singleton is that status and
  two or more is `:inconsistent`.  `context` is the vantage `:disjoint` and `:orthogonal`
  are read from (default `CxUniverse`)."
  ([kb a b] (subsumption-status kb a b 'CxUniverse))
  ([kb a b context]
   (let [ss (subsumption-statuses kb a b context)]
     (case (count ss)
       0 :unknown
       1 (first ss)
       :inconsistent))))

(defn disjointness-audit
  "The `subsumption-status` of every unordered pair of distinct types **visible from
  `context`** (default `CxWell`).  Returns
  `{:types n :pairs n :by-status {status count …} :pairs-data [{:a t :b t :status s :statuses ss} …]}`.
  The shared-instance query runs only for a pair the taxonomy and disjoint declarations
  leave open, facts-only.  `:unknown` pairs are the candidates for a missing `disjoint` or
  `orthogonal` assertion.  An entry whose `:statuses` holds `:orthogonal` also carries
  `:witness` (`:declared`, `:shared-instance`, `:shared-spec` or `:unwitnessed-spec`) and,
  for the last three, `:via`, the instance or subtype found."
  ([kb] (disjointness-audit kb 'CxWell))
  ([kb context]
   ;; `by-print-key`, never bare `sort`: a type node may be a NAT (a list), which `compare`
   ;; throws on.  A relation is a genl node when `genl` specializes it by another
   ;; (`(genl performedBy doneBy)`) but has no instances to share or keep apart, so every
   ;; pair it entered could only read :unknown.
   (let [ts   (into [] (remove #(relation? kb % context)) (nm/by-print-key (types kb context)))
         n    (count ts)
         rd   (instance-reads kb context)
         data (with-open [r (progress/start ::disjointness-audit
                                            "disjointness audit: read the type pairs"
                                            (quot (* n (dec n)) 2))]
                (persistent!
                 (reduce
                  (fn [acc i]
                    (let [rd (audit-row-reads kb context rd (nth ts i))]
                      (reduce
                       (fn [a j]
                         (let [{ss :statuses w :witness t :via}
                               (integrity/subsumption-reading kb (nth ts i) (nth ts j) context rd)]
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
                       acc (range (inc i) n))))
                  (transient []) (range (dec n)))))]
     {:types     n
      :pairs     (count data)
      :by-status (frequencies (map :status data))
      :pairs-data data})))

(defn query-plan
  "How a goal would be answered.  A **single sentence** gives the provers applicable to it
  with their per-prover estimates and which of them run; an entry that does not run
  carries `:runs? false` with a `:shadowed-by`, or `:guarded-by` naming a source no prover
  reads.  A **vector** gives the *join plan*: the conjuncts in run order, each a map of
  `:goal`, `:bound-before`, `:est-matches` (upper bound on fan-out under those bindings),
  `:est-rows`, `:est-prefix`, `:block` and the flags `:deferred?`, `:recursive?` and
  `:isolated?` (docs/inference.md, \"Conjunctive query planning\").

    (query-plan kb '[(dog ?y) (parentOf Tom ?y)] 'CxMantle)
    ;; => ({:goal (parentOf Tom ?y) :est-matches 2 :bound-before #{}    ...}
    ;;     {:goal (dog ?y)          :est-matches 1 :bound-before #{?y}  ...})"
  ([kb goal] (query-plan kb goal '?ctx))
  ([kb goal context]
   (check-shape! (conjunction-goal-problem goal))
   (let [[goal context kb] (checked-ist-goal kb goal context)]
     (if (vector? goal)
       (plan/explain kb goal context)
       (provers/plan kb goal context)))))

(defn- node-debugger-read
  "The shared read of `search-tree` and `compare-tacticians`: check the goal's shape and
  `opts` against `opt-keys`, prepare the conjunction, and run the node-engine fn `run`."
  [run kb goal context opts opt-keys fn-name]
  (check-shape! (conjunction-goal-problem goal))
  (let [[goal context kb] (checked-ist-goal kb goal context)
        d     (query-depth opts opt-keys fn-name)
        goals (quasiquote/prepare-conjunction-for-read kb goal context)]
    (run kb goals context (query-node-opts kb context d opts))))

(defn search-tree
  "The backward search for `goal` in `context` as data: every node the frontier reached,
  what each cost and what was dropped.  The read behind the inference debugger.

  Needs a depth (`{:max-depth n}`, or `*query-options*` `:max-depth`) and runs `query`'s
  search.  The key set is `search-tree-opt-keys` (`:node-budget`, an optional `:max-ms`
  that reports `:timeout`, and `:strategy`); another key is refused (`:unknown-option`).
  Returns `{:goals :context :strategy :status :bounded? :answers :nodes :stats
  :unenumerated :unenumerated-in-guards}`; `:status` is `:complete`, `:bounded` or
  `:timeout`, and each answer carries the `:node` it came off."
  ([kb goal] (search-tree kb goal '?ctx nil))
  ([kb goal context] (search-tree kb goal context nil))
  ([kb goal context opts]
   (node-debugger-read inference/search-tree kb goal context opts
                       search-tree-opt-keys "search-tree")))

(defn compare-tacticians
  "Run `goal` in `context` under several **tacticians** (the node engine's search
  orderings), each to completion, and return one row per tactician: the search it ran, its
  wall-clock `:ms`, its `:status`, its `:unenumerated` and its answer set.  The answer sets
  must be identical; a row that differs is a bug, surfaced.

  `opts` is `compare-tacticians-opt-keys`: `search-tree`'s depth and bounds, plus
  `:tacticians` (the subset to run, `inference/default-compare-tacticians` otherwise),
  and not `:strategy`.  Needs a depth as `search-tree` does."
  ([kb goal] (compare-tacticians kb goal '?ctx nil))
  ([kb goal context] (compare-tacticians kb goal context nil))
  ([kb goal context opts]
   (node-debugger-read inference/compare-tacticians kb goal context opts
                       compare-tacticians-opt-keys "compare-tacticians")))

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

  A prover reading **stored facts** gives `:solve-with-support` in place of `:solve`, so
  a forward rule that fired on an answer is withdrawn when a fact it named is retracted:

    :solve-with-support  a seq of `[bindings support]`, `support` the handles of the facts
                         the answer was read from
    :support-functors    the predicates it answers with support, a non-empty set
    :support-sources     the predicates it reads to answer them, a set

  Three readings take a constant or a fn: `:est-bindings` (a non-negative number; by default
  1 for a ground goal and unbounded for an open one), `:cost` (`:lookup`, `:compute` by
  default, or `:search`) and `:completeness` (0 to 100; 50 by default).  Refused
  (`:unknown-option`): an unknown key, a missing `:applicable?`, both or neither solve key, a
  support key without its companions, a value outside its domain (a fn's return is checked
  at each call), and a support element that is not a handle (as the answer is read).
  docs/inference.md, *What a computed answer rests on*."
  [spec]
  (provers/fn-prover spec))

(defn add-evaluatable
  "Register a plain Clojure fn `f` as the evaluatable predicate/function `pred` on `kb`.
  Two shapes, chosen by `opts`:

  * a **check** predicate: `(add-evaluatable kb 'evenSum (fn [a b] (even? (+ a b))))`
    makes `(evenSum 2 4)` hold; every argument must be ground;
  * a **result-binding** function: `(add-evaluatable kb 'sumOf + {:result :first})` binds
    `(sumOf ?r 2 3)` to `?r = 5`; the `:result` slot is a variable to bind or a value to
    check, and the rest are the ground inputs `f` receives.

  `opts` is `provers/evaluatable`'s: `:result`, `:arity`, `:cost` and `:completeness`
  (defaults `:lookup`, 100); another key is refused (`:unknown-option`).  Returns `kb`."
  ([kb pred f] (add-evaluatable kb pred f nil))
  ([kb pred f opts]
   (opts/check! opts #{:result :arity :cost :completeness} "add-evaluatable"
                (str "An option nothing reads takes the default in silence, which for a"
                     " computed relation means a shape or a cost tier the caller did not"
                     " choose."))
   (add-prover kb (provers/evaluatable pred f opts))))

(defn register-modal-predicate
  "Grant `pred` belief-style projection: `(pred agent sentence)` is answered by proving
  `sentence` in `agent`'s context, as `believes` is (docs/belief.md).  Asserts the
  `(modal_predicate pred)` marker, so `retract!` of it takes the grant back.  With no
  `context` the grant is in `CxUniverse`, where the default `believes` grant lives; pass a
  `context` to scope it.  Returns `kb`."
  ([kb pred] (register-modal-predicate kb pred sx/root-context))
  ([kb pred context] (assert kb (list 'modal_predicate pred) context) kb))

;; ---- the optional reasoners ---------------------------------------------
;; The reasoners `reasoners` names ship unregistered, and until one is registered, its
;; vocabulary is ordinary content.  `vaelii.core` is the only namespace outside this repo may name, so
;; these fns name the provers in `vaelii.impl.*`.

(defn reasoners
  "The names of the optional reasoners, sorted — what `add-reasoner` takes.  `calculi`
  describes the six that are relation algebras in full; the other six are the
  quantitative reasoners, the calendar clock, the instant-inclusion reader and the
  start-bound reader, and `:brave-cautious` is the ASP dilemma reader (docs/labeling.md)."
  []
  (provers/reasoner-names))

(defn reasoner
  "The prover named by keyword, a value for `add-prover`.  `add-reasoner` is the ordinary
  way in.  Six are the relation algebras `calculi` describes; `:duration` and `:metric-time`
  are the quantitative pair (docs/duration.md, docs/stp.md), `:sign` the qualitative
  arithmetic (docs/sign.md), `:calendar` the clock behind the calendar constructors,
  `:includes-instant` and `:tightest-start-bound` two temporal reads (docs/time.md), and
  `:brave-cautious` the ASP reader of `(bravely S)` / `(cautiously S)`
  (docs/labeling.md).  An unknown name is refused as `:unknown-option`."
  [nm]
  (provers/reasoner nm))

(defn- watches-a-calculus-would-answer
  "The standing watches on `kb`, as `{:token :goal :calculus}`, whose goal predicate a
  calculus among the reasoners `names` answers, of either polarity."
  [kb names]
  (let [cs (keep #(:calculus (provers/reasoner %)) names)]
    (for [{:keys [token goal]} (feed/listeners kb)
          :when goal
          :let [b (sx/underlying-body goal)
                c (when (sequential? b)
                    (first (filter #(contains? (:predicates %) (first b)) cs)))]
          :when c]
      {:token token :goal goal :calculus (:name c)})))

(defn add-reasoner
  "Register one or more shipped reasoners on `kb` by name, returning `kb`.

      (doto (open-kb {}) (add-reasoner :allen :rcc8))

  Registration is per-KB and idempotent per name (docs/qcn.md).  A bad name in the list
  registers none of it, and neither does a calculus that answers the goal predicate of a
  standing `watch` (`:not-watchable`).  A later `open-kb` names the same set in
  `:reasoners` or passes `:reasoners :stored`; any other set is refused
  (`:reasoner-mismatch`; docs/storage.md, \"The reasoner set\")."
  [kb & names]
  (run! provers/check-reasoner-name! names)
  (when-let [ws (seq (watches-a-calculus-would-answer kb names))]
    (throw (ex-info (str "add-reasoner would register a calculus answering the goal of "
                         (count ws) " standing watch(es), which watch refuses: "
                         (pr-str (mapv :goal ws)) " — unwatch them first")
                    {:type :not-watchable :watches (vec ws)})))
  (kb/add-reasoners! kb names)
  kb)

;; ---- qualitative constraint reasoning -----------------------------------
;; These four reads expose the whole network a context's facts constrain (docs/qcn.md).
;; A calculus answers whether or not its prover is registered, and its namespace is
;; resolved at runtime, so requiring this namespace loads no leaf algebra.

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
  "The constraint network `calculus` computes over everything **believed and visible** in
  `context`: every pair of terms its predicates relate, tightened by path consistency.

    {:calculus :rcc8  :context CxWell
     :nodes [A B C]   :consistent? true
     :constraints {[A B] #{:ntpp} [B A] #{:ntppi} …}}

  When the believed facts are unsatisfiable `:consistent?` is false, `:constraints` is the
  network as stated, and `:unsatisfiable` names the pairs no model satisfies.
  `:unsatisfiable-sources` has one map per component
  `{:source :metric :pairs [[P Q] …] :cycle [P Q R] :support [handle …]}`; `:cycle` is the
  instants on a negative cycle (`:metric` only), `:support` the facts behind them
  (docs/qcn.md).  A variable context reads every context into one diagnostic network."
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
  "One concrete arrangement consistent with everything believed in `context`,
  `{[a b] → relation}` with one base relation per pair, or nil when the believed facts are
  unsatisfiable.  The arrangement is a function of the facts alone, never of arrival
  order.  A variable context draws it from the union network of every context, a
  diagnostic reading, not a world any reader sees (docs/qcn.md)."
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
;; A budget realizes the lazy answer stream under a bound and reports whether it ran dry
;; (`:complete`) or was cut short (`:timeout` / `:capped`).  The unrealized tail (for
;; `prove`, the DFS goal stack) is the continuation.  The partial-result contract is in
;; vaelii.impl.budget.

(defn ask-within
  "Anytime `ask`: answer `goal` in `context`, bounded by `budget`, a map of any of
  `{:max-ms n :max-results n :max-cost <tier>}`.  Returns the partial-result contract
  `{:results :status :count :elapsed-ms :resume :unenumerated :unenumerated-in-guards}`
  (vaelii.impl.budget): `:results` are the solutions realized in *this* step, `:status` is
  `:complete` / `:incomplete` / `:timeout` / `:capped`, and `:resume` (nil when `:complete`
  or `:incomplete`) continues the same search under a fresh budget via `resume`.
  `:incomplete` is a run that ran dry after a both-open goal over a transitive predicate
  named in `:unenumerated`.  `:max-cost` drops every prover whose `cost` tier is above the
  ceiling (`:lookup` < `:compute` < `:search`); any other value throws
  (`:unknown-option`).  docs/anytime.md."
  ([kb goal budget] (ask-within kb goal '?ctx budget))
  ([kb goal context budget]
   ;; `ask`'s entry point, since this is `ask` bounded: a goal it refuses cannot be one this
   ;; answers, or the budget would decide which spelling is legal
   (check-shape! (sentence-goal-problem goal))
   ;; The budget against `ask`'s half of the key set (`budget/ask-budget-keys`):
   ;; `:max-ms` / `:max-results` / `:max-cost`, not `:max-depth` / `:max-term-growth`.
   ;; `collect` re-checks against the union, so a `resume` under either entry point still
   ;; passes.  Value checks ride along, so a string `:max-ms` is `:unknown-option`.
   (budget/check-budget! budget budget/ask-budget-keys "ask-within")
   (let [[goal context kb] (checked-ist-goal kb goal context)
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
  "One bounded step of the DFS prover, wrapped in the anytime contract.  The continuation
  captures the remaining goal stack, so `resume` continues where the search stopped.  The
  bounds map is `budget/prove-bounds`, the one translation of the key set."
  [kb context budget stack una truncated]
  (budget/check-budget! budget)
  (let [rules-fn (fn [g] (provers/candidate-rules kb g context))
        bounds   (merge (budget/prove-bounds budget) (provers/registry-bounds kb context)
                        {:truncated truncated})
        start    (System/nanoTime)
        {:keys [solutions status stack]} (binding [provers/*unenumerated* una]
                                           (res/prove-from kb rules-fn context bounds stack []))]
    (budget/from-batch solutions status start
                       (fn [b] (run-prove-step kb context b stack una truncated)))))

(defn prove-within
  "Anytime `prove`: run the depth-first backward chainer over `goal` (a sentence or a
  conjunction vector, as `prove`) in `context`, bounded by `budget`, a map of any of
  `{:max-ms n :max-results n :max-depth n :max-term-growth n}`.  Returns the partial-result
  contract of `ask-within` plus `:truncated?`, and `resume` continues from the unfinished
  goal stack (docs/anytime.md).  `:max-depth` bounds the rule expansions the search may
  stack; `:max-term-growth` overrides `res/default-max-term-growth`, the nesting a rule may
  add past the deepest term its path has met.  `:max-cost` is ignored here."
  ([kb goal budget] (prove-within kb goal '?ctx budget))
  ([kb goal context budget]
   (check-shape! (conjunction-goal-problem goal))
   ;; The budget against `prove`'s half of the key set (`budget/prove-budget-keys`), not
   ;; `:max-cost`.  **Before `inference-engine?` reads `:max-depth`**: the selector takes
   ;; `(long max-depth)`, so a string depth is a bare cast unless the value check has
   ;; already refused it.
   (budget/check-budget! budget budget/prove-budget-keys "prove-within")
   (let [[goal context kb] (checked-ist-goal kb goal context)
         goals (quasiquote/prepare-conjunction-for-read kb goal context)]
     (if (inference-engine? (:max-depth budget))
       ;; The node engine's continuation is the session itself, and the bounds are checked
       ;; per node expansion, not per yielded solution (`inference/search-within`), so a
       ;; wide unproductive stretch cannot run past the deadline.
       (let [sess (inference/session kb goals context
                                     (merge (query-options (:max-depth budget))
                                            (provers/registry-bounds kb context)
                                            {:track-truncation? true}))]
         (budget/reporting-unenumerated
          (inference/search-within sess budget)
          #(assoc (inference/unenumerated sess) :truncated? (boolean @(:truncated sess)))))
       ;; the DFS's continuation is the goal stack, so the collectors ride the closure
       (let [una       (provers/unenumerated-collector)
             truncated (atom false)]
         (budget/reporting-unenumerated
          (run-prove-step kb context budget
                          (res/initial-prove-stack kb goals context
                                                   (:est-override (provers/registry-bounds kb context)))
                          una truncated)
          #(assoc (provers/unenumerated-report una) :truncated? @truncated)))))))

(defn resume
  "Continue a `:timeout` / `:capped` partial result from `ask-within` / `prove-within`
  under a fresh `budget`, returning the next partial result, whose `:unenumerated` holds
  every step's.  A `:complete` or `:incomplete` result has no continuation and is returned
  unchanged (docs/anytime.md), so

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

  A lazy seq of {:level :handle :sentence :context :bindings}, nil where the level cannot
  supply a field; at level 0 a vector goal is an index path.  Under `lookup-opt-keys`'
  `{:max-ms n}` it is a vector, or `:budget-exhausted` at the clock.  docs/levels.md."
  ([kb level goal] (lookup kb level goal '?ctx))
  ([kb level goal context]
   (let [[goal context kb] (checked-ist-goal kb goal context)]
     (lvl/lookup kb level goal context)))
  ([kb level goal context opts]
   (check-opts! :search opts lookup-opt-keys "lookup")
   (if (empty? opts)
     (lookup kb level goal context)
     (let [[goal context kb] (checked-ist-goal kb goal context)]
       (exhaustive-within "lookup" opts (lvl/lookup-within kb level goal context opts))))))

(defn escalate
  "The cheapest level that answers `goal`: climb from `floor` and stop at the first level
  with results.  Returns {:level :name :results :tried}, `:results` that level's lazy seq;
  nothing answering gives :level nil.  `:unenumerated` is present when the stopping level
  answered a both-open goal over a transitive predicate from its extent (docs/levels.md).
  `floor` defaults to 2 (also for nil).  `opts` is `escalate-opt-keys`: `{:max-ms n}`; a
  climb stopped before any level answered returns `{:level nil :status :timeout}`."
  ([kb goal] (escalate kb goal '?ctx))
  ([kb goal context]
   (let [[goal context kb] (checked-ist-goal kb goal context)]
     (lvl/escalate kb goal context)))                ; `levels/query-floor` owns the default
  ([kb goal context floor]
   (let [[goal context kb] (checked-ist-goal kb goal context)]
     (lvl/escalate kb goal context floor)))
  ([kb goal context floor opts]
   (check-opts! :search opts escalate-opt-keys "escalate")
   (let [[goal context kb] (checked-ist-goal kb goal context)]
     (lvl/escalate kb goal context (if (nil? floor) lvl/query-floor floor) opts))))

(defn explain-levels
  "What every level yields for `goal`: a seq of {:level :name :count}.  The level at which
  the count first rises is the machinery the answer depends on.  Unlike `lookup` it
  realizes every level fully.  A row carries `:unenumerated` when its count lacks the
  closure pairs of a both-open goal over a transitive predicate (docs/levels.md).  It
  explains the retrieval stack, not belief; `why` / `why-not` explain belief."
  ([kb goal] (explain-levels kb goal '?ctx))
  ([kb goal context]
   (let [[goal context kb] (checked-ist-goal kb goal context)]
     (lvl/explain kb goal context))))

(defn levels
  "The stack as data: {:level :name :below :adds} per level."
  [] lvl/level-table)

(defn- clash-grounds?
  "Does `opts` ask a clash report for its `:grounds`?  Yes unless `{:grounds? false}`.
  An opts key outside `ks` is refused, as at the extent readers."
  [opts fn-name ks]
  (opts/check! opts ks fn-name
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
  "The contradictions the last settle could not satisfy: irreducible clashes among
  known-true content, two `:monotonic` beliefs that cannot both hold.  Both stay believed.
  A coexisting pair at `:default` is a dilemma, and `contradictions` reports it.

  Each entry has `contradictions`' shape, with the entry's `:sentence` composing
  `contradicts` over the member sentences, in content order.  `{:grounds? false}` leaves
  `:grounds` off.  `{:defeats? true}` adds the decided nogoods, in content order, each
  with `:verdict :defeat`, `:placed-in` (the most general placement contexts that decide
  it), and `:loser` and `:winners` (`{:handle :sentence :context :defeat-class :rules}`).
  A context below `:placed-in` does not believe the loser (docs/nmtms.md)."
  ;; each arity reads the clashes itself rather than calling another through the var, so
  ;; a caller that rebinds `conflicts` to count its scans counts one per call
  ([kb] (clashes/with-grounds kb (clashes/ranked (clashes/conflicts-of kb))))
  ([kb opts]
   (let [grounds? (clash-grounds? opts "conflicts" #{:grounds? :defeats?})
         rs       (clashes/ranked (if (:defeats? opts)
                                    (clashes/conflicts-and-defeats-of kb)
                                    (clashes/conflicts-of kb)))]
     (if grounds? (clashes/with-grounds kb rs) rs))))

(defn contradictions
  "The coexisting pairs the last settle left standing: represented dilemmas, not failures.
  Each entry is
  `{:nogood #{h ..} :handles [h ..] :priority int :kind kw-or-nil :sentence (contradicts ..)
  :sides [{:handle :sentence :context :defeat-class :justifications [...]} ...]
  :grounds [{:handle :sentence :context} ...]}`, plus `:inherited` for `:kind :inherited`
  and `:vantages {context handle}` where placements defeat different members, in content
  order.  `:priority` ranks a definitional clash (3 to 4) above a rebuttal (1 to 2), and an
  inherited clash is a rebuttal.  `(contradictions kb)` reports the KB as a whole; `(contradictions kb context)`
  what stands for one reader (a nil or variable context is the KB-wide reading).
  `{:grounds? false}` leaves `:grounds` off.  Kinds and scoping: docs/nmtms.md, \"The
  clash reports\"; the inherited clash: docs/inherit.md."
  ;; as in `conflicts`, no arity calls another through the var
  ([kb] (clashes/with-grounds kb (clashes/ranked (clashes/contradictions-of kb))))
  ([kb context]
   (clashes/with-grounds kb (clashes/ranked (contradictions-read kb context))))
  ([kb context opts]
   (let [rs (clashes/ranked (contradictions-read kb context))]
     (if (clash-grounds? opts "contradictions" #{:grounds?}) (clashes/with-grounds kb rs) rs))))

;; Classifying a dilemma is an opt-in solve producing *persistent* inert contexts:
;; `(do/label CxDilemma Into)` then `(do/classify Into)` (docs/solving.md).  Representing
;; dilemmas is separate and unconditional: `contradictions`, above.

(defn settle-stats
  "Instrumentation for the `exceptWhen` fixpoint in `settle`: `{:iterations n :passes n
  :histogram {n count}}`.  `:iterations` counts the passes of the last settle in which the
  blocked set moved (0 nothing blocked, 1 one pass sufficed, ≥2 the fixpoint iterated),
  `:passes` the total loop passes including the confirming one, and `:histogram` the
  distribution of `:iterations` over every settle since `reset-settle-stats!`
  (docs/exceptions.md)."
  [kb]
  @(reasoning/settle-stats kb))

(defn reset-settle-stats!
  "Clear the settle instrumentation, including the histogram."
  [kb]
  (reset! (reasoning/settle-stats kb) {:iterations 0 :passes 0 :histogram {}}) kb)

(defn caches
  "What this process is holding beside the stores: every derived structure the engine
  caches, ranked by entries.  One row apiece:

    {:cache :literal-matches :label \"Literal matches\" :scope :kb
     :entries 3841 :limit 4096 :unit \"literals\"
     :hits 91204 :misses 12038 :hit-rate 0.883 :counters :kb
     :recompute-ns 4210388811 :retired 0 :compared 0 :spurious 0 :evicted 0
     :clearable? true :note \"…\"}

  `:scope` and `:counters` are `:kb` for a cache hanging off this KB and `:process` for
  one every KB in the JVM shares.  A nil `:entries` is a cache that cannot be counted from
  outside; an `:error` on a row is a cache whose own read threw.  `clear-caches` empties
  the clearable ones (docs/caches.md)."
  [kb]
  (caches-impl/rows kb))

(defn clear-caches
  "Drop every cache that offers a clear, and say what went:
  `{:cleared [{:cache :label :entries}…] :entries total}`.  Not `!`: every entry is
  derived and no belief moves.  Scoped to `kb`.

  `opts` is `{:counters? true}`, off by default: it zeroes this KB's own tallies (listed
  under `:tallies-reset`) and the hit and miss counters of the `:process`-scoped caches,
  and the reply carries `:counters-reset`.  `caches`' `:clearable?` says which rows this
  touches, and a `:cleared` entry carrying `:error` is one whose clear threw."
  ([kb] (clear-caches kb nil))
  ([kb opts]
   (check-opts! :bound opts #{:counters?} "clear-caches")
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
  return the profile.  `1.0` restores the shipped bounds; below 1 shrinks the caches, above
  1 grows them.  A per-cache floor keeps a small scale from taking a cache below the point
  where it saves nothing.  Process-wide, as `set-log-level` is.  `VAELII_CACHE_SCALE` sets
  the starting value.  Refused when `x` is not a number or is below zero (`:type
  :unknown-option`)."
  [x]
  (when-not (and (number? x) (>= (double x) 0.0))
    (throw (ex-info (str "cache scale must be a number 0 or more, not " (pr-str x))
                    {:type :unknown-option :mismatch :bad-value :scale x})))
  (caches-impl/set-scale x))

(defn set-cache-limit
  "Override cache `id`'s bound with `n` regardless of the scale, or clear the override when
  `n` is nil, and return the profile.  `id` is a `:cache` keyword from `caches`, `n` a
  positive whole number.  Refused (`:unknown-option`) when `id` is not a keyword or `n` is
  neither nil nor a positive whole number, and for a cache no override moves (docs/caches.md).
  An `id` that names no registered cache is warned, not refused, and the override is
  recorded."
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
  caches, under the low mark it grows them back.  Returns nil.  `:kbs` is a thunk answering
  the live KBs whose per-KB caches the trim reaches.  Idempotent: a second call replaces the
  thunk and attaches no second listener.  Nothing attaches the guard at engine load.  `!`
  because it attaches to the process's collectors.  [docs/caches.md](docs/caches.md)"
  [{:keys [kbs] :as opts}]
  (check-opts! :bound opts #{:kbs} "install-memory-guard!")
  (caches-impl/install-memory-guard! {:kbs kbs})
  nil)

(defn switch-value
  "The value of the build switch spelled `spelling`, a `VAELII_*` environment variable or a
  `vaelii.*` system property, read against its domain now, as `open-kb`'s check reads it.
  A value outside the domain is refused (`:unknown-option`, `:mismatch :bad-value`), as is
  a name the build reads no switch under (`:mismatch :unknown-key`); either names the
  switch under `:switch` and the older key under `:property`.  The table is
  `vaelii.impl.config/switches`, tabulated in [docs/operations.md](docs/operations.md)."
  [spelling]
  (if-let [row (first (filter #(some #{spelling} (:names %)) config/switches))]
    ((:reader row))
    (throw (ex-info (str (pr-str spelling) " is not a switch this build reads")
                    {:type :unknown-option :mismatch :unknown-key :switch spelling :property spelling
                     :options (vec config/switch-names)}))))

(defn violations
  "The ledger of definitional constraints a derived conclusion would have broken during
  forward chaining, and what a bounded pass did not reach: a vector of
  `{:violation <kind> :sentence S :context C :rule handle :run n :detail {…}}`.  Read
  `:sentence` and `:context` with `when-let`: an entry about a term, pair, budget, network
  or antecedent names no dropped sentence.  The ledger keeps the newest 1000;
  `clear-violations!` empties it, except the `:forced-conclusion`, `:inert-argument` and
  `:inert-rule` entries, which are read off stored state at each call.  Every kind and its
  `:detail` keys: docs/api.md, \"The `violations` ledger\"."
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
  types some context can see as disjoint, where each membership was admissible where it was
  written.  Entries are in `violations`' shape (`{:violation :disjoint :detail {:term :held
  :visible-from :message}}`), computed on demand and not filed.  `settle` files none: a
  pair a reader sees whole is decided there and answered by `contradictions` or
  `conflicts`.  Reads only."
  [kb]
  (clashes/exposed-clashes kb))

(defn specified-violations
  "The audit result for one binary `(predAllSpecified pred indep)` requirement in `context`:
  `{:status :audited :violations #{x…}}`, every member x of `indep` that `context` audits
  (it sees an ordinary defining home of x, or none is stored) with no believed `(pred x y)`
  whose **determinate** filler y satisfies `pred`'s derived slot contract, or a `{:status
  :gap …}` (`:missing-slot-typing`, or `:incomplete-defining-contexts` naming unclassified
  support).  A proved skeletal-only instance is exempt.  `arg-pos` selects the twin:
  `:second` (the default) is `predAllSpecified`; `:first` is `predSpecifiedAll`.
  Computed on demand and not filed (docs/predall.md)."
  ([kb pred indep context] (specified-violations kb pred indep context :second))
  ([kb pred indep context arg-pos]
   (predall/specified-violations kb pred indep context arg-pos)))

(defn all-specified-violations
  "Audit every binary `predAllSpecified` and `predSpecifiedAll` declaration visible in
  `context`, each stored one in every known reader seeing its GAF and an ordinary defining
  home, and every *Exists* declaration (`exists-violations`, keyed `[functor pred a b]`),
  and return `{[functor pred indep] result…}`, each result `{:status :audited :violations
  #{…}}` or a `{:status :gap …}` diagnostic (`:missing-slot-typing`,
  `:incomplete-defining-contexts`, or `:legacy-ternary-declaration` keyed by its whole
  argument tuple).  Declarations that hold are omitted and gaps never are, so an empty map
  is a clean sweep.  `kb-integrity` consumes the same per-declaration audit stream."
  [kb context]
  (predall/all-specified-violations kb context))

(defn exists-violations
  "The audit result for one *Exists* declaration in `context`, `{:status :audited
  :violations #{x…}}`: for `(predAllExists pred indep dep)` each member x of `indep` with no
  believed `(pred x y)` whose y is a member of `dep`; for `(predExistsAll pred dep indep)`
  each member x of `indep` with no believed `(pred y x)` whose y is a member of `dep`; for
  `(predExistsInstance pred indep fixed)` and `(predInstanceExists pred fixed dep)` the
  fixed term when no such tuple bears to it or from it.  Any member, an `indeterminate_term`
  included, is a filler.  Throws `:bad-args` for any other sentence.  Computed on demand and
  not filed ([predall.md](../docs/predall.md))."
  [kb declaration context]
  (predall/exists-violations kb declaration context))

(defn functional-at-instant-violations
  "The per-instant functionality clashes of one `(functional_at_instant f)` declaration in
  `context`, as a set of maps `{:function f :subject s :instant t :values #{v…} :kind k}`,
  one per moment `t` at which more than one distinct value of the fluent function `f` holds
  for one subject `s`.  `:kind` is `:merge` when the clashing values are all symbols and
  `:contradiction` otherwise.  Computed on demand and not filed; the candidate moments are
  the `time_point` members `ask` answers in `context` (docs/time.md, \"Functionality at an
  instant\")."
  [kb f context]
  (fluent/functional-at-instant-violations kb f context))

(defn all-functional-at-instant-violations
  "Audit every `(functional_at_instant f)` declaration visible in `context`, and return
  `{f #{violation…} …}` — declarations that clash nowhere are omitted, so an empty map is
  a clean sweep."
  [kb context]
  (fluent/all-functional-at-instant-violations kb context))

(defn kb-integrity
  "Run the bounded, read-only integrity sweep in `context`.  `candidate-terms` is a finite
  set of ground terms (`:bad-args` otherwise).  Answers `{:status :audited :candidate-count
  n}` when no pass finds anything, `:status :gap` with the non-empty finding categories, or
  `:status :truncated` with its `:reason`, the `:pass` it stopped in and the findings kept.
  Every answer carries `:work` and `:elapsed-ms`.  `options` takes `:max-work`, `:max-ms`,
  `:max-results`, and `:categories`, a set of category keys to run; the review-only
  categories run only when named. Finding keys and category contracts: docs/integrity.md.
  Stores nothing."
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
  "Per forward rule, what forward chaining did with it: how many firings it **placed**, how
  many it **refused** and why, or whether it did nothing.  `chain-stats` is the run's
  headline counters; this is the per-rule breakdown, `O(rules)`, off the rule index, the
  refusal ledger (re-decided against current belief) and the justification graph, so it
  reflects the KB as it is now.  Each row is `{:rule :sentence :believed? :placed :void
  :refused :refusals :status}`, `:void` the firings the forced-monotonic set holds void
  (`vaelii.impl.chain/rule-firing-report`).  The violations a firing files are read
  through `violations`, keyed by the same `:rule` handle."
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
  "Install the solver a labeling (docs/labeling.md) solves a dilemma's program with when no
  ASP backend is reachable, returning `kb`.  Takes a **name**:

    :stub  (the default) a deterministic local stub: greedy, one contradiction at a time
    :asp   the real answer-set backend: globally optimal, order-independent (docs/asp.md);
           native clingo, else the clasp subprocess, else the stub

  or any `vaelii.impl.types.solve/Solver` value."
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
  "Retract every **target-following meta-sentex** naming a handle that left the store,
  looping to a fixpoint, since a retracted meta is itself a sentex another meta may name.
  Reads the removal sink to learn what left.  A no-op unless the KB declares a
  `target_following_predicate`.  The engine's own `except` / `exceptWhen` metas carry no
  mark and are untouched."
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
  "The removal record `retract!` and `edit!` bind for their duration: every sentex that
  leaves the store while they run (`integrate/*removed-sink*`).  Built only when something
  reads one: a reified constant (`nat/any-reified-constants?`), a
  `target_following_predicate`, or a placed read (`exc/placed-reads?`).  Otherwise the presence check answers nil and nothing is
  collected."
  [kb]
  (integrate/removal-sink (or (nat/any-reified-constants? kb)
                              (seq (props kb :target-following))
                              (exc/placed-reads? kb))))

(defn- finish-teardown!
  "The four sweeps a teardown owes once its settle has run, run by both write entry points
  so a batch and a single retraction leave the same state:

  * the **meta cascade**: a `target_following_predicate` sentex must not outlive the
    sentex it names;
  * the **orphan sweep**: a reified constant no live use references any more;
  * the **structural-genlCx revival**: the edges the teardown's belief moves call for are
    rebuilt against the settled belief (docs/context-nat.md);
  * the **formula positions**: a rule holding a variable-functor application is held or
    released as the believed `formula` declarations read its positions, re-decided over
    `removed`, the facts the teardown removed (`nat-maint/reconcile-formula-positions`).

  The second and third run only beside a `sink`."
  [kb sink removed]
  (retract-following-metas! kb sink)
  (when sink
    (nat-maint/collect-orphans! kb sink retract!)
    (nat-maint/reconcile-revivals! kb sink))
  (nat-maint/reconcile-formula-positions kb removed))

(defn- rolled-back
  "The refusal an atomic batch rethrows once the KB is restored: the original `ex-data`
  plus `:rolled-back true` and `:in` / `:index` / `:entry` naming the batch line that
  raised it (`check-edit`'s vocabulary).  The original is the **cause**.  A `Throwable`
  without `ex-data` is rethrown as raised."
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

  An **inert** sentex (`assert-inert`) was never a TMS datum and is torn down directly,
  with no settle.  A stored premise the TMS has no node for is refused
  (`:unrecovered-premise`); see `retract-storage!`."
  [kb handle]
  (check-writable! kb "retract!")
  ;; A teardown settles more than once (revive, re-derive, settle again) and the orphan
  ;; sweep retracts inside it.  A feed event per settle would report a datum that went OUT
  ;; and revived as a removal then an addition, so the whole operation is one event
  ;; (`feed/with-one-event`).
  (feed/with-one-event kb
    ;; the sweeps below are scoped to what this teardown removed, so the removals are
    ;; recorded as they happen — the dependency sweep's, the settle's, and the sweeps' own
    (let [sink (teardown-sink kb)]
      (binding [integrate/*removed-sink*  sink
                observe/*write-record*    (settle/write-record kb)
                special/*producer-moves* (or special/*producer-moves* (special/producer-moves))]
        (let [handle (the-handle handle "retract!")
              _      (when-let [problem (or (checks/forcing-retraction-problem kb handle "retract!")
                                            (special/mint-rule-retraction-problem kb handle "retract!"))]
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
  `{:handles hs}` removes the unsupported records among `hs`; others are left.
  `{:force? true}` removes every record `unsupported` reports.  With neither, refused
  (`:unsupported-unattested`): this call deletes only what its caller attests.
  docs/storage.md."
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
    ;; The whole batch is held to `check-edit`'s answer before anything is applied, so a
    ;; refusal never leaves a half-applied batch: an entry's shape, then every `:remove`
    ;; handle (`:bad-handle` for a non-handle, `:unknown-handle` for an integer naming
    ;; nothing stored).
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
      ;; One removal record for the batch, for `retract!`'s reason: the orphan sweep asks
      ;; about the constants this batch stopped referencing.  Read **before** the adds: a
      ;; batch that declares the KB's first reifiable function sees false here and true at
      ;; the sweep, which leaves a nil sink and sends it down the whole-KB arm.
      (let [sink (teardown-sink kb)]
        (binding [integrate/*removed-sink*  sink
                  observe/*write-record*    (settle/write-record kb)
                  special/*producer-moves* (or special/*producer-moves* (special/producer-moves))]
          (let [audit    (atom {})
                mark     (volatile! nil)
                owed     (volatile! {})
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
                            chain/*rollback-scope* true
                            rules/*stratification-memo*
                            (or rules/*stratification-memo* (volatile! nil))
                            rules/*negated-keys-memo*
                            (or rules/*negated-keys-memo* (volatile! nil))
                            exc/*reader-states*
                            (or exc/*reader-states* (volatile! nil))
                            special/*owed-subsumption* owed]
                    ;; a shutdown may stop this phase, which the catch takes back whole
                    (dur/as-unit
                     (fn []
                       (let [added (into [] (map-indexed
                                             (fn [i entry]
                                               (vreset! at [:add i entry])
                                               (let [[sentence context opts] entry]
                                                 (assert kb sentence context (or opts {})))))
                                         add)]
                         (binding [special/*owed-subsumption* nil]
                           (doseq [[opts sentences] @owed]
                             (let [seeds (special/batch-subsumption-seeds kb sentences)]
                               (when (seq seeds) (chain/chain-all kb seeds opts)))))
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
                ;; **The committed phase.**  Nothing here refuses: the removals were cleared
                ;; above, and a fault from a settle or teardown sweep has no undo for a swept
                ;; record.  A shutdown's stop request is off here (`dur/as-unit` covers the
                ;; phase above only), and the caller's bound ends here.
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

  The final state equals running the asserts and retracts singly.  **All-or-nothing**: a
  refusal `check-edit` cannot see rolls the batch back at the handles it wrote; the handle
  counter stays moved.  Returns `{:added <one entry per add, `assert`-shaped> :removed
  {:removed-sentexes n :removed-justifications n}}`; `edit-with-consequences` adds the
  belief diff.  `opts` takes `edit-opt-keys`; `:max-ms` and `:stop?` bound the adds'
  chaining, and ending it before the first removal refuses the batch (`:interrupted`) and
  rolls it back.  docs/api.md, \"Contract notes: `edit!`\"."
  ;; `batch` is destructured in the body, not the parameter vector, as in `check-edit`: the
  ;; published `:arglists` is what a generated client reads to name the argument.
  ([kb batch] (apply-edit! kb batch))
  ([kb batch opts]
   (check-opts! :bound opts edit-opt-keys "edit!")
   (opts/check-values! opts "edit!")
   (chain/call-with-stop opts #(apply-edit! kb batch))))

(defn- snapshot-fact
  "`[sentence strength]` for `fact` of `context`'s `replace-facts!` snapshot: the literal
  under its `(set/monotonic …)` and `(ist Ctx …)` wrappers, and the strength `opts` and
  the wrapper request.  Refuses (`:shape`) a rule, a fact holding a variable, which the held
  set does not count, a fact `assert` stores outside `context`, and a fact naming a
  stored sentex by handle or by reference."
  [kb fact context opts]
  (let [[s c o] (loop [s fact, c context, o (select-keys opts [:strength])]
                  (let [[s o] (sx/peel-strength s o)]
                    (if-let [[c' s'] (entry/ist-parts s)] (recur s' c' o) [s c o])))
        placed  (stored-context kb s c)
        refusal (cond
                  (rules/rule-sentence? (rules/inner-rule s)) "is a rule"
                  (sx/some-symbol? sx/variable? s) "holds a variable"
                  (not= context placed) (str "is stored in " (pr-str placed))
                  (or (sx/names-a-handle? s) (seq (entry/references kb s c))) "names a stored sentex")]
    (when refusal
      (throw (ex-info (str "replace-facts!: " (pr-str fact) " " refusal "; the facts replaced are"
                           " the ground literals " context " stores that name no sentex")
                      {:type :shape :sentence fact :context context})))
    [s (:strength o :default)]))

(defn replace-facts!
  "Make `facts`, a seq of ground literals, the ground literal premises `context` stores that
  name no sentex, in one `edit!`: a fact not held so, or held weaker than requested, is
  added under `opts`' `assert` keys, and each such premise no fact names is retracted.
  `opts`' `edit-opt-keys` bound the edit.  A fact names the row `handle-of` finds, so either
  order of a symmetric literal names one.  A rule, a fact holding a variable, a fact stored
  outside `context` and a fact naming a sentex are refused (`:shape`).  Returns `{:added
  n :removed n :edit <edit!'s result>}`, `:added` counting the rows the adds name; equal
  sets write nothing and give `:edit nil` (docs/storage.md)."
  ([kb context facts] (replace-facts! kb context facts {}))
  ([kb context facts opts]
   (check-writable! kb "replace-facts!")
   (check-shape! (lookup-context-shape-problem context))
   (let [recs  (:records kb)
         held  (into {} (keep (fn [h]
                                (let [sx (p/get-sentex recs h)]
                                  (when (kb/replaceable-premise? kb h sx)
                                    [h (or (:strength sx) :default)]))))
                     (reads/as-stored-in-context (:index kb) context))
         named (volatile! #{})
         fopts (not-empty (apply dissoc opts edit-opt-keys))
         add   (into []
                     (comp (distinct)
                           (remove (fn [fact]
                                     (let [[_ strength] (snapshot-fact kb fact context opts)
                                           h            (handle-of kb fact context)]
                                       (when-let [stored (get held h)]
                                         (vswap! named conj h)
                                         (<= (strength/rank-of strength) (strength/rank-of stored))))))
                           (map #(cond-> [% context] fopts (conj fopts))))
                     facts)
         gone  (into [] (remove @named) (keys held))]
     (if (and (empty? add) (empty? gone))
       {:added 0 :removed 0 :edit nil}
       (let [edit (edit! kb {:add add :remove gone} (select-keys opts edit-opt-keys))]
         {:added (count (set (:added edit))) :removed (count gone) :edit edit})))))

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
  "Explain `handle`'s belief and visibility from `context` as a deterministic map:
  storage, raw JTMS IN, context-visible exception force, withdrawal from `context`,
  assertion-context inheritance, and the terminal answers `:believed?` / `:visible?`.
  `:exceptions` is in assertion-context and content order; nested meta-exceptions are under
  `:excepted-by`.  `:withdrawn?` is true when `context` reads the handle as withdrawn
  (`why-not` names the defeat).  Nil and unknown handles report absent storage and raw
  belief.  A malformed handle is refused (`:bad-handle`)."
  [kb handle context]
  (let [h       (the-handle handle "belief-status")
        stored  (when-some [h h] (p/get-sentex (:records kb) h))
        raw-in? (boolean (jtms/in? (reasoning/tms kb) h))
        {:keys [exceptions excepted?]} (exc/exception-status kb h context)
        ;; A directly excepted handle is answered by the forest above, and a scoped defeat
        ;; reads the scoped supporter entries alone.  Resting only on a withdrawn handle
        ;; holds for a non-premise only (a premise keeps its label in the region fixpoint),
        ;; so only that case asks the full per-reader withdrawal.
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
  elements: `:id` (the handle), `:context`, for a literal `:sentence`, and for a rule
  `:antecedent` / `:consequent` / `:engines` / `:defeasible` / `:effect` and no `:sentence`
  (`sentence-of` builds either one's sentence).  Key into it; the
  concrete `vaelii.impl.types.sentex/LiteralSentex` / `RuleSentex` record class is internal and not
  part of the contract.  nil (`handle-of` of an absent sentence) answers nil; a
  non-handle (a vector of handles included) is refused (`:bad-handle`)."
  [kb handle]
  (when-some [h (the-handle handle "sentex")]
    (p/get-sentex (:records kb) h)))

(defn canonical-sentex
  "The canonical sentex for `sentence` in `context`, **without storing it**: the un-stored
  counterpart of `sentex`, built through the store's own constructor, so it is the form
  `assert` would key on (docs/canonicalization.md).  Same map shape as `sentex`
  (`:sentence` / `:context`) with no `:id`.  `(canonical-sentex kb S C)` digests to the same
  value on every KB that shares the taxonomy, so it is a content identity independent of a
  handle.  A ground reifiable NAT resolves to its stored constant, never minting, as
  `handle-of` does; an unminted NAT stays a compound (docs/nat.md, Read path)."
  [kb sentence context]
  (res/kb-sentex kb (or (nat-read/resolve-for-read kb sentence context true) sentence) context))

;; ---- content digests: a checksum of a stored sentex's content ---------------

(defn digest?
  "Is `x` a content digest string: `\"sha256:\"` then 64 lowercase hex characters?"
  [x]
  (digest/digest? x))

(defn digest
  "The **content digest** of a sentex: `\"sha256:\"` and the lowercase hex SHA-256 of its
  context, sign and canonical sentence (docs/storage.md, \"Content digests\").  Two KBs
  holding one sentex compute one digest for it, and a `(sentexHandle n)` inside the
  sentence digests as the record `n` names.  `(digest kb handle)` reads the stored record
  and answers nil when the handle names none.  `(digest kb sentence context)`
  canonicalizes through `canonical-sentex` and needs nothing stored.  A sentence holding a
  value the encoding does not cover (a map, a `Date`) is refused `:not-encodable`."
  ([kb handle]
   (when-some [h (the-handle handle "digest")]
     (digest/digest kb h)))
  ([kb sentence context]
   (let [csx (canonical-sentex kb sentence context)
         h   (when (some sx/sentex-handle? (tree-seq sequential? seq (sx/sentence-of csx)))
               (handle-of kb sentence context))]
     (if h (digest/digest kb h) (digest/unstored-digest kb csx)))))

(defn digests
  "`(mapv #(digest kb %) handles)`, digesting each record a chain of references names
  once.  `{:provenance? true}` digests each record's `:creator` and `:created` with its
  identity, so the digest changes when the provenance does."
  ([kb handles] (digests kb handles nil))
  ([kb handles opts]
   (opts/check! opts #{:provenance?} "digests" nil)
   (digest/digests kb handles (boolean (:provenance? opts)))))

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

(defn mint-rule-kind
  "The declaring kind (`arg`, `genlArg`, `resultArg`, …) whose mints are justified under
  the stored rule `s`, or nil for any other sentex.  Takes the record `sentex` answers.
  Neither engine runs such a rule: the engine computes the mints in code and names the
  rule in each mint's justification (docs/argtypes.md)."
  [s] (kv/mint-rule-kind s))

(defn defeat-class
  "The current defeat-class of a believed handle (:monotonic / :default), or nil when
  it is OUT — the effective strength of the belief after settling.  nil for a nil
  handle too; a non-handle is refused (`:bad-handle`)."
  [kb handle]
  (when-some [h (the-handle handle "defeat-class")]
    (jtms/defeat-class (reasoning/tms kb) h)))

(defn- in-content-order
  "`justifications` ordered by `kb/justification-content-key` through
  `nm/sort-by-content-key`, which builds the key once per justification and short-circuits
  below two.  Both matter here: the TMS lists every justification a rule licenses under the
  rule's node (`jtms/rests-on`), so `dependent-justifications` on a rule lists its whole
  firing history, and a derived fact usually rests on one justification."
  [kb justifications]
  (nm/sort-by-content-key (kb/justification-content-key kb) justifications))

(defn- justifications-by-content
  "The justifications `edge` (a TMS reader over a handle) returns, in content order.
  Empty for a nil handle; a non-handle is refused (`:bad-handle`)."
  [kb handle fname edge]
  (if-some [h (the-handle handle fname)]
    (in-content-order kb (keep #(justification kb %) (edge (reasoning/tms kb) h)))
    ()))

(defn supporting-justifications
  "Justifications that conclude `handle`, in **content** order (`kb/justification-content-key`),
  so one knowledge base answers identically whatever order it arrived in.  Empty for a nil
  handle; a non-handle is refused (`:bad-handle`).  docs/nmtms.md."
  [kb handle]
  (justifications-by-content kb handle "supporting-justifications" jtms/supports))

(defn dependent-justifications
  "Justifications that use `handle` as an antecedent, in content order as
  `supporting-justifications` is: what rests on it, as an impact analysis before a
  `retract!` asks.  A rule handle's dependents are every firing it licensed.  Empty for a
  nil handle; a non-handle is refused (`:bad-handle`)."
  [kb handle]
  (justifications-by-content kb handle "dependent-justifications" jtms/dependents))

(defn justification-verdicts
  "The verdict `context` reads on each justification of `handle`, as `{justification-id
  reason}`: `:supports` where every handle it rests on is believed there, else
  `:antecedent-out`, unless the network blocks it (`:blocked`, its rule's `exceptWhen`
  holds) or holds it void (`:void`), `context`'s forced-monotonic reading holds it void
  (`:void`), a guard defeat in force at `context` covers it (`:guard`, docs/naf.md), or it
  is a `nogood` justification of a placement `context` exempts (`:exempt`).  Belief here is
  `why`'s reading, with the excepts not applied.  Empty for a nil handle; a non-handle is
  refused (`:bad-handle`)."
  [kb handle context]
  (if-some [h (the-handle handle "justification-verdicts")]
    (exc/justification-verdicts kb h context)
    {}))

(defn blocked-justifications
  "The ids of the justifications the network currently holds **blocked**: a block their
  rule carries holds (a closed extent, a withdrawn `different`), so they confer nothing even
  with every antecedent IN (docs/exceptions.md).  The whole set is returned, one read per
  page of a proof tree, and the same answer behind the daemon.  Each settle replaces the
  set (`jtms/set-blocked`), so it is the state as of the last one, and it is empty where no
  rule carries an exception."
  [kb]
  (jtms/blocked (reasoning/tms kb)))

;; ---- describe: what the KB holds about one term ---------------------------
;; `describe` assembles its map by the term's `term-role`; the browser's term page renders
;; it (docs/web.md).  Every list is bounded and carries `:total`, `:exact?` and
;; `:sorted?`, since an imported ontology has `thing` with 110,128 subtypes.

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

(defn- annotations-on
  "The second arguments of the `(p term x)` sentexes visible from `context`, for each `p`
  of `preds`, distinct and in content order: a term's `comment` strings, or its example
  annotations."
  [kb preds term context]
  (->> (for [p preds sx (visible-matches kb (list p term '?x) context)] sx)
       (keep #(nth (:sentence %) 2 nil))
       distinct
       nm/by-print-key
       vec))

(defn- comments-on
  "The `(comment term \"…\")` strings visible from `context`, in content order — the KB's
  documentation of the term, stated in the KB's own representation."
  [kb term context]
  (annotations-on kb '[comment] term context))

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
  `tax/separating-partners` is the enumeration, the frame `disjoint?` is the membership
  test of; it covers `(disjoint a b)`, a shared `disjoint_metatype`, and a sibling under a
  `(sibling_disjoint C)` parent.  Belief and context scoping are the frame's.  It reads the
  index and not two pattern reads per supertype (4.3 ms against 0.014 ms for `dog`).  The
  result is filtered to the nodes of the genl hierarchy, so it is a subset of the closure
  `disjoint-line` builds out of it."
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

(defn- sibling-separation
  "The row for type `t`'s sibling `s` at `context`, read off
  `integrity/subsumption-reading` with `rd` (`instance-reads`), over the `genl` edges
  `context` sees: `:separation` is `:genl`
  or `:spec` where one is below the other, `:disjoint` where a separation reaches the pair,
  `:orthogonal` where an `orthogonal` declaration states the overlap, `:overlaps` where a
  shared instance or a shared subtype shows one, and `:missing` where nothing decides the
  pair.  An `:overlaps` row carries the reading's `:witness` and `:via`."
  [kb t s context rd]
  (let [{ss :statuses w :witness v :via} (integrity/subsumption-reading kb t s context rd true)
        sep (cond (or (:genl ss) (:coextensional ss)) :genl
                  (:spec ss)                          :spec
                  (:disjoint ss)                      :disjoint
                  (= :declared w)                     :orthogonal
                  w                                   :overlaps
                  :else                               :missing)]
    (cond-> {:term s :separation sep}
      (= :overlaps sep) (assoc :witness w :via v))))

(def ^:private arity-classes
  "The memberships `:arity-class` lists: the exact-arity classes and the variable-arity
  ones."
  (into sx/variable-arity-classes (keys sx/exact-arity-classes)))

(defn- definitional-block
  "The definitional block `handbook/06-definitional-block.md` names, for the term
  `described` (a `describe` answer of role `:type` or `:predicate`), as `{:part :value}`
  rows in the handbook's order.  A part the KB holds nothing for has the value `:missing`.
  `:kind` is the types asserted of the term (`types-of`) less the arity classes, which
  `:arity-class` lists.  `:siblings` is a row list of `sibling-separation` rows, one per
  type sharing a direct parent.  The handbook's links part (`seeAlso`, `termsRelated`)
  has no row."
  [kb {:keys [term role context] :as described} limit]
  (let [tx      (reasoning/taxonomy kb)
        part    (fn [k v] {:part k :value (if (or (nil? v) (and (coll? v) (empty? v))
                                                  (and (map? v) (zero? (:total v))))
                                            :missing v)})
        sibs    (fn []
                  (let [bt (bounded-terms
                            (disj (into #{} (mapcat #(tax/direct-specs tx % context))
                                        (tax/direct-genls tx term context))
                                  term)
                            limit)
                        rd (instance-reads kb context)]
                    {:part  :siblings
                     :value (-> (dissoc bt :terms)
                                (assoc :rows (mapv #(sibling-separation kb term % context rd)
                                                   (:terms bt))))}))
        asserted (set (types-of kb term context))
        kind    (part :kind (bounded-terms (remove arity-classes asserted) limit))
        aclass  (part :arity-class (bounded-terms (filter arity-classes asserted) limit))
        parents (part :parents (:genls-direct described))]
    (case role
      :type      [(part :comment (:comment described))
                  (part :positive-examples
                        (annotations-on kb '[positiveExampleComment positiveExample]
                                        term context))
                  (part :negative-examples
                        (annotations-on kb '[negativeExampleComment negativeExample]
                                        term context))
                  parents (sibs) kind aclass]
      :predicate [(part :comment (:comment described))
                  kind aclass
                  (part :arity (:arity described))
                  (part :arg-declarations (:arg-declarations described))
                  parents
                  (part :props (:props described))])))

(defn describe
  "Everything the KB holds about one term, as one map, keyed by the term's own role
  (`term-role`; stored content overrides it, `described-role`).  Four shapes carry `:term`,
  `:role`, `:context`, the KB's `:comment` strings and the closure lines `:genls`, `:specs`
  and `:disjoint`.  On top of that:

  | `:role` | also carries |
  |---|---|
  | `:predicate` | `:arity` (the exact length that binds it, nil where none binds or two do), `:arity-via`, `:arg-declarations`, `:props`, `:inverse`, `:extent-count`, and the grants `:closed-extent?` `:abducible?` `:modal?` `:decontextualized?` |
  | `:type` | `:predicates-for-type` (whose argument declarations admit it) and `:instance-count` |
  | `:individual` | `:types` (asserted, not supertypes) and `:predicates` with a count each |
  | `:context` | `:up` / `:down` (the `genlCx` ancestor sets), `:sentex-count`, `:computed-spec-of` for a reified NAT |

  A `:predicate` and a `:type` also carry `:definitional-block`, the
  `handbook/06-definitional-block.md` parts as `{:part :value}` rows, each `:missing`
  where the KB holds nothing.  Declarations and closures are read from `context`'s
  `genlCx` ancestor set; `?ctx`, the default, reads every context.

  Each list is `{:terms|:rows :total :exact? :sorted?}`: `:exact?` is false where `:total`
  is a bound, `:sorted?` false where the list is in closure order.  `:limit`
  (`default-describe-limit`) caps a list; `describe-opt-keys` is the key set.
  `:extent-count` and `:instance-count` are stored counts (`count-with-functor`'s contract),
  so they can exceed what `sentexes-matching` answers.  `props` and `has-prop?` answer the
  metadata `:props` leaves out.  docs/api.md."
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
         blocked #(assoc % :definitional-block (definitional-block kb % limit))
         base  {:term     term
                :role     role
                :context  context
                :comment  (comments-on kb term context)
                :genls    (bounded-terms (disj up term) limit)
                :specs    (bounded-terms (disj (specs kb term context) term) limit)
                ;; The **declared** edges beside the closures: one `genl` step, not
                ;; reflexive.  A reader wants what it was told (`dog` is a `mammal`); at
                ;; `thing` the closure is 110,128 names.  O(degree).
                :genls-direct (bounded-terms (tax/direct-genls tx term context) limit)
                :specs-direct (bounded-terms (tax/direct-specs tx term context) limit)
                :disjoint (disjoint-line kb context ptns limit)
                ;; Both readings, since they answer different questions.  `:disjoint` is
                ;; every type the separation reaches, which a membership check is against;
                ;; `:disjoint-maximal` is the types it was declared between, which a reader
                ;; asking "what is this NOT" can hold.
                :disjoint-maximal (bounded-terms (set ptns) limit)}]
     (case role
       :predicate
       (let [len (arity/relation-length kb term)]
         (blocked
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
                 :decontextualized? (has-prop? kb :decontextualized term context))))

       :type
       (blocked
        (assoc base
               :predicates-for-type (predicates-for-type kb term context limit)
               :instance-count      (count-with-functor kb term)))

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

(defn- content-namer
  "A fn from a handle of `kb` to its content name `(ist C S)`, `S` the stored sentence with
  each `(sentexHandle n)` in it named the same way, or nil for a handle naming no record.
  A record its own chain of references re-enters is named by its digest (`dg`)."
  [kb dg]
  (let [recs (:records kb)
        memo (volatile! {})]
    (letfn [(spell [seen x]
              (cond (sx/sentex-handle? x) (or (named seen (sx/handle-id x)) x)
                    (not (sequential? x)) x
                    (not-any? sx/sentex-handle? (tree-seq sequential? seq x)) x
                    (vector? x) (mapv #(spell seen %) x)
                    :else (apply list (map #(spell seen %) x))))
            (named [seen h]
              (cond (contains? seen h) (dg h)
                    (and (empty? seen) (contains? @memo h)) (@memo h)
                    :else (when-let [sx (p/get-sentex recs h)]
                            (let [n (list sx/ist-functor (:context sx)
                                          (spell (conj seen h) (sx/sentence-of sx)))]
                              (when (empty? seen) (vswap! memo assoc h n))
                              n))))]
      (fn [h] (named #{} h)))))

(defn- name-order
  "The content order of a content name: its sentence, then its context."
  [n]
  (if (seq? n) [(nth n 2) (second n)] [n]))

(def ^:private named-keys
  "The keys of a `why`, `why-not` or `argue` answer whose value is a handle or a collection of
  handles.  The content form names each handle, and re-sorts the collections under
  `sorted-named-keys` by `name-order`."
  #{:root :informant :rule :defeat :via :missing :handles :nogood :consequence :grounds
    :because :antecedents :defeats})

(def ^:private sorted-named-keys #{:because :antecedents :defeats :missing :grounds})

(defn- support-order
  "The content order of a content-form `:support` entry, `why`'s or `why-not`'s."
  [e]
  [(name-order (:informant e)) (mapv name-order (:because e)) (mapv name-order (:missing e))
   (:strength e) (:verdict e)])

(def ^:private entry-order
  "The content order of a content-form `:withdrawn-by` or `:contradicted-by` entry.  A
  conflict's entry has no `:sentence` or `:context`, and its `:defeat` orders it."
  (juxt :sentence :context :vantage :defeat))

(defn- content-form
  "`x`, an answer of `why`, `why-not` or `argue`, with no handle in it (docs/overlay.md,
  \"Two seats' explanations\"): a map's `:handle` becomes the record's `:digest` beside its
  stored `:sentence`, a handle under `named-keys` and a `(sentexHandle n)` anywhere become
  `content-namer`'s `(ist C S)`, a justification id is dropped, a rule beside its handle
  reads as stored, and `:support`, `:withdrawn-by` and `:contradicted-by` are re-sorted by
  content."
  [kb x]
  (let [dg       (digest/digester kb)
        named    (content-namer kb dg)
        stored   #(some-> (named %) (nth 2))
        handles? #(and (coll? %) (not (map? %)) (seq %) (every? integer? %))]
    (letfn [(value [k v]
              (cond (integer? v)  (named v)
                    (handles? v)  (cond (set? v)              (into #{} (map named) v)
                                        (sorted-named-keys k) (nm/sort-by-content-key name-order (map named v))
                                        :else                 (mapv named v))
                    :else         (form v)))
            (entry [m k v]
              (cond (and (= :nodes k) (map? v)) (assoc m k (into {} (map (fn [[h n]] [(named h) (form n)])) v))
                    (named-keys k)              (assoc m k (value k v))
                    :else                       (assoc m k (form v))))
            (node [m]
              (let [h (:handle m), r (:rule m), i (:informant m)]
                (cond-> (reduce-kv entry {} (cond-> (dissoc m :handle)
                                              (integer? (:justification m)) (dissoc :justification)
                                              (contains? m :antecedents)    (dissoc :id)))
                  (contains? m :handle)                           (assoc :digest (when (integer? h) (dg h)))
                  (and (integer? h) (stored h))                   (assoc :sentence (stored h))
                  (and (integer? i) (contains? m :rule))          (assoc :rule (stored i))
                  (and (integer? r) (contains? m :rule-sentence)) (assoc :rule-sentence (stored r))
                  (and (integer? r) (= :rule (:via m)))           (assoc :sentence (stored r))
                  (vector? (:support m)) (update :support #(nm/sort-by-content-key support-order %))
                  (:withdrawn-by m)      (update :withdrawn-by #(nm/sort-by-content-key entry-order %))
                  (:contradicted-by m)   (update :contradicted-by #(nm/sort-by-content-key entry-order %)))))
            (form [x]
              (cond (map? x)              (node x)
                    (sx/sentex-handle? x) (or (named (sx/handle-id x)) x)
                    (seq? x)              (apply list (map form x))
                    (coll? x)             (into (empty x) (map form) x)
                    :else                 x))]
      (form x))))

(defn why
  "Why does the KB believe `handle`?  The justification graph reachable from `handle`, as
  data:

    {:root h
     :nodes {h  {:handle h :sentence S :context C :believed? true :defeat-class :default
                 :premise? false
                 :support [{:justification jid :informant <rule handle or symbol>
                            :rule <the rule's sentence> :strength :monotonic
                            :verdict :supports :because [h1 h2 …]}]}
             h1 {…} h2 {…} …}}

  One node per reachable handle.  A premise is `:premise? true` with its `:strength` and no
  `:support`.  A derived node's `:support` is its justifications in content order.  Each
  `:verdict` is the reason the node's context reads on that justification; a believed node
  can list one a guard defeat (`:guard`) or an exception (`:blocked`) covers.  Belief is
  read at each node's own context.  A stored node not believed there is a leaf `{:believed?
  false}`; ask `why-not` (docs/nmtms.md).  An unknown handle (nil included) is a node
  `{:stored? false}`.  `{:content? true}` names every sentex by content (docs/overlay.md)."
  ([kb handle]
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
  ([kb handle opts]
   (opts/check! opts #{:content?} "why")
   (cond->> (why kb handle) (:content? opts) (content-form kb))))

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
             ;; Rewritten from the **sentex's own context**, the only context that
             ;; supersedes it (`special/migrate-into`), so the representative named is the
             ;; one that context elected.  The unscoped rewrite names the global election,
             ;; which diverges when a `rewriteOf` outside this context's ancestor set
             ;; re-elected the head (docs/equality.md).
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
;; `:nearest` runs a bounded backward search for the rule that came closest to concluding
;; an unstored sentence and the antecedents the KB lacks.  It is opt-in because `why-not`
;; is called in loops over conflict lists.

(def why-not-opt-keys
  "Every key `why-not`'s sentence arity reads.  `:nearest n` asks for the n rules that came
  closest and is the switch that runs a search at all; `:max-depth` and `:max-ms` are that
  search's bounds.  A key off the key set is refused (`:unknown-option`) — a misspelt
  `:nearset` would answer the ordinary `why-not` and read exactly like a goal no rule
  concludes.  `:content?` names every sentex by content, as `why`'s does."
  #{:nearest :max-depth :max-ms :content?})

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
  "A rule's antecedents, under the bindings the goal forces on its consequent, split into a
  set the KB satisfies **jointly** and the rest.  The antecedents are taken in the rule's
  canonical order, each joined onto the ones satisfied before it with `query` and no depth,
  so no rule expands.  One that joins goes to `:satisfied`, one that does not to `:missing`:
  the satisfied set holds under one binding of the variables the goal leaves open, and
  `:missing` is empty only when the whole body joins.  The set is maximal, not maximum.  An
  antecedent the registry refuses counts as missing rather than throwing.  The result is in
  the rule's own variable names (`readable-sentence`)."
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
  node-engine search.  Every dead frontier node carries the rewrite that produced it, so the
  rules that could have concluded the goal are what the frontier already holds.  For each,
  the goal is unified with the rule's consequent and the antecedents are judged under those
  bindings.  Ranked by satisfied antecedents, most first, ties broken on content (the rule's
  sentence, then what is missing, then the bindings), never on the rule's handle
  (docs/defenses.md)."
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
  "The handle of a sentex for `sentence` stored in a context `context` inherits from, or nil.
  `why-not`'s sentence arity asks it after probing `context` itself, so a sentence stored in
  a general context and read from a specific one is explained rather than reported
  `:not-stored`.  The most specific candidate answers: a candidate another candidate sees is
  dropped, and a tie is broken on content (`nm/print-key`)."
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
  `{:handle h :sentence S :context C :believed? false :reason <keyword> …}`, with one
  `:reason` per way a handle goes unbelieved (`:not-stored`, `:superseded`, `:defeated`,
  `:withdrawn`, `:inert`, `:forced-conclusion`, `:unsupported`, `:excepted`,
  `:closed-extent`).  A believed handle yields `{:believed? true}`.  A nil handle is
  `:not-stored`; a non-handle is refused (`:bad-handle`).  `(why-not kb sentence context)`
  takes an `(ist Ctx S)`; `{:nearest n}` adds the n closest rules for `:not-stored`
  (`why-not-opt-keys`).  docs/api.md, \"Contract notes: `why-not`\"."
  ([kb handle] (why-not-handle kb (the-handle handle "why-not")))
  ([kb sentence context]
   (let [[sentence context kb] (checked-ist-goal kb sentence context)
         ;; the stored spelling of a ground reifiable NAT is its constant, looked up where
         ;; `assert` stores it (`handle-of`)
         s (nat-read/maybe-reify-for-read kb sentence context true)
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
     (cond->> (if (and (number? n) (pos? (long n)) (= :not-stored (:reason base)))
                (merge base (nearest-misses kb (:sentence base) (:context base) (long n)
                                            (or (:max-depth opts) default-nearest-depth)
                                            (or (:max-ms opts) default-nearest-ms)))
                base)
       (:content? opts) (content-form kb)))))

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
  "What would this batch do to the KB, **without** leaving it done.  `batch` is `edit`'s
  shape, `{:add [[sentence context opts?] …] :remove [handle …]}`.  The adds are asserted,
  the removes suspended, belief settles once, the difference is read off, and every write
  is taken back.  Returns

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

  Each half is in content order, `:handle` is nil for content the batch created, `:reason`
  is `why-not`'s, and the standing dilemmas are subtracted from `:contradictions`.  A
  `:refused` line is skipped and the rest previewed.  `opts`: `:max-depth`,
  `:max-term-depth`, `:max-derivations`, `:max-results` (a positive integer capping each
  half; `:bounded?` reports a cut) and `:release-withheld?` (runs the release sweep,
  `:release-path :swept`).  A bad key, a bad cap and an unrecovered KB are refused
  (`:unknown-option`, `:unrecovered-kb`).  Under `oplog/replay!` it returns nil.
  docs/preview.md."
  ([kb batch] (preview kb batch nil))
  ([kb batch opts]
   ;; a batch `edit` refuses outright is refused here too
   (check-writable! kb "preview")
   (check-edit-batch! batch)
   (check-opts! :bound opts #{:max-depth :max-term-depth :max-derivations :max-results
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
  "`edit`, plus what the batch turned out to **mean**: the belief it added and took away, in
  `preview`'s entry shapes.  Returns `edit`'s `{:added :removed}` with `:believed-added`,
  `:believed-removed` and `:bounded?` merged in.  The removed half omits what the
  dependency-directed sweep deleted; `preview` names it.  `opts` takes `:max-results n` and
  `edit!`'s `edit-opt-keys`; an unknown key and a cap that is not a positive integer are
  refused (`:unknown-option`).  docs/preview.md, \"The other direction\"."
  ([kb batch] (edit-with-consequences! kb batch nil))
  ([kb batch opts]
   (check-opts! :bound opts (conj edit-opt-keys :max-results) "edit-with-consequences")
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
;; Delivery hangs off the settle (`settle/settle`'s tail, via `feed/deliver!`), not off
;; the store: a store event would announce content the KB does not believe.  Only a stored
;; sentex is a TMS datum, so an answer that exists only while a prover computes it (an
;; evaluable, an aggregate, `unknown`, an `arg` type inference, a `set/backwardRule`'s
;; conclusion) is never reported, and `watch` refuses a goal of that shape (docs/feed.md).

(defn- watch-match
  "The bindings `goal` takes on the sentex at `handle`, or nil when it does not answer.
  Matched with `res/match1`, the subsumption a rule antecedent gets: `(animal ?x)` is
  answered by a stored `(dog Muffet)` through the `genl` closure.  One cached closure lookup,
  so a mutation costs a filter over the region and not a query per listener.  Context-scoped
  on both halves: the sentex must sit in a context the watch's own can see, and the `genl`
  edges the subsumption walks are only those that context sees.  A variable context watches
  every context and binds to the one that answered, as `ask` does."
  [kb goal context handle]
  (when-let [sx (p/get-sentex (:records kb) handle)]
    (let [any? (sx/variable? context)]
      (when (or any? (sees? kb context (:context sx)))
        (when-let [b (res/match1 kb goal (sx/sentence-of sx) (when-not any? context))]
          (cond-> b any? (assoc context (:context sx))))))))

(defn- watch-goal-problem
  "Why `goal` cannot be answered from a moved region, or nil when it can.  Matching one
  against the region's entries would be wrong, not merely incomplete: a conjunction (the
  vector spelling and the `(and …)` one alike) joins against facts the batch never touched;
  an aggregate, a NAF literal and a `thereExists` are properties of a whole answer set, which
  a fact leaving belief can flip; an evaluable is computed, never stored; `ist` has the
  watch's own context argument; an `or` is a union of queries and a watch matches one entry
  against one goal."
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

(defn- watch-calculus-problem
  "Why `goal`, of either polarity, cannot be watched on `kb`, or nil: its predicate is one
  a registered calculus answers (`qkb/calculus-for`).  The calculus answers it off the
  network, which entails tuples no fact stores and answers nothing over a blocked node,
  so the region's stored facts are neither every answer nor only answers."
  [kb goal]
  (let [b (sx/underlying-body goal)]
    (when-let [c (and (sequential? b) (symbol? (first b)) (qkb/calculus-for kb (first b)))]
      (str "`" (first b) "` is answered by the " (name (:name c)) " network, which entails"
           " tuples no fact stores and answers none naming a node of an unsatisfiable"
           " component"))))

(defn- moved-entries
  "The `{:believed-added :believed-removed}` a listener receives, from two handle
  vectors, with `:defeats` when the delay `defeats` holds a report, and `:unsatisfiable`
  holding the `:qualitative-inconsistency` entries of the networks `added` made
  unsatisfiable (`qkb/fed-inconsistencies`).  A `delay`, because
  the entries are the expensive half — a supporting justification and a `why-not` apiece
  — and a KB whose only listeners are standing queries never wants them: those filter to
  their own matches first and render only those."
  [kb added removed defeats]
  (delay (let [unsat (qkb/fed-inconsistencies kb added)]
           (cond-> {:believed-added   (mapv #(preview-added-entry kb %) added)
                    :believed-removed (mapv #(preview-removed-entry kb %) removed)}
             (seq @defeats) (assoc :defeats @defeats)
             (seq unsat)    (assoc :unsatisfiable unsat)))))

(defn- watched-defeats
  "The `:defeat` reports of `defeats` a standing query on `goal` at `context` answers:
  `goal` matches the loser (`watch-match`), and `context` is a variable or sees a context
  the report is placed in, so the loser left belief there."
  [kb goal context defeats]
  (filterv (fn [{:keys [loser placed-in]}]
             (and (watch-match kb goal context (:handle loser))
                  (or (sx/variable? context) (some #(sees? kb context %) placed-in))))
           defeats))

(defn- notify-listener!
  "Hand one listener its share of an event.  A standing query gets only the entries its goal
  answers, each with the `:bindings` that answered, and is not called when none do; a plain
  listener gets the whole diff.  A listener that throws is logged and skipped, since the
  settle is already committed.  A `VirtualMachineError` is rethrown, and an
  `InterruptedException` sets the thread's interrupt flag again before it is logged and
  skipped (docs/feed.md)."
  [kb {:keys [f goal context token]} added removed entries defeats]
  (try
    (if goal
      (let [prepared (quasiquote/prepare-goal-for-read kb goal context)
            matched  (fn [handles build]
                       (into [] (keep (fn [h]
                                        (when-let [b (watch-match kb prepared context h)]
                                          (assoc (build kb h) :bindings b))))
                             handles))
            in       (matched added preview-added-entry)
            out      (matched removed preview-removed-entry)
            ds       (watched-defeats kb prepared context @defeats)]
        (when (or (seq in) (seq out) (seq ds))
          (f (cond-> {:believed-added in :believed-removed out}
               (seq ds) (assoc :defeats ds)))))
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
          (let [defeats (delay (clashes/defeats-placed kb added))
                entries (moved-entries kb added removed defeats)]
            ;; A listener's write settles, which would fold its region into the sink the
            ;; *original* caller bound, so `edit-with-consequences` would report it as a
            ;; consequence of the batch.  The sinks are closed for the duration.  A write a
            ;; listener makes marks the operation log unusable (`vaelii.impl.oplog`).
            (binding [settle/*touched-sink*    nil
                      settle/*touched-in-sink* nil
                      oplog/*listener?*        true]
              (doseq [l ls] (notify-listener! kb l added removed entries defeats)))))))))

(defn watch
  "Be told when belief moves, instead of asking again.  Two shapes, both returning a
  **token** for `unwatch`:

    (watch kb f)                  every belief change
    (watch kb goal context f)     a standing query: only what answers `goal`

  `f` is called with one argument, `{:believed-added [...] :believed-removed [...]}` in
  `preview`'s entry shapes, plus `:defeats` and, for a plain listener, `:unsatisfiable`
  (docs/feed.md).  A standing query's entries carry `:bindings` too, and `f` is not called
  when nothing its goal answers moved.  `context` scopes the goal up the `genlCx` ancestor
  set; `'?ctx` watches every context.

  One settle, one call: a batch under `with-deferred-settle` / `assert-many` / `edit`
  delivers one event.  `f` runs on the writing thread after the settle and may read and
  write; delivery gives up after 64 rounds with a warning, and a listener that throws is
  logged and skipped.  A goal whose answer is not a function of the region is refused
  (`:not-watchable`): a conjunction, an aggregate, `unknown`, `thereExists`, an evaluable,
  an `ist`, and either polarity of a predicate a registered calculus answers."
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
     (when-let [why (or (watch-goal-problem goal) (watch-calculus-problem kb goal))]
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
  `:error :warn :info :debug :trace`, quietest first; anything else is refused (`:type
  :unknown-option`).  Process-wide, since two KBs in one JVM share one `*log-fn*`; the
  daemon's op table does not carry it, and a daemon's level is the one its process started
  with (`VAELII_LOG_LEVEL`) or this call from its own REPL.  `log-level` reads it back."
  [level]
  (logging/set-level level))

;; ---- persistence / recovery ---------------------------------------------

;; (The taxonomy rebuild — `stored-declarations` and the per-functor replay — lives
;; in `vaelii.impl.special` now, as the `:rebuild` column of the special-predicate
;; table: it was the third hand-mirrored enumeration of the same functors, and the
;; table makes a rebuild arm that drifts from its integrate arm a load-time error.)

(defn recover
  "Rebuild the in-memory JTMS and taxonomy from the persistent stores.  Call after
  constructing a KB against an existing store, e.g. after a restart.  Derivation depths
  reset to 0 (they only bound future forward chaining).  The JTMS is rebuilt first, the
  taxonomy replays every stored special-predicate sentex and is then reconciled against
  belief, and belief is settled last (docs/taxonomy.md).  The orchestration lives in
  `vaelii.impl.recovery` (docs/namespaces.md, \"The layering\")."
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
  "Apply a batch of premise additions, premise removals and rule direction changes to the
  records of a KB **without belief**, and return what it did.  No belief read, sweep or
  settle runs; `settle-record-edits!` settles any number of batches with one rebuild.

    `:add`       — a seq of `[sentence context]`, ground `genl`, `sense` or `comment`
                   facts: a new one is stored as a premise with its postings, a stored
                   derived one gains the premise mark;
    `:remove`    — a seq of handles; a record a surviving justification concludes only
                   loses its premise mark;
    `:direction` — `{handle direction}` over stored derive rules.

  Returns `{:added n :present n :removed n :unpremised n :absent n :redirected n
  :justifications-removed n :seeds [h …]}`; the same batch run again completes a crashed
  one.  Refuses before writing: `:belief-built`, `:unrecovered-kb`, `:shape`,
  `:not-ground`, `:naming`, `:not-well-formed`, `:record-edit-unsupported`,
  `:unknown-option`, `:unknown-handle`, `:mint-rule`.  A `genl` cycle, a negation cycle
  and a disjointness or argument clash go unchecked: screen them with `check` while the KB
  has belief.  docs/storage.md, \"Editing the records of a KB without belief\"."
  [kb batch]
  (let [h #(the-handle % "edit-records!")]
    (record-edit/apply! kb (cond-> batch
                             (contains? batch :remove)
                             (update :remove #(into [] (map h) %))
                             (contains? batch :direction)
                             (update :direction #(into {} (map (fn [[k d]] [(h k) d])) %))))))

(defn settle-record-edits!
  "Settle what `edit-records!` batches left: build belief over the edited records (`reindex`
  when the index was never built, else `recover` when belief was not), delete the stored
  justifications resting on a record the store does not hold, sweep the consequence closure
  of their conclusions and of `:seeds` as a retraction does, re-chain the affected rules,
  and bring each seed that is a stored premise fact in as `assert` brings one in.  Unless
  `:arg-types? false`, `record-arg-types` then draws the argument-type mints a batch owes.

  `opts`: `:seeds`, the union of the batches' `:seeds`; `:arg-types?`, default true (when
  false, a pass a batch or the sweep owes stays owed, `arg-types-owed`); `:on-progress`,
  called with `{:phase :done :total}` as each step begins, `:phase` being `:reindex`,
  `:recover`, `:sweep` or `:arg-types`.  A throw from it is rethrown at the next phase
  boundary, and a second call finishes.  Returns `{:rebuilt :reindex|:recover|nil
  :unrooted n :removed-sentexes n :removed-justifications n :rules-chained n :rechained n
  :arrived n :arg-types {…}}`, or `:arg-types-owed? bool` in place of `:arg-types`.
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
  to, or nil when none runs: the state `write-hazards` reports as `{:stale-belief true}`.  A
  rebuild that threw stays reported, with `:failed`, until `recover` rebuilds belief on the
  calling thread.

    :step :of :label         the step running now (1-based), the step count, its phrase
    :failed                  after a throw: `{:at :class :message}`
    :started-at :elapsed-ms  when the rebuild began (epoch ms), and how long it has run
    :image                   the installed image's `:source` digest and `:written-at`, and
                             its `:recover` step timings when recorded
    :source                  the running build's source digest
    :expected-ms :fraction   the image's recorded recover total, and the share the steps
                             done so far took"
  [kb]
  (recovery/rebuild-progress kb))

(def ^:private store-state-keys
  "The keys `store-state` answers."
  #{:readable? :network? :believes? :recoverable?})

(defn store-state
  "What `kb`'s record store and belief network hold, as a map of booleans:

    :readable?     one stored record reads back as a sentex (true for an empty store); on
                   false the map adds `:thawed-keys`, the keys that record read back with
    :network?      the belief network holds a node for at least one handle
    :believes?     the belief network holds at least one IN node
    :recoverable?  the store holds a premise mark or a justification, which `recover`
                   rebuilds belief from

  `ks` names the keys to compute and defaults to all four; another key is refused
  (`:unknown-option`).  `:believes?` false over a non-empty store means every answer is
  empty; `recover` repairs it when `:recoverable?` is true, a reload when false."
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
  ;; ...and the inert rules' handles, which the wipe deleted: the table holds none
  (kb/forget-mint-rules! kb true)
  (kb/forget-lazy-rules! kb true)
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
  "Seal `kb`'s operation log (`open-kb`'s `:oplog?`): write the index image and the reasoning
  image, name them in `seal.nippy`, and start the log's next generation (docs/storage.md,
  \"The operation log\").  Returns `{:sealed true :generation g :watermark w :ms t}`, or
  `{:sealed false :reason r}` with nothing changed, `r` being `:not-applicable` (no log),
  `:in-operation`, `:settle-deferred` or `:settle-running`.  A KB whose images cannot be
  written answers that reason and marks the log unusable, so the next open rebuilds from
  the records.  A log that stopped on a failed write or fsync refuses with
  `:store-unusable`.  Call it from the thread that writes `kb`."
  [kb]
  (seal/seal! kb))

(defn close!
  "Release a durable KB's directory: flush and close the record store, drop it from the
  durability daemon, and **release the exclusive file lock**.  Returns the KB, which must not
  be used afterwards.  `clear!` destroys the content and leaves the store open; this keeps
  the content and lets go of the store.

  Two KBs opened over one directory share the stores, so closing either closes both.  On a
  `fork` it releases the fork's own directory, never the base's.  On a KB with no directory
  it releases only RAM, so it is safe in a `finally`.  It also drops the KB's
  process-registry state (an engine-allocated space, a disk-backed derived index, the
  matcher's alpha index, the nogood readers' memos) and every listener `watch` registered
  on this KB value.  An in-memory `:space` is released by `clear!`."
  [kb]
  (feed/unregister-all! kb)
  ;; The RAM caches first, for every backend, since they hold only RAM and releasing them
  ;; cannot fail the close of the durable half below: the incremental matcher's alpha
  ;; index, and the RAM derived index a disk-backed KB built.
  (rete/forget-kb! kb)
  (kb/release-index-space! (:index-space kb))
  (kb/release-engine-space! (:engine-space kb))
  ;; every step runs, and the first failure is rethrown after the last (`close-dir!`'s shape)
  (let [failures (into []
                       (keep #(try (%) nil (catch Throwable t t)))
                       [#(some-> (:dir kb) disk/close-dir!)
                        ;; after the directory's close, whose seal still appends to the oplog
                        #(some-> (:oplog kb) oplog/close-log!)
                        #(when (instance? java.io.Closeable (:records kb))
                           (.close ^java.io.Closeable (:records kb)))
                        ;; after the close-time image writes, which refill the memos with this KB
                        decide/drop-memos])]
    (when-first [t failures] (throw t)))
  kb)

(defn- rebase-writes
  "The write entry points a rebase of fork `kb` asserts and retracts through."
  [kb]
  {:assert!       (fn [s c o] (assert kb s c o))
   :assert-inert! (fn [s c] (assert-inert kb s c))
   :retract!      #(retract! kb %)
   :recover       recover
   :reindex       reindex})

(defn- finish-follow!
  "Run the rule firings the durable fork `kb` owes over the base records its reopen took in
  (`rebase/fire-arrivals!`).  A KB that refuses writes keeps them owed, and the next open
  that can write runs them."
  [kb]
  (when-let [hs (rebase/firings-owed kb)]
    (if-let [p (writable-problem kb "open-kb")]
      (trove/log! {:level :warn :id ::firings-owed
                   :msg   (str (:dir kb) " owes the rule firings over " (count hs) " base records"
                               " its reopen took in, and this KB refuses writes: " (:message p))})
      (rebase/fire-arrivals! kb hs))))

(defn- finish-pending-rebase!
  "Assert again the writes a rebase of the durable fork `kb` left in its directory when it
  stopped before asserting them (`rebase/finish-pending!`).  A KB that refuses writes keeps
  the marker, and the next open or rebase that can write finishes it."
  [kb]
  (when (rebase/pending? kb)
    (if-let [p (writable-problem kb "open-kb")]
      (trove/log! {:level :warn :id ::rebase-pending
                   :msg   (str (:dir kb) " holds the writes of a rebase that did not finish,"
                               " and this KB refuses writes: " (:message p))})
      (rebase/finish-pending! kb (rebase-writes kb)))))

(defn import!
  "Read an export dump from `dir` into the empty `kb`, the inverse of `export!`.  `opts`:
  `{:belief? true|:stored|false :report-every n :on-progress f :drop-principal? bool
  :reasoners :stored :rebase? bool :on-replayed f}`.  `:belief? true` (the default) lands
  the state a restart produces, `:stored` stores everything and leaves `recover` for
  later, `false` stores and indexes records only.  `:on-progress` is called every
  `:report-every` frames (default 500000) with `{:phase :done :total}`; under `:rebase?`,
  `:on-replayed` with each replayed premise's old record and new handle.  Refused: an
  unread key or value (`:unknown-option`); another reasoner set (`:reasoner-mismatch`).  A
  foreign dump needs its reader plugin; one refused for its content leaves `kb` empty.
  The summary: docs/api.md, \"Reading a dump back\"."
  ([kb dir] (import! kb dir {}))
  ([kb dir opts]
   (if (and (:rebase? opts) (rebase/fork? kb))
     (do (check-writable! kb "import!")
         (rebase/rebase! kb dir (dissoc opts :rebase? :on-replayed)
                         (assoc (rebase-writes kb) :on-replayed (:on-replayed opts))))
     (let [opts    (dissoc opts :rebase? :on-replayed)
           summary (io-import/import-dump kb dir opts)]
       ;; after the recover, where a caller's own `add-reasoner` call after an import lands
       (some->> (io-import/dump-reasoners kb (io-import/read-meta dir) dir opts)
                (kb/add-reasoners! kb))
       summary))))

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

  `opts`: `{:variant :records|:records+index :compression :gzip|:xz|:none :chunk-size n
  :provenance? bool :belief? bool :on-progress f}` (defaults `:records`, `:gzip`, 10000,
  true, true).  `:belief? true` also writes the reasoning image.  `:on-progress` is called
  with `{:phase :done :total}` at each chunk boundary; a callback that throws cancels,
  leaving a directory with no `meta.edn`, which is not loadable.  An unread key is refused
  (`:unknown-option`).  `dir` must be absent or empty, and no one may be writing `kb`.
  `!` although it destroys nothing here: it writes outside the process (docs/storage.md)."
  ([kb dir] (export/export! kb dir {}))
  ([kb dir opts] (export/export! kb dir opts)))

;; ---- the text KB: a KB as the format its ontology is authored in ---------
;; A dump is a KB's **state** and text is its **content**, so they are two entry points:
;; `export!`'s options (chunks, compression, provenance, index) mean nothing here, and the
;; way back is `assert`, since a text KB is **re-asserted**, not restored.

(defn export-text!
  "Write `kb`'s premises and inert sentexes as a **text KB**, one `<Context>.txt` per context,
  in the format `load-text!` reads, and return a summary:

      {:contexts n :sentences n :skipped n :files [\"CxUniverse.txt\" …]
       :bytes n :elapsed-ms n :dir \"…\"}

  `opts`: `{:context C}` writes that one context's file, `{:ancestor-set C}` writes `C` and
  every context it sees; with neither, every context holding a premise or an inert sentex.
  `{:delta? true}` on a fork writes the fork's own writes only and adds `:retractions` to
  the summary; on a non-fork it is refused.  An unread key is refused (`:unknown-option`).
  `dir` must be absent or empty.

  No derived sentex is written.  Each premise keeps its `:strength` (`:monotonic` as a
  `(set/monotonic S)` wrapper), each rule its `set/*Rule` wrappers and `exceptWhen`, and an
  inert sentex is `(set/inert S)`.  A KB without belief refuses (`:unrecovered-kb`) when it
  stores a sentex that is neither premise nor inert.  A handle at a reference position is
  `(ist Cx S)`, a delta adding its digest; `:skipped` counts the records with no text.
  `!` although it destroys nothing.  docs/kbs.md, docs/overlay.md, \"A delta\"."
  ([kb dir] (export-text! kb dir {}))
  ([kb dir opts]
   (let [opts (or opts {})]
     (if (and (map? opts) (:delta? opts))
       (do (when-not (rebase/fork? kb)
             (throw (ex-info (str "export-text! {:delta? true} writes a fork's own writes over"
                                  " its base, and this KB is no fork")
                             {:type :unknown-option :mismatch :conflict :option :delta?})))
           (assoc (text/write-kb! kb dir opts (rebase/own-records kb))
                  :retractions (count (rebase/removed-keys kb))))
       (text/write-kb! kb dir opts)))))

(defn load-text!
  "Read a **text KB** into `kb`, a directory of `Cx….txt` files or one such file, and return a
  summary:

      {:contexts n :sentences n :files [\"CxUniverse.txt\" …] :elapsed-ms n :path \"…\"}

  The inverse of `export-text!`, and the entry point `lein cli load` is.  The file name is
  the context, and a sentence for another context says so with `(ist Cx S)`.  Forms are read
  with `clojure.edn`, so a file never runs code.  Every form goes through the ordinary write
  path, and the KB need not be empty.  `(set/monotonic S)` asserts `S` known-true and
  `(set/inert S)` stores `S` through `assert-inert`.

  A directory is one order-insensitive pass: a refused form is retried until a round stores
  nothing more, then re-asserted without the catch so it throws its own error.  A
  reference `(ist Cx S)` resolves as `assert` resolves it.  A delta's digests are compared
  with those of the sentexes its references resolve to (`:canonical-mismatch`).
  `{:merge? true}` reads a delta (`export-text!`'s `:delta?`) into a KB holding content of
  its own: a refused form is reported as `:refused [{:form :context :type} …]`, not thrown
  (docs/overlay.md, \"A delta\").  `!` because it writes knowledge into the KB.  docs/kbs.md."
  ([kb source] (load-text! kb source nil))
  ([kb source opts]
   (opts/check! opts #{:merge?} "load-text!" nil)
   (check-writable! kb "load-text!")
   (let [t0      (System/nanoTime)
         merge?  (boolean (:merge? opts))
         refused (volatile! [])
         {:keys [files entries path]} (text/entries source)
         n       (text/load-entries!
                  (fn [sentence context o] (assert kb sentence context (or o {})))
                  (fn [sentence context] (assert-inert kb sentence context))
                  entries
                  (when merge?
                    (fn [[form context] e]
                      (vswap! refused conj {:form form :context context :type (:type (ex-data e))})))
                  (text/digest-check kb))]
     (cond-> {:contexts   (count (distinct (map second entries)))
              :sentences  n
              :files      files
              :elapsed-ms (long (/ (- (System/nanoTime) t0) 1000000))
              :path       path}
       merge? (assoc :refused @refused)))))

;; ---- kb-diff: what two KBs disagree about --------------------------------
;; Handles are allocated in assertion order, so a diff keyed on one would report a
;; reloaded KB as wholly changed.  The key is content: the canonical sentence, its context
;; and its strength, the key `assert` dedups on (docs/canonicalization.md, docs/defenses.md).

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

  Each side is a KB, or a **string** naming a text KB (a directory of `Cx….txt` files or one
  such file), read into an in-RAM KB of its own (`load-text!`) and closed before this
  returns.  `lein cli diff <a> <b>` compares two exports.

  | key | holds |
  |---|---|
  | `:added` | in `b` and not in `a` |
  | `:removed` | in `a` and not in `b` |
  | `:moved` | the same sentence at the same strength, in a different context |
  | `:belief-changed` | the same sentex on both sides, believed on one and not the other |

  An `:added` / `:removed` row is `{:sentence :context :strength :premise? :believed?}`, a
  `:belief-changed` row carries `:believed-in-a` / `:believed-in-b` instead of `:believed?`,
  and a `:moved` row reads `{:sentence :from :to :strength :premise?}`.  Rows are keyed on
  content, never on a handle, and every list is in content order.  Justifications,
  provenance and handles are not compared.  O(|a| + |b|)."
  [a b]
  (let [opened (volatile! [])]
    (try
      (diff-sides (diff-side opened a) (diff-side opened b))
      (finally (run! close! @opened)))))

;; ---- four-valued epistemic status --------------------------------------
;; `argue` reads both a sentence and its explicit negation and reports where belief
;; stands between them.  It is built entirely on `ask`/`query`/`why`, so it lives on the
;; public surface rather than under `impl`.

(defn- argue-results
  "Query results for `goal` in `context` — a seq of binding maps (an empty map for a
  ground goal), or nil if not provable.  Rules fire only with `:max-depth`.  A ground
  goal has one answer at most, so its search stops at the first."
  [kb goal context opts]
  (seq (cond
         (:max-depth opts)
         (query-capped kb goal context opts (when-not (sx/some-symbol? sx/variable? goal) 1))
         (:max-ms opts) (ask kb goal context (select-keys opts [:max-ms]))
         :else          (ask kb goal context))))

(defn- argue-justification
  "The `why` graph for `sentence` in `context` when it is stored and believed, else nil."
  [kb sentence context]
  (when-let [h (handle-of kb sentence context)]
    (when (in? kb h)
      (why kb h))))

(defn- answer-supports
  "The readings a `SupportingProver` reports for the ground `goal` at `context`, each a
  vector of `{:handle :sentence :context}` naming the sentexes one answer was read from,
  or nil when no answer names one.  Entries sort on their sentence and context, and
  readings on those keys (docs/inference.md, \"An answer no record holds\")."
  [kb goal context]
  (when-not (sx/some-symbol? sx/variable? goal)
    (let [node (memoize (fn [h] (let [s (p/get-sentex (:records kb) h)]
                                  {:handle h :sentence (readable-sentence s) :context (:context s)})))
          k    (fn [n] [(nm/print-key (:sentence n)) (nm/name-key (:context n))])
          rs   (into #{}
                     (keep (fn [[_ sup]]
                             (when (seq sup) (vec (nm/sort-by-content-key k compare (map node sup))))))
                     (provers/solve-goal-with-support kb goal context))]
      (not-empty (vec (nm/sort-by-content-key #(mapv k %) compare rs))))))

(defn- with-leaf-supports
  "The derivation `trees`, each `:leaf` node carrying `:supports` where `answer-supports`
  names some for its goal at `context`."
  [kb context trees]
  (mapv (fn node [n]
          (if (= :leaf (:via n))
            (if-let [s (answer-supports kb (:goal n) context)] (assoc n :supports s) n)
            (update n :because #(mapv node %))))
        trees))

(defn- argue-derivation
  "The search's own derivation of the ground `goal` in `context`, or nil; a pattern gets
  none, since it answers once per binding.  At a positive depth it is `query`'s
  `{:proof? true}` tree, off `results` when the caller asked for proofs, and a goal a
  prover answered is the one `:via :leaf` node the search took.  Below it no rule
  expands, and the tree is that one leaf when `answer-supports` names something for it.
  Each leaf carries what `answer-supports` names (`:supports`)."
  [kb goal context opts results]
  (when-not (sx/some-symbol? sx/variable? goal)
    (let [d (:max-depth opts)]
      (if (and (nat-int? d) (pos? (long d)))
        (some->> (if (:proof? opts)
                   (:proof (first results))
                   (:proof (first (query-capped kb goal context (assoc opts :proof? true) 1))))
                 (with-leaf-supports kb context))
        (when-let [s (answer-supports kb goal context)]
          [{:goal goal :via :leaf :supports s}])))))

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

(def argue-opt-keys
  "Every key `argue` reads: `query-opt-keys`, and `:content?`, which names every sentex in
  the answer by content as `why`'s does and orders `:for` and `:against` by their bindings."
  (conj query-opt-keys :content?))

(defn argue
  "Four-valued epistemic status of a ground assertion.  Queries both `asent` and its
  explicit negation `(not asent)` and returns a map:

      {:verdict     :true | :false | :unknown | :contradiction
       :for         <results for asent, when provable>
       :against     <results for (not asent), when provable>
       :for-why     <`why`'s graph for asent, when stored and believed>
       :against-why <`why`'s graph for (not asent), when stored and believed>
       :for-derivation     <the search's proof tree, or below a positive depth one leaf>
       :against-derivation <the same, for (not asent)>
       :defeated-by <the `:defeat` reports, `conflicts`' shape, of the placed nogoods
                    that defeat a stored asent at context>}

  A side carries at most one of `:for-why` and `:for-derivation`, and a derivation leaf a
  `SupportingProver` answered names the sentexes it was read from (`:supports`).  Without
  opts it uses `ask`; pass `{:max-depth N}` for rules to fire.  `opts` is
  `argue-opt-keys`; another key is refused (`:unknown-option`).  When both sides are
  provable the verdict is `:contradiction` unless a `:monotonic` justification beats a
  `:default` one (docs/nmtms.md, \"Observation beats expectation\")."
  ([kb asent context] (argue kb asent context nil))
  ([kb asent context opts]
   (opts/check! opts argue-opt-keys "argue"
                (str "An option nothing reads takes the default in silence, which here is"
                     " the no-rule-expansion read — a misspelt depth answers :unknown for"
                     " a sentence a rule derives."))
   (opts/check-values! opts "argue")
   (if (:content? opts)
     (let [r     (content-form kb (argue kb asent context (dissoc opts :content?)))
           order (fn [a] (vec (nm/sort-by-content-key first (:bindings a a))))]
       (cond-> r
         (:for r)     (update :for #(nm/sort-by-content-key order %))
         (:against r) (update :against #(nm/sort-by-content-key order %))))
     (let [neg       (list 'not asent)
           dl        (budget/deadline opts)
           for-r     (argue-results kb asent context (remaining-clock opts dl))
           against-r (argue-results kb neg context (remaining-clock opts dl))
           pos?      (boolean (seq for-r))
           neg?      (boolean (seq against-r))
           ;; the JTMS's answer: a stored, believed side only
           for-j     (argue-justification kb asent context)
           against-j (argue-justification kb neg context)
           ;; and the search's, for a side a rule answered rather than the store.  A
           ;; fallback rather than a second opinion: where the JTMS has a justification it
           ;; is the better answer, and asking for a tree nobody reads costs a whole query
           for-d     (when (and pos? (not for-j))
                       (argue-derivation kb asent context (remaining-clock opts dl) for-r))
           against-d (when (and neg? (not against-j))
                       (argue-derivation kb neg context (remaining-clock opts dl) against-r))
           defeats   (when-not pos? (not-empty (clashes/defeats-against kb asent context)))
           base      (cond-> {}
                       pos?      (assoc :for for-r)
                       neg?      (assoc :against against-r)
                       for-j     (assoc :for-why for-j)
                       against-j (assoc :against-why against-j)
                       for-d     (assoc :for-derivation for-d)
                       against-d (assoc :against-derivation against-d)
                       defeats   (assoc :defeated-by defeats))]
       (cond
         (and pos? (not neg?)) (assoc base :verdict :true)
         (or defeats (and neg? (not pos?))) (assoc base :verdict :false)
         (and (not pos?) (not neg?)) (assoc base :verdict :unknown)
         :else (if-let [resolved (argue-resolve-contradiction kb asent context)]
                 (assoc base :verdict resolved)
                 (assoc base :verdict :contradiction)))))))

;; ---- the operation log ----------------------------------------------------
;; Every public write entry point above is routed through `vaelii.impl.oplog/run-op`, so a
;; KB with an operation log records each outermost write as the call that made it.  An
;; entry point missing from `write-ops` is a write the log does not record.

(defn- op-inputs
  "What a frame records beyond an operation's arguments: the clock `:created` is read
  from, the creator, and the dynamic bindings that change what a write stores.  A frame
  inside a `with-deferred-settle` batch records the batch's id, and an `abduce` the token
  its scratch context is named by."
  [op]
  (cond-> {:clock                (*clock*)
           :creator              *creator*
           :bulk-load?           *bulk-load?*
           :write-unrecovered?   *write-unrecovered?*
           :defer-settle?        *defer-settle?*
           :defer-depths?        tax/*defer-depths?*
           :assertive-arg-types? argument/*assertive-arg-types?*
           :sweep?               settle/*sweep?*}
    *batch-id*     (assoc :batch *batch-id*)
    (= :abduce op) (assoc :token (abduce/new-token))))

(defn- replayed-batch-rejoins
  "The map a frame recorded with `inputs` owes its re-joins to: under
  `oplog/replay!`, the replay's map for the batch `(:batch inputs)` names, emptied when that
  batch is not the previous frame's, and nil for a frame outside a batch; else
  `chain/*batch-rejoins*`."
  [inputs]
  (if-let [v oplog/*replay-batch*]
    (let [[id m] @v]
      (cond (not (:defer-settle? inputs)) (do (vreset! v [nil (java.util.HashMap.)]) nil)
            (= id (:batch inputs))        m
            :else                         (let [m (java.util.HashMap.)]
                                            (vreset! v [(:batch inputs) m])
                                            m)))
    chain/*batch-rejoins*))

(defn- with-op-inputs
  "Run `thunk` with the bindings `inputs` records, or under the bindings in force when
  `inputs` is nil — which is how a write nested inside a recorded operation runs."
  [inputs thunk]
  (if (nil? inputs)
    (thunk)
    (binding [chain/*batch-rejoins*           (replayed-batch-rejoins inputs)
              *clock*                         (constantly (:clock inputs))
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
  to its end. Record-only edits leave belief unread; their later rebuild is observed."
  [op class g]
  (fn [kb & args]
    (binding [observe/*route-gain-sink* (if (:reasoning kb)
                                          (special/route-gain-sink kb)
                                          observe/*route-gain-sink*)]
      (let [write (fn [] (dur/call-as-write
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
                                  (throw e)))))))]
        (if (= op :edit-records)
          (write)
          (with-support-observer kb write))))))

(def ^:private write-ops
  "Every public write entry point, as `name -> [op class]`.  The classes are
  `vaelii.impl.oplog`'s: `:replay` is recorded, `:seal` and `:config` mark the log unusable.
  Keywords, not vars, so the source identity does not put every write entry point into the
  digest (`read-ops`); the writes that derive belief are roots of the digest by name
  (`vaelii.impl.source-identity/roots`)."
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
   :replace-facts!           [:replace-facts :replay]
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
                                 (fn [in]
                                   (binding [chain/*batch-rejoins*
                                             (replayed-batch-rejoins (assoc in :defer-settle? true))]
                                     (closing-settle kb in)))))))

;; ---- reads during a background rebuild's install ----------------------------
;; A KB opened with `:recover? :background` answers from an earlier build's reasoning image
;; while belief is rebuilt, and the install replaces the `Reasoning` value with one
;; `vreset!` (`vaelii.impl.recovery`).  Every read entry point in `read-ops` runs against
;; `kb/read-copy`, a copy holding the belief the read began with, so a public read and the
;; lazy seq it returns see one belief whole.

(defmacro ^:private read-copy-fn
  "A fn calling `g` under `kb/reading` with its own arguments, the first replaced by
  `kb/read-copy` of it.  Up to five arguments after the KB, `g` is called directly; beyond
  that, through `apply`."
  [g]
  (let [kb    (gensym "kb")
        fixed (for [n (range 6) :let [args (vec (repeatedly n #(gensym "a")))]]
                `([~kb ~@args] (kb/reading ~kb (~g (kb/read-copy ~kb) ~@args))))
        five  (vec (repeatedly 5 #(gensym "a")))
        more  (gensym "more")]
    `(fn ~@fixed
       ([~kb ~@five & ~more] (kb/reading ~kb (apply ~g (kb/read-copy ~kb) ~@five ~more))))))

(defn- on-read-copy
  "Read entry point `g`, run under `kb/reading` against `kb/read-copy` of its KB."
  [g]
  (read-copy-fn g))

(def ^:private read-ops
  "The names of every public read entry point whose first argument is a KB and that reads its
  belief, its derived state or its stores.  `background_rebuild_test` fails on a public fn
  taking a KB first that is in none of this set, `write-ops` and the test's list of the rest.
  Keywords, not vars, so the source identity (`vaelii.impl.source-identity`) does not put
  every read into the digest a reasoning image is written with."
  #{:all-functional-at-instant-violations :all-specified-violations :argue :ask
    :ask-within :ask? :belief-status :believed :believed? :blocked-justifications
    :canonical-sentex :chain-report :chain-stats :check :check-edit :common-genls :common-specs
    :compare-tacticians :conflicts :context-down :context-up :contexts :contexts-of
    :contradictions :count-in-context :count-with-arg :count-with-functor
    :defeat-class :defining-contexts :dependent-justifications :deprecated? :describe :digest :digests
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
