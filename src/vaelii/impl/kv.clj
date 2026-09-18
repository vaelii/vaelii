;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.kv
  "The key-value substrate the index rests on, and the one `IndexStore`
  implementation written over it.

  The index — the trie, the secondary roots, the rule predicate index, the exception
  re-check index, and the inverted term index — is *all* sets and counters keyed
  by structured vectors.  `KvIndexStore` encodes that structure once, in terms of a
  small `KvBackend` protocol; a backend is then just an adapter that says how a
  scalar, a counter, and a set live in some store.  An in-memory map
  (`vaelii.impl.memory`) and an on-disk WAL (`vaelii.impl.disk.kv`) are two such
  adapters; a SQL or overlay backend is another.

  ## The count-aware trie

  A sentex is indexed by its trie path.  Every node, identified by its path
  prefix, is exactly three keys:

    count-key  [:trie :count prefix]  ->  integer: how many sentexes live at the leaves
                                     under this prefix (selectivity without walking).
    set-key    [:trie :children prefix]  ->  a SET: the next possible token labels (the
                                     node's child edges).
    leaf-key   [:trie :handles prefix]  ->  a SET: the handles of the sentexes whose path
                                     ends exactly here.

  **Child edges and leaf handles are separate keys because the trie is ragged.**
  Paths differ in length with arity, so one sentex's *full* path can be a proper
  prefix of another's: `(rel A B)` in `CxCee` keys as `[rel A B CxCee]`,
  and `(rel A B CxCee X)` in `CxDee` keys as `[rel A B CxCee X
  CxDee]` — the first path is an interior node of the second.  Storing both
  handles and child tokens in one set therefore mixed them, and a caller could not
  tell them apart by type (a handle is an integer, and so is the token `1970`).  Two
  keys make the distinction structural: `lookup` reads only the leaf key at its
  terminus, so it can never return a token as a handle, and `children` reads only
  the child set, so `plan`'s fan-out divisor can never count a handle as a branch.

  Alongside the trie sit the secondary roots, the rule predicate index, the
  exception re-check index, and the inverted term index — all flat sets whose
  cardinality is their own size.  One more flat set, the **term roster**
  `[:term-roster]`, holds the term index's *names* rather than handles, so the
  vocabulary can be listed and counted in O(terms) instead of a walk over every record.

  Contract: lookup expects a *full* path (sentence tokens + a context slot; the
  context may itself be a variable).  A short pattern terminates on an interior
  node, whose leaf key is empty, so it yields nothing rather than that node's child
  labels dressed up as handles.

  ## The `KvBackend`

  Logical keys are structured vectors and set members are bare values; a backend
  turns those into whatever its store wants (an in-memory map uses them directly; the
  on-disk backend nippy-frames them into its log).  The required ops are
  `kv-batch` (the whole index write for one sentex lands as one unit — one batched
  write) and `kv-intersect` (the multi-column narrowing `sentexes-with-args` needs, one
  set intersection rather than N fetch-and-filter reads).  A batch op is a vector
  `[op key & args]` with `op` one of `:put`, `:delete`, `:increment`,
  `:decrement`, `:add-to-set`, `:remove-from-set`; `kv-batch`
  returns one reply per op in order (only `:increment`/`:decrement` replies — the post-op
  counter value — are read; the rest are placeholders that keep the vector aligned).

  **`kv-member?` is a membership test, not a fetch**, and it is its own op because on
  several backends those cost different orders.  `exception-rule?` is the gate
  `chain/rule-view-of` takes once per candidate rule per new datum, so answering it by
  materializing the roster and testing the result makes forward chaining a product of
  two KB-sized quantities.  A flat-map backend hands the stored set back by reference
  and hides the distinction entirely; a dense one holds the roster as an `IntPostings`,
  where 1e5 gate calls against a roster of 1,000 cost 15,926 ms built-then-tested
  against 87 ms on the flat map — so the op exists to let each backend answer with the
  probe it already has (a hash lookup, a binary search, a bitmap test)."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p
             :refer [ArgColumns arg-agnostic-count arg-agnostic-members
                     arg-scoped-intersect kv-batch kv-clear! kv-count kv-entries kv-get
                     kv-intersect kv-load kv-member? kv-members unknown-op!]]
            [vaelii.impl.sentex :as sx]))

(def index-layout-version
  "Which key shapes this build's index is written in.

  The key families below — `[:trie :count|:children|:handles prefix]`, the roots, the
  rule / exception indexes, the term index and the roster — *are* the index's portable
  form, so a dump of them is only readable by a build that agrees on them.  An index
  written in a layout this build does not use reads as **empty** rather than as wrong
  (a lookup finds no key and answers nothing), which is fail-safe and undiagnosable —
  so the layout is stated as a number and checked, rather than discovered by a KB that
  quietly stopped answering.

  **Bump it whenever a key shape changes**: a new family, a renamed tag, a different
  arity, or a different value type at an existing key.

  2 scopes the argument roots by predicate (`[:argument-root pred pos term]`) and adds
  the `[:argument-slot pos term]` roster that keeps the predicate-agnostic reads
  answerable."
  2)

(defn apply-op
  "Apply one `kv-batch` write op to map `m`, returning `[m' reply]`.  Only
  `:increment`/`:decrement` carry a meaningful reply (the post-op counter value); the
  rest reply nil.  `:remove-from-set` drops the key when the set empties, so an absent
  key and an empty set are indistinguishable — a set with no members does not exist.

  **The op semantics live here, with the protocol that names them, and not in the
  backends.**  Both map-shaped backends fold their writes through this — the in-memory
  one (`vaelii.impl.memory`) over its state map, the on-disk one
  (`vaelii.impl.disk.kv`) over the RAM half of its write-ahead log, where it is also
  what *replays* the log, since a WAL frame there is the write op itself rather than
  the resulting value.  Written twice, the two copies could answer one op differently,
  and the disk side is replay: a seventh op added to the live path and missed in the
  fold would be a write that applies once and never comes back.

  An unrecognized op goes to `unknown-op!`, which every adapter shares: a bulk load
  taking the transient path, a dense backend's own batch, a fork decorator's, and an
  ordinary write taking this one may not disagree about what an unreadable op is.

  `:decrement` floors at zero, per the `KvBackend` contract: these counters are
  cardinalities.  The floor is in every fold rather than in one of them, because the WAL
  replays through this and the live write went through a backend — a floor applied on
  only one side would make a reopened store disagree with the one that wrote it."
  [m [op k a]]
  (case op
    :put  [(assoc m k a) nil]
    :delete  [(dissoc m k) nil]
    :increment (let [v (inc (long (get m k 0)))] [(assoc m k v) v])
    :decrement (let [v (max 0 (dec (long (get m k 0))))] [(assoc m k v) v])
    :add-to-set [(update m k (fnil conj #{}) a) nil]
    :remove-from-set (let [s (disj (get m k) a)]
                       [(if (empty? s) (dissoc m k) (assoc m k s)) nil])
    (unknown-op! op)))

;; ---- logical keys -------------------------------------------------------
;; Structured vectors — a backend encodes them (used directly as map keys in memory;
;; nippy-framed on disk).  The trie node's three keys share the [:trie …] prefix and
;; differ only in the :count/:children/:handles tag; the roots and indexes take
;; their own tags.

(defn- count-key [prefix] [:trie :count prefix])
(defn- set-key   [prefix] [:trie :children prefix])
;; leaf handles live under their own key, never mixed into the child-token set —
;; see the ragged-path note in the namespace docstring.
(defn- leaf-key  [prefix] [:trie :handles prefix])

(defn- rule-ante-key   [pred] [:rule-index :antecedent pred])
(defn- rule-conseq-key [pred] [:rule-index :consequent pred])
;; exception re-check index — a predicate is a symbol and the roster key a keyword,
;; so `[:exception-index :rules]` can never collide with a predicate's own key.
(defn- exception-pred-key  [pred] [:exception-index pred])
(defn- exception-rules-key []     [:exception-index :rules])

;; secondary roots — the trie is ordered [pred args… ctx], so it narrows only
;; left-to-right: it can count "predicate P" but not "context C" (the deepest level)
;; nor "X in argument position 2" without fixing everything to its left.  These
;; single-level roots fill that in; cardinality is the set's own size.
(defn- ctx-key  [c]     [:context-root c])
(defn- pred-key [p]     [:functor-root p])
;; canonicalize the term so a compound query term (a reader-literal list) hits the
;; same key as the stored subterm (built by canon); see sentex/canon.
(defn- arg-key  [pred pos t] [:argument-root pred pos (sx/canon t)])
;; The argument roots are scoped by predicate, so a probe of `(P ?x B)` reads exactly
;; P's facts with B at that position instead of every functor's, which the caller then
;; had to filter by instantiating each candidate.  The slot roster below is what keeps
;; the predicate-AGNOSTIC public reads (`sentexes-with-arg` / `count-with-arg`) answerable
;; without a second copy of the postings: it holds the predicates present at a slot, so
;; the coarse read is a union over a handful of keys rather than one wide bucket.
(defn- slot-key [pos t]      [:argument-slot pos (sx/canon t)])
;; public: the columnar index (vaelii.impl.columnar) emits the same term/root keys into
;; a shared backend for the non-trie families, so both stores key identically.
(defn term-key [term]  [:term-index (sx/canon term)])
;; the term roster — ONE set holding every name the term index is keyed by, so the
;; vocabulary is listable and countable without walking the records.  Its own key
;; family, because its members are terms rather than handles: a backend that packs the
;; handle families into int postings routes `[:term-roster]` to its ordinary set storage.
(def ^:private roster-key [:term-roster])

(extend-protocol ArgColumns
  Object
  ;; the flat-map reading of the family: a scoped read is one vector-keyed set fetch, a
  ;; multi-column read one intersection, and an agnostic read a union/sum over the slot
  ;; roster's predicates.  `arg-key` canonicalizes the term exactly as the stored key is.
  (arg-scoped-members [b pred pos term] (kv-members b (arg-key pred pos term)))
  (arg-scoped-intersect [b pred pos-terms]
    (let [ks (mapv (fn [[pos term]] (arg-key pred pos term)) pos-terms)]
      (if (= 1 (count ks)) (kv-members b (nth ks 0)) (kv-intersect b ks))))
  (arg-agnostic-members [b pos term]
    (let [preds (kv-members b (slot-key pos term))]
      (case (count preds)
        0 #{}
        1 (kv-members b (arg-key (first preds) pos term))
        (reduce (fn [acc pd] (into acc (kv-members b (arg-key pd pos term)))) #{} preds))))
  (arg-agnostic-count [b pos term]
    (reduce (fn [n pd] (+ (long n) (long (kv-count b (arg-key pd pos term)))))
            0 (kv-members b (slot-key pos term)))))

(defn root-keys
  "The secondary-root keys a sentex belongs to: its context always, plus — for a
  *fact* — its functor and each indexable top-level argument by 1-based position.
  A negative fact roots under its positive body's functor (polarity lives in the
  record), so `sentexes-with-functor` covers both polarities.  A rule contributes
  only its context; its predicates live in the rule index instead."
  [sentex]
  (let [b (sx/body sentex)]
    (cond-> [(ctx-key (:context sentex))]
      (and (sequential? b) (seq b) (symbol? (first b)))
      (into (let [pred (first b)]
              (cons (pred-key pred)
                    (keep-indexed (fn [i a]
                                    (when (sx/indexable-term? a) (arg-key pred (inc i) a)))
                                  (rest b))))))))

(defn sentex-terms
  "The distinct terms that make a sentex findable: its indexable content terms (see
  sentex/index-terms — connective-free, no numbers/strings/variables) plus its
  context."
  [sentex]
  (conj (sx/index-terms sentex) (:context sentex)))

;; ---- the term roster ----------------------------------------------------
;; Membership is *derived from the postings*, never counted separately: a name enters
;; the roster when the first sentex to mention it is indexed (its `[:term-index term]` posting
;; is empty) and leaves when the last one is unindexed (its posting is exactly that
;; handle).  Both are decided from the pre-write state, so each stays one extra read per
;; name and the index write remains a single batch.  Only *symbols* are rostered: a
;; ground compound keys the term index too, but it is a sentence fragment, not a name.

(defn roster-adds
  "The write ops entering `terms` (one sentex's, from `sentex-terms`) in the roster —
  read BEFORE their postings are written, so a name is entered exactly by the first
  sentex to mention it."
  [backend terms]
  (into [] (comp (filter symbol?)
                 (remove (fn [t] (pos? (long (kv-count backend (term-key t))))))
                 (map (fn [t] [:add-to-set roster-key t])))
        terms))

(defn roster-retires
  "The write ops retiring the names in `terms` that `handle` is the last mention of —
  read BEFORE their postings are removed, so a name dies exactly when its posting is
  `#{handle}`."
  [backend terms handle]
  (into [] (comp (filter symbol?)
                 (filter (fn [t]
                           (let [k (term-key t)]
                             (and (= 1 (long (kv-count backend k)))
                                  (contains? (kv-members backend k) handle)))))
                 (map (fn [t] [:remove-from-set roster-key t])))
        terms))

;; ---- the argument-slot roster --------------------------------------------
;; The predicate-scoped argument roots answer `(P ?x B)` directly, but they cannot
;; answer the predicate-AGNOSTIC public reads (`sentexes-with-arg` / `count-with-arg`,
;; which `settle` uses for functional-predicate clash detection and the planner for
;; selectivity).  Rather than keep a second copy of every posting, this roster holds the
;; *predicates* present at a slot, so the coarse read is a union over a handful of keys.
;; Membership is reference-counted off the postings exactly as the term roster's is: a
;; predicate enters when its first fact at that slot is indexed and leaves when the last
;; one is unindexed.

(defn arg-slots
  "`[[pred pos term] ...]` - the predicate-scoped argument roots a fact contributes.
  Empty for a rule and for a non-fact, matching `root-keys`."
  [sentex]
  (let [b (sx/body sentex)]
    (if (and (sequential? b) (seq b) (symbol? (first b)))
      (let [pred (first b)]
        (into [] (keep-indexed (fn [i a] (when (sx/indexable-term? a) [pred (inc i) a])))
              (rest b)))
      [])))

(defn slot-adds
  "Write ops entering a sentex's predicates in their slots - read BEFORE the postings
  are written, so a predicate is entered exactly by its first fact at that slot."
  [backend sentex]
  (into [] (comp (remove (fn [[pred pos t]]
                           (pos? (long (kv-count backend (arg-key pred pos t))))))
                 (map (fn [[pred pos t]] [:add-to-set (slot-key pos t) pred])))
        (arg-slots sentex)))

(defn slot-retires
  "Write ops retiring the predicates `handle` is the last fact of at their slots - read
  BEFORE the postings are removed, so a predicate dies exactly when its posting is
  `#{handle}`."
  [backend sentex handle]
  (into [] (comp (filter (fn [[pred pos t]]
                           (let [k (arg-key pred pos t)]
                             (and (= 1 (long (kv-count backend k)))
                                  (contains? (kv-members backend k) handle)))))
                 (map (fn [[pred pos t]] [:remove-from-set (slot-key pos t) pred])))
        (arg-slots sentex)))

(defn- ->count
  "A trie counter as a long.  The `Long/parseLong` arm is for a backend that replies
  in bytes; both in-memory backends store a boxed `Long` (`memory.clj`, `dense_kv.clj`),
  and routing those through `(str)` and back allocated a String per counter read on the
  default index — once per ground pattern token per frontier node, so on the path of
  every `find-sentex-handle` and every `prefix-estimate` step of the planner."
  [reply]
  (cond
    (nil? reply)    0
    (number? reply) (long reply)
    :else           (Long/parseLong (str reply))))
(defn- count-at* [backend prefix] (->count (kv-get backend (count-key prefix))))

(def sealed-prefix
  "The count prefix of the batch-seal counter: incremented as the **last** op of every
  `index-sentex` batch and decremented as the last op of an unindex's cleanup batch,
  so it equals the indexed-sentex count exactly when every batch landed whole.  The
  durable open's coverage gate compares it against the record count: the WAL logs one
  frame per op, so a torn tail keeps a batch's *prefix* — the root counter `count-at
  []` reads is op 0 and survives every tear, which is what makes it the wrong
  instrument — while this counter is the op a tear loses first.  A namespaced keyword,
  so it collides with no term path; only the count key is written, so no trie walk
  ever meets it.  Zero on a store whose index arrived by `index-load` replay or was
  written before the counter existed — the gate falls back to the root count there."
  [::sealed])

(def ^:dynamic *arg-point-cache*
  "An OPTIONAL point-query memo for the predicate-agnostic argument reads
  (`sentexes-with-arg` / `count-with-arg`): an atom holding `{[:m pos term] members}` and
  `{[:c pos term] count}`, or **nil (the default) for no memo**.

  It exists to answer one question the belief-settle sweep raised: does memoizing the
  `could-clash?` / `pairable?` point reads pay?  It does not, for the sweep.  The sweep is
  a one-shot pass over its region that reads each `(pos, term)` about once, so the memo
  pays a hash and a growing map for hits that rarely land — and, decisively, it is
  **unsound across a write**: the sweep settles belief as it reads, so a memo held over it
  can hand back a stale posting.  The sweep therefore MUST leave this nil (its default);
  bind it to a fresh atom only around a read-only burst that re-probes the same `(pos,
  term)` many times with no intervening index write.  Off, the check is one `nil?` branch
  on the read path — the reason it is a dynamic var and not a field."
  nil)

(defn- unindex-present!
  "Take `handle`, stored at the trie leaf of `pth` (`sx/path sentex`), out of every
  index family — the caller has established it is there (`unindex-sentex!`).  Two
  batches instead of a round trip per trie level: one to drop the leaf handle and
  decrement every level's counter, whose replies decide which nodes died; one to delete
  the dead nodes' keys, detach them from their parents, and clean the term index and
  roots."
  [backend sentex pth handle]
  (let [n        (count pth)
        terms    (sentex-terms sentex)
        roots    (root-keys sentex)                                ; derived from the sentex alone
        roster   (roster-retires backend terms handle)             ; reads the pre-write postings
        slots    (slot-retires backend sentex handle)              ; likewise
        prefixes (mapv #(subvec pth 0 %) (range n -1 -1))          ; leaf .. root
        replies  (kv-batch backend
                           (cons [:remove-from-set (leaf-key pth) handle]
                                 (map (fn [prefix] [:decrement (count-key prefix)]) prefixes)))
        dead     (keep (fn [[prefix c]] (when (<= (long c) 0) prefix))
                       (map vector prefixes (rest replies)))]
    (kv-batch backend
              (concat
               (mapcat (fn [prefix]
                         ;; the node is empty: drop its counter *and* both of its
                         ;; sets, or an orphaned [:trie :count prefix] leaves
                         ;; plan/prefix-estimate costing off a phantom count forever;
                         ;; then detach its edge from the parent's child set.
                         (cond-> [[:delete (count-key prefix)]
                                  [:delete (set-key prefix)]
                                  [:delete (leaf-key prefix)]]
                           (pos? (count prefix))
                           (conj [:remove-from-set (set-key (subvec pth 0 (dec (count prefix))))
                                  (nth pth (dec (count prefix)))])))
                       dead)
               (map (fn [t] [:remove-from-set (term-key t) handle]) terms)
               (map (fn [k] [:remove-from-set k handle]) roots)
               roster slots
               ;; the batch seal, last on purpose — `sealed-prefix` says why
               [[:decrement (count-key sealed-prefix)]]))
    ;; the mirror of the assert tally in `index-sentex`, and the reason it is a separate
    ;; one: `dead` is the only quantity here the sentex does not decide.  Every other
    ;; number is a property of what is being retracted; how many trie nodes empty
    ;; is a property of what is left behind it (`vaelii.impl.profile`).
    (when (prof/profiling?)
      (prof/record-index-retract sentex {:levels (inc n)
                                         :terms  (count terms)
                                         :roots  (count roots)
                                         :roster (count roster)
                                         :slots  (count slots)
                                         :dead   (count dead)}))
    handle))

(defrecord KvIndexStore [backend]
  p/IndexStore
  ;; One batch, not three round trips: the trie levels, the inverted term index, and
  ;; the secondary roots land together.  On the in-memory backends the batch applies
  ;; in one swap, so a reader never sees a sentex half-indexed.  Durability is
  ;; another matter: the disk WAL logs one frame per op (`disk/kv.clj`, `apply-ops!`),
  ;; so a crash mid-batch persists a *prefix* — e.g. an argument-root posting whose
  ;; predicate never entered the slot roster, which under-answers the
  ;; predicate-agnostic reads while the trie and the scoped reads see the fact.  The
  ;; record/index boundary remains; `vaelii.impl.reindex` is the repair for both.
  (index-sentex [_ sentex handle]
    (let [pth    (sx/path sentex)
          n      (count pth)
          terms  (sentex-terms sentex)
          roots  (root-keys sentex)                   ; derived from the sentex alone
          roster (roster-adds backend terms)          ; reads the pre-write postings
          slots  (slot-adds backend sentex)]          ; likewise, before any posting lands
      (kv-batch backend
                (concat
                 (mapcat (fn [i]
                           (let [prefix (subvec pth 0 i)]
                             [[:increment (count-key prefix)]
                              (if (< i n)
                                [:add-to-set (set-key prefix)  (nth pth i)]   ; child edge
                                [:add-to-set (leaf-key prefix) handle])]))    ; leaf handle
                         (range (inc n)))
                 (map (fn [t] [:add-to-set (term-key t) handle]) terms)
                 (map (fn [k] [:add-to-set k handle]) roots)
                 roster slots
                 ;; the batch seal, last on purpose — `sealed-prefix` says why
                 [[:increment (count-key sealed-prefix)]]))
      ;; what this assert cost the index, per family, when somebody is asking
      ;; (`vaelii.impl.profile`).  Guarded rather than passed unconditionally so the
      ;; counts map is built only while the instrument is on; off, this is a deref.
      (when (prof/profiling?)
        (prof/record-index-write sentex {:levels (inc n)
                                         :terms  (count terms)
                                         :roots  (count roots)
                                         :roster (count roster)
                                         :slots  (count slots)}))
      handle))

  ;; **Gated on the handle being at the leaf.**  The counters are decremented without
  ;; looking, and a node whose count reaches zero is deleted with every handle at its
  ;; leaf — so one stray unindex (a handle never indexed here, or indexed and already
  ;; removed) would take live nodes, and the sentexes stored under them, out of the
  ;; trie.  One membership probe on the leaf — a hash lookup on every backend, no
  ;; protocol read tallied — makes a stray unindex a no-op instead.
  ;;
  ;; **And says so**, because the no-op is safe and not therefore right.  The caller is
  ;; `integrate/sentex-removed!`, which deletes the record on the next line whether or
  ;; not anything came out of the index: a genuine record/index divergence therefore
  ;; leaves the trie handing out a handle whose record is gone, which is indistinguishable from a
  ;; corrupted store several operations later and nowhere near here.  Silence made that
  ;; indistinguishable from a caller retracting a handle twice.  `reindex` is the repair,
  ;; and the log is what tells somebody to run it.
  (unindex-sentex! [_ sentex handle]
    (let [pth (sx/path sentex)]
      (if (kv-member? backend (leaf-key pth) handle)
        (unindex-present! backend sentex pth handle)
        (trove/log! {:level :warn :id ::unindex-absent
                     :data {:handle handle :path pth :context (:context sentex)}})))
    handle)

  ;; Every read below tallies the **family** that answered it (`vaelii.impl.profile`),
  ;; one entry per protocol call: a deref and a `nil?` check when nobody is asking, and
  ;; the one measurement that says whether a family a KB pays to maintain is ever read.
  ;; What a call *cost* is a separate question — the trie's is the fan tally in `lookup`.
  ;;
  ;; The trie is two families to a reader even though it is one structure on disk, and
  ;; the split is the whole reason the tally is worth reading: these three are the
  ;; **cost model's** probes (`plan`'s selectivity and fan-out divisor), and `lookup`
  ;; below is **retrieval**.  A run that reads the counts a hundred times per walk is
  ;; using the trie to plan, not to fetch, and a family roster that added them together
  ;; would report that as one number meaning neither.
  (count-at [_ prefix] (prof/record-read :trie-counts) (count-at* backend prefix))

  (children [_ prefix] (prof/record-read :trie-counts) (vec (kv-members backend (set-key prefix))))
  ;; the set's cardinality, which every backend answers without building the set —
  ;; `children` above would materialize it into a vector for the same number
  (count-children [_ prefix] (prof/record-read :trie-counts) (kv-count backend (set-key prefix)))

  ;; The terminus reads the *leaf* key, so an under-long pattern — which stops on an
  ;; interior node — yields nothing instead of that node's child tokens, and a full
  ;; path that also happens to be interior (ragged arity) yields its own handles
  ;; without the child token sitting at the same prefix.
  ;;
  ;; **Structural walk.**  A positive-fact key linearizes nested compounds into arity
  ;; markers (see `vaelii.impl.sentex`), so a query token is one of three:
  ;;   * a variable — matches exactly one complete stored form.  If the child is an
  ;;     atom it advances one level; if the child is a marker it **skips** the whole
  ;;     subterm the marker's arity spans (`skip-one` / `skip-n`, recursing for nested
  ;;     arity).  This is what lets `(p ?y b)` bind a whole compound of unknown depth.
  ;;   * a marker `[::subterm k]` — matched exactly, like any token; the query's own
  ;;     next k linearized forms then match the subterm's elements.
  ;;   * anything else (an atom, or a whole list token in a `:false`/`:rule` key) —
  ;;     matched exactly by `count-at`.
  ;; Only child *sets* are read while walking; handles are read solely at the terminus,
  ;; so the skip can never cross into a leaf handle or read a marker as one.  This is a
  ;; superset filter — `res/unify` is the source of truth — and a markerless (flat)
  ;; key, holding no marker for the skip to read, walks one level per token.
  (lookup [_ pattern]
    (prof/record-read :trie-lookup)
    (letfn [(child-tokens [prefix] (kv-members backend (set-key prefix)))
            (skip-one [prefix]                         ; advance past one complete form
              (mapcat (fn [c]
                        (if (sx/subterm-mark? c)
                          (skip-n (conj prefix c) (sx/subterm-arity c))
                          [(conj prefix c)]))
                      (child-tokens prefix)))
            (skip-n [prefix n]                         ; advance past n complete forms
              (if (zero? n)
                [prefix]
                (mapcat #(skip-n % (dec n)) (skip-one prefix))))]
      ;; `visits` and `widest` describe the walk itself: one probe per frontier node per
      ;; level, and how wide the frontier ever got.  A narrowing walk holds the frontier
      ;; at one node and visits one per level; a walk that got stuck behind a variable
      ;; visits that level's whole child set, which is the fan the secondary roots exist
      ;; to avoid.  Two long ops per level whether or not anybody is counting; the tally
      ;; itself is a deref when the instrument is off.
      (loop [frontier [[]]                             ; node prefixes reached so far
             qs pattern
             visits 0
             widest 1]
        (if (empty? qs)
          (let [hs (into #{} (mapcat (fn [prefix] (kv-members backend (leaf-key prefix)))) frontier)]
            (prof/record-fan pattern (+ visits (count frontier)) widest (count hs))
            hs)
          (let [q (first qs)
                frontier'
                (into []
                      (mapcat
                       (fn [prefix]
                         (if (sx/variable? q)
                           (skip-one prefix)
                           (when (pos? (count-at* backend (conj prefix q)))
                             [(conj prefix q)]))))
                      frontier)]
            (recur frontier' (rest qs)
                   (+ visits (count frontier))
                   (max widest (count frontier'))))))))

  ;; The exact leaf — one hash read of the node the path names, no walk and no fan.
  ;; Tallied as retrieval like `lookup` beside it, because that is what it is; it records
  ;; no fan, having none to record.
  (leaf-at [_ path] (prof/record-read :trie-lookup) (kv-members backend (leaf-key (vec path))))

  (sentexes-in-context [_ context] (prof/record-read :context-root) (kv-members backend (ctx-key context)))
  (count-in-context    [_ context] (prof/record-read :context-root) (kv-count    backend (ctx-key context)))

  (sentexes-with-functor [_ pred] (prof/record-read :functor-root) (kv-members backend (pred-key pred)))
  (count-with-functor    [_ pred] (prof/record-read :functor-root) (kv-count    backend (pred-key pred)))

  ;; Predicate-agnostic reads, answered as a union over the slot roster's predicates.
  ;; One key in the overwhelmingly common case (a term occupies a given position under
  ;; one predicate); a handful otherwise. The single-predicate case never copies into a
  ;; union, and on the two set-backed backends it is allocation-free outright — the
  ;; stored set is handed straight back. The dense one still builds a set out of its
  ;; int posting, and a fork still merges; what the branch saves them is the union.
  (sentexes-with-arg [_ pos term]
    (prof/record-read :argument-slot)
    (prof/record-read :argument-root)
    (if-let [c *arg-point-cache*]
      (let [k [:m pos term]]
        (if-some [v (get @c k)] v (let [v (arg-agnostic-members backend pos term)]
                                    (swap! c assoc k v) v)))
      (arg-agnostic-members backend pos term)))
  (count-with-arg    [_ pos term]
    (prof/record-read :argument-slot)
    (prof/record-read :argument-root)
    (if-let [c *arg-point-cache*]
      (let [k [:c pos term]]
        (if-some [v (get @c k)] v (let [v (arg-agnostic-count backend pos term)]
                                    (swap! c assoc k v) v)))
      (arg-agnostic-count backend pos term)))

  ;; Multi-column narrowing. With the argument roots scoped by predicate, a named
  ;; functor needs NO functor-root intersection: `(rel ?x B C)` reads
  ;; [:argument-root rel 2 B] and [:argument-root rel 3 C] and intersects only those,
  ;; and a single bound argument is one hash lookup with nothing intersected at all.
  ;; A `nil` pred (a variable functor) has no scope to read, so it falls back to the
  ;; predicate-agnostic reads above and intersects those.
  ;; The result stays a superset of the positional-trie hits — it still does not
  ;; constrain numeric arguments or context — which the caller's `unify` filters exact.
  (sentexes-with-args [this pred pos-terms]
    (cond
      (nil? pred)
      (if (empty? pos-terms)
        #{}
        (reduce (fn [acc [pos term]]
                  (let [s (p/sentexes-with-arg this pos term)]
                    (if (nil? acc) s (set/intersection acc s))))
                nil pos-terms))
      (empty? pos-terms) (do (prof/record-read :functor-root) (kv-members backend (pred-key pred)))
      :else
      (do (prof/record-read :argument-root)
          (arg-scoped-intersect backend pred pos-terms))))

  ;; Both predicate sets are complete — every rule is registered under all of its
  ;; antecedent predicates and its consequent predicate, whatever its direction — so
  ;; "what could conclude P?" is answerable for forward-only rules too.  Direction is
  ;; not indexed: it is a field on the rule's own sentex, which chaining reads.
  (index-rule [_ handle ante-preds conseq-pred]
    (kv-batch backend
              (cond-> (mapv (fn [p] [:add-to-set (rule-ante-key p) handle]) ante-preds)
                conseq-pred (conj [:add-to-set (rule-conseq-key conseq-pred) handle])))
    nil)

  (unindex-rule! [_ handle ante-preds conseq-pred]
    (kv-batch backend
              (cond-> (mapv (fn [p] [:remove-from-set (rule-ante-key p) handle]) ante-preds)
                conseq-pred (conj [:remove-from-set (rule-conseq-key conseq-pred) handle])))
    nil)

  (rules-by-antecedent [_ pred] (prof/record-read :rule-index) (kv-members backend (rule-ante-key pred)))
  (rules-by-consequent [_ pred] (prof/record-read :rule-index) (kv-members backend (rule-conseq-key pred)))

  ;; The exception re-check index.  A rule carrying an `exceptWhen` is posted under
  ;; every predicate its exception query mentions, so asserting or retracting a fact on
  ;; that predicate finds the rules whose exception it could have flipped; and into the
  ;; `:rules` roster, which a genl/genlCx edge change re-checks wholesale (a
  ;; closure can flip an exception with no matching fact ever arriving).  Granularity
  ;; is the rule, never the firing; nothing here records whether an exception *holds*.
  (index-exception [_ handle preds]
    (kv-batch backend
              (conj (mapv (fn [p] [:add-to-set (exception-pred-key p) handle]) preds)
                    ;; unconditional: a rule with an exception belongs in the roster
                    ;; whatever its exception mentions, or the taxonomy trigger misses it.
                    [:add-to-set (exception-rules-key) handle]))
    nil)

  (unindex-exception! [_ handle preds]
    (kv-batch backend
              (conj (mapv (fn [p] [:remove-from-set (exception-pred-key p) handle]) preds)
                    [:remove-from-set (exception-rules-key) handle]))
    nil)

  (rules-with-exception-on [_ pred] (prof/record-read :exception-index)
    (kv-members backend (exception-pred-key pred)))
  (exception-rules [_] (prof/record-read :exception-index) (kv-members backend (exception-rules-key)))
  ;; the roster *probe*, not the roster: `kv-member?` so a backend that packs the family
  ;; into int postings tests membership rather than materializing every rule that carries
  ;; an exception, once per candidate rule per new datum
  (exception-rule? [_ handle] (prof/record-read :exception-index)
    (kv-member? backend (exception-rules-key) handle))

  (sentexes-with-term [_ term] (prof/record-read :term-index) (kv-members backend (term-key term)))
  (sentexes-with-terms [_ terms]
    (prof/record-read :term-index)
    (if (empty? terms) #{} (kv-intersect backend (mapv term-key terms))))

  ;; the roster reads: one set fetch and one size read, both O(distinct terms) at worst and
  ;; neither touching a record — the whole point of maintaining the roster.
  (terms      [_] (prof/record-read :term-roster) (kv-members backend roster-key))
  (term-count [_] (prof/record-read :term-roster) (kv-count    backend roster-key))

  ;; the flat-map index *is* the portable projection, so both directions are the
  ;; backend's own enumeration and install — no key is reshaped on the way through.
  ;; minus the batch-seal counter: it describes the WAL's own health, not the
  ;; records, so it is no part of the portable projection — a dump carries it to no
  ;; store that can read it as anything, and the cross-backend parity of this seq is
  ;; what `index-dump-test` pins
  (index-entries [_]         (remove (fn [[k _]] (= k (count-key sealed-prefix)))
                                     (kv-entries backend)))
  (index-load    [_ entries] (kv-load    backend entries))

  (clear-index! [_] (kv-clear! backend) nil))
