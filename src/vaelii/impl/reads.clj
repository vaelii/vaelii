;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.reads
  "The named entry points onto the index — a read **as stored**, or a read **as believed**.

  The fourth invariant is that a stored sentex is not a believed one (README.md, \"The
  model in one page\").  Every `IndexStore` posting is storage: it holds a defeated
  default, a conclusion whose support was withdrawn and a spelling an equality retired,
  because all three are revivable and the index is not where belief lives.  So a caller
  reading a posting has a question to answer, and until it is asked in the name of the
  read nothing distinguishes the caller that answered it from the one that forgot.

  This namespace is where it is asked.  Every raw `vaelii.impl.protocols` index read
  outside a short list of implementers goes through an entry point here, and the entry point's own
  name says which answer it gives — `lein lint`'s **E16** is what keeps that true, and
  its allowlist is the one place the exceptions are written down.

  ## The two entry points, and why they take different arguments

  - **`as-stored-…` takes the index store.**  An as-stored read *is* an index
    operation, so the entry point's arglist is the protocol method's and nothing else is in
    scope.  A caller reaching one is saying it wants storage: a candidate set it filters
    itself, a name set that must over-approximate, a diagnostic that reports what is
    written.  Each entry point below says what a stored-but-disbelieved answer is *for*.
  - **`believed-…` takes the KB.**  Belief lives in the JTMS, so a believed read is a
    question about the KB and not about the index — which is exactly the distinction the
    arglists carry.  The filter is `jtms/in?`, which already drops a **superseded**
    spelling along with a defeated one (`vaelii.impl.jtms`'s `-in?`), so a believed entry point
    means what `kb/sentexes-matching` means for the handles it yields.

  An entry point over a named method is a **wrapper and never a rewrite**: one call to
  the method, the same laziness, the same count-aware path.  An entry point over the
  `family-*` methods tallies its family's `:reads` here, one per logical read, since the
  method serves every family and tallies nothing.  An argument read is the slot predicate set
  and then a node per predicate in it, and tallies `:argument-slot` and `:argument-root`
  once each, which is what keeps `assert_cost_test` reading the same numbers.

  ## A read over every context is named `…-global`

  A family read takes the reader's ancestor set, and passes `p/every-context` only where it
  reads past every reader on purpose: a name set scoped later, the taxonomy's supporters, a
  census.  The entry point that forwards `p/every-context` ends in `-global`, and lint
  E16 holds the allowlist of its callers (docs/indexing.md, \"The family methods\").

  ## Where there is only one entry point, and why

  - **The cardinalities** (`stored-count-…`) count a posting set's members.  Belief is
    not in the index, so there is no O(1) believed count and this namespace does not
    pretend otherwise — a believed count is `(count (believed-… …))` and is O(n).  The
    public readers state the same thing (`vaelii.core/count-with-functor`).
  - **The vocabulary** (`stored-terms-global`, `stored-term-count-global`) is the set
    of names the term index is keyed by.  A name enters with the first sentex mentioning it and leaves
    with the last, so it answers *what this KB talks about* — a question defeat does not
    change.
  - **The watched-rule set** (`watched-rule?`, `watched-rules`, `watched-rules-on`)
    answers \"which rules might need re-checking\", never \"does the exception hold\", and
    stores no truth value at all (`protocols/IndexStore`).  Filtering it by belief would
    narrow a re-check queue, and a missed re-check is a wrong belief where an extra one
    is a query nobody needed.

  ## Two belief questions this namespace does not answer

  - **A rule's** belief is `resolution/rule-believed?` and not `jtms/in?`: a sentex the
    TMS holds no node for is *available* rather than disbelieved, which is an arm a plain
    membership test does not have.  So `as-stored-rules-by-antecedent-global` and its
    consequent twins have no believed sibling here, and a chainer asks
    `res/rule-believed?` of each handle it means to fire.
  - **`resolution/*belief-blind*`** is not read here.  It is a named opt-out scoped to
    the retrieval entry point that resolves `CxEverything`, and no caller of these entry points is on
    that path — an entry point that consulted it would extend the opt-out to reads nobody granted
    it to."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:dynamic *contexts-read*
  "nil, or a volatile set to which each entry point here that reads by context adds the
  contexts it reads.  A test binds it around a settle step to bound the contexts that
  step reads (`genlcx_move_oracle_test`); a read over every context adds nothing."
  nil)

(defn- read-in!
  "Add the contexts `ctxs` to `*contexts-read*` when it is bound."
  [ctxs]
  (when-let [t *contexts-read*]
    ;; the every-context marker is a keyword, not a collection of contexts
    (when (coll? ctxs) (vswap! t into ctxs))))

(defn- read-at!
  "Add the context `c` to `*contexts-read*` when it is bound."
  [c]
  (when-let [t *contexts-read*] (vswap! t conj c)))

;; ---- extents: the trie and the secondary roots ---------------------------

(defn as-stored-in-context
  "Handles stored in `context` — its whole extent, rules included, belief unread.

  A stored-but-disbelieved answer is what a caller wants here when it is about the
  *contents* of a context rather than about what holds in it: a teardown that must remove
  every record it finds, an ancestor set sweep that fetches each record and decides on the record,
  a level-1 diagnostic reporting what the root holds."
  [index context]
  (read-at! context)
  (prof/record-read :context-root)
  (p/family-leaf index :context-root [context]))

(defn as-stored-with-functor
  "Handles of fact sentexes whose functor is `pred`, any arity, either polarity — belief
  unread.

  The candidate-set read: a caller narrowing by predicate almost always fetches each
  record and decides on its polarity, its context and its belief together, and doing so
  one handle at a time is cheaper than two passes over the same set.  A caller whose
  filter is belief alone takes `believed-with-functor` instead."
  [index pred]
  (p/sentexes-with-functor index pred))

(defn- slot-union-global
  "The union of the `:argument-root` nodes `[pd pos term]` over the predicates `preds`, in
  every context.  A slot holds one predicate in the common case, and that node's
  handles are handed back as stored."
  [index preds pos term]
  (case (count preds)
    0 #{}
    1 (p/family-handles index :argument-root [(first preds) pos term] p/every-context)
    (reduce (fn [acc pd]
              (into acc (p/family-handles index :argument-root [pd pos term] p/every-context)))
            #{} preds)))

(defn as-stored-with-arg-global
  "Handles of fact sentexes holding `term` at 1-based argument `pos`, in every context —
  belief unread.  One read of the slot predicate set `[:argument-slot pos term]` for the
  predicates at the slot, then each predicate's argument-root node.

  Same shape as `as-stored-with-functor`: a candidate set whose consumer decides per
  record."
  [index pos term]
  (prof/record-read :argument-slot)
  (prof/record-read :argument-root)
  (let [term (sx/canon term)]
    (slot-union-global index (p/family-leaf index :argument-slot [pos term]) pos term)))

(defn as-stored-unary-with-arg-global
  "Handles of the unary fact sentexes whose lone argument is `term`, either polarity, in
  every context — belief unread, and a superset (the unary predicate set outlives its last unary
  fact where a fact of another arity empties the node), so the caller filters each record
  by arity.  The `:unary-slot` set, then the argument-root nodes at position 1."
  [index term]
  (prof/record-read :argument-slot)
  (prof/record-read :argument-root)
  (let [term (sx/canon term)]
    (slot-union-global index (p/family-leaf index :unary-slot [term]) 1 term)))

(defn as-stored-with-args
  "Handles with functor `pred` AND each `[pos term]` of `pos-terms`, belief unread:
  the intersection of `pred`'s argument-root nodes at the named positions, or the
  predicate extent when `pos-terms` is empty.  `pred` may be nil, for a
  variable-functor pattern."
  [index pred pos-terms]
  (p/sentexes-with-args index pred pos-terms))

(defn as-stored-with-args-in
  "`as-stored-with-args` restricted to the handles stated in one of `contexts`, a set: the
  argument roots end in the context, so no leaf outside `contexts` is read."
  [index pred pos-terms contexts]
  (read-in! contexts)
  (p/sentexes-with-args index pred pos-terms contexts))

(defn as-stored-predicates-at-arg
  "The predicates holding a **stored** fact, either polarity, with `term` at argument `pos`
  — the slot predicate set's entry, no handle read and no belief consulted.

  A name-set read rather than a posting read, so it names predicates where the other
  entry points here name handles.  A predicate enters with its first stored fact at the
  slot and leaves with its last, so a defeated claim keeps it listed: the answer is for a
  caller that must over-approximate which predicates a term could be claimed under."
  [index pos term]
  (prof/record-read :argument-slot)
  (p/family-leaf index :argument-slot [pos (sx/canon term)]))

(defn as-stored-unary-predicates
  "The predicates holding a **stored** unary fact, either polarity, over `term`: the
  `:unary-slot` set, a superset that outlives the term's last unary fact of a
  predicate (`kv/unary-slot-key`), no handle read and no belief consulted."
  [index term]
  (prof/record-read :argument-slot)
  (p/family-leaf index :unary-slot [(sx/canon term)]))

(defn as-stored-with-term
  "Handles the inverted term index keys by `term` — belief unread.

  Exact for a symbol; for a compound outside the indexed depth bounds it holds only the
  sentexes that nest it deep enough, so `kb/find-sentexes` is the exact read for one.  The
  postings are a candidate set in both cases: a term appears in a sentence the reader then
  has to look at."
  [index term]
  (prof/record-read :term-index)
  (p/family-leaf index :term-index [(sx/canon term)]))

(defn as-stored-naming-handle
  "Handles of the stored sentexes that nest the handle term `(sentexHandle h)` inside a
  content literal, every meta naming handle `h` among them, belief unread: the term's own
  term-index key, one read.  Holds only while the store was indexed with
  `sx/*min-indexed-depth*` 1 or less, the default, which keys a compound nested at depth 1.
  A sentex holding the term as a content literal itself is not among them;
  `kb/find-sentexes` is the exact read for any compound."
  [index h]
  (as-stored-with-term index (sx/sentex-handle h)))

(defn as-stored-with-terms
  "Handles the inverted term index keys by every one of `terms`, one intersection — belief
  unread.  A candidate set, as `as-stored-with-term`'s is."
  [index terms]
  (p/sentexes-with-terms index terms))

(defn as-stored-at-path
  "Handles whose trie path matches `pattern` — one walk, no records fetched, nothing
  interpreted.  A variable token in the path is a wildcard that fans over every child.

  The rawest read the index has.  Level 0 of `vaelii.impl.levels` addresses the trie
  directly and interprets neither belief nor polarity, which is what makes it the floor
  the other levels are measured against, and `vaelii.impl.decide` reads one exact
  sentence under every context to find a stored converse."
  [index pattern]
  (p/lookup index pattern))

(defn believed-with-functor
  "Handles of fact sentexes with functor `pred` that the KB **believes** — the extent
  above, filtered by `jtms/in?`.

  Lazy, as the posting read is: the filter is applied as the seq is walked, so a consumer
  taking a prefix pays a TMS probe per handle it takes and not per handle in the root.  A
  superseded spelling drops out with a defeated one, since that is what `in?` answers."
  [kb pred]
  (let [tms (reasoning/tms kb)]
    (filter #(jtms/in? tms %) (p/sentexes-with-functor (:index kb) pred))))

(defn believed-with-args
  "Handles with functor `pred` AND each `[pos term]` of `pos-terms` that the KB
  **believes** — `as-stored-with-args` filtered by `jtms/in?`, lazily.

  The narrowing read's believed entry point: a caller that knows several of a sentence's terms
  and wants only what holds asks here rather than intersecting and then filtering by
  hand."
  [kb pred pos-terms]
  (let [tms (reasoning/tms kb)]
    (filter #(jtms/in? tms %) (p/sentexes-with-args (:index kb) pred pos-terms))))

;; ---- cardinalities: a posting set's size, and never its members -----------

(defn stored-count-in-context
  "How many sentexes are **stored** in `context` — one set-size read, O(1), nothing
  fetched and no belief consulted.  A defeated default still occupies its context."
  [index context]
  (read-at! context)
  (prof/record-read :context-root)
  ;; the context root is a flat set per context, so the count over `#{context}` is its size
  (long (p/family-count index :context-root [] #{context})))

(defn stored-count-with-functor
  "How many fact sentexes are **stored** with functor `pred` — one set-size read, O(1).

  The presence check in front of nearly every definitional check in the engine: a KB that declares
  none of a feature's predicates pays one integer read and stops, which is what keeps an
  unused feature off the assert path."
  [index pred]
  (p/count-with-functor index pred))

(defn stored-count-with-arg-global
  "How many fact sentexes **store** `term` at argument position `pos`, in every context —
  the slot predicate set, then one O(1) count read per predicate at the slot.  The sum is
  disjoint: a handle is one sentex with one functor, so it sits under one predicate at a
  fixed `(pos, term)`."
  [index pos term]
  (prof/record-read :argument-slot)
  (prof/record-read :argument-root)
  (let [term (sx/canon term)]
    (transduce (map #(long (p/family-count index :argument-root [% pos term] p/every-context)))
               + 0 (p/family-leaf index :argument-slot [pos term]))))

(defn stored-count-at
  "How many sentexes are **stored** under trie prefix `prefix` — the count-aware trie's
  own tally, no walk.  `[]` is the whole KB."
  [index prefix]
  (p/count-at index prefix))

(defn as-stored-children
  "The child tokens **stored** under trie prefix `prefix`, belief unread: under `[]`, the
  first token of every stored sentence, so every functor of a stored fact."
  [index prefix]
  (p/children index prefix))

(defn as-stored-leaf
  "Handles stored at exactly the trie leaf `path`: one read, never a wildcard match
  (`kb/find-sentex-handle`'s dedup)."
  [index path]
  (p/leaf-at index path))

(defn stored-count-children
  "How many child tokens sit under interior prefix `prefix` — the trie's distinct-value
  count at a position, answered without building the child set.

  What the planner's cost model divides by, so it must not scale with the KB:
  `(count (stored-children …))` would, and this does not: `family-child-count` answers
  the child set's cardinality without building it."
  [index prefix]
  (prof/record-read :trie-counts)
  (long (p/family-child-count index :trie prefix)))

;; ---- the bodies stored in both polarities ----------------------------------

;; The opposed family (`kv/opposed-adds`) holds a body while a `(not B)` and a `B` are both
;; stored, in any contexts, and its members are the handles of both polarities.  A
;; negation nogood needs a body stored both ways, and a stored-but-disbelieved member
;; still forms one: the placement reads each member's belief itself.

(defn stores-opposed?
  "Is any body **stored** in both polarities?  One count read, belief unread."
  [index]
  (prof/record-read :opposed)
  (pos? (long (p/family-child-count index :opposed-bodies []))))

(defn stored-opposed?
  "Is `body` **stored** in both polarities?  One membership read, belief unread."
  [index body]
  (prof/record-read :opposed)
  (boolean (p/family-member? index :opposed-bodies [] (sx/canon body))))

(defn as-stored-opposed-bodies
  "Every body **stored** in both polarities, as a set."
  [index]
  (prof/record-read :opposed)
  (p/family-leaf index :opposed-bodies []))

(defn stores-opposed-with-functor?
  "Is a body of functor `f` **stored** in both polarities?  Two count reads, belief
  unread."
  [index f]
  (prof/record-read :opposed)
  (or (pos? (long (p/family-child-count index :opposed-functor [f])))
      (pos? (long (p/family-child-count index :opposed-between [f])))))

(defn stores-opposed-between?
  "Is a body of functor `f` that is `nm/between-predicates?` **stored** in both
  polarities?  One count read, belief unread."
  [index f]
  (prof/record-read :opposed)
  (pos? (long (p/family-child-count index :opposed-between [f]))))

(defn as-stored-opposed-members-global
  "The handles of `body`'s facts of both polarities while it is **stored** in both, in
  every context, belief unread; empty when it is not."
  [index body]
  (prof/record-read :opposed)
  (p/family-handles index :opposed [(sx/canon body)] p/every-context))

(defn as-stored-opposed-in
  "The handles of the facts of every body **stored** in both polarities that are stated
  in a context of `contexts`, belief unread: |contexts| leaf reads."
  [index contexts]
  (read-in! contexts)
  (prof/record-read :opposed)
  (if (empty? contexts) #{} (p/family-handles index :opposed-in [] contexts)))

;; ---- the length set, the terms of two unary predicates, the self tuples ----

(defn as-stored-self-tuples
  "The handles of the **stored** ground positive binary self tuples `(f a a)` of functor
  `f` stated in a context of `contexts`, belief unread."
  [index f contexts]
  (read-in! contexts)
  (prof/record-read :predicate-extent)
  (p/family-handles index :self-tuple [f] contexts))

(defn as-stored-self-tuples-global
  "`as-stored-self-tuples` in every context."
  [index f]
  (prof/record-read :predicate-extent)
  (p/family-handles index :self-tuple [f] p/every-context))

(defn as-stored-shape-lengths
  "The lengths the positive facts of functor `f` are **stored** at, as a set, belief
  unread: one name-set read.  A length leaves with its last fact."
  [index f]
  (prof/record-read :predicate-extent)
  (p/family-leaf index :shape-lengths [f]))

(defn as-stored-mint-rules
  "The `[kind handle]` of every **stored** rule of `kv/mint-rules`, as a set: one name-set
  read."
  [index]
  (prof/record-read :mint-rules)
  (p/family-leaf index :mint-rules []))

(defn stored-count-shape-tuples-global
  "How many **stored** positive facts of functor `f` hold `n` arguments, in every
  context: one count read."
  [index f n]
  (prof/record-read :predicate-extent)
  (long (p/family-count index :shape-tuple [f n] p/every-context)))

(defn stored-count-denials-global
  "How many **stored** negative facts `(not (f …))` there are, in every context: the
  predicate extent, which holds both polarities, less the positive facts at each stored
  length.  One count read per length."
  [index f]
  (- (stored-count-with-functor index f)
     (transduce (map #(stored-count-shape-tuples-global index f %)) +
                (as-stored-shape-lengths index f))))

(defn as-stored-shape-tuples-global
  "The handles of the **stored** positive facts of functor `f` holding `n` arguments, in
  every context, belief unread."
  [index f n]
  (prof/record-read :predicate-extent)
  (p/family-handles index :shape-tuple [f n] p/every-context))

(defn stored-count-denials-in
  "How many **stored** negative facts `(not (f …))` there are in the contexts of
  `contexts`, a set, or `p/every-context` for all of them: `stored-count-denials-global`
  read at those contexts' leaves.  A positive fact of no argument, `(f)`, sits in the
  extent and at no stored length, so it counts here too: 0 is exact, and any other
  answer bounds the denials from above."
  [index f contexts]
  (read-in! contexts)
  (prof/record-read :predicate-extent)
  (- (long (p/family-count index :predicate-extent [f] contexts))
     (transduce (map #(long (p/family-count index :shape-tuple [f %] contexts))) +
                (as-stored-shape-lengths index f))))

(defn as-stored-shape-tuples-in
  "The handles of the **stored** positive facts of functor `f` holding `n` arguments in
  the contexts of `contexts` (a set, or `p/every-context`), belief unread.  One context
  answers its leaf as stored."
  [index f n contexts]
  (read-in! contexts)
  (prof/record-read :predicate-extent)
  (p/family-handles index :shape-tuple [f n] contexts))

;; ---- the arity bindings ----------------------------------------------------
;; The stored facts binding a relation's length (`sx/arity-binding`), read by the arity
;; family, which keeps a reader's by `jtms/in?` and its ancestor set.

(defn as-stored-arity-binding-kinds
  "The `[kind value]` of every **stored** length binding of `pred`, as a set, belief
  unread: one read."
  [index pred]
  (prof/record-read :arity-binding)
  (p/family-leaf index :arity-binding-kinds [pred]))

(defn stored-arity-bound?
  "Does `pred` hold a **stored** length binding, belief unread: one probe."
  [index pred]
  (prof/record-read :arity-binding)
  (boolean (p/family-member? index :arity-bound [] pred)))

(defn as-stored-arity-bound
  "Every predicate holding a **stored** length binding, as a set, belief unread."
  [index]
  (prof/record-read :arity-binding)
  (p/family-leaf index :arity-bound []))

(defn stored-count-arity-bound
  "How many predicates `as-stored-arity-bound` holds: one read."
  [index]
  (prof/record-read :arity-binding)
  (long (p/family-child-count index :arity-bound [])))

(defn- arity-bindings
  "`[[handle kind value context] ...]` of `pred` in the contexts `ctxs` keeps: per stored
  `[kind value]`, its node's children in `ctxs` and a leaf read per child kept."
  [index pred ctxs]
  (prof/record-read :arity-binding)
  (into [] (mapcat (fn [[kind v]]
                     (let [node [pred kind v]]
                       (for [c (p/family-children index :arity-binding node ctxs)
                             h (p/family-leaf index :arity-binding (conj node c))]
                         [h kind v c]))))
        (p/family-leaf index :arity-binding-kinds [pred])))

(defn as-stored-arity-bindings
  "`[[handle kind value context] ...]`, the **stored** length bindings of `pred` stated
  in a context of `contexts`, belief unread."
  [index pred contexts]
  (read-in! contexts)
  (arity-bindings index pred contexts))

(defn as-stored-arity-bindings-global
  "`as-stored-arity-bindings` in every context."
  [index pred]
  (arity-bindings index pred p/every-context))

(defn as-stored-unary-multi-terms
  "The terms the unary predicate set lists two or more predicates of, as a set, belief unread:
  a superset of the terms holding two **stored** memberships."
  [index]
  (prof/record-read :argument-slot)
  (p/family-leaf index :unary-multi []))

(defn as-stored-unary-kept-terms
  "The terms of `as-stored-unary-multi-terms` whose unary predicate set lists `pred`, as a set,
  belief unread: a superset of the terms holding a **stored** membership or denial of
  `pred` beside a stored fact of another unary predicate."
  [index pred]
  (prof/record-read :argument-slot)
  (p/family-leaf index :unary-kept [pred]))

(defn as-stored-unary-kept-types
  "The predicates `as-stored-unary-kept-terms` holds a term under, as a set, belief
  unread."
  [index]
  (prof/record-read :argument-slot)
  (p/family-leaf index :unary-kept-types []))

(defn stored-count-unary-kept-types
  "How many predicates `as-stored-unary-kept-types` holds: one read."
  [index]
  (prof/record-read :argument-slot)
  (long (p/family-child-count index :unary-kept-types [])))

(defn as-stored-unary-denied-terms
  "The terms a **stored** `(not (pred term))` names, as a set, belief unread."
  [index pred]
  (prof/record-read :argument-slot)
  (p/family-leaf index :unary-denied [pred]))

(defn as-stored-unary-denied-types
  "The predicates `as-stored-unary-denied-terms` holds a term under, as a set, belief
  unread."
  [index]
  (prof/record-read :argument-slot)
  (p/family-leaf index :unary-denied-types []))

(defn stored-count-unary-denied-types
  "How many predicates `as-stored-unary-denied-types` holds: one read."
  [index]
  (prof/record-read :argument-slot)
  (long (p/family-child-count index :unary-denied-types [])))

;; ---- the stored excepts and defeats ----------------------------------------
;; A positive `(except (sentexHandle H))` keys in the trie as `[except m sentexHandle H
;; ctx]`, `m` the arity marker of the handle term, so the level above the context answers
;; by target and in either polarity's place only the positive one is read: a `(not …)`
;; keys under `[:false …]`.  `defeat` keys the same way.

(def ^:private handle-mark (sx/subterm-mark 2))

(defn- naming-prefix
  "The trie prefix of the positive `(functor (sentexHandle h))` facts, one level above
  their contexts; with no `h`, the level whose children are the handles named."
  ([functor] [functor handle-mark sx/sentex-handle-functor])
  ([functor h] [functor handle-mark sx/sentex-handle-functor (long h)]))

(defn stores-any?
  "Is a positive `(functor …)` fact **stored** in any context?  One count read on the
  trie's `[functor]`, belief unread."
  [index functor]
  (pos? (p/count-at index [functor])))

(defn stores-in?
  "Does a context of `contexts` **store** a fact of functor `pred`, either polarity?  The
  predicate extent's children intersected with `contexts`, no leaf read, belief unread."
  [index pred contexts]
  (read-in! contexts)
  (prof/record-read :predicate-extent)
  (boolean (seq (p/family-children index :predicate-extent [pred] contexts))))

(defn stored-naming?
  "Is a positive `(functor (sentexHandle h))` **stored** in any context?  One count read."
  [index functor h]
  (pos? (p/count-at index (naming-prefix functor h))))

(defn as-stored-named-global
  "The handles the positive `(functor (sentexHandle H))` facts **stored** in any context
  name, as a set: the children of the trie's `[functor m sentexHandle]` level.  On the map
  backends the set is the one the backend holds, so two reads with no write between them
  answer one object."
  [index functor]
  (prof/record-read :trie-counts)
  (let [cs (p/family-children index :trie (naming-prefix functor) p/every-context)]
    (if (set? cs) cs (set cs))))

(defn as-stored-naming-by-context
  "The positive `(functor (sentexHandle h))` facts **stored**, as one `[context handles]`
  pair per context stating one: the children under the prefix and the leaf under each."
  [index functor h]
  (let [pre (naming-prefix functor h)]
    (keep (fn [c] (let [hs (p/leaf-at index (conj pre c))] (when (seq hs) [c hs])))
          (p/children index pre))))

(defn as-stored-naming
  "The handles of the positive `(functor (sentexHandle h))` facts **stored** in a context
  of `contexts` (every context when nil), as a vector, or nil when there is none.  The
  children under the prefix are filtered by `contexts` before a leaf is read, so a context
  outside `contexts` costs a membership test."
  ([index functor h] (as-stored-naming index functor h nil))
  ([index functor h contexts]
   (let [pre (naming-prefix functor h)]
     (not-empty (into [] (comp (filter #(or (nil? contexts) (contains? contexts %)))
                               (mapcat #(p/leaf-at index (conj pre %))))
                      (p/children index pre))))))

;; ---- the vocabulary -----------------------------------------------------

(defn stored-terms-global
  "Every symbol term the index is keyed by, in every context — the KB's vocabulary,
  unordered.

  A name is in this set while some **stored** sentex mentions it, so it answers what
  the KB talks about rather than what it currently holds: defeating the one fact about a
  term does not unname the term."
  [index]
  (prof/record-read :term-names)
  (p/family-children index :term-names [] p/every-context))

(defn stored-term-count-global
  "How many distinct symbol terms the index is keyed by, in every context — the set's
  own count, no walk over it."
  [index]
  (prof/record-read :term-names)
  (long (p/family-count index :term-names [] p/every-context)))

;; ---- the rule indexes ----------------------------------------------------

(defn as-stored-rules-by-antecedent-global
  "Handles of rules with an antecedent on `pred`, stated in any context — every rule,
  whatever its direction, belief unread.

  Belief for a **rule** is `resolution/rule-believed?` and not `jtms/in?`, which is why
  there is no believed entry point beside this one: a rule the TMS holds no node for is available
  rather than disbelieved, and a chainer asks that question of each handle it means to
  fire."
  [index pred]
  (prof/record-read :rule-index)
  (p/family-handles index :rule-antecedent [pred] p/every-context))

(defn as-stored-rules-by-consequent-in
  "Handles of rules concluding `pred` stated in one of `contexts`, a set — every rule,
  whatever its direction, belief unread.

  `resolution/rule-believed?` is the belief question, as for the antecedent entry point above.  A
  rule whose consequent functor is a variable files under `protocols/var-consequent-key`
  rather than under a canonical `?var0`, so a concrete goal's answer is this bucket
  unioned with that catch-all (`resolution/concluding-rule-handles`)."
  [index pred contexts]
  (read-in! contexts)
  (prof/record-read :rule-index)
  (p/family-handles index :rule-consequent [pred] contexts))

(defn as-stored-rules-by-consequent-global
  "`as-stored-rules-by-consequent-in` in every context."
  [index pred]
  (prof/record-read :rule-index)
  (p/family-handles index :rule-consequent [pred] p/every-context))

(defn as-stored-rule-keys
  "The antecedent keys some **stored** rule takes (`rules/antecedent-key`), as a set: the
  root level of the `:rule-antecedent` trie."
  [index]
  (prof/record-read :rule-index)
  (p/family-leaf index :rule-antecedent-keys []))

(defn stored-rule-key?
  "Does a **stored** rule take the antecedent key `k`?  One membership test."
  [index k]
  (prof/record-read :rule-index)
  (boolean (p/family-member? index :rule-antecedent-keys [] k)))

(defn stored-rule-key-test
  "A membership test for the antecedent keys some **stored** rule takes, or nil when no
  stored rule takes one: one read, the key count, then one membership test per key the
  caller asks about."
  [index]
  (prof/record-read :rule-index)
  (when (pos? (long (p/family-child-count index :rule-antecedent-keys [])))
    (fn [k] (boolean (p/family-member? index :rule-antecedent-keys [] k)))))

(defn stored-rule-key-count
  "How many antecedent keys the **stored** rules take.  One read, the key count."
  [index]
  (prof/record-read :rule-index)
  (long (p/family-child-count index :rule-antecedent-keys [])))

(defn as-stored-rule-keys-deferred
  "`[n keys]`: how many antecedent keys the **stored** rules take, and `as-stored-rule-keys`
  as a delay, or nil when they take none.  One read, the key count, and the set read only
  when the caller forces the delay."
  [index]
  (prof/record-read :rule-index)
  (let [n (long (p/family-child-count index :rule-antecedent-keys []))]
    (when (pos? n)
      [n (delay (p/family-leaf index :rule-antecedent-keys []))])))

(defn as-stored-rule-keys-meeting
  "The antecedent keys some **stored** rule takes among a caller's candidates, as a vector,
  read from the smaller side in one read.  `within` takes the stored key count and returns
  the candidate keys when they are at most that many, else nil: then each candidate costs
  a membership test.  Otherwise the stored keys `keep?` accepts, one pass over them, which
  a backend that decodes the set pays per key."
  [index within keep?]
  (prof/record-read :rule-index)
  (let [n (long (p/family-child-count index :rule-antecedent-keys []))]
    (if (zero? n)
      []
      (if-let [ks (within n)]
        (into [] (filter #(p/family-member? index :rule-antecedent-keys [] %)) ks)
        (into [] (filter keep?) (p/family-leaf index :rule-antecedent-keys []))))))

(defn as-stored-rules-in
  "Handles of the **stored** rules of `kind` stated in one of `contexts`: `:rule` for
  every rule, `:solve` for the rules a solve reads (`rules/solve-sentex?`), `:lazy` for
  the rules whose `:engines` take `:lazy`.  The rule
  extent ends in the context, so this costs min(|contexts stating one|, |contexts|) probes
  plus a leaf read per context kept."
  [index kind contexts]
  (read-in! contexts)
  (prof/record-read :rule-index)
  (p/family-handles index :rule-extent [kind] contexts))

(defn as-stored-rules-in-global
  "`as-stored-rules-in` in every context."
  [index kind]
  (prof/record-read :rule-index)
  (p/family-handles index :rule-extent [kind] p/every-context))

(defn stored-rule-count-global
  "How many rules of `kind` (`as-stored-rules-in`, default `:rule`) the store holds, in
  every context: the rule extent's node count, with no handle set built."
  ([index] (stored-rule-count-global index :rule))
  ([index kind]
   (prof/record-read :rule-index)
   (long (p/family-count index :rule-extent [kind] p/every-context))))

(defn stores-rule-in?
  "Does a context of `contexts` **store** a rule?  The rule extent's children intersected
  with `contexts`, no leaf read."
  [index contexts]
  (read-in! contexts)
  (prof/record-read :rule-index)
  (boolean (seq (p/family-children index :rule-extent [:rule] contexts))))

;; ---- the mint family ------------------------------------------------------
;; The records a **stored** argument-declaration justification concludes
;; (`special/post-mint!`), read by the settle's mint withdrawal.  A mint is a fact about a
;; stored justification and not about belief: a blocked or OUT mint stays filed, and the
;; withdrawal asks each candidate's belief itself (`special/withdrawable-mint`).

(defn stored-mint-count-global
  "How many records are filed as mints, in every context.  One count read."
  [index]
  (prof/record-read :mint)
  (long (p/family-count index :mint-in [] p/every-context)))

(defn as-stored-mint-terms
  "The terms some filed mint is about, as a set."
  [index]
  (prof/record-read :mint)
  (p/family-leaf index :mint-terms []))

(defn stored-mint-term-count
  "How many terms some filed mint is about.  One count read."
  [index]
  (prof/record-read :mint)
  (long (p/family-child-count index :mint-terms [])))

(defn stored-mint-term?
  "Is some filed mint about `term`?  One membership test."
  [index term]
  (prof/record-read :mint)
  (boolean (p/family-member? index :mint-terms [] term)))

(defn as-stored-mints-about-global
  "Handles of the mints filed about `term`, in every context."
  [index term]
  (prof/record-read :mint)
  (p/family-handles index :mint [term] p/every-context))

(defn as-stored-mint-contexts-global
  "The contexts some filed mint is stored in, as a set."
  [index]
  (prof/record-read :mint)
  (set (p/family-children index :mint-in [] p/every-context)))

(defn stored-mint-context-count
  "How many contexts some filed mint is stored in.  One count read."
  [index]
  (prof/record-read :mint)
  (long (p/family-child-count index :mint-in [])))

(defn stored-mint-count-in
  "How many mints are filed in the contexts `cs`.  One count read per context."
  [index cs]
  (read-in! cs)
  (prof/record-read :mint)
  (long (p/family-count index :mint-in [] cs)))

(defn as-stored-mints-in
  "Handles of the mints filed in context `c`.  One leaf read."
  [index c]
  (read-at! c)
  (prof/record-read :mint)
  (p/family-leaf index :mint-in [c]))

;; ---- the watched-rule (exception re-check) set ----------------------------

(defn watched-rule?
  "Is `handle` in the exception/watched-rule set: an O(1) membership read, the check the
  firing path runs.

  The set stores no truth value, so there is no second entry point: it answers which rules
  carry an `exceptWhen` at all, never whether one holds.  Whether the exception *fires* is
  `provers/exceptions-block?`, and whether the rule itself is believed is
  `resolution/rule-believed?`."
  [index handle]
  (prof/record-read :exception-index)
  (p/family-member? index :exception-index [:rules] handle))

(defn watched-rules
  "Handles of every rule carrying a re-check condition — an exception, an `(unknown S)`
  antecedent, an aggregate, a closed-extent negative or a `different` antecedent
  (`rules/rechecked?`).

  Read to **queue re-checks**, which is why belief is not filtered: over-queueing costs a
  query at the next settle and under-queueing leaves a conclusion standing on evidence
  that has moved.  A trigger is conservative in the direction the answer is."
  [index]
  (prof/record-read :exception-index)
  (p/family-leaf index :exception-index [:rules]))

(defn watched-rule-count
  "How many rules `watched-rules` holds, read as the set's count without building the
  set."
  [index]
  (prof/record-read :exception-index)
  (long (p/family-child-count index :exception-index [:rules])))

(defn watched-rules-on
  "Handles of rules whose re-check condition mentions `pred` — the predicate-scoped slice
  of `watched-rules`, and unfiltered for its reason."
  [index pred]
  (prof/record-read :exception-index)
  (p/family-leaf index :exception-index [pred]))

(defn watched-rule-on?
  "Is `handle` in the `watched-rules-on` slice for `pred`: an O(1) membership read."
  [index pred handle]
  (prof/record-read :exception-index)
  (p/family-member? index :exception-index [pred] handle))

;; ---- reads scoped to the contexts a reader sees ---------------------------

(defn as-stored-with-functor-in
  "`as-stored-with-functor` restricted to the facts stated in one of `contexts` — a
  reader's ancestor set, or nil for every context.  The predicate extent ends in the
  context, so this costs min(|contexts stating one|, |contexts|) membership probes plus
  one leaf read per context kept (docs/indexing.md, \"By-context reads\")."
  [index pred contexts]
  (read-in! contexts)
  (p/sentexes-with-args index pred [] contexts))

(defn- functor-census
  [index pred ctxs]
  (prof/record-read :predicate-extent)
  (let [n (long (p/family-child-count index :predicate-extent [pred]))]
    [(if (zero? n) [] (p/family-children index :predicate-extent [pred] ctxs)) n]))

(defn as-stored-contexts-with-functor
  "`[seen n]`: the contexts of the set `contexts` in which a fact with functor `pred` is
  **stored**, either polarity, and how many contexts state one — the predicate extent's
  children, no handle read and no belief consulted.  Two calls: the children count, then,
  when it is not zero, min(|contexts stating one|, |contexts|) membership probes.  A
  defeated fact keeps its context listed, so the answer is for a caller that must
  over-approximate where `pred` is stated."
  [index pred contexts]
  (read-in! contexts)
  (functor-census index pred contexts))

(defn as-stored-contexts-with-functor-global
  "`as-stored-contexts-with-functor` over every context."
  [index pred]
  (functor-census index pred p/every-context))

(defn stored-count-with-functor-in
  "How many facts with functor `pred` are **stored** in the contexts of `contexts`: one
  leaf count per context stating one."
  [index pred contexts]
  (read-in! contexts)
  (prof/record-read :predicate-extent)
  (p/family-count index :predicate-extent [pred] contexts))

(defn stored-count-with-arg-in
  "How many facts with functor `pred` and `term` at argument `pos` are **stored** in the
  contexts of `contexts`: one leaf count per context the argument node lists and
  `contexts` holds."
  [index pred pos term contexts]
  (read-in! contexts)
  (prof/record-read :argument-root)
  (p/family-count index :argument-root [pred pos (sx/canon term)] contexts))

(defn as-stored-tokens-at-global
  "The distinct child tokens at argument `pos` of `pred`'s **stored** positive facts, in
  every context, belief unread: a walk of the trie under `[pred]` that skips the `pos - 1`
  arguments before it, a compound by its arity marker's count, and reads the child tokens
  at `pos`.  No handle is read, so the walk grows with the distinct prefixes up to `pos`.
  An atom at `pos` is its own token and a compound is its subterm mark
  (`sx/subterm-mark?`).  Past the last argument of a shorter tuple the children are
  contexts, so a caller reads the tuples of each term it keeps."
  [index pred pos]
  (letfn [(kids [prefix] (p/children index prefix))
          (skip [prefix n]
            (if (zero? n)
              [prefix]
              (mapcat (fn [tok]
                        (let [p' (conj prefix tok)]
                          (if (sx/subterm-mark? tok)
                            (mapcat #(skip % (dec n)) (skip p' (sx/subterm-arity tok)))
                            (skip p' (dec n)))))
                      (kids prefix))))]
    (prof/record-read :trie-counts)
    (into #{} (mapcat kids) (skip [pred] (dec pos)))))

(defn as-stored-atoms-at-global
  "The distinct atomic terms among `as-stored-tokens-at-global`: a compound at `pos` is
  not answered."
  [index pred pos]
  (into #{} (remove sx/subterm-mark?) (as-stored-tokens-at-global index pred pos)))

(defn as-stored-contexts-with-arg-in
  "The contexts of `contexts` holding a **stored** fact with functor `pred` and `term` at
  argument `pos`: the argument node's children that `contexts` holds."
  [index pred pos term contexts]
  (read-in! contexts)
  (prof/record-read :argument-root)
  (p/family-children index :argument-root [pred pos (sx/canon term)] contexts))

(defn as-stored-contexts-with-arg-global
  "`as-stored-contexts-with-arg-in` over every context: the argument node's children."
  [index pred pos term]
  (prof/record-read :argument-root)
  (p/family-children index :argument-root [pred pos (sx/canon term)] p/every-context))

(defn stored-census-with-arg-global
  "`[n k]`: how many facts with functor `pred` and `term` at argument `pos` are **stored**,
  in every context, and in how many contexts.  Two count reads."
  [index pred pos term]
  (prof/record-read :argument-root)
  (let [node [pred pos (sx/canon term)]]
    [(p/family-count index :argument-root node p/every-context)
     (long (p/family-child-count index :argument-root node))]))

;; ---- the taxonomy's supporter families -------------------------------------

(defn as-stored-supporters-global
  "The **stored** supporters of taxonomy key `k` (`[:genl a b]`, `[:genlCx a b]` or a
  flat-cache key) as `{handle ctx}`, belief unread: the node's children, then one leaf
  read per context.  The taxonomy decides an entry's belief from them, and a disbelieved
  supporter stays listed so that its revival can bring the entry back."
  [index k]
  (prof/record-read :tax-support)
  (reduce (fn [m c] (reduce #(assoc %1 %2 c) m (p/family-leaf index :tax-support (conj k c))))
          {} (p/family-children index :tax-support k p/every-context)))

(defn stored-supporter-count-global
  "How many **stored** handles support taxonomy key `k`, in every context: one count read."
  [index k]
  (prof/record-read :tax-support)
  (p/family-count index :tax-support k p/every-context))

(defn as-stored-installed-keys
  "The taxonomy keys **stored** handle `h` installs, as a set, belief unread: the keys a
  reconcile re-examines when `h`'s label moves.  One read."
  [index h]
  (prof/record-read :tax-support)
  (p/family-leaf index :tax-installs [h]))

(defn stored-count-named-supporters-global
  "How many positive `(functor (sentexHandle H))` facts are **stored** in every context,
  `functor` `except` or `defeat`, whose H installs a taxonomy key of relation `rel`
  (`kv/key-relation`): one count read on the `:tax-named` family, belief unread."
  [index rel functor]
  (prof/record-read :tax-named)
  (long (p/family-count index :tax-named [rel functor] p/every-context)))

(defn as-stored-supporter-map
  "Every taxonomy key with a **stored** supporter, as `{k {handle ctx}}`, by a walk of every
  entry `index` holds: O(store), for a raw taxonomy's private store, which holds the
  supporter families and nothing else."
  [index]
  (prof/record-read :tax-support)
  (reduce (fn [m [ek hs]]
            (if (and (vector? ek) (= :tax-support (nth ek 0)) (= :handles (nth ek 1)))
              (let [leaf (nth ek 2)]
                (reduce #(assoc-in %1 [(pop leaf) %2] (peek leaf)) m hs))
              m))
          {} (p/index-entries index)))
