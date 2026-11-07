;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.rules
  "A rule *is* a sentex — same structure (sentence + context), different indexing.
  Its sentence is an implication:

    (implies (and <antecedent> ...) <consequent>)     ; single antecedent needs no `and`

  Antecedents and consequent are sentence patterns that may contain variables.
  Rules are indexed by their antecedent/consequent predicates (see the index
  store) so forward chaining finds candidate rules without scanning, and — being
  ordinary sentexes — they get handles, TMS support, and retraction for free.

  Rules must be range-restricted: every consequent variable appears in some
  antecedent, so a fired consequent is ground.  The one exemption is a **head
  existential** `(exists ?y C)`, whose marked variable forward firing skolemizes
  (docs/skolem.md).  The same closure is required of an `exceptWhen` exception, which is a
  query rather than a conclusion but must be ground for the same reason (checked at the
  assert layer via `sentex/check-exception-closed`)."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]))

;; The rule *form* — its functor, its parts, its builder — has one owner:
;; `vaelii.impl.sentex`, whose constructor both parses and rebuilds it, so its
;; spelling decisions are the stored spelling.  The names below are delegations
;; kept for this namespace's readers; the dependency direction — rules already
;; requires sentex for the wrapper tables, peeling, and exception machinery —
;; decides which namespace owns the form.

(defn rule-sentence?
  "Is `sentence` a rule form `(implies <ante> <conseq>)`?"
  [sentence]
  (sx/implies? sentence))

(defn rule?
  "Is `sentex` a rule — a record with an `:antecedent`?  The field is the discriminant
  everywhere; a rule record holds no sentence to test."
  [sentex]
  (some? (:antecedent sentex)))

(defn antecedents
  "The antecedent patterns of a rule sentence (unwrapping a leading `and`)."
  [sentence]
  (sx/rule-antecedents sentence))

(defn consequent [sentence] (sx/rule-consequent sentence))

(defn rule-sentence
  "Build a rule sentence from antecedent patterns and a consequent pattern.
  One spelling for the whole codebase — see `sentex/rule-sentence`."
  [antecedents consequent]
  (sx/rule-sentence antecedents consequent))

(defn antecedent-key
  "The antecedent-index key an antecedent `literal` files under: its functor, or
  `[:not f]` for a negation whose body has functor `f`.

  Keyed under the bare `not` every negated antecedent of every rule shares one bucket,
  and each arriving negation decodes, and tries to match, every one of them;
  keyed by the body's predicate an arriving `(not (p a))` reaches the rules with a
  negated antecedent on `p` — and, through `trigger-keys`' genl walk, those on a genl of
  `p`, which is the direction subsumption runs in under a negation.  A vector, so the key
  can never collide with a predicate, which is always a symbol.  The same spelling on the
  index side (`antecedent-keys`, every writer) and the trigger side
  (`trigger-keys`)."
  [literal]
  (let [f (nm/functor literal)]
    (if (and (= sx/not-functor f) (= 2 (count literal)))
      (let [g (nm/functor (second literal))]
        (if (symbol? g) [:not g] f))
      f)))

(defn antecedent-keys
  "`antecedent-key` of each of `antes` — a rule record's `:antecedent`, or the antecedents
  `antecedent-predicates` splits off a sentence.  Every writer of the antecedent index
  passes the record's `:antecedent` here, the add (`special/index-rule-sentex`,
  `reindex`) and the removal (`special/disintegrate-sentex!`) alike, so the two compute
  their keys from one input."
  [antes]
  (keep antecedent-key antes))

(defn antecedent-predicates
  "The antecedent-index keys of a rule `sentence` — each antecedent's `antecedent-key`; a
  positive literal's key is its predicate, a negated one's is `[:not pred]`."
  [sentence]
  (antecedent-keys (antecedents sentence)))

(defn dependency-predicates
  "The antecedent keys of a rule `sentence` as `consequent-predicate` keys: what a rule
  reading those antecedents depends on, spelled as the thing that could satisfy it is filed.
  An `antecedent-key` names a negation by its body's predicate (`[:not flies]`), while a
  conclusion `(not (flies ?x))` is filed under `not`.  A dependency lookup among concluders
  must ask for `not`, or it reads an empty bucket and `checks/check-stratified` accepts a
  negation cycle.  Coarser than the index key on purpose: every negated antecedent depends on
  every negated conclusion, the safe direction (`checks/stratification-readers`)."
  [sentence]
  (map #(if (vector? %) sx/not-functor %) (antecedent-predicates sentence)))

(defn signed-reach
  "`p`'s global `genl` closure in direction `dir` (`:up` or `:down`), together with the
  predicates `genlInverse` edges reach either way round (`tax/signed-closure`): every
  predicate an antecedent or fact on `p` can meet through the matching fan.  The plain
  closure itself on a KB declaring no `genlInverse`."
  [tax dir p]
  (let [[st sw] (tax/signed-closure tax dir p nil)]
    (if (empty? sw) st (into st sw))))

(defn trigger-keys
  "The antecedent-index keys an arriving fact `sentence` triggers rules through, and the
  trigger side of `antecedent-key`.

  A positive fact triggers its predicate and its supertypes (`match1`'s subsumption).  A
  negative fact `(not (p a))` entails `(not (q a))` for every spec `q` of `p`, so it triggers
  `[:not q]` for each spec of its body's predicate.  Each side is the closure intersected with
  the keys some stored rule reads (`reads/as-stored-rule-keys`), walking the smaller of a
  membership test per closure term and one pass over the stored keys.  The spec walk stops at
  the stored key count (`tax/specs-global-within`), and `(not (thing X))` takes the pass.  The
  closures are unscoped, a superset that the placement narrows."
  [tax sentence index]
  (let [k (antecedent-key sentence)]
    (if (vector? k)
      (let [g (second k)]
        (reads/as-stored-rule-keys-meeting
         index
         ;; the bounded spec walk sees no genlInverse edge, so a KB declaring one takes
         ;; the pass
         (fn [n] (when (tax/genl-inverse-free? tax)
                   (some->> (tax/specs-global-within tax g n) (map #(vector :not %)))))
         #(and (vector? %) (contains? (signed-reach tax :up (second %)) g))))
      (let [up (delay (signed-reach tax :up k))]
        (reads/as-stored-rule-keys-meeting
         index
         (fn [n] (when (<= (count @up) (long n)) @up))
         #(contains? @up %))))))

(defn consequent-key
  "`consequent-predicate` of a rule whose consequent pattern is `c0`, read off the
  consequent itself — which a rule record holds as its `:consequent`."
  [c0]
  (let [c (let [inner (peek (sx/peel-rule-wrapper c0))]
            (if (sx/implies? inner) inner c0))]
    (nm/functor c)))

(defn consequent-predicate
  "The predicate a rule concludes.

  A **generator** concludes a rule, so its key is `implies` — reached by peeling the
  `set/*Rule` wrapper first, because that wrapper belongs to the rule being generated
  rather than to the generator (docs/generators.md).  Without the peel one generator
  files under `set/defaultRule` and the next under `implies`, by nothing more than how
  its generated rule happened to be written, and the single cell that answers *which rules
  are generators* would answer for some of them."
  [sentence]
  (consequent-key (consequent sentence)))

;; ---- virtual rule-direction predicates ----------------------------------
;; Wrapping a rule sets the engines that run it (`:engines` on the record,
;; `sx/direction-engines`).  Default (a bare implies) is backward — forward chaining
;; materializes a conclusion per match, intractable on a large KB, so forward is opt-in
;; (set/forwardRule).  Five directions:
;;   #{:forward :backward}  set/forwardRule — forward AND backward (the wrapper adds forward
;;                          without taking the backward use away); the forward mode the
;;                          ontology uses.
;;   #{:backward}           backward only (the default).
;;   #{:forward}            forward-chains, never backward (set/forwardOnlyRule): a rule
;;                          whose conclusion answers a goal its own antecedent poses.
;;   #{:backward :lazy}     backward; a forward join proves it (set/lazyForwardRule).
;;   #{}                    neither engine (set/inertRule, documentation).
;; A choice or constraint rule holds #{:solve}: a solve reads it and neither chainer does.
;; The *index* is complete either way — a rule is filed under both its antecedent and its
;; consequent predicates whatever its engines (`special/index-rule-sentex`) — and the
;; engines on the record are what the two chainers read.

(defn forward-sentex?
  "Does this stored rule sentex forward-chain?  Read off the record's `:engines`, which
  its `set/*Rule` wrapper set.  An `assumptionRule` (a choice head) and a
  `hard`/`softConstraint` (a contradiction marker) hold `#{:solve}` — their heads are
  decided or forbidden by a solve, not derived — so neither chainer runs them."
  [sentex] (contains? (:engines sentex) :forward))

(defn backward-sentex?
  "Does this stored rule sentex backward-chain?  Read off the record's `:engines`, as
  `forward-sentex?` is."
  [sentex] (contains? (:engines sentex) :backward))

(defn lazy-sentex?
  "Does a forward join prove this stored rule sentex's conclusion on demand
  (`set/lazyForwardRule`)?  Read off `:engines`; a rule that also forward-chains stores
  its conclusions, so it is not lazy."
  [sentex] (let [e (:engines sentex)] (and (contains? e :lazy) (not (contains? e :forward)))))

(defn solve-sentex?
  "Does a `do/label` solve read this stored rule sentex — a choice, constraint or
  cardinality rule, or a `set/solveRule`?  Read off `:engines`, as `forward-sentex?` is."
  [sentex] (contains? (:engines sentex) :solve))

(defn chains?
  "Does either chainer run this stored rule sentex?  False for an inert rule and for a
  choice or constraint rule."
  [sentex] (or (forward-sentex? sentex) (backward-sentex? sentex)))

;; ---- exceptWhen: the rule states its own exception ------------------------
;; `(exceptWhen <query> <rule>)` blocks: for a binding its query holds of, the rule
;; does not conclude.  The exception is *not* part of the rule record — it is a
;; separate belief-following meta-sentex `(exceptWhen <query> (sentexHandle H))`
;; naming the rule by handle (`sentex/exceptWhen-meta`); the engine reads a rule's
;; exceptions through `provers/rule-exceptions`, and their predicates are registered
;; in the re-check index by the meta-sentex's own indexing (`special`).  See
;; docs/exceptions.md.

(defn assumption?
  "Is this stored rule sentex a `set/assumptionRule` — a choice rule whose head a solve
  decides rather than the chainer deriving?  Its `:effect` is `:choose`
  (docs/solving.md)."
  [sentex] (= :choose (:effect sentex)))

(defn constraint-of
  "The constraint class of this stored rule sentex — `:hard` / `:soft` from its
  `set/hardConstraint` / `set/softConstraint` wrapper (`:effect` `:forbid` /
  `:penalize`), or nil for any other rule (docs/solving.md)."
  [sentex] (sx/effect-constraint (:effect sentex)))

(defn constraint?
  "Is this stored rule sentex a `set/hardConstraint` / `set/softConstraint` — a
  contradiction rule whose conjunctive body a solve grounds into a nogood?"
  [sentex] (some? (constraint-of sentex)))

;; ---- negation as failure: `unknown` antecedents --------------------------
;; The accessors mirror the exception ones.  See docs/naf.md, "In a rule antecedent".

(defn naf-antecedents-of
  "The `(unknown S)` antecedent literals of a raw rule *sentence* — for the checks
  that run before a rule is stored as a sentex (stratification)."
  [rule-sentence]
  (filter sx/unknown? (antecedents rule-sentence)))

(defn naf-antecedents
  "The `(unknown S)` antecedent literals of a stored rule — its negation-as-failure
  conditions."
  [sentex]
  (filter sx/unknown? (:antecedent sentex)))

(defn has-naf?
  "Does this rule carry any `unknown` antecedent?"
  [sentex]
  (boolean (seq (naf-antecedents sentex))))

(def different-flip-predicates
  "The predicates a fact can arrive on that flips a `(different …)` antecedent.  `different`
  is negation as failure over the equality closure and over the `indeterminate_term` category,
  whose members are exempt from the unique-name assumption.  A merge ends a difference and
  identifying an indeterminate term starts one, so a rule reading `different` owes a re-check
  in both directions.  A subkind of the category needs no entry, since
  `special/recheck-on-predicate` fans a predicate up its `genls-global` closure.  `genl` is here
  because the edge makes a kind indeterminate; a skolem is not, since its membership is minted.
  This is the set `checks/negative-predicates` runs the stratification edge to."
  '#{rewriteOf sameAs equals indeterminate_term genl})

(defn different-antecedents
  "The `(different …)` antecedent literals of a stored rule — its unique-name conditions,
  which read the equality closure and the `indeterminate_term` category rather than a fact
  the justification names."
  [sentex]
  (filter #(= 'different (nm/functor %)) (:antecedent sentex)))

(defn has-different?
  "Does this rule carry a `(different …)` antecedent?"
  [sentex]
  (boolean (seq (different-antecedents sentex))))

(defn watched-literals
  "The literals a re-check watches for query literal `q`, an `unknown` antecedent's query
  or an `exceptWhen` conjunct: each query-operator frame peeled, recursively, to what it
  reads (an `unknown`'s conjuncts, a `thereExists`'s body, a `forall`'s desugared NAF, an
  aggregate's census body, an `and`'s conjuncts), and anything else as itself.  No sentex
  is stored under a query operator's functor, so no fact arrives on one.  A `not` frame is
  not peeled, because `special/recheck-on-sentence` keys an arriving `(not S)` under `not`
  too (docs/naf.md, \"`S` may be a conjunction\")."
  [q]
  (cond
    (sx/unknown? q)      (mapcat watched-literals (sx/naf-query-conjuncts q))
    (sx/there-exists? q) (watched-literals (nth q 2))
    ;; a nested one, which no entry point desugars: what it reads is its NAF form's
    (and (sx/forall? q) (sx/implies? (nth q 2))) (watched-literals (sx/desugar-forall-literal q))
    (sx/aggregate? q)    (watched-literals (sx/aggregate-body q))
    (sx/conjunction? q)  (mapcat watched-literals (sx/conjuncts q))
    :else                [q]))

(defn watched-predicates
  "The predicates a re-check keys `queries` under — `watched-literals` of each, then its
  functor.  What `exceptWhen`'s three registration sites and the stratification graph
  read of an exception's conjuncts, and what `naf-predicates` reads of an `unknown`
  antecedent's."
  [queries]
  (keep nm/functor (mapcat watched-literals queries)))

(defn- naf-queries-of
  "The query literals one `(unknown …)` antecedent is watched by: `watched-literals` of
  every conjunct."
  [unk]
  (mapcat watched-literals (sx/naf-query-conjuncts unk)))

(defn naf-predicates-of
  "The predicates a raw rule *sentence*'s `unknown` antecedents mention, for the
  stratification check on a rule not yet stored."
  [rule-sentence]
  (keep nm/functor (mapcat naf-queries-of (naf-antecedents-of rule-sentence))))

(defn naf-predicates
  "The predicates a stored rule's `unknown` antecedents mention: its keys in the
  `[:exception-index …]` re-check index."
  [sentex]
  (keep nm/functor (mapcat naf-queries-of (naf-antecedents sentex))))

(defn naf-queries
  "The inner query literals of a rule's `unknown` antecedents (`naf-queries-of`), for
  the settle-time firing filter."
  [sentex]
  (mapcat naf-queries-of (naf-antecedents sentex)))

;; ---- aggregation: a rule antecedent that counts --------------------------
;; An aggregate antecedent takes `unknown`'s re-check index and negative edges.
;; See docs/aggregate.md, "Maintenance".

(defn aggregate-antecedents-of
  "The aggregate antecedent literals of a raw rule *sentence*, for the checks that run
  before it is stored."
  [rule-sentence]
  (filter sx/aggregate? (antecedents rule-sentence)))

(defn aggregate-antecedents
  "The aggregate antecedent literals of a stored rule."
  [sentex]
  (filter sx/aggregate? (:antecedent sentex)))

(defn has-aggregate?
  "Does this rule carry any aggregate antecedent?"
  [sentex]
  (boolean (seq (aggregate-antecedents sentex))))

(defn aggregate-queries
  "The body queries of a rule's aggregate antecedents, whole, for the settle-time firing
  filter.  None is ground, so the filter keeps every firing of an aggregate rule.  A
  reader that needs the conjuncts peels them with `watched-literals`."
  [sentex]
  (map sx/aggregate-body (aggregate-antecedents sentex)))

(defn aggregate-predicates-of
  "The predicates a raw rule *sentence*'s aggregate bodies mention, one per conjunct
  (`watched-literals`): the stratification graph's negative-edge keys and the re-check
  index's keys."
  [rule-sentence]
  (watched-predicates (aggregate-antecedents-of rule-sentence)))

(defn aggregate-predicates
  "The predicates a stored rule's aggregate bodies mention."
  [sentex]
  (watched-predicates (aggregate-antecedents sentex)))

(defn condition-queries-of
  "The queries a raw rule *sentence*'s re-check conditions read: every conjunct of its
  `unknown` antecedents, and its aggregate antecedents, which `watched-literals` peels to
  their census bodies.  The closed-extent, separation-denial and negates-denial re-check
  keys of a rule are read off these."
  [rule-sentence]
  (concat (mapcat sx/naf-query-conjuncts (naf-antecedents-of rule-sentence))
          (aggregate-antecedents-of rule-sentence)))

;; ---- a closed extent: `(not (P …))` read as negation as failure ----------
;; The structural half; the callers pass the taxonomy that says whether a grant is in
;; force.  See docs/naf.md, "Under the grant, a negative antecedent is NAF".

(defn negative-literal?
  "Is `a` a `(not (P …))` literal with a flat, symbol-headed body — the form a closed
  extent can be read over?"
  [a]
  (and (sequential? a) (= 2 (count a)) (= 'not (first a))
       (let [b (second a)] (and (sequential? b) (symbol? (first b))))))

(defn closed-negative-antecedents
  "The `(not L)` antecedents of `antes` every variable of which a generator antecedent
  binds: the only negative literals a closed extent reads as negation as failure."
  [antes]
  (let [gens  (remove #(or (sx/unknown? %) (sx/deferred-literal? %) (negative-literal? %))
                      antes)
        bound (into #{} (mapcat sx/free-vars) gens)]
    (filterv #(and (negative-literal? %) (every? bound (sx/free-vars %))) antes)))

(defn closed-extent-declared?
  "Does `tx` declare a closed extent on `pred` in any context, by
  `closed_extent_predicate` or by a `closedExtentForArg` of any position and value?  The
  join, the re-check index and the stratification graph read this over-approximation;
  derive time decides each selected literal in the conclusion's context."
  [tx pred]
  (or (tax/has-prop? tx :closed-extent pred)
      (tax/has-prop? tx :closed-extent-arg pred)))

(defn closed-extent-antecedents
  "The closed negative antecedents of `antes` whose predicate `tx` declares a closed
  extent (`closed-extent-declared?`), unscoped.  Two set reads and `[]` when the KB
  declares no closed extent."
  [tx antes]
  (if (and (empty? (tax/props tx :closed-extent)) (empty? (tax/props tx :closed-extent-arg)))
    []
    (filterv #(closed-extent-declared? tx (nm/functor (second %)))
             (closed-negative-antecedents antes))))

(defn closed-extent-predicates-of
  "The predicates inside a raw rule *sentence*'s closed-extent negative antecedents: its
  re-check keys and its negative edges."
  [tx rule-sentence]
  (keep #(nm/functor (second %)) (closed-extent-antecedents tx (antecedents rule-sentence))))

(defn closed-extent-query-predicates
  "The predicates of the `(not (P …))` literals a re-check watches in `queries`
  (`watched-literals`) on which `tx` declares a closed extent (`closed-extent-declared?`).
  These are the extra re-check keys and negative edges of a closed-extent negative inside
  an `unknown` antecedent, an aggregate body or an `exceptWhen` query: the literal is
  posted under `not`, and
  a `(P …)` arriving or leaving moves it while posting under `P` alone."
  [tx queries]
  (distinct (for [l     (mapcat watched-literals queries)
                  :when (negative-literal? l)
                  :let  [p (nm/functor (second l))]
                  :when (closed-extent-declared? tx p)]
              p)))

(defn closed-extent-recheck-predicates-of
  "The re-check keys a raw rule *sentence*'s closed-extent negatives post it under, and
  its negative edges on them: the antecedents' (`closed-extent-predicates-of`) and those
  nested in its `unknown` antecedents and aggregate bodies (`condition-queries-of`,
  `closed-extent-query-predicates`)."
  [tx rule-sentence]
  (distinct (concat (closed-extent-predicates-of tx rule-sentence)
                    (closed-extent-query-predicates tx (condition-queries-of rule-sentence)))))

(defn separation-denial-predicates
  "The types a separation's denial can move a negated literal of `queries` on, as the
  re-check index's extra keys: for each `(not (T …))` a re-check watches
  (`watched-literals`) with a unary `T`, every type a declaration separates `T` from
  (`tax/separating-partners`, read unscoped with no exception, a superset over every
  reader).  `provers/DisjointnessNegationProver` answers `(not (T x))` from a membership
  `(S x)` of a type below one of them, and the trigger fans an arriving `(S x)` out to
  `S`'s supertypes (`special/recheck-on-predicate`), so a rule posted under them is
  re-checked when such a membership arrives or leaves.  Empty for a `T` no separation
  reaches."
  [tx queries]
  (distinct
   (for [l     (mapcat watched-literals queries)
         :when (and (seq? l) (= 'not (first l)))
         :let  [b (second l)]
         :when (and (seq? b) (= 2 (count b)) (symbol? (first b)) (tax/separable? tx (first b)))
         p     (sort (tax/separating-partners tx (first b) nil (constantly false)))]
     p)))

(defn separation-denial-predicates-of
  "`separation-denial-predicates` of a raw rule *sentence*'s `unknown` antecedents and
  aggregate bodies (`condition-queries-of`): the extra keys the re-check index posts the
  rule under beside `recheck-predicates` (`special/index-rule-sentex`), a taxonomy read as
  `closed-extent-predicates-of` is."
  [tx rule-sentence]
  (separation-denial-predicates tx (condition-queries-of rule-sentence)))

(defn negates-denial-predicates
  "The predicates a `negates` declaration's denial can move a negated literal of
  `queries` on, as the re-check index's extra keys: for each `(not (P …))` a re-check
  watches (`watched-literals`), every predicate declared to negate `P` or a supertype of
  it (`tax/negates-over`, unscoped, a superset over every reader).
  `provers/NegatesProver` answers `(not (P …))` from a believed tuple of such a
  predicate's spec subtree, and the trigger fans the tuple up to the predicate
  (`special/recheck-on-predicate`).  Empty, off one map read, on a KB declaring no
  `negates`."
  [tx queries]
  (if-not (tax/negates? tx)
    ()
    (distinct
     (for [l     (mapcat watched-literals queries)
           :when (negative-literal? l)
           [_ r] (sort (tax/negates-over tx (first (second l))))]
       r))))

(defn negates-denial-predicates-of
  "`negates-denial-predicates` of a raw rule *sentence*'s `unknown` antecedents and
  aggregate bodies, as `separation-denial-predicates-of` reads them."
  [tx rule-sentence]
  (negates-denial-predicates tx (condition-queries-of rule-sentence)))

(defn has-nested-naf?
  "Does an `unknown` query of this rule carry a nested `(unknown …)` or an aggregate, so
  that an arriving fact can release its block (docs/naf.md, \"`forall` is sugar for a
  nested `unknown`\")?"
  [sentex]
  (boolean (some (fn [unk] (sx/some-form #(or (sx/unknown? %) (sx/aggregate? %))
                                         (second unk)))
                 (naf-antecedents sentex))))

(defn exception-arrival-releasable?
  "Can an arriving fact both impose and lift the exception `queries` (a rule's
  `provers/rule-exceptions`)?  An exception blocks while it holds, so a literal it reads
  under an even number of `unknown`s is one an arrival makes hold, and one under an odd
  number is one an arrival makes fail.  With both, a block one arrival imposed is swept
  rather than refused, and a later arrival can lift it with no refusal to read, so the
  rule is owed a re-join as `arrival-releasable?` owes one.  An aggregate moves either way
  on its own.  An exception of one polarity is not: a block an arrival imposes is never
  lifted by one, and a block a retraction imposed is re-chained by the sweep."
  [queries]
  (let [pols (volatile! #{})]
    (letfn [(walk [q pos?]
              (cond
                (sx/unknown? q)      (run! #(walk % (not pos?)) (sx/naf-query-conjuncts q))
                (sx/there-exists? q) (walk (nth q 2) pos?)
                (sx/conjunction? q)  (run! #(walk % pos?) (sx/conjuncts q))
                (sx/aggregate? q)    (vswap! pols conj :aggregate)
                :else                (vswap! pols conj pos?)))]
      (run! (fn [conjs] (run! #(walk % true) conjs)) queries))
    (or (contains? @pols :aggregate) (and (contains? @pols true) (contains? @pols false)))))

(defn arrival-releasable?
  "Can an arriving fact *release* one of this rule's re-check conditions rather than
  only impose one?  True for an **aggregate** and for a **nested** NAF.  Read by the
  settle loop, which owes such a rule a re-join, and by the `genlCx` and equality edge
  triggers, which skip their firing-side narrowing for it (docs/exceptions.md,
  \"Re-chaining what was released, not what was touched\")."
  [sentex]
  (or (has-aggregate? sentex) (has-nested-naf? sentex)))

(defn recheck-predicates
  "The predicates whose change must re-check this rule for its own re-check conditions: the
  predicates its `unknown` antecedents and aggregate bodies mention, plus
  `different-flip-predicates` where it reads `different`.  A closed-extent negative antecedent
  adds its own (`closed-extent-predicates-of`), since that is a taxonomy read.  An exceptWhen
  exception is registered under its rule by the meta-sentex's own indexing.  This is the key
  set the `[:exception-index …]` index posts a rule under.  Each kind reads what the KB
  believes at firing time, so a fact arriving on those predicates brings the firing back for
  re-decision.  A `different` antecedent holds by the absence of a merge and has no support
  handle, so the re-check is the only way to withdraw the firing (docs/predall.md)."
  [sentex]
  (distinct (concat (naf-predicates sentex)
                    (aggregate-predicates sentex)
                    (when (has-different? sentex) different-flip-predicates))))

(defn nonempty-recheck-predicates
  "`[nonempty]` for a rule with a positive antecedent on `nonempty`, else nil: the key the
  re-check index posts the rule under.  `NonemptyProver` computes the antecedent from the
  believed members of its type, so every membership re-checks the rule
  (`special/recheck-nonempty-readers`) and no predicate of the rule names them."
  [sentex]
  (when (some #(and (sequential? %) (= 'nonempty (first %))) (:antecedent sentex))
    ['nonempty]))

(defn rechecked?
  "Does this rule carry a re-check condition of its **own** — an `unknown` antecedent, an
  aggregate, or a `different` antecedent?  The check on registering it in the re-check
  index; an exceptWhen exception is registered by its own meta-sentex and is not read off
  the rule."
  [sentex]
  (or (has-naf? sentex) (has-aggregate? sentex) (has-different? sentex)))

;; ---- what the join cannot do, and the placement can ----------------------
;; See docs/aggregate.md, "Comparing the count".

(defn post-join-literals
  "The antecedent literals evaluated **after** the join, in written order: every
  aggregate, plus every deferred literal reading a variable an aggregate writes or one
  of these writes in turn, so an `(evaluate ?d (+ ?n 1))` carries a later `(lessThan ?d
  9)` along.  `unknown` is not here: it binds nothing and is evaluated per placement as
  `:naf`.  Asked on every join, so a rule without an aggregate costs one `some`."
  [antes]
  (if-not (some sx/aggregate? antes)
    []
    (:out (reduce (fn [{:keys [produced out] :as acc} a]
                    (if (or (sx/aggregate? a)
                            (and (sx/deferred-literal? a)
                                 (not (sx/unknown? a))
                                 (some produced (sx/deferred-input-vars a))))
                      {:produced (into produced (sx/deferred-output-vars a))
                       :out      (conj out a)}
                      acc))
                  {:produced #{} :out []}
                  antes))))

(defn post-join-antecedents
  "`post-join-literals` over a stored rule's antecedents."
  [sentex]
  (post-join-literals (vec (:antecedent sentex))))

(def ^:private direction-wrapper
  "The surface `set/*Rule` wrapper each direction rewraps and exports to.  `:backward` is
  the default (a bare implies), so it needs no wrapper; `:both` and `:forward` both mean
  forward + backward and write as `set/forwardRule`; `:forward-only` (forward, never
  backward) writes `set/forwardOnlyRule`; `:lazy-forward` writes `set/lazyForwardRule`;
  `:inert` writes `set/inertRule`."
  '{:forward set/forwardRule :both set/forwardRule
    :forward-only set/forwardOnlyRule :lazy-forward set/lazyForwardRule :inert set/inertRule})

(defn wrap-direction
  "Express `direction` as the corresponding `set/*Rule` wrapper around `sentence`.
  `:backward` needs no wrapper — a bare `(implies …)` is backward by default."
  [sentence direction]
  (if-let [w (direction-wrapper direction)] (list w sentence) sentence))

(defn inner-rule
  "The bare `(implies …)` inside any virtual rule wrappers (`set/*Rule` and
  `exceptWhen`, which may nest in any order — a defeasible forward rule with an
  exception).  The direction / default / assumption wrappers become record fields and
  the exceptWhen becomes a meta-sentex, so the checks and the stored sentence both work
  on this.

  A `forall` antecedent is desugared here too (`sentex/desugar-forall-rule`), so every
  pre-storage check — range restriction, closure, quantifier locality, stratification —
  reads the nested NAF the constructor will store rather than the sugar it was written
  with.  A stored rule holds no `forall`, so this is the identity on one."
  [sentence]
  (let [[_ _ _ _ _ inner] (sx/peel-rule-wrapper sentence)]
    (sx/desugar-forall-rule inner)))

;; ---- cardinality bounds on choice heads ----------------------------------
;; `(asp/atMost k ?v pattern)` bounds how many of the ground choice heads matching
;; `pattern` a solve may set true — counting over the projected variable `?v` and
;; grouping by the pattern's other variables, the way `agg/count` projects a variable.
;; It is not an `(implies …)` rule, so it is normalized (below) into an ordinary
;; hard/soft constraint rule whose consequent MARKER carries the operator and the bound:
;;   (asp/atMost 6 ?c (empireBuild ?c transport))
;;     -> (set/hardConstraint (implies (empireBuild ?c transport) (cardAtMost 6 ?c)))
;; Everything downstream then treats it as the constraint rule it is — the trie key, the
;; codec, and subsumption all distinguish `atMost 6` from `atMost 3` and from a bare twin
;; because k and the operator ride the stored consequent, so none of them need a new arm.
;; Only `solve-context` reads the marker back (`cardinality-of`) and grounds it to ONE
;; solver cardinality atom rather than the `C(n, k+1)` subset nogoods a hand-written
;; encoding needs (docs/solving.md).  A weighted bound `(asp/atMostSum k ?w ?v body)`
;; rides `(sumAtMost k ?w ?v)` the same way, its body a conjunction like a minimize's.

(def ^:private sum-markers
  "The consequent-marker functors a normalized weighted bound carries."
  '#{sumAtMost sumAtLeast})

(def cardinality-markers
  "The consequent-marker functors a normalized cardinality rule carries, weighted or not."
  (into '#{cardAtMost cardAtLeast} sum-markers))

(def ^:private cardinality-wrappers
  "The eight surface wrappers → `[marker constraint-class]`."
  '{asp/atMost         [cardAtMost  :hard]
    asp/atLeast        [cardAtLeast :hard]
    asp/softAtMost     [cardAtMost  :soft]
    asp/softAtLeast    [cardAtLeast :soft]
    asp/atMostSum      [sumAtMost   :hard]
    asp/atLeastSum     [sumAtLeast  :hard]
    asp/softAtMostSum  [sumAtMost   :soft]
    asp/softAtLeastSum [sumAtLeast  :soft]})

(def ^:private cardinality-rewrap
  "The inverse of `cardinality-wrappers`: `[marker constraint-class]` → surface wrapper,
  so `rewrap` restores the authored form on export."
  (set/map-invert cardinality-wrappers))

;; ---- minimize objectives and soft-constraint priorities ------------------
;; `asp/minimize` and a priority-tagged `set/softConstraint` are the answer-set
;; *objective* surface — the weak-constraint counterpart to the hard/soft nogoods.  Like
;; the cardinality bounds they normalize into an internal `set/softConstraint` whose
;; consequent MARKER carries the extra operands (a priority level, and for a minimize the
;; per-head weight variable), so nothing downstream needs a new rule arm: `solve-context`
;; reads the marker back (`soft-cost-of`), and `edge/translate` already keys a minimize's
;; objective level off the nogood's `:priority` and its per-literal weight off `[[v w]]`.
;; A soft with no priority stays level-1 (`:priority 1`), unit weight, as every soft was
;; before.  Distinct priorities become distinct lexicographic minimize levels, so a
;; lower-priority tiebreak breaks ties among the higher objective's optima without the
;; solver churning a plateau of equal-cost models (docs/solving.md).

(def minimize-marker
  "The consequent-marker functor a normalized `asp/minimize` carries:
  `(minimizeCost <priority> <weight-var>)`."
  'minimizeCost)

(def soft-priority-marker
  "The consequent-marker functor a normalized priority-tagged `set/softConstraint`
  carries: `(softPriority <priority> <the authored consequent>)`."
  'softPriority)

(def minimize-wrapper 'asp/minimize)

(def ^:private priority-constraint-wrappers
  "The constraint wrappers a leading-integer priority may tag."
  '#{set/softConstraint set/hardConstraint})

(defn minimize-surface?
  "Is `sentence` a `(asp/minimize priority ?weight body)` surface form?"
  [sentence]
  (boolean (and (sequential? sentence) (seq sentence)
                (= minimize-wrapper (first sentence)))))

(defn soft-priority-surface?
  "Is `sentence` a priority-tagged constraint wrapper — a leading positive integer before
  the rule, `(set/softConstraint P (implies …))`?"
  [sentence]
  (boolean (and (sequential? sentence) (= 3 (count sentence))
                (contains? priority-constraint-wrappers (first sentence))
                (integer? (second sentence)))))

(defn cardinality-surface?
  "Is `sentence` a `(asp/atMost …)` / `(asp/atLeast …)` surface form (or a soft twin)?"
  [sentence]
  (boolean (and (sequential? sentence) (seq sentence)
                (contains? cardinality-wrappers (first sentence)))))

(defn normalize-cardinality
  "Rewrite a `(asp/atMost k ?v pattern)` surface form into the internal constraint rule
  `(set/hardConstraint (implies pattern (cardAtMost k ?v)))`, and a weighted
  `(asp/atMostSum k ?w ?v body)` into `(set/hardConstraint (implies body (sumAtMost k ?w
  ?v)))` — the soft twins into `set/softConstraint`.  The identity on anything else, so
  `assert` and `check` apply it to every sentence.

  Refuses a malformed bound here, at the entry point, before storage: `k` a non-negative
  integer, `?v` (and `?w`, distinct from it) a variable the pattern binds, `pattern` a
  literal or, for a weighted bound, a conjunction.  The range check that runs on the
  rewritten rule then holds the marker's variables to the antecedent."
  [sentence]
  (if-not (cardinality-surface? sentence)
    sentence
    (let [[marker klass] (cardinality-wrappers (first sentence))
          sum?           (contains? sum-markers marker)
          [wrapper k & more] sentence
          [w v pattern]  (if sum? more (cons nil more))]
      (when-not (= (if sum? 5 4) (count sentence))
        (throw (ex-info (str "a cardinality bound is (" wrapper
                             (if sum? " k ?weight ?counted body" " k ?counted pattern")
                             "); got " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence})))
      (when (and sum? (not (and (sx/variable? w) (not= w v)
                                (sequential? pattern) (some #{w} (sx/form-vars pattern)))))
        (throw (ex-info (str "a weighted bound's weight slot must be a variable the body binds,"
                             " distinct from the counted one; got " (pr-str w) " in "
                             (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :weight w})))
      (when-not (and (integer? k) (not (neg? k)))
        (throw (ex-info (str "a cardinality bound's count must be a non-negative integer; got "
                             (pr-str k) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :count k})))
      (when-not (sx/variable? v)
        (throw (ex-info (str "a cardinality bound's counted slot must be a variable; got "
                             (pr-str v) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :counted v})))
      (when-not (and (sequential? pattern)
                     (some #{v} (sx/form-vars pattern)))
        (throw (ex-info (str "a cardinality bound's counted variable " (pr-str v)
                             " must appear in the pattern " (pr-str pattern))
                        {:type :not-well-formed :sentence sentence :counted v :pattern pattern})))
      (list (get {:hard 'set/hardConstraint :soft 'set/softConstraint} klass)
            (if sum?
              (list 'implies pattern (list marker k w v))
              (sx/rule-sentence [pattern] (list marker k v)))))))

(defn normalize-soft-priority
  "Rewrite a priority-tagged `(set/softConstraint P (implies body C))` into the internal
  `(set/softConstraint (implies body (softPriority P C)))`, moving the priority level onto
  the consequent marker so the split, the checks, and the store see an ordinary soft
  constraint.  The identity on anything else.

  Refuses a malformed form here, before storage: the priority a positive integer, the
  wrapper `set/softConstraint` (a hard constraint is an integrity constraint, never
  minimized, so a priority on it is meaningless), and the body a rule."
  [sentence]
  (if-not (soft-priority-surface? sentence)
    sentence
    (let [[wrapper priority inner] sentence]
      (when-not (= 'set/softConstraint wrapper)
        (throw (ex-info (str "a priority applies only to a minimized soft constraint; "
                             (pr-str wrapper) " is a hard integrity constraint with no "
                             "objective level: " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence})))
      (when-not (pos-int? priority)
        (throw (ex-info (str "a soft constraint's priority must be a positive integer; got "
                             (pr-str priority) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :priority priority})))
      (when-not (and (sx/implies? inner) (= 3 (count inner)))
        (throw (ex-info (str "a priority-tagged soft constraint wraps a rule; got "
                             (pr-str inner) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence})))
      (list 'set/softConstraint
            (list 'implies (second inner)
                  (list soft-priority-marker priority (nth inner 2)))))))

(defn normalize-minimize
  "Rewrite `(asp/minimize priority ?weight body)` into the internal soft constraint
  `(set/softConstraint (implies body (minimizeCost priority ?weight)))` — a soft whose
  choice-head body is penalized by the data weight `?weight` at `priority`, so the
  objective at that level sums `?weight` over every chosen head.  `body` names a choice
  head and binds `?weight` off a background fact — the weak-constraint idiom
  `#minimize{ W@P, head : head-facts, weight-fact }`.  The identity on anything else.

  Refuses a malformed form: the priority a positive integer, `?weight` a variable the body
  binds, `body` a literal or conjunction."
  [sentence]
  (if-not (minimize-surface? sentence)
    sentence
    (let [[_ priority w body] sentence]
      (when-not (= 4 (count sentence))
        (throw (ex-info (str "a minimize is (asp/minimize priority ?weight body); got "
                             (pr-str sentence))
                        {:type :not-well-formed :sentence sentence})))
      (when-not (pos-int? priority)
        (throw (ex-info (str "a minimize's priority must be a positive integer; got "
                             (pr-str priority) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :priority priority})))
      (when-not (sx/variable? w)
        (throw (ex-info (str "a minimize's weight slot must be a variable; got " (pr-str w)
                             " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :weight w})))
      (when-not (and (sequential? body)
                     (some #{w} (sx/form-vars body)))
        (throw (ex-info (str "a minimize's weight variable " (pr-str w) " must appear in "
                             "the body " (pr-str body))
                        {:type :not-well-formed :sentence sentence :weight w :body body})))
      (list 'set/softConstraint
            (list 'implies body (list minimize-marker priority w))))))

(def internal-markers
  "The consequent-marker functors the answer-set surfaces normalize into.  No authored
  sentence spells one: `refuse-internal-marker` refuses a constraint rule that does."
  (conj cardinality-markers minimize-marker soft-priority-marker))

(def ^:private internal-marker-surface
  "The surface form to write in place of each internal marker, for the refusal message."
  '{cardAtMost   "(asp/atMost k ?counted pattern) or (asp/softAtMost …)"
    cardAtLeast  "(asp/atLeast k ?counted pattern) or (asp/softAtLeast …)"
    sumAtMost    "(asp/atMostSum k ?weight ?counted body) or (asp/softAtMostSum …)"
    sumAtLeast   "(asp/atLeastSum k ?weight ?counted body) or (asp/softAtLeastSum …)"
    minimizeCost "(asp/minimize priority ?weight body)"
    softPriority "(set/softConstraint priority (implies body marker))"})

(defn- authored-constraint-consequents
  "The consequent literals of the rule a constraint wrapper holds, as written: through any
  direction, default or assumption wrapper around the constraint wrapper and past a leading
  priority inside it, one per conjunct of a conjunctive consequent.  Empty for every other
  sentence."
  [sentence]
  (let [peel? (fn [s] (and (sequential? s) (= 2 (count s))
                           (let [h (first s)]
                             (or (contains? sx/rule-direction-wrappers h)
                                 (= sx/default-rule-wrapper h)
                                 (= sx/assumption-rule-wrapper h)))))
        s     (loop [s sentence] (if (peel? s) (recur (second s)) s))]
    (if-not (and (sequential? s) (seq s) (contains? sx/constraint-rule-wrappers (first s)))
      []
      (let [inner (last s)
            c     (when (and (sx/implies? inner) (= 3 (count inner))) (nth inner 2))]
        (if (and (sequential? c) (= 'and (first c))) (rest c) (some-> c vector))))))

(defn refuse-internal-marker
  "Throw `:not-well-formed` when a constraint rule's authored consequent is one of the
  `internal-markers`; return `sentence` unchanged otherwise.  A hand-written marker skips
  the operand checks its surface form runs, and the solve reads each operand as a count or
  an objective level, so a symbol operand such as `(cardAtMost ?a ?c)` would reach
  arithmetic and throw a bare `ClassCastException` out of `do/label`."
  [sentence]
  (if-let [m (some #(when (and (sequential? %) (contains? internal-markers (first %))) %)
                   (authored-constraint-consequents sentence))]
    (throw (ex-info (str (pr-str (first m)) " is the internal marker a solve surface "
                         "normalizes into, not an authored consequent; write "
                         (internal-marker-surface (first m)) " instead: " (pr-str sentence))
                    {:type :not-well-formed :sentence sentence :marker (first m)}))
    sentence))

(defn normalize-solve-surface
  "Rewrite the answer-set surface forms — cardinality bounds, priority-tagged soft
  constraints, and minimize objectives — into their internal constraint-rule forms, so
  the split, the checks, and the store all see ordinary constraint rules.  Each rewrite is
  the identity off its own surface, and the three surfaces are disjoint, so the order does
  not matter; the identity on every other sentence.  A constraint rule that spells an
  internal marker itself is refused first (`refuse-internal-marker`)."
  [sentence]
  (-> sentence refuse-internal-marker
      normalize-cardinality normalize-soft-priority normalize-minimize))

(defn cardinality-of
  "The cardinality bound a stored constraint rule expresses — `{:op :at-most|:at-least
  :k int :counted ?v}` — read off the consequent marker `(cardAtMost k ?v)` /
  `(cardAtLeast k ?v)`, plus `:weight ?w` off a weighted `(sumAtMost k ?w ?v)` /
  `(sumAtLeast k ?w ?v)`, or nil for an ordinary constraint rule."
  [sentex]
  (let [c (:consequent sentex)]
    (when (and (sequential? c) (contains? cardinality-markers (first c)))
      (if (contains? sum-markers (first c))
        {:op      (if (= 'sumAtMost (first c)) :at-most :at-least)
         :k       (nth c 1)
         :weight  (nth c 2)
         :counted (nth c 3)}
        {:op      (if (= 'cardAtMost (first c)) :at-most :at-least)
         :k       (second c)
         :counted (nth c 2)}))))

(defn soft-cost-of
  "Read the objective level and per-head weight a **ground** soft-constraint marker
  carries, for `solve-context` to put on the nogood — the counterpart to `cardinality-of`
  for the minimize/priority surface:

    `(minimizeCost p w)` → `{:priority p :weight w :marker marker}` — a minimize term over
                           the chosen head, weighted `w` at level `p`;
    `(softPriority p m)` → `{:priority p :marker m}` — the authored soft `m`, at level `p`,
                           unit weight;
    anything else        → `{:priority 1 :marker marker}` — an ordinary soft, level 1.

  `:marker` is the value to name the nogood by (the authored one, unwrapped)."
  [marker]
  (cond
    (and (sequential? marker) (= minimize-marker (first marker)))
    {:priority (nth marker 1) :weight (nth marker 2) :marker marker}
    (and (sequential? marker) (= soft-priority-marker (first marker)))
    {:priority (nth marker 1) :marker (nth marker 2)}
    :else
    {:priority 1 :marker marker}))

;; ---- polycanonicalization: split a conjunctive consequent ----------------

(defn- conjunctive? [c] (and (sequential? c) (= 'and (first c))))

(defn rewrap
  "Put the direction / default / assumption / constraint wrappers a rule was written with
  back around `sentence`: the inverse of `sx/peel-rule-wrapper`, since the wrappers ride the
  record and not the stored sentence.  The arguments are the wrappers as `peel-rule-wrapper`
  reads them: a polycanonicalized conjunct keeps the mode of its rule, and `split-exceptWhen`
  restores the qualified rule's other wrappers.  `rewrap-sentex` reads them off a stored
  record.  An exceptWhen is not among them (`split-exceptWhen`).  A cardinality constraint
  rule restores its authored surface, `(asp/atMost k ?v pattern)`, instead of the internal
  `set/hardConstraint (implies …)` form (`normalize-cardinality`).  `solve?` puts
  `set/solveRule` outermost, around the direction wrapper."
  ([sentence direction defeasible assumption constraint]
   (rewrap sentence direction defeasible assumption constraint false))
  ([sentence direction defeasible assumption constraint solve?]
   (let [conseq (when (sx/implies? sentence) (consequent sentence))
         cf     (when (sequential? conseq) (first conseq))]
     (cond
       ;; a minimize restores its authored `(asp/minimize p ?w body)` — the whole
       ;; antecedent form is the body, conjunctive or not
       (and constraint (= minimize-marker cf))
       (let [[_ p w] conseq]
         (list minimize-wrapper p w (second sentence)))
       ;; a priority-tagged soft restores `(set/softConstraint p (implies body C))`
       (and constraint (= soft-priority-marker cf))
       (let [[_ p m] conseq]
         (list 'set/softConstraint p (list 'implies (second sentence) m)))
       ;; a weighted bound restores `(asp/atMostSum k ?w ?v body)`, the whole antecedent
       ;; form its body, as a minimize does
       (and constraint (contains? sum-markers cf))
       (let [[marker k w v] conseq]
         (list (cardinality-rewrap [marker constraint]) k w v (second sentence)))
       ;; a cardinality bound restores its authored surface (`normalize-cardinality`)
       (and constraint (contains? cardinality-markers cf))
       (let [[marker k v] conseq]
         (list (cardinality-rewrap [marker constraint]) k v (first (antecedents sentence))))
       :else
       (cond-> sentence
         defeasible      (->> (list sx/default-rule-wrapper))
         assumption      (->> (list sx/assumption-rule-wrapper))
         constraint      (->> (list (get {:hard 'set/hardConstraint :soft 'set/softConstraint}
                                         constraint)))
         direction       (wrap-direction direction)
         solve?          (->> (list sx/solve-rule-wrapper)))))))

(defn rewrap-sentex
  "`rewrap` with the wrappers read off the stored rule sentex `sx` — the form its author
  wrote, around `sentence` (its canonical or its originalized sentence).  A `:derive`
  rule gets its direction wrapper (none for backward, the default), `set/defaultRule`
  when defeasible and `set/solveRule` when a solve runs it; a choice or constraint rule gets its head wrapper
  alone, since the wrapper stack refuses anything beside it."
  [sentence sx]
  (let [effect (:effect sx)]
    (if (= :derive effect)
      (rewrap sentence (sx/engines-direction (:engines sx)) (:defeasible sx) nil nil
              (contains? (:engines sx) :solve))
      (rewrap sentence nil nil (= :choose effect) (sx/effect-constraint effect)))))

(defn expand-consequent
  "Polycanonicalize a rule that concludes a conjunction into one rule per conjunct,
  preserving any virtual wrapper (default / forward / backward / inert / assumptionRule).
  A rule `(implies A (and C1 C2))` becomes `[(implies A C1) (implies A C2)]`; anything
  else (a non-rule, or a rule with a single consequent) returns `[sentence]` unchanged.

  Runs on a rule whose exceptWhen has already been split off (`split-exceptWhen`), so
  the exception is re-attached once per conjunct by the caller, against each conjunct's
  own handle."
  [sentence]
  (let [[dir def? _exc assum con inner] (sx/peel-rule-wrapper sentence)
        solve? (sx/solve-wrapped? sentence)]
    (if (and (rule-sentence? inner)
             (conjunctive? (consequent inner)) (seq (rest (consequent inner))))
      (let [as (antecedents inner)]
        (mapv #(rewrap (rule-sentence as %) dir def? assum con solve?) (rest (consequent inner))))
      [sentence])))

;; ---- polycanonicalization: distribute a disjunctive antecedent ----------
;; The antecedent twin of the conjunctive-consequent split above, and the same trick:
;; `or` never reaches the record.  `(implies (or A B) C)` is stored as the two rules
;; `(implies A C)` and `(implies B C)`, each an ordinary rule sentex with its own
;; handle, its own justifications and its own retraction — so nothing downstream of the
;; assert entry point has to know the connective exists.  The two splits compose: a rule that
;; disjoins its antecedent *and* conjoins its consequent stores the **product**
;; (`expand-rule`).  See docs/canonicalization.md.

(def max-alternatives
  "How many alternatives one rule may expand to.  A disjunctive antecedent is *stored*
  expanded, so the width is paid in handles, index entries and TMS nodes rather than at
  query time — and a nest of `or`s multiplies, so the cost of a typo is exponential in a
  sentence that still reads like one line.  Sixteen is the width past which a rule is
  better written as a type: assert a `genl` and one rule on the supertype, which is one
  handle however many members it covers."
  16)

(defn- distributes-or?
  "Does this antecedent form carry an `or` in a position the DNF distributes over —
  itself, or inside an `and` / `or` it nests in?  An `or` in an *argument* slot is a
  term, not a connective frame, and is left where it stands."
  [form]
  (cond
    (sx/disjunction? form) true
    (conjunctive? form)    (boolean (some distributes-or? (rest form)))
    :else                  false))

(defn- alternative-count
  "How many DNF alternatives one antecedent form yields — a sum over an `or`'s
  disjuncts, a product over a distributing `and`'s conjuncts, one for a literal.
  Arithmetic rather than a count of the expansion, so a rule far over the cap is
  refused without ever being materialized: `+'` and `*'` promote, so a nest deep enough
  to overflow a long still reports its own width."
  [form]
  (cond
    (sx/disjunction? form) (reduce +' 0 (map alternative-count (sx/disjuncts form)))
    (and (conjunctive? form) (distributes-or? form))
    (reduce *' 1 (map alternative-count (rest form)))
    :else 1))

(defn- antecedent-alternative-count
  "The number of rules a whole antecedent list expands to — the product of its members'."
  [antes]
  (reduce *' 1 (map alternative-count antes)))

(defn antecedent-alternatives
  "The DNF alternatives of an antecedent list, as `{:antecedents [...] :choices [...]}`
  in written order — `:antecedents` being that alternative's literals and `:choices` the
  disjuncts it took, which is what a refusal names when one alternative is the bad one.

  A disjunct that is itself compound contributes its *own* choices rather than being
  named whole, so the innermost disjunct is what a message points at: in
  `(or (and A (or B C)) D)` an alternative's choice is `B`, `C` or `D`, never the `and`."
  [antes]
  (letfn [(combine [xs ys]
            (for [x xs, y ys]
              {:antecedents (into (:antecedents x) (:antecedents y))
               :choices     (into (:choices x) (:choices y))}))
          (dnf [form]
            (cond
              (sx/disjunction? form)
              (for [d (sx/disjuncts form), alt (dnf d)]
                (if (seq (:choices alt)) alt (assoc alt :choices [d])))

              (and (conjunctive? form) (distributes-or? form))
              (reduce combine [{:antecedents [] :choices []}] (map dnf (rest form)))

              :else [{:antecedents [form] :choices []}]))]
    (reduce combine [{:antecedents [] :choices []}] (map dnf antes))))

(defn expand-antecedent
  "Polycanonicalize a rule whose antecedent disjoins into one rule per DNF alternative,
  preserving any virtual wrapper.  `(implies (or A B) C)` becomes `[(implies A C) (implies B
  C)]` and `(implies (and (or A B) D) C)` becomes `[(implies (and A D) C) (implies (and B D)
  C)]`.  Anything else, a non-rule, a rule with no `or`, or an `or` in an argument slot, returns
  `[sentence]`.

  Only the level written here is expanded: a generator's generated rule keeps its `or` until
  `chain/mint-rule` expands what it stores.  A rule the cap refuses and an empty `(or)` return
  `[sentence]` unexpanded, and `disjunction-problems` reports both from that form."
  [sentence]
  (let [[dir def? _exc assum con inner] (sx/peel-rule-wrapper sentence)
        solve? (sx/solve-wrapped? sentence)]
    (if (and (rule-sentence? inner) (some distributes-or? (antecedents inner)))
      (let [antes (antecedents inner)
            n     (antecedent-alternative-count antes)]
        (if (or (zero? n) (> n max-alternatives))
          [sentence]
          (mapv #(rewrap (rule-sentence (:antecedents %) (consequent inner))
                         dir def? assum con solve?)
                (antecedent-alternatives antes))))
      [sentence])))

(defn expand-rule
  "Both polycanonicalizations of a rule, composed: one rule per DNF alternative of the
  antecedent, and within each, one per conjunct of the consequent.  A rule that does
  neither returns `[sentence]`, so every caller can treat the result uniformly.

  The **product**, and in that order — alternatives outermost, conjuncts within — which
  is the order `assert` stores them and therefore the order an `exceptWhen` is
  re-attached along.  `(implies (or A B) (and C1 C2))` stores four rules."
  [sentence]
  (into [] (mapcat expand-consequent) (expand-antecedent sentence)))

(defn split-exceptWhen
  "Split an `(exceptWhen <query> <rule>)` assertion into `[exception inner]`.

  `exception` is the flattened conjunction of every exceptWhen wrapper (a vector of
  literals in the author's variable names, block-if-all-hold), and `inner` is what the
  exceptWhen qualifies: the wrapped rule with its exceptWhen(s) stripped but its
  direction / default / assumption wrappers intact, or the `(sentexHandle H)` a
  bare-handle exceptWhen named.  `[nil sentence]` when there is no exceptWhen.

  This is the layer at which an exceptWhen becomes a separate meta-sentex: the assert
  layer stores `inner` as the rule (or resolves the handle) and the exception as
  `(exceptWhen <aligned-query> (sentexHandle H))` against it."
  [sentence]
  (let [[dir def? exc assum con inner] (sx/peel-rule-wrapper sentence)]
    (if (seq exc)
      [(vec exc) (if (sx/sentex-handle? inner)
                   inner
                   (rewrap inner dir def? assum con (sx/solve-wrapped? sentence)))]
      [nil sentence])))

(defn exceptWhen-not-a-rule
  "The refusal an inline `(exceptWhen <query> X)` earns when X is not a rule, as a problem
  map, or nil.  An exception blocks a rule's conclusions, and a fact has none; `assert`
  throws it, `check` reports it and an import skips the frame."
  [exc inner]
  (when-not (rule-sentence? (inner-rule inner))
    {:type :not-well-formed :sentence inner :exception (vec exc)
     :message (str "exceptWhen qualifies a rule, and " (pr-str inner) " is not one: an"
                   " exception blocks what a rule concludes, and a fact concludes nothing")}))

;; ---- generators: a rule whose consequent is a rule -----------------------
;; `(implies <antes> (implies <inner-antes> <inner-conseq>))` — a **generator**, whose
;; firing generates the inner rule with its holes filled.  The scoping rule is
;; computed, not annotated: the inner rule's variables that its enclosing antecedents
;; also mention are **holes**, bound by the join and ground at mint; the rest are the
;; generated rule's own, and belong to it.
;;
;; The nesting is not capped.  A generated rule may itself be a generator, and then the
;; mint generates in turn — each level's firing grounds that level's holes and stores the
;; level below it.  One reading decides every level, because the scoping rule composes:
;; a variable belongs to the **outermost** level whose antecedents mention it, which is
;; the level whose firing makes it ground.  See docs/generators.md.

(defn generated-rule
  "The bare rule form a generator's `consequent` generates — the `(implies …)` inside
  whatever `set/*Rule` wrapper the author put on it — or nil when the consequent
  concludes a fact, which is every ordinary rule.

  The wrapper is peeled here and *kept* by the caller that mints: it sets the
  **generated** rule's direction, which is the only place a direction can be written for
  a rule nobody types out."
  [consequent]
  (let [inner (peek (sx/peel-rule-wrapper consequent))]
    (when (sx/implies? inner) inner)))

(defn generator?
  "Is this rule *sentence* a generator — does it conclude a rule?"
  [sentence]
  (some? (generated-rule (consequent (inner-rule sentence)))))

(defn generator-sentex?
  "Is this stored rule sentex a generator?  Read off the record's `:consequent`, which
  is where the canonicalized rule kept it."
  [sentex]
  (boolean (some-> (:consequent sentex) generated-rule)))

(defn holes
  "The variables a generator's generated rule takes from the firing — those its
  enclosing `antecedents` also mention, as a set.

  Computed rather than declared, which is the whole reason a generator needs no
  vocabulary of its own: sharing a variable name with the antecedents *is* how an
  author says \"fill this in\", and the remaining variables are the generated rule's own
  by the same token.  Two spellings cannot disagree, because there is only one.

  One level's question.  Under nesting each level asks it of the level below, and
  `nesting` carries the answers down as `:bound`."
  [antecedents generated]
  (let [ante-vars (into #{} (mapcat sx/form-vars antecedents))]
    (into #{} (filter ante-vars) (sx/form-vars generated))))

(defn nesting
  "A rule sentence peeled into its levels, outermost first, one map per `implies`:

        {:antecedents …  ; that level's antecedent patterns
         :consequent  …  ; what it concludes, wrapper and all
         :generated   …  ; the bare rule it generates, nil at the innermost level
         :bound       …} ; the variables an *enclosing* level's antecedents bind

  An ordinary rule is one level, a generator two, with no cap.  `:bound` is accumulated on the
  way down: every enclosing level has fired and substituted its holes before a level's rule is
  stored, so those variables are ground there, may stand in functor position, and count as
  bound for the innermost rule's range restriction.  The holes, the variable functors and the
  range restriction are all read off these levels, so they agree about which level owns a
  variable."
  [sentence]
  (loop [r (inner-rule sentence) bound #{} acc []]
    (let [as    (antecedents r)
          c     (consequent r)
          g     (generated-rule c)
          level {:antecedents as :consequent c :generated g :bound bound}]
      (if g
        (recur g (into bound (mapcat sx/form-vars) as) (conj acc level))
        (conj acc level)))))

(defn innermost-rule
  "The rule at the bottom of a generator's nesting — the one whose consequent is a
  **conclusion** rather than another rule, and so the only level of a generator that
  ever concludes a fact.  `inner-rule` for a rule that generates nothing."
  [sentence]
  (let [{:keys [antecedents consequent]} (peek (nesting sentence))]
    (rule-sentence antecedents consequent)))

(defn- ordinary-range-problems
  "`range-problems` for a rule that concludes a *fact* — every rule but a generator.
  `bound` is what counts as bound beside the antecedents' own variables: empty for a
  written rule, and a generator's holes for the rule it generates."
  [antecedents consequent bound]
  (let [exists?   (sx/head-exists? consequent)
        evars     (if exists? (sx/head-exists-vars consequent) #{})
        cbody     (if exists? (sx/head-exists-body consequent) consequent)
        cvars     (sx/form-vars cbody)
        ante-vars (into (set bound) (mapcat sx/form-vars) antecedents)]
    (cond-> []
      (and (sequential? cbody) (= 'and (first cbody))
           (empty? (rest cbody)))
      (conj "rule consequent is an empty conjunction")

      ;; `_` is an anonymous wildcard: two occurrences are two *different* variables
      ;; (canonicalization numbers each one separately), so it can never carry a
      ;; binding from an antecedent to the consequent — matching one against another
      ;; would store a non-ground junk fact.
      (some #(= '_ %) cvars)
      (conj "rule consequent uses the anonymous wildcard _, which binds nothing")

      :always
      (into (for [v (distinct cvars)
                  :when (and (not= '_ v) (not (ante-vars v)) (not (evars v)))]
              (str "rule is not range-restricted: consequent variable " v
                   " is unbound by the antecedents"))))))

(defn range-problems
  "Why `antecedents => consequent` is not range-restricted, as a seq of problem strings, empty
  when the rule is fine.  The value form, like the wff arms.  A head existential `(exists ?y C)`
  exempts only its marked variables: the check runs over the inner `C` (docs/skolem.md).

  A generator is checked at its innermost level, with every enclosing level's holes counted as
  bound; each generator level's own range restriction is vacuous.  The refusal therefore
  reaches the author where the generator is written.  Each generator level also owes one claim:
  it must fill a hole no enclosing level has already filled, since otherwise it generates the
  same rule at every firing."
  [antecedents consequent]
  (let [levels (nesting (rule-sentence antecedents consequent))
        inner  (peek levels)]
    (-> (into []
              (comp (map-indexed vector)
                    (keep (fn [[i {:keys [antecedents generated bound]}]]
                            (when (every? bound (holes antecedents generated))
                              (if (pos? i)
                                (str "rule generator at nesting level " (inc i)
                                     " shares no variable with the rule it generates"
                                     " that a level further out has not already filled,"
                                     " so every firing generates the same rule: share a"
                                     " variable the levels above it do not")
                                (str "rule generator shares no variable with the rule it"
                                     " generates, so every firing generates the same rule:"
                                     " share the variable that is meant to vary, or"
                                     " write the rule itself"))))))
              (butlast levels))
        (into (ordinary-range-problems (:antecedents inner) (:consequent inner)
                                       (:bound inner))))))

(defn check-range-restricted
  "Throw `:type :not-range-restricted` unless every consequent variable is bound by
  some antecedent (and the consequent is a well-formed conclusion).

  Uses `ex-info`, not `clojure.core/assert`: an elidable check under `*assert*` false
  would store the junk rule *silently* — the exact failure `check-ground` exists to
  prevent — and an `AssertionError` carries no `:type` for callers to discriminate
  on."
  [antecedents consequent]
  (when-let [problems (seq (range-problems antecedents consequent))]
    (throw (ex-info (first problems)
                    {:type        :not-range-restricted
                     :problems    (vec problems)
                     :antecedents (vec antecedents)
                     :consequent  consequent}))))

;; ---- what a disjunction may not do --------------------------------------
;; `or` is accepted only where it *disappears* (`expand-antecedent`), so the refusals below
;; are the positions from which it cannot: a place where nothing would expand it, or a
;; width at which expanding it is the wrong storage.  Every one is a pure read of the
;; sentence, which is why they are reported at the shape entry point — before the KB is read
;; at all, by both storage entry points and by `core/check` alike.

(defn- some-disjunction
  "The first `or` anywhere in `form`, arguments included, or nil."
  [form]
  (sx/some-form sx/disjunction? form))

(defn- literal-disjunction
  "The first `or` standing in a literal position of `form`, or nil.  The positions are
  the ones `nm/applied-literals` descends, which treats an `or` as a literal and
  descends no argument, so an `or` in an argument slot is a term and is not returned."
  [form]
  (some (fn [[_ lit]] (when (sx/disjunction? lit) lit)) (nm/applied-literals form)))

(defn- malformed
  "The `:not-well-formed` problem an `or` in a position nothing expands carries.  The
  keyword is a literal at this one site rather than an argument: the refusal vocabulary
  is scanned from the sources (`type_contract_test`), and a `:type` behind a parameter is
  one that scan can name but not resolve."
  [sentence extra message]
  (merge {:type :not-well-formed :sentence sentence :message message} extra))

(defn- query-body-problem
  "The refusal an `or` inside a closed-query body carries.  `unknown`, `thereExists` and
  the aggregates are answered as **one** closed query each (docs/naf.md,
  docs/aggregate.md): the evaluator runs the body's conjuncts and reads whether they
  held, and nothing there unions two runs — so an `or` under one of them is a query the
  answer is not computed from, which is the one way a guard can silently pass
  everything.  Not expanded either, because the body is not the rule: splitting the rule
  on it would make `(unknown (or A B))` mean \"A is underivable **or** B is\", which is
  the De Morgan opposite of what it reads as."
  [sentence frame rewrite]
  (malformed
   sentence {:frame frame}
   (str "or cannot stand inside the body of " frame ": it is answered as one closed"
        " query and nothing there unions two runs, so the disjunction would decide the"
        " rule without being evaluated — " rewrite)))

(defn- antecedent-disjunction-problems
  "The refusals one antecedent literal's `or`s carry, walking the frames a disjunction
  may legally nest in — `and` and `or` themselves — and naming the ones it may not."
  [sentence lit]
  (cond
    (sx/disjunction? lit)
    (if (empty? (sx/disjuncts lit))
      [(malformed
        sentence {:literal lit}
        (str "or takes at least one alternative, and (or) offers none: a rule with an"
             " empty disjunct list expands to no rules at all, which is not the rule"
             " that was written.  Drop the antecedent, or name the alternatives"))]
      (vec (mapcat #(antecedent-disjunction-problems sentence %) (sx/disjuncts lit))))

    (conjunctive? lit)
    (vec (mapcat #(antecedent-disjunction-problems sentence %) (rest lit)))

    (sx/negation? lit)
    (if (literal-disjunction (second lit))
      [(malformed
        sentence {:literal lit}
        (str "or cannot stand under not: (not (or A B)) is \"neither A nor B\", which is"
             " a conjunction of negations rather than a choice, and expanding the rule on"
             " it would store the opposite claim.  Write the two negations as separate"
             " antecedents"))]
      [])

    (sx/unknown? lit)
    (if (literal-disjunction (second lit))
      [(query-body-problem sentence "unknown"
                           (str "(unknown (or A B)) is \"neither A nor B is derivable\","
                                " so write (unknown A) and (unknown B) as two"
                                " antecedents"))]
      [])

    (sx/there-exists? lit)
    (if (literal-disjunction (nth lit 2))
      [(query-body-problem sentence "thereExists"
                           (str "there is no rewrite that keeps one witness: write one"
                                " rule per alternative, each with its own thereExists"))]
      [])

    (sx/aggregate? lit)
    (if (literal-disjunction (sx/aggregate-body lit))
      [(query-body-problem sentence (name (first lit))
                           (str "a count over a union is not the sum of two counts —"
                                " a witness satisfying both alternatives would be"
                                " counted twice — so name the extent with a rule and"
                                " aggregate over that"))]
      [])

    :else []))

(defn- consequent-disjunction-problem
  "The refusal an `or` in a rule's conclusion carries.  A disjunctive *head* is not
  something forward chaining can place: it says one of two things holds without saying
  which, and belief is a label on a sentex rather than on a set of them.  What the
  engine does have is the choice itself — `set/assumptionRule` offers the head to a
  solve, and the solver picks a model (docs/solving.md).  So the head is written as one
  assumptionRule per alternative, with a constraint saying what may not be chosen
  together."
  [sentence conseq]
  (malformed
   sentence {:consequent conseq}
   (str "or cannot stand in a rule's conclusion: a disjunctive head asserts that one of"
        " the alternatives holds without saying which, and forward chaining places a"
        " sentex rather than a choice.  Offer the alternatives to a solve instead —"
        " one (set/assumptionRule (implies <body> <alternative>)) each, with a"
        " set/hardConstraint ruling out the combinations that cannot stand — and read"
        " the answer with solve (docs/solving.md)")))

(defn- exception-disjunction-problem
  "The refusal an `or` inside an `exceptWhen` query carries.  The exception is *already*
  disjunctive across assertions: each `exceptWhen` meta-sentex is an independent
  \"unless\" clause and a firing is blocked if **any** of them holds
  (`provers/rule-exceptions`), while the conjuncts within one all must hold.  So a
  disjunctive exception is two exceptions, and writing it that way keeps each one
  separately assertable, retractable and believable — which one `or` inside a single
  query would not be."
  [sentence q]
  (malformed
   sentence {:exception q}
   (str "or cannot stand inside an exceptWhen query: the conjuncts of one exception all"
        " have to hold.  Assert one exceptWhen per alternative against the same rule —"
        " (exceptWhen <alternative> (sentexHandle H)) — since a firing is blocked if any"
        " of a rule's exceptions holds, which is the disjunction, one clause at a time")))

(defn- width-problem
  "The refusal a rule too wide to expand carries, naming the count."
  [sentence n]
  {:type :disjunction-too-wide :sentence sentence
   :alternatives n :cap max-alternatives
   :message
   (str "a disjunctive antecedent is stored as one rule per alternative, and this one"
        " expands to " n ", over the cap of " max-alternatives ".  The width is paid in"
        " handles, index entries and TMS nodes rather than at query time, and nested"
        " disjuncts multiply.  Name the alternatives as a type instead — a genl edge per"
        " member and one rule on the supertype — or split the rule by hand")})

(defn- alternative-range-problems
  "Range restriction, asked **per alternative**, naming the disjuncts that alternative
  took.

  This is the check a disjunctive rule cannot inherit from the ordinary one, because the
  ordinary one reads the disjunction whole: `(implies (or (dog ?p) (cat ?q)) (fed ?p))`
  has `?p` somewhere in its antecedents, so the flat read passes — and then one of the
  two rules it expands to concludes about a variable nothing binds.  Refusing the
  **whole** rule rather than the bad half is what keeps the expansion invisible: a rule
  the author wrote is stored entirely or not at all, exactly as a conjunctive consequent
  is."
  [sentence level]
  (let [{:keys [antecedents consequent bound]} level]
    (vec (for [alt (antecedent-alternatives antecedents)
               p   (ordinary-range-problems (:antecedents alt) consequent bound)]
           {:type :not-range-restricted :sentence sentence
            :problems [p] :antecedents (:antecedents alt) :consequent consequent
            :disjuncts (:choices alt)
            :message
            (str p ", in the alternative that takes "
                 (str/join " and " (map pr-str (:choices alt)))
                 " — every alternative a disjunctive antecedent expands to is a rule in"
                 " its own right, and each has to bind the consequent on its own")}))))

(defn disjunction-problems
  "Why a sentence's `or`s cannot be polycanonicalized away, as problem maps; empty when they
  can, and empty in one read for a sentence with no `or`.  Four families, in this order: an `or`
  in a position nothing expands (a conclusion, a closed-query body, an exception, under `not`),
  an empty `(or)`, a rule wider than `max-alternatives`, and an alternative the consequent is
  not range-restricted over.  A non-rule reads empty (`sx/connective-problems` refuses a
  standalone `or`).  A generator is read level by level: every level's antecedents may
  disjoin, only the innermost consequent is a conclusion, and the innermost range check counts
  an enclosing level's variables as bound (`checks/rule-violation` answers for the generated
  rule)."
  [sentence]
  (if-not (some-disjunction sentence)
    []
    (let [[_ _ exc _ _ inner] (sx/peel-rule-wrapper sentence)]
      (if-not (rule-sentence? inner)
        []                              ; `sx/connective-problems` refuses a fact's `or`
        (let [levels     (nesting inner)
              innermost  (peek levels)
              structural (-> (vec (for [level levels
                                        lit   (:antecedents level)
                                        p     (antecedent-disjunction-problems sentence lit)]
                                    p))
                             (into (when (literal-disjunction (:consequent innermost))
                                     [(consequent-disjunction-problem
                                       sentence (:consequent innermost))]))
                             (into (for [q exc :when (literal-disjunction q)]
                                     (exception-disjunction-problem sentence q))))]
          (if (seq structural)
            structural
            (let [wide (vec (for [level levels
                                  :let  [n (antecedent-alternative-count (:antecedents level))]
                                  :when (> n max-alternatives)]
                              (width-problem sentence n)))]
              (cond
                (seq wide) wide
                (some distributes-or? (:antecedents innermost))
                (alternative-range-problems sentence innermost)
                :else []))))))))

(defn check-disjunction!
  "Throw the first `disjunction-problems` refusal, or return nil.  The throwing form both
  storage entry points read: `core/check-sentence-shape!` runs it before anything is stored, and
  `checks/check-rule!` runs it again over what is about to be stored — which is where a
  rule the cap refused, and so never expanded, is caught on the mint path."
  [sentence]
  (when-let [p (first (disjunction-problems sentence))]
    (throw (ex-info (:message p) (dissoc p :message)))))

;; ---- the functor a rule is indexed by ------------------------------------

(defn variable-functor-literals
  "The `[role literal]` pairs of a rule whose functor is a variable: `(?p ?x ?y)` or the dotted
  rest `(?pred . ?args)`.  Read through `naming/applied-literals` one level at a time, so the
  frames descended into are those the naming check descends: a negated antecedent, a head
  existential, an aggregate's body.

  Inside a generator's generated rule the question is asked of non-holes only.  A generated
  rule is a pattern and the mint is what gets stored, checked in its own right when minted.  A
  variable an enclosing level binds is ground before anything is keyed on it, so one generator
  can range over a family of predicates.  A variable bound by a literal of the rule being
  stored (`(implies (and (?tpred ?type ?ability) (?type ?instance)) …)`) is refused; written one
  level further in it is a hole of the middle level and both functors are concrete.  A
  generated variable functor no enclosing level binds is refused, naming the generator."
  [sentence]
  (letfn [(level-literals [i {:keys [antecedents consequent generated]}]
            ;; only the innermost level's consequent is a conclusion; every other one is
            ;; the level below, read there as that level's own literals
            (let [arole (if (pos? i) :generated-antecedent :antecedent)
                  crole (if (pos? i) :generated-consequent :consequent)]
              (cond-> (into [] (mapcat #(nm/applied-literals arole %)) antecedents)
                (nil? generated) (into (nm/applied-literals crole consequent)))))
          (level-problems [i level]
            (filter (fn [[_ lit]]
                      (let [f (nm/functor lit)]
                        (and (sx/variable? f) (not ((:bound level) f)))))
                    (level-literals i level)))]
    (vec (mapcat level-problems (range) (nesting sentence)))))

(defn check-indexable-functors
  "Throw `:type :not-indexable` when an antecedent literal of the rule `sentence` puts a
  variable in functor position.  A variable functor in the consequent is allowed and indexed
  (`consequent-index-pred`).

  The rule index is keyed by predicate.  Every consequent variable is antecedent-bound
  (`check-range-restricted`), so a consequent `(?p ?y ?x)` fires through its concrete
  antecedent and the `var-consequent-key` catch-all cell serves backward goals.  An antecedent
  `(?p ?x ?y)` names no predicate to key on, so `chain/fire-rules-for` cannot find the rule from
  an arriving fact and the rule would give two answers in two arrival orders.  The message
  names the instantiated rule, or the generator level to move it to (docs/generators.md): a
  functor a level further out binds is ground before its rule is stored.  An `:inert` rule is
  exempt at the caller (`checks/check-rule!`)."
  [sentence]
  (when-let [bad (seq (filter (comp #{:antecedent :generated-antecedent} first)
                              (variable-functor-literals sentence)))]
    (let [[role lit] (first bad)
          generated? (= :generated-antecedent role)]
      (throw (ex-info (str "a rule's antecedent predicate cannot be a variable: "
                           (pr-str lit)
                           (when generated? " in the generated rule's antecedent")
                           " — the rule index is keyed by predicate, so a variable"
                           " functor there names none for an arriving fact to trigger,"
                           " and the rule would fire over whatever is stored when a"
                           " concrete antecedent beside it arrives.  "
                           (if generated?
                             (str "Nothing an enclosing generator binds fills it: move"
                                  " the literal that binds it out one level, so the"
                                  " functor is ground before the rule is generated.")
                             (str "Assert the instantiated rules, one per predicate it"
                                  " ranges over, or generate them from a generator whose"
                                  " antecedent binds the predicate.")))
                      {:type :not-indexable :role role :literal lit
                       :literals (mapv second bad) :sentence sentence})))))

(defn consequent-index-pred
  "The key the consequent slot of `index-rule` files `rule-sentex` under: its
  `consequent-predicate`, or `p/var-consequent-key` when that predicate is a variable (a rule
  with concrete antecedents concluding `(?p …)`, allowed by `check-indexable-functors`).  The
  shared catch-all bucket is unioned into every concrete-goal answer by
  `resolution/concluding-rule-handles`.  An `:inert` rule concludes nothing, so it keeps the
  canonical variable, a key nothing reads.  `special/index-rule-sentex`, its unindex twin and
  `reindex/index-one!` share this spelling."
  [rule-sentex]
  (let [c (consequent-key (:consequent rule-sentex))]
    (if (and (sx/variable? c) (chains? rule-sentex))
      p/var-consequent-key
      c)))

;; ---- the rule indexes' writes ---------------------------------------------

(def ^:dynamic *stratification-memo*
  "nil, or a volatile an `assert` or a `settle` binds, holding the stored half of the
  stratification graph that `checks/stratification-readers` builds once and reuses across
  the write's or the pass's checks.  Every write to the rule indexes below empties it, as
  does a rule's engines moving (`forget-stratification`)."
  nil)

(def ^:dynamic *negated-keys-memo*
  "nil, or a volatile bound beside `*stratification-memo*` holding `stored-negated-keys`,
  emptied with it."
  nil)

(defn forget-stratification
  "Empty `*stratification-memo*` and `*negated-keys-memo*`: a stored rule's graph node moved."
  []
  (when-let [m *stratification-memo*] (vreset! m nil))
  (when-let [m *negated-keys-memo*] (vreset! m nil)))

(defn stored-negated-keys
  "The `[:not P]` antecedent keys the stored rules take, as a set: one pass over the stored
  keys (`reads/as-stored-rule-keys-meeting`), held for `index` in `*negated-keys-memo*`
  while one is bound."
  [index]
  (let [mem *negated-keys-memo*
        hit (some-> mem deref)]
    (if (identical? index (first hit))
      (second hit)
      (let [nk (set (reads/as-stored-rule-keys-meeting index (constantly nil) vector?))]
        (when mem (vreset! mem [index nk]))
        nk))))

;; A rule is posted under each antecedent key in the `:rule-antecedent` count trie and under
;; its consequent key in `:rule-consequent`, each ending in the rule's context; a watched
;; rule is posted in the `:exception-index` set of each predicate its re-check condition
;; mentions and in the `[:rules]` set.  Each is one `p/family-apply!` batch, and a post
;; of a handle already filed (or a retire of one not filed) changes nothing.

(defn- rule-family-ops
  [op handle ante-keys conseq-key context]
  (cond-> (mapv (fn [k] [op :rule-antecedent [k context] handle]) (distinct ante-keys))
    (some? conseq-key) (conj [op :rule-consequent [conseq-key context] handle])))

(defn index-rule
  "Post rule `handle`, stated in `context`, under each of `ante-keys` and under
  `conseq-key` (nil when it has none).  `antecedent-keys` and `consequent-index-pred`
  compute the keys."
  [index handle ante-keys conseq-key context]
  (p/family-apply! index (rule-family-ops :post handle ante-keys conseq-key context))
  (forget-stratification)
  nil)

(defn unindex-rule!
  "Retire rule `handle`, stated in `context`, from the keys `index-rule` posted it under."
  [index handle ante-keys conseq-key context]
  (p/family-apply! index (rule-family-ops :retire handle ante-keys conseq-key context))
  (forget-stratification)
  nil)

(defn- watched-ops [op handle preds]
  (conj (mapv (fn [pd] [op :exception-index [pd] handle]) preds)
        [op :exception-index [:rules] handle]))

(defn index-exception
  "Post rule `handle` under each predicate of `preds` in the re-check index, and into the
  `[:rules]` set whatever `preds` holds."
  [index handle preds]
  (p/family-apply! index (watched-ops :post handle preds))
  (forget-stratification)
  nil)

(defn unindex-exception!
  "Retire rule `handle` from each predicate of `preds` in the re-check index and from the
  `[:rules]` set."
  [index handle preds]
  (p/family-apply! index (watched-ops :retire handle preds))
  (forget-stratification)
  nil)

(defn direct-concluders
  "Rule handles whose consequent predicate is exactly `pred`, unioned with the
  variable-consequent catch-all (`p/var-consequent-key`): a rule concluding `(?p …)` could
  conclude `pred` once `?p` binds, so any reader answering \"which stored rules conclude
  `pred`\" must include it or it disagrees with the backward chainer.  This is the
  **stored-graph** read — no spec fan, unlike `resolution/concluding-rule-handles` — shared
  by the stratification-cycle check and the blocked-firing explanation."
  [index pred]
  (into (set (reads/as-stored-rules-by-consequent-global index p/var-consequent-key))
        (reads/as-stored-rules-by-consequent-global index pred)))
