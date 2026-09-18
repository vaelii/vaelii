;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.sign
  "Sign arithmetic — the coarsest quantitative reasoning there is, and the one a
  common-sense KB can nearly always do.  Nobody knows how fast the tap runs or how fast
  the drain empties, and everybody knows the tub fills when the tap runs faster.

  A quantity's **sign** is one of three values, `SignNegative` / `SignZero` /
  `SignPositive`, and the three are jointly exhaustive and pairwise disjoint over the
  reals — so a set of them is a real constraint and its complement is a refutation, which
  is the same licence the relation algebras of `vaelii.impl.qcn` reason under.  A
  quantity's **trend** is the sign of its rate of change, and it is not a second theory:
  `(derivativeOf Rate Q)` says which quantity a rate is the rate *of*, and a trend is then
  that rate's sign read at the other end of the edge.

  Three declared relations do the arithmetic.  `(qualitativeSum A B Q)` says Q is A + B,
  `(qualitativeDifference A B Q)` that it is A − B, `(qualitativeProduct A B Q)` that it
  is A × B — declarations about *which* quantities stand in the relation, not sentences
  about numbers, since there are no numbers here at all.

  **Ambiguity is answered with no answer.**  Two positives sum to a positive and two
  negatives to a negative, but a positive and a negative sum to anything whatever: the
  sign of the total is the sign of the larger, and nothing here knows which that is.  So
  the sum takes all three values and no goal about it is answered — never a guess.  What
  resolves it is a stated `(greaterInMagnitudeThan A B)`, and then the sum takes A's sign.

  Written the way `qcn` and `stp` are written, and for the same reason: **pure data in,
  pure data out** in the first half, the KB reading and the prover in the second.  The
  algorithm is a greatest fixpoint over sets of possible signs — a constraint narrows an
  output and never widens it, intersection is commutative and associative, so the reading
  is a function of the believed facts and never of the order they arrived in.  A set
  narrowed to nothing is a contradiction, reported to the violations ledger, and then no
  sign goal in that context is answered: an unsatisfiable theory is not mined for
  conclusions.

  The prover is **opt-in**: register it with `vaelii.core/add-reasoner :sign`, and until
  then a KB stores and retrieves these facts as ordinary facts.  The vocabulary ships in
  `kb/upper/CxMeasure.txt` either way.  See docs/sign.md."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]))

;; =========================================================================
;; THE ALGEBRA — pure data in, pure data out.  No KB, no context, no belief.
;; =========================================================================

(def all-signs
  "The three values a quantity's sign takes.  Jointly exhaustive and pairwise disjoint
  over the reals: exactly one holds of any quantity, which is what makes a *set* of them
  the constraint \"one of these\" rather than an absence of knowledge, and what licenses
  the refutation `solve` answers for a negated goal."
  #{:negative :zero :positive})

(def negated
  "Each sign under negation — what `qualitativeDifference` turns its subtrahend into, so
  that A − B is read as A + (−B) and one addition table serves both."
  {:negative :positive, :zero :zero, :positive :negative})

(defn- sum-pair
  "The signs `x + y` can take, given which addend (if either) is known the larger in
  magnitude — `:left` for the first, `:right` for the second, nil for neither.

  Zero is the identity and like signs keep theirs.  **Opposite** signs are the whole
  point of the table: the total takes the sign of whichever is larger and is nil when they
  are equal, so with nothing said about their magnitudes all three values survive.  That
  is not a failure to compute — it is the correct constraint, and it answers no goal
  precisely because a guess between three values is the one thing a KB must not do."
  [x y dominant]
  (cond
    (= :zero x) #{y}
    (= :zero y) #{x}
    (= x y)     #{x}
    :else       (case dominant
                  :left  #{x}
                  :right #{y}
                  all-signs)))

(defn- product-pair
  "The sign of `x × y`, which is never ambiguous: anything times nothing is nothing, like
  signs give a positive, and opposite signs a negative.  Magnitudes do not come into it,
  which is why no comparison is read here."
  [x y]
  #{(cond (or (= :zero x) (= :zero y)) :zero
          (= x y)                      :positive
          :else                        :negative)})

(defn- lift
  "A table over single signs applied to two possible **sets**: the union of what it
  answers for every combination.  Sound and exact — a value the output can take is one
  some admissible pair of inputs produces, and every such pair is enumerated."
  [f sa sb]
  (into #{} (mapcat (fn [x] (mapcat (fn [y] (f x y)) sb))) sa))

(defn combined
  "The signs the output of `kind` can take, given its two inputs' possible sets and which
  input (if either) is the larger in magnitude.  `kind` is the arithmetic predicate the
  relation was stated with."
  [kind sa sb dominant]
  (case kind
    qualitativeSum        (lift #(sum-pair %1 %2 dominant) sa sb)
    qualitativeDifference (lift #(sum-pair %1 (negated %2) dominant) sa sb)
    qualitativeProduct    (lift product-pair sa sb)))

;; ---- the fixpoint --------------------------------------------------------
;; A **state** is `{[attribute quantity] → [#{signs} #{handle}]}`, where the attribute is
;; `:sign` or `:trend` and an unrecorded key is the whole of `all-signs` — nothing known.
;; A **constraint** is `{:in [key…] :out key :derive fn :support #{handle} :key …}`: what
;; the output's set is narrowed to, given its inputs'.
;;
;; So the arithmetic and the derivative edge are one mechanism.  `(derivativeOf R Q)` is a
;; constraint each way — the rate's sign *is* the quantity's trend — and running it in
;; both directions rather than only downward is what lets a stated trend pin the rate that
;; produced it, and two rates of one quantity agree with each other.

(defn- narrowed
  "One constraint applied to `state`: intersect the output's possible set with what the
  inputs derive, and union the supports in when it moved.  `state` unchanged when it did
  not — a constraint that merely agrees with what is already known adds no handle, so a
  conclusion rests on what actually pinned it.

  `:key` is not read here.  It orders the constraints (`constraint-order`), and that order
  is what makes *which* witness a narrowing names a function of content rather than of
  arrival."
  [state {:keys [in out derive support]}]
  (let [ins  (mapv #(get state % [all-signs #{}]) in)
        cur  (get state out [all-signs #{}])
        next (set/intersection (first cur) (derive (mapv first ins)))]
    (if (= next (first cur))
      state
      (assoc state out
             [next (reduce into (into (second cur) support) (map second ins))]))))

(defn resolve-state
  "Narrow every constraint's output to a fixpoint, and answer the state reached.

  It terminates because every step **shrinks** a set in a three-element lattice and there
  are finitely many keys, and it reaches the same state whatever order the constraints are
  taken in: intersection is commutative and associative, so the fixpoint is the greatest
  one below the stated facts and is unique.  The order the constraints are taken in
  decides only which handles a narrowing names, and `constraint-order` fixes that on
  content."
  [state cs]
  (loop [st state]
    (let [next (reduce narrowed st cs)]
      (if (= next st) st (recur next)))))

(defn inconsistent-state?
  "Has some quantity been narrowed to no sign at all?  A quantity has one of three values
  and a set of them is the claim \"one of these\", so an empty set is a set of facts no
  assignment satisfies."
  [state]
  (boolean (some (comp empty? first val) state)))

;; =========================================================================
;; THE KB HALF — reading believed facts in, reading answers back out.
;; =========================================================================

(def sign-predicates
  "The two predicates a sign is *stated* with, and the two the prover answers.  `trendOf`
  is answered as well as read: a trend is a value in its own right, whether stated
  outright or read off the rate that produces it."
  '#{signOf trendOf})

(def arithmetic-predicates
  "The three declared relations the arithmetic runs over."
  '#{qualitativeSum qualitativeDifference qualitativeProduct})

(def derivative-predicate
  "The edge joining a rate to the quantity it is the rate of, and so a sign to a trend."
  'derivativeOf)

(def comparison-predicate
  "What resolves the one ambiguous entry in the addition table."
  'greaterInMagnitudeThan)

(def sign-sources
  "Every predicate the reading reads, which is what a conclusion drawn from a sign rests
  on besides the facts a rule's other antecedents matched (`prover-types/SupportingProver`)."
  (into (conj arithmetic-predicates derivative-predicate comparison-predicate)
        sign-predicates))

(def sign-of-value
  "The three sign individuals, and the value each denotes.  Symbols in the KB, keywords in
  the arithmetic — the KB's own three terms are the public representation and the keywords are what
  the tables are written over."
  '{SignNegative :negative SignZero :zero SignPositive :positive})

(def value-of-sign
  "`sign-of-value` read backwards: how a computed value is rendered as the term a KB
  states."
  (into {} (map (fn [[term v]] [v term])) sign-of-value))

(defn- term? [x] (and (symbol? x) (not (sx/variable? x))))

(defn- attribute-of
  "The state attribute `pred` records — `:sign` for `signOf`, `:trend` for `trendOf`."
  [pred]
  (if (= 'trendOf pred) :trend :sign))

;; ---- reading the KB into a state and a constraint list -------------------

(defn- stated-values
  "Every believed, visible `(signOf Q S)` and `(trendOf Q S)` as the starting state:
  `{[attribute Q] → [#{sign} #{handle}]}`.

  A stated value narrows the quantity to that one sign, and **two that disagree narrow it
  to nothing** — which is the contradiction `reading` reports rather than adjudicates.
  There is no `functional` mark on either predicate to refuse the second at the entry point, and
  deliberately: `functional` merges two symbol arguments through the equality partition,
  and merging `SignPositive` with `SignNegative` would make one term of the two rather
  than report that a KB has said both."
  [kb context]
  (reduce
   (fn [state pred]
     (reduce (fn [st m]
               (let [b (second m), q (get b '?q), v (sign-of-value (get b '?s))]
                 (if (and (term? q) v)
                   (let [k         [(attribute-of pred) q]
                         [cur sup] (get st k [all-signs #{}])]
                     (assoc st k [(set/intersection cur #{v}) (conj sup (first m))]))
                   st)))
             state
             (res/matches-visible kb (list pred '?q '?s) context)))
   {}
   (nm/by-print-key sign-predicates)))

(defn- believed-pairs
  "Every `[handle a b]` for which `(pred a b)` is believed and visible from `context`."
  [kb pred context]
  (for [m     (res/matches-visible kb (list pred '?a '?b) context)
        :let  [b (second m), x (get b '?a), y (get b '?b)]
        :when (and (term? x) (term? y))]
    [(first m) x y]))

(defn- dominance
  "`(fn [a b] → {:side :left|:right :support #{handle}} | nil)` over the believed
  `greaterInMagnitudeThan` facts: which of two addends is the larger in magnitude, and
  what says so.

  A KB told it both ways round has a contradiction to report — the predicate is declared
  `asymmetric` — and the reading does not wait for the settle to do it: the cond is keyed
  on content, so a KB in that state reads one answer rather than whichever the index
  yielded."
  [kb context]
  (let [by-pair (reduce (fn [m [h a b]] (update m [a b] (fnil conj #{}) h))
                        {} (believed-pairs kb comparison-predicate context))]
    (fn [a b]
      (cond
        (seq (get by-pair [a b])) {:side :left  :support (get by-pair [a b])}
        (seq (get by-pair [b a])) {:side :right :support (get by-pair [b a])}
        :else                     nil))))

(defn- arithmetic-constraints
  "One constraint per believed arithmetic relation: the output's signs are what the
  addends' allow, with the magnitude comparison folded in at read time — it is a function
  of the believed facts too, so closing over it costs one lookup per relation rather than
  one per pass."
  [kb context dominant]
  (for [pred  (nm/by-print-key arithmetic-predicates)
        m     (res/matches-visible kb (list pred '?a '?b '?q) context)
        :let  [b (second m), x (get b '?a), y (get b '?b), q (get b '?q)]
        :when (and (term? x) (term? y) (term? q))
        :let  [dom (dominant x y)]]
    {:key     [pred x y q]
     :in      [[:sign x] [:sign y]]
     :out     [:sign q]
     :derive  (fn [[sx sy]] (combined pred sx sy (:side dom)))
     :support (into #{(first m)} (:support dom))}))

(defn- derivative-constraints
  "Two constraints per believed `(derivativeOf R Q)`: the rate's sign is the quantity's
  trend, and the quantity's trend is the rate's sign.

  Both directions, because the edge is an identity rather than an implication.  Downward
  is what makes a trend derivable at all — a tub fills because its net inflow is positive.
  Upward is what a stated trend buys: it pins the rate that produced it, so the rate can
  go on to be an addend of something else, and it makes two rates declared of one quantity
  agree with each other rather than sit side by side."
  [kb context]
  (for [[h r q] (believed-pairs kb derivative-predicate context)
        [from to tag] [[[:sign r] [:trend q] :down] [[:trend q] [:sign r] :up]]]
    {:key     [derivative-predicate r q tag]
     :in      [from]
     :out     to
     :derive  first
     :support #{h}}))

(defn- constraint-order
  "The constraints in an order fixed by their **content** — the relation, its arguments,
  and for a derivative edge which way it runs.

  Not decoration.  The fixpoint's *value* is order-independent whatever order they are
  taken in, but which handles a narrowing names is one witness among several, and only a
  run in a content-determined order picks the same witness every time.  That set becomes a
  firing's antecedents, so a run keyed on arrival order would make what a conclusion rests
  on depend on when its facts were stored (docs/nmtms.md).  The same reason
  `qcn-kb/tighten-with-support` refuses a warm start."
  [cs]
  (nm/sort-by-content-key (comp nm/print-key :key) compare cs))

;; ---- the reading, resident on the KB -------------------------------------

(defn- file-violation!
  "Append one entry to the KB's accumulating violations ledger, newest 1000 kept — the
  shape `vaelii.impl.violations` keeps, without its chaining-run stamp: nothing here is
  reached from a firing, so there is no run to name."
  [kb entry]
  (when-let [v (reasoning/violations kb)]
    (swap! v (fn [entries]
               (let [e' (conj entries entry) n (count e')]
                 (if (> n 1000) (vec (subvec e' (- n 1000))) e'))))))

(defn- report-inconsistency!
  "Append an unsatisfiable sign reading to the violations ledger, and log it at :warn,
  naming the quantities whose possible signs emptied.

  Not a `wff` check, for the three reasons `qcn-kb/report-inconsistency!` gives: `wff`
  throws and would blame whichever fact arrived last, where the clash is a property of the
  set; the check costs a fixpoint over every sign fact in the context and `wff` runs per
  assert; and the prover is opt-in, so a KB that never asked to reason about signs would
  be held to an arithmetic it never registered."
  [kb context state]
  (let [entry {:violation :sign-inconsistency
               :context   context
               :sentence  nil
               :detail    {:message (str "the sign facts visible from " context
                                         " cannot all be satisfied, so no sign goal is"
                                         " answered there")
                           :quantities (nm/by-print-key
                                        (into #{} (comp (filter (comp empty? first val))
                                                        (map (comp second key)))
                                              state))}}]
    (trove/log! {:level :warn :id ::sign-inconsistency :data entry})
    (file-violation! kb entry)))

(defn- build-reading
  "The believed sign facts of `context` as `{:state … :inconsistent? …}`.

  The verdict rides beside the state rather than replacing it, so a contradiction can be
  *reported* — the entry names the quantities that emptied, and they are only readable off
  the state that emptied them.  Deciding it here rather than per read also keeps the
  resident answer O(1) to consume: the scan for an empty set is a walk over every
  quantity, and `reading` is asked once per binding of a joining rule."
  [kb context]
  (let [dominant (dominance kb context)
        cs       (constraint-order (concat (arithmetic-constraints kb context dominant)
                                           (derivative-constraints kb context)))
        state    (resolve-state (stated-values kb context) cs)]
    {:state state :inconsistent? (inconsistent-state? state)}))

(defn reading
  "The resolved sign state visible from `context`: `{[attribute quantity] → [#{sign}
  #{handle}]}`, or `:inconsistent` when the facts contradict each other.

  **Resident** on the KB's `:qcn` atom under a key of this namespace's own, stamped with
  `observe/change-clock` exactly as a qualitative network is (`qcn-kb/read-network`), so a
  rule joining a sign antecedent over many bindings reads the KB once rather than once per
  binding — and so does a settle re-checking one firing after another.

  The inconsistency is **reported** on the way past, once per KB, context and state
  (`observe/newly-seen?`): the alternative is a query that silently answers nothing about
  a KB that has said two contradictory things.  A change of belief is a different state
  and reports again."
  [kb context]
  (let [{:keys [state inconsistent?]}
        (observe/cached (reasoning/qcn kb) [::reading context]
                        (fn [_stale] (build-reading kb context)))]
    (if inconsistent?
      (do (when (observe/newly-seen? (reasoning/qcn kb) [::reported context] state)
            (report-inconsistency! kb context state))
          :inconsistent)
      state)))

(defn possible-signs
  "The signs `attribute` (`:sign` or `:trend`) may take for `quantity` in `context`, and
  what says so: `[#{sign} #{handle}]`.

  `[#{} #{}]` when the reading is inconsistent — an unsatisfiable theory entails nothing —
  and the whole of `all-signs` with no support for a quantity nothing constrains, which is
  a real answer (\"nothing is known\") rather than an absent one."
  [kb context attribute quantity]
  (let [state (reading kb context)]
    (if (= :inconsistent state)
      [#{} #{}]
      (get state [attribute quantity] [all-signs #{}]))))

;; ---- the prover ----------------------------------------------------------

(defn- goal-literal
  "The `(signOf Q S)` literal a goal is about — the goal itself, or the one under a `not`
  — else nil.  The surface convention `qcn-kb/claimed-literal` reads, for the same reason:
  a goal reaches a prover in the form the caller wrote it."
  [goal]
  (let [lit (if (and (sequential? goal) (= 2 (count goal))
                     (= sx/not-functor (first goal)) (sequential? (second goal)))
              (second goal)
              goal)]
    (when (and (sequential? lit) (= 3 (count lit))
               (contains? sign-predicates (first lit)))
      lit)))

(defn- negated-goal? [goal]
  (and (sequential? goal) (= 2 (count goal)) (= sx/not-functor (first goal))))

(defn- quantities-of
  "Every quantity the reading records `attribute` for — what an open goal enumerates."
  [state attribute]
  (into #{} (comp (filter #(= attribute (first (key %)))) (map (comp second key))) state))

(defn- answers-for
  "The solutions for one quantity: `[[bindings support]]` or nothing.

  **Positive** — entailment: the possible set must be exactly the goal's sign, since a
  goal names one of three jointly-exhaustive values and anything wider leaves it open.  An
  open sign argument binds when the set is a singleton.

  **Negative** — refutation: the possible set must exclude the named sign.  Licensed by
  the three values being jointly exhaustive and pairwise disjoint, exactly as a calculus's
  are, so ruling one out *proves* the negation rather than failing to prove the claim.  An
  open sign argument is not answered under a negation: `(not (signOf Q ?s))` asks which
  values Q does not take, and a KB that knows nothing about Q would answer all three
  while knowing none of them.

  An answer with **empty** support is dropped by the forward join rather than resting a
  conclusion on nothing (`prover-types/SupportingProver`), and this is where one would come
  from — a quantity nothing constrains — so the empty set is never a singleton and never
  excludes anything."
  [state attribute q svar neg?]
  (let [[poss sup] (get state [attribute q] [all-signs #{}])]
    (cond
      (sx/variable? svar)
      (when (and (not neg?) (= 1 (count poss)))
        [[{svar (value-of-sign (first poss))} sup]])

      (contains? sign-of-value svar)
      (let [v (sign-of-value svar)]
        (if neg?
          (when-not (contains? poss v) [[{} sup]])
          (when (= poss #{v}) [[{} sup]])))

      :else nil)))

(defn- solve-sign
  "Every solution for a sign goal in `context`, each paired with the handles it rests on."
  [kb goal context]
  (let [neg?       (negated-goal? goal)
        [pred q s] (goal-literal goal)
        attribute  (attribute-of pred)
        state      (reading kb context)]
    (when-not (= :inconsistent state)
      (if (term? q)
        (answers-for state attribute q s neg?)
        ;; an open quantity enumerates the ones the reading records, in a content order so
        ;; the answers do not arrive in handle order
        (mapcat (fn [x]
                  (map (fn [[b sup]] [(assoc b q x) sup])
                       (answers-for state attribute x s neg?)))
                (nm/by-print-key (quantities-of state attribute)))))))

(defn- answer-slot?
  "Can `s` be the value argument — a variable to bind, or one of the three sign terms?"
  [s]
  (or (sx/variable? s) (contains? sign-of-value s)))

(defrecord SignProver []
  prover-types/Prover
  (applicable? [_ _ goal _]
    (when-let [[_ q s] (goal-literal goal)]
      (and (or (term? q) (sx/variable? q)) (answer-slot? s))))
  ;; The quantities the reading records bound an open enumeration, and a ground pair is a
  ;; check — but an estimate must not cost what it estimates, and counting them is the
  ;; whole fixpoint.  A sign theory is a handful of quantities beside the facts about
  ;; them, so the constant is honest where a stored extent would not be.
  (est-bindings [_ _ goal _]
    (let [[_ q s] (goal-literal goal)]
      (if (and (term? q) (not (sx/variable? s))) 1 8)))
  ;; A fixpoint over the stored sign facts before the first answer, not a search.
  (cost         [_ _ _ _] :compute)
  ;; Authoritative over everything the reading reads: a stated `(signOf Q SignPositive)`
  ;; narrows Q to that value and is answered back out of the same pass, so unioning a raw
  ;; fact match in would add nothing this does not already answer.  A source it does not
  ;; read is `provers/sole-prover`'s question.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context] (map first (solve-sign kb goal context)))

  prover-types/SupportingProver
  (support-functors [_] sign-predicates)
  (support-sources  [_] sign-sources)
  (solve-with-support [_ kb goal context] (solve-sign kb goal context)))

(defn sign-prover
  "The sign-arithmetic prover, to register with `vaelii.core/add-prover`."
  []
  (->SignProver))
