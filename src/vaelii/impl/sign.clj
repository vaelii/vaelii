;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.sign
  "Sign arithmetic: a quantity is negative, zero or positive, `qualitativeSum` /
  `qualitativeDifference` / `qualitativeProduct` combine signs, `derivativeOf` makes a
  trend the sign of a rate, and `greaterInMagnitudeThan` resolves the ambiguous sum.  The
  algebra (pure data) comes first, then the KB reading and `SignProver`, registered with
  `vaelii.core/add-reasoner :sign`.  See docs/sign.md."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

;; =========================================================================
;; THE ALGEBRA — pure data in, pure data out.  No KB, no context, no belief.
;; =========================================================================

(def all-signs
  "The three values a quantity's sign takes, jointly exhaustive and pairwise disjoint."
  #{:negative :zero :positive})

(def negated
  "Each sign under negation: `qualitativeDifference` reads A − B as A + (−B)."
  {:negative :positive, :zero :zero, :positive :negative})

(defn- sum-pair
  "The signs `x + y` can take.  `dominant` names the addend known larger in magnitude —
  `:left`, `:right` or nil — and decides opposite signs, which are otherwise all three."
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
  "The sign of `x × y`, which no magnitude affects."
  [x y]
  #{(cond (or (= :zero x) (= :zero y)) :zero
          (= x y)                      :positive
          :else                        :negative)})

(defn- lift
  "A table over single signs applied to two possible sets: the union over every pair."
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

(deftype ^:private Support [own parents])

(defn- support-handles
  "The handles a support value names.  A set names itself.  A `Support` names its `own`
  handles and every handle its `parents` name, and the walk visits each node once, so
  reading one quantity's support costs the nodes it reaches rather than a copy per
  narrowing along the way."
  [sup]
  (if (set? sup)
    sup
    (let [seen (java.util.IdentityHashMap.)]
      (loop [stack [sup], acc (transient #{})]
        (if-let [x (peek stack)]
          (let [stack (pop stack)]
            (cond
              (set? x)              (recur stack (reduce conj! acc x))
              (.containsKey seen x) (recur stack acc)
              :else                 (let [^Support x x]
                                      (.put seen x true)
                                      (recur (into stack (.-parents x))
                                             (reduce conj! acc (.-own x))))))
          (persistent! acc))))))

(defn- narrowed
  "One constraint applied to `state`: intersect the output's possible set with what the
  inputs derive, and add the supports when the set moved.  An optional `:decided-by`
  maps the inputs' sets to further handles the derivation read.  The new support is a
  `Support` over the output's previous support and the inputs' supports, which shares
  them rather than copying them."
  [state {:keys [in out derive support decided-by]}]
  (let [ins  (mapv #(get state % [all-signs #{}]) in)
        sets (mapv first ins)
        cur  (get state out [all-signs #{}])
        next (set/intersection (first cur) (derive sets))]
    (if (= next (first cur))
      state
      (assoc state out
             [next (->Support (into support (when decided-by (decided-by sets)))
                              (into [(second cur)] (map second) ins))]))))

(defn- resolve-state*
  "`resolve-state` with each support left a `Support` node (`support-handles` reads it)."
  [state cs]
  (let [cs      (vec cs)
        readers (reduce-kv (fn [m i {:keys [in]}]
                             (reduce #(update %1 %2 (fnil conj []) i) m (distinct in)))
                           {} cs)]
    (loop [st state, now (into (sorted-set) (range (count cs))), later (sorted-set)]
      (if-let [i (first now)]
        (let [{:keys [out] :as c} (nth cs i)
              moved (narrowed st c)
              now   (disj now i)]
          (if (identical? moved st)
            (recur st now later)
            (let [rs (get readers out)]
              (recur moved
                     (into now (filter #(> (long %) (long i))) rs)
                     (into later (remove #(> (long %) (long i))) rs)))))
        (if (seq later) (recur st later (sorted-set)) st)))))

(defn- flat-supports
  "`state` with every support read out to its handle set."
  [state]
  (update-vals state (fn [[signs sup]] [signs (support-handles sup)])))

(defn resolve-state
  "Narrow every constraint's output to the greatest fixpoint.

  `state` is `{[attribute quantity] → [#{sign} #{handle}]}`, `attribute` `:sign` or
  `:trend`; an absent key is `all-signs` with no support.  A constraint is `{:in [key…]
  :out key :derive fn :support #{handle}}`, `:derive` mapping the inputs' sets to the
  output's.  The sets reached do not depend on the order of `cs`; which handles a
  narrowing names does.

  A worklist over `cs`'s positions, applied in passes in `cs` order: a constraint is
  re-applied only after a key it reads moved, in the current pass when it stands after
  the constraint that moved the key and in the next pass otherwise.  A constraint whose
  inputs have not moved cannot move its output, so this applies the narrowings a
  round-robin over the whole of `cs` applies, in the same order, and names the same
  handles, at a cost of the moves rather than of passes × constraints."
  [state cs]
  (flat-supports (resolve-state* state cs)))

(defn inconsistent-state?
  "Has some quantity been narrowed to no sign at all?"
  [state]
  (boolean (some (comp empty? first val) state)))

;; =========================================================================
;; THE KB HALF — reading believed facts in, reading answers back out.
;; =========================================================================

(def sign-predicates
  "The predicates a sign is stated with and the prover answers."
  '#{signOf trendOf})

(def arithmetic-predicates
  '#{qualitativeSum qualitativeDifference qualitativeProduct})

(def sign-sources
  "Every predicate the reading reads (`prover-types/SupportingProver`)."
  (into arithmetic-predicates '#{signOf trendOf derivativeOf greaterInMagnitudeThan}))

(def sign-of-value
  "Each sign term the KB states, and the keyword the tables are written over."
  '{SignNegative :negative SignZero :zero SignPositive :positive})

(def value-of-sign (set/map-invert sign-of-value))

(defn- attribute-of [pred] (if (= 'trendOf pred) :trend :sign))

;; ---- reading the KB into a state and a constraint list -------------------

(defn- believed
  "Every `[handle arg…]` for which `(pred arg…)` is believed and visible from `context`,
  every argument a ground term.  `vars` names one variable per argument."
  [kb context pred & vars]
  (for [[h b] (res/matches-visible kb (apply list pred vars) context)
        :let  [args (mapv #(get b %) vars)]
        :when (every? sx/plain-symbol? args)]
    (into [h] args)))

(defn- stated-values
  "Every believed, visible `(signOf Q S)` and `(trendOf Q S)` as the starting state.  Two
  stated values that disagree narrow the key to the empty set."
  [kb context]
  (reduce (fn [st [pred h q s]]
            (if-let [v (sign-of-value s)]
              (let [k [(attribute-of pred) q], [cur sup] (get st k [all-signs #{}])]
                (assoc st k [(set/intersection cur #{v}) (conj sup h)]))
              st))
          {}
          (for [pred (nm/by-print-key sign-predicates)
                t    (believed kb context pred '?q '?s)]
            (cons pred t))))

(defn- dominance
  "`(fn [a b] → {:side :left|:right :support #{handle}} | nil)`: which of two addends a
  stored `greaterInMagnitudeThan` names the larger, and its handles.  A pair stated both
  ways round answers `:left`."
  [kb context]
  (let [by-pair (reduce (fn [m [h a b]] (update m [a b] (fnil conj #{}) h))
                        {} (believed kb context 'greaterInMagnitudeThan '?a '?b))]
    (fn [a b]
      (cond
        (seq (get by-pair [a b])) {:side :left  :support (get by-pair [a b])}
        (seq (get by-pair [b a])) {:side :right :support (get by-pair [b a])}
        :else                     nil))))

(defn- arithmetic-constraints
  "One constraint per believed arithmetic relation, its comparison read once here.  The
  comparison's handles are support only for inputs whose result it decides: never a
  product's, and a sum's only when its addends' signs can be opposite."
  [kb context dominant]
  (for [pred      (nm/by-print-key arithmetic-predicates)
        [h x y q] (believed kb context pred '?a '?b '?q)
        :let      [dom (dominant x y)]]
    {:key        [pred x y q]
     :in         [[:sign x] [:sign y]]
     :out        [:sign q]
     :derive     (fn [[sx sy]] (combined pred sx sy (:side dom)))
     :support    #{h}
     :decided-by (when dom
                   (fn [[sx sy]]
                     (when (not= (combined pred sx sy (:side dom)) (combined pred sx sy nil))
                       (:support dom))))}))

(defn- derivative-constraints
  "Two constraints per believed `(derivativeOf R Q)`: R's sign to Q's trend, and back."
  [kb context]
  (for [[h r q] (believed kb context 'derivativeOf '?a '?b)
        [from to tag] [[[:sign r] [:trend q] :down] [[:trend q] [:sign r] :up]]]
    {:key     ['derivativeOf r q tag]
     :in      [from]
     :out     to
     :derive  first
     :support #{h}}))

(defn- constraint-order
  "The constraints sorted on `:key` (relation, arguments, direction), so the handles a
  narrowing names depend on content and not on arrival (docs/nmtms.md)."
  [cs]
  (nm/sort-by-content-key (comp nm/print-key :key) compare cs))

;; ---- the reading, resident on the KB -------------------------------------

(defn- report-inconsistency!
  "File an unsatisfiable reading as a `:sign-inconsistency` violation, logged at :warn,
  naming the quantities whose possible signs emptied."
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
    (violations/report-without-run kb entry)))

(defn- build-reading
  "The believed sign facts of `context` resolved, as `{:state … :inconsistent? …}`."
  [kb context]
  (let [dominant (dominance kb context)
        cs       (constraint-order (concat (arithmetic-constraints kb context dominant)
                                           (derivative-constraints kb context)))
        state    (resolve-state* (stated-values kb context) cs)]
    {:state state :inconsistent? (inconsistent-state? state)}))

(defn reading
  "The resolved sign state visible from `context`, or `:inconsistent` when the facts
  contradict each other.  The `resolve-state` shape, except that a narrowed key's support
  is a node over the supports it was derived from; `possible-signs` reads one out as a
  handle set.

  Cached on the KB's `:qcn` atom and keyed by `observe/change-clock`, as
  `qcn-kb/read-network` is.  An inconsistency is reported once per KB, context and state
  (`observe/newly-seen?`)."
  [kb context]
  (let [{:keys [state inconsistent?]}
        (observe/cached (reasoning/qcn kb) [::reading context]
                        (fn [_stale] (build-reading kb context)))]
    (if inconsistent?
      (do (when (observe/newly-seen? (reasoning/qcn kb) [::reported context]
                                     (flat-supports state))
            (report-inconsistency! kb context state))
          :inconsistent)
      state)))

(defn possible-signs
  "The signs `attribute` (`:sign` or `:trend`) may take for `quantity` in `context`, and
  what says so: `[#{sign} #{handle}]`.  `[#{} #{}]` when the reading is inconsistent;
  `all-signs` with no support for a quantity nothing constrains."
  [kb context attribute quantity]
  (let [state (reading kb context)]
    (if (= :inconsistent state)
      [#{} #{}]
      (let [[signs sup] (get state [attribute quantity] [all-signs #{}])]
        [signs (support-handles sup)]))))

;; ---- the prover ----------------------------------------------------------

(defn- negated-goal? [goal]
  (and (sequential? goal) (= 2 (count goal)) (= sx/not-functor (first goal))))

(defn- goal-literal
  "The `(signOf Q S)` or `(trendOf Q S)` literal a goal is about — the goal itself, or the
  one under a `not` — else nil."
  [goal]
  (let [lit (if (and (negated-goal? goal) (sequential? (second goal))) (second goal) goal)]
    (when (and (sequential? lit) (= 3 (count lit))
               (contains? sign-predicates (first lit)))
      lit)))

(defn- answers-for
  "The solutions for one quantity, `[[bindings support]]` or nothing.  Positive: the
  possible set is exactly the goal's sign, and an open sign binds when the set is a
  singleton.  Negated: the set excludes the named sign; an open sign is not answered.  A
  quantity nothing constrains answers neither way, so no answer has empty support."
  [state attribute q svar neg?]
  (let [[poss sup] (get state [attribute q] [all-signs #{}])
        sup        (support-handles sup)]
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
  "Every solution for a sign goal in `context`, each paired with the handles it rests on.
  An open quantity enumerates the quantities the reading records, in content order."
  [kb goal context]
  (let [neg?       (negated-goal? goal)
        [pred q s] (goal-literal goal)
        attribute  (attribute-of pred)
        state      (reading kb context)]
    (when-not (= :inconsistent state)
      (if (sx/plain-symbol? q)
        (answers-for state attribute q s neg?)
        (mapcat (fn [x]
                  (map (fn [[b sup]] [(assoc b q x) sup])
                       (answers-for state attribute x s neg?)))
                (nm/by-print-key (into #{} (keep (fn [[[a x]]] (when (= a attribute) x)))
                                       state)))))))

(defrecord SignProver []
  prover-types/Prover
  (applicable? [_ _ goal _]
    (when-let [[_ q s] (goal-literal goal)]
      (and (or (sx/plain-symbol? q) (sx/variable? q))
           (or (sx/variable? s) (contains? sign-of-value s)))))
  ;; A constant: counting the reading's quantities costs the whole fixpoint.
  (est-bindings [_ _ goal _]
    (let [[_ q s] (goal-literal goal)]
      (if (and (sx/plain-symbol? q) (not (sx/variable? s))) 1 8)))
  (cost         [_ _ _ _] :compute)
  ;; The stated sign facts are read into the reading and answered back out of it, so a
  ;; raw fact match adds nothing.
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
