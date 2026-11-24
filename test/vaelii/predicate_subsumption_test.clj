;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predicate-subsumption-test
  "Predicate subsumption in matching: `(genl fatherOf parentOf)` makes a `parentOf`
  query (and antecedent, and goal) reach a stored `fatherOf` fact — the subtype rule
  the type hierarchy already gives, generalized to the predicate hierarchy.

  It reuses the existing `genl` closure (no new taxonomy state): `wff` already accepts
  a genl edge between predicates (it only forbids individuals), so the whole of the
  change is `res/match1` and `res/match-pattern` fanning the functor over its
  `specs` for every arity instead of only for unary literals.  These assert the new
  capability, that it follows belief (retract the edge and it is gone), and — via
  `match-pattern-equals-manual-union` — that the fan is exactly the union over the
  spec closure.

  The **backward dual** lives here too: a rule concluding a *spec* of the goal's
  predicate answers the goal, so `candidate-rules` draws candidates from
  `res/concluding-rule-handles` (`specs ∩ rules-by-consequent`) and the chainers
  unify the goal against the consequent with `res/subsuming-unify`.  Exercised with
  a **backward-only** rule so forward chaining cannot materialize the subtype
  conclusion and mask the backward path.

  **`genlInverse` is binary `genl` with the arguments swapped**: `(genlInverse P Q)`
  makes a stored `(P a b)` answer `(Q b a)`, through the same fan.  The tests at the end
  assert that every reader of the fan takes the swap — query, forward trigger, join,
  backward rule, negation — that the swaps compose by parity along a chain (an even
  number of `genlInverse` edges answers exactly what a `genl` chain answers), and that a
  justification names the `genlInverse` edges as it names `genl` ones."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))

(tu/deftest-kb match1-subsumes-a-sub-predicate
  (tu/with-terms [fatherOf parentOf loves A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
    (testing "a fatherOf fact satisfies a parentOf antecedent, binding the arguments"
      (is (= {(symbol "?x") A (symbol "?y") B}
             (res/match1 kb (list parentOf (symbol "?x") (symbol "?y")) (list fatherOf A B)))))
    (testing "an unrelated predicate does not"
      (is (nil? (res/match1 kb (list parentOf (symbol "?x") (symbol "?y")) (list loves A B)))))
    (testing "the equal-functor case is a plain unify, unchanged"
      (is (= {(symbol "?x") A (symbol "?y") B}
             (res/match1 kb (list parentOf (symbol "?x") (symbol "?y")) (list parentOf A B)))))))

(tu/deftest-kb match-pattern-reaches-sub-predicate-facts
  (tu/with-terms [fatherOf parentOf A B C D]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list fatherOf A B) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list parentOf C D) 'CxUniverse {:strength :monotonic})
    (testing "a parentOf query matches both the direct parentOf fact and the fatherOf one"
      (let [sentences (set (map (fn [[h _]] (:sentence (v/sentex kb h)))
                                (res/match-pattern kb (list parentOf (symbol "?x") (symbol "?y")) '?ctx)))]
        (is (contains? sentences (list parentOf C D)))
        (is (contains? sentences (list fatherOf A B)))))
    (testing "a fatherOf query does NOT reach the parentOf fact (subsumption is one-way)"
      (let [sentences (set (map (fn [[h _]] (:sentence (v/sentex kb h)))
                                (res/match-pattern kb (list fatherOf (symbol "?x") (symbol "?y")) '?ctx)))]
        (is (contains? sentences (list fatherOf A B)))
        (is (not (contains? sentences (list parentOf C D))))))))

(tu/deftest-kb match-pattern-equals-manual-union
  ;; the oracle: the generalized fan is exactly the union of raw matches over the spec
  ;; closure — nothing more, nothing less
  (tu/with-terms [fatherOf motherOf parentOf A B C D E F]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list fatherOf A B) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list motherOf C D) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list parentOf E F) 'CxUniverse {:strength :monotonic})
    (doseq [pat [(list parentOf (symbol "?x") (symbol "?y"))
                 (list parentOf A (symbol "?y"))
                 (list parentOf (symbol "?x") D)
                 (list parentOf E F)]]
      (let [got   (proj (res/match-pattern kb pat '?ctx))
            manual (proj (mapcat (fn [f'] (res/raw-match kb (cons f' (rest pat)) '?ctx))
                                 (tax/specs-global (reasoning/taxonomy kb) parentOf)))]
        (is (= manual got) (str "match-pattern diverged from the spec-union on " (pr-str pat)))))))

(tu/deftest-kb forward-chaining-fires-through-subsumption
  (tu/with-terms [fatherOf parentOf hasChild A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'implies (list parentOf (symbol "?x") (symbol "?y"))
                       (list hasChild (symbol "?y") (symbol "?x"))) 'CxUniverse {:direction :forward})
    (v/assert kb (list fatherOf A B) 'CxUniverse {:strength :monotonic})
    (testing "a rule on the super-predicate fires on a sub-predicate fact"
      (is (seq (v/sentexes-matching kb (list hasChild B A) 'CxUniverse))))))

(tu/deftest-kb ask-reaches-through-subsumption-and-follows-belief
  (tu/with-terms [fatherOf parentOf A B]
    (v/assert kb (list fatherOf A B) 'CxUniverse {:strength :monotonic})
    (testing "before the genl edge, a parentOf goal is not answered by the fatherOf fact"
      (is (not (v/ask? kb (list parentOf A B) 'CxUniverse))))
    (let [edge (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})]
      (testing "with the edge, the goal is answered by subsumption"
        (is (v/ask? kb (list parentOf A B) 'CxUniverse)))
      (testing "retracting the edge withdraws the subsumption (belief-following)"
        (v/retract! kb edge)
        (is (not (v/ask? kb (list parentOf A B) 'CxUniverse)))))))

;; ---- backward dual: a subtype-concluding rule answers a supertype goal ----

(tu/deftest-kb subsuming-unify-honors-consequent-specificity
  (tu/with-terms [fatherOf parentOf loves A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
    (let [x (symbol "?x") y (symbol "?y")]
      (testing "a fatherOf consequent answers a parentOf goal, binding the arguments"
        (is (= {x A y B}
               (res/subsuming-unify kb (list parentOf x y) (list fatherOf A B)))))
      (testing "an unrelated consequent does not"
        (is (nil? (res/subsuming-unify kb (list parentOf x y) (list loves A B)))))
      (testing "the equal-functor case is a plain unify, unchanged"
        (is (= {x A y B}
               (res/subsuming-unify kb (list parentOf x y) (list parentOf A B)))))
      (testing "one-way: a parentOf consequent does NOT answer a fatherOf goal (super ⊉ sub)"
        (is (nil? (res/subsuming-unify kb (list fatherOf x y) (list parentOf A B))))))))

(tu/deftest-kb concluding-rule-handles-is-specs-intersect-index
  (tu/with-terms [fatherOf parentOf sonOf A B]
    (let [rule (v/assert-rule kb [(list sonOf '?y '?x)] (list fatherOf '?x '?y)
                              'CxUniverse {:direction :backward})]
      (testing "before the edge, only fatherOf's own goal reaches the rule"
        (is (contains? (res/concluding-rule-handles kb fatherOf) rule))
        (is (not (contains? (res/concluding-rule-handles kb parentOf) rule))))
      (let [edge (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})]
        (testing "with fatherOf ⊑ parentOf, a parentOf goal reaches the fatherOf rule"
          (is (contains? (res/concluding-rule-handles kb parentOf) rule)))
        (testing "and it is exactly specs(parentOf) ∩ rules-by-consequent"
          (is (= (into #{} (mapcat #(seq (reads/as-stored-rules-by-consequent-global (:index kb) %)))
                       (tax/specs-global (reasoning/taxonomy kb) parentOf))
                 (res/concluding-rule-handles kb parentOf))))
        (testing "retracting the edge withdraws the rule from the parentOf goal"
          (v/retract! kb edge)
          (is (not (contains? (res/concluding-rule-handles kb parentOf) rule))))))))

(tu/deftest-kb all-chainers-answer-supertype-goal-from-subtype-rule
  ;; fatherOf ⊑ parentOf, and a *backward-only* rule concludes the subtype fatherOf
  ;; from a sonOf fact.  Forward chaining cannot fire a backward rule, so (fatherOf A B)
  ;; is never stored — the only way to answer a parentOf goal is to backward-chain the
  ;; rule and unify parentOf against its fatherOf consequent by subsumption.
  (tu/with-terms [fatherOf parentOf sonOf A B]
    (let [p (symbol "?p") c (symbol "?c")]
      (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list sonOf '?y '?x)] (list fatherOf '?x '?y)
                     'CxUniverse {:direction :backward})
      (v/assert kb (list sonOf B A) 'CxUniverse {:strength :monotonic})
      (testing "the subtype conclusion is never materialized (backward rule, no forward firing)"
        (is (nil? (v/handle-of kb (list fatherOf A B) 'CxUniverse)))
        (is (empty? (v/sentexes-matching kb (list parentOf A B) 'CxUniverse))))
      (testing "the node engine answers the parentOf goal via the fatherOf-concluding rule, with the right binding"
        (is (v/query? kb (list parentOf p c) 'CxUniverse {:max-depth 2}))
        (is (contains? (set (v/query kb (list parentOf p c) 'CxUniverse {:max-depth 2}))
                       {p A c B})))
      (testing "prove (recur DFS) agrees"
        (is (v/provable? kb (list parentOf p c) 'CxUniverse))
        (is (some #(and (= A (% p)) (= B (% c))) (v/prove kb (list parentOf p c) 'CxUniverse))))
      (testing "backward (lazy) agrees"
        (is (some #(and (= A (% p)) (= B (% c))) (v/prove kb (list parentOf p c) 'CxUniverse)))))))

;; ---- the fan-out is scoped by the vantage --------------------------------
;; A genl edge connects a sub-predicate's facts to a supertype pattern only where
;; the edge is visible: matching from a context that cannot see `(genl dog animal)`
;; does not reach `(dog Muffet)` from `(animal ?x)`, however visible the fact itself.
;; Both retrieval paths — the reference fan-out and the set-algebra twin — must
;; agree, and the any-context read keeps the global fan.

(tu/deftest-kb the-matching-fan-out-walks-only-visible-genl-edges
  (tu/with-terms [dog_t animal_t Muffet CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl dog_t animal_t) CxA)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (doseq [hierarchical? [true false]]
      (binding [res/*hierarchical-retrieval* hierarchical?]
        (testing (str "hierarchical-retrieval " hierarchical?)
          (testing "the edge is visible from A, so the supertype query reaches the fact"
            (is (seq (v/ask kb (list animal_t '?x) CxA))))
          (testing "and invisible from the sibling, which sees the fact but not the edge"
            (is (empty? (v/ask kb (list animal_t '?x) CxB))))
          (testing "the any-context read keeps the global fan"
            (is (seq (v/ask kb (list animal_t '?x) '?ctx)))))))))

(tu/deftest-kb a-subtype-concluding-rule-answers-only-where-the-edge-is-visible
  ;; the backward dual of the scoped fan-out: concluding-rule-handles intersects the
  ;; consequent index with the spec closure *as seen from the goal's context*, so a
  ;; rule concluding fatherOf answers a parentOf goal exactly where
  ;; (genl fatherOf parentOf) is visible — in all three chainers.
  (tu/with-terms [fatherOf parentOf sonOf A B CxA CxB]
    (let [p (symbol "?p") c (symbol "?c")]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl fatherOf parentOf) CxA {:strength :monotonic})
      (v/assert-rule kb [(list sonOf '?y '?x)] (list fatherOf '?x '?y)
                     'CxUniverse {:direction :backward})
      (v/assert kb (list sonOf B A) 'CxUniverse {:strength :monotonic})
      (testing "the goal is answered where the subtype edge is visible"
        (is (v/query? kb (list parentOf p c) CxA {:max-depth 2}))
        (is (v/provable? kb (list parentOf p c) CxA))
        (is (some #(and (= A (% p)) (= B (% c))) (v/prove kb (list parentOf p c) CxA))))
      (testing "and not where it is out of sight, though rule and fact are visible"
        (is (not (v/query? kb (list parentOf p c) CxB {:max-depth 2})))
        (is (not (v/provable? kb (list parentOf p c) CxB)))
        (is (empty? (v/prove kb (list parentOf p c) CxB))))
      (testing "the subtype goal itself still answers from either sibling"
        (is (v/query? kb (list fatherOf p c) CxB {:max-depth 2}))))))

;; ---- genlInverse: binary genl with the arguments swapped -----------------
;; `(genlInverse P Q)` means `(P x y)` entails `(Q y x)`.  The fan carries a parity bit:
;; a `genl` edge keeps it, a `genlInverse` edge flips it, so a chain answers with the
;; arguments swapped exactly when it holds an odd number of `genlInverse` edges.

(defn- chain!
  "Fresh binary predicates `p0 … pn` joined bottom-up by the relations `kinds` (each
  `'genl` or `'genlInverse`), every edge stated at `strength` in `CxUniverse`.  Answers
  `[preds edge-handles]`."
  ([kb kinds] (chain! kb kinds :monotonic))
  ([kb kinds strength]
   (let [ps (vec (repeatedly (inc (count kinds)) #(tu/fresh-term :predicate "rel")))
         es (mapv (fn [i k] (v/assert kb (list k (ps i) (ps (inc i))) 'CxUniverse {:strength strength}))
                  (range) kinds)]
     [ps es])))

(defn- pairs
  "The `[?x ?y]` pairs an open `(pred ?x ?y)` ask answers from `context`."
  [kb pred context]
  (set (map (juxt #(get % '?x) #(get % '?y)) (v/ask kb (list pred '?x '?y) context))))

(defn- because-premises
  "The sentences a stored conclusion's first justification rests on, as a set."
  [kb sentence]
  (let [w (tu/why-root kb (v/handle-of kb sentence 'CxUniverse))]
    (set (map :sentence (:because (first (:support w)))))))

(tu/deftest-kb a-genlInverse-edge-answers-the-swapped-goal
  (tu/with-terms [childOf parentOf Tom Bob]
    (v/assert kb (list childOf Bob Tom) 'CxUniverse {:strength :monotonic})
    (testing "before the edge, the swapped goal is not answered"
      (is (not (v/ask? kb (list parentOf Tom Bob) 'CxUniverse))))
    (let [edge (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :monotonic})]
      (testing "with the edge, (childOf Bob Tom) answers (parentOf Tom Bob)"
        (is (v/ask? kb (list parentOf Tom Bob) 'CxUniverse))
        (is (= #{[Tom Bob]} (pairs kb parentOf 'CxUniverse))))
      (testing "and not the unswapped spelling"
        (is (not (v/ask? kb (list parentOf Bob Tom) 'CxUniverse))))
      (testing "either argument bound"
        (is (= #{Bob} (set (map #(get % '?y) (v/ask kb (list parentOf Tom '?y) 'CxUniverse)))))
        (is (= #{Tom} (set (map #(get % '?x) (v/ask kb (list parentOf '?x Bob) 'CxUniverse))))))
      (testing "the reference fan-out and the set-algebra path agree"
        (doseq [h? [true false]]
          (binding [res/*hierarchical-retrieval* h?]
            (is (= #{[Tom Bob]} (pairs kb parentOf 'CxUniverse)) (str "hierarchical " h?)))))
      (testing "retracting the edge withdraws the answer"
        (v/retract! kb edge)
        (is (not (v/ask? kb (list parentOf Tom Bob) 'CxUniverse)))))))

(tu/deftest-kb a-genlInverse-edge-licenses-no-converse
  (tu/with-terms [childOf parentOf Tom Bob]
    (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list parentOf Tom Bob) 'CxUniverse {:strength :monotonic})
    (testing "a stored (parentOf Tom Bob) answers no childOf goal"
      (is (not (v/ask? kb (list childOf Bob Tom) 'CxUniverse)))
      (is (empty? (pairs kb childOf 'CxUniverse))))))

(tu/deftest-kb a-chain-swaps-exactly-when-it-holds-an-odd-number-of-genlInverse-edges
  (tu/with-terms [A B]
    (doseq [kinds [['genlInverse]
                   ['genlInverse 'genlInverse]
                   ['genlInverse 'genlInverse 'genlInverse]
                   ['genlInverse 'genlInverse 'genlInverse 'genlInverse]
                   ['genl 'genlInverse]
                   ['genlInverse 'genl]
                   ['genl 'genlInverse 'genl 'genlInverse 'genl]
                   ['genlInverse 'genl 'genlInverse 'genl 'genlInverse]]]
      (let [[ps] (chain! kb kinds)
            top  (peek ps)
            odd? (odd? (count (filter #{'genlInverse} kinds)))]
        (v/assert kb (list (ps 0) A B) 'CxUniverse {:strength :monotonic})
        (testing (pr-str kinds)
          (is (= (if odd? #{[B A]} #{[A B]}) (pairs kb top 'CxUniverse)))
          (doseq [h? [true false]]
            (binding [res/*hierarchical-retrieval* h?]
              (is (= (if odd? #{[B A]} #{[A B]}) (pairs kb top 'CxUniverse))
                  (str "hierarchical " h?)))))))))

(tu/deftest-kb an-even-genlInverse-chain-acts-exactly-like-a-genl-chain
  ;; two and four `genlInverse` edges against the same number of `genl` edges: the same
  ;; answers to the same goals, the same forward conclusion, and a justification of the
  ;; same shape — the rule, the fact, and one supporter per edge
  (tu/with-terms [A B C]
    (doseq [n [2 4]]
      (let [[gs ges] (chain! kb (repeat n 'genl))
            [vs ies] (chain! kb (repeat n 'genlInverse))
            outg     (tu/fresh-term :predicate "outG")
            outi     (tu/fresh-term :predicate "outI")]
        (v/assert kb (list 'implies (list (peek gs) '?x '?y) (list outg '?x '?y)) 'CxUniverse {:direction :forward})
        (v/assert kb (list 'implies (list (peek vs) '?x '?y) (list outi '?x '?y)) 'CxUniverse {:direction :forward})
        (v/assert kb (list (gs 0) A B) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list (vs 0) A B) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list (gs 2) B C) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list (vs 2) B C) 'CxUniverse {:strength :monotonic})
        (testing (str n " edges: the same answers")
          (is (= #{[A B] [B C]} (pairs kb (peek gs) 'CxUniverse)))
          (is (= (pairs kb (peek gs) 'CxUniverse) (pairs kb (peek vs) 'CxUniverse))))
        (testing (str n " edges: the same forward conclusion, unswapped")
          (is (v/handle-of kb (list outg A B) 'CxUniverse))
          (is (v/handle-of kb (list outi A B) 'CxUniverse))
          (is (nil? (v/handle-of kb (list outi B A) 'CxUniverse))))
        (testing (str n " edges: the same justification shape, naming every edge")
          (let [pg (because-premises kb (list outg A B))
                pi (because-premises kb (list outi A B))]
            (is (= (inc n) (count pg) (count pi)))
            (is (contains? pi (list (vs 0) A B)))
            (is (= (set (map #(:sentence (v/sentex kb %)) ies))
                   (disj pi (list (vs 0) A B))))
            (is (= (set (map #(:sentence (v/sentex kb %)) ges))
                   (disj pg (list (gs 0) A B))))))))))

(tu/deftest-kb an-odd-genlInverse-chain-acts-like-one-genlInverse-edge
  (tu/with-terms [A B]
    (doseq [n [1 3]]
      (let [[ps es] (chain! kb (repeat n 'genlInverse))
            out     (tu/fresh-term :predicate "out")]
        (v/assert kb (list 'implies (list (peek ps) '?x '?y) (list out '?x '?y)) 'CxUniverse {:direction :forward})
        (v/assert kb (list (ps 0) A B) 'CxUniverse {:strength :monotonic})
        (testing (str n " edges: swapped")
          (is (= #{[B A]} (pairs kb (peek ps) 'CxUniverse)))
          (is (v/handle-of kb (list out B A) 'CxUniverse))
          (is (nil? (v/handle-of kb (list out A B) 'CxUniverse))))
        (testing (str n " edges: the justification names each edge and the fact")
          (is (= (conj (set (map #(:sentence (v/sentex kb %)) es)) (list (ps 0) A B))
                 (because-premises kb (list out B A)))))))))

(tu/deftest-kb a-forward-rule-fires-through-a-genlInverse-edge
  ;; the fatherOf/parentOf shape of `forward-chaining-fires-through-subsumption`, swapped
  (tu/with-terms [childOf parentOf hasChild Tom Bob]
    (let [edge (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :monotonic})
          _    (v/assert kb (list 'implies (list parentOf '?x '?y) (list hasChild '?x '?y))
                         'CxUniverse {:direction :forward})
          fact (v/assert kb (list childOf Bob Tom) 'CxUniverse {:strength :monotonic})
          h    (v/handle-of kb (list hasChild Tom Bob) 'CxUniverse)]
      (testing "the rule on parentOf fires on the childOf fact, swapped"
        (is h)
        (is (nil? (v/handle-of kb (list hasChild Bob Tom) 'CxUniverse))))
      (testing "the justification names the genlInverse edge and the fact"
        (is (= #{edge fact} (set (map :handle (:because (first (:support (tu/why-root kb h)))))))))
      (testing "argue reads the stored conclusion's justification"
        (let [a (v/argue kb (list hasChild Tom Bob) 'CxUniverse)]
          (is (= :true (:verdict a)))
          (is (some #(= edge (:handle %)) (:because (first (:support (tu/why-root (:for-why a)))))))))
      (testing "retracting the edge withdraws the conclusion"
        (v/retract! kb edge)
        (is (not (v/ask? kb (list hasChild Tom Bob) 'CxUniverse)))))))

(tu/deftest-kb the-fact-arriving-first-fires-the-rule-when-the-edge-arrives
  (tu/with-terms [childOf parentOf hasChild Tom Bob]
    (v/assert kb (list childOf Bob Tom) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list hasChild '?x '?y))
              'CxUniverse {:direction :forward})
    (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :monotonic})
    (is (v/handle-of kb (list hasChild Tom Bob) 'CxUniverse))))

(defn- inverse-join!
  "Assert `(inverse childOf parentOf)` in `inverse-cx`, and `(childOf C0 P0)` and the
  forward rule `(parentOf ?p ?c) → (parent_ ?p)` in `CxTop`, in `order`.  Answers
  `{:inverse h :fact h}`."
  [kb order [childOf parentOf parent_ C0 P0 CxTop] inverse-cx]
  (into {} (for [step order]
             [step (case step
                     :inverse (v/assert kb (list 'inverse childOf parentOf) inverse-cx {:strength :monotonic})
                     :fact    (v/assert kb (list childOf C0 P0) CxTop {:strength :monotonic})
                     :rule    (v/assert kb (list 'implies (list parentOf '?p '?c) (list parent_ '?p))
                                        CxTop {:direction :forward}))])))

(tu/deftest-kb a-forward-rule-joins-a-declared-inverse-partner-in-every-arrival-order
  (doseq [order (tu/permutations [:inverse :fact :rule])]
    (tu/with-terms [childOf parentOf parent_ C0 P0 CxTop]
      (v/assert kb (list 'genlCx CxTop 'CxUniverse) 'CxUniverse)
      (let [terms     [childOf parentOf parent_ C0 P0 CxTop]
            believed? #(boolean (some->> (v/handle-of kb (list parent_ P0) CxTop) (v/believed? kb)))]
        (testing (str order " with the inverse beside the fact")
          (let [{:keys [inverse fact]} (inverse-join! kb order terms CxTop)]
            (is (believed?))
            (v/retract! kb inverse)
            (is (not (believed?)) "retracting the inverse withdraws it")
            (v/assert kb (list 'inverse childOf parentOf) CxTop {:strength :monotonic})
            (is (believed?))
            (v/retract! kb fact)
            (is (not (believed?)) "retracting the fact withdraws it")))))
    (tu/with-terms [childOf parentOf parent_ C0 P0 CxTop CxLow]
      (v/assert kb (list 'genlCx CxTop 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxLow CxTop) 'CxUniverse)
      (testing (str order " with the inverse in CxLow, a decontextualized_predicate's sentence")
        (inverse-join! kb order [childOf parentOf parent_ C0 P0 CxTop] CxLow)
        (is (v/ask? kb (list parentOf P0 C0) CxTop))
        (is (some->> (v/handle-of kb (list parent_ P0) CxTop) (v/believed? kb)))))))

(tu/deftest-kb a-fact-the-fan-reaches-as-written-and-swapped-fires-each-reading-over-its-own-path
  (doseq [order (tu/permutations [:inverse :fact :rule])]
    (tu/with-terms [childOf parentOf kinOf kin_ A B]
      (v/assert kb (list 'genl parentOf kinOf) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl childOf kinOf) 'CxUniverse {:strength :monotonic})
      (let [hs        (into {} (for [step order]
                                 [step (case step
                                         :inverse (v/assert kb (list 'inverse childOf parentOf) 'CxUniverse
                                                            {:strength :monotonic})
                                         :fact    (v/assert kb (list parentOf A B) 'CxUniverse {:strength :monotonic})
                                         :rule    (v/assert kb (list 'implies (list kinOf '?x '?y) (list kin_ '?x))
                                                            'CxUniverse {:direction :forward}))]))
            believed? #(boolean (some->> (v/handle-of kb (list kin_ %) 'CxUniverse) (v/believed? kb)))]
        (testing (str order " (parentOf A B) is (kinOf A B), and read as (childOf B A), (kinOf B A)")
          (is (believed? A))
          (is (believed? B)))
        (testing (str order " the swapped reading names the inverse, the reading as written does not")
          (is (contains? (because-premises kb (list kin_ B)) (:sentence (v/sentex kb (:inverse hs)))))
          (v/retract! kb (:inverse hs))
          (is (believed? A))
          (is (not (believed? B))))))))

(tu/deftest-kb a-reading-across-a-swap-cycle-to-its-own-predicate-rests-on-the-cycle
  (doseq [cycle [:self-inverse :inverse-and-genl]
          order (tu/permutations [:cycle :fact :rule])]
    (tu/with-terms [relOf partnerOf out_ A B]
      (let [m         {:strength :monotonic}
            hs        (into {} (for [step order]
                                 [step (case step
                                         :cycle (if (= cycle :self-inverse)
                                                  [(v/assert kb (list 'inverse relOf relOf) 'CxUniverse m)]
                                                  [(v/assert kb (list 'inverse relOf partnerOf) 'CxUniverse m)
                                                   (v/assert kb (list 'genl partnerOf relOf) 'CxUniverse m)])
                                         :fact  (v/assert kb (list relOf A B) 'CxUniverse m)
                                         :rule  (v/assert kb (list 'implies (list relOf '?x '?y) (list out_ '?x))
                                                          'CxUniverse {:direction :forward}))]))
            believed? #(boolean (some->> (v/handle-of kb (list out_ %) 'CxUniverse) (v/believed? kb)))]
        (testing (str cycle " " order)
          (is (believed? A))
          (is (believed? B))
          (v/retract! kb (peek (:cycle hs)))
          (is (believed? A) "the reading as written rests on no edge")
          (is (not (believed? B)) "retracting an edge of the cycle withdraws the swapped reading"))))))

(defn- rests-on?
  "Does a justification of the stored `sentence` in CxUniverse name the sentex `h`?"
  [kb sentence h]
  (boolean (some (fn [j] (some #(= h (:handle %)) (:because j)))
                 (:support (tu/why-root kb (v/handle-of kb sentence 'CxUniverse))))))

(defn- second-route-rows!
  "Assert each row `[edge! second! depart!]` of `rows` with the fact `(pOf A B)` and the
  forward rule `(qOf ?x ?y) → (out_ ?x)`, in every arrival order.  The firing names the
  departing edge.  After `depart!` the second route still answers `(qOf B A)`, and
  `(out_ B)` is believed."
  [kb rows]
  (doseq [[label [edge! second! depart!]] rows
          order (tu/permutations [:edge :second :fact :rule])]
    (tu/with-terms [pOf qOf rOf out_ A B]
      (let [m  {:strength :monotonic}
            hs (into {} (for [step order]
                          [step (case step
                                  :edge   (edge! pOf qOf rOf)
                                  :second (second! pOf qOf rOf)
                                  :fact   (v/assert kb (list pOf A B) 'CxUniverse m)
                                  :rule   (v/assert kb (list 'implies (list qOf '?x '?y) (list out_ '?x))
                                                    'CxUniverse {:direction :forward}))]))]
        (testing (str label " " order)
          (is (rests-on? kb (list out_ B) (:edge hs)) "the firing names the departing edge")
          (depart! pOf qOf (:edge hs))
          (is (v/ask? kb (list qOf B A) 'CxUniverse))
          (is (some->> (v/handle-of kb (list out_ B) 'CxUniverse) (v/believed? kb))))))))

(tu/deftest-kb a-retracted-swap-edge-leaves-the-firing-a-second-route-licenses
  (let [m {:strength :monotonic}]
    (second-route-rows!
     kb {"a genlInverse beside an inverse"
         [(fn [p q _] (v/assert kb (list 'genlInverse p q) 'CxUniverse m))
          (fn [p q _] (v/assert kb (list 'inverse p q) 'CxUniverse m))
          (fn [_ _ h] (v/retract! kb h))]
         "a genlInverse beside a genlInverse and a genl edge"
         [(fn [p q _] (v/assert kb (list 'genlInverse p q) 'CxUniverse m))
          (fn [p q r] (v/assert kb (list 'genlInverse p r) 'CxUniverse m)
            (v/assert kb (list 'genl r q) 'CxUniverse m))
          (fn [_ _ h] (v/retract! kb h))]})))

(tu/deftest-kb a-defeated-swap-edge-leaves-the-firing-a-second-route-licenses
  (let [m {:strength :monotonic}]
    (second-route-rows!
     kb {"a defeated :default genlInverse beside a genlInverse and a genl edge"
         [(fn [p q _] (v/assert kb (list 'genlInverse p q) 'CxUniverse {:strength :default}))
          (fn [p q r] (v/assert kb (list 'genlInverse p r) 'CxUniverse m)
            (v/assert kb (list 'genl r q) 'CxUniverse m))
          (fn [p q _] (v/assert kb (list 'not (list 'genlInverse p q)) 'CxUniverse m))]})))

(tu/deftest-kb an-except-on-a-swap-edge-hides-a-firing-where-no-second-route-licenses-it
  (doseq [[label edges second neg? lit seen?]
          [["genlInverse alone"          (fn [p q _] [(list 'genlInverse p q)]) (fn [_ _ _] []) false :q false]
           ["genlInverse beside genl"    (fn [p q _] [(list 'genlInverse p q)]) (fn [p q _] [(list 'genl p q)]) false :q false]
           ["genlInverse beside an odd route" (fn [p q _] [(list 'genlInverse p q)])
            (fn [p q r] [(list 'genlInverse p r) (list 'genl r q)]) false :q true]
           ["genlInverse beside an even route" (fn [p q _] [(list 'genlInverse p q)])
            (fn [p q r] [(list 'genlInverse p r) (list 'inverse r q)]) false :q false]
           ["inverse alone"              (fn [p q _] [(list 'inverse p q)]) (fn [_ _ _] []) false :q false]
           ["inverse beside an odd route" (fn [p q _] [(list 'inverse p q)])
            (fn [p q r] [(list 'genlInverse p r) (list 'genl r q)]) false :q true]
           ["inverse beside the reverse edge" (fn [p q _] [(list 'inverse p q)])
            (fn [p q _] [(list 'genlInverse q p)]) false :q false]
           ["negated, genlInverse alone" (fn [p q _] [(list 'genlInverse q p)]) (fn [_ _ _] []) true :q false]
           ["negated, genlInverse beside an odd route" (fn [p q _] [(list 'genlInverse q p)])
            (fn [p q r] [(list 'genlInverse q r) (list 'genl r p)]) true :q true]
           ["negated, inverse alone"     (fn [p q _] [(list 'inverse q p)]) (fn [_ _ _] []) true :q false]
           ["negated, inverse beside an odd route" (fn [p q _] [(list 'inverse q p)])
            (fn [p q r] [(list 'genlInverse q r) (list 'genl r p)]) true :q true]
           ["self-inverse alone"         (fn [p _ _] [(list 'inverse p p)]) (fn [_ _ _] []) false :p false]
           ["self-inverse beside an odd route" (fn [p _ _] [(list 'inverse p p)])
            (fn [p _ r] [(list 'genlInverse p r) (list 'genl r p)]) false :p true]
           ["an inverse and genl cycle alone" (fn [p q _] [(list 'inverse p q) (list 'genl q p)])
            (fn [_ _ _] []) false :p false]
           ["an inverse and genl cycle beside an odd route" (fn [p q _] [(list 'inverse p q) (list 'genl q p)])
            (fn [p _ r] [(list 'genlInverse p r) (list 'genl r p)]) false :p true]]
          edge-last? [false true]]
    (tu/with-terms [pOf qOf rOf out_ A B CxHide]
      (let [m    {:strength :monotonic}
            put! (fn [ss] (mapv #(v/assert kb % 'CxUniverse m) ss))
            _    (v/assert kb (list 'genlCx CxHide 'CxUniverse) 'CxUniverse m)
            es   (when-not edge-last? (put! (edges pOf qOf rOf)))
            _    (put! (second pOf qOf rOf))
            es   (or es (put! (edges pOf qOf rOf)))
            l    (if (= :p lit) pOf qOf)
            neg  #(if neg? (list 'not %) %)]
        (v/assert kb (neg (list pOf A B)) 'CxUniverse m)
        (v/assert kb (list 'implies (neg (list l '?x '?y)) (list out_ '?x)) 'CxUniverse {:direction :forward})
        (testing (str label (when edge-last? ", the edge last"))
          (is (v/ask? kb (list out_ B) 'CxUniverse))
          (v/assert kb (list 'except (sx/sentex-handle (first es))) CxHide m)
          (is (= seen? (v/ask? kb (list out_ B) CxHide))))))))

(tu/deftest-kb a-default-genlInverse-edge-is-defeasible
  (tu/with-terms [childOf parentOf hasChild Tom Bob]
    (let [edge (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :default})]
      (v/assert kb (list 'implies (list parentOf '?x '?y) (list hasChild '?x '?y))
                'CxUniverse {:direction :forward})
      (v/assert kb (list childOf Bob Tom) 'CxUniverse {:strength :monotonic})
      (testing "believed: the swapped goal answers, and the conclusion holds at the edge's class"
        (is (v/ask? kb (list parentOf Tom Bob) 'CxUniverse))
        (is (= :default (:defeat-class (tu/why-root kb (v/handle-of kb (list hasChild Tom Bob) 'CxUniverse))))))
      (let [hn (v/assert kb (list 'not (list 'genlInverse childOf parentOf)) 'CxUniverse
                         {:strength :monotonic})]
        (testing "defeated: neither the swapped goal nor the conclusion"
          (is (not (v/believed? kb edge)))
          (is (not (v/ask? kb (list parentOf Tom Bob) 'CxUniverse)))
          (is (not (v/ask? kb (list hasChild Tom Bob) 'CxUniverse))))
        (testing "retracting the defeater revives both"
          (v/retract! kb hn)
          (is (v/ask? kb (list parentOf Tom Bob) 'CxUniverse))
          (is (v/ask? kb (list hasChild Tom Bob) 'CxUniverse)))))))

(tu/deftest-kb an-except-on-the-genlInverse-edge-hides-its-conclusions
  (tu/with-terms [childOf parentOf Tom Bob CxHide]
    (v/assert kb (list 'genlCx CxHide 'CxUniverse) 'CxUniverse {:strength :monotonic})
    (let [edge (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :monotonic})]
      (v/assert kb (list childOf Bob Tom) 'CxUniverse {:strength :monotonic})
      (is (v/ask? kb (list parentOf Tom Bob) CxHide))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle edge)) CxHide {:strength :monotonic})]
        (testing "the context holding the except reads no swap"
          (is (not (v/ask? kb (list parentOf Tom Bob) CxHide))))
        (testing "the context above it still does"
          (is (v/ask? kb (list parentOf Tom Bob) 'CxUniverse)))
        (testing "retracting the except restores it"
          (v/retract! kb eh)
          (is (v/ask? kb (list parentOf Tom Bob) CxHide)))))))

(tu/deftest-kb a-genlInverse-edge-answers-only-where-it-is-visible
  (tu/with-terms [childOf parentOf Tom Bob CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlInverse childOf parentOf) CxA {:strength :monotonic})
    (v/assert kb (list childOf Bob Tom) 'CxUniverse {:strength :monotonic})
    (doseq [h? [true false]]
      (binding [res/*hierarchical-retrieval* h?]
        (testing (str "hierarchical-retrieval " h?)
          (is (v/ask? kb (list parentOf Tom Bob) CxA))
          (is (not (v/ask? kb (list parentOf Tom Bob) CxB)))
          (is (v/ask? kb (list parentOf Tom Bob) '?ctx)))))))

(tu/deftest-kb a-genlInverse-edge-swaps-only-binary-facts
  (tu/with-terms [rel3 sup3 A B C]
    (v/assert kb (list 'genlInverse rel3 sup3) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list rel3 A B C) 'CxUniverse {:strength :monotonic})
    (testing "a ternary fact answers no goal on the general predicate"
      (is (empty? (v/ask kb (list sup3 '?x '?y '?z) 'CxUniverse)))
      (is (empty? (v/ask kb (list sup3 '?x '?y) 'CxUniverse))))))

(tu/deftest-kb a-negation-carries-through-a-genlInverse-edge-contrapositively
  ;; (P x y) ⊢ (Q y x), so ¬(Q y x) ⊢ ¬(P x y)
  (tu/with-terms [childOf parentOf Tom Bob]
    (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'not (list parentOf Tom Bob)) 'CxUniverse {:strength :monotonic})
    (is (v/ask? kb (list 'not (list childOf Bob Tom)) 'CxUniverse))
    (is (not (v/ask? kb (list 'not (list childOf Tom Bob)) 'CxUniverse)))))

(tu/deftest-kb a-rule-concluding-a-genlInverse-spec-answers-the-general-goal
  ;; the backward dual: a backward-only rule concludes childOf, and a parentOf goal is
  ;; answered through it with the arguments swapped
  (tu/with-terms [childOf parentOf sonOf Tom Bob]
    (let [p (symbol "?p") c (symbol "?c")]
      (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :monotonic})
      (v/assert-rule kb [(list sonOf '?x '?y)] (list childOf '?x '?y)
                     'CxUniverse {:direction :backward})
      (v/assert kb (list sonOf Bob Tom) 'CxUniverse {:strength :monotonic})
      (testing "the node engine"
        (is (contains? (set (v/query kb (list parentOf p c) 'CxUniverse {:max-depth 2}))
                       {p Tom c Bob}))
        (is (not (v/query? kb (list parentOf Bob Tom) 'CxUniverse {:max-depth 2}))))
      (testing "prove"
        (is (some #(and (= Tom (% p)) (= Bob (% c))) (v/prove kb (list parentOf p c) 'CxUniverse)))))))

(tu/deftest-kb with-no-genlInverse-edge-the-fan-is-the-genl-closure
  ;; the relation-genl reading is untouched when no genlInverse edge exists
  (tu/with-terms [fatherOf motherOf parentOf A B]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list fatherOf A B) 'CxUniverse {:strength :monotonic})
    (let [tx (reasoning/taxonomy kb)]
      (is (= (tax/specs tx parentOf 'CxUniverse) (res/sub-predicates kb parentOf 'CxUniverse)))
      (is (= (tax/specs-global tx parentOf) (res/sub-predicates kb parentOf '?ctx)))
      (is (= (tax/genls tx fatherOf 'CxUniverse) (res/super-predicates kb fatherOf 'CxUniverse)))
      (is (empty? (res/swapped-sub-predicates kb parentOf 'CxUniverse)))
      (is (empty? (res/swapped-super-predicates kb fatherOf 'CxUniverse))))))

;; ---- a wide fan: read only the members that can hold the goal's arguments ------------

(defn- wide-fan!
  "A binary `top` with `n` predicates under it, one in three across a `genlInverse` edge
  and one in five marked `symmetric`, and a fact on a few of them.  Answers `top`."
  [kb n [A B C]]
  (let [top (tu/fresh-term :predicate "top")
        ps  (vec (repeatedly n #(tu/fresh-term :predicate "member")))]
    (doseq [[i p] (map-indexed vector ps)]
      (v/assert kb (list (if (zero? (mod i 3)) 'genlInverse 'genl) p top) 'CxUniverse {:strength :monotonic})
      (when (zero? (mod i 5)) (v/assert kb (list 'symmetric p) 'CxUniverse)))
    (doseq [[p x y] [[(ps 0) A B] [(ps 1) A B] [(ps 2) B A] [(ps 5) B C] [(ps 7) C A] [(ps 10) A C]]]
      (v/assert kb (list p x y) 'CxUniverse {:strength :monotonic}))
    (v/assert kb (list 'not (list (ps 4) A C)) 'CxUniverse {:strength :monotonic})
    top))

(tu/deftest-kb a-wide-fan-answers-what-reading-every-member-answers
  ;; `slot-cut` leaves out the members whose slot predicate sets miss a ground argument; the
  ;; members left are read as the uncut fan reads them, so the two answer one set
  (tu/with-terms [A B C D]
    (let [top   (wide-fan! kb 90 [A B C])
          raw   (fn [s] (res/raw-match kb s '?ctx))
          whole #(proj (res/fanned-match kb % '?ctx raw res/lazy-mapcat false))
          cut   #(proj (res/fanned-match kb % '?ctx raw res/lazy-mapcat true))]
      (doseq [pat [(list top A B) (list top B A) (list top A C) (list top C A) (list top A D)
                   (list top A '?y) (list top '?x A) (list top '?x C) (list top D '?y)
                   (list top '?x '?y) (list top 3 '?y)
                   (list 'not (list top A C)) (list 'not (list top '?x C))]]
        (is (= (whole pat) (cut pat)) (pr-str pat)))
      (testing "and it reaches what the members store"
        (is (seq (cut (list top A B))))
        (is (seq (cut (list top '?x A))))))))

(tu/deftest-kb a-wide-fan-reads-only-the-members-holding-its-arguments
  (tu/with-terms [A B C D]
    (let [top   (wide-fan! kb 90 [A B C])
          reads (atom 0)
          raw   (fn [s] (swap! reads inc) (res/raw-match kb s '?ctx))
          n     (fn [pat indexed?] (reset! reads 0)
                  (dorun (res/fanned-match kb pat '?ctx raw res/lazy-mapcat indexed?))
                  @reads)]
      (testing "uncut, every member is read"
        (is (= 91 (n (list top A D) false))))
      (testing "cut, only the members storing both arguments"
        (is (zero? (n (list top A D) true)))
        (is (<= (n (list top A B) true) 3)))
      (testing "a goal naming no indexable argument reads them all"
        (is (= 91 (n (list top '?x '?y) true)))))))

(tu/deftest-kb concludes?-answers-whether-a-rule-concludes-the-goal
  (tu/with-terms [fatherOf parentOf sonOf likes]
    (is (false? (res/concludes? kb parentOf nil)))
    (let [rule (v/assert-rule kb [(list sonOf '?y '?x)] (list fatherOf '?x '?y)
                              'CxUniverse {:direction :backward})]
      (is (false? (res/concludes? kb parentOf nil)))
      (let [edge (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse {:strength :monotonic})]
        (is (true? (res/concludes? kb parentOf nil)))
        (v/retract! kb edge))
      (v/retract! kb rule))
    (testing "a variable-consequent rule concludes every predicate"
      (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list likes '?p '?x '?y)] '(?p ?x ?y)))
                'CxNaturalWorld)
      (is (true? (res/concludes? kb parentOf nil))))
    (doseq [p [parentOf fatherOf sonOf likes]]
      (is (= (boolean (seq (res/concluding-rule-handles kb p nil))) (res/concludes? kb p nil)) (pr-str p)))))

(tu/deftest-kb the-signed-fan-follows-its-edges
  ;; memoized on the change clock, so an edge arriving or leaving moves the next read
  (tu/with-terms [childOf parentOf sonOf]
    (let [tx  (reasoning/taxonomy kb)
          fan #(tax/signed-closure tx :down parentOf 'CxUniverse)]
      (v/assert kb (list 'genlInverse childOf parentOf) 'CxUniverse {:strength :monotonic})
      (is (= [#{parentOf} #{childOf}] (fan)))
      (let [edge (v/assert kb (list 'genl sonOf childOf) 'CxUniverse {:strength :monotonic})]
        (is (= [#{parentOf} #{childOf sonOf}] (fan)))
        (v/retract! kb edge)
        (is (= [#{parentOf} #{childOf}] (fan)))))))
