;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.intersection-test
  "The `intersection` definitional collection relation: (intersection ?combined . ?types)
  declares ?combined as the intersection of ?types. Two defining directions, each proven
  to *fire* into materialized, justified facts:

    * intersection -> genl: the combined kind is a subtype of each type it intersects.
    * membership: a thing that is each type is concluded a member of the combined kind
      (a generator generates a concrete-functor rule per intersection fact, since the
      membership consequent's predicate is a variable).

  Two and three types, over kinds and over binary predicates. See CxUniverse."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- believes?
  [kb sentence ctx]
  (boolean (seq (v/sentexes-matching kb sentence ctx))))

;; ---- the arity floor -----------------------------------------------------

(tu/deftest-kb one-type-intersection-is-out-below-the-arity-floor
  (tu/with-terms [combined_kind type_a]
    (v/assert kb (list 'genl type_a 'thing) 'CxUniverse)
    ;; arityMin is three (the combined kind plus at least two types); the intersection
    ;; of a single type is that type, and the tuple is held inert and read OUT.
    (is (tu/stored-in-clash? kb (list 'intersection combined_kind type_a) 'CxUniverse)
        "(intersection combined one-type) is one argument below the floor")))

;; ---- binary: intersection -> genl ----------------------------------------

(tu/deftest-kb binary-intersection-derives-genl-of-each-type
  (tu/with-terms [combined_kind type_a type_b]
    (v/assert kb (list 'genl type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'intersection combined_kind type_a type_b) 'CxUniverse)
    (is (v/ask? kb (list 'genl combined_kind type_a) 'CxUniverse)
        "combined kind is genl the first type it intersects")
    (is (v/ask? kb (list 'genl combined_kind type_b) 'CxUniverse)
        "combined kind is genl the second type it intersects")))

;; ---- binary: membership --------------------------------------------------

(tu/deftest-kb binary-intersection-concludes-membership-from-the-conjuncts
  (tu/with-terms [combined_kind type_a type_b]
    (v/assert kb (list 'genl type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'unary combined_kind) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'intersection combined_kind type_a type_b) 'CxUniverse)
    (v/assert kb (list type_a 'Item) 'CxUniverse)
    (v/assert kb (list type_b 'Item) 'CxUniverse)
    (is (believes? kb (list combined_kind 'Item) 'CxUniverse)
        "a thing that is each type is a member of the combined kind")))

(tu/deftest-kb binary-intersection-membership-needs-every-conjunct
  (tu/with-terms [combined_kind type_a type_b]
    (v/assert kb (list 'genl type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'unary combined_kind) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'intersection combined_kind type_a type_b) 'CxUniverse)
    (v/assert kb (list type_a 'Item) 'CxUniverse)
    (is (not (believes? kb (list combined_kind 'Item) 'CxUniverse))
        "being only one of the types does not make a member of the combined kind")))

;; ---- ternary -------------------------------------------------------------

(tu/deftest-kb ternary-intersection-derives-genl-and-membership
  (tu/with-terms [combined_kind type_a type_b type_c]
    (v/assert kb (list 'genl type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'genl type_c 'thing) 'CxUniverse)
    (v/assert kb (list 'unary combined_kind) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'intersection combined_kind type_a type_b type_c) 'CxUniverse)
    (is (v/ask? kb (list 'genl combined_kind type_c) 'CxUniverse)
        "combined kind is genl the third type in a ternary intersection")
    (testing "membership requires all three"
      (v/assert kb (list type_a 'Item) 'CxUniverse)
      (v/assert kb (list type_b 'Item) 'CxUniverse)
      (is (not (believes? kb (list combined_kind 'Item) 'CxUniverse))
          "two of three is not enough")
      (v/assert kb (list type_c 'Item) 'CxUniverse)
      (is (believes? kb (list combined_kind 'Item) 'CxUniverse)
          "all three makes a member"))))

(tu/deftest-kb a-declaration-below-cxuniverse-leaves-one-generated-membership-rule
  (tu/with-terms [CxBelow combined_kind type_a type_b tagOf]
    (v/assert kb (list 'genlCx CxBelow 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate combined_kind) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'arg tagOf 1 combined_kind) CxBelow)
    (v/assert kb (list 'intersection combined_kind type_a type_b) 'CxUniverse)
    (let [rule (list 'implies (list 'and (list type_a '?x) (list type_b '?x)) (list combined_kind '?x))]
      (is (some? (v/handle-of kb rule 'CxUniverse)) "the membership rule is generated in CxUniverse")
      (is (nil? (v/handle-of kb rule CxBelow)) "and not again in CxBelow"))
    (v/assert kb (list type_a 'Item) CxBelow)
    (v/assert kb (list type_b 'Item) CxBelow)
    (is (believes? kb (list combined_kind 'Item) CxBelow)
        "CxBelow concludes the membership from the CxUniverse rule")))

(defn- tuple?
  "Is `sentence` believed in CxUniverse?  A failing `is` prints it, not the KB."
  [sentence]
  (believes? tu/*kb* sentence 'CxUniverse))

(tu/deftest-kb a-binary-intersection-derives-genl-of-each-predicate
  (tu/with-terms [can able may]
    (doseq [p [can able may]] (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (list 'intersection can able may) 'CxUniverse)
    (is (v/ask? kb (list 'genl can able) 'CxUniverse))
    (is (v/ask? kb (list 'genl can may) 'CxUniverse))))

(tu/deftest-kb a-binary-intersection-concludes-the-tuple-from-each-component
  (tu/with-terms [can able may]
    (doseq [p [can able may]] (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (list 'intersection can able may) 'CxUniverse)
    (v/assert kb (list able 'Alice 'kayaking) 'CxUniverse)
    (testing "one component is not enough"
      (is (not (tuple? (list can 'Alice 'kayaking)))))
    (v/assert kb (list may 'Alice 'kayaking) 'CxUniverse)
    (testing "both components make a tuple of the combined predicate"
      (is (tuple? (list can 'Alice 'kayaking))))
    (testing "and the components of two different tuples do not combine"
      (v/assert kb (list able 'Bob 'kayaking) 'CxUniverse)
      (v/assert kb (list may 'Bob 'rowing) 'CxUniverse)
      (is (not (tuple? (list can 'Bob 'kayaking))))
      (is (not (tuple? (list can 'Bob 'rowing)))))))

(tu/deftest-kb a-three-way-binary-intersection-needs-all-three-components
  (tu/with-terms [can able may wants]
    (doseq [p [can able may wants]] (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (list 'intersection can able may wants) 'CxUniverse)
    (is (v/ask? kb (list 'genl can wants) 'CxUniverse))
    (v/assert kb (list able 'Alice 'kayaking) 'CxUniverse)
    (v/assert kb (list may 'Alice 'kayaking) 'CxUniverse)
    (is (not (tuple? (list can 'Alice 'kayaking))) "two of three is not enough")
    (v/assert kb (list wants 'Alice 'kayaking) 'CxUniverse)
    (is (tuple? (list can 'Alice 'kayaking)) "all three make the tuple")))

(tu/deftest-kb a-binary-intersection-concludes-no-one-argument-tuple
  (tu/with-terms [can able may]
    (doseq [p [can able may]] (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (let [before (set (v/violations kb))]
      (v/assert kb (list 'intersection can able may) 'CxUniverse)
      (v/assert kb (list able 'Alice 'kayaking) 'CxUniverse)
      (v/assert kb (list may 'Alice 'kayaking) 'CxUniverse)
      (is (nil? (v/handle-of kb (list 'implies (list 'and (list able '?x) (list may '?x)) (list can '?x))
                             'CxUniverse))
          "a binary combined predicate generates no unary membership rule")
      (is (empty? (v/sentexes-matching kb (list can '?x) 'CxUniverse))
          "so it concludes no one-argument tuple")
      (is (= before (set (v/violations kb))) "and files no violation"))))

;; ---- the unary rule's guard is the arity-1 class membership ---------------
;; The unary membership generator takes a combined kind that is a member of a class
;; relationTypeByArity maps to 1.  Each test below checks how the generated rule is
;; justified: by a firing of a rule with no arity antecedent, resting on no rule that
;; concludes an arity.  The lazy-forward converse concludes one, so a rule generated
;; through it fails that check.

(defn- unwrapped
  "`rule` without its `set/…` direction wrappers."
  [rule]
  (if (and (seq? rule) (symbol? (first rule)) (= "set" (namespace (first rule))))
    (recur (second rule))
    rule))

(defn- reads-arity?
  "Is `s` a rule with an `arity` antecedent, or a rule concluding an `arity`?"
  [s]
  (let [r (unwrapped s)]
    (boolean
     (when (and (seq? r) (= 'implies (first r)))
       (let [[_ ante conseq] r
             lits (if (and (seq? ante) (= 'and (first ante))) (rest ante) [ante])]
         (or (some #(and (seq? %) (= 'arity (first %))) lits)
             (and (seq? conseq) (= 'arity (first conseq)))))))))

(defn- generation
  "How the KB holds the generated rule at handle `h`.  `:believed?` is its belief.
  `:reads-arity?` says whether one of its justifications is a firing of a rule reading
  an `arity`, or names a rule concluding one among its antecedents.  `:because` is the
  antecedent handles of its justifications."
  [kb h]
  (if (nil? h)
    {:believed? false :reads-arity? false :because #{}}
    (let [{:keys [nodes]} (v/why kb h)
          node            (get nodes h)
          sups            (:support node)]
      {:believed?    (boolean (:believed? node))
       :reads-arity? (boolean (some (fn [s]
                                      (or (reads-arity? (:rule s))
                                          (some #(reads-arity? (:sentence (get nodes %)))
                                                (:because s))))
                                    sups))
       :because      (into #{} (mapcat :because) sups)})))

(defn- unary-rule
  "The unary membership rule an intersection of `parts` into `combined` generates."
  [combined parts]
  (list 'implies (cons 'and (map #(list % '?x) parts)) (list combined '?x)))

(defn- intersection-world!
  "Assert two types below `thing`, their intersection into `combined` and a member of
  each type at `:monotonic`, in CxUniverse."
  [kb combined type-a type-b]
  (let [mono {:strength :monotonic}]
    (v/assert kb (list 'genl type-a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl type-b 'thing) 'CxUniverse)
    (v/assert kb (list 'intersection combined type-a type-b) 'CxUniverse mono)
    (v/assert kb (list type-a 'Item) 'CxUniverse mono)
    (v/assert kb (list type-b 'Item) 'CxUniverse mono)))

(tu/deftest-kb an-arity-of-one-alone-admits-a-kind-to-the-unary-membership-rule
  ;; No unary or unary_predicate declaration: the arity fact alone makes the kind
  ;; eligible, through the unary membership the forward class rule stores from it.
  (tu/with-terms [combined_kind type_a type_b]
    (v/assert kb (list 'arity combined_kind 1) 'CxUniverse {:strength :monotonic})
    (intersection-world! kb combined_kind type_a type_b)
    (let [g (generation kb (v/handle-of kb (unary-rule combined_kind [type_a type_b]) 'CxUniverse))]
      (is (:believed? g) "the unary membership rule is generated")
      (is (not (:reads-arity? g)) "from the class membership, not through an arity guard"))
    (is (believes? kb (list combined_kind 'Item) 'CxUniverse)
        "and concludes the membership")))

(tu/deftest-kb a-class-a-kb-maps-to-one-admits-its-members-to-the-unary-membership-rule
  ;; monadic_kind is a class of the test's own, mapped to 1 by its own mapping fact.
  (tu/with-terms [monadic_kind combined_kind type_a type_b]
    (v/assert kb (list 'genl monadic_kind 'fixed_arity) 'CxUniverse)
    (v/assert kb (list 'relationTypeByArity monadic_kind 1) 'CxUniverse {:strength :monotonic})
    (let [m (v/assert kb (list monadic_kind combined_kind) 'CxUniverse {:strength :monotonic})]
      (intersection-world! kb combined_kind type_a type_b)
      (let [g (generation kb (v/handle-of kb (unary-rule combined_kind [type_a type_b]) 'CxUniverse))]
        (is (:believed? g) "the unary membership rule is generated")
        (is (contains? (:because g) m) "resting on the membership in the mapped class")
        (is (not (:reads-arity? g)) "and not through an arity guard")))
    (is (believes? kb (list combined_kind 'Item) 'CxUniverse)
        "and concludes the membership")))

(tu/deftest-kb retracting-a-default-unary-premise-withdraws-the-rule-and-its-memberships
  ;; The eligibility is a :default premise.  The generated rule takes its class, so the
  ;; membership it concludes from :monotonic parts is :default, and retracting the
  ;; premise withdraws the rule and the membership.
  (tu/with-terms [combined_kind type_a type_b]
    (let [premise (v/assert kb (list 'unary combined_kind) 'CxUniverse)
          rule    (unary-rule combined_kind [type_a type_b])]
      (intersection-world! kb combined_kind type_a type_b)
      (let [g (generation kb (v/handle-of kb rule 'CxUniverse))]
        (is (:believed? g) "the unary membership rule is generated")
        (is (contains? (:because g) premise) "resting on the :default premise")
        (is (not (:reads-arity? g)) "and not through an arity guard"))
      (is (= :default (v/defeat-class kb (v/handle-of kb (list combined_kind 'Item) 'CxUniverse)))
          "the membership is capped at the premise's :default")
      (v/retract! kb premise)
      (is (not (:believed? (generation kb (v/handle-of kb rule 'CxUniverse))))
          "retracting the premise withdraws the generated rule")
      (is (not (believes? kb (list combined_kind 'Item) 'CxUniverse))
          "and the membership it concluded"))))

(tu/deftest-kb a-binary-combined-predicate-takes-the-binary-rule-and-no-unary-one
  (tu/with-terms [can able may]
    (doseq [p [can able may]] (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (v/assert kb (list 'intersection can able may) 'CxUniverse)
    (v/assert kb (list able 'Alice 'kayaking) 'CxUniverse)
    (v/assert kb (list may 'Alice 'kayaking) 'CxUniverse)
    (is (tuple? (list can 'Alice 'kayaking)) "the binary rule concludes the tuple")
    (is (not (:believed? (generation kb (v/handle-of kb (unary-rule can [able may]) 'CxUniverse))))
        "and no unary membership rule is generated")
    (testing "the unary membership generator reads the class membership, not an arity"
      (is (nil? (v/handle-of kb '(implies (and (intersection ?combined ?type1 ?type2) (arity ?combined 1))
                                          (implies (and (?type1 ?x) (?type2 ?x)) (?combined ?x)))
                             'CxUniverse)))
      (is (some? (v/handle-of kb '(implies (relationTypeByArity ?class 1)
                                           (implies (and (intersection ?combined ?type1 ?type2)
                                                         (?class ?combined))
                                                    (implies (and (?type1 ?x) (?type2 ?x))
                                                             (?combined ?x))))
                              'CxUniverse))))))

(defn- membership-rule?
  "Is `rule` the unary membership rule concluding `(combined ?x)` from the `parts`?"
  [rule combined parts]
  (let [r (unwrapped rule)]
    (boolean
     (when (and (seq? r) (= 'implies (first r)))
       (let [[_ ante conseq] r
             lits (if (and (seq? ante) (= 'and (first ante))) (rest ante) [ante])]
         (and (seq? conseq) (= combined (first conseq))
              (= (set parts) (set (map first lits)))))))))

(deftest the-load-holds-the-unary-membership-firings-and-a-first-query-adds-no-record
  ;; reflection.txt states (intersection closed_literal literal closed_expression) and the
  ;; closed_predication one, and abstract.txt a declined_rule_macro record whose argument
  ;; is a quoted closed predication.  The generated rules' firings over that record are
  ;; made by the load.  A first query of the memberships stores no sentex and no
  ;; justification.
  (tu/with-neutral-kb [kb #(doto (tu/isolated-fresh) (tu/load-core!))]
    (let [q       (list sx/quote-functor '(genl container hollow))
          record  (v/handle-of kb (list 'declined_rule_macro q) 'CxUniverse)
          kinds   '[[closed_literal [literal closed_expression]]
                    [closed_predication [predication closed_expression]]]]
      (is (some? record) "abstract.txt's declined record is loaded")
      (doseq [[combined parts] kinds
              :let [h    (v/handle-of kb (list combined q) 'CxUniverse)
                    sups (when h
                           (filterv #(membership-rule? (:rule %) combined parts)
                                    (get-in (v/why kb h) [:nodes h :support])))]]
        (is (some #(some #{record} (:because %)) sups)
            (str "the load holds the " combined " rule's firing over the declined record"))
        (is (not-any? #(:reads-arity? (generation kb (:informant %))) sups)
            (str "and the " combined " rule is generated from the class membership")))
      (let [before (tu/content-count kb)]
        (doseq [[combined] kinds]
          (v/ask? kb (list combined q) 'CxUniverse)
          (v/query kb (list combined q) 'CxUniverse {:max-depth 3}))
        (is (= before (tu/content-count kb))
            "the first query of each membership stores no sentex and no justification")))))

;; ---- the membership's strength ------------------------------------------
;; The generated membership rule is bare, so it confers :monotonic and the combined
;; membership is capped at the weakest conjunct.

(tu/deftest-kb the-combined-membership-is-capped-at-the-weakest-conjunct
  (tu/with-terms [combined_kind type_a type_b]
    (v/assert kb (list 'genl type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'unary combined_kind) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'intersection combined_kind type_a type_b) 'CxUniverse {:strength :monotonic})
    (testing "a :default conjunct makes a :default member"
      (v/assert kb (list type_a 'Item) 'CxUniverse)
      (v/assert kb (list type_b 'Item) 'CxUniverse {:strength :monotonic})
      (is (= :default (v/defeat-class kb (v/handle-of kb (list combined_kind 'Item) 'CxUniverse)))))
    (testing "and :monotonic conjuncts make a :monotonic member"
      (v/assert kb (list type_a 'Other) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list type_b 'Other) 'CxUniverse {:strength :monotonic})
      (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list combined_kind 'Other) 'CxUniverse)))))))

(tu/deftest-kb a-forced-monotonic-combined-kind-is-concluded-from-forced-monotonic-conjuncts
  ;; A firing concluding a forced-monotonic literal is void unless its rule adds no defeasibility
  ;; and every antecedent is forced-monotonic.  The bare membership rule adds none, so a
  ;; forced-monotonic combined kind is concluded from two forced-monotonic parts.
  (tu/with-terms [combined_kind type_a type_b]
    (doseq [t [combined_kind type_a type_b]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse)
      (v/assert kb (list 'unary t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'forced_monotonic_predicate t) 'CxUniverse {:strength :monotonic}))
    (v/assert kb (list 'intersection combined_kind type_a type_b) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list type_a 'Item) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list type_b 'Item) 'CxUniverse {:strength :monotonic})
    (is (believes? kb (list combined_kind 'Item) 'CxUniverse)
        "the membership is concluded")
    (is (not-any? #(and (= :forced-conclusion (:violation %))
                        (= (list combined_kind 'Item) (:sentence %)))
                  (v/violations kb))
        "and its firing is not void")))

;; ---- the forward reading, at every reader and in every arrival order ------
;;
;; These tests read belief alone, through `ask?` at each reader, so they hold whether a
;; membership firing is stored or answered by the closure.  A change to how the engine
;; stores the membership rule's firings is held to them.
;;
;; The world gives the combined kind two kinds of member.  `only_kind` reaches the two
;; parts through the combined kind alone; `both_kind` reaches them through the combined
;; kind and also around it, through `side_a` and `side_b`.  `CxExcept` excepts
;; `both_kind`'s edge to the combined kind, so a member of `both_kind` is a member of the
;; two parts there by the other route, and the forward reading makes it a member of the
;; combined kind.  `CxDenial` denies `only_kind`'s edge at `:monotonic`, so a member of
;; `only_kind` is a member of neither part there.  `probe_kind` is declared disjoint from
;; the combined kind, and `Probe` is stated in both parts at `:monotonic` and in
;; `probe_kind` at `:default`.  The intersection is asserted `:monotonic` and the membership
;; rule is bare, so the combined membership of a thing stated in both parts at
;; `:monotonic` is `:monotonic`, and the clash takes the `:default` `probe_kind`
;; membership OUT.

(defn- ix-world
  "The content steps of the world above over the terms `t`, `{step [[sentence context
  opts] …]}`.  An `[:except-of s c]` sentence is the `except` of the stored `s` in `c`,
  read when the step runs."
  [{:keys [comb part-a part-b side-a side-b only both probe only-x both-x stated-x half-x
           probe-x base cx-except cx-denial]}]
  (let [mono {:strength :monotonic}]
    {:types     [[(list 'genl part-a 'thing) base] [(list 'genl part-b 'thing) base]
                 [(list 'genl probe 'thing) base]]
     :ix        [[(list 'unary comb) base mono] [(list 'intersection comb part-a part-b) base mono]]
     :only-edge [[(list 'genl only comb) base]]
     :both-edge [[(list 'genl both comb) base]]
     :bypass    [[(list 'genl both side-a) base] [(list 'genl side-a part-a) base]
                 [(list 'genl both side-b) base] [(list 'genl side-b part-b) base]]
     :members   [[(list only only-x) base] [(list both both-x) base]
                 [(list part-a stated-x) base] [(list part-b stated-x) base]
                 [(list part-a half-x) base]]
     :except    [[[:except-of (list 'genl both comb) base] cx-except]]
     :denial    [[(list 'not (list 'genl only comb)) cx-denial mono]]
     :probe     [[(list 'disjoint comb probe) base mono]
                 [(list part-a probe-x) base mono] [(list part-b probe-x) base mono]
                 [(list probe probe-x) base]]}))

(def ^:private canonical-steps
  [:types :ix :only-edge :both-edge :bypass :members :except :denial :probe])

(defn- assert-step!
  "Assert step `step` of `world`, returning its handles."
  [kb world step]
  (mapv (fn [[s c opts]]
          (let [s (if (and (vector? s) (= :except-of (first s)))
                    (let [[_ target tc] s]
                      (list 'except (list 'sentexHandle (v/handle-of kb target tc))))
                    s)]
            (v/assert kb s c (or opts {}))))
        (get world step)))

(defn- ix-snapshot
  "Whether each reader answers each membership: `{[reader term type] bool}`."
  [kb {:keys [comb part-a part-b probe only both only-x both-x stated-x half-x probe-x base
              cx-except cx-denial]}]
  (into {}
        (concat
         (for [r [base cx-except cx-denial]
               x [only-x both-x stated-x half-x probe-x]
               t [comb part-a part-b probe]]
           [[r x t] (v/ask? kb (list t x) r)])
         (for [r [base cx-except cx-denial]
               [k sub] [[:edge-only only] [:edge-both both]]]
           [[r k] (v/ask? kb (list 'genl sub comb) r)]))))

(defn- build-ix
  "A fresh vocabulary KB holding the world's contexts and `steps` asserted in that order;
  calls `f` with the KB and each step's handles, inside the net-neutrality check."
  [t steps f]
  (let [world (ix-world t)]
    (tu/with-neutral-kb [kb #(doto (tu/isolated-fresh) (tu/load-core!))]
      (v/assert kb (list 'genlCx (:base t) 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx (:cx-except t) (:base t)) 'CxUniverse)
      (v/assert kb (list 'genlCx (:cx-denial t) (:base t)) 'CxUniverse)
      (f kb (into {} (for [s steps] [s (assert-step! kb world s)]))))))

(defn- sampled-orders
  "The canonical order and `n` shuffles of it from `seed`, each keeping `:except` after
  `:both-edge`, since the except names the edge's handle."
  [n seed]
  (let [rnd (java.util.Random. (long seed))
        ok? (fn [o] (< (.indexOf ^java.util.List o :both-edge) (.indexOf ^java.util.List o :except)))]
    (cons canonical-steps
          (->> (repeatedly #(let [l (java.util.ArrayList. ^java.util.Collection canonical-steps)]
                              (java.util.Collections/shuffle l rnd)
                              (vec l)))
               (filter ok?)
               (take n)))))

(defn- forward-reading-breaks
  "The `[reader term combined part-a part-b]` rows of `snap` where the combined
  membership is not answered exactly when both part memberships are."
  [snap {:keys [comb part-a part-b only-x both-x stated-x half-x base cx-except cx-denial]}]
  (for [r [base cx-except cx-denial]
        x [only-x both-x stated-x half-x]
        :let [c (snap [r x comb]) a (snap [r x part-a]) b (snap [r x part-b])]
        :when (not= c (and a b))]
    [r x c a b]))

(defn- ix-terms
  "The world's terms, fresh per call."
  []
  (tu/with-terms [comb_kind part_a part_b side_a side_b only_kind both_kind probe_kind
                  Only Both Stated Half Probe CxBase CxExcept CxDenial]
    {:comb comb_kind :part-a part_a :part-b part_b :side-a side_a :side-b side_b
     :only only_kind :both both_kind :probe probe_kind :only-x Only :both-x Both
     :stated-x Stated :half-x Half :probe-x Probe :base CxBase :cx-except CxExcept
     :cx-denial CxDenial}))

(defn- check-orders
  [n seed]
  (let [t (ix-terms)]
    (let [results (for [o (sampled-orders n seed)]
                    [o (build-ix t o (fn [kb _] (ix-snapshot kb t)))])
          snaps   (set (map second results))
          snap    (second (first results))]
      (is (= 1 (count snaps))
          (str "belief varied by arrival order: "
               (pr-str (map (fn [[o s]] [o (remove (fn [[k v]] (= v (snap k))) s)]) results))))
      (is (= [true true false true true false]
             (for [r [(:base t) (:cx-except t) (:cx-denial t)] k [:edge-both :edge-only]]
               (snap [r k])))
          "the except withdraws both_kind's edge and the denial only_kind's, each at its reader")
      (is (= [true false]
             [(snap [(:base t) (:probe-x t) (:comb t)]) (snap [(:base t) (:probe-x t) (:probe t)])])
          "the membership rule concludes at :monotonic from :monotonic parts, so the clash takes probe_kind OUT")
      (is (empty? (forward-reading-breaks snap t)))
      (is (true? (snap [(:cx-except t) (:both-x t) (:comb t)]))
          "the except leaves the route around the combined kind, and the forward reading")
      (is (false? (snap [(:cx-denial t) (:only-x t) (:comb t)]))
          "the denial leaves only_kind no route to either part"))))

(defn- check-retractions
  "For each step of `steps`, retracting it from the canonical build reads as the
  canonical build without it, and the forward reading holds after it while the
  intersection stands.  Retracting `:both-edge` retracts the except naming it."
  [steps]
  (let [t (ix-terms)]
    (doseq [s steps
            :let [gone (cond-> #{s} (= s :both-edge) (conj :except))
                  after (build-ix t canonical-steps
                                  (fn [kb hs]
                                    (doseq [g (sort-by #(if (= % :except) 0 1) gone)
                                            h (rseq (get hs g))]
                                      (v/retract! kb h))
                                    (ix-snapshot kb t)))
                  never (build-ix t (vec (remove gone canonical-steps))
                                  (fn [kb _] (ix-snapshot kb t)))]]
      (is (= never after)
          (str "retracting " s " differs from never asserting it: "
               (pr-str (remove (fn [[k v]] (= v (never k))) after))))
      (when-not (= s :ix)
        (is (empty? (forward-reading-breaks after t)) (str "after retracting " s))))))

(deftest the-forward-reading-holds-at-every-reader-in-sampled-orders
  (check-orders 1 7)
  (check-retractions [:both-edge]))

(deftest ^:slow the-forward-reading-holds-at-every-reader-in-every-order-and-retraction
  (check-orders 24 11)
  (check-retractions canonical-steps))
