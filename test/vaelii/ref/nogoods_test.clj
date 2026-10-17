;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ref.nogoods-test
  "Each nogood family of the belief reference on hand-built views: the plain convicting
  case, the case read through the `genl` closure, and the cases the docs exclude. No KB
  is opened; a view is a literal set of believed sentences, a class map and the closure
  of the `genl` sentences among them."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.ref.nogoods :as ng]))

;; ---- the view helper --------------------------------------------------------

(defn- genl-closure
  "A function from a term to the term and every supertype the `(genl a b)` sentences in
  `believed` reach from it."
  [believed]
  (let [out (reduce (fn [m s]
                      (if (and (seq? s) (= 'genl (first s)) (= 3 (count s)))
                        (update m (nth s 1) (fnil conj #{}) (nth s 2))
                        m))
                    {} believed)]
    (fn [t]
      (loop [seen #{t} todo [t]]
        (if (empty? todo)
          seen
          (let [nxt (remove seen (get out (peek todo)))]
            (recur (into seen nxt) (into (pop todo) nxt))))))))

(defn- view-of
  "A view at `CxTest` believing exactly `sentences`. `classes` maps a sentence to its
  class; a believed sentence it does not name is `:default`."
  ([sentences] (view-of sentences {}))
  ([sentences classes]
   (let [believed (set sentences)]
     {:context  'CxTest
      :sees     #{'CxTest}
      :believed believed
      :class    (fn [s] (when (contains? believed s) (get classes s :default)))
      :genl     (genl-closure believed)})))

(defn- member-sets [nogoods]
  (set (map :members nogoods)))

;; ---- disjoint ---------------------------------------------------------------

(deftest a-disjoint-declaration-convicts-two-memberships-of-one-term
  (is (= [{:kind :disjoint :members #{'(dog Fido) '(cat Fido)} :ground #{'(disjoint dog cat)}}]
         (ng/disjoint (view-of '[(disjoint dog cat) (dog Fido) (cat Fido) (cat Tom)])))))

(deftest a-disjoint-declaration-between-supertypes-convicts-memberships-of-their-subtypes
  (is (= [{:kind    :disjoint
           :members #{'(dog Fido) '(tree Fido)}
           :ground  #{'(disjoint animal plant) '(genl dog mammal) '(genl mammal animal)
                      '(genl tree plant)}}]
         (ng/disjoint (view-of '[(disjoint animal plant) (genl dog mammal)
                                 (genl mammal animal) (genl cat mammal) (genl tree plant)
                                 (dog Fido) (tree Fido)])))))

(deftest a-declaration-stated-both-ways-is-one-nogood-with-both-in-its-ground
  (is (= [{:kind    :disjoint
           :members #{'(dog Fido) '(cat Fido)}
           :ground  #{'(disjoint dog cat) '(disjoint cat dog)}}]
         (ng/disjoint (view-of '[(disjoint dog cat) (disjoint cat dog)
                                 (dog Fido) (cat Fido)])))))

(deftest a-declaration-between-a-type-and-its-supertype-is-its-own-nogood-and-convicts-two-memberships
  (testing "the declaration is a one-member nogood, and one membership under both types forms none"
    (is (= [{:kind :disjoint :members #{'(disjoint dog animal)} :ground #{'(genl dog animal)}}]
           (ng/disjoint (view-of '[(disjoint dog animal) (genl dog animal) (dog Fido)])))))
  (testing "a membership of each separated type forms one"
    (is (= #{#{'(dog Fido) '(animal Fido)} #{'(disjoint dog animal)}}
           (member-sets (ng/disjoint (view-of '[(disjoint dog animal) (genl dog animal)
                                                (dog Fido) (animal Fido)])))))))

;; ---- functional and functionalInArg ------------------------------------------

(deftest a-functional-mark-convicts-two-numeric-fillers-for-one-subject
  (is (= [{:kind :functional :members #{'(ageOf Bob 5) '(ageOf Bob 6)}
           :ground #{'(functional ageOf)}}]
         (ng/functional (view-of '[(functional ageOf) (ageOf Bob 5) (ageOf Bob 6)
                                   (ageOf Ann 7)])))))

(deftest a-functional-mark-convicts-a-filler-written-at-a-sub-predicate
  (is (= [{:kind :functional :members #{'(ageInYearsOf Bob 5) '(ageOf Bob 6)}
           :ground #{'(functional ageOf) '(genl ageInYearsOf ageOf)}}]
         (ng/functional (view-of '[(functional ageOf) (genl ageInYearsOf ageOf)
                                   (ageInYearsOf Bob 5) (ageOf Bob 6)])))))

(deftest two-symbol-fillers-form-a-functional-nogood
  (is (= [{:kind :functional :members #{'(motherOf Tom Ann) '(motherOf Tom Beth)}
           :ground #{'(functional motherOf)}}]
         (ng/functional (view-of '[(functional motherOf) (motherOf Tom Ann)
                                   (motherOf Tom Beth)])))))

(deftest a-functional-in-arg-mark-reads-every-other-position-as-the-determinant
  (is (= [{:kind :functional-in-arg
           :members #{'(priceIn Shop Apple 3) '(priceIn Shop Apple 4)}
           :ground #{'(functionalInArg priceIn 3)}}]
         (ng/functional (view-of '[(functionalInArg priceIn 3) (priceIn Shop Apple 3)
                                   (priceIn Shop Apple 4) (priceIn Shop Pear 4)
                                   (priceIn Mart Apple 5)])))))

(deftest a-pair-convicted-under-both-spellings-is-one-functional-nogood
  (is (= [{:kind :functional :members #{'(ageOf Bob 5) '(ageOf Bob 6)}
           :ground #{'(functional ageOf) '(functionalInArg ageOf 2)}}]
         (ng/functional (view-of '[(functional ageOf) (functionalInArg ageOf 2)
                                   (ageOf Bob 5) (ageOf Bob 6)])))))

;; ---- asymmetric --------------------------------------------------------------

(deftest an-asymmetric-mark-convicts-a-tuple-and-its-converse
  (is (= [{:kind :asymmetric :members #{'(typeLargerThan Rex Tom) '(typeLargerThan Tom Rex)}
           :ground #{'(asymmetric typeLargerThan)}}]
         (ng/asymmetric (view-of '[(asymmetric typeLargerThan) (typeLargerThan Rex Tom)
                                   (typeLargerThan Tom Rex) (typeLargerThan Rex Rex)])))))

(deftest an-asymmetric-mark-convicts-a-converse-written-at-a-sub-predicate
  (is (= [{:kind :asymmetric :members #{'(fatherOf Tom Bob) '(parentOf Bob Tom)}
           :ground #{'(asymmetric parentOf) '(genl fatherOf parentOf)}}]
         (ng/asymmetric (view-of '[(asymmetric parentOf) (genl fatherOf parentOf)
                                   (fatherOf Tom Bob) (parentOf Bob Tom)])))))

(deftest an-asymmetric-self-tuple-convicts-nothing
  (is (= [] (ng/asymmetric (view-of '[(asymmetric typeLargerThan) (typeLargerThan Rex Rex)])))))

;; ---- anti_transitive ---------------------------------------------------------

(deftest an-anti-transitive-chain-and-its-direct-step-are-one-three-member-nogood
  (is (= [{:kind    :anti-transitive
           :members #{'(parentOf Ann Bob) '(parentOf Bob Cy) '(parentOf Ann Cy)}
           :ground  #{'(anti_transitive parentOf)}}]
         (ng/anti-transitive (view-of '[(anti_transitive parentOf) (parentOf Ann Bob)
                                        (parentOf Bob Cy) (parentOf Ann Cy)])))))

(deftest an-anti-transitive-chain-spelled-at-two-predicates-is-one-chain
  (is (= [{:kind    :anti-transitive
           :members #{'(fatherOf Ann Bob) '(parentOf Bob Cy) '(fatherOf Ann Cy)}
           :ground  #{'(anti_transitive parentOf) '(genl fatherOf parentOf)}}]
         (ng/anti-transitive (view-of '[(anti_transitive parentOf) (genl fatherOf parentOf)
                                        (fatherOf Ann Bob) (parentOf Bob Cy)
                                        (fatherOf Ann Cy)])))))

(deftest an-anti-transitive-triple-with-coinciding-roles-keeps-its-distinct-members
  (testing "a step beside a self tuple at its end is a two-member nogood"
    (is (= #{#{'(parentOf Ann Bob) '(parentOf Bob Bob)}}
           (member-sets (ng/anti-transitive
                         (view-of '[(anti_transitive parentOf) (parentOf Ann Bob)
                                    (parentOf Bob Bob)]))))))
  (testing "a lone self tuple and a chain with no direct step convict nothing"
    (is (= [[] []]
           [(ng/anti-transitive (view-of '[(anti_transitive parentOf) (parentOf Bob Bob)]))
            (ng/anti-transitive (view-of '[(anti_transitive parentOf) (parentOf Ann Bob)
                                           (parentOf Bob Cy)]))]))))

;; ---- covering ---------------------------------------------------------------

(deftest a-cover-naming-a-part-disjoint-from-its-whole-is-a-nogood-with-the-disjoint
  (is (= [{:kind :covering :members #{'(covering w p1 p2) '(disjoint p1 w)} :ground #{}}]
         (ng/covering (view-of '[(covering w p1 p2) (disjoint p1 w)])))))

(deftest a-cover-with-every-part-denied-convicts-the-membership-and-the-denials
  (is (= [{:kind    :covering
           :members #{'(w X) '(not (p1 X)) '(not (p2 X))}
           :ground  #{'(covering w p1 p2)}}]
         (ng/covering (view-of '[(covering w p1 p2) (w X) (not (p1 X)) (not (p2 X))])))))

(deftest a-denial-of-a-supertype-of-a-part-denies-the-part
  ;; the review's scenario d
  (is (= [{:kind    :covering
           :members #{'(w X) '(not (q X)) '(not (p2 X))}
           :ground  #{'(covering w p1 p2) '(genl p1 q)}}]
         (ng/covering (view-of '[(genl p1 w) (genl p2 w) (genl p1 q) (covering w p1 p2)
                                 (w X) (not (q X)) (not (p2 X))])))))

(deftest a-membership-of-a-subtype-of-the-whole-is-refuted-by-the-cover
  (is (= [{:kind    :covering
           :members #{'(s X) '(not (p1 X)) '(not (p2 X))}
           :ground  #{'(covering w p1 p2) '(genl s w)}}]
         (ng/covering (view-of '[(covering w p1 p2) (genl s w) (s X)
                                 (not (p1 X)) (not (p2 X))])))))

(deftest a-cover-with-a-part-left-undenied-convicts-nothing
  (is (= [] (ng/covering (view-of '[(covering w p1 p2) (w X) (not (p1 X)) (p2 X)])))))

(deftest two-denials-of-one-part-give-one-nogood-each
  (is (= #{#{'(w X) '(not (p1 X)) '(not (p2 X))}
           #{'(w X) '(not (q X)) '(not (p2 X))}}
         (member-sets (ng/covering (view-of '[(covering w p1 p2) (genl p1 q) (w X)
                                              (not (p1 X)) (not (q X)) (not (p2 X))]))))))

(deftest a-membership-in-a-type-separated-from-a-part-denies-the-part
  ;; https://github.com/vaelii/vaelii/issues/183: the separation's denial is a denier of
  ;; the part, and the membership doing the denying is the member
  (is (= [{:kind    :covering
           :members #{'(w X) '(s1 X) '(s2 X)}
           :ground  #{'(covering w p1 p2) '(disjoint s1 p1) '(disjoint s2 p2)}}]
         (ng/covering (view-of '[(covering w p1 p2) (disjoint s1 p1) (disjoint s2 p2)
                                 (w X) (s1 X) (s2 X)])))))

(deftest a-separation-denies-a-part-only-over-monotonic-edges
  ;; a `:default` edge from the part up to the separated type does not contrapose
  (let [world '[(covering w p1 p2) (genl p1 q) (disjoint s1 q) (disjoint s2 p2)
                (w X) (s1 X) (s2 X)]]
    (is (= [] (ng/covering (view-of world))))
    (is (= [{:kind    :covering
             :members #{'(w X) '(s1 X) '(s2 X)}
             :ground  #{'(covering w p1 p2) '(disjoint s1 q) '(disjoint s2 p2) '(genl p1 q)}}]
           (ng/covering (view-of world '{(genl p1 q) :monotonic}))))))

;; ---- inherited (transitiveInArgInverse) --------------------------------------------

(def ^:private scenario-e
  "The review's scenario e, with `carriesLoad` for `P`."
  '[(transitiveInArgInverse carriesLoad 1 genl) (genl hauler animal) (genl vehicle animal)
    (genl cart hauler) (genl cart vehicle) (carriesLoad vehicle Bone1)
    (carriesLoad hauler Bone1) (not (carriesLoad cart Bone1))])

(deftest a-denial-below-two-known-true-claims-clashes-with-each-inherited-claim
  ;; one nogood per general claim: the denial, the claim, the declaration and the one
  ;; edge the reach crosses; the edges up to `animal` carry no claim and stay out
  (is (= [{:kind    :inherited
           :members #{'(not (carriesLoad cart Bone1)) '(carriesLoad hauler Bone1)
                      '(transitiveInArgInverse carriesLoad 1 genl) '(genl cart hauler)}
           :ground  #{}}
          {:kind    :inherited
           :members #{'(not (carriesLoad cart Bone1)) '(carriesLoad vehicle Bone1)
                      '(transitiveInArgInverse carriesLoad 1 genl) '(genl cart vehicle)}
           :ground  #{}}]
         (ng/inherited (view-of scenario-e
                                '{(carriesLoad vehicle Bone1) :monotonic
                                  (carriesLoad hauler Bone1)  :monotonic})))))

(deftest a-default-general-claim-is-undercut-and-forms-no-nogood
  (is (= #{#{'(not (carriesLoad cart Bone1)) '(carriesLoad vehicle Bone1)
             '(transitiveInArgInverse carriesLoad 1 genl) '(genl cart vehicle)}}
         (member-sets (ng/inherited (view-of scenario-e
                                             '{(carriesLoad vehicle Bone1) :monotonic})))))
  (is (= [] (ng/inherited (view-of scenario-e)))))

(deftest an-inherited-clash-names-every-edge-of-a-two-hop-route
  (is (= #{#{'(not (carriesLoad cart Bone1)) '(carriesLoad animal Bone1)
             '(transitiveInArgInverse carriesLoad 1 genl) '(genl cart hauler) '(genl hauler animal)}}
         (member-sets (ng/inherited (view-of '[(transitiveInArgInverse carriesLoad 1 genl)
                                               (genl cart hauler) (genl hauler animal)
                                               (carriesLoad animal Bone1)
                                               (not (carriesLoad cart Bone1))]
                                             '{(carriesLoad animal Bone1) :monotonic}))))))

(deftest two-routes-to-one-general-claim-form-one-nogood-each
  (is (= #{#{'(not (carriesLoad cart Bone1)) '(carriesLoad animal Bone1)
             '(transitiveInArgInverse carriesLoad 1 genl) '(genl cart hauler) '(genl hauler animal)}
           #{'(not (carriesLoad cart Bone1)) '(carriesLoad animal Bone1)
             '(transitiveInArgInverse carriesLoad 1 genl) '(genl cart animal)}}
         (member-sets (ng/inherited (view-of '[(transitiveInArgInverse carriesLoad 1 genl)
                                               (genl cart hauler) (genl hauler animal)
                                               (genl cart animal) (carriesLoad animal Bone1)
                                               (not (carriesLoad cart Bone1))]
                                             '{(carriesLoad animal Bone1) :monotonic}))))))

(deftest an-inherited-clash-needs-the-declaration-a-strict-supertype-and-matching-positions
  (let [known '{(carriesLoad hauler Bone1) :monotonic (carriesLoad hauler Bone2) :monotonic
                (carriesLoad cart Bone1) :monotonic}]
    (is (= [[] [] []]
           [(ng/inherited (view-of '[(genl cart hauler) (carriesLoad hauler Bone1)
                                     (not (carriesLoad cart Bone1))]
                                   known))
            (ng/inherited (view-of '[(transitiveInArgInverse carriesLoad 1 genl)
                                     (carriesLoad cart Bone1) (not (carriesLoad cart Bone1))]
                                   known))
            (ng/inherited (view-of '[(transitiveInArgInverse carriesLoad 1 genl) (genl cart hauler)
                                     (carriesLoad hauler Bone2) (not (carriesLoad cart Bone1))]
                                   known))]))))

(deftest a-membership-of-a-separated-type-clashes-with-the-inherited-membership
  (is (= [{:kind    :inherited
           :members '#{(plain lower) (down upper) (transitiveInArgInverse down 1 genl)
                       (genl lower upper)}
           :ground  '#{(disjoint top plain) (genl down top)}}]
         (ng/inherited (view-of '[(transitiveInArgInverse down 1 genl) (genl lower upper)
                                  (genl down top) (disjoint top plain)
                                  (down upper) (plain lower)]
                                '{(down upper) :monotonic})))))

(deftest a-membership-of-a-type-no-separation-names-or-beside-a-default-claim-is-no-clash
  (let [view '[(transitiveInArgInverse down 1 genl) (genl lower upper) (down upper)
               (plain lower)]]
    (is (= [[] []]
           [(ng/inherited (view-of view '{(down upper) :monotonic}))
            (ng/inherited (view-of (conj view '(disjoint down plain))))]))))

;; ---- supertype --------------------------------------------------------------

(deftest a-membership-beside-a-denial-of-a-supertype-of-its-type-is-a-nogood
  (is (= [{:kind    :supertype
           :members #{'(dog Rex) '(not (animal Rex))}
           :ground  #{'(genl dog mammal) '(genl mammal animal)}}]
         (ng/supertype (view-of '[(genl dog mammal) (genl mammal animal)
                                  (dog Rex) (not (animal Rex))])))))

(deftest a-denial-of-the-type-itself-or-of-a-type-not-above-it-is-no-supertype-nogood
  (is (= [] (ng/supertype (view-of '[(dog Rex) (not (dog Rex))]))))
  (is (= [] (ng/supertype (view-of '[(genl dog animal) (animal Rex) (not (dog Rex))])))))

;; ---- irreflexive -------------------------------------------------------------

(deftest an-irreflexive-mark-convicts-a-default-self-tuple-as-a-one-member-nogood
  (let [v (view-of '[(irreflexive typeLargerThan) (typeLargerThan Rex Rex) (typeLargerThan Tom Rex)])]
    (is (= [{:kind :irreflexive :members #{'(typeLargerThan Rex Rex)}
             :ground #{'(irreflexive typeLargerThan)}}]
           (ng/irreflexive v)))
    (testing "the one-member nogood reaches the decision through families"
      (is (some #{#{'(typeLargerThan Rex Rex)}} (map :members (mapcat #(% v) ng/families)))))))

(deftest an-irreflexive-mark-reaches-a-sub-predicate-over-a-believed-edge-of-either-class
  (let [content '[(irreflexive typeLargerThan) (genl muchLargerThan typeLargerThan)
                  (muchLargerThan Rex Rex)]
        edge    '(genl muchLargerThan typeLargerThan)
        nogood  {:kind :irreflexive :members #{'(muchLargerThan Rex Rex)}
                 :ground #{'(irreflexive typeLargerThan) edge}}]
    (is (= [[nogood] [nogood] []]
           [(ng/irreflexive (view-of content {edge :default}))
            (ng/irreflexive (view-of content {edge :monotonic}))
            (ng/irreflexive (view-of (remove #{edge} content)))]))))

(deftest an-irreflexive-mark-without-a-self-tuple-convicts-nothing
  (is (= [] (ng/irreflexive (view-of '[(irreflexive typeLargerThan) (typeLargerThan Rex Tom)
                                       (typeLargerThan Tom Rex) (smallerThan Rex Rex)])))))

;; ---- anti_symmetric ----------------------------------------------------------

(deftest an-anti-symmetric-mark-convicts-a-converse-pair
  (is (= [{:kind :anti-symmetric :members #{'(atOrAbove 1 2) '(atOrAbove 2 1)}
           :ground #{'(anti_symmetric atOrAbove)}}]
         (ng/anti-symmetric (view-of '[(anti_symmetric atOrAbove) (atOrAbove 1 2)
                                       (atOrAbove 2 1) (atOrAbove 1 3)])))))

(deftest an-anti-symmetric-self-tuple-is-not-a-converse-pair
  (is (= [] (ng/anti-symmetric (view-of '[(anti_symmetric atOrAbove) (atOrAbove 1 1)])))))

(deftest an-anti-symmetric-symbol-pair-is-returned-as-a-nogood
  (is (= [{:kind :anti-symmetric :members #{'(ancestorOf Ann Bob) '(parentOf Bob Ann)}
           :ground #{'(anti_symmetric ancestorOf) '(genl parentOf ancestorOf)}}]
         (ng/anti-symmetric (view-of '[(anti_symmetric ancestorOf) (genl parentOf ancestorOf)
                                       (ancestorOf Ann Bob) (parentOf Bob Ann)])))))

;; ---- order independence -----------------------------------------------------

(deftest every-family-answers-the-same-for-the-same-content-in-any-order
  (let [content (concat scenario-e
                        '[(disjoint animal plant) (tree Bone1) (animal Bone1)
                          (functional ageOf) (ageOf Bob 5) (ageOf Bob 6)
                          (asymmetric typeLargerThan) (typeLargerThan Rex Tom) (typeLargerThan Tom Rex)
                          (irreflexive fondOf) (fondOf Rex Rex)
                          (anti_symmetric atOrAbove) (atOrAbove Ann Bob) (atOrAbove Bob Ann)
                          (anti_transitive parentOf) (parentOf Ann Bob) (parentOf Bob Cy)
                          (parentOf Ann Cy) (genl tree plant)
                          (covering w p1 p2) (w X) (not (p1 X)) (not (p2 X))
                          (genl dog mammal) (dog Rex) (not (mammal Rex))])
        classes '{(carriesLoad vehicle Bone1) :monotonic (carriesLoad hauler Bone1) :monotonic}
        answer  (fn [sentences]
                  (let [v (view-of sentences classes)]
                    (mapv #(% v) ng/families)))
        answers (mapv answer [content (reverse content)
                              (concat (drop 7 content) (take 7 content))
                              (sort-by pr-str content)])]
    (testing "the content convicts under every family"
      (is (every? seq (first answers))))
    (is (apply = answers))))
