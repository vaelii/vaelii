;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.closure-join-test
  "Forward chaining over a `genl` or `genlCx` antecedent reads the cached closure.

  A query answers `(genl t t)` and a pair two edges apart from the closure
  (`TransitivityProver`).  A forward rule with the same literal in its antecedent answers
  it the same way whenever the join has bound an end: the reflexive pair and the pair no
  edge states both fire, the firing names the edges of one path, and an arriving or
  departing edge re-joins the rule.  With both ends open the stored edges answer alone."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.reads :as reads]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)

(defn- pair-rule
  "*A pair whose first member is below its second qualifies* — both ends of the `genl`
  literal bound by the first antecedent."
  [pairOf qualifies]
  (list 'set/forwardRule
        (list 'implies (list 'and (list pairOf '?a '?b) (list 'genl '?a '?b))
              (list qualifies '?a '?b))))

(defn- holds? [kb s ctx] (boolean (v/ask? kb s ctx)))

(tu/deftest-kb a-join-that-binds-both-ends-reads-the-reflexive-pair
  (tu/with-terms [pairOf qualifies pug]
    (v/assert kb (pair-rule pairOf qualifies) U)
    (v/assert kb (list pairOf pug pug) U)
    (is (holds? kb (list 'genl pug pug) U) "the query answers the reflexive pair")
    (is (holds? kb (list qualifies pug pug) U) "and the forward join agrees")
    (testing "the reflexive pair rests on no edge"
      (let [h     (v/handle-of kb (list qualifies pug pug) U)
            named (set (map :sentence (vals (:nodes (v/why kb h)))))]
        (is (= #{(list qualifies pug pug) (list pairOf pug pug)} named))))))

(tu/deftest-kb a-join-that-binds-both-ends-reads-a-pair-two-edges-apart
  (tu/with-terms [pairOf qualifies pug dog mammal]
    (v/assert kb (pair-rule pairOf qualifies) U)
    (v/assert kb (list 'genl pug dog) U)
    (let [far (v/assert kb (list 'genl dog mammal) U)]
      (v/assert kb (list pairOf pug mammal) U)
      (is (holds? kb (list qualifies pug mammal) U))
      (testing "the firing names the edges of the path"
        (let [h     (v/handle-of kb (list qualifies pug mammal) U)
              named (set (keys (:nodes (v/why kb h))))]
          (is (contains? named far))))
      (testing "and a path edge going takes the conclusion"
        (v/retract! kb far)
        (is (nil? (v/handle-of kb (list qualifies pug mammal) U)))))))

(tu/deftest-kb a-join-that-binds-one-end-reads-that-ends-closure
  (tu/with-terms [picked qualifies pug dog mammal]
    (v/assert kb (list 'genl pug dog) U)
    (v/assert kb (list 'genl dog mammal) U)
    (testing "the lower end bound: every supertype, the term itself included"
      (v/assert kb (list 'set/forwardRule
                         (list 'implies (list 'and (list picked '?a) (list 'genl '?a '?b))
                               (list qualifies '?a '?b)))
                U)
      (v/assert kb (list picked pug) U)
      (is (= #{pug dog mammal}
             (set (map '?y (v/query kb (list qualifies pug '?y) U))))
          "the same set the query answers")
      (is (= (set (map '?y (v/query kb (list 'genl pug '?y) U)))
             (set (map '?y (v/query kb (list qualifies pug '?y) U))))))))

(tu/deftest-kb a-join-that-binds-the-upper-end-reads-its-subtypes
  (tu/with-terms [picked qualifies pug dog mammal]
    (v/assert kb (list 'genl pug dog) U)
    (v/assert kb (list 'genl dog mammal) U)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list picked '?b) (list 'genl '?a '?b))
                             (list qualifies '?a '?b)))
              U)
    (v/assert kb (list picked mammal) U)
    (is (= #{pug dog mammal} (set (map '?x (v/query kb (list qualifies '?x mammal) U)))))))

(tu/deftest-kb a-join-with-both-ends-open-reads-the-stored-edges
  ;; The closure over every pair is quadratic in a chain's length, so an antecedent with
  ;; neither end bound is answered by the stored edges, as a transitive predicate's is.
  ;; Read off storage rather than `query`: `set/forwardRule` runs backward too, and a
  ;; backward proof reads the closure the forward join declines.
  (tu/with-terms [qualifies pug dog mammal]
    (v/assert kb (list 'genl pug dog) U)
    (v/assert kb (list 'genl dog mammal) U)
    (v/assert kb (list 'set/forwardRule (list 'implies (list 'genl '?a '?b) (list qualifies '?a '?b)))
              U)
    (let [stored? (fn [x y] (some? (v/handle-of kb (list qualifies x y) U)))]
      (is (stored? pug dog))
      (is (stored? dog mammal))
      (is (not (stored? pug mammal)) "no edge states the far pair")
      (is (not (stored? pug pug)) "no edge states the reflexive pair"))))

(tu/deftest-kb the-closure-join-reads-the-same-whichever-ingredient-arrived-last
  (let [orders {"rule, pair, near edge, far edge" [:rule :pair :near :far]
                "rule, pair, far edge, near edge" [:rule :pair :far :near]
                "edges, pair, rule"               [:near :far :pair :rule]
                "edges, rule, pair"               [:far :near :rule :pair]}]
    (doseq [[label order] orders]
      (testing label
        (tu/with-terms [pairOf qualifies pug dog mammal]
          (let [step {:rule #(v/assert kb (pair-rule pairOf qualifies) U)
                      :pair #(v/assert kb (list pairOf pug mammal) U)
                      :near #(v/assert kb (list 'genl pug dog) U)
                      :far  #(v/assert kb (list 'genl dog mammal) U)}]
            (doseq [k order] ((step k)))
            (is (holds? kb (list qualifies pug mammal) U))))))))

(tu/deftest-kb a-second-path-re-derives-what-a-departed-edge-licensed
  (tu/with-terms [pairOf qualifies pug dog pet mammal]
    (v/assert kb (pair-rule pairOf qualifies) U)
    (v/assert kb (list pairOf pug mammal) U)
    (let [edges (mapv #(v/assert kb % U)
                      [(list 'genl pug dog) (list 'genl dog mammal)
                       (list 'genl pug pet) (list 'genl pet mammal)])]
      (is (holds? kb (list qualifies pug mammal) U))
      (v/retract! kb (edges 1))
      (is (holds? kb (list qualifies pug mammal) U) "the path through pet still licenses it")
      (v/retract! kb (edges 3))
      (is (not (holds? kb (list qualifies pug mammal) U)) "and with both paths gone, nothing does"))))

(tu/deftest-kb the-conclusion-lands-where-the-path-is-visible
  (tu/with-terms [pairOf qualifies pug dog mammal CxStory]
    (v/assert kb (list 'genlCx CxStory U) U)
    (v/assert kb (pair-rule pairOf qualifies) U)
    (v/assert kb (list pairOf pug mammal) U)
    (v/assert kb (list 'genl pug dog) U)
    (v/assert kb (list 'genl dog mammal) CxStory)
    (is (= #{CxStory} (set (v/contexts-of kb (list qualifies pug mammal)))))
    (is (not (holds? kb (list qualifies pug mammal) U))
        "CxUniverse sees no path, and does not answer the genl query either")
    (is (not (holds? kb (list 'genl pug mammal) U)))))

(tu/deftest-kb a-genlCx-join-reads-the-reflexive-pair-and-the-far-pair
  (tu/with-terms [pairOf qualifies CxTop CxMid CxLow]
    (v/assert kb (list 'genlCx CxMid CxTop) U)
    (let [low (v/assert kb (list 'genlCx CxLow CxMid) U)]
      (v/assert kb (list 'set/forwardRule
                         (list 'implies (list 'and (list pairOf '?a '?b) (list 'genlCx '?a '?b))
                               (list qualifies '?a '?b)))
                U)
      (v/assert kb (list pairOf CxLow CxLow) U)
      (v/assert kb (list pairOf CxLow CxTop) U)
      (is (holds? kb (list qualifies CxLow CxLow) U) "reflexive")
      (is (holds? kb (list qualifies CxLow CxTop) U) "two edges apart")
      (testing "the far pair names the edges of the path"
        (let [h (v/handle-of kb (list qualifies CxLow CxTop) U)]
          (is (contains? (set (keys (:nodes (v/why kb h)))) low)))))))

;; ---- the planner runs the closure literal after a literal binding an end ----
;; Each reading builds its own KB on the isolated space, so a reading's sentences
;; compare across arrival orders by content.

(deftest a-closure-literal-the-cost-model-ranks-first-waits-for-its-end
  ;; Eight `pairOf` rows against two edges: ranked on stored rows alone, the closure
  ;; literal would run first with both ends open and read the two edges only.
  (doseq [rel     '[genl genlCx]
          written [:pair-first :closure-first]
          order   (oi/permutations [:rule :edges :pairs])]
    (testing (str rel ", " written ", " order)
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [pairOf qualifies pug dog mammal CxLow CxMid]
          (let [[lo mid hi] (if (= 'genl rel) [pug dog mammal] [CxLow CxMid U])
                antes       [(list pairOf '?a '?b) (list rel '?a '?b)]
                step {:rule  #(v/assert kb (list 'set/forwardRule
                                                 (list 'implies
                                                       (cons 'and (if (= :pair-first written)
                                                                    antes
                                                                    (reverse antes)))
                                                       (list qualifies '?a '?b)))
                                        U)
                      :edges #(doseq [[x y] [[lo mid] [mid hi]]] (v/assert kb (list rel x y) U))
                      :pairs #(doseq [[x y] (concat [[lo lo] [lo hi]]
                                                    (repeatedly 6 (fn [] [(tu/tmp-ind "F")
                                                                          (tu/tmp-ind "G")])))]
                                (v/assert kb (list pairOf x y) U))}]
            (doseq [k order] ((step k)))
            (is (holds? kb (list qualifies lo lo) U) "reflexive")
            (is (holds? kb (list qualifies lo hi) U) "two edges apart")))))))

(defn- reasons
  "The justifications of `goal` in CxUniverse as `[antecedents subsumptions]`, by content."
  [kb goal]
  (let [content (fn [h] (let [sx (v/sentex kb h)] [(v/sentence-of sx) (:context sx)]))]
    (frequencies (for [j (v/supporting-justifications kb (v/handle-of kb goal U))]
                   [(into #{} (map content) (:antecedents j)) (:subsumptions j)]))))

(deftest a-closure-literal-the-recursive-literal-binds-stores-one-justification-set-in-every-order
  ;; The recursive literal runs after every other generator, and only it binds an end of
  ;; the `genl` literal.
  (tu/with-terms [pug dog mammal reaches Z]
    (doseq [written [:closure-first :recursive-first]]
      (testing (name written)
        (let [antes    [(list 'genl '?a '?b) (list reaches '?b '?c)]
              rule     (list 'set/forwardRule
                             (list 'implies (cons 'and (if (= :closure-first written)
                                                         antes
                                                         (reverse antes)))
                                   (list reaches '?a '?c)))
              readings (for [order (oi/permutations [:rule :near :far :fact])]
                         (tu/with-neutral-kb [kb tu/isolated-fresh]
                           (doseq [s (map {:rule rule
                                           :near (list 'genl pug dog)
                                           :far  (list 'genl dog mammal)
                                           :fact (list reaches mammal Z)}
                                          order)]
                             (v/assert kb s U))
                           [(reasons kb (list reaches pug Z)) (reasons kb (list reaches dog Z))]))]
          (is (= 1 (count (distinct readings))))
          (is (contains? (ffirst readings)
                         [#{[(list reaches mammal Z) U] [(list 'genl pug dog) U]
                            [(list 'genl dog mammal) U]}
                          #{[pug mammal]}])
              "the pair two edges apart joins the fact directly"))))))

;; ---- a disjoint antecedent reads the separations ---------------------------

(defn- separated-rule
  "*A pair of separated types qualifies* — both ends of the `disjoint` literal bound by
  the first antecedent."
  [pairOf qualifies]
  (list 'set/forwardRule
        (list 'implies (list 'and (list pairOf '?a '?b) (list 'disjoint '?a '?b))
              (list qualifies '?a '?b))))

(tu/deftest-kb a-disjoint-antecedent-matches-every-separation-a-query-answers
  (doseq [[label separate]
          {"a partition"                    (fn [w a b _] [(list 'partition w a b)])
           "a separating declaration"       (fn [w a b _] [(list 'separating w a b)])
           "a disjoint_metatype"            (fn [_ a b m] [(list 'disjoint_metatype m)
                                                           (list m a) (list m b)])
           "a sibling_disjoint parent"      (fn [w a b _] [(list 'sibling_disjoint w)
                                                           (list 'genl a w) (list 'genl b w)])
           "a disjoint over two supertypes" (fn [w a b m] [(list 'genl a w) (list 'genl b m)
                                                           (list 'disjoint w m)])}]
    (testing label
      (tu/with-terms [pairOf qualifies whole qa qb kind]
        (doseq [s (separate whole qa qb kind)] (v/assert kb s U))
        (v/assert kb (separated-rule pairOf qualifies) U)
        (v/assert kb (list pairOf qa qb) U)
        (is (holds? kb (list 'disjoint qa qb) U) "the query answers the pair")
        (is (holds? kb (list qualifies qa qb) U) "and the forward join agrees")))))

(tu/deftest-kb a-type-below-two-parts-of-a-partition-fires-the-issue-rule
  (tu/with-terms [whole qa qb qc emptied]
    (v/assert kb (list 'partition whole qa qb) U {:strength :monotonic})
    (v/assert kb (list 'genl qc qa) U)
    (v/assert kb (list 'genl qc qb) U)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list 'genl '?c '?a) (list 'genl '?c '?b)
                                            (list 'disjoint '?a '?b))
                             (list emptied '?c)))
              U)
    (is (holds? kb (list emptied qc) U))))

(tu/deftest-kb a-join-that-binds-one-end-reads-every-type-separated-from-it
  (tu/with-terms [picked qualifies whole qa qb pug]
    (v/assert kb (list 'partition whole qa qb) U)
    (v/assert kb (list 'genl pug qb) U)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list picked '?a) (list 'disjoint '?a '?b))
                             (list qualifies '?a '?b)))
              U)
    (v/assert kb (list picked qa) U)
    (is (= (set (map '?y (v/query kb (list 'disjoint qa '?y) U)))
           (set (map '?y (v/query kb (list qualifies qa '?y) U)))
           #{qb pug}))))

(tu/deftest-kb a-separation-firing-rests-on-the-declaration-and-the-edges-it-climbed
  (tu/with-terms [pairOf qualifies whole qa qb pug]
    (let [decl   (v/assert kb (list 'partition whole qa qb) U)
          edge   (v/assert kb (list 'genl pug qa) U)]
      (v/assert kb (separated-rule pairOf qualifies) U)
      (v/assert kb (list pairOf pug qb) U)
      (is (holds? kb (list qualifies pug qb) U))
      (let [named (set (keys (:nodes (v/why kb (v/handle-of kb (list qualifies pug qb) U)))))]
        (is (contains? named decl))
        (is (contains? named edge)))
      (testing "the edge going takes the conclusion"
        (v/retract! kb edge)
        (is (nil? (v/handle-of kb (list qualifies pug qb) U))))
      (testing "and so does the declaration going"
        (v/assert kb (list pairOf qa qb) U)
        (is (holds? kb (list qualifies qa qb) U))
        (v/retract! kb decl)
        (is (not (holds? kb (list qualifies qa qb) U)))))))

(tu/deftest-kb an-exception-withdraws-a-separation-firing-and-its-retraction-restores-it
  (tu/with-terms [pairOf qualifies whole qa qb]
    (v/assert kb (list 'partition whole qa qb) U)
    (v/assert kb (separated-rule pairOf qualifies) U)
    (v/assert kb (list pairOf qa qb) U)
    (is (holds? kb (list qualifies qa qb) U))
    (let [exc (v/assert kb (list 'siblingDisjointException qa qb) U)]
      (is (not (holds? kb (list 'disjoint qa qb) U)))
      (is (not (holds? kb (list qualifies qa qb) U)) "the exempted pair matches nothing")
      (v/retract! kb exc)
      (is (holds? kb (list qualifies qa qb) U) "and the separation is back"))))

(def ^:private marks
  "Two marks that spare a pair one of whose types is a `genl` of the other, each as a fn
  of the parent or metatype and the two types."
  {"a sibling_disjoint parent" (fn [m a b] [(list 'sibling_disjoint m)
                                            (list 'genl a m) (list 'genl b m)])
   "a disjoint_metatype"       (fn [m a b] [(list 'disjoint_metatype m)
                                            (list m a) (list m b)])})

(tu/deftest-kb an-edge-between-two-marked-types-leaving-separates-them-in-every-order
  ;; With the edge never stated, the mark separates the pair and the rule fires.  An edge
  ;; stated and then retracted leaves the same knowledge, so the rule fires there too,
  ;; whichever ingredient arrived first.  A defeated edge still relates the two types in
  ;; the global closure the genl-relatedness guard reads, so there the query answers no
  ;; separation, and the rule answers what the query answers.
  (doseq [[label mark] marks
          order [[:mark :rule :pair :edge] [:edge :mark :pair :rule] [:rule :edge :pair :mark]]
          leave [:never :retract :defeat]]
    (testing (str label ", " order ", " leave)
      (tu/with-terms [pairOf qualifies kind qa qb]
        (let [edge (atom nil)
              step {:mark #(doseq [s (mark kind qa qb)] (v/assert kb s U))
                    :rule #(v/assert kb (separated-rule pairOf qualifies) U)
                    :pair #(v/assert kb (list pairOf qa qb) U)
                    :edge #(when-not (= :never leave)
                             (reset! edge (v/assert kb (list 'genl qa qb) U)))}]
          (doseq [k order] ((step k)))
          (case leave
            :never   nil
            :retract (v/retract! kb @edge)
            :defeat  (v/assert kb (list 'not (list 'genl qa qb)) U {:strength :monotonic}))
          (when-not (= :defeat leave)
            (is (holds? kb (list 'disjoint qa qb) U)))
          (is (= (holds? kb (list 'disjoint qa qb) U) (holds? kb (list qualifies qa qb) U))
              "the forward join answers what the query answers"))))))

(tu/deftest-kb an-edge-arriving-between-two-marked-types-withdraws-the-firing
  (doseq [[label mark] marks]
    (testing label
      (tu/with-terms [pairOf qualifies kind qa qb]
        (doseq [s (mark kind qa qb)] (v/assert kb s U))
        (v/assert kb (separated-rule pairOf qualifies) U)
        (v/assert kb (list pairOf qa qb) U)
        (is (holds? kb (list qualifies qa qb) U))
        (v/assert kb (list 'genl qa qb) U)
        (is (not (holds? kb (list 'disjoint qa qb) U)))
        (is (not (holds? kb (list qualifies qa qb) U)))))))

(tu/deftest-kb the-separation-join-reads-the-same-whichever-ingredient-arrived-last
  (let [orders {"rule, pair, edge, cover" [:rule :pair :edge :cover]
                "cover, rule, pair, edge" [:cover :rule :pair :edge]
                "cover, edge, pair, rule" [:cover :edge :pair :rule]
                "rule, cover, edge, pair" [:rule :cover :edge :pair]}]
    (doseq [[label order] orders]
      (testing label
        (tu/with-terms [pairOf qualifies whole qa qb pug]
          (let [step {:rule   #(v/assert kb (separated-rule pairOf qualifies) U)
                      :pair   #(v/assert kb (list pairOf pug qb) U)
                      :edge   #(v/assert kb (list 'genl pug qa) U)
                      :cover #(v/assert kb (list 'partition whole qa qb) U)}]
            (doseq [k order] ((step k)))
            (is (holds? kb (list qualifies pug qb) U))))))))

(tu/deftest-kb a-disjoint-literal-a-closure-literal-waits-on-reads-the-closure-in-every-order
  ;; Each literal binds the other's ends and nothing else binds either, so the rule
  ;; arriving last reads the closure only through a join the stored `disjoint` leads.
  (doseq [edges [[:near-far] [:near :far]]
          order (oi/permutations (into [:rule :disjoint] edges))]
    (testing (str order)
      (tu/with-terms [narrow mid broad clashes]
        (let [step {:rule     #(v/assert kb (list 'set/forwardRule
                                                  (list 'implies (list 'and (list 'disjoint '?a '?b)
                                                                       (list 'genl '?a '?b))
                                                        (list clashes '?a '?b)))
                                         U)
                    :disjoint #(v/assert kb (list 'disjoint narrow broad) U)
                    :near-far #(v/assert kb (list 'genl narrow broad) U)
                    :near     #(v/assert kb (list 'genl narrow mid) U)
                    :far      #(v/assert kb (list 'genl mid broad) U)}]
          (doseq [k order] ((step k)))
          (is (= [#{[narrow broad]}]
                 (some->> (v/handle-of kb (list clashes narrow broad) U)
                          (v/supporting-justifications kb)
                          (map :subsumptions)))
              "one justification, reading the pair as the closure's"))))))

(deftest ^:red withdrawing-the-symmetric-mark-keeps-a-firing-the-separation-reading-proves
  ;; The store sorts the pair, so the rule's literal reads it mirrored.  The matcher's
  ;; firing names the mark; the separation reading needs none.  No re-join runs when a
  ;; mark leaves, so the firing goes OUT although the stated pair still proves it.
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (tu/with-terms [narrow broad clashes]
      (v/assert kb '(symmetric disjoint) U)
      (v/assert kb (list 'set/forwardRule
                         (list 'implies (list 'and (list 'disjoint '?a '?b) (list 'genl '?a '?b))
                               (list clashes '?a '?b)))
                U)
      (v/assert kb (list 'disjoint narrow broad) U)
      (v/assert kb (list 'genl narrow broad) U)
      (is (holds? kb (list clashes narrow broad) U) "the firing reads the mirrored pair")
      (v/retract! kb (v/handle-of kb '(symmetric disjoint) U))
      (is (holds? kb (list clashes narrow broad) U)
          "the stated pair still separates the two types, so the firing stays IN"))))

(defn- fired-pairs
  "The pairs over `types` that `p` holds in CxUniverse."
  [kb p types]
  (into #{} (comp (map #(vec (rest (:sentence %)))) (filter #(every? (set types) %)))
        (v/sentexes-matching kb (list p '?x '?y) U)))

(tu/deftest-kb a-disjoint-antecedent-no-other-literal-names-fires-on-the-stated-pair-in-every-order
  ;; `disjoint` is declared symmetric, so the matcher reads the stored pair in both
  ;; argument orders (docs/inference.md) and the rule fires on each.  The specialized
  ;; pair the query answers is not stored, so nothing fires on it.
  (doseq [order (oi/permutations [:rule :disjoint :edge])]
    (testing (str order)
      (tu/with-terms [fish_ mammal_ whale_ keptApart]
        (let [step {:rule     #(v/assert kb (list 'set/forwardRule
                                                  (list 'implies '(disjoint ?a ?b)
                                                        (list keptApart '?a '?b)))
                                         U)
                    :disjoint #(v/assert kb (list 'disjoint fish_ mammal_) U)
                    :edge     #(v/assert kb (list 'genl whale_ mammal_) U)}]
          (doseq [k order] ((step k)))
          (is (holds? kb (list 'disjoint fish_ whale_) U) "the query answers the specialized pair")
          (is (= #{[fish_ mammal_] [mammal_ fish_]} (fired-pairs kb keptApart [fish_ mammal_ whale_]))))))))

(tu/deftest-kb a-disjoint-antecedent-with-a-constant-matches-it-in-either-position
  ;; The rule names the constant second and the stated pair names it first, so only
  ;; the symmetric read binds ?x for the first rule.  Without `(symmetric disjoint)` only
  ;; the rule naming the constant first fires.
  (doseq [order (oi/permutations [:second :first :disjoint])]
    (testing (str order)
      (tu/with-terms [fish_ mammal_ apartFromFish apartFromFish2]
        (let [step {:second   #(v/assert kb (list 'set/forwardRule
                                                  (list 'implies (list 'disjoint '?x fish_)
                                                        (list apartFromFish '?x)))
                                         U)
                    :first    #(v/assert kb (list 'set/forwardRule
                                                  (list 'implies (list 'disjoint fish_ '?x)
                                                        (list apartFromFish2 '?x)))
                                         U)
                    :disjoint #(v/assert kb (list 'disjoint fish_ mammal_) U)}]
          (doseq [k order] ((step k)))
          (is (holds? kb (list apartFromFish mammal_) U) "the constant read in second position")
          (is (holds? kb (list apartFromFish2 mammal_) U) "the constant read in first position"))))))

(tu/deftest-kb a-disjoint-antecedent-another-literal-names-fires-on-every-separated-pair-in-every-order
  ;; `(genl ?a animal)` names ?a alone.  The edge arriving last moves `whale`, so only a
  ;; re-join binding ?b to it reads `[fish whale]`.
  (doseq [order (oi/permutations [:rule :disjoint :edge :animals])]
    (testing (str order)
      (tu/with-terms [fish_ mammal_ whale_ animal_ keptApart]
        (let [step {:rule     #(v/assert kb (list 'set/forwardRule
                                                  (list 'implies (list 'and (list 'genl '?a animal_)
                                                                       '(disjoint ?a ?b))
                                                        (list keptApart '?a '?b)))
                                         U)
                    :disjoint #(v/assert kb (list 'disjoint fish_ mammal_) U)
                    :edge     #(v/assert kb (list 'genl whale_ mammal_) U)
                    :animals  #(doseq [t [fish_ whale_]] (v/assert kb (list 'genl t animal_) U))}]
          (doseq [k order] ((step k)))
          (is (= #{[fish_ mammal_] [fish_ whale_] [whale_ fish_]}
                 (fired-pairs kb keptApart [fish_ mammal_ whale_]))))))))

;; ---- a negated antecedent reads a separation's denial ----------------------

(defn- denial-rule
  "*A `pet` that is not a `dog` is `stray`* — the negated literal's argument bound by the
  first antecedent."
  [pet dog stray]
  (list 'set/forwardRule
        (list 'implies (list 'and (list pet '?x) (list 'not (list dog '?x)))
              (list stray '?x))))

(def ^:private denial-ingredients [:rule :pet :member :edge :disjoint])

(defn- denial-fires-in-orders
  "Assert each ingredient of a separation-denial firing in each order of `orders`, and
  check the forward join stores the conclusion the query's denial licenses."
  [kb orders]
  (doseq [order orders]
    (testing (str order)
      (tu/with-terms [pet dog cat kitten stray Tom]
        (let [step {:rule     #(v/assert kb (denial-rule pet dog stray) U)
                    :pet      #(v/assert kb (list pet Tom) U)
                    :member   #(v/assert kb (list kitten Tom) U)
                    :edge     #(v/assert kb (list 'genl kitten cat) U {:strength :monotonic})
                    :disjoint #(v/assert kb (list 'disjoint dog cat) U)}]
          (doseq [k order] ((step k)))
          (is (holds? kb (list 'not (list dog Tom)) U))
          (is (some? (v/handle-of kb (list stray Tom) U)) "the forward join agrees"))))))

(tu/deftest-kb a-negated-antecedent-a-separation-denies-fires-whichever-ingredient-arrived-last
  ;; each rotation puts a different ingredient last, so each trigger path runs once
  (denial-fires-in-orders kb (for [i (range (count denial-ingredients))]
                               (let [[a b] (split-at i denial-ingredients)] (concat b a)))))

(tu/deftest-kb ^:slow a-negated-antecedent-a-separation-denies-fires-in-every-order
  (denial-fires-in-orders kb (oi/permutations denial-ingredients)))

(tu/deftest-kb a-separation-denial-firing-rests-on-the-membership-the-declaration-and-the-edge
  (tu/with-terms [pet dog cat kitten stray Tom]
    (let [decl   (v/assert kb (list 'disjoint dog cat) U)
          edge   (v/assert kb (list 'genl kitten cat) U {:strength :monotonic})
          member (v/assert kb (list kitten Tom) U)]
      (v/assert kb (denial-rule pet dog stray) U)
      (v/assert kb (list pet Tom) U)
      (let [named (set (keys (:nodes (v/why kb (v/handle-of kb (list stray Tom) U)))))]
        (is (every? named [decl edge member])))
      (doseq [[label h re] [["the membership" member #(v/assert kb (list kitten Tom) U)]
                            ["the edge" edge #(v/assert kb (list 'genl kitten cat) U
                                                        {:strength :monotonic})]
                            ["the declaration" decl #(v/assert kb (list 'disjoint dog cat) U)]]]
        (testing (str label " going takes the conclusion, and its return restores it")
          (v/retract! kb h)
          (is (not (holds? kb (list stray Tom) U)))
          (re)
          (is (holds? kb (list stray Tom) U)))))))

(tu/deftest-kb an-edit-of-memberships-reads-the-negated-rule-keys-once
  (tu/with-terms [pet dog cat kitten stray]
    (v/assert kb (list 'disjoint dog cat) U)
    (v/assert kb (list 'genl kitten cat) U {:strength :monotonic})
    (v/assert kb (denial-rule pet dog stray) U)
    (let [xs    (map #(symbol (str "Tom" %)) (range 5))
          reads (atom 0)
          meet  reads/as-stored-rule-keys-meeting]
      (with-redefs [reads/as-stored-rule-keys-meeting
                    (fn [idx within keep?]
                      (when (and (nil? (within Long/MAX_VALUE)) (keep? [:not dog]))
                        (swap! reads inc))
                      (meet idx within keep?))]
        (v/edit! kb {:add (vec (mapcat (fn [x] [[(list pet x) U] [(list kitten x) U]]) xs))}))
      (is (= 1 @reads))
      (is (every? #(holds? kb (list stray %) U) xs)))))

(tu/deftest-kb a-separation-denial-through-a-default-edge-fires-nothing
  ;; A `:default` edge does not contrapose, on either side of the separation
  ;; (docs/taxonomy.md, "A separation answers a denial").
  (doseq [side [:member :denied]]
    (testing (name side)
      (tu/with-terms [pet dog cat kitten stray Tom]
        (let [[sub super] (if (= :member side) [kitten cat] [kitten dog])
              member      (if (= :member side) kitten cat)
              denied      (if (= :member side) dog kitten)]
          (v/assert kb (list 'disjoint dog cat) U)
          (v/assert kb (list 'genl sub super) U {:strength :default})
          (v/assert kb (list member Tom) U)
          (v/assert kb (denial-rule pet denied stray) U)
          (v/assert kb (list pet Tom) U)
          (is (not (holds? kb (list 'not (list denied Tom)) U)))
          (is (not (holds? kb (list stray Tom) U)) "the forward join agrees")
          (v/assert kb (list 'genl sub super) U {:strength :monotonic})
          (is (holds? kb (list 'not (list denied Tom)) U))
          (is (holds? kb (list stray Tom) U) "a monotonic edge contraposes"))))))

(tu/deftest-kb an-exception-withdraws-a-separation-denial-firing-and-its-retraction-restores-it
  (tu/with-terms [pet whole qa qb stray Tom]
    (v/assert kb (list 'partition whole qa qb) U)
    (v/assert kb (list qa Tom) U)
    (v/assert kb (denial-rule pet qb stray) U)
    (v/assert kb (list pet Tom) U)
    (is (holds? kb (list stray Tom) U))
    (let [exc (v/assert kb (list 'siblingDisjointException qa qb) U)]
      (is (not (holds? kb (list 'not (list qb Tom)) U)))
      (is (not (holds? kb (list stray Tom) U)) "the exempted pair denies nothing")
      (v/retract! kb exc)
      (is (holds? kb (list stray Tom) U) "and the denial is back"))))

(tu/deftest-kb an-edge-between-two-marked-types-withdraws-a-separation-denial-firing-until-it-leaves
  ;; the mark's edges and memberships are monotonic, so the query reads the denial
  (doseq [[label mark] marks]
    (testing label
      (tu/with-terms [pet kind qa qb stray Tom]
        (doseq [s (mark kind qa qb)] (v/assert kb s U {:strength :monotonic}))
        (v/assert kb (list qa Tom) U)
        (v/assert kb (denial-rule pet qb stray) U)
        (v/assert kb (list pet Tom) U)
        (is (holds? kb (list stray Tom) U))
        (let [edge (v/assert kb (list 'genl qa qb) U)]
          (is (not (holds? kb (list 'not (list qb Tom)) U)))
          (is (not (holds? kb (list stray Tom) U)) "the forward join agrees")
          (v/retract! kb edge)
          (is (holds? kb (list stray Tom) U) "and the denial is back"))))))

(tu/deftest-kb a-closed-extent-negative-on-a-separated-type-fires-by-negation-as-failure
  ;; the grant withholds the literal from the join, so no stored negation and no
  ;; membership answers it, and the placement check reads the level-6 question
  (tu/with-terms [pet dog cat stray Tom]
    (v/assert kb (list 'disjoint dog cat) U)
    (v/assert kb (list 'closed_extent_predicate dog) U)
    (v/assert kb (denial-rule pet dog stray) U)
    (v/assert kb (list pet Tom) U)
    (is (holds? kb (list 'not (list dog Tom)) U))
    (is (holds? kb (list stray Tom) U) "the forward join agrees")))

(tu/deftest-kb a-reader-of-a-lazy-rule-a-separation-denies-fires-when-it-or-a-fact-arrives-last
  ;; the lazy rule is never fired; the forward reader proves its conclusion inside its join.
  ;; A separation moving re-joins no lazy rule's readers (inference.md), so the edge and
  ;; the declaration arrive first.
  (let [ings [:rule :edge :disjoint :reader :pet :member]]
    (doseq [k     [:reader :pet :member]
            :let [order (conj (filterv #(not= k %) ings) k)]]
      (testing (str order)
        (tu/with-terms [pet dog cat kitten stray adoptable Tom]
          (let [lazy (list 'set/lazyForwardRule (second (denial-rule pet dog stray)))
                step {:rule     #(v/assert kb lazy U)
                      :reader   #(v/assert kb (list 'set/forwardRule
                                                    (list 'implies (list stray '?x) (list adoptable '?x)))
                                           U)
                      :pet      #(v/assert kb (list pet Tom) U)
                      :member   #(v/assert kb (list kitten Tom) U)
                      :edge     #(v/assert kb (list 'genl kitten cat) U {:strength :monotonic})
                      :disjoint #(v/assert kb (list 'disjoint dog cat) U)}]
            (doseq [k order] ((step k)))
            (is (some? (v/handle-of kb (list adoptable Tom) U)))))))))
