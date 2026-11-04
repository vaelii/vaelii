;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.query-context-test
  "The query contexts and the variable context: the write side refuses a query context,
  the read side resolves each, and the two joint strategies agree (docs/contexts.md).  A
  query context reaching the engine answers empty, so every test here checks a positive
  answer beside each refusal."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.vantage :as vantage]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- proper-subset?
  "Every member of `a` is in `b`, and `b` has more — the form a *narrower* reading has
  against a wider one."
  [a b]
  (and (every? b a) (> (count b) (count a))))

(defn- siblings!
  "Wire `a` and `b` as incomparable contexts under CxUniverse: each sees the whole shipped
  ontology, neither sees the other, and no context sees both."
  [kb a b]
  (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx b 'CxUniverse) 'CxUniverse))

;; ---- a query context is not a place -------------------------------------

(tu/deftest-kb nothing-is-asserted-into-a-query-context
  (doseq [qc '[CxEverything CxInference CxNothing]]
    (testing (str qc)
      (let [e (is (thrown? clojure.lang.ExceptionInfo (v/assert kb '(dog Muffet) qc)))]
        (is (= :shape (:type (ex-data e)))
            "refused as a shape invariant, so no :naming policy can wave it through")))))

(tu/deftest-kb no-genlCx-edge-may-name-a-query-context
  (tu/with-terms [CxReal]
    (v/assert kb (list 'genlCx CxReal 'CxUniverse) 'CxUniverse)
    (doseq [qc '[CxEverything CxInference CxNothing]]
      (testing (str qc)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'genlCx CxReal qc) 'CxUniverse))
            "as the super: it would start inheriting a place in the lattice")
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'genlCx qc CxReal) 'CxUniverse))
            "as the sub: CxNothing sees nothing precisely because nothing wires it")))))

(tu/deftest-kb a-query-context-is-not-one-of-the-kbs-contexts
  (let [cs (set (v/contexts kb))]
    (doseq [qc '[CxEverything CxInference CxNothing]]
      (is (not (contains? cs qc)) (str qc " must not be a node of the genlCx lattice")))))

;; ---- CxInference: the joint reading -------------------------------------

(tu/deftest-kb cxinference-refuses-a-join-no-single-reader-sees
  (tu/with-terms [CxA CxB p1 p2 Ind1 Ind2]
    (siblings! kb CxA CxB)
    (v/assert kb (list p1 'Muffet Ind1) CxA)
    (v/assert kb (list p2 Ind1 Ind2) CxB)
    (let [goal [(list p1 'Muffet '?x) (list p2 '?x '?y)]]
      (testing "no context sees both halves"
        (is (empty? (filter #(and (contains? (set (v/context-up kb %)) CxA)
                                  (contains? (set (v/context-up kb %)) CxB))
                            (v/contexts kb)))))
      (testing "the wide reading still joins them — that is what CxEverything is for"
        (is (seq (v/query kb goal 'CxEverything))))
      (testing "a variable context does not: it is the joint reading"
        (is (empty? (v/query kb goal '?ctx))))
      (testing "every real vantage answers nothing"
        (doseq [c [CxA CxB 'CxUniverse 'CxWell]]
          (is (empty? (v/query kb goal c)) (str "from " c))))
      (testing "so CxInference answers nothing"
        (is (empty? (v/query kb goal 'CxInference)))))))

(tu/deftest-kb cxinference-answers-and-binds-the-witness-when-a-reader-exists
  (tu/with-terms [CxA CxB CxBoth p1 p2 Ind1 Ind2]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'genlCx CxBoth CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBoth CxB) 'CxUniverse)
    (v/assert kb (list p1 'Muffet Ind1) CxA)
    (v/assert kb (list p2 Ind1 Ind2) CxB)
    (let [goal [(list p1 'Muffet '?x) (list p2 '?x '?y)]
          sols (vec (v/query kb goal 'CxInference))]
      (is (= 1 (count sols)))
      (testing "the bindings the goal asked for"
        (is (= Ind1 (get (first sols) '?x)))
        (is (= Ind2 (get (first sols) '?y))))
      (testing "plus the reader that answered, under witness-key"
        (is (= CxBoth (get (first sols) vantage/witness-key))))
      (testing "the witness is the *most general* reader, not every one below it"
        (tu/with-terms [CxDeeper]
          (v/assert kb (list 'genlCx CxDeeper CxBoth) 'CxUniverse)
          (is (= [CxBoth] (mapv #(get % vantage/witness-key)
                                (v/query kb goal 'CxInference)))
              "CxDeeper sees everything CxBoth does and adds no claim"))))))

(tu/deftest-kb cxinference-finds-a-reader-with-no-genlCx-edge-of-its-own
  (tu/with-terms [CxLoner p1]
    (v/assert kb (list p1 'Muffet 'Muffet) CxLoner)
    (is (not (contains? (set (v/contexts kb)) CxLoner))
        "precondition: no edge, so not a node of the lattice")
    (doseq [s [:fan :post-hoc]]
      (let [sols (vec (binding [vantage/*strategy* s]
                        (v/query kb (list p1 '?a '?b) 'CxInference)))]
        (is (= 1 (count sols)) (str s))
        (is (= CxLoner (get (first sols) vantage/witness-key)) (str s))))))

(tu/deftest-kb cxinference-witnesses-an-inferred-type-where-its-ingredients-meet
  ;; constraint-only, so `(t1 X)` is inferred at the read from the tuple and the
  ;; declaration, and no membership is stored for a reader to match
  (tu/without-entailing
   (doseq [[label edges tuple-at decl-at want]
           [["both in one edgeless context" [] :a :a [:a]]
            ["both in one edgeless context, beside an unrelated edge"
             [[:z 'CxUniverse]] :a :a [:a]]
            ["split over two contexts no context sees together" [] :a :b []]
            ["split over two siblings and the context below both"
             [[:a 'CxUniverse] [:b 'CxUniverse] [:both :a] [:both :b]] :a :b [:both]]]
           s [:fan :post-hoc]]
     (tu/with-terms [CxA CxB CxBoth CxZ p1 t1 X Y]
       (let [c #(get {:a CxA :b CxB :both CxBoth :z CxZ} % %)]
         (doseq [[sub super] edges]
           (v/assert kb (list 'genlCx (c sub) (c super)) 'CxUniverse))
         (v/assert kb (list p1 X Y) (c tuple-at))
         (v/assert kb (list 'arg p1 1 t1) (c decl-at))
         (is (= (mapv c want)
                (mapv vantage/witness-key
                      (binding [vantage/*strategy* s] (v/query kb (list t1 X) 'CxInference))))
             (str label ", " s))
         (is (= s (binding [vantage/*strategy* s]
                    (:strategy (vantage/answers kb [(list t1 X)] #(v/query kb (list t1 X) %) {}))))
             (str label ", " s ": the strategy asked for is the one that answered")))))))

(tu/deftest-kb cxinference-reads-the-edgeless-context-holding-a-computed-answer
  ;; one unrelated edge, so the lattice is not empty and the read does not fall back to
  ;; the unscoped one; RCC-8 registered for the calculus row
  (tu/without-entailing
   (tu/with-terms [CxA CxZ psym ptr pinv qinv pdi qdi prefl tt1 tt2 tt3 pm pa pb pti ptd pce
                   tw tp1 tp2 tds tdn A B C D E F R1 R2 R3]
     (v/assert kb (list 'genlCx CxZ 'CxUniverse) 'CxUniverse)
     (v/add-reasoner kb :rcc8)
     (doseq [[label facts goal also]
             [["the mirror of a symmetric fact"
               [(list 'symmetric psym) (list psym B A)] (list psym A B)]
              ["two hops of a transitive predicate"
               [(list 'transitive ptr) (list ptr A B) (list ptr B C)] (list ptr A C)]
              ["the partner spelling of an inverse"
               [(list 'inverse pinv qinv) (list qinv B A)] (list pinv A B)]
              ["a denial through a known-true inverse"
               [(list 'set/monotonic (list 'inverse pdi qdi)) (list 'not (list qdi B A))]
               (list 'not (list pdi A B))]
              ["two genl edges" [(list 'genl tt1 tt2) (list 'genl tt2 tt3)] (list 'genl tt1 tt3)]
              ["an argument type read up genl" [(list 'arg pm 1 tt1)] (list 'arg pm 1 tt3)]
              ["a separation read down genl" [(list 'disjoint tt2 'number)] (list 'disjoint tt1 'number)]
              ;; the mark's lifted copy in CxUniverse answers, and CxA sees CxUniverse
              ["a reflexive pair" [(list 'reflexive prefl)] (list prefl A A) #{'CxUniverse}]
              ["an open membership a declaration types"
               [(list 'arg pm 1 tt1) (list pm B C)] (list tt1 '?x)]
              ["a denial read off a negates declaration"
               [(list 'negates pa pb) (list pb A B)] (list 'not (list pa A B))]
              ["a claim carried up genl by transitiveInArg"
               [(list 'transitiveInArg pti 2 'genl) (list pti A tt1)] (list pti A tt2)]
              ["a denial carried down genl by transitiveInArgInverse"
               [(list 'transitiveInArgInverse ptd 1 'genl) (list 'not (list ptd tt2 A))]
               (list 'not (list ptd tt1 A))]
              ;; a number, which `ArgTypeProver` does not type, so its usage names no reader
              ["the part a covering leaves"
               [(list 'covering tw tp1 tp2) (list tw 5) (list 'not (list tp1 5))] (list tp2 5)]
              ["a denial under a closed extent"
               [(list 'closed_extent_predicate pce)] (list 'not (list pce A))]
              ["a computed sufficient condition"
               [(list 'defnSufficient tds (list 'greaterThan '?x 10))] (list tds 20)]
              ["a computed necessary condition that fails"
               [(list 'defnNecessary tdn (list 'greaterThan '?x 10))] (list 'not (list tdn 3))]
              ["an RCC-8 composition"
               [(list 'nonTangentialProperPart R1 R2) (list 'nonTangentialProperPart R2 R3)]
               (list 'nonTangentialProperPart R1 R3)]
              ;; last: the merge it makes is of terms no other row names
              ["two hops of sameAs" [(list 'sameAs D E) (list 'sameAs E F)] (list 'sameAs D F)]]]
       (doseq [f facts] (v/assert kb f CxA))
       (doseq [s [:fan :post-hoc]]
         (is (= (or also #{CxA})
                (set (map vantage/witness-key
                          (binding [vantage/*strategy* s] (v/query kb goal 'CxInference)))))
             (str label ", " s)))))))

;; ---- the two implementations must agree ---------------------------------

(tu/deftest-kb fan-and-post-hoc-answer-alike
  ;; stored-fact literals and no rule expansion, so post-hoc answers each goal
  (tu/with-terms [CxA CxB CxBoth p1 p2 Ind1 Ind2 Ind3]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'genlCx CxBoth CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBoth CxB) 'CxUniverse)
    (v/assert kb (list p1 'Muffet Ind1) CxA)
    (v/assert kb (list p1 'Muffet Ind2) CxA)
    (v/assert kb (list p2 Ind1 Ind3) CxB)
    (v/assert kb (list p2 Ind2 Ind3) CxBoth)
    (v/assert kb (list p2 Ind3 Ind3) CxA)
    (doseq [goal [[(list p1 'Muffet '?x) (list p2 '?x '?y)]
                  [(list p2 '?x '?y)]
                  [(list p1 '?a '?b) (list p2 '?b '?c) (list p2 '?c '?d)]]]
      (testing (pr-str goal)
        (let [fan  (set (binding [vantage/*strategy* :fan]
                          (v/query kb goal 'CxInference)))
              post (set (binding [vantage/*strategy* :post-hoc]
                          (v/query kb goal 'CxInference)))]
          (is (= fan post) "the strategy is a cost decision, not a semantic one"))))))

;; ---- CxEverything: syntactic, and blind to belief ------------------------

(tu/deftest-kb cxeverything-sees-a-defeated-default
  (tu/with-terms [p1 Ind1]
    (let [h (v/assert kb (list p1 Ind1) 'CxUniverse)]
      (v/assert kb (list 'not (list p1 Ind1)) 'CxUniverse {:strength :monotonic})
      (is (false? (v/in? kb h)) "precondition: the default is stored but OUT")
      (testing "a belief-following read does not have it"
        (is (empty? (v/sentexes-matching kb (list p1 Ind1) '?ctx)))
        (is (empty? (v/query kb (list p1 '?x) '?ctx))))
      (testing "CxEverything does — that is what it is for"
        (is (= [h] (mapv :id (v/sentexes-matching kb (list p1 Ind1) 'CxEverything))))
        (is (= [{'?x Ind1}] (vec (v/query kb (list p1 '?x) 'CxEverything))))))))

(tu/deftest-kb cxeverything-and-an-ordinary-read-do-not-answer-each-other
  ;; `matches-visible` caches by literal and view context; both reads ask the same
  ;; literal at the same (wildcard) context, so without the flag in the key whichever
  ;; ran first would answer for both.
  (tu/with-terms [p1 Ind1]
    (let [h (v/assert kb (list p1 Ind1) 'CxUniverse)]
      (v/assert kb (list 'not (list p1 Ind1)) 'CxUniverse {:strength :monotonic})
      (is (false? (v/in? kb h)))
      (testing "ordinary first, then blind"
        (is (empty? (v/query kb (list p1 '?x) '?ctx)))
        (is (seq (v/query kb (list p1 '?x) 'CxEverything))))
      (testing "blind first, then ordinary"
        (tu/with-terms [p2 Ind2]
          (let [h2 (v/assert kb (list p2 Ind2) 'CxUniverse)]
            (v/assert kb (list 'not (list p2 Ind2)) 'CxUniverse {:strength :monotonic})
            (is (false? (v/in? kb h2)))
            (is (seq (v/query kb (list p2 '?x) 'CxEverything)))
            (is (empty? (v/query kb (list p2 '?x) '?ctx)))))))))

(tu/deftest-kb cxeverything-crosses-contexts-no-reader-spans
  (tu/with-terms [CxA CxB p1 p2 Ind1 Ind2]
    (siblings! kb CxA CxB)
    (v/assert kb (list p1 'Muffet Ind1) CxA)
    (v/assert kb (list p2 Ind1 Ind2) CxB)
    (let [goal [(list p1 'Muffet '?x) (list p2 '?x '?y)]]
      (is (= [{'?x Ind1 '?y Ind2}] (vec (v/query kb goal 'CxEverything)))
          "the syntactic reading asks what the store spells, not what a vantage holds")
      (is (empty? (v/query kb goal 'CxInference))
          "which is the whole difference between the two"))))

;; ---- CxNothing: the provers alone ---------------------------------------

(tu/deftest-kb cxnothing-sees-no-stored-fact
  (tu/with-terms [p1 Ind1]
    (v/assert kb (list p1 Ind1) 'CxUniverse)
    (is (seq (v/query kb (list p1 '?x) '?ctx)) "precondition: the fact is there")
    (is (empty? (v/query kb (list p1 '?x) 'CxNothing)))
    (is (empty? (v/sentexes-matching kb (list p1 Ind1) 'CxNothing)))))

(tu/deftest-kb cxnothing-still-lets-a-prover-answer
  ;; an evaluable is computed rather than matched, so it is exactly what survives a
  ;; vantage that holds nothing
  (is (= [{'?n 5}] (vec (v/query kb '(evaluate ?n (+ 2 3)) 'CxNothing)))))

(tu/deftest-kb cxnothing-inherits-nothing-not-even-the-shipped-vocabulary
  ;; The `genl` closure is **reflexive**, so `(genl dog ?x)` answers `dog` with no edge in
  ;; view at all — that answer is the closure's own shape rather than anything CxNothing
  ;; can see, and it is the control on this test as much as the assertion is: a reading
  ;; that saw nothing *whatsoever* would have lost the reflexive answer too.
  (let [nothing (set (map '?x (v/query kb '(genl dog ?x) 'CxNothing)))
        well    (set (map '?x (v/query kb '(genl dog ?x) 'CxWell)))]
    (is (= #{'dog} nothing)
        "the reflexive answer, and not one edge of the shipped taxonomy")
    (is (contains? well 'mammal)
        "control: a real vantage below the middle contexts walks the chain in CxUniverse")
    (is (proper-subset? nothing well))))

;; ---- an entry point that cannot resolve one says so ------------------------------

(tu/deftest-kb an-unresolving-entry-point-refuses-rather-than-answering-empty
  (tu/with-terms [p1 Ind1]
    (v/assert kb (list p1 Ind1) 'CxUniverse)
    (doseq [[nm f] [["handle-of"      #(v/handle-of kb (list p1 Ind1) %)]
                    ["lookup"         #(v/lookup kb 2 (list p1 '?x) %)]
                    ["explain-levels" #(v/explain-levels kb (list p1 '?x) %)]
                    ["query-plan"     #(v/query-plan kb (list p1 '?x) %)]
                    ["why-not"        #(v/why-not kb (list p1 Ind1) %)]]]
      (testing nm
        (is (some? (f 'CxUniverse)) "control: the entry point works at a real context")
        (let [e (is (thrown? clojure.lang.ExceptionInfo (f 'CxInference)))]
          (is (= :unsupported-context (:type (ex-data e)))))))))

(tu/deftest-kb an-ist-goal-rescues-an-unresolving-entry-point
  (tu/with-terms [p1 Ind1]
    (let [h (v/assert kb (list p1 Ind1) 'CxUniverse)]
      (is (= h (v/handle-of kb (list 'ist 'CxUniverse (list p1 Ind1)) 'CxInference))))))

;; ---- post-hoc's ingredients are not only the facts -----------------------

(tu/deftest-kb post-hoc-places-by-the-genl-edge-a-match-subsumed-through
  ;; the fact in CxA and the edge it is matched over in CxB
  (tu/with-terms [CxA CxB sub_t sup_t Ind1]
    (siblings! kb CxA CxB)
    (v/assert kb (list sub_t Ind1) CxA)
    (v/assert kb (list 'genl sub_t sup_t) CxB)
    (let [goal (list sup_t '?x)]
      (testing "the answer needs both, and no reader sees both"
        (is (empty? (v/query kb goal CxA)) "CxA has the fact, not the edge")
        (is (empty? (v/query kb goal CxB)) "CxB has the edge, not the fact")
        (is (seq (v/query kb goal 'CxEverything)) "the wide reading joins them")
        (is (empty? (v/query kb goal '?ctx)) "a variable context is the joint reading"))
      (testing "so neither strategy may answer"
        (is (empty? (binding [vantage/*strategy* :fan] (v/query kb goal 'CxInference))))
        (is (empty? (binding [vantage/*strategy* :post-hoc] (v/query kb goal 'CxInference))))))
    (testing "and both answer when one reader does see both"
      (tu/with-terms [CxBoth]
        (v/assert kb (list 'genlCx CxBoth CxA) 'CxUniverse)
        (v/assert kb (list 'genlCx CxBoth CxB) 'CxUniverse)
        (let [goal (list sup_t '?x)
              fan  (set (binding [vantage/*strategy* :fan] (v/query kb goal 'CxInference)))
              post (set (binding [vantage/*strategy* :post-hoc] (v/query kb goal 'CxInference)))]
          (is (= #{{'?x Ind1 vantage/witness-key CxBoth}} fan))
          (is (= fan post)))))))

(tu/deftest-kb post-hoc-places-by-the-genlInverse-edge-a-match-subsumed-through
  ;; The fact is in CxA, and the `genlInverse` edge it is matched over is in CxB.
  (tu/with-terms [CxA CxB childOf parentOf Ind1 Ind2]
    (siblings! kb CxA CxB)
    (v/assert kb (list childOf Ind1 Ind2) CxA)
    (v/assert kb (list 'genlInverse childOf parentOf) CxB)
    (let [goal (list parentOf '?x '?y)]
      (is (seq (v/query kb goal 'CxEverything)) "the wide reading joins them")
      (testing "no reader sees both, so neither strategy may answer"
        (is (empty? (binding [vantage/*strategy* :fan] (v/query kb goal 'CxInference))))
        (is (empty? (binding [vantage/*strategy* :post-hoc] (v/query kb goal 'CxInference))))))))

(tu/deftest-kb post-hoc-will-not-place-an-answer-into-a-context-that-excepts-it
  ;; the unscoped pass matches the excepted sentex, so the placement has to drop CxA
  (tu/with-terms [CxA p1 Ind1]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (let [h (v/assert kb (list p1 Ind1) CxA)
          goal (list p1 '?x)]
      (is (seq (v/query kb goal CxA)) "precondition: visible before the except")
      (v/assert kb (list 'except (list 'sentexHandle h)) CxA)
      (is (empty? (v/query kb goal CxA)) "hidden from CxA and everything below it")
      (is (seq (v/query kb goal 'CxEverything)) "the wide pass still matches it")
      (testing "so neither strategy may answer"
        (is (empty? (binding [vantage/*strategy* :fan] (v/query kb goal 'CxInference))))
        (is (empty? (binding [vantage/*strategy* :post-hoc] (v/query kb goal 'CxInference))))))))

;; ---- a variable context is the same reading, with somewhere to put the answer ----

(tu/deftest-kb a-variable-context-is-the-joint-reading-and-binds-its-own-name
  (tu/with-terms [CxA CxB CxBoth p1 p2 Ind1 Ind2]
    (siblings! kb CxA CxB)
    (v/assert kb (list 'genlCx CxBoth CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBoth CxB) 'CxUniverse)
    (v/assert kb (list p1 'Muffet Ind1) CxA)
    (v/assert kb (list p2 Ind1 Ind2) CxB)
    (let [goal [(list p1 'Muffet '?x) (list p2 '?x '?y)]]
      (testing "the witness lands in whatever variable the caller named"
        (is (= [CxBoth] (mapv '?home (v/query kb goal '?home))))
        (is (= [CxBoth] (mapv '?ctx (v/query kb goal '?ctx))))
        (is (= [CxBoth] (mapv '?ctx (v/query kb goal)))
            "including the short arity, which names ?ctx"))
      (testing "CxInference names no variable, so its witness is beside the bindings"
        (let [sol (first (v/query kb goal 'CxInference))]
          (is (= CxBoth (:context sol)))
          (is (not (contains? sol '?ctx)) "nothing was passed to bind")))
      (testing "the witness UNIFIES into that variable; it does not overwrite it"
        ;; two facts in CxA, one naming CxA and one naming CxB: with the witness variable
        ;; in the argument slot, only the row whose argument is its own witness survives
        (tu/with-terms [holdsIn]
          (v/assert kb (list holdsIn CxA) CxA)
          (v/assert kb (list holdsIn CxB) CxA)
          (is (= [{'?home CxA}] (vec (v/query kb (list holdsIn '?home) '?home))))
          (is (= #{CxA} (set (map '?home (v/query kb (list holdsIn '?c) '?home))))
              "control: in an ordinary slot both rows come back, both witnessed by CxA"))))))

;; ---- where the joint reading stops, and why -----------------------------

(tu/deftest-kb a-goal-with-no-monotone-literal-is-asked-of-the-kb
  ;; CxB does not see the fact, so a fanned `unknown` would answer true from CxB
  (tu/with-terms [CxA CxB p1 Ind1]
    (siblings! kb CxA CxB)
    (v/assert kb (list p1 Ind1) CxA)
    (is (false? (v/ask? kb (list 'unknown (list p1 Ind1)) CxA)) "CxA sees it")
    (is (true? (v/ask? kb (list 'unknown (list p1 Ind1)) CxB)) "CxB does not")
    (testing "asked of the KB, it is known — the ignorant reader does not get a vote"
      (is (false? (v/ask? kb (list 'unknown (list p1 Ind1)) '?ctx)))
      (is (false? (v/ask? kb (list 'unknown (list p1 Ind1))))))
    (testing "an evaluable is the same shape: computed, so it names no context"
      (is (= [{'?n 5}] (vec (v/query kb '(evaluate ?n (+ 2 3)))))
          "answered, and with no witness — there is nothing that could bear one"))))

(tu/deftest-kb a-mixed-goal-evaluates-naf-at-the-reader-that-answered
  (tu/with-terms [CxA CxB p1 p2 Ind1]
    (siblings! kb CxA CxB)
    (v/assert kb (list p1 Ind1) CxA)
    (v/assert kb (list p2 Ind1) CxB)
    (testing "a reader that sees p1 and does not know p2"
      (is (= [CxA] (mapv '?ctx (v/query kb [(list p1 '?x) (list 'unknown (list p2 '?x))]
                                        '?ctx)))))
    (testing "and the converse, from the other side"
      (is (= [CxB] (mapv '?ctx (v/query kb [(list p2 '?x) (list 'unknown (list p1 '?x))]
                                        '?ctx)))))))

;; ---- post-hoc's budget and domain ----------------------------------------
;;
;; Each shape here is one `vantage_differential_test`'s generator does not build: a third
;; literal, a merged spelling in the goal, an argument-type declaration.

(defn- agree?
  "Do the two strategies answer alike?  Returns `[fan post-hoc]` for a readable failure."
  [kb goal ctx]
  [(set (binding [vantage/*strategy* :fan] (v/query kb goal ctx)))
   (set (binding [vantage/*strategy* :post-hoc] (v/query kb goal ctx)))])

(tu/deftest-kb a-join-past-the-budget-falls-to-the-fan-rather-than-throwing
  ;; three literals: the bail fires at stage two at the earliest, and only a literal after
  ;; it reduces over the sentinel
  (tu/with-terms [CxA p1 p2 p3 K]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (dotimes [i 40]
      (v/assert kb (list p1 (symbol (str "QA" i)) K) CxA)
      (v/assert kb (list p2 K (symbol (str "QB" i))) CxA)
      (v/assert kb (list p3 (symbol (str "QB" i)) 'QM) CxA))
    (binding [vantage/*rows-per-reader* 1]          ; force the bail on a small world
      (let [goal [(list p1 '?x '?k) (list p2 '?k '?y) (list p3 '?y '?m)]
            [fan post] (agree? kb goal '?ctx)]
        (is (= fan post) "abandoned mid-join, and the fan answered")
        (is (seq fan) "and the world really does answer")
        (is (= [:fan true]
               ((juxt :strategy :abandoned-post-hoc)
                (vantage/answers kb goal #(v/query kb goal %) {}))))))))

(tu/deftest-kb the-budget-does-not-charge-for-the-first-literal
  (tu/with-terms [CxA p1]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (dotimes [i 30] (v/assert kb (list p1 (symbol (str "QC" i)) 'QN) CxA))
    (binding [vantage/*rows-per-reader* 1]
      (let [{:keys [strategy]} (vantage/answers kb [(list p1 '?x '?y)]
                                                #(v/query kb (list p1 '?x '?y) %) {})]
        (is (= :post-hoc strategy)
            "thirty rows in one literal, budget one, and still not abandoned")))))

(tu/deftest-kb a-merge-the-reader-cannot-see-did-not-rewrite-its-goal
  ;; the reader above the `sameAs` asks the goal as written, the one below asks it rewritten
  (tu/with-terms [CxUp CxLow p1 A B Q]
    (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLow CxUp) 'CxUniverse)
    (v/assert kb (list p1 A Q) CxUp)                ; the fact, above the merge
    (v/assert kb (list 'sameAs A B) CxLow)          ; the merge, below it
    (let [[fan post] (agree? kb (list p1 B '?y) '?ctx)]
      (is (= fan post))
      (is (= [CxLow] (mapv '?ctx fan))
          "only the context that can see the sameAs can ask the question with B in it"))))

(tu/deftest-kb a-literal-that-reaches-another-prover-once-bound-goes-to-the-fan
  ;; `(t1 ?a)` reaches the stored-fact prover alone as written, since under the entailing
  ;; reading the mint `(t1 X)` covers what the argument-type prover would add, and
  ;; `(t1 X)` reaches the argument-type prover once the join binds `?a`
  (tu/with-entailing
    (tu/with-terms [CxA p1 t1 Seed X Y]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list t1 Seed) CxA)
      (v/assert kb (list 'arg p1 1 t1) CxA)          ; argument type: p1's first arg is a t1
      (v/assert kb (list p1 X Y) CxA)
      (let [goal       [(list p1 '?a '?b) (list t1 '?a)]
            [fan post] (agree? kb goal '?ctx)]
        (is (= fan post))
        (is (seq fan) "the argument-type prover answers the second literal, and it counts")
        (is (= [:fan true] ((juxt :strategy :abandoned-post-hoc)
                            (vantage/answers kb goal #(v/query kb goal %) {}))))))))

(tu/deftest-kb post-hoc-places-an-inferred-type-by-every-route-its-genl-edge-is-stated-on
  ;; one `genl` edge stated in two sibling contexts, and the reader below one of them: a
  ;; placement by the other route alone finds no context that sees the usage
  (tu/without-entailing
   (tu/with-terms [CxP CxQ CxD ta tb p1 Fido Rex Y]
     (siblings! kb CxP CxQ)
     (v/assert kb (list 'genlCx CxD CxQ) 'CxUniverse)
     (v/assert kb (list 'genl ta tb) CxP)
     (v/assert kb (list 'genl ta tb) CxQ)
     (v/assert kb (list ta Fido) CxD)
     (v/assert kb (list 'arg p1 1 ta) CxD)
     (v/assert kb (list p1 Rex Y) CxD)
     (doseq [[label goal] [["a stored membership" (list tb Fido)]
                           ["an inferred membership" (list tb Rex)]]
             s [:fan :post-hoc]]
       (let [{:keys [answers strategy]} (binding [vantage/*strategy* s]
                                          (vantage/answers kb [goal] #(v/query kb goal %) {}))]
         (is (= s strategy) (str label ", " s))
         (is (= [CxD] (mapv vantage/witness-key answers)) (str label ", " s)))))))

(tu/deftest-kb post-hoc-places-an-open-inferred-type-at-the-meet-of-its-declaration-and-usage
  ;; constraint-only, so `(t5 ?a)` reaches the argument-type prover as written; the
  ;; declaration is in CxA, the usage in CxB, and only CxC sees both
  (tu/without-entailing
   (tu/with-terms [CxA CxB CxC p5 t5 M N]
     (siblings! kb CxA CxB)
     (v/assert kb (list 'genlCx CxC CxA) 'CxUniverse)
     (v/assert kb (list 'genlCx CxC CxB) 'CxUniverse)
     (v/assert kb (list 'arg p5 1 t5) CxA)
     (v/assert kb (list p5 M N) CxB)
     (doseq [s [:fan :post-hoc]]
       (let [goal [(list t5 '?a)]
             {:keys [answers strategy]} (binding [vantage/*strategy* s]
                                          (vantage/answers kb goal #(v/query kb goal %) {}))]
         (is (= s strategy) (str s))
         (is (= [CxC] (mapv vantage/witness-key answers)) (str s))
         (is (= [M] (map '?a (binding [vantage/*strategy* s] (v/query kb (first goal) 'CxInference))))
             (str s)))))))

(tu/deftest-kb an-open-inferred-type-reads-no-usage-its-reader-retired
  ;; constraint-only, so `(t5 ?a)` reaches the argument-type prover's open arm; CxB merges
  ;; M and N, so it retires the usage spelled at the elected-away term and reads its twin
  (tu/without-entailing
   (tu/with-terms [CxA CxB p5 t5 M N Z]
     (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
     (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
     (v/assert kb (list p5 M Z) CxA)
     (v/assert kb (list p5 N Z) CxA)
     (v/assert kb (list 'arg p5 1 t5) CxB)
     (v/assert kb (list 'sameAs M N) CxB)
     (let [goal (list t5 '?a)]
       (is (= 1 (count (v/query kb goal CxB))))
       (doseq [s [:fan :post-hoc]]
         (is (= 1 (count (binding [vantage/*strategy* s] (v/query kb goal 'CxInference))))
             (str s)))))))

(tu/deftest-kb a-blind-read-does-not-leave-its-closure-behind
  (tu/with-terms [CxA before A B C]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'transitive before) 'CxUniverse)
    (v/assert kb (list before A B) CxA {:strength :monotonic})
    (v/assert kb (list before B C) CxA {:strength :default})
    (v/assert kb (list 'not (list before B C)) CxA {:strength :monotonic})
    ;; the blind read runs first: warmed the other way, a shared entry would give the blind
    ;; read the ordinary answer, which this test would not see
    (let [blind (set (map #(get % '?y) (v/ask kb (list before A '?y) 'CxEverything)))
          reach (set (map #(get % '?y)
                          (:results (v/ask-within kb (list before A '?y) {:max-ms 5000}))))]
      (is (= #{B C} blind) "belief off, so the defeated default is spelled and returned")
      (is (= #{B} reach)
          "and the ordinary read that followed it does not inherit the unbelieved walk"))))

(tu/deftest-kb a-rule-cannot-name-a-query-context-as-its-target
  (tu/with-terms [CxA p1 p2 Ind1]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (is (= :not-well-formed
           (try (v/assert-rule kb [(list p1 '?x)] (list 'ist 'CxNothing (list p2 '?x)) CxA
                               {:chain? true})
                nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
    (v/assert kb (list p1 Ind1) CxA {:chain? true})
    (is (empty? (v/sentexes-matching kb (list p2 '?x) 'CxEverything))
        "and nothing was stored")))

(tu/deftest-kb the-records-read-stays-lazy-when-no-context-is-named
  (tu/with-terms [CxA p1]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (dotimes [i 5] (v/assert kb (list p1 (symbol (str "QL" i)) 'QLK) CxA))
    (is (instance? clojure.lang.LazySeq (v/sentexes-matching kb (list p1 '?a '?b)))
        "the default context")
    (is (instance? clojure.lang.LazySeq (v/sentexes-matching kb (list p1 '?a '?b) CxA))
        "and a named one")
    (testing "and it is the fan, not the wildcard"
      ;; a sentex excepted from the only context that sees it is visible to the wildcard
      ;; and to no reader
      (let [h (v/handle-of kb (list p1 'QL0 'QLK) CxA)]
        (v/assert kb (list 'except (list 'sentexHandle h)) CxA)
        (is (not-any? #(= h (:id %)) (v/sentexes-matching kb (list p1 '?a '?b)))
            "no reader sees it, so the read does not report it")))))

(tu/deftest-kb a-proof-answer-carries-its-witness-among-the-bindings
  ;; `:proof?` with a depth answers `{:bindings … :proof …}`
  (tu/with-terms [CxA q1 r1 Ind1]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list q1 Ind1) CxA)
    (v/assert-rule kb [(list q1 '?x)] (list r1 '?x) CxA)
    (let [[answer :as answers] (v/query kb (list r1 '?x) '?home {:max-depth 2 :proof? true})]
      (is (seq answers) "precondition: the rule answers it")
      (is (= #{:bindings :proof} (set (keys answer)))
          "the documented shape, and not a third key beside it")
      (is (= CxA (get-in answer [:bindings '?home]))
          "the witness is a binding, so it is among the bindings"))))

;; ---- what an unscoped read cannot be asked -------------------------------

(defn- refusal
  "The `:type` `f` is refused with, or `:answered` if it was not refused at all."
  [f]
  (try (doall (f)) :answered (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb a-goal-may-not-spell-the-marker-an-unscoped-read-matches-on
  (tu/with-terms [CxA p1 X Y]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list p1 X Y) CxA)
    (let [goal (list p1 '?ctx '?b)]
      (testing "every unscoped entry point refuses it"
        (is (= :shape (refusal #(v/query kb goal))))
        (is (= :shape (refusal #(v/query kb goal '?home))))
        (is (= :shape (refusal #(v/query kb goal 'CxEverything))))
        (is (= :shape (refusal #(v/query kb goal 'CxInference))))
        (is (= :shape (refusal #(v/ask kb goal))))
        (is (= :shape (refusal #(v/sentexes-matching kb goal)))))
      (testing "and a named context answers it"
        (is (= [{'?ctx X '?b Y}] (vec (v/query kb goal CxA)))
            "?ctx binds the argument it stands in, there being no marker to collide with")))
    (testing "a goal that does not spell it is untouched"
      (is (= [{'?a X '?b Y '?ctx CxA}] (vec (v/query kb (list p1 '?a '?b))))))))

(tu/deftest-kb a-context-that-names-no-context-is-refused-rather-than-empty
  (tu/with-terms [CxA p1 X Y]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list p1 X Y) CxA)
    (let [goal (list p1 '?a '?b)]
      (is (= :shape (refusal #(v/query kb goal '(CxTimeFn ?t))))
          "not ground, so it names no context")
      (is (= :shape (refusal #(v/query kb goal '(CxBogusFn ZQ))))
          "no believed (result CxBogusFn context) declares it a context, so it names none either")
      (is (= :shape (refusal #(v/query kb goal [CxA])))
          "and a vector is not a context at all")
      (testing "the shapes a read does take are unaffected"
        (is (seq (v/query kb goal CxA)) "a context")
        (is (seq (v/query kb goal '?home)) "a variable")
        (is (seq (v/query kb goal 'CxInference)) "a query context")))))

(tu/deftest-kb the-network-reads-refuse-a-query-context-rather-than-look-consistent
  (tu/with-terms [CxA]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (doseq [c '[CxEverything CxNothing CxInference]]
      (is (= :unsupported-context (refusal #(v/qualitative-network kb :rcc8 c)))
          (str "qualitative-network at " c))
      (is (= :unsupported-context (refusal #(v/possible-relations kb :rcc8 c 'ZA 'ZB)))
          (str "possible-relations at " c)))
    (testing "a named context still answers"
      (is (true? (:consistent? (v/qualitative-network kb :rcc8 CxA)))))))
