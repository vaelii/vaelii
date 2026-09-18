;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.query-context-test
  "**The three query contexts read; they are not places.**

  `CxEverything`, `CxInference` and `CxNothing` are `Cx…` symbols that name a *way of
  reading* rather than a context (`nm/query-contexts`, docs/contexts.md).  Two things have
  to hold of each, and they pull in opposite directions:

  - the **write** side refuses it, everywhere a context can be named — the assert entry point and
    the `genlCx` slots — so nothing is ever stored in one and nothing wires one into the
    lattice;
  - the **read** side resolves it at the entry point, so the engine below never sees the symbol.

  The second is the one worth testing hardest, and not because it is subtle to implement.
  All three spell like contexts and none is a `?var`, so a symbol that leaked past the
  entry point would be read by every unscoped-path test in the engine as an ordinary *concrete*
  context the taxonomy has never heard of — up-closure itself alone, sees nothing, answers
  **empty**.  No throw, no warning, just a read that quietly stops finding things.  So
  every test here checks a positive: what the reading is *for*, not only what it refuses."
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
;;
;; The default `?ctx` reads "in some context" *per literal*: the join hands every conjunct
;; the same wildcard, so it will join two facts no one context can see.  CxInference is
;; that reading made joint over the derivation.

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
      (testing "and a variable context no longer does: it is the joint reading now"
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
      (testing "plus the reader that answered, under ?ctx"
        (is (= CxBoth (get (first sols) vantage/witness-key))))
      (testing "the witness is the *most general* reader, not every one below it"
        (tu/with-terms [CxDeeper]
          (v/assert kb (list 'genlCx CxDeeper CxBoth) 'CxUniverse)
          (is (= [CxBoth] (mapv #(get % vantage/witness-key)
                                (v/query kb goal 'CxInference)))
              "CxDeeper sees everything CxBoth does and adds no claim"))))))

(tu/deftest-kb cxinference-finds-a-reader-with-no-genlCx-edge-of-its-own
  ;; the seed the lattice cannot supply: an edgeless context is not a node of the
  ;; closure, so `tax/contexts` does not list it — but a fact asserted into it is real
  ;; and that context is its own reader.
  (tu/with-terms [CxLoner p1]
    (v/assert kb (list p1 'Muffet 'Muffet) CxLoner)
    (is (not (contains? (set (v/contexts kb)) CxLoner))
        "precondition: no edge, so not a node of the lattice")
    (let [sols (vec (v/query kb (list p1 '?a '?b) 'CxInference))]
      (is (= 1 (count sols)))
      (is (= CxLoner (get (first sols) vantage/witness-key))))))

;; ---- the two implementations must agree ---------------------------------

(tu/deftest-kb fan-and-post-hoc-answer-alike
  ;; A pure cost decision that must not change the answer set, in the shape
  ;; `res/*hierarchical-retrieval*` already establishes for retrieval.  Inside post-hoc's
  ;; declared domain — stored-fact literals, no rule expansion — the two are compared
  ;; directly, witnesses included.
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
      (is (seq (v/query kb goal 'CxEverything))
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
        "control: a real vantage below the spindle walks the chain in CxOrganism")
    (is (proper-subset? nothing well))))

;; ---- an entry point that cannot resolve one says so ------------------------------

(tu/deftest-kb an-unresolving-entry-point-refuses-rather-than-answering-empty
  ;; The failure mode this whole design guards against: a query context reaching the
  ;; engine is read as an ordinary concrete context the taxonomy never heard of, and the
  ;; read answers empty with no throw and no warning.  Only four entry points resolve one; the
  ;; rest refuse, so an entry point added later inherits the refusal instead of the silence.
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
  ;; `ist` resolution runs first, so the named context wins and there is no query context
  ;; left to refuse — the entry point answers about CxUniverse, as it would have anyway.
  (tu/with-terms [p1 Ind1]
    (v/assert kb (list p1 Ind1) 'CxUniverse)
    (is (some? (v/handle-of kb (list 'ist 'CxUniverse (list p1 Ind1)) 'CxInference)))))

;; ---- post-hoc's ingredients are not only the facts -----------------------

(tu/deftest-kb post-hoc-places-by-the-genl-edge-a-match-subsumed-through
  ;; Retrieval is type-aware, so a matched fact is not the only ingredient of its own
  ;; match: `(sup_t ?x)` is answered by a stored `(sub_t Rex)` over `(genl sub_t sup_t)`,
  ;; and a reader that sees the fact but not that edge does not have the answer.  Placing
  ;; by the fact's context alone reported one from CxA that no reader of the KB has.
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

(tu/deftest-kb post-hoc-will-not-place-an-answer-into-a-context-that-excepts-it
  ;; `matches-visible` at '?ctx runs where the hidden set is empty by construction, so an
  ;; unscoped pass matches a sentex that is excepted from the very context it is about to
  ;; place the answer in.  The forward chainer descends for this (exception-aware
  ;; placements); the backward one has to as well.
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
        ;; two facts in CxA, one naming CxA and one naming CxB.  Asked with the witness
        ;; variable in the argument slot, only the row whose argument agrees with its own
        ;; witness survives — an `assoc` would have overwritten the disagreeing row and
        ;; reported it as though it agreed.
        (tu/with-terms [holdsIn]
          (v/assert kb (list holdsIn CxA) CxA)
          (v/assert kb (list holdsIn CxB) CxA)
          (is (= [{'?home CxA}] (vec (v/query kb (list holdsIn '?home) '?home))))
          (is (= #{CxA} (set (map '?home (v/query kb (list holdsIn '?c) '?home))))
              "control: in an ordinary slot both rows come back, both witnessed by CxA"))))))

;; ---- where the joint reading stops, and why -----------------------------

(tu/deftest-kb a-goal-with-no-monotone-literal-is-asked-of-the-kb
  ;; Fanning over readers is existential over them, and NAF is not monotone: a fact stored,
  ;; believed and visible is `unknown` to any context that cannot see it, and there is
  ;; nearly always such a context.  Fanned, `(unknown X)` would be satisfied by the most
  ;; ignorant reader in the KB and answer true of everything.
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
  ;; No rule needed for this one: the monotone literal decides which readers can answer at
  ;; all, and the `unknown` is then evaluated at those readers and nowhere else.
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

;; ---- what a review found the placement still could not see ---------------
;;
;; Five defects, each one a way the *faster* strategy answered differently from the fan.
;; They are here rather than in the generated differential test because each needs a shape
;; the generator does not reach — a third literal, a merged spelling in the goal, an
;; argument-type declaration — and a property test that cannot produce the shape proves
;; nothing about it.  The generator was widened to reach four of them; these pin all five
;; exactly, so a regression names itself.

(defn- agree?
  "Do the two strategies answer alike?  Returns `[fan post-hoc]` for a readable failure."
  [kb goal ctx]
  [(set (binding [vantage/*strategy* :fan] (v/query kb goal ctx)))
   (set (binding [vantage/*strategy* :post-hoc] (v/query kb goal ctx)))])

(tu/deftest-kb a-join-past-the-budget-falls-to-the-fan-rather-than-throwing
  ;; The bail crossed three nested reduces and was wrapped for two, so the goals-reduce
  ;; took the bare sentinel as its next `sols` and reduced over a keyword.  It needs a
  ;; **third** literal to show: the bail fires at stage two at the earliest, and only a
  ;; literal after it reduces over the sentinel.
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
        (is (seq fan) "and the world really does answer")))))

(tu/deftest-kb the-budget-does-not-charge-for-the-first-literal
  ;; The stage that does no multiplying pays nothing, or a broad single-literal read
  ;; abandons a pass it is winning.
  (tu/with-terms [CxA p1]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (dotimes [i 30] (v/assert kb (list p1 (symbol (str "QC" i)) 'QN) CxA))
    (binding [vantage/*rows-per-reader* 1]
      (let [{:keys [strategy]} (vantage/answers kb [(list p1 '?x '?y)]
                                                #(v/query kb (list p1 '?x '?y) %) {})]
        (is (= :post-hoc strategy)
            "thirty rows in one literal, budget one, and still not abandoned")))))

(tu/deftest-kb a-merge-the-reader-cannot-see-did-not-rewrite-its-goal
  ;; Preparation is per reader: a goal is rewritten by the merges *its* reader sees, and
  ;; post-hoc matches one rewritten globally.  A reader above the `sameAs` never rewrites
  ;; the caller's spelling — so it asks a different question, gets different answers, and
  ;; one unscoped pass cannot have built them.  Post-hoc hands the whole read to the fan.
  (tu/with-terms [CxUp CxLow p1 A B Q]
    (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLow CxUp) 'CxUniverse)
    (v/assert kb (list p1 A Q) CxUp)                ; the fact, above the merge
    (v/assert kb (list 'sameAs A B) CxLow)          ; the merge, below it
    (let [[fan post] (agree? kb (list p1 B '?y) '?ctx)]
      (is (= fan post))
      (is (= [CxLow] (mapv '?ctx fan))
          "only the context that can see the sameAs can ask the question with B in it"))))

(tu/deftest-kb a-literal-that-leaves-the-domain-once-bound-goes-to-the-fan
  ;; `placeable?` sees the conjunction as written, and `applicable?` gates on groundness:
  ;; `(t ?a)` is fact-only and `(t QX)` is not, once the join has bound `?a`.  Post-hoc
  ;; only ever reads the index, so the literal that gained a prover answered with less.
  (tu/with-terms [CxA p1 t1 Seed X Y]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list t1 Seed) CxA)
    (v/assert kb (list 'arg p1 1 t1) CxA)           ; argument type: p1's first arg is a t1
    (v/assert kb (list p1 X Y) CxA)
    (let [[fan post] (agree? kb [(list p1 '?a '?b) (list t1 '?a)] '?ctx)]
      (is (= fan post))
      (is (seq fan) "the argument-type prover answers the second literal, and it counts"))))

(tu/deftest-kb a-blind-read-does-not-leave-its-closure-behind
  ;; `CxEverything` walks the same closure with the belief filter off and moves no clock,
  ;; so without the flag in the cache key the two modes share one entry and whichever ran
  ;; first answers for both — an ordinary read reporting a defeated default.
  (tu/with-terms [CxA before A B C]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'transitive before) 'CxUniverse)
    (v/assert kb (list before A B) CxA {:strength :monotonic})
    (v/assert kb (list before B C) CxA {:strength :default})
    (v/assert kb (list 'not (list before B C)) CxA {:strength :monotonic})
    ;; **The blind read runs first**, and the order is the test.  Warmed the other way the
    ;; ordinary entry is the one already held and the blind read inherits *its* answer —
    ;; wrong in the harmless direction, and it would hide this.
    (let [blind (set (map #(get % '?y) (v/ask kb (list before A '?y) 'CxEverything)))
          reach (set (map #(get % '?y)
                          (:results (v/ask-within kb (list before A '?y) {:max-ms 5000}))))]
      (is (= #{B C} blind) "belief off, so the defeated default is spelled and returned")
      (is (= #{B} reach)
          "and the ordinary read that followed it does not inherit the unbelieved walk"))))

(tu/deftest-kb a-rule-cannot-name-a-query-context-as-its-target
  ;; Every write entry point refuses a query context.  A rule names no target at all: an
  ;; `(ist Cx S)` consequent is refused whatever `Cx` is, so the chainer places only into
  ;; the maximal contexts that see the rule and its facts, and a query context is never one.
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
  ;; `sentexes-matching` promises a seq that fetches what it is asked for, and making the
  ;; default context the joint reading turned it into a realized vector — every reader asked
  ;; before the caller sees element one.  There is no witness to maximize on a records read,
  ;; so unlike `fan` nothing here has to see every reader before it can answer at all.
  (tu/with-terms [CxA p1]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (dotimes [i 5] (v/assert kb (list p1 (symbol (str "QL" i)) 'QLK) CxA))
    (is (instance? clojure.lang.LazySeq (v/sentexes-matching kb (list p1 '?a '?b)))
        "the default context")
    (is (instance? clojure.lang.LazySeq (v/sentexes-matching kb (list p1 '?a '?b) CxA))
        "and a named one, which never stopped being lazy")
    (testing "and it is still the fan, not the wildcard it replaced"
      ;; the difference the fan exists for: a sentex excepted from the only context that
      ;; could see it is visible to an unscoped read and to no vantage at all
      (let [h (v/handle-of kb (list p1 'QL0 'QLK) CxA)]
        (v/assert kb (list 'except (list 'sentexHandle h)) CxA)
        (is (not-any? #(= h (:id %)) (v/sentexes-matching kb (list p1 '?a '?b)))
            "no reader sees it, so the read does not report it")))))

(tu/deftest-kb a-proof-answer-carries-its-witness-among-the-bindings
  ;; `:proof?` answers `{:bindings … :proof …}`, so a witness assoc'ed at the top level is
  ;; invisible to `(:bindings answer)` — and the unify check that stops an already-bound
  ;; `?ctx` being overwritten was reading a key that is never there.
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
  ;; Retrieval unifies the sentex's context slot against `?ctx`, so a goal variable spelled
  ;; the same way came back bound to the **context** — `(p ?ctx ?b)` answering `{?ctx CxA,
  ;; ?b Y}` with the first argument's binding silently replaced.  Naming the context
  ;; variable something else is not a workaround: the marker is fixed, so `?home` as the
  ;; context still leaves `?ctx` in the goal captured.
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
      (testing "and a named context answers it, correctly, as it always did"
        (is (= [{'?ctx X '?b Y}] (vec (v/query kb goal CxA)))
            "?ctx binds the argument it stands in, there being no marker to collide with")))
    (testing "a goal that does not spell it is untouched"
      (is (= [{'?a X '?b Y '?ctx CxA}] (vec (v/query kb (list p1 '?a '?b))))))))

(tu/deftest-kb a-context-that-names-no-context-is-refused-rather-than-empty
  ;; A compound context is admitted only when it reifies.  Unrefused, one that does not
  ;; reaches the engine as a context nothing is asserted in and the read answers empty —
  ;; indistinguishable from a true negative, which is the failure this entry point exists to stop.
  (tu/with-terms [CxA p1 X Y]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list p1 X Y) CxA)
    (let [goal (list p1 '?a '?b)]
      (is (= :shape (refusal #(v/query kb goal '(CxTimeFn ?t))))
          "not ground, so it names no context")
      (is (= :shape (refusal #(v/query kb goal '(CxBogusFn ZQ))))
          "not a declared context-denoting function, so it names none either")
      (is (= :shape (refusal #(v/query kb goal [CxA])))
          "and a vector is not a context at all")
      (testing "the shapes a read does take are unaffected"
        (is (seq (v/query kb goal CxA)) "a context")
        (is (seq (v/query kb goal '?home)) "a variable")
        (is (seq (v/query kb goal 'CxInference)) "a query context")))))

(tu/deftest-kb the-network-reads-refuse-a-query-context-rather-than-look-consistent
  ;; The worst shape of the silent-empty failure: these answer a *structure*, so a query
  ;; context came back `{:nodes [] :consistent? true}` — an unsatisfiable KB and a way of
  ;; reading rendered identically, and the reassuring one is what you would act on.
  (tu/with-terms [CxA]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (doseq [c '[CxEverything CxNothing CxInference]]
      (is (= :unsupported-context (refusal #(v/qualitative-network kb :rcc8 c)))
          (str "qualitative-network at " c))
      (is (= :unsupported-context (refusal #(v/possible-relations kb :rcc8 c 'ZA 'ZB)))
          (str "possible-relations at " c)))
    (testing "a named context still answers"
      (is (true? (:consistent? (v/qualitative-network kb :rcc8 CxA)))))))
