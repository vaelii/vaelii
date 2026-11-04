;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-gnarly-test
  "Gnarly `except` tests: cross-context exceptions, cross-context meta-exceptions,
  deep exception chains, excepting special-predicate sentexes, and the
  special-predicate sweep that verifies `except` blocks or does not block the
  cached behaviour behind each interpreted functor."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- helpers ------------------------------------------------------------

;; ---- 1. cross-context except --------------------------------------------

(tu/deftest-kb cross-context-except
  ;; Assert a fact in context A, except it from context B (a descendant of A via
  ;; genlCx).  The except hides the fact in B and B's descendants but leaves it
  ;; visible in A and A's siblings.
  (tu/with-terms [shiny gold CxTop CxMid CxLeaf CxSibling]
    (v/assert kb (list 'genlCx CxTop 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxMid CxTop) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxLeaf CxMid) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxSibling CxTop) 'CxUniverse {:strength :monotonic})

    (let [h (v/assert kb (list shiny gold) CxTop {:strength :monotonic})]
      (testing "visible everywhere before any except"
        (is (v/ask? kb (list shiny gold) CxTop))
        (is (v/ask? kb (list shiny gold) CxMid))
        (is (v/ask? kb (list shiny gold) CxLeaf))
        (is (v/ask? kb (list shiny gold) CxSibling)))

      (let [eh (v/assert kb (list 'except (sx/sentex-handle h)) CxMid {:strength :monotonic})]
        (testing "hidden in CxMid and its descendant CxLeaf"
          (is (not (v/ask? kb (list shiny gold) CxMid)))
          (is (not (v/ask? kb (list shiny gold) CxLeaf))))
        (testing "visible in CxTop (the ancestor) and CxSibling (does not see CxMid)"
          (is (v/ask? kb (list shiny gold) CxTop))
          (is (v/ask? kb (list shiny gold) CxSibling)))
        (testing "retract the except — visibility returns everywhere"
          (v/retract! kb eh)
          (is (v/ask? kb (list shiny gold) CxMid))
          (is (v/ask? kb (list shiny gold) CxLeaf)))))))

;; ---- 2. cross-context meta-except ---------------------------------------

(tu/deftest-kb cross-context-meta-except
  ;; Fact in CxTop, excepted in CxMid, meta-excepted in CxLeaf.  The meta-except
  ;; restores visibility only from CxLeaf's vantage — CxMid still sees the except.
  (tu/with-terms [bright gem CxTop CxMid CxLeaf]
    (v/assert kb (list 'genlCx CxTop 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxMid CxTop) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxLeaf CxMid) 'CxUniverse {:strength :monotonic})

    (let [h (v/assert kb (list bright gem) CxTop {:strength :monotonic})]
      (let [e (v/assert kb (list 'except (sx/sentex-handle h)) CxMid {:strength :monotonic})]
        (testing "fact hidden in CxMid and CxLeaf"
          (is (not (v/ask? kb (list bright gem) CxMid)))
          (is (not (v/ask? kb (list bright gem) CxLeaf))))

        (let [m (v/assert kb (list 'except (sx/sentex-handle e)) CxLeaf {:strength :monotonic})]
          (testing "meta-except in CxLeaf restores visibility there"
            (is (v/ask? kb (list bright gem) CxLeaf)
                "the meta-except suppresses E's effect from CxLeaf's vantage"))
          (testing "CxMid still sees the except — the meta-except is below it"
            (is (not (v/ask? kb (list bright gem) CxMid))
                "the except is asserted here and no meta-except is visible"))
          (testing "CxTop is untouched throughout"
            (is (v/ask? kb (list bright gem) CxTop)))
          (testing "retracting the meta-except re-hides in CxLeaf"
            (v/retract! kb m)
            (is (not (v/ask? kb (list bright gem) CxLeaf)))))
        (v/retract! kb e)))))

(tu/deftest-kb conjunctive-meta-excepts-compose-only-at-joint-reader
  ;; P and Q are each hidden at the base. CxLeft restores only P; CxRight restores
  ;; only Q. A static closure per context cannot answer this correctly: CxBottom may
  ;; prove the conjunction's consequence only while it inherits both restoration
  ;; ancestor sets at once, and loses it again when either inheritance edge is withdrawn.
  (tu/with-terms [p q r Item CxBase CxLeft CxRight CxBottom]
    (doseq [[sub super] [[CxBase 'CxWell]
                         [CxLeft CxBase]
                         [CxRight CxBase]
                         [CxBottom CxBase]]]
      (v/assert kb (list 'genlCx sub super) 'CxUniverse {:strength :monotonic}))
    (v/assert-rule kb [(list p Item) (list q Item)] (list r Item) CxBase
                   {:direction :forward :strength :monotonic})
    (let [ph (v/assert kb (list p Item) CxBase {:strength :monotonic})
          qh (v/assert kb (list q Item) CxBase {:strength :monotonic})
          pe (v/assert kb (list 'except (sx/sentex-handle ph)) CxBase
                       {:strength :monotonic})
          qe (v/assert kb (list 'except (sx/sentex-handle qh)) CxBase
                       {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle pe)) CxLeft
                {:strength :monotonic})
      (v/assert kb (list 'except (sx/sentex-handle qe)) CxRight
                {:strength :monotonic})
      (testing "neither branch alone restores the conjunction"
        (let [left-edge (v/assert kb (list 'genlCx CxBottom CxLeft) 'CxUniverse
                                  {:strength :monotonic})]
          (is (v/ask? kb (list p Item) CxBottom))
          (is (not (v/ask? kb (list q Item) CxBottom)))
          (is (not (v/ask? kb (list r Item) CxBottom)))
          (v/retract! kb left-edge))
        (let [right-edge (v/assert kb (list 'genlCx CxBottom CxRight) 'CxUniverse
                                   {:strength :monotonic})]
          (is (not (v/ask? kb (list p Item) CxBottom)))
          (is (v/ask? kb (list q Item) CxBottom))
          (is (not (v/ask? kb (list r Item) CxBottom)))
          (v/retract! kb right-edge)))
      (testing "the joint reader proves R, and either missing edge withdraws it"
        (let [left-edge  (v/assert kb (list 'genlCx CxBottom CxLeft) 'CxUniverse
                                   {:strength :monotonic})
              right-edge (v/assert kb (list 'genlCx CxBottom CxRight) 'CxUniverse
                                   {:strength :monotonic})]
          (is (v/ask? kb (list p Item) CxBottom))
          (is (v/ask? kb (list q Item) CxBottom))
          (is (true? (boolean (v/ask? kb (list r Item) CxBottom))))
          (v/retract! kb left-edge)
          (is (not (v/ask? kb (list r Item) CxBottom)))
          (v/assert kb (list 'genlCx CxBottom CxLeft) 'CxUniverse
                    {:strength :monotonic})
          (is (true? (boolean (v/ask? kb (list r Item) CxBottom))))
          (v/retract! kb right-edge)
          (is (not (v/ask? kb (list r Item) CxBottom))))))))

(defn- late-edge-reading
  "CxHide and CxSub each see CxTop, which holds P = (pp Rex) and the forward rule
  (pp ?x) ∧ (ss ?x) ⇒ (qq ?x).  Assert P, then the steps `ops` in order: the edge
  `(genlCx CxSub CxHide)`, `(except P)` in CxHide, the rule, and (ss Rex) in CxSub.  Read
  [CxSub stores (qq Rex), CxSub believes it] with the edge in and again after retracting
  it, then retract the rest."
  [kb ops]
  (tu/with-terms [pp ss qq Rex CxTop CxHide CxSub]
    (let [M       {:strength :monotonic}
          hs      (volatile! (mapv #(v/assert kb (list 'genlCx % CxTop) 'CxUniverse M) [CxHide CxSub]))
          p       (v/assert kb (list pp Rex) CxTop M)
          edge    (volatile! nil)
          reading (fn [] [(boolean (some #(= (list qq Rex) (v/sentence-of %))
                                         (v/sentexes-in-context kb CxSub)))
                          (boolean (v/ask? kb (list qq Rex) CxSub))])]
      (vswap! hs conj p)
      (doseq [op ops]
        (vswap! hs conj
                (case op
                  :edge   (vreset! edge (v/assert kb (list 'genlCx CxSub CxHide) 'CxUniverse M))
                  :except (v/assert kb (list 'except (sx/sentex-handle p)) CxHide M)
                  :rule   (v/assert-rule kb [(list pp '?x) (list ss '?x)] (list qq '?x) CxTop
                                         {:direction :forward :strength :monotonic})
                  :fact   (v/assert kb (list ss Rex) CxSub M))))
      (let [with (reading)]
        (v/retract! kb @edge)
        (let [without (reading)]
          (doseq [h (rseq @hs)] (when (v/sentex kb h) (v/retract! kb h)))
          [with without])))))

(tu/deftest-kb a-late-genlCx-edge-sweeps-what-the-except-it-reveals-blocks-and-its-retraction-restores-it
  ;; The firing is placed at CxSub, the common descendant of CxTop and CxSub.  The edge
  ;; shows CxSub the except of P, so the firing is swept there whether the edge arrived
  ;; before the except, the rule or the fact, or after them
  ;; (`special/recheck-except-ancestors`); retracting the edge places it again.
  (is (= #{[[false false] [true true]]}
         (into #{} (map #(late-edge-reading kb %)) (oi/permutations [:edge :except :rule :fact])))))

(defn- excepted-edge-reading
  "CxQ, CxB and CxS each see CxUniverse.  E1 = (genlCx CxQ CxB), the forward rule
  (genlCx CxQ ?b) ⇒ (genlCx CxS ?b), which derives E2 = (genlCx CxS CxB), an except of E1
  in CxS, (pp Xx) in CxB, (ss Xx) in CxS and the forward rule (pp ?x) ∧ (ss ?x) ⇒ (qq ?x)
  in CxB arrive in `order`; `direct?` also asserts E2 first.  Reads [CxS sees CxB under
  the belief reading, under the network reading, (pp Xx) asked at CxS, (qq Xx) stored at
  CxS, (qq Xx) asked at CxS] after the six writes and again after retracting the except,
  then retracts the rest."
  [kb order direct?]
  (tu/with-terms [pp ss qq Xx CxQ CxB CxS]
    (let [M       {:strength :monotonic}
          hs      (volatile! (mapv #(v/assert kb (list 'genlCx % 'CxUniverse) 'CxUniverse M) [CxQ CxB CxS]))
          e1      (volatile! nil)
          ex      (volatile! nil)
          reading (fn []
                    (let [up #(binding [tax/*network-belief* %]
                                (contains? (tax/context-up (reasoning/taxonomy kb) CxS) CxB))]
                      [(up false) (up true)
                       (boolean (v/ask? kb (list pp Xx) CxS))
                       (boolean (some #(= (list qq Xx) (v/sentence-of %)) (v/sentexes-in-context kb CxS)))
                       (boolean (v/ask? kb (list qq Xx) CxS))]))]
      (when direct? (vswap! hs conj (v/assert kb (list 'genlCx CxS CxB) 'CxUniverse M)))
      (doseq [op order]
        (vswap! hs conj
                (case op
                  :edge    (vreset! e1 (v/assert kb (list 'genlCx CxQ CxB) 'CxUniverse M))
                  :cx-rule (v/assert-rule kb [(list 'genlCx CxQ '?b)] (list 'genlCx CxS '?b) 'CxUniverse
                                          {:direction :forward :strength :monotonic})
                  :except  (vreset! ex (v/assert kb (list 'except (sx/sentex-handle @e1)) CxS M))
                  :pp      (v/assert kb (list pp Xx) CxB M)
                  :ss      (v/assert kb (list ss Xx) CxS M)
                  :rule    (v/assert-rule kb [(list pp '?x) (list ss '?x)] (list qq '?x) CxB
                                          {:direction :forward :strength :monotonic}))))
      (let [with (reading)]
        (v/retract! kb @ex)
        (let [without (reading)]
          (doseq [h (rseq @hs)] (when (and (not= h @ex) (v/sentex kb h)) (v/retract! kb h)))
          [with without])))))

(defn- excepted-edge-orders
  "Every order of the six writes in which the except follows the edge it names."
  []
  (remove #(< (.indexOf ^java.util.List % :except) (.indexOf ^java.util.List % :edge))
          (oi/permutations [:edge :cx-rule :except :pp :ss :rule])))

(defn- excepted-edge-readings
  "The distinct readings over `orders`, without and with E2 asserted directly."
  [kb orders]
  (into #{} (for [direct? [false true], order orders] [direct? (excepted-edge-reading kb order direct?)])))

(def ^:private excepted-edge-expected
  ;; E2's one justification rests on E1, which the except hides at CxS, so CxS does not
  ;; see CxB under either reading: (pp Xx) is not asked true there and the firing that
  ;; needs both antecedents is not placed there.  Retracting the except shows CxB, and
  ;; (qq Xx) is stored and believed at CxS.  With E2 also asserted directly, its premise
  ;; justification rests on no excepted edge and CxS sees CxB throughout.
  #{[false [[false false false false false] [true true true true true]]]
    [true [[true true true true true] [true true true true true]]]})

(tu/deftest-kb a-genlCx-edge-resting-on-an-excepted-genlCx-edge-leaves-the-excepting-reader-for-reads-and-chain
  ;; A sample of 15 of the 360 orders; the ^:slow twin below reads every one.
  (is (= excepted-edge-expected (excepted-edge-readings kb (take-nth 24 (excepted-edge-orders))))))

(tu/deftest-kb ^:slow a-genlCx-edge-resting-on-an-excepted-genlCx-edge-leaves-the-excepting-reader-in-every-order
  (is (= excepted-edge-expected (excepted-edge-readings kb (excepted-edge-orders)))))

(defn- hidden-super-except-reading
  "CxTop and CxSub see CxUniverse; E2 = (genlCx CxSup CxTop) with an except of E2 stated in
  CxSup.  (ff Aa) in CxSub, the forward rule (ff ?x) ⇒ (gg ?x) in CxSub, an except of
  (ff Aa) stated in CxTop and E = (genlCx CxSub CxSup) arrive in `order`.  Reads [(gg Aa)
  stored at CxSub, (gg Aa) asked at CxSub, (ff Aa) asked at CxSub] after the writes and
  again after retracting E, then retracts the rest."
  [kb order]
  (tu/with-terms [ff gg Aa CxTop CxSup CxSub]
    (let [M       {:strength :monotonic}
          hs      (volatile! (mapv #(v/assert kb (list 'genlCx % 'CxUniverse) 'CxUniverse M) [CxTop CxSub]))
          e2      (v/assert kb (list 'genlCx CxSup CxTop) 'CxUniverse M)
          _       (vswap! hs conj e2 (v/assert kb (list 'except (sx/sentex-handle e2)) CxSup M))
          f       (volatile! nil)
          e       (volatile! nil)
          reading (fn []
                    [(boolean (some #(= (list gg Aa) (v/sentence-of %)) (v/sentexes-in-context kb CxSub)))
                     (boolean (v/ask? kb (list gg Aa) CxSub))
                     (boolean (v/ask? kb (list ff Aa) CxSub))])]
      (doseq [op order]
        (vswap! hs conj
                (case op
                  :edge (vreset! e (v/assert kb (list 'genlCx CxSub CxSup) 'CxUniverse M))
                  :fact (vreset! f (v/assert kb (list ff Aa) CxSub M))
                  :exf  (v/assert kb (list 'except (sx/sentex-handle @f)) CxTop M)
                  :rule (v/assert-rule kb [(list ff '?x)] (list gg '?x) CxSub
                                       {:direction :forward :strength :monotonic}))))
      (let [with (reading)]
        (v/retract! kb @e)
        (let [without (reading)]
          (doseq [h (rseq @hs)] (when (and (not= h @e) (v/sentex kb h)) (v/retract! kb h)))
          [with without])))))

(tu/deftest-kb an-except-in-a-context-the-sub-reaches-past-a-hidden-edge-is-rechecked-when-the-edge-arrives
  ;; CxSup does not see CxTop (its edge is excepted there), but CxSub's raw ancestor set
  ;; holds CxTop once E arrives, and the excepts in force are read off the raw set: the
  ;; except of (ff Aa) hides the fact and sweeps the firing at CxSub in every order, and
  ;; retracting E gives both back.
  (is (= #{[[false false false] [true true true]]}
         (into #{} (map #(hidden-super-except-reading kb %))
               (remove #(< (.indexOf ^java.util.List % :exf) (.indexOf ^java.util.List % :fact))
                       (oi/permutations [:edge :fact :exf :rule]))))))

(defn- reader-below-sub-reading
  "CxY, CxSub under CxUniverse; CxSup under CxY; CxR under CxSub; E' = (genlCx CxSub CxY)
  with an except of E' stated in CxR.  (pp Xx) in CxY, (ss Xx) in CxR, the forward rule
  (pp ?x) ∧ (ss ?x) ⇒ (qq ?x) in CxR and E = (genlCx CxSub CxSup) arrive in `order`.  Reads
  [CxR sees CxY, (pp Xx) asked at CxR, (qq Xx) stored at CxR, (qq Xx) asked at CxR] after
  the writes and again after retracting E, then retracts the rest."
  [kb order]
  (tu/with-terms [pp ss qq Xx CxY CxSub CxR CxSup]
    (let [M       {:strength :monotonic}
          hs      (volatile! (mapv #(v/assert kb (apply list 'genlCx %) 'CxUniverse M)
                                   [[CxY 'CxUniverse] [CxSub 'CxUniverse] [CxSup CxY] [CxR CxSub]]))
          esy     (v/assert kb (list 'genlCx CxSub CxY) 'CxUniverse M)
          _       (vswap! hs conj esy (v/assert kb (list 'except (sx/sentex-handle esy)) CxR M))
          e       (volatile! nil)
          reading (fn []
                    [(contains? (set (tax/context-up (reasoning/taxonomy kb) CxR)) CxY)
                     (boolean (v/ask? kb (list pp Xx) CxR))
                     (boolean (some #(= (list qq Xx) (v/sentence-of %)) (v/sentexes-in-context kb CxR)))
                     (boolean (v/ask? kb (list qq Xx) CxR))])]
      (doseq [op order]
        (vswap! hs conj
                (case op
                  :edge (vreset! e (v/assert kb (list 'genlCx CxSub CxSup) 'CxUniverse M))
                  :pp   (v/assert kb (list pp Xx) CxY M)
                  :ss   (v/assert kb (list ss Xx) CxR M)
                  :rule (v/assert-rule kb [(list pp '?x) (list ss '?x)] (list qq '?x) CxR
                                       {:direction :forward :strength :monotonic}))))
      (let [with (reading)]
        (v/retract! kb @e)
        (let [without (reading)]
          (doseq [h (rseq @hs)] (when (and (not= h @e) (v/sentex kb h)) (v/retract! kb h)))
          [with without])))))

(tu/deftest-kb a-genlCx-edge-shows-a-reader-below-its-sub-what-the-sub-already-saw
  ;; CxSub sees CxY over E' before E arrives; CxR does not, because the except of E' is
  ;; stated there.  E shows CxR CxY through CxSup, so the rule at CxR fires over (pp Xx) in
  ;; every order, and retracting E hides CxY from CxR again.
  (is (= #{[[true true true true] [false false false false]]}
         (into #{} (map #(reader-below-sub-reading kb %)) (oi/permutations [:edge :pp :ss :rule])))))

(defn- context-move-row
  "Asserts the `genlCx` edges `[sub super]` of `edges` and an except of each edge `excepted`
  maps to its stating context, then reads, per reader under `sub`, the ancestor sets before
  and after `(genlCx sub super)` = `edge`, effective (`tax/context-up`) and raw
  (`tax/context-up-global`).  Returns [the per-reader diffs unioned, effective and raw,
  `special/context-move` after the edge arrives, and after it is retracted]."
  [kb edges excepted [sub super]]
  (let [M     {:strength :monotonic}
        tx    (reasoning/taxonomy kb)
        hs    (volatile! [])
        by    (into {} (map (fn [e] (let [h (v/assert kb (apply list 'genlCx e) 'CxUniverse M)]
                                      (vswap! hs conj h)
                                      [e h])))
                    edges)
        _     (doseq [[e c] excepted]
                (vswap! hs conj (v/assert kb (list 'except (sx/sentex-handle (by e))) c M)))
        ancestor-sets (fn [] (into {} (map (fn [d] [d [(set (tax/context-up tx d)) (set (tax/context-up-global tx d))]]))
                                   (tax/context-down-global tx sub)))
        before (ancestor-sets)
        eh     (v/assert kb (list 'genlCx sub super) 'CxUniverse M)
        after  (ancestor-sets)
        diff   (fn [i] (into #{} (mapcat (fn [[d v]] (remove (nth (get before d) i #{}) (nth v i)))) after))
        shown  (special/context-move kb sub super)
        _      (v/retract! kb eh)
        hidden (special/context-move kb sub super)]
    (doseq [h (rseq @hs)] (when (v/sentex kb h) (v/retract! kb h)))
    [(diff 0) (diff 1) shown hidden]))

(tu/deftest-kb an-edge-to-cxuniverse-moves-no-context-in-either-direction
  (tu/with-terms [CxLeaf]
    (let [h (v/assert kb (list 'genlCx CxLeaf 'CxUniverse) 'CxUniverse)]
      (is (= [#{} #{}] ((juxt :raw :moved) (special/context-move kb CxLeaf 'CxUniverse))))
      (v/retract! kb h)
      (is (= [#{} #{}] ((juxt :raw :moved) (special/context-move kb CxLeaf 'CxUniverse)))))))

(tu/deftest-kb context-move-names-what-each-reader-gains-through-the-edge
  ;; Each row: the effective `:shown` equals the per-reader diff of `context-up` and the
  ;; raw stratum the diff of `context-up-global`.  After the retraction `:hidden` holds at
  ;; least the diff: an except reached only through the edge leaves force with it, and
  ;; the except family re-checks what it hid (`recheck-except-ancestors`).
  (doseq [row [:plain :seen-elsewhere :reader-below-sub :hidden-super :distant-except]]
    (tu/with-terms [CxA CxB CxC CxD CxR]
      (let [[edges excepted edge]
            (case row
              ;; CxA, CxB under CxUniverse, CxC under CxA
              :plain            [[[CxA 'CxUniverse] [CxB 'CxUniverse] [CxC CxA]] {} [CxA CxB]]
              ;; CxA sees CxD already, through CxC
              :seen-elsewhere   [[[CxA CxC] [CxC CxD] [CxB CxD] [CxD 'CxUniverse]] {} [CxA CxB]]
              ;; W2: CxR under CxA does not see CxD, whose edge from CxA is excepted at CxR
              :reader-below-sub [[[CxD 'CxUniverse] [CxA 'CxUniverse] [CxB CxD] [CxR CxA] [CxA CxD]]
                                 {[CxA CxD] CxR} [CxA CxB]]
              ;; W1: CxB does not see CxD, its edge excepted at CxB
              :hidden-super     [[[CxD 'CxUniverse] [CxA 'CxUniverse] [CxB CxD]]
                                 {[CxB CxD] CxB} [CxA CxB]]
              ;; SYMPTOMS 3: an except of a genlCx edge no reader under CxA reaches
              :distant-except   [[[CxA 'CxUniverse] [CxB 'CxUniverse] [CxC 'CxUniverse] [CxD CxC]]
                                 {[CxD CxC] CxD} [CxA CxB]])
            [eff raw shown hidden] (context-move-row kb edges excepted edge)]
        (is (= [eff raw] [(:shown shown) (:raw shown)]) (str row " shown"))
        (is (= #{} (:hidden shown)) (str row))
        (is (every? (:hidden hidden) eff) (str row " hidden"))
        (is (= raw (:raw hidden)) (str row " raw hidden"))))))

;; ---- 3. chain of 212 excepts --------------------------------------------

(tu/deftest-kb chain-of-212-excepts
  ;; H0 hidden by E1, E1 hidden by E2, ..., E211 hidden by E212.
  ;; At depth N (1-based): odd N -> H0 is visible (the except hiding it is itself
  ;; hidden), even N -> H0 is hidden.  212 is even, so H0 should be hidden.
  ;; Then retract E212 (the deepest) and verify the cascade recalculates.
  (tu/with-terms [shiny gold CxChain]
    (v/assert kb (list 'genlCx CxChain 'CxWell) 'CxUniverse {:strength :monotonic})

    (let [h0 (v/assert kb (list shiny gold) CxChain {:strength :monotonic})]
      (testing "H0 is visible before any except"
        (is (v/ask? kb (list shiny gold) CxChain)))

      ;; Build chain: E1 excepts H0, E2 excepts E1, ..., E212 excepts E211
      (let [chain (loop [i 1, prev-handle h0, acc []]
                    (if (> i 212)
                      acc
                      (let [eh (v/assert kb (list 'except (sx/sentex-handle prev-handle))
                                         CxChain {:strength :monotonic})]
                        (recur (inc i) eh (conj acc eh)))))]

        (testing "with 212 layers (even), H0 is visible"
          ;; E1 hides H0.  E2 hides E1 -> H0 visible.  E3 hides E2 -> E1 active -> H0 hidden.
          ;; Cascade from the deepest: E212 is active (nothing hides it), E211 is
          ;; suppressed, E210 active, ..., E1: distance from E212 is 211 (odd) -> suppressed.
          ;; With E1 suppressed, H0 is NOT excepted.
          ;; Pattern: odd layer count = H0 hidden, even layer count = H0 visible.
          (is (v/ask? kb (list shiny gold) CxChain)
              "212 layers (even) should leave H0 visible"))

        (testing "retract the deepest (E212) — cascade recalculates to 211 (odd)"
          (v/retract! kb (peek chain))
          ;; 211 layers (odd): E211 is now the deepest and active, E210 suppressed, ...,
          ;; E1: distance from E211 is 210 (even) -> active.  E1 active -> H0 hidden.
          (is (not (v/ask? kb (list shiny gold) CxChain))
              "211 layers (odd) should leave H0 hidden"))

        (testing "retract the next deepest (E211) — back to 210 (even)"
          (v/retract! kb (peek (pop chain)))
          (is (v/ask? kb (list shiny gold) CxChain)
              "210 layers (even) should leave H0 visible"))

        ;; Clean up the rest of the chain by retracting from deepest to shallowest
        (doseq [eh (reverse (pop (pop chain)))]
          (v/retract! kb eh))))))

;; ---- 4. except a genlCx link -------------------------------------------

(tu/deftest-kb except-genlCx-link
  ;; A genlCx declaration is forced into CxUniverse, but its effect can be excepted
  ;; from a concrete reader.  From that reader's ancestor set it behaves as if retracted;
  ;; an ancestor that cannot see the exception keeps the edge.  The ordinary genl
  ;; test below asserts the degenerate declaration-and-except-in-one-context case.
  (tu/with-terms [shiny gold CxChild CxParent]
    (v/assert kb (list 'genlCx CxParent 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [edge-h (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse {:strength :monotonic})]
      (v/assert kb (list shiny gold) CxParent {:strength :monotonic})

      (testing "CxChild sees CxParent's facts before any except"
        (is (v/ask? kb (list shiny gold) CxChild)))

      (let [eh (v/assert kb (list 'except (sx/sentex-handle edge-h))
                         CxChild {:strength :monotonic})]
        (testing "excepting a genlCx link removes its interpreted closure"
          (is (not (v/ask? kb (list shiny gold) CxChild)))
          (is (v/ask? kb (list shiny gold) CxParent)
              "the reader-scoped exception does not retract the edge globally"))
        (testing "retract the except — the genlCx link returns"
          (v/retract! kb eh)
          (is (v/ask? kb (list shiny gold) CxChild)))))))

(defn- counting-filtered-walks
  "Run `f` with `tax/reachable-filtered?` counted; returns `[result calls]`.  A plain
  fn, so `with-redefs` intercepts the call `sees?` makes."
  [f]
  (let [n    (atom 0)
        orig @#'tax/reachable-filtered?]
    (with-redefs [tax/reachable-filtered? (fn [& args] (swap! n inc) (apply orig args))]
      (let [r (f)] [r @n]))))

(tu/deftest-kb context-down-follows-a-genlCx-except-and-is-memoized-between-changes
  ;; `context-down` has no single reader, so under an except that reaches a `genlCx`
  ;; supporter it filters every candidate by that candidate's own forward walk.  That
  ;; answer is memoized per context and retired by exactly the events that can move it:
  ;; the except arriving, and the except leaving.
  (tu/with-terms [CxChild CxParent CxOther]
    (let [tx     (reasoning/taxonomy kb)
          down   #(tax/context-down tx CxParent)]
      (v/assert kb (list 'genlCx CxParent 'CxWell) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genlCx CxOther CxParent) 'CxUniverse {:strength :monotonic})
      (let [edge-h (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse
                             {:strength :monotonic})]
        (is (= #{CxParent CxChild CxOther} (down)) "both children inherit")
        (let [eh (v/assert kb (list 'except (sx/sentex-handle edge-h)) CxChild
                           {:strength :monotonic})]
          (testing "the except arriving changes the answer"
            (is (= #{CxParent CxOther} (down)) "the reader that hides the edge drops out"))
          (testing "and the second read is a memo hit — no filtered walk"
            (let [[r calls] (counting-filtered-walks down)]
              (is (= #{CxParent CxOther} r))
              (is (zero? calls))))
          (testing "the except leaving restores the answer"
            (v/retract! kb eh)
            (is (= #{CxParent CxChild CxOther} (down)))))))))

(tu/deftest-kb context-down-under-a-genlCx-except-is-held-per-reading
  ;; A belief search (`tax/*search*` :belief) reads no except, so CxChild sees CxParent
  ;; there and not under the visibility or the network reading.  In every order of the
  ;; three reads, each answers what a fresh memo answers.
  (doseq [order (oi/permutations [:plain :network :search])]
    (tu/with-terms [CxChild CxParent CxOther]
      (let [M     {:strength :monotonic}
            in    {:plain {} :network {#'tax/*network-belief* true} :search {#'tax/*search* :belief}}
            down  (fn [r tx] (with-bindings (in r) (tax/context-down tx CxParent)))]
        (v/assert kb (list 'genlCx CxParent 'CxWell) 'CxUniverse M)
        (v/assert kb (list 'genlCx CxOther CxParent) 'CxUniverse M)
        (v/assert kb (list 'except (sx/sentex-handle (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse M)))
                  CxChild M)
        (testing (vec order)
          (is (= {:plain #{CxParent CxOther} :network #{CxParent CxOther}
                  :search #{CxParent CxChild CxOther}}
                 (into {} (map (fn [r] [r (down r (reasoning/taxonomy kb))])) order)))
          (is (= {:plain #{CxParent CxOther} :network #{CxParent CxOther}
                  :search #{CxParent CxChild CxOther}}
                 (into {} (map (fn [r] [r (down r (reasoning/taxonomy kb))])) order))
              "read again from the memo"))))))

(tu/deftest-kb an-except-on-an-unrelated-fact-leaves-context-down-on-the-raw-path
  ;; The whole-KB presence check says an except exists; the relation check says whether
  ;; it reaches a `genlCx` supporter.  One on an ordinary fact reaches none, so no
  ;; candidate pays a filtered walk — the answer is the raw closure, which is the same set.
  (tu/with-terms [shiny gold CxChild CxParent]
    (let [tx (reasoning/taxonomy kb)]
      (v/assert kb (list 'genlCx CxParent 'CxWell) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse {:strength :monotonic})
      (let [h  (v/assert kb (list shiny gold) CxParent {:strength :monotonic})
            eh (v/assert kb (list 'except (sx/sentex-handle h)) CxChild {:strength :monotonic})]
        (is (not (v/ask? kb (list shiny gold) CxChild)) "the fact is hidden")
        (let [[r calls] (counting-filtered-walks #(tax/context-down tx CxParent))]
          (is (= #{CxParent CxChild} r))
          (is (zero? calls) "no genlCx supporter is targeted, so nothing is filtered"))
        (let [[r calls] (counting-filtered-walks #(tax/sees? tx CxChild CxParent))]
          (is (true? r))
          (is (zero? calls) "and a single probe takes the pruned unfiltered walk"))
        (v/retract! kb eh)))))

(tu/deftest-kb the-nearest-context-neighbours-follow-a-genlCx-except
  ;; `CxLeaf` reaches `CxTop` through `CxMid` and by an edge of its own.  The nearest
  ;; parents of a context are read as that context reads its ancestor set
  ;; (`context-up`), and a context is a nearest child of the contexts its own read names
  ;; as nearest parents, which is how `context-down` reads each candidate.
  (let [M {:strength :monotonic}]
    (testing "an except on the nearer edge, stated in the context under the edge"
      (tu/with-terms [CxTop CxMid CxLeaf]
        (let [tx (reasoning/taxonomy kb)]
          (v/assert kb (list 'genlCx CxTop 'CxWell) 'CxUniverse M)
          (v/assert kb (list 'genlCx CxMid CxTop) 'CxUniverse M)
          (v/assert kb (list 'genlCx CxLeaf CxTop) 'CxUniverse M)
          (let [near-h (v/assert kb (list 'genlCx CxLeaf CxMid) 'CxUniverse M)]
            (is (= #{CxMid} (tax/min-context-parents tx CxLeaf)))
            (is (= #{CxMid} (tax/max-context-children tx CxTop)))
            (is (= #{CxLeaf} (tax/max-context-children tx CxMid)))
            (let [eh (v/assert kb (list 'except (sx/sentex-handle near-h)) CxLeaf M)]
              (is (not (contains? (set (tax/context-up tx CxLeaf)) CxMid))
                  "the context no longer sees the nearer parent")
              (is (= #{CxTop} (tax/min-context-parents tx CxLeaf))
                  "so the farther parent is its nearest one")
              (is (= #{CxMid CxLeaf} (tax/max-context-children tx CxTop))
                  "and it is a nearest child of the farther parent")
              (is (= #{} (tax/max-context-children tx CxMid))
                  "and no child of the parent it does not see")
              (is (every? (set (tax/context-down tx CxTop)) (tax/max-context-children tx CxTop)))
              (v/retract! kb eh)
              (is (= #{CxMid} (tax/min-context-parents tx CxLeaf)))
              (is (= #{CxMid} (tax/max-context-children tx CxTop)))
              (is (= #{CxLeaf} (tax/max-context-children tx CxMid))))))))
    (testing "an except on the edge above the nearer parent, stated in the context below both"
      (tu/with-terms [CxTop CxMid CxLeaf]
        (let [tx (reasoning/taxonomy kb)]
          (v/assert kb (list 'genlCx CxTop 'CxWell) 'CxUniverse M)
          (v/assert kb (list 'genlCx CxLeaf CxMid) 'CxUniverse M)
          (v/assert kb (list 'genlCx CxLeaf CxTop) 'CxUniverse M)
          (let [far-h (v/assert kb (list 'genlCx CxMid CxTop) 'CxUniverse M)
                eh    (v/assert kb (list 'except (sx/sentex-handle far-h)) CxLeaf M)]
            (is (= #{CxMid CxTop} (tax/min-context-parents tx CxLeaf))
                "the context reaches the farther parent by its own edge alone")
            (is (= #{CxTop} (tax/min-context-parents tx CxMid))
                "the nearer parent reads no except and keeps its edge")
            (is (= #{CxMid CxLeaf} (tax/max-context-children tx CxTop)))
            (is (= #{CxLeaf} (tax/max-context-children tx CxMid)))
            (v/retract! kb eh)
            (is (= #{CxMid} (tax/min-context-parents tx CxLeaf)))
            (is (= #{CxMid} (tax/max-context-children tx CxTop)))))))))

;; ---- 4b. an except a rule concluded ------------------------------------
;;
;; A visibility `except` is one of the structural integrate arms — nothing about its
;; functor is in the special-predicate table, so it is dispatched on the sentence's
;; shape (`special/structural-integrate`).  The derivation path has to reach that arm
;; too, and the two halves of what it does there are what these assert: `recheck-except`
;; queues the firings that used the hidden handle, and the scoped reads, memoized under
;; the change clock, read the except at the next read.
;;
;; Neither is visible from a cold KB, because a cold read computes rather than recalls
;; and a fresh derivation has no standing firing to sweep.  Both tests therefore *warm*
;; the thing under test first — a firing that already stands, a memo that already holds
;; an answer — which is the state a running KB is always in.

(tu/deftest-kb a-rule-derived-except-sweeps-the-firing-that-used-its-target
  ;; The first half.  The rule fires while nothing hides its antecedent; the except then
  ;; arrives **by derivation**, and the conclusion is left resting on a fact its own
  ;; context can no longer see unless the derivation path queues the sweep.
  ;; `hide` is made forced-monotonic where the rule is stated, so a rule
  ;; reading it may conclude an `except` there (docs/nmtms.md, "The forced-monotonic set")
  (tu/with-terms [q p hide Aa trigger CxSub]
    (v/assert kb (list 'forced_monotonic_predicate hide) CxSub)
    (v/assert kb (list 'genlCx CxSub 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list q Aa) CxSub {:strength :monotonic})]
      (v/assert kb (list 'implies (list q '?x) (list p '?x)) CxSub {:direction :forward :strength :monotonic})
      (is (seq (v/sentexes-matching kb (list p Aa) CxSub)) "the rule fired")
      (v/assert kb (list 'implies (list hide '?z) (list 'except (sx/sentex-handle h)))
                CxSub {:direction :forward :strength :monotonic})
      (v/assert kb (list hide trigger) CxSub {:strength :monotonic})
      (is (seq (v/sentexes-matching kb (list 'except (sx/sentex-handle h)) '?c))
          "the except is stored, and nothing asserted it")
      (is (not (v/ask? kb (list q Aa) CxSub)) "so its target is hidden from CxSub")
      (is (empty? (v/sentexes-matching kb (list p Aa) CxSub))
          "and the conclusion resting on that target is swept, as it is when the
           except is asserted rather than concluded"))))

(tu/deftest-kb a-rule-derived-except-retires-the-scoped-reads-a-stated-one-retires
  ;; The second half, and the one a memo can hide.  `relation-filter-active?` and
  ;; `context-down`'s reverse answer are both memoized; the except set they read is written
  ;; at the store primitive.  A memo the derived except does not retire hides it from
  ;; every warm read — and the KB then disagrees with `recover` over one store, which is
  ;; the property the derivation path exists to keep.
  (tu/with-terms [shiny gold hide trigger CxChild CxParent CxOther]
    (v/assert kb (list 'forced_monotonic_predicate hide) CxChild)
    (let [tx (reasoning/taxonomy kb)]
      (v/assert kb (list 'genlCx CxParent 'CxWell) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genlCx CxOther CxParent) 'CxUniverse {:strength :monotonic})
      (let [edge-h (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse
                             {:strength :monotonic})
            fact-h (v/assert kb (list shiny gold) CxParent {:strength :monotonic})
            reads  (fn [] [(tax/context-down tx CxParent)
                           (tax/sees? tx CxChild CxParent)
                           (v/ask? kb (list shiny gold) CxChild)])]
        ;; warm both memos behind an except that reaches no `genlCx` supporter, so
        ;; `relation-filter-active?` caches *false* for the relation under test
        (v/assert kb (list 'except (sx/sentex-handle fact-h)) CxOther {:strength :monotonic})
        (is (= [#{CxParent CxChild CxOther} true true] (reads))
            "warm, and the answers are the raw ones")
        ;; ...then derive the except on the edge, rather than stating it
        (v/assert kb (list 'implies (list hide '?z)
                           (list 'except (sx/sentex-handle edge-h)))
                  CxChild {:direction :forward :strength :monotonic})
        (v/assert kb (list hide trigger) CxChild {:strength :monotonic})
        (is (seq (v/sentexes-matching kb (list 'except (sx/sentex-handle edge-h)) '?c))
            "the except is stored, and nothing asserted it")
        (let [after (reads)]
          (is (= [#{CxParent CxOther} false false] after)
              "the warm memos are retired: the reader that hides the edge drops out of
               the reverse answer, stops seeing the parent, and stops inheriting its facts")
          (testing "and the restarted KB agrees with the running one"
            (v/recover kb)
            (is (= after (reads)))))))))

;; ---- 5. except a genl link ---------------------------------------------

(tu/deftest-kb except-genl-link
  ;; Excepting a genl declaration is well-formed and removes its interpreted edge.
  (tu/with-terms [dog animal CxTax]
    (v/assert kb (list 'genlCx CxTax 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [genl-h (v/assert kb (list 'genl dog animal) CxTax {:strength :monotonic})]

      (testing "genl closure is active before any except"
        (is (v/genl? kb dog animal CxTax))
        (is (contains? (v/genls kb dog CxTax) animal)))

      (let [eh (v/assert kb (list 'except (sx/sentex-handle genl-h))
                         CxTax {:strength :monotonic})]
        (testing "the genl sentex and interpreted edge are absent"
          (is (empty? (v/sentexes-matching kb (list 'genl dog animal) CxTax)))
          (is (not (v/genl? kb dog animal CxTax)))
          (is (v/genl? kb dog animal)
              "the unscoped cache remains a global superset, not a false retraction"))
        (testing "retract the except — the genl sentex and edge return"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'genl dog animal) CxTax)))
          (is (v/genl? kb dog animal CxTax)))))))

;; ---- 6. except an equals sentex ----------------------------------------

(tu/deftest-kb except-equals-sentex
  ;; Excepting an equality is well-formed and splits the interpreted class.
  (tu/with-terms [CxEq]
    (v/assert kb (list 'genlCx CxEq 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [a (tu/tmp-ind) b (tu/tmp-ind)]
      (let [eq-h (v/assert kb (list 'equals a b) CxEq {:strength :monotonic})
            eh   (v/assert kb (list 'except (sx/sentex-handle eq-h))
                           CxEq {:strength :monotonic})]
        (testing "excepting equals hides the sentex and splits the class"
          (is (empty? (v/sentexes-matching kb (list 'equals a b) CxEq)))
          (is (false? (v/ask? kb (list 'equals a b) CxEq)))
          (is (not (v/same-class? kb a b CxEq)))
          (is (v/same-class? kb a b)
              "the global equality partition stays intact"))
        (testing "retract the except — equality returns"
          (v/retract! kb eh)
          (is (= [eq-h] (map :id (v/sentexes-matching kb (list 'equals a b) CxEq))))
          (is (true? (v/ask? kb (list 'equals a b) CxEq)))
          (is (v/same-class? kb a b CxEq)))))))

;; ---- 7. special-predicate sweep -----------------------------------------
;; For each special predicate with code support, assert the sentex, verify the
;; special behavior is active, except the sentex handle, verify the sentex is
;; hidden from query, retract the except, verify the special behavior returns.

(tu/deftest-kb except-blocks-genl-sentex-visibility
  ;; genl: the taxonomy closure.
  (tu/with-terms [dog animal pet CxG]
    (v/assert kb (list 'genlCx CxG 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [gh (v/assert kb (list 'genl dog animal) CxG {:strength :monotonic})]
      (testing "genl closure active"
        (is (v/genl? kb dog animal CxG))
        (is (contains? (v/genls kb dog CxG) animal)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle gh)) CxG {:strength :monotonic})]
        (testing "the sentex and its context-scoped closure are hidden"
          (is (empty? (v/sentexes-matching kb (list 'genl dog animal) CxG)))
          (is (not (v/genl? kb dog animal CxG))))
        (testing "retract except — genl sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'genl dog animal) CxG)))
          (is (v/genl? kb dog animal CxG)))))))

(tu/deftest-kb except-blocks-genlCx-sentex-visibility
  ;; genlCx: the context inheritance closure.
  (tu/with-terms [shiny gold CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [cx-h (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})]
      (v/assert kb (list shiny gold) CxA {:strength :monotonic})
      (testing "CxB sees CxA's content before except"
        (is (v/ask? kb (list shiny gold) CxB)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle cx-h)) 'CxUniverse
                         {:strength :monotonic})]
        (testing "the genlCx sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'genlCx CxB CxA) 'CxUniverse))))
        (testing "retract except — genlCx sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'genlCx CxB CxA) 'CxUniverse))))))))

(tu/deftest-kb except-blocks-disjoint-sentex-visibility
  ;; disjoint: pairwise type separation.
  (tu/with-terms [dog cat Muffet CxD]
    (v/assert kb (list 'genlCx CxD 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [dh (v/assert kb (list 'disjoint dog cat) CxD {:strength :monotonic})]
      (testing "disjoint is active"
        (is (v/disjoint? kb dog cat)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle dh)) CxD {:strength :monotonic})]
        (testing "the disjoint sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'disjoint dog cat) CxD))))
        (testing "retract except — disjoint sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'disjoint dog cat) CxD)))
          (is (v/disjoint? kb dog cat)))))))

(tu/deftest-kb except-blocks-disjointMetatype-sentex-visibility
  ;; disjoint_metatype: members of the metatype become pairwise disjoint.
  (tu/with-terms [animal_species dog cat CxDM]
    (v/assert kb (list 'genlCx CxDM 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list animal_species dog) CxDM {:strength :monotonic})
    (v/assert kb (list animal_species cat) CxDM {:strength :monotonic})
    (let [dmh (v/assert kb (list 'disjoint_metatype animal_species) CxDM {:strength :monotonic})]
      (testing "disjoint_metatype makes members disjoint"
        (is (v/disjoint? kb dog cat)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle dmh)) CxDM {:strength :monotonic})]
        (testing "the disjoint_metatype sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'disjoint_metatype animal_species) CxDM))))
        (testing "retract except — disjoint_metatype sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'disjoint_metatype animal_species) CxDM))))))))

(tu/deftest-kb except-blocks-transitive-sentex-visibility
  ;; transitive: the transitive closure prover.
  (tu/with-terms [insideOf Gem Box Vault CxT]
    (v/assert kb (list 'genlCx CxT 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [th (v/assert kb (list 'transitive insideOf) CxT {:strength :monotonic})]
      (v/assert kb (list insideOf Gem Box) CxT {:strength :monotonic})
      (v/assert kb (list insideOf Box Vault) CxT {:strength :monotonic})
      (testing "transitive closure is active"
        (is (v/has-prop? kb :transitive insideOf))
        (is (v/ask? kb (list insideOf Gem Vault) CxT)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle th)) CxT {:strength :monotonic})]
        (testing "the transitive sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'transitive insideOf) CxT))))
        (testing "retract except — transitive sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'transitive insideOf) CxT)))
          (is (v/has-prop? kb :transitive insideOf)))))))

(tu/deftest-kb except-blocks-symmetric-sentex-visibility
  ;; symmetric: both directions of a symmetric predicate are provable.
  (tu/with-terms [siblingOf Alice Bob CxS]
    (v/assert kb (list 'genlCx CxS 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [sh (v/assert kb (list 'symmetric siblingOf) CxS {:strength :monotonic})]
      (v/assert kb (list siblingOf Alice Bob) CxS {:strength :monotonic})
      (testing "symmetric provability active"
        (is (v/has-prop? kb :symmetric siblingOf))
        (is (v/ask? kb (list siblingOf Bob Alice) CxS)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle sh)) CxS {:strength :monotonic})]
        (testing "the symmetric sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'symmetric siblingOf) CxS))))
        (testing "retract except — symmetric sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'symmetric siblingOf) CxS)))
          (is (v/has-prop? kb :symmetric siblingOf)))))))

(tu/deftest-kb except-blocks-asymmetric-sentex-visibility
  ;; asymmetric: the converse of an asymmetric predicate forms a nogood with the claim.
  (tu/with-terms [olderThan Alice Bob CxAs]
    (v/assert kb (list 'genlCx CxAs 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [ah (v/assert kb (list 'asymmetric olderThan) CxAs {:strength :monotonic})]
      (v/assert kb (list olderThan Alice Bob) CxAs {:strength :monotonic})
      (testing "asymmetric is active — the default converse is stored and loses"
        (is (v/has-prop? kb :asymmetric olderThan))
        (is (tu/stored-in-clash? kb (list olderThan Bob Alice) CxAs)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle ah)) CxAs {:strength :monotonic})]
        (testing "the asymmetric sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'asymmetric olderThan) CxAs))))
        (testing "retract except — asymmetric sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'asymmetric olderThan) CxAs)))
          (is (v/has-prop? kb :asymmetric olderThan)))))))

(tu/deftest-kb except-blocks-reflexive-sentex-visibility
  ;; reflexive: a reflexive predicate holds of everything with itself.
  (tu/with-terms [sameGroupAs Alice CxR]
    (v/assert kb (list 'genlCx CxR 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [rh (v/assert kb (list 'reflexive sameGroupAs) CxR {:strength :monotonic})]
      (testing "reflexive is active"
        (is (v/has-prop? kb :reflexive sameGroupAs)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle rh)) CxR {:strength :monotonic})]
        (testing "the reflexive sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'reflexive sameGroupAs) CxR))))
        (testing "retract except — reflexive sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'reflexive sameGroupAs) CxR)))
          (is (v/has-prop? kb :reflexive sameGroupAs)))))))

(tu/deftest-kb except-blocks-functional-sentex-visibility
  ;; functional: a functional predicate has at most one value per subject.
  (tu/with-terms [motherOf Alice Mom CxF]
    (v/assert kb (list 'genlCx CxF 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [fh (v/assert kb (list 'functional motherOf) CxF {:strength :monotonic})]
      (testing "functional is active"
        (is (v/has-prop? kb :functional motherOf)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle fh)) CxF {:strength :monotonic})]
        (testing "the functional sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'functional motherOf) CxF))))
        (testing "retract except — functional sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'functional motherOf) CxF)))
          (is (v/has-prop? kb :functional motherOf)))))))

(tu/deftest-kb except-blocks-irreflexive-sentex-visibility
  ;; irreflexive: a :default self tuple is OUT at a reader that reads the mark, and a
  ;; reader the mark is excepted from believes it.
  (tu/with-terms [before Alice CxIr]
    (v/assert kb (list 'genlCx CxIr 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [ih (v/assert kb (list 'irreflexive before) CxIr {:strength :monotonic})
          th (v/assert kb (list before Alice Alice) CxIr)]
      (testing "irreflexive is active"
        (is (v/has-prop? kb :irreflexive before))
        (is (not (v/believed? kb th CxIr))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle ih)) CxIr {:strength :monotonic})]
        (testing "the irreflexive sentex is hidden from query, and the self tuple believed"
          (is (empty? (v/sentexes-matching kb (list 'irreflexive before) CxIr)))
          (is (v/believed? kb th CxIr)))
        (testing "retract except — irreflexive sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'irreflexive before) CxIr)))
          (is (v/has-prop? kb :irreflexive before))
          (is (not (v/believed? kb th CxIr))))))))

(tu/deftest-kb except-blocks-antiSymmetric-sentex-visibility
  ;; anti_symmetric: a believed converse merges the two arguments via equals.
  (tu/with-terms [subsumes CxAnti]
    (v/assert kb (list 'genlCx CxAnti 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [ash (v/assert kb (list 'anti_symmetric subsumes) CxAnti {:strength :monotonic})]
      (testing "anti_symmetric is active"
        (is (v/has-prop? kb :anti-symmetric subsumes)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle ash)) CxAnti {:strength :monotonic})]
        (testing "the anti_symmetric sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'anti_symmetric subsumes) CxAnti))))
        (testing "retract except — anti_symmetric sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'anti_symmetric subsumes) CxAnti)))
          (is (v/has-prop? kb :anti-symmetric subsumes)))))))

(tu/deftest-kb except-blocks-arity-sentex-visibility
  ;; arity: the declared arity is cached and checked on every assertion.
  (tu/with-terms [myRel CxAr]
    (v/assert kb (list 'genlCx CxAr 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [arh (v/assert kb (list 'arity myRel 2) CxAr {:strength :monotonic})]
      (testing "arity declaration is active"
        (is (= 2 (tax/declared-arity (reasoning/taxonomy kb) myRel))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle arh)) CxAr {:strength :monotonic})]
        (testing "the arity sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'arity myRel 2) CxAr))))
        (testing "retract except — arity sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'arity myRel 2) CxAr)))
          (is (= 2 (tax/declared-arity (reasoning/taxonomy kb) myRel))))))))

(tu/deftest-kb except-blocks-inverse-sentex-visibility
  ;; inverse: the inverse relation.
  (tu/with-terms [parentOf childOf CxInv]
    (v/assert kb (list 'genlCx CxInv 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [ih (v/assert kb (list 'inverse parentOf childOf) CxInv {:strength :monotonic})]
      (testing "inverse is active"
        (is (= childOf (v/inverse-of kb parentOf)))
        (is (= parentOf (v/inverse-of kb childOf))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle ih)) CxInv {:strength :monotonic})]
        (testing "the inverse sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'inverse parentOf childOf) CxInv))))
        (testing "retract except — inverse sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'inverse parentOf childOf) CxInv)))
          (is (= childOf (v/inverse-of kb parentOf))))))))

(tu/deftest-kb except-blocks-genlArg-sentex-visibility
  ;; the constraint-only reading: the refusal is the subject
  (tu/without-entailing
   ;; genlArg: argument subtype constraint.
   (tu/with-terms [typeRel root sub CxAG]
     (v/assert kb (list 'genlCx CxAG 'CxWell) 'CxUniverse {:strength :monotonic})
     (v/assert kb (list 'genl root 'thing) CxAG {:strength :monotonic})
     (v/assert kb (list 'genl sub root) CxAG {:strength :monotonic})
     (let [agh (v/assert kb (list 'genlArg typeRel 1 root) CxAG {:strength :monotonic})]
       (testing "genlArg constraint is active — subtype passes, a disjoint sibling fails"
         (is (v/assert kb (list typeRel sub (tu/tmp-type)) CxAG))
         (tu/with-terms [other]
           (v/assert kb (list 'genl other 'thing) CxAG {:strength :monotonic})
           (v/assert kb (list 'disjoint other root) CxAG {:strength :monotonic})
           (is (= :arg-genl (tu/kb-write-type #(v/assert kb (list typeRel other (tu/tmp-type)) CxAG))))))
       (let [eh (v/assert kb (list 'except (sx/sentex-handle agh)) CxAG {:strength :monotonic})]
         (testing "the genlArg sentex is hidden from query"
           (is (empty? (v/sentexes-matching kb (list 'genlArg typeRel 1 root) CxAG))))
         (testing "retract except — genlArg sentex returns"
           (v/retract! kb eh)
           (is (seq (v/sentexes-matching kb (list 'genlArg typeRel 1 root) CxAG)))))))))

(tu/deftest-kb except-blocks-interArgIsa-sentex-visibility
  ;; interArgIsa: conditional argument type declaration.
  (tu/with-terms [eats carnivore meat CxIA]
    (v/assert kb (list 'genlCx CxIA 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genl carnivore 'thing) CxIA {:strength :monotonic})
    (v/assert kb (list 'genl meat 'thing) CxIA {:strength :monotonic})
    (let [iah (v/assert kb (list 'interArgIsa eats 1 carnivore 2 meat) CxIA
                        {:strength :monotonic})]
      (testing "interArgIsa constraint is active — queryable"
        (is (v/ask? kb (list 'interArgIsa eats 1 carnivore 2 meat) CxIA)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle iah)) CxIA {:strength :monotonic})]
        (testing "the interArgIsa sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'interArgIsa eats 1 carnivore 2 meat) CxIA))))
        (testing "retract except — interArgIsa sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'interArgIsa eats 1 carnivore 2 meat) CxIA))))))))
