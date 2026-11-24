;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negation-test
  "Explicit negation with contradiction detection, and defeasible defaults
  (penguins don't fly).  Each test invents gensym'd terms; the fixture rebuilds
  an empty KB per test and asserts the test tore its additions back down."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.settle :as settle]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb negation-is-soft-not-thrown
  (let [dog (tu/tmp-type) muffet (tu/tmp-ind) rex (tu/tmp-ind)]
    (testing "asserting the negation of a believed fact does not throw"
      (v/assert kb (list dog muffet) 'CxUniverse {:strength :monotonic})
      (is (some? (v/assert kb (list 'not (list dog muffet)) 'CxUniverse)))
      (testing "and the weaker (default) belief is the one defeated"
        (is (seq    (v/sentexes-matching kb (list dog muffet) 'CxUniverse)))         ; monotonic survives
        (is (empty? (v/sentexes-matching kb (list 'not (list dog muffet)) 'CxUniverse)))  ; default defeated
        (is (empty? (v/conflicts kb)))))                                    ; resolved, nothing reported
    (testing "strength decides regardless of assertion order"
      (v/assert kb (list 'not (list dog rex)) 'CxUniverse)                ; default
      (v/assert kb (list dog rex) 'CxUniverse {:strength :monotonic})
      (is (seq    (v/sentexes-matching kb (list dog rex) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list 'not (list dog rex)) 'CxUniverse))))))

(tu/deftest-kb penguins-dont-fly
  (let [penguin (tu/tmp-type) bird (tu/tmp-type) animal (tu/tmp-type)
        flies (tu/tmp-pred) robin (tu/tmp-ind) tweety (tu/tmp-ind)]
    (v/assert kb (list 'genl penguin bird) 'CxUniverse)
    (v/assert kb (list 'genl bird animal)  'CxUniverse)
    (v/assert-rule kb [(list penguin '?x)] (list 'not (list flies '?x)) 'CxUniverse {:direction :forward})  ; bare rule
    (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)       ; defeasible
    (v/assert kb (list bird robin) 'CxUniverse)
    ;; Known-true grounds are what let the exception out-rank the default.  A bare rule
    ;; confers :monotonic and is capped by its weakest antecedent, so over a :monotonic
    ;; premise it concludes :monotonic and beats the :default flight rule; over a
    ;; :default premise both sides would be :default and the pair a represented dilemma.
    ;; (An exception stated *on* the general rule with `exceptWhen` blocks it instead —
    ;; see except_test; this test is about defeat.)
    (v/assert kb (list penguin tweety) 'CxUniverse {:strength :monotonic})
    (testing "a normal bird flies by default"
      (is (seq (v/sentexes-matching kb (list flies robin) 'CxUniverse))))
    (testing "a penguin does not — the default is defeated by the stronger conclusion"
      (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list 'not (list flies tweety)) 'CxUniverse))))))

(tu/deftest-kb default-applies-when-not-defeated
  (let [bird (tu/tmp-type) animal (tu/tmp-type) flies (tu/tmp-pred) eagle (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxUniverse)
    (v/assert kb (tu/default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
    (v/assert kb (list bird eagle) 'CxUniverse)
    (testing "with no contrary evidence the default conclusion holds"
      (is (v/believed? kb (v/handle-of kb (list flies eagle) 'CxUniverse))))))

;; ---- nogood discovery is driven off the opposed bodies (settle F1) -------
;; The negation family reads a body's pairs only when the body is stored in both
;; polarities (`reads/stored-opposed?`).  These tests check the two things that existence
;; check could get wrong: it must not miss a real clash, and a negation with no positive
;; twin must add no work yet still be believed.

(tu/deftest-kb an-unpaired-negation-forms-no-nogood
  (let [swims (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind)]
    (testing "negative facts with no positive twin are just knowledge, not clashes"
      (v/assert kb (list 'not (list swims a)) 'CxUniverse)
      (v/assert kb (list 'not (list swims b)) 'CxUniverse)
      (v/assert kb (list 'not (list swims c)) 'CxUniverse)
      (is (empty? (v/conflicts kb)))
      (is (empty? (v/contradictions kb)))
      (is (seq (v/sentexes-matching kb (list 'not (list swims a)) 'CxUniverse))))))

(tu/deftest-kb a-symmetric-negation-nogood-survives-the-existence-check
  ;; The existence check reads a `count-at` of the *stored* body.  A fact normalizes its body
  ;; before `not` wraps it, so a symmetric positive `(siblingOf Ann Bob)` and a
  ;; negation written with the arguments swapped `(not (siblingOf Bob Ann))` store the
  ;; same sorted body — the existence check must still pair them.  If the check keyed on
  ;; the author's argument order it would look under `[siblingOf Bob Ann]`, find nothing,
  ;; and silently drop the clash.
  (let [siblingOf (tu/tmp-pred) ann (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert kb (list 'symmetric siblingOf) 'CxUniverse)
    (v/assert kb (list siblingOf ann bob) 'CxUniverse)                 ; stored sorted
    (v/assert kb (list 'not (list siblingOf bob ann)) 'CxUniverse)     ; arguments swapped
    (testing "the swapped-argument pair is still recognised as a default/default dilemma"
      (is (= 1 (count (v/contradictions kb))))
      (let [{:keys [handles]} (first (v/contradictions kb))]
        (testing "both sides stay believed — a dilemma, not a silent miss"
          (is (every? #(v/believed? kb %) handles)))))))

(tu/deftest-kb a-symmetric-monotonic-negation-still-defeats-the-swapped-positive
  ;; Same pairing, but with a strength difference so the nogood resolves by defeat
  ;; rather than standing as a dilemma: the existence check must find the pair for either
  ;; outcome, and here the weaker (default) positive is the one that gives way.
  (let [siblingOf (tu/tmp-pred) ann (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert kb (list 'symmetric siblingOf) 'CxUniverse)
    (v/assert kb (list siblingOf ann bob) 'CxUniverse)                             ; default
    (v/assert kb (list 'not (list siblingOf bob ann)) 'CxUniverse {:strength :monotonic})
    (testing "the pair is found and the default positive is defeated by the monotonic negation"
      (is (empty? (v/sentexes-matching kb (list siblingOf ann bob) 'CxUniverse)))
      (is (empty? (v/contradictions kb)))
      (is (empty? (v/conflicts kb))))))

(tu/deftest-kb the-opposed-set-tracks-assertion-and-retraction
  ;; The opposed set is maintained incrementally on the store/remove path, so a clash
  ;; forms exactly when both polarities are stored and dissolves when either leaves.
  (let [warm (tu/tmp-pred) sun (tu/tmp-ind)]
    (testing "one polarity alone: no clash"
      (v/assert kb (list warm sun) 'CxUniverse)                        ; default positive
      (is (empty? (v/contradictions kb))))
    (testing "the twin arriving forms the dilemma"
      (let [hn (v/assert kb (list 'not (list warm sun)) 'CxUniverse)]  ; default -> dilemma
        (is (= 1 (count (v/contradictions kb))))
        (testing "and retracting it dissolves the clash, the survivor still believed"
          (v/retract! kb hn)
          (is (empty? (v/contradictions kb)))
          (is (seq (v/sentexes-matching kb (list warm sun) 'CxUniverse))))))))

(tu/deftest-kb a-body-with-no-twin-is-not-posted-and-still-pairs-later
  ;; The opposed family holds a body only while both polarities are stored, so a body
  ;; with no twin adds no entry.  The order that would expose a wrong
  ;; existence check is a **settle between the two polarities**: the twin's arrival is then the only
  ;; write that can form the pair.
  (let [warm (tu/tmp-pred) sun (tu/tmp-ind) moon (tu/tmp-ind)]
    (v/assert kb (list warm sun) 'CxUniverse)
    (v/assert kb (list warm moon) 'CxUniverse)          ; a second settle, nothing opposed
    (is (empty? (v/contradictions kb)))
    (testing "and the index did not grow: a batch of twinless bodies adds no entry"
      (v/with-deferred-settle kb
        (doseq [i (range 8)]
          (v/assert kb (list warm (tu/tmp-ind (str "Cold" i))) 'CxUniverse
                    {:chain? false}))
        (is (empty? (reads/as-stored-opposed-bodies (:index kb))))))
    (let [hn (v/assert kb (list 'not (list warm sun)) 'CxUniverse)]
      (is (= 1 (count (v/contradictions kb))) "the twin arriving is what forms the pair")
      (testing "and the index drops the entry when the twin leaves"
        (v/retract! kb hn)
        (is (empty? (v/contradictions kb)))
        (is (seq (v/sentexes-matching kb (list warm sun) 'CxUniverse)))))
    (testing "the pair re-forms when the twin comes back"
      (v/assert kb (list 'not (list warm sun)) 'CxUniverse)
      (is (= 1 (count (v/contradictions kb)))))))

(tu/deftest-kb the-opposed-family-holds-a-body-while-both-polarities-are-stored
  ;; `(near A B)` extends `(near A)`'s positive key stream and is no positive of it.
  (tu/with-terms [near A B CxP CxQ CxN]
    (let [idx      (:index kb)
          body     (list near A)
          state    (fn [] {:bodies  (reads/as-stored-opposed-bodies idx)
                           :members (reads/as-stored-opposed-members-global idx body)
                           :in      (mapv #(reads/as-stored-opposed-in idx #{%}) [CxP CxQ CxN])})
          longer   (v/assert kb (list near A B) CxP)
          n1       (v/assert kb (list 'not body) CxN)]
      (is (= {:bodies #{} :members #{} :in [#{} #{} #{}]} (state))
          "a longer sentence under the key stream is no positive of the body")
      (let [p1 (v/assert kb body CxP)
            p2 (v/assert kb body CxQ)]
        (is (= {:bodies #{body} :members #{n1 p1 p2} :in [#{p1} #{p2} #{n1}]} (state))
            "the first positive joins the body with the stored denial")
        (v/retract! kb p1)
        (is (= {:bodies #{body} :members #{n1 p2} :in [#{} #{p2} #{n1}]} (state)))
        (v/retract! kb n1)
        (is (= {:bodies #{} :members #{} :in [#{} #{} #{}]} (state))
            "the last denial takes every member out")
        (let [n2 (v/assert kb (list 'not body) CxN)]
          (is (= {:bodies #{body} :members #{n2 p2} :in [#{} #{p2} #{n2}]} (state))
              "the first denial joins the body with the stored positive")
          (v/retract! kb p2)
          (is (= {:bodies #{} :members #{} :in [#{} #{} #{}]} (state))
              "the last positive takes every member out")
          (v/retract! kb n2)))
      (v/retract! kb longer))))

(tu/deftest-kb the-opposed-set-survives-recover
  ;; The opposed bodies are an index family the store holds, and a settle after `recover`
  ;; places every pair over them (`decide/take-edge-cursor!`'s `first?`).  Without that a
  ;; restart would forget every stored clash and silently believe both sides.
  (let [warm (tu/tmp-pred) sun (tu/tmp-ind)]
    (v/assert kb (list warm sun) 'CxUniverse)                          ; default
    (v/assert kb (list 'not (list warm sun)) 'CxUniverse)              ; default -> dilemma
    (is (= 1 (count (v/contradictions kb))) "the pair is a dilemma before recover")
    (v/recover kb)
    (testing "after recover the same clash is rediscovered from storage"
      (is (= 1 (count (v/contradictions kb))))
      (let [{:keys [handles]} (first (v/contradictions kb))]
        (is (every? #(v/believed? kb %) handles) "both sides believed — the dilemma stands")))))

(tu/deftest-kb a-pair-in-two-contexts-is-decided-by-each-reader-that-sees-both
  ;;   CxL  (flies Tweety) default        CxR  (not (flies Tweety)) monotonic
  ;;   CxJ sees CxL and CxR, and CxM sees CxL and a default (not (flies Tweety)) in CxD
  ;; The pair in CxL/CxR is decided where both contexts are seen, and nowhere else; the
  ;; network keeps both sides IN.  The pair in CxL/CxD is a dilemma, reported at CxM.
  (tu/with-terms [flies Tweety CxL CxR CxD CxJ CxM]
    (doseq [[c up] [[CxL 'CxUniverse] [CxR 'CxUniverse] [CxD 'CxUniverse]
                    [CxJ CxL] [CxJ CxR] [CxM CxL] [CxM CxD]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse))
    (let [pos (v/assert kb (list flies Tweety) CxL)
          neg (v/assert kb (list 'not (list flies Tweety)) CxR {:strength :monotonic})
          dn  (v/assert kb (list 'not (list flies Tweety)) CxD)]
      (testing "the reader seeing both takes the default side OUT"
        (is (false? (v/believed? kb pos CxJ)))
        (is (true? (v/believed? kb neg CxJ)))
        (is (= [CxJ] (tu/defeat-vantages kb pos CxJ))))
      (testing "a context seeing one side believes it, and the network keeps it IN"
        (is (true? (v/believed? kb pos CxL)))
        (is (true? (v/believed? kb pos))))
      (testing "the default pair is a dilemma reported at the reader that sees both"
        (let [r (first (filter #(= #{pos dn} (:nogood %)) (v/contradictions kb)))]
          (is (some? r))
          (is (nil? (:kind r)) "a rebuttal")
          (is (= (list 'contradicts (list flies Tweety) (list 'not (list flies Tweety)))
                 (:sentence r)))
          (is (some #(= #{pos dn} (:nogood %)) (v/contradictions kb CxM)))
          (is (not-any? #(= #{pos dn} (:nogood %)) (v/contradictions kb CxL)))))
      (testing "retracting the denial gives the side back at the reader"
        (v/retract! kb neg)
        (is (true? (v/believed? kb pos CxJ)))))))

;; ---- a negation pair is placed as a nogood ---------------------------------

(defn- placed
  "The stored `contradicts` and `defeat` sentexes, each as `[sentence context]` with its
  `sentexHandle` arguments resolved."
  [kb]
  (into #{} (for [f '[contradicts defeat]
                  s (v/sentexes-with-functor kb f)]
              (tu/handle-free kb [(:sentence s) (:context s)]))))

(tu/deftest-kb a-negation-pair-is-placed-and-no-reader-decides-it
  ;;   CxL  (flies Tweety) default        CxR  (not (flies Tweety)) monotonic
  ;;   CxJ sees CxL and CxR
  (tu/with-terms [flies Tweety CxL CxR CxJ]
    (doseq [[c up] [[CxL 'CxUniverse] [CxR 'CxUniverse] [CxJ CxL] [CxJ CxR]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse))
    (let [pos (v/assert kb (list flies Tweety) CxL)
          neg (v/assert kb (list 'not (list flies Tweety)) CxR {:strength :monotonic})
          P   [(list flies Tweety) CxL]
          N   [(list 'not (list flies Tweety)) CxR]]
      (testing "the pair's contradicts and the defeat of its default member are stored at CxJ"
        (is (= #{[(list 'contradicts N P) CxJ] [(list 'defeat P) CxJ]} (placed kb))))
      (testing "the reader reads no verdict of its own on the pair, and the defeat hides the side"
        (is (false? (v/believed? kb pos CxJ)))
        (is (true? (v/believed? kb pos CxL))))
      (testing "retracting the denial takes the placed sentexes out"
        (v/retract! kb neg)
        (is (empty? (placed kb)))
        (is (true? (v/believed? kb pos CxJ)))))))

(defn- retract-reading
  "The placed sentences once the KB holds the pair, `CxD` under `CxL` and `CxE` under
  `CxD` and `CxR`, and `(genlCx CxD CxR)` asserted and retracted when `edge?`, with
  `CxE` written `:CxE`."
  [edge?]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [flies Tweety CxL CxR CxD CxE]
      (doseq [[c up] [[CxL 'CxUniverse] [CxR 'CxUniverse] [CxD CxL] [CxE CxD] [CxE CxR]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse))
      (v/assert kb (list flies Tweety) CxL)
      (v/assert kb (list 'not (list flies Tweety)) CxR {:strength :monotonic})
      (when edge?
        (v/retract! kb (v/assert kb (list 'genlCx CxD CxR) 'CxUniverse)))
      (into #{} (map (fn [[s c]] [(first s) (if (= c CxE) :CxE c)])) (placed kb)))))

(deftest retracting-a-context-edge-places-the-pair-at-its-new-common-descendant
  ;;   CxL  (flies Tweety) default        CxR  (not (flies Tweety)) monotonic
  ;;   CxD under CxL, CxE under CxD and CxR; (genlCx CxD CxR) makes CxD the placement,
  ;;   and its retraction leaves CxE, as the KB where the edge never arrived holds it
  (let [without (retract-reading false)]
    (is (= #{['contradicts :CxE] ['defeat :CxE]} without))
    (is (= without (retract-reading true)))))

;; ---- a pair with a superseded member --------------------------------------

(def ^:private merge-orders
  "The merge first, the merge last, and two interleavings of the four writes."
  [[:merge :pos :neg :rule] [:pos :neg :rule :merge] [:pos :merge :neg :rule] [:rule :neg :merge :pos]])

(defn- names-term?
  "Does a sentence in `xs` name the term `t`?"
  [xs t]
  (boolean (some #{t} (tree-seq coll? seq xs))))

(defn- merged-negation-reading
  "In a fresh KB where CxB sees CxA, the writes `ops` in order: `:pos` (pp Zz) default in
  CxA, `:neg` (not (pp D)) at `strength` in N, D the `:denied` term or Zz, `:rule` (pp ?x) => (rr ?x) forward in
  CxA, `:merge` (rewriteOf Aa Zz) monotonic in N, where N is CxA for `:same` and CxB
  for `:split`, and `:except` / `:unexcept` an `except` of the merge in N stored / retracted.
  Returns the placed sentences, the reported contradictions' sides, and the
  belief at N of (pp Zz) in CxA, (pp Aa) in N and (rr Aa) in N (nil when not stored)."
  [{:keys [pp rr Zz Aa CxA CxB denied]} shape strength ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
    (let [n (if (= shape :split) CxB CxA)
          hs (volatile! {})]
      (doseq [op ops]
        (case op
          :pos      (v/assert kb (list pp Zz) CxA)
          :neg      (v/assert kb (list 'not (list pp (or denied Zz))) n {:strength strength})
          :rule     (v/assert kb (list 'implies (list pp '?x) (list rr '?x)) CxA {:direction :forward})
          :merge    (vswap! hs assoc :merge (v/assert kb (list 'rewriteOf Aa Zz) n {:strength :monotonic}))
          :except   (vswap! hs assoc :except (v/assert kb (list 'except (list 'sentexHandle (:merge @hs))) n
                                                       {:strength :monotonic}))
          :unexcept (v/retract! kb (:except @hs))))
      (let [bel (fn [s c] (when-let [h (v/handle-of kb s c)] (v/believed? kb h n)))]
        {:placed    (placed kb)
         :reported  (into #{} (map #(into #{} (map (juxt :sentence :context)) (:sides %)))
                          (v/contradictions kb))
         :at-reader [(bel (list pp Zz) CxA) (bel (list pp Aa) n) (bel (list rr Aa) n)]}))))

(deftest a-negation-pair-with-a-superseded-member-is-placed-alike-in-every-arrival-order
  ;; the pair over the superseded spelling Zz keeps its placement in every order, beside the
  ;; pair over the restated spelling Aa, and only the restated pair is reported
  (tu/with-terms [pp rr Zz Aa CxA CxB]
    (let [terms {:pp pp :rr rr :Zz Zz :Aa Aa :CxA CxA :CxB CxB}]
      (doseq [shape [:same :split], strength [:monotonic :default]]
        (testing [shape strength]
          (let [rs (mapv #(merged-negation-reading terms shape strength %) merge-orders)]
            (is (= 1 (count (into #{} (map #(dissoc % :reported)) rs))) "the placed sentences and belief")
            (is (every? #(names-term? (:placed %) Zz) rs))
            (is (= (if (= :default strength) [1] [0]) (distinct (map (comp count :reported) rs))))
            (is (not-any? #(names-term? (:reported %) Zz) rs))
            (when (= :monotonic strength)
              (is (= [false false false] (:at-reader (first rs))) "the defeat of (pp Zz) hides (rr Aa)"))))))))

;; ---- a store written with no belief ---------------------------------------

(tu/deftest-kb a-recovered-store-places-its-negation-pairs-before-its-first-write
  ;; CxUniverse  (flies Tweety) default, (not (flies Tweety)) monotonic.  The dump imported
  ;; records-only holds the placed sentexes with no justification, so the recover places
  ;; the pair, in place and in a second KB opened over the store.
  (tu/with-terms [flies swims Tweety Nemo]
    (v/assert kb (list flies Tweety) 'CxUniverse)
    (v/assert kb (list 'not (list flies Tweety)) 'CxUniverse {:strength :monotonic})
    (doseq [reopen? [false true]]
      (testing (if reopen? "reopened" "in place")
        (let [[source recovered written]
              (tu/recovered-readings kb reopen? [(list flies Tweety) 'CxUniverse]
                                     #(v/assert % (list swims Nemo) 'CxUniverse))]
          (is (false? (:loser source)))
          (is (= 2 (count (:placed source))))
          (is (= source recovered) "before any write")
          (is (= source written) "after an unrelated write"))))))

(deftest a-firing-over-a-superseded-spelling-reads-alike-in-every-arrival-order
  ;; The negation is written over the representative Aa, so no pair over Zz exists in any
  ;; order.  With the rule and (pp Zz) before the merge, a stored (rr Zz) restates as
  ;; (rr Aa) under [(rr Zz) (rewriteOf Aa Zz)], beside the firing off (pp Aa) the defeat
  ;; hides.  The merge makes (pp Zz) and (pp Aa) one sentence, so N believes no (rr Aa).
  (tu/with-terms [pp rr Zz Aa CxA CxB]
    (let [terms {:pp pp :rr rr :Zz Zz :Aa Aa :CxA CxA :CxB CxB :denied Aa}
          rs    (mapv #(merged-negation-reading terms :same :monotonic %)
                      (oi/permutations [:pos :neg :rule :merge]))]
      (is (= #{false} (into #{} (map (comp last :at-reader)) rs))))))

;; A store written before 0.24.0 holds the firing over the superseded spelling;
;; `withdraw-retired-firings!` redefined to a no-op writes one.
(deftest a-recovered-store-withdraws-a-firing-over-a-superseded-spelling
  (tu/with-terms [pp rr Zz Aa CxA]
    (let [build (fn [kb]
                  (v/assert kb (list pp Zz) CxA)
                  (v/assert kb (list 'not (list pp Aa)) CxA {:strength :monotonic})
                  (v/assert kb (list 'implies (list pp '?x) (list rr '?x)) CxA {:direction :forward})
                  (v/assert kb (list 'rewriteOf Aa Zz) CxA {:strength :monotonic}))
          read  (fn [kb]
                  {:stored   (into #{} (map (juxt :sentence :context)) (v/sentexes-with-functor kb rr))
                   :believed (when-let [h (v/handle-of kb (list rr Aa) CxA)] (v/believed? kb h CxA))})
          fresh (tu/with-neutral-kb [kb tu/fresh] (build kb) (read kb))]
      (is (false? (:believed fresh)))
      (tu/with-neutral-kb [kb tu/fresh]
        (with-redefs-fn {#'settle/withdraw-retired-firings! (constantly false)} #(build kb))
        (is (true? (:believed (read kb))) "the pre-0.24 write believes (rr Aa)")
        (v/recover kb)
        (is (= fresh (read kb)))))))

(deftest a-firing-over-a-superseded-spelling-reads-alike-when-an-except-of-the-merge-comes-and-goes
  ;; An except of the merge in N gives (pp Zz) back to N, which fires it again; the except
  ;; leaving supersedes (pp Zz) once more and withdraws that firing at the merge.
  (tu/with-terms [pp rr Zz Aa CxA CxB]
    (let [terms {:pp pp :rr rr :Zz Zz :Aa Aa :CxA CxA :CxB CxB :denied Aa}
          read  #(:at-reader (merged-negation-reading terms :same :monotonic %))
          rs    (mapv (fn [o] [(read (conj (vec o) :except)) (read (conj (vec o) :except :unexcept))])
                      (oi/permutations [:pos :neg :rule :merge]))]
      (is (= #{[[true false nil] [false false false]]} (into #{} rs))))))
