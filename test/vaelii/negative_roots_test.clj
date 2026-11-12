;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negative-roots-test
  "An open negative pattern reads its candidates off the argument roots, which hold both
  polarities, so the positive facts are left out at the index before any record is fetched
  (`res/negative-root-handles`).  Two things are held here.

  **The answer is the reference read's.**  `res/*split-negative-roots?*` false is the read
  as it was, fetching every candidate and dropping the positive ones on polarity in
  `match-one`.  Every open negative pattern below is answered both ways, uncached, at every
  context and at `?ctx`, and the two answers must be the same set.  The KB is shaped to
  give the split every way to go wrong: denials of one predicate in some contexts and none
  in others, a predicate whose positive extent is large and whose denials are few, a
  predicate with positives alone, a `genl` edge that fans a negation to its genl, two
  lengths under one functor, a symmetric predicate, a denial an `except` hides and a
  denial a monotonic positive defeats.

  **The positive extent is not fetched.**  With no denial stored in the contexts read, an
  open negative fetches nothing, and with some stored it fetches at most what the denials
  number, whatever the positive extent holds.  `(not (empty ?w))` fans to
  `(not (unary_predicate ?w))`, which fetched every positive record a probe, a postgres
  round trip each, once per cover part per minted type."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (fn [t] (try (t) (finally (prof/stop)))))

(def ^:private M {:strength :monotonic})

(def ^:private wide
  "How many positive members the broad predicate holds: large against the denials, so a
  read that fetches the positive extent shows as a count no denial accounts for."
  300)

(defn- kb-with-both-polarities []
  (let [kb (tu/fresh)]
    (v/with-deferred-settle kb
      (doseq [[c u] '[[CxNrA CxUniverse] [CxNrB CxUniverse] [CxNrC CxNrA] [CxNrC CxNrB]
                      [CxNrD CxUniverse]]]
        (v/assert kb (list 'genlCx c u) 'CxUniverse M))
      (v/assert kb '(genl nr_part nr_whole) 'CxUniverse M)
      (v/assert kb '(binary_predicate nrRel) 'CxUniverse M)
      (v/assert kb '(symmetric nrSym) 'CxUniverse M)
      ;; the broad predicate: a wide positive extent in CxNrA, two denials in CxNrB
      (dotimes [i wide] (v/assert kb (list 'nr_whole (symbol (str "NrW" i))) 'CxNrA {}))
      (v/assert kb '(not (nr_whole NrDw0)) 'CxNrB M)
      (v/assert kb '(not (nr_whole NrDw1)) 'CxNrB {})
      ;; the part, whose negation fans to the whole: positives in CxNrB, a denial in CxNrA
      (dotimes [i 40] (v/assert kb (list 'nr_part (symbol (str "NrP" i))) 'CxNrB {}))
      (v/assert kb '(not (nr_part NrDp0)) 'CxNrA M)
      ;; positives alone, at two lengths
      (dotimes [i 60] (v/assert kb (list 'nr_bare (symbol (str "NrB" i))) 'CxNrA {}))
      ;; a binary predicate in both polarities, a hub at argument 1
      (dotimes [i 50] (v/assert kb (list 'nrRel 'NrHub (symbol (str "NrR" i))) 'CxNrA {}))
      (v/assert kb '(not (nrRel NrHub NrR0x)) 'CxNrB M)
      (v/assert kb '(not (nrRel NrOther NrHub)) 'CxNrA M)
      ;; symmetric, in both polarities
      (dotimes [i 20] (v/assert kb (list 'nrSym 'NrS (symbol (str "NrT" i))) 'CxNrA {}))
      (v/assert kb '(not (nrSym NrU NrS)) 'CxNrB M))
    ;; a denial an `except` hides from CxNrC, and a denial a monotonic positive defeats
    (let [h (v/assert kb '(not (nr_whole NrDw2)) 'CxNrA M)]
      (v/assert kb (list 'except (list 'sentexHandle h)) 'CxNrC M))
    (v/assert kb '(not (nr_whole NrDw3)) 'CxNrD {})
    (v/assert kb '(nr_whole NrDw3) 'CxNrD M)
    kb))

(def ^:private patterns
  '[(not (nr_whole ?w)) (not (nr_part ?w)) (not (nr_bare ?w))
    (not (nrRel ?x ?y)) (not (nrRel NrHub ?y)) (not (nrRel ?x NrHub))
    (not (nrSym ?x ?y)) (not (nrSym NrS ?y)) (not (nrSym ?x NrS))
    (not (nr_absent ?w))])

(defn- answer [kb pattern context split?]
  (binding [res/*split-negative-roots?* split?]
    (into #{} (map (fn [[h b]] [h b])) (res/matches-visible kb pattern context false))))

(deftest an-open-negative-answers-what-the-reference-read-answers
  (tu/with-cleared-kb [kb #(kb-with-both-polarities)]
    (doseq [c '[CxNrA CxNrB CxNrC CxNrD CxUniverse ?ctx]
            pat patterns]
      (testing (str pat " at " c)
        (is (= (answer kb pat c false) (answer kb pat c true)))))
    (testing "the KB holds what the cases are about"
      (is (= #{'NrDw0 'NrDw1} (into #{} (map #(get (second %) '?w))
                                    (res/matches-visible kb '(not (nr_whole ?w)) 'CxNrB false))))
      (is (= #{'NrDw0 'NrDw1 'NrDp0} (into #{} (map #(get (second %) '?w))
                                           (res/matches-visible kb '(not (nr_part ?w)) 'CxNrC false))))
      (is (not-any? #(= 'NrDw2 (get (second %) '?w))
                    (res/matches-visible kb '(not (nr_whole ?w)) 'CxNrC false))
          "the except hides its denial from CxNrC")
      (is (not-any? #(= 'NrDw3 (get (second %) '?w))
                    (res/matches-visible kb '(not (nr_whole ?w)) 'CxNrD false))
          "the defeated denial is not read")
      (is (seq (res/matches-visible kb '(not (nrSym NrS ?y)) 'CxNrB false))
          "the symmetric denial is read"))))

(defn- fetched [kb pattern context split?]
  (binding [res/*split-negative-roots?* split?]
    (prof/start)
    (dorun (res/matches-visible kb pattern context false))
    (get-in (prof/stop) [:fetches :sentex] 0)))

(deftest an-open-negative-fetches-no-positive-record
  ;; one fetch per denial stored in a context the read reaches, whatever the positive
  ;; extent: an except or a defeat hides a denial after it is fetched
  (tu/with-cleared-kb [kb #(kb-with-both-polarities)]
    (testing "no denial in the contexts read: nothing is fetched"
      (is (zero? (fetched kb '(not (nr_bare ?w)) 'CxNrA true)))
      (is (zero? (fetched kb '(not (nr_absent ?w)) 'CxNrA true))))
    (testing "denials beside a wide positive extent: the denials alone are fetched"
      ;; CxNrA holds the wide extent and the denial the except hides from CxNrC
      (is (= 1 (fetched kb '(not (nr_whole ?w)) 'CxNrA true)))
      ;; and CxNrB the two others
      (is (= 3 (fetched kb '(not (nr_whole ?w)) 'CxNrC true)))
      ;; the part's own denial, and the whole's three through the genl edge
      (is (= 4 (fetched kb '(not (nr_part ?w)) 'CxNrC true))))
    (testing "the reference read fetches the positive extent"
      (is (< wide (fetched kb '(not (nr_whole ?w)) 'CxNrC false))))))
