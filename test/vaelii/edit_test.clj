;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.edit-test
  "`edit` — a batched add-then-remove that settles once.  The point is efficiency and
  a stable belief state: adds land before removes, so a conclusion the removed premise
  solely-supported but an added one re-derives keeps a witness through the
  dependency-directed sweep — it is never swept and rebuilt, and never flickers OUT and
  back.  The final state equals running the asserts and retracts singly."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(deftest edit-adds-before-removing-so-a-rederivable-conclusion-survives
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [a b c X TheContext]
      ;; two rules concluding the same thing, from different premises
      (v/assert-rule kb [(list a '?x)] (list c '?x) TheContext)
      (v/assert-rule kb [(list b '?x)] (list c '?x) TheContext)
      (let [fa (v/assert kb (list a X) TheContext)
            ch (v/handle-of kb (list c X) TheContext)]
        (is (v/in? kb ch) "(c X) is derived from (a X)")
        (let [result (v/edit! kb {:add [[(list b X) TheContext]] :remove [fa]})]
          (testing "the return reports the add and the teardown"
            (is (= 1 (count (:added result))))
            (is (pos? (:removed-sentexes (:removed result)))))
          (testing "the removed premise is gone and the added one is believed"
            (is (nil? (v/handle-of kb (list a X) TheContext)))
            (is (v/in? kb (v/handle-of kb (list b X) TheContext))))
          (testing "(c X) survived on the new support — same handle, still IN"
            (is (v/in? kb ch))
            (is (contains?
                 (->> (v/supporting-justifications kb ch)
                      (mapcat :antecedents) set)
                 (v/handle-of kb (list b X) TheContext))
                "its live support now names the added premise")))))))

(deftest edit-matches-separate-assert-and-retract
  ;; Run the same scenario two ways on two *sequential* fresh KBs (nesting two
  ;; `tu/fresh` would collide — both take the scratch db pair), then compare belief.
  (tu/with-terms [a b c X TheContext]
    (letfn [(scenario [kb via-edit?]
              (v/assert-rule kb [(list a '?x)] (list c '?x) TheContext)
              (v/assert-rule kb [(list b '?x)] (list c '?x) TheContext)
              (let [fa (v/assert kb (list a X) TheContext)]
                (if via-edit?
                  (v/edit! kb {:add [[(list b X) TheContext]] :remove [fa]})
                  (do (v/assert kb (list b X) TheContext)   ; add...
                      (v/retract! kb fa))))               ; ...then remove
              (into {} (for [s [(list a X) (list b X) (list c X)]]
                         [s (let [h (v/handle-of kb s TheContext)] (boolean (and h (v/in? kb h))))])))]
      (let [via-edit (tu/with-neutral-kb [kb tu/fresh] (scenario kb true))
            via-sep  (tu/with-neutral-kb [kb tu/fresh] (scenario kb false))]
        (is (= via-edit via-sep)
            "edit reaches the same belief as add-then-retract done singly")
        (is (get via-edit (list c X)) "(c X) is believed either way")))))

(deftest edit-degenerate-only-adds-or-only-removes
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p q X TheContext]
      (testing "only adds behaves like assert-many"
        (let [r (v/edit! kb {:add [[(list p X) TheContext] [(list q X) TheContext]]})]
          (is (= 2 (count (:added r))))
          (is (= {:removed-sentexes 0 :removed-justifications 0} (:removed r)))
          (is (v/in? kb (v/handle-of kb (list p X) TheContext)))
          (is (v/in? kb (v/handle-of kb (list q X) TheContext)))))
      (testing "only removes behaves like retract"
        (let [ph (v/handle-of kb (list p X) TheContext)
              r  (v/edit! kb {:remove [ph]})]
          (is (empty? (:added r)))
          (is (pos? (:removed-sentexes (:removed r))))
          (is (nil? (v/handle-of kb (list p X) TheContext)))
          (is (v/in? kb (v/handle-of kb (list q X) TheContext)) "the untouched premise stays"))))))

;; ---- the door refuses what the dry run reports ---------------------------

(deftest a-malformed-add-entry-is-refused-whole-not-applied-in-part
  ;; One fn (`add-entry-shape-problem`) is read by both doors, so what `check-edit`
  ;; reports as `:shape` is what `edit` throws — a 4-element entry is never applied
  ;; with the junk silently dropped.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet ShapeContext]
      (testing "a 4-element entry is :shape at both doors, and nothing lands"
        (let [batch  {:add [[(list dog Muffet) ShapeContext {} :junk]]}
              before (v/sentex-count kb)]
          (is (= [:shape] (mapv :type (v/check-edit kb batch))))
          (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
            (is (= :shape (:type (ex-data e)))))
          (is (= before (v/sentex-count kb)))
          (is (nil? (v/handle-of kb (list dog Muffet) ShapeContext))
              "the entry was refused whole, not applied minus the junk")))
      (testing "a non-sequential entry is :shape at both doors, not a bare throw"
        (doseq [bad [42 {:sentence 1}]]
          (let [batch {:add [bad]}]
            (is (= [:shape] (mapv :type (v/check-edit kb batch))))
            (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
              (is (= :shape (:type (ex-data e)))))))))))

(deftest a-batch-half-that-is-not-a-sequence-is-shape-at-every-door
  ;; `{:add 5}` reaches every door's iteration, so unrefused it raises a bare
  ;; "Don't know how to create ISeq" out of `check-edit`, `edit` and `preview` alike —
  ;; over the daemon, a 500 with no `:type` to discriminate on.
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [batch [{:add 5} {:remove 5} {:add {:a 1}} {:remove #{7}}]]
      (testing (pr-str batch)
        (is (= [:shape] (mapv :type (v/check-edit kb batch))))
        (doseq [[nm door] [["edit" #(v/edit! kb batch)]
                           ["preview" #(v/preview kb batch)]]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (door))
                      (str nm " refuses " (pr-str batch)))]
            (is (= :shape (:type (ex-data e))) (str nm " says :shape"))))))))

(deftest an-unknown-remove-handle-refuses-the-batch-before-anything-lands
  ;; `check-edit` flags the handle as `:unknown-handle`; a door that then quietly
  ;; folded it into zero counts would apply the adds first and leave a half-applied
  ;; batch behind a refusal the dry run had already named.  `retract!` standalone is
  ;; the deliberate contrast: retracting one absent handle is an ordinary zero-count
  ;; answer, not a batch.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet HalfContext]
      (let [ghost 9999999
            batch {:add [[(list dog Muffet) HalfContext]] :remove [ghost]}]
        (is (nil? (v/sentex kb ghost)) "the handle names nothing stored")
        (testing "check-edit predicts the refusal"
          (is (some #(= :unknown-handle (:type %)) (v/check-edit kb batch))))
        (testing "edit refuses the whole batch with the same :type"
          (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
            (is (= :unknown-handle (:type (ex-data e))))
            (is (= ghost (:handle (ex-data e))))))
        (testing "and the add half did not land — no half-applied batch"
          (is (nil? (v/handle-of kb (list dog Muffet) HalfContext))))
        (testing "retract! standalone keeps its zero-count answer"
          (is (= {:removed-sentexes 0 :removed-justifications 0}
                 (v/retract! kb ghost))))
        (testing "and a nil :remove entry stays nothing-to-remove"
          (is (= 0 (:removed-sentexes (:removed (v/edit! kb {:remove [nil]}))))))))))
