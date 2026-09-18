;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.examples-test
  "The worked examples, run against the KB they describe.

  This is the gate that keeps `/reasoning` from becoming a brochure. Every card on that
  page declares what the shipped ontology is supposed to answer, and the ontology is
  edited far more often than the page is — so a rule removed, a declaration dropped or a
  disjointness restated turns a test red here instead of leaving a card that confidently
  states a verdict the KB no longer gives."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.examples :as ex]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- scratch
  "A context below CxWell to stand in for the reader's sandbox: it sees the whole
  shipped ontology, and the fixture takes everything written into it away again."
  [kb]
  (let [c (tu/fresh-term :context :ExampleRun)]
    (v/assert kb (list 'genlCx c 'CxWell) 'CxUniverse)
    c))

;; ---- the table itself ---------------------------------------------------

(deftest every-example-is-well-formed
  (doseq [{:keys [id group title shows rests-on goal refuse kind expect]} ex/examples]
    (testing (str id)
      (is (string? id))
      (is (seq group))
      (is (seq title))
      (is (seq shows))
      (is (seq rests-on) "an example that names nothing it rests on cannot be checked")
      (if (= :refusal kind)
        (is (some? refuse))
        (do (is (some? goal))
            (is (#{:yes :no} expect) "a goal example says what the ontology should answer"))))))

(deftest example-ids-are-unique
  (is (= (count ex/examples) (count (distinct (map :id ex/examples))))))

;; ---- what they answer ---------------------------------------------------

(tu/deftest-kb every-example-rests-on-sentexes-this-kb-holds
  ;; `available?` is what greys a card out on another corpus; on the shipped one every
  ;; card must be live, or the page would be quietly showing nothing
  (doseq [e ex/examples]
    (is (ex/available? kb e)
        (str (:id e) " — missing: "
             (pr-str (for [[s c h] (ex/dependencies kb e) :when (nil? h)] [s c]))))))

(tu/deftest-kb every-example-answers-as-the-ontology-intends
  (let [ctx (scratch kb)]
    (doseq [{:keys [id premises context] :as e} ex/examples]
      (let [where (if (seq premises) ctx (or context 'CxWell))]
        (when (seq premises) (ex/establish! kb e where))
        (let [r (ex/run kb e where)]
          (is (:as-intended? r)
              (str id " — " (pr-str (dissoc r :why)))))))))

(tu/deftest-kb the-examples-do-not-interfere-with-each-other
  ;; the page's real situation: one sandbox holds every example the reader has run, so
  ;; each card's verdict has to survive all the others being established.  Two cards
  ;; sharing an individual is the way this goes wrong — establish one that kills the
  ;; animal another card says is alive and the second card silently starts contradicting
  ;; its own text.  Establish everything FIRST, then ask.
  (let [ctx (scratch kb)]
    (doseq [e ex/examples :when (seq (:premises e))] (ex/establish! kb e ctx))
    (doseq [{:keys [id premises context] :as e} ex/examples]
      (let [r (ex/run kb e (if (seq premises) ctx (or context 'CxWell)))]
        (is (:as-intended? r)
            (str id " — " (pr-str (dissoc r :why))))))))

(tu/deftest-kb the-read-only-examples-write-nothing
  ;; the gallery renders every card with no premises on every page load, so running one
  ;; has to be a read: a page that grew the KB each time it was opened would be a bug
  ;; nobody saw until the store filled up
  (let [before (v/sentex-count kb)]
    (doseq [e ex/examples :when (empty? (:premises e))]
      (ex/run kb e (or (:context e) 'CxWell)))
    (is (= before (v/sentex-count kb)))))

(tu/deftest-kb establishing-an-example-twice-stores-it-once
  (let [ctx (scratch kb)
        e   (ex/by-id "grandparent")]
    (ex/establish! kb e ctx)
    (let [after-one (v/sentex-count kb)]
      (ex/establish! kb e ctx)
      (is (= after-one (v/sentex-count kb))
          "re-running an example finds its premises rather than duplicating them"))))

(tu/deftest-kb an-example-this-kb-cannot-support-is-unavailable-not-wrong
  ;; the honest failure mode, and the whole reason a card names its dependencies: on a
  ;; corpus that does not hold them the card says so rather than answering from
  ;; vocabulary that is not there
  (tu/with-terms [nowhere Zork]
    (let [e {:id "fabricated" :group "g" :title "t" :shows "s"
             :rests-on [[(list nowhere Zork) 'CxWell]]
             :goal (list nowhere Zork) :expect :yes}]
      (is (not (ex/available? kb e)))
      (let [r (ex/run kb e 'CxWell)]
        (is (false? (:available? r)))
        (is (nil? (:answered? r)) "an unavailable example is not run at all")
        (is (nil? (:as-intended? r)) "and makes no claim either way")))))

;; ---- the claims the cards make about the machinery ----------------------

(tu/deftest-kb the-levels-the-cards-name-are-the-levels-that-answer
  ;; each card reports the level `escalate` stopped at, and the level *is* the claim:
  ;; a closure answering at 5 and the chainers answering at 7 are different statements
  ;; about what the KB had to do
  (let [level (fn [id] (:level (ex/run kb (ex/by-id id) 'CxWell)))]
    (testing "a cached closure, with no sentex materialized for the answer"
      (is (= 5 (level "genl-chain")))
      (is (nil? (:handle (ex/run kb (ex/by-id "genl-chain") 'CxWell)))))
    (testing "the prover stack, for disjointness and argument preservation"
      (is (= 6 (level "disjoint-metatype")))
      (is (= 6 (level "arg-preserving"))))
    (testing "plain context inheritance, for a forward-derived sentex with a record"
      (is (= 3 (level "metadata-to-type")))
      (is (some? (:handle (ex/run kb (ex/by-id "metadata-to-type") 'CxWell)))))))

(tu/deftest-kb a-refusal-example-stores-nothing
  (let [ctx (scratch kb)
        e   (ex/by-id "disjoint-refusal")]
    (ex/establish! kb e ctx)
    (let [before (v/sentex-count kb)
          r      (ex/run kb e ctx)]
      (is (:refused? r))
      (is (= '(:disjoint) (map :type (:problems r))))
      (is (= before (v/sentex-count kb))
          "`check` answers what assert would do and writes nothing"))))

(tu/deftest-kb the-shows-text-is-prose-not-a-paragraph-of-code
  ;; the cards are read by someone meeting the engine for the first time
  (doseq [{:keys [id shows]} ex/examples]
    (let [one-line (str/replace shows #"\s+" " ")]
      (is (< 40 (count one-line) 500) (str id " — " (count one-line) " chars")))))
