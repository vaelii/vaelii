;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.derived-callout-test
  "What a write turned out to mean — `vaelii.core/edit-with-consequences!` — and the
  callout the browser renders from it.

  The engine half is checked against `preview`, which answers the same question about the
  same batch by a completely different route (apply, read, roll back, and read belief-before
  off the restored KB).  They share the entry shapes and nothing else: this one captures
  the labels on the way through, because it has no rollback to read after.  So agreement is
  evidence, not tautology — and disagreement would mean one of them is wrong about what a
  commit does, which is the whole claim the proposal panel rests on."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- sentences [entries] (mapv :sentence entries))

;; ---- the engine: what a write meant --------------------------------------

(tu/deftest-kb a-rule-firing-is-reported-with-the-argument-that-made-it
  (tu/with-terms [dog mortal Muffet CxRule]
    (v/assert kb (list 'genlCx CxRule 'CxWell) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list mortal '?x) CxRule {:direction :forward})
    (let [r (v/edit-with-consequences! kb {:add [[(list dog Muffet) CxRule]]})
          derived (remove :premise? (:believed-added r))]
      (testing "the premise the caller wrote is reported, and marked as one — that mark is
                how a reader tells what it said from what followed"
        (is (= [(list dog Muffet)]
               (sentences (filter :premise? (:believed-added r))))))
      (testing "and the conclusion it produced, which `edit` alone never mentions"
        (is (= [(list mortal Muffet)] (sentences derived))))
      (testing "with the argument one level deep, as sentences rather than handles"
        (let [j (:justification (first derived))]
          (is (= [(list dog Muffet)] (:antecedents j)))
          (is (= (list 'implies (list dog '?x) (list mortal '?x)) (:rule j)))
          (is (integer? (:informant j)) "the rule handle, so the proof is reachable")))
      (testing "the conclusion is a real sentex with a real proof"
        (let [h (:handle (first derived))]
          (is (nat-int? h))
          (is (v/in? kb h))
          (is (= (list mortal Muffet) (:sentence (v/why kb h)))))))))

(tu/deftest-kb a-write-that-follows-from-nothing-reports-only-itself
  (tu/with-terms [swims Willy CxQuiet]
    (v/assert kb (list 'genlCx CxQuiet 'CxWell) 'CxUniverse)
    (let [r (v/edit-with-consequences! kb {:add [[(list swims Willy) CxQuiet]]})]
      (is (= [(list swims Willy)] (sentences (:believed-added r))))
      (is (every? :premise? (:believed-added r)) "nothing followed, and nothing is claimed")
      (is (= [] (:believed-removed r))))))

(tu/deftest-kb a-write-that-defeats-a-default-reports-the-withdrawal
  (tu/with-terms [bird flies Tweety CxDefeat]
    (v/assert kb (list 'genlCx CxDefeat 'CxWell) 'CxUniverse)
    (v/assert kb (list 'set/defaultRule
                       (list 'set/forwardRule (list 'implies (list 'and (list bird '?x)) (list flies '?x))))
              CxDefeat)
    (v/assert kb (list bird Tweety) CxDefeat)
    (is (v/ask? kb (list flies Tweety) CxDefeat) "the default holds first")
    (testing "known-true content beats a default, and the withdrawal is reported — the
              half a caller reading only `:added` would never see"
      (let [r (v/edit-with-consequences!
               kb {:add [[(list 'not (list flies Tweety)) CxDefeat
                          {:strength :monotonic}]]})
            gone (:believed-removed r)]
        (is (= [(list flies Tweety)] (sentences gone)))
        (is (= :defeated (:reason (first gone))))
        (is (nat-int? (:handle (first gone)))
            "still stored, so it is still addressable — defeat is not deletion")))))

(tu/deftest-kb the-report-agrees-with-what-preview-promised
  (testing "preview and the commit answer the same question about the same batch by two
            different routes; a disagreement means one of them is wrong about the engine"
    (tu/with-terms [cat purrs alive CxPair]
      (v/assert kb (list 'genlCx CxPair 'CxWell) 'CxUniverse)
      (v/assert-rule kb [(list cat '?x)] (list purrs '?x) CxPair {:direction :forward})
      (v/assert-rule kb [(list purrs '?x)] (list alive '?x) CxPair {:direction :forward})
      (tu/with-terms [Tom]
        (let [batch    {:add [[(list cat Tom) CxPair]]}
              promised (v/preview kb batch)
              actual   (v/edit-with-consequences! kb batch)]
          (is (= (set (sentences (:believed-added promised)))
                 (set (sentences (:believed-added actual)))))
          (is (= (set (sentences (:believed-removed promised)))
                 (set (sentences (:believed-removed actual)))))
          (testing "including the cascade — one assert, two rules deep"
            (is (= #{(list cat Tom) (list purrs Tom) (list alive Tom)}
                   (set (sentences (:believed-added actual)))))))))))

(deftest the-two-truth-maintenance-representations-report-the-same-thing
  ;; A space of its own, because the `finally` below CLEARS it — and a number
  ;; **outside 4..15**, which is the range `VAELII_TEST_SPACE` selects a block
  ;; from (`testing.md`).  A literal inside that range is unused only until
  ;; somebody moves the block onto it, and then the clear takes this namespace's
  ;; own `:once` starter KB with it — reported by whichever teardown runs next,
  ;; as a KB that has lost every sentex the fixture loaded, naming nothing that
  ;; leads back here.
  (doseq [tms [:reference :dense]]
    (let [kb (v/open-kb {:space 913 :tms tms})]
      (try
        (v/assert kb '(genlCx CxTmsCallout CxUniverse) 'CxUniverse)
        (v/assert-rule kb ['(tms_callout_dog ?x)] '(tms_callout_mortal ?x) 'CxTmsCallout {:direction :forward})
        (let [r (v/edit-with-consequences!
                 kb {:add [['(tms_callout_dog TmsCalloutMuffet) 'CxTmsCallout]]})]
          (is (= ['(tms_callout_mortal TmsCalloutMuffet)]
                 (sentences (remove :premise? (:believed-added r))))
              (str "under " tms)))
        (finally (v/clear! kb))))))

(tu/deftest-kb the-report-is-capped-and-says-when-it-was
  (tu/with-terms [seed CxCap]
    (v/assert kb (list 'genlCx CxCap 'CxWell) 'CxUniverse)
    (let [preds (repeatedly 4 #(tu/tmp-pred "capped"))]
      (doseq [p preds] (v/assert-rule kb [(list seed '?x)] (list p '?x) CxCap {:direction :forward}))
      (tu/with-terms [Thing]
        (let [r (v/edit-with-consequences! kb {:add [[(list seed Thing) CxCap]]}
                                           {:max-results 2})]
          (is (= 2 (count (:believed-added r))))
          (is (:bounded? r) "a partial answer never is indistinguishable from a complete one"))))))

;; ---- the browser: the callout --------------------------------------------

(defn- callout-text
  "The rendered callout, tags stripped — what a reader actually reads.  Nil when the page
  shows none, which is the answer for a commit that derived nothing."
  [body]
  (when-let [i (str/index-of body "class=\"callout\"")]
    (-> (subs body i)
        (str/replace #"<[^>]*>" "")
        (str/replace #"&apos;" "'")
        (str/replace #"\s+" " "))))

(defn- assert-through-the-form [kb text ctx]
  (callout-text (:body ((web/app kb) {:request-method :post :uri "/assert"
                                      :params {"text" text "ctx" (str ctx)}
                                      :headers {"host" "localhost:3000"}}))))

(tu/deftest-kb the-genl-sequence-produces-the-callout
  (testing "the newbie's ninety seconds: say two things, and a third is true.  Nothing is
            *derived* here — the engine never materializes a supertype membership — so the
            callout has to read it off the taxonomy, and say so rather than claim a record"
    (tu/with-terms [dog_ animal_ Muffet CxGenl]
      (v/assert kb (list 'genlCx CxGenl 'CxWell) 'CxUniverse)
      (v/assert kb (list 'genl dog_ animal_) CxGenl)
      (let [out (assert-through-the-form kb (pr-str (list dog_ Muffet)) CxGenl)]
        (is (some? out) "the callout appeared")
        (is (str/includes? out "You didn't say this, but it follows"))
        (is (str/includes? out (str "(" animal_ " " Muffet ")")))
        (testing "and the explanation names the two premises, not handles"
          (is (str/includes? out (str "because (" dog_ " " Muffet ")")))
          (is (str/includes? out (str "every " dog_ " is a " animal_)))
          (is (not (re-find #"#\d+" out)) "no bare handle is shown to a first-time reader")))
      (testing "there is genuinely no such sentex — the callout is not describing a record"
        (is (nil? (v/handle-of kb (list animal_ Muffet) CxGenl)))
        (is (v/ask? kb (list animal_ Muffet) CxGenl) "it is still true, answered on demand")))))

(tu/deftest-kb a-rule-firing-shows-its-proof-in-the-callout
  (tu/with-terms [fish gilled Nemo CxFish]
    (v/assert kb (list 'genlCx CxFish 'CxWell) 'CxUniverse)
    (v/assert-rule kb [(list fish '?x)] (list gilled '?x) CxFish {:direction :forward})
    (let [out (assert-through-the-form kb (pr-str (list fish Nemo)) CxFish)]
      (is (str/includes? out (str "(" gilled " " Nemo ")")))
      (is (str/includes? out (str "because (" fish " " Nemo ")")))
      (is (str/includes? out "and the rule")
          "a rule firing says which rule; a subsumption has none to name")
      (is (str/includes? out "proof")
          "and it has a record, so the whole tree is one click away"))))

(tu/deftest-kb a-commit-that-derives-nothing-shows-nothing
  (testing "silence beats \"0 new conclusions\" — an empty callout makes the boring case as
            loud as the interesting one"
    (tu/with-terms [rel A B CxSilent]
      (v/assert kb (list 'genlCx CxSilent 'CxWell) 'CxUniverse)
      (is (nil? (assert-through-the-form kb (pr-str (list rel A B)) CxSilent))))))

(tu/deftest-kb the-callout-caps-at-three-and-counts-the-rest
  (tu/with-terms [trigger Subject CxMany]
    (v/assert kb (list 'genlCx CxMany 'CxWell) 'CxUniverse)
    (doseq [_ (range 5)]
      (v/assert-rule kb [(list trigger '?x)] (list (tu/tmp-pred "many") '?x) CxMany {:direction :forward}))
    (let [out (assert-through-the-form kb (pr-str (list trigger Subject)) CxMany)]
      (is (str/includes? out "more consequences")
          "the rest are counted rather than listed")
      (is (re-find #"and 2 more consequences" out)))))

(tu/deftest-kb the-callout-never-repeats-what-the-batch-itself-said
  (testing "a supertype the same commit stated outright is not news"
    ;; Two levels, not one, and that is what makes the claim checkable: the batch states
    ;; the near supertype and leaves the far one unsaid, so a callout is genuinely
    ;; rendered and the suppression is a *missing line* in a panel that exists.  With one
    ;; level there is nothing else to say, the page shows no callout at all, and "no
    ;; callout" satisfies the assertion whether the suppression works or not.
    (tu/with-terms [pup_ hound_ mammal_ Rex CxStated]
      (v/assert kb (list 'genlCx CxStated 'CxWell) 'CxUniverse)
      (v/assert kb (list 'genl pup_ hound_) CxStated)
      (v/assert kb (list 'genl hound_ mammal_) CxStated)
      (let [out (assert-through-the-form
                 kb (str (pr-str (list pup_ Rex)) "\n" (pr-str (list hound_ Rex)))
                 CxStated)]
        (is (some? out) "the callout appeared")
        (is (str/includes? out (str "(" mammal_ " " Rex ")"))
            "the supertype nobody stated is exactly what a callout is for")
        (is (not (str/includes? out (str "(" hound_ " " Rex ") because")))
            "the reader wrote it; telling them it follows is noise")))))
