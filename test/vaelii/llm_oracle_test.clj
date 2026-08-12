;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.llm-oracle-test
  "The outside judge (`vaelii.impl.llm.oracle`): the KB's own conclusions glossed into
  English, put to a model, and answered agree / disagree / unsure.

  Everything here but the last test runs against the offline stub, so the machinery — the
  claim set, the prompt, the parse, the arithmetic — is checked without a host.  What the
  offline half cannot check is whether the sentences are *judgeable*, and that is what the
  `^:llm` tier at the bottom is for: it is the only thing that says a real reader
  understood the question.

  The invariant that matters most is the dull one: **nothing here writes**.  A judge that
  could retract what it disagreed with would be a model editing the knowledge base with no
  reviewer, which is the one thing this repo's whole LLM design refuses."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.llm.ollama :as ollama]
            [vaelii.impl.llm.oracle :as oracle]
            [vaelii.impl.llm.score :as score]
            [vaelii.impl.llm.stub :as stub]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private N 'CxNaturalWorld)

(defn- derived-claims [kb] (oracle/claims kb (score/derived-handles kb N)))

(defn- judged
  "Run the judge over `claims` with a scripted answer."
  [claims verdicts]
  (oracle/judge claims {:provider (stub/provider {:script [{:verdicts verdicts}]})}))

;; ---- what gets asked ----------------------------------------------------

(tu/deftest-kb a-claim-is-the-kbs-own-sentence-not-a-paraphrase
  (let [cs (derived-claims kb)]
    (is (seq cs))
    (testing "every claim carries the sentence it was composed from"
      (is (every? #(some? (:sentence %)) cs))
      (is (every? #(= N (:context %)) cs)))
    (testing "and the English is composed, so nothing arrived from a model"
      (is (every? #(contains? #{:composed :partial :named} (:source %)) cs))
      (is (some #(= :composed (:source %)) cs)))))

(tu/deftest-kb a-derived-claim-is-shown-its-situation-and-never-its-rule
  ;; (warmBlooded Ann) is not judgeable on its own — nobody knows Ann.  With the fact it
  ;; rests on in front of it, it is an ordinary question about people.
  (let [warm (first (filter #(= '(warmBlooded Ann) (:sentence %)) (derived-claims kb)))]
    (is (some? warm))
    (is (= ["Ann is a human"] (:givens warm)))
    (testing "the line reads as a situation and a claim"
      (is (str/starts-with? (oracle/line warm) (str "[" (:index warm) "] Given: Ann is a human.")))
      (is (str/includes? (oracle/line warm) "Claim: Ann holds its own body temperature")))
    (testing "the rule it fired through is not in the line — that would ask about validity"
      (is (not (str/includes? (oracle/line warm) "If")))
      (is (not (str/includes? (oracle/line warm) "then"))))
    (testing "and neither are the taxonomy edges, which are vocabulary and not a situation"
      (is (not (str/includes? (oracle/line warm) "Every mammal"))))))

(tu/deftest-kb a-premise-is-shown-with-no-situation-at-all
  (let [premise (first (oracle/claims kb [(v/handle-of kb '(genl penguin bird) 'CxOrganism)]))]
    (is (empty? (:givens premise)))
    (is (= "[0] Every penguin is a bird." (oracle/line premise)))))

(tu/deftest-kb an-apposition-is-cut-out-of-a-given-and-kept-in-a-claim
  ;; A gloss defines its terms after the claim, which is what a reader of one sentence
  ;; wants and noise in front of a question.
  (let [cs (derived-claims kb)
        membership (first (oracle/claims kb [(v/handle-of kb '(human Tom) N)]))]
    (is (every? #(not (str/includes? % " — ")) (mapcat :givens cs)))
    (is (some #(= ["Tom is a human"] (:givens %)) cs)
        "the given is the membership with its definition cut off")
    (testing "the same sentence as a claim keeps whatever the KB composed"
      (is (str/starts-with? (:text membership) "Tom is a human — a biological human being")))))

(tu/deftest-kb the-prompt-is-a-function-of-the-knowledge-and-not-of-its-order
  ;; Two KBs holding the same knowledge must ask the same question, or one run cannot be
  ;; compared with the one before it.  Sorting on the glossed text is what buys that;
  ;; sorting on handles would make the prompt an artifact of assertion order.
  (let [texts (map :text (derived-claims kb))]
    (is (= (sort texts) texts))
    (testing "and the numbering runs 0..n-1 over what is actually asked"
      (is (= (range (count (derived-claims kb))) (map :index (derived-claims kb)))))))

(tu/deftest-kb a-sentence-the-kb-documents-nothing-about-is-not-put-to-a-judge
  ;; Asking about a `:named` gloss measures the prompt, not the KB — the model would be
  ;; judging our spacing of an s-expression.
  (tu/with-terms [zorks Muffet2]
    (v/assert kb (list 'dog Muffet2) N)
    (v/assert kb (list zorks Muffet2) N)
    (let [handle (v/handle-of kb (list zorks Muffet2) N)
          claim (first (oracle/claims kb [handle]))]
      (is (= :named (:source claim)))
      (is (not (oracle/judgeable? claim)))
      (let [result (oracle/judge (oracle/claims kb (conj (score/derived-handles kb N) handle))
                                 {})]
        (is (= [handle] (map :handle (:skipped result))))
        (is (every? oracle/judgeable? (:judged result)))))))

;; ---- what comes back ----------------------------------------------------

(tu/deftest-kb a-verdict-lands-on-the-claim-it-names
  (let [cs (vec (take 3 (derived-claims kb)))
        r (judged cs [[2 :false "no"] [0 :true] [1 :unsure]])]
    (is (= [:agrees :unsure :disputes] (map :verdict (:judged r))))
    (is (= [nil nil "no"] (map :note (:judged r))))
    (testing "and the claims come back in the order they were asked in"
      (is (= (map :sentence cs) (map :sentence (:judged r)))))))

(tu/deftest-kb a-claim-the-answer-skipped-is-unanswered-and-not-agreement
  (let [cs (vec (take 3 (derived-claims kb)))
        r (judged cs [[0 :true]])]
    (is (= [:agrees :unanswered :unanswered] (map :verdict (:judged r))))
    (is (= 2 (:unanswered (oracle/agreement r))))
    (testing "an unanswered claim is out of the agreed count and out of the decided one"
      (is (= 1 (:agreed (oracle/agreement r))))
      (is (= 1.0 (:decided (oracle/agreement r)))))))

(deftest a-mangled-answer-degrades-rather-than-throwing
  (testing "an item number naming no claim is dropped — a verdict with nothing to attach
            to is not evidence about anything"
    (is (= {} (oracle/parse-verdicts (stub/verdicts-text [[9 :true]]) 3)))
    (is (= {} (oracle/parse-verdicts (stub/verdicts-text [[-1 :true]]) 3))))
  (testing "a word outside the enum reads as a shrug rather than an exception"
    (is (= :unsure (:verdict (get (oracle/parse-verdicts
                                   "{\"verdicts\":[{\"item\":0,\"verdict\":\"probably\"}]}" 2)
                                  0)))))
  (testing "the words a model reaches for anyway are taken"
    (is (= :agrees (:verdict (get (oracle/parse-verdicts
                                   "{\"verdicts\":[{\"item\":0,\"verdict\":\"YES\"}]}" 2) 0))))
    (is (= :disputes (:verdict (get (oracle/parse-verdicts
                                     "{\"verdicts\":[{\"item\":0,\"verdict\":\"no\"}]}" 2) 0)))))
  (testing "a repeated item keeps the first answer"
    (is (= :agrees (:verdict (get (oracle/parse-verdicts
                                   (stub/verdicts-text [[0 :true] [0 :false]]) 2) 0)))))
  (testing "a fence, which models add unprompted even under a schema"
    (is (= :agrees (:verdict (get (oracle/parse-verdicts
                                   (str "```json\n" (stub/verdicts-text [[0 :true]]) "\n```") 2)
                                  0))))
    (testing "and prose with no JSON in it at all"
      (is (= {} (oracle/parse-verdicts "I would rather not say." 2))))))

(tu/deftest-kb the-batches-renumber-so-a-verdict-cannot-drift
  ;; Every turn's numbering starts at zero, so `item: 1` in the second batch is that
  ;; batch's second claim.  A run-wide numbering would make a model's off-by-one land on
  ;; a claim from another turn.
  (let [cs (vec (take 4 (derived-claims kb)))
        p (stub/provider {:script [{:verdicts [[0 :true] [1 :true]]}
                                   {:verdicts [[0 :false] [1 :false]]}]})
        r (oracle/judge cs {:provider p :batch-size 2})]
    (is (= 2 (:batches r)))
    (is (= [:agrees :agrees :disputes :disputes] (map :verdict (:judged r))))
    (testing "and each turn showed only its own claims"
      (is (= 2 (count (re-seq #"\[\d+\]" (get-in (first (stub/requests p))
                                                 [:messages 0 :content]))))))))

(tu/deftest-kb the-rate-over-nothing-is-no-score-rather-than-a-bad-one
  (let [empty-result (oracle/judge [] {})]
    (is (nil? (:rate (oracle/agreement empty-result))))
    (is (nil? (:decided (oracle/agreement empty-result))))
    (is (zero? (:total (oracle/agreement empty-result)))))
  (testing "and a judge that shrugs at everything has a rate but nothing decided"
    (let [cs (vec (take 2 (derived-claims kb)))
          a (oracle/agreement (judged cs [[0 :unsure] [1 :unsure]]))]
      (is (= 0.0 (:rate a)))
      (is (nil? (:decided a))))))

(tu/deftest-kb a-disagreement-is-reported-with-the-strength-the-claim-is-held-at
  ;; The reader's first question about a disputed claim is whether the KB was claiming a
  ;; universal or a default, and a derived sentex carries no strength of its own — so the
  ;; report reads the JTMS rather than an empty slot.
  (let [awake (first (filter #(= '(awake Ann) (:sentence %)) (derived-claims kb)))
        r (judged [awake] [[0 :false "people sleep"]])
        text (oracle/report r)]
    (is (= :default (:strength awake)))
    (is (str/includes? text "[default]"))
    (is (str/includes? text "people sleep"))
    (is (str/includes? text "(awake Ann)")))
  (testing "a conclusion resting on known-true content says the other thing"
    ;; Every claim above reads `:default`, and that is the KB rather than the report: the
    ;; shipped rules and the test-world's cast are both asserted at the ordinary default
    ;; strength, so nothing derived over them could be anything else.  A monotonic example
    ;; has to be built.
    (tu/with-terms [Rex]
      (v/assert kb (list 'dog Rex) N {:strength :monotonic})
      (v/assert kb '(implies (and (dog ?x)) (hasCapability ?x travelling)) N {:strength :monotonic})
      (let [travels (first (oracle/claims kb [(v/handle-of kb (list 'hasCapability Rex 'travelling) N)]))]
        (is (= :monotonic (:strength travels)))
        (is (str/includes? (oracle/report (judged [travels] [[0 :false]])) "[monotonic]"))))))

;; ---- the invariant ------------------------------------------------------

(tu/deftest-kb judging-writes-nothing
  (let [before (v/sentex-count kb)
        cs (derived-claims kb)
        r (oracle/judge cs {:provider (stub/provider
                                       {:script [{:verdicts (for [i (range 20)] [i :false])}]})})]
    (is (seq (:judged r)))
    (is (= before (v/sentex-count kb)) "not one sentex moved")
    (testing "and every claim the judge disputed is still believed"
      (doseq [c (take 5 (filter #(= :disputes (:verdict %)) (:judged r)))]
        (is (v/in? kb (:handle c)))))))

(deftest the-oracle-namespace-calls-no-writer
  ;; The source-level half of the same invariant: a namespace that never names a writer
  ;; cannot write, whatever a future edit does to its logic.
  (let [src (slurp (io/file "src/vaelii/impl/llm/oracle.clj"))]
    (doseq [writer ["v/assert" "v/retract!" "v/edit!" "v/apply-" "v/ist"]]
      (is (not (str/includes? src writer))
          (str "oracle.clj names " writer " — the judge is a read")))))

;; ---- the live tier: the agreement in docs/commonsense.md ----------------

(defn- judging-provider
  "The judging provider: **phi4:14b at the window the host is already serving**.  Both are
  pinned rather than defaulted — a different model or a different `num_ctx` makes Ollama
  evict and reload, which on a shared host costs whoever else is using it.

  A constructor and nothing else: it holds no opt-in check, and is named so it cannot be
  read as the helper that does.  Consent is the caller's, and the one caller below asks
  for it first."
  []
  (ollama/provider {:model "phi4:14b" :num-ctx 4096 :timeout-ms 600000}))

(def ^:private control-sentences
  "Five claims this ontology's own content says are false, three about kinds and two about
  things.  None of them contradicts anything stored — an asymmetric `largerThan` the other
  way round would be refused where it was written, which would measure the checker rather
  than the judge — so each is a well-formed, storable, believed sentence that happens not
  to be true.

  They are the **control group**, and without one the headline number is not a
  measurement: a judge that answers `true` to everything scores exactly as well as a judge
  that is reading, on a run made only of sound conclusions."
  '[(largerThan mouse horse)
    (partType bird fin)
    (partType tree feather)
    (not (mortal Rex99))
    (eats Kibble Muffet)])

(defn- controls!
  "Assert the control claims into a scratch context beneath the world and return their
  handles.  A context of their own, so the judged set is one batch a judge cannot tell
  apart while nothing false is mixed into a theory anybody else reads."
  [kb]
  (v/assert kb '(genlCx CxControl CxWell) 'CxWell)
  (v/assert kb '(dog Rex99) 'CxControl)
  (mapv #(v/assert kb % 'CxControl) control-sentences))

(deftest ^:llm a-live-model-judges-what-the-kb-concluded
  (cond
    (not (tu/live-llm?))
    (println "\nSKIP live oracle — set VAELII_LLM_LIVE=1 to opt in")

    (not (ollama/available?))
    (println (str "\nSKIP live oracle — no Ollama at " (ollama/base-url)
                  " — set VAELII_OLLAMA_HOST to point at one"))

    :else
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (starter/load-into kb)
      (world/load-into kb)
      (let [planted (set (controls! kb))
            cs (oracle/claims kb (into (score/derived-handles kb N) planted))
            t0 (System/currentTimeMillis)
            r (oracle/judge cs {:provider (judging-provider) :num-ctx 4096 :batch-size 20})
            elapsed (- (System/currentTimeMillis) t0)
            {sound false control true} (group-by #(contains? planted (:handle %)) (:judged r))
            a (oracle/agreement (assoc r :judged sound))
            c (oracle/agreement (assoc r :judged control))]
        (println (format "\nphi4:14b judged %d claims in %d batches, %d ms"
                         (:total (oracle/agreement r)) (:batches r) elapsed))
        (println "\nthe KB's own conclusions:\n" (oracle/report (assoc r :judged sound)))
        (println "\nthe planted falsehoods:\n" (oracle/report (assoc r :judged control)))
        ;; every control, verdict and all — which falsehood a judge let through is worth
        ;; more to a reader than the count of the ones it caught
        (doseq [{:keys [verdict text note]} (sort-by :text control)]
          (println (format "  %-9s %s%s" (name verdict) text
                           (if note (str "  — " note) ""))))
        (is (pos? (:total a)))
        (is (< (:unanswered a) (:total a))
            "a judge that answered nothing at all is a broken prompt, not a verdict")
        (is (pos? (:agreed a))
            "agreement with none of it means the claims are not reaching the judge as
             sentences — the number to read is in the report above, not in this bound")
        (is (= (count control-sentences) (:total c))
            "every control was put to the judge")
        (is (pos? (:disputed c))
            "a judge that disputes none of the planted falsehoods is not reading them,
             and the agreement above is then a measurement of nothing")
        (is (< (:agreed c) (:agreed a))
            "and it agrees with the sound conclusions more readily than with the false
             ones — the whole claim this run makes")))))
