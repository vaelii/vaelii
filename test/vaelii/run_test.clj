;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.run-test
  "Reading and running a run file (`vaelii.host.run`): the entries a run asserts and the
  context each asserts into.  The reads it answers, a solve read's answer sets among them,
  the refusals of a directive the reader cannot honour, and the base a run starts from."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.run :as run]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.test-util :as tu :refer [deftest-kb]]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- write-files!
  "Write each `[name text]` of `files` under `dir`, and answer the path of the first."
  [dir files]
  (doseq [[n text] files]
    (io/make-parents (io/file dir n))
    (spit (io/file dir n) text))
  (str (io/file dir (ffirst files))))

(defn- read-files
  "`read-run-file` over `files` written to a temp directory, or the refusal's ex-data."
  [files]
  (tu/with-tmp
    (fn [dir]
      (try (run/read-run-file (write-files! dir files))
           (catch clojure.lang.ExceptionInfo e (ex-data e))))))

(defn- run-lines
  "`run-in` over `kb` of a run file holding `lines`, at rule depth `depth`."
  [kb depth & lines]
  (run/run-in kb (read-files [["run.vae" (apply str (interleave lines (repeat "\n")))]]) depth))

(defn- answered
  "Each read's answer: a `#truth` read's verdict, a `#show` read's `[answers status]`."
  [{:keys [answers]}]
  (mapv #(or (:verdict %) [(:answers %) (:status %)]) answers))

(deftest a-form-asserts-into-the-context-the-last-context-directive-names
  (let [r (read-files [["zoo.vae" (str "(dog Rex)\n#context CxZoo\n(bird Tweety)\n"
                                       "#show (bird ?x)\n#context CxPark\n#truth (dog Rex)\n")]])]
    (is (= [['(dog Rex) run/default-context] ['(bird Tweety) 'CxZoo]] (:entries r)))
    (is (= [['show '(bird ?x) 'CxZoo 4] ['truth '(dog Rex) 'CxPark 6]]
           (mapv (juxt :directive :arg :context :line) (:reads r))))
    (is (= 3 (:line (meta (second (:entries r))))))
    (is (nil? (:base r)))))

(deftest an-included-file-keeps-its-context-to-itself
  (let [r (read-files [["main.vae" (str "#base core\n#context CxA\n#include \"lib/more.vae\"\n"
                                        "(cat Tom)\n#include \"CxKb.txt\"\n")]
                       ["lib/more.vae" "#base core\n(dog Rex)\n#context CxB\n(bird Tweety)\n"]
                       ["CxKb.txt" "(fish Nemo)\n"]])]
    (is (= 'core (:base r)))
    (is (= [['(dog Rex) 'CxA] ['(bird Tweety) 'CxB] ['(cat Tom) 'CxA] ['(fish Nemo) 'CxKb]]
           (:entries r)))
    (is (= 3 (count (:files r))))))

(deftest a-directive-the-reader-cannot-honour-is-refused-by-mismatch
  (doseq [[files mismatch] [[[["a.vae" "#shwo (dog ?x)\n"]] :unknown-key]
                            [[["a.vae" "(dog #show Rex)\n"]] :misplaced]
                            [[["a.vae" "#show (dog #truth Rex)\n"]] :misplaced]
                            [[["a.vae" "#context dog\n"]] :bad-value]
                            [[["a.vae" "#context CxEverything\n"]] :bad-value]
                            [[["a.vae" "#base nothing\n"]] :bad-value]
                            [[["a.vae" "#show Rex\n"]] :bad-value]
                            [[["a.vae" "#truth (dog ?x)\n"]] :bad-value]
                            [[["a.vae" "#include 3\n"]] :bad-value]
                            [[["a.vae" "#solve [:limit 3]\n"]] :bad-value]
                            [[["a.vae" "#solve {:reading :one}\n"]] :bad-value]
                            [[["a.vae" "#solve {:limit 0}\n"]] :bad-value]
                            [[["a.vae" "#solve {:project false}\n"]] :bad-value]
                            [[["a.vae" "#base core\n#base starter\n"]] :conflict]
                            [[["a.vae" "#include \"b.vae\"\n"] ["b.vae" "#include \"a.vae\"\n"]] :cycle]]]
    (testing (pr-str files)
      (is (= [:bad-directive mismatch] ((juxt :type :mismatch) (read-files files)))))))

(deftest a-solve-read-runs-under-the-last-solve-map-of-its-own-file
  (let [r (read-files [["main.vae" "#solve {:limit 2}\n#include \"more.vae\"\n#models (p ?x)\n#show (p ?x)\n"]
                       ["more.vae" "#solve {:among :all :project true}\n#brave (p ?x)\n"]])]
    (is (= [['brave {:among :all :project true}] ['models {:limit 2}] ['show nil]]
           (mapv (juxt :directive :solve) (:reads r))))))

(deftest an-include-naming-no-file-is-a-missing-resource
  (is (= :missing-resource (:type (read-files [["a.vae" "#include \"gone.vae\"\n"]])))))

(deftest-kb a-run-answers-every-read-after-every-form-is-stored
  (tu/with-terms [bird penguin flies Tweety Opus Bob CxZoo]
    (let [[fly? bird? peng?] (map #(list % '?x) [flies bird penguin])]
      (is (= [[[(list flies Tweety)] :complete] :false :true :unknown]
             (answered (run-lines kb 8
                                  (str "#context " CxZoo)
                                  (str "#show " (pr-str fly?))
                                  (pr-str (list 'genl penguin bird))
                                  (pr-str (list bird Tweety))
                                  (pr-str (list penguin Opus))
                                  (pr-str (list 'set/forwardRule
                                                (list 'exceptWhen peng? (list 'implies bird? fly?))))
                                  (pr-str (list 'implies peng? (list 'not fly?)))
                                  (str "#truth " (pr-str (list flies Opus)))
                                  (str "#truth " (pr-str (list flies Tweety)))
                                  (str "#truth " (pr-str (list flies Bob))))))))))

(deftest-kb a-show-cut-at-the-depth-reports-truncated
  (tu/with-terms [aa bb cc Xx CxChain]
    (let [lines [(str "#context " CxChain)
                 (pr-str (list 'implies (list aa '?x) (list bb '?x)))
                 (pr-str (list 'implies (list bb '?x) (list cc '?x)))
                 (pr-str (list aa Xx))
                 (str "#show " (pr-str (list cc '?x)))]]
      (is (= [[[] :truncated]] (answered (apply run-lines kb 1 lines))))
      (is (= [[[(list cc Xx)] :complete]] (answered (apply run-lines kb 2 lines)))))))

(deftest-kb a-refused-form-is-reported-at-its-line-and-no-read-is-answered
  (tu/with-terms [dog Rex]
    (let [r (run-lines kb 8 (pr-str (list dog Rex)) (pr-str (list Rex dog))
                       (str "#show " (pr-str (list dog '?x))))]
      (is (= [[2 :naming]] (mapv (juxt :line (comp :type ex-data :error)) (:refused r))))
      (is (nil? (:answers r))))))

(defn- assignment-lines
  "A run file assigning `ann` and `bob` one task each, `costOf` weighting each pairing and
  `asp/minimize` summing the weights: the optimum is ann on t1 and bob on t2, at cost 3."
  [{:keys [person task assignedTo costOf Ann Bob T1 T2 CxStaff]} & reads]
  (let [at (list assignedTo '?p '?t)]
    (concat [(str "#context " CxStaff)]
            (map pr-str
                 (concat (for [i [Ann Bob]] (list person i))
                         (for [t [T1 T2]] (list task t))
                         (for [[i t w] [[Ann T1 1] [Ann T2 3] [Bob T1 2] [Bob T2 2]]]
                           (list costOf i t w))
                         [(list 'set/assumptionRule
                                (list 'implies (list 'and (list person '?p) (list task '?t)) at))
                          (list 'asp/atLeast 1 '?t at)
                          (list 'asp/atMost 1 '?t at)
                          (list 'asp/atMost 1 '?p at)
                          (list 'asp/minimize 1 '?w (list 'and at (list costOf '?p '?t '?w)))]))
            reads)))

(deftest-kb a-solve-read-answers-from-the-optimal-answer-sets-of-its-context
  (when (solver/available?)
    (tu/with-terms [person task assignedTo costOf Ann Bob T1 T2 CxStaff]
      (let [t     {:person person :task task :assignedTo assignedTo :costOf costOf
                   :Ann Ann :Bob Bob :T1 T1 :T2 T2 :CxStaff CxStaff}
            best  [(list assignedTo Ann T1) (list assignedTo Bob T2)]
            reads (:answers (apply run-lines kb 8
                                   (assignment-lines
                                    t
                                    (str "#models " (pr-str (list assignedTo '?p '?t)))
                                    (str "#model " (pr-str (list assignedTo Bob '?t)))
                                    (str "#cautious " (pr-str (list assignedTo '?p '?t)))
                                    (str "#brave " (pr-str (list assignedTo Ann '?t))))))]
        (is (= [[[best] :optimum [3]]
                [[[(list assignedTo Bob T2)]] :optimum [3]]
                [best :optimum [3]]
                [[(first best)] :optimum [3]]]
               (mapv (juxt #(or (:answer-sets %) (:answers %)) :status :costs) reads)))
        (is (not-any? run/stopped-short? reads))))))

(deftest-kb a-solve-read-over-a-program-with-no-answer-set-is-unsat-and-complete
  (when (solver/available?)
    (tu/with-terms [person task assignedTo costOf Ann Bob T1 T2 CxStaff]
      (let [t     {:person person :task task :assignedTo assignedTo :costOf costOf
                   :Ann Ann :Bob Bob :T1 T1 :T2 T2 :CxStaff CxStaff}
            ;; two people, two tasks, and a bound of no task at all for Ann
            reads (:answers (apply run-lines kb 8
                                   (assignment-lines
                                    t
                                    (pr-str (list 'asp/atMost 0 '?t (list assignedTo Ann '?t)))
                                    (str "#models " (pr-str (list assignedTo '?p '?t)))
                                    (str "#cautious " (pr-str (list assignedTo '?p '?t))))))]
        (is (= [[[] :unsat] [[] :unsat]]
               (mapv (juxt #(or (:answer-sets %) (:answers %)) :status) reads)))
        (is (not-any? run/stopped-short? reads))))))

(deftest-kb ^:slow the-core-base-is-core-txt-and-interface-rules-and-restores-from-its-dump
  (tu/with-tmp
    (fn [dir]
      (let [counts (for [_ [:load :restore]]
                     (let [b (run/base-kb 'core dir)]
                       (try (v/sentex-count b) (finally (v/close! b)))))]
        (is (apply = counts))
        (is (< 0 (first counts) (v/sentex-count kb))
            "the upper ontology holds the core base and the domain files beside it")))))
