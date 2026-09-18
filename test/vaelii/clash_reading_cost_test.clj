;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.clash-reading-cost-test
  "What a reading of the standing clashes costs, as counts.  Two claims, both exact
  integers rather than durations, for `assert_cost_test`'s reason — a call count is a
  property of the algorithm where a millisecond is a property of the box.  `lein perf`'s
  `standing-clash-reading` bounds the *ratio* over a growing standing set, and a ratio
  divides out a constant factor per report, so neither claim below is reachable from it.

  ## One: the reader arity builds the hidden predicate once per call

  `core/contradictions`'s reader arity keeps an entry only where the reader believes every
  member, and belief there is `res/excepted?` — `hidden-fn`, which reads the `except`
  roster and the reader's `genlCx` ancestor set to build a predicate, then answers a
  handle with a lookup.  Asked per member it builds that predicate `2 x reports` times per
  reading and throws each one away; asked once for the reading it builds one.  Pinned at
  **1** below, at two sizes, so the count is a property of the call and not of the KB.

  ## Two: the disagreement reports are built once per settle, not once per read

  A report reads a sentence and the supporting justifications of every side and sorts
  them on content, which is why `settle/record-clashes!` publishes the ordinary ones once
  per settle.  The reports for a nogood whose vantages disagreed cannot be published that
  way — a settle whose region does not reach the pair weighs it in no round — so
  `disagreement-reports` builds them from the roster at read time and caches them beside
  the per-reader withdrawals.  Pinned below at **one build per settle**: the first reading
  after a settle builds the pair's report, and every later reading builds nothing."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.settle :as settle]
            [vaelii.test-util :as tu]))

;; ---- one: the hidden predicate per reading -------------------------------

(defn- hidden-fn-builds
  "`res/hidden-fn` calls made while `f` runs.  Redefined rather than instrumented, because
  building the predicate is what costs and the engine carries no counter for it."
  [f]
  (let [calls (atom 0)
        orig  res/hidden-fn]
    (with-redefs [res/hidden-fn (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(def ^:private builds-per-reading
  "Hidden predicates a reader's `contradictions` builds: one for the reading."
  1)

(defn- dilemma-world!
  "n standing P/-P dilemmas in `cx`, plus one believed `except` over a decoy, so the
  reader's `hidden-fn` is a predicate rather than the nil an unexcepting KB answers."
  [kb cx n]
  (v/with-deferred-settle kb
    (let [decoy (v/assert kb '(crc_decoy CrcDecoy) cx {:strength :monotonic})]
      (v/assert kb (list 'except (list 'sentexHandle decoy)) cx {:strength :monotonic}))
    (dotimes [i n]
      (let [s (list (symbol (str "crc_p" i)) (symbol (str "CrcX" i)))]
        (v/assert kb s cx {})
        (v/assert kb (list 'not s) cx {})))))

(deftest a-reader-s-clash-reading-builds-one-hidden-predicate-whatever-it-reads
  (doseq [n [4 40]]
    (testing (str n " standing dilemmas")
      (let [kb (tu/isolated-fresh)]
        (try
          (tu/with-shipped-config
            (tu/with-terms [CxCrcHold CxCrcRead]
              (v/assert kb (list 'genlCx CxCrcHold 'CxUniverse) 'CxUniverse)
              (v/assert kb (list 'genlCx CxCrcRead CxCrcHold) 'CxUniverse)
              (dilemma-world! kb CxCrcHold n)
              ;; one reading outside the count, so the measured one is not a first call
              (v/contradictions kb CxCrcRead)
              (is (= n (count (v/contradictions kb CxCrcRead)))
                  "the reader must read every dilemma, or the count below measures nothing")
              (is (= builds-per-reading
                     (hidden-fn-builds #(v/contradictions kb CxCrcRead))))))
          (finally (tu/clear-kb! kb)))))))

;; ---- two: the disagreement reports per settle ----------------------------

(defn- clash-report-builds
  "`settle/clash-report` calls made while `f` runs."
  [f]
  (let [calls (atom 0)
        orig  @#'settle/clash-report]
    (with-redefs-fn {#'settle/clash-report (fn [& args] (swap! calls inc) (apply orig args))}
      (fn [] (f)))
    @calls))

(defn- types! [kb & ts]
  (doseq [t ts] (v/assert kb (list 'genl t 'thing) 'CxUniverse)))

(deftest the-disagreement-reports-are-built-once-per-settle-and-not-once-per-read
  ;;   CxUniverse
  ;;     +- CxCrcA      (crc_cat CrcRex) default, and monotonic through a rule
  ;;     +- CxCrcB      (crc_dog CrcRex) default, and monotonic through a rule
  ;;     +- CxCrcH1     (except (sentexHandle (crc_cat_src CrcRex)))
  ;;     +- CxCrcH2     (except (sentexHandle (crc_dog_src CrcRex)))
  ;;   CxCrcW1 - sees CxCrcA CxCrcB CxCrcH1, so it defeats cat
  ;;   CxCrcW2 - sees CxCrcA CxCrcB CxCrcH2, so it defeats dog
  ;;   CxCrcZ  - sees both vantages, reads two verdicts and takes neither
  (tu/with-neutral-kb [kb #(doto (v/open-kb (assoc tu/scratch-space :constraints :arbitrate))
                             (tu/clear-kb!))]
    (tu/with-terms [CxCrcA CxCrcB CxCrcH1 CxCrcH2 CxCrcW1 CxCrcW2 CxCrcZ
                    crc_cat crc_dog crc_cat_src crc_dog_src CrcRex]
      (types! kb crc_cat crc_dog)
      (doseq [c [CxCrcA CxCrcB CxCrcH1 CxCrcH2]]
        (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
      (doseq [[vantage hide] [[CxCrcW1 CxCrcH1] [CxCrcW2 CxCrcH2]]
              up             [CxCrcA CxCrcB hide]]
        (v/assert kb (list 'genlCx vantage up) 'CxUniverse))
      (doseq [up [CxCrcW1 CxCrcW2]] (v/assert kb (list 'genlCx CxCrcZ up) 'CxUniverse))
      (v/assert kb (list crc_cat CrcRex) CxCrcA)
      (v/assert kb (list 'set/forwardRule (list 'implies (list crc_cat_src '?x)
                                                (list crc_cat '?x)))
                CxCrcA {:strength :monotonic})
      (let [cat-src (v/assert kb (list crc_cat_src CrcRex) CxCrcA {:strength :monotonic})]
        (v/assert kb (list crc_dog CrcRex) CxCrcB)
        (v/assert kb (list 'set/forwardRule (list 'implies (list crc_dog_src '?x)
                                                  (list crc_dog '?x)))
                  CxCrcB {:strength :monotonic})
        (let [dog-src (v/assert kb (list crc_dog_src CrcRex) CxCrcB {:strength :monotonic})]
          (v/assert kb (list 'except (list 'sentexHandle cat-src)) CxCrcH1
                    {:strength :monotonic})
          (v/assert kb (list 'except (list 'sentexHandle dog-src)) CxCrcH2
                    {:strength :monotonic})
          (v/assert kb (list 'disjoint crc_dog crc_cat) 'CxUniverse)))
      (testing "the disagreement is on the roster, or the counts below measure nothing"
        (is (= 1 (count (filter :vantages (v/contradictions kb))))))
      (testing "the first reading after a settle builds the pair's report"
        ;; the `disjoint` assert above settled, and the reading on the roster above is a
        ;; 1-arity one, which builds them too — so an unrelated assert puts the cache
        ;; back in the state a settle leaves it
        (v/assert kb '(crc_unrelated CrcU) 'CxUniverse {})
        (is (pos? (clash-report-builds #(v/contradictions kb CxCrcZ)))))
      (testing "every later reading builds nothing"
        (is (zero? (clash-report-builds #(v/contradictions kb CxCrcZ))))
        (is (zero? (clash-report-builds #(v/contradictions kb))))
        (is (zero? (clash-report-builds #(v/contradictions kb CxCrcW1)))))
      (testing "a settle that moves belief discards the cache, so the next reading rebuilds"
        (v/assert kb '(crc_unrelated2 CrcU2) 'CxUniverse {})
        (is (pos? (clash-report-builds #(v/contradictions kb CxCrcZ))))))))
