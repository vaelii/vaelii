;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.exempt-reads-test
  "The read walk asks of every handle of a support which of its `nogood` justifications
  the reader exempts (`except/exempt-justifications`) whenever a placement can be exempt
  somewhere (`except/exemption-reads?`).  Only a placed `(contradicts …)` or `defeat`
  holds such a justification, so a handle with none is answered off the network and its
  record is not read: on a postgres store each such read is a round trip, per handle of
  the support of every membership a mint reads.

  Held here: the answer at every handle and reader is the one read with the record
  fetched first, and a handle with no `nogood` justification fetches no record."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private M {:strength :monotonic})

(defn- exempting-kb
  "Placed defeats over default facts heading a forward chain, and a
  `siblingDisjointException` beside the placed `(contradicts …)`, so placements can be
  exempt."
  []
  (let [kb (tu/fresh)]
    (v/assert kb '(genlCx CxErSub CxPerf) 'CxUniverse M)
    (v/with-deferred-settle kb
      (v/assert kb '(genl er_s1 thing) 'CxPerf M)
      (v/assert kb '(genl er_s2 thing) 'CxPerf M)
      (v/assert kb '(siblingDisjointException er_s1 er_s2) 'CxPerf M)
      (v/assert-rule kb '[(er_p ?x)] '(er_q ?x) 'CxPerf {:direction :forward})
      (dotimes [i 6]
        (let [x (symbol (str "ErX" i))]
          (v/assert kb (list 'er_p x) 'CxPerf {})
          (v/assert kb (list 'not (list 'er_p x)) (if (even? i) 'CxPerf 'CxErSub) M))))
    kb))

(defn- fetched-first
  "`exempt-justifications` as it read before: the record of `x` fetched, then each branch
  reading the `nogood` justifications."
  [{:keys [kb tms recs up] :as st} x]
  (let [s       (:sentence (p/get-sentex recs x))
        exempt? #(decide/exempt-at? kb % up (#'exc/unseen-fn st))
        js      (#'exc/nogood-justifications tms x)]
    (if (and (seq? s) (= 'contradicts (first s)))
      (when (and (seq js) (exempt? (into #{} (map sx/handle-id) (rest s))))
        (into #{} (map :id) js))
      (when-let [l (#'exc/defeat-target* s)]
        (into #{} (keep (fn [[j ms]] (when (exempt? ms) (:id j)))) (#'exc/member-sets st x l))))))

(deftest a-handle-with-no-nogood-justification-reads-no-record
  (tu/with-cleared-kb [kb #(exempting-kb)]
    (let [tms (reasoning/tms kb)
          hs  (sort (jtms/datums tms))]
      (is (exc/exemption-reads? kb))
      (is (some #(seq (#'exc/nogood-justifications tms %)) hs) "the KB holds placements")
      (doseq [ctx '[CxPerf CxErSub]]
        (let [st (#'exc/reader-state kb ctx)]
          (is (:exempting? st))
          (doseq [h hs]
            (is (= (fetched-first st h) (#'exc/exempt-justifications st h)) (str ctx " " h))
            (when (empty? (#'exc/nogood-justifications tms h))
              (prof/start)
              (#'exc/exempt-justifications st h)
              (is (zero? (get-in (prof/stop) [:fetches :sentex] 0))
                  (str "no record read for " h " at " ctx)))))))))
