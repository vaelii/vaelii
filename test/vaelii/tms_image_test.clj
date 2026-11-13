;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.tms-image-test
  "The dense network's byte image (`dense/write-image` / `dense/read-image!`).  A network
  read back from an image holds exactly the network that wrote it, and behaves the same
  under every later operation — the second half matters as much as the first, because a
  posting reloaded in the wrong form, or a column reloaded without its default, answers
  identically until the next write.

  The operation streams are the dense oracle's (`jtms_dense_oracle_test`): randomized
  premises, justifications, defeats, blocks, supersessions, retractions and sweeps."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.jtms :as jtms]
            [vaelii.jtms-dense-oracle-test])
  (:import [java.io ByteArrayInputStream ByteArrayOutputStream DataInputStream DataOutputStream]))

(def ^:private gen-ops #'vaelii.jtms-dense-oracle-test/gen-ops)
(def ^:private apply-op! #'vaelii.jtms-dense-oracle-test/apply-op!)

(defn- image-bytes ^bytes [t]
  (let [bo (ByteArrayOutputStream.)]
    (dense/write-image t (DataOutputStream. bo))
    (.toByteArray bo)))

(defn- from-bytes [^bytes b]
  (dense/read-image! (dense/create-dense-tms) (DataInputStream. (ByteArrayInputStream. b))))

(defn- build [seed n]
  (let [t   (dense/create-dense-tms)
        ops (gen-ops (java.util.Random. seed) n 12)]
    (doseq [op ops] (apply-op! t op))
    [t (into #{} (keep #(when (= :justify (first %)) (second %))) ops)]))

(defn- built [seed n] (first (build seed n)))

(defn- without-touched [snap] (dissoc snap :touched :touched-in :touched-new :touched-out))

(deftest proof-readings-survive-images-and-network-copies
  (let [t (dense/create-dense-tms)
        reading {:nonplacing #{1} :label-only #{1} :reader 'CxPrivate}
        j (jtms/->just 10 'rule [1] 2 '{?x A} :monotonic nil reading)]
    (jtms/add-premise t 1 :monotonic)
    (jtms/add-justification t j)
    (let [loaded (from-bytes (image-bytes t))
          copied (dense/copy-into! (dense/create-dense-tms) t)]
      (doseq [r [loaded copied]]
        (is (= reading (:reading (jtms/justification r 10))))
        (is (= (without-touched (jtms/snapshot t))
               (without-touched (jtms/snapshot r))))
        ;; Reusing an id with an unannotated record must clear the sparse column.
        (jtms/drop-justification! r 10)
        (jtms/add-justification r (jtms/->just 10 'rule [1] 2 nil :monotonic))
        (is (nil? (:reading (jtms/justification r 10)))))
      (is (= reading (:reading (jtms/justification t 10)))))))

(defn- result= [a b]
  (if (map? a)
    (and (= (set (:removed-sentexes a)) (set (:removed-sentexes b)))
         (= (set (:removed-justifications a)) (set (:removed-justifications b))))
    (= a b)))

(deftest a-reloaded-network-holds-the-network-that-wrote-it
  (doseq [seed (range 1 121)]
    (let [t (built seed 80)
          r (from-bytes (image-bytes t))]
      (is (= (without-touched (jtms/snapshot t)) (without-touched (jtms/snapshot r)))
          (str "seed " seed))
      (is (empty? (:touched (jtms/snapshot r))) "a reloaded network starts its touched set empty"))))

(deftest a-reloaded-network-answers-every-later-operation-alike
  (doseq [seed (range 1 81)]
    (let [[t issued] (build seed 80)
          r (from-bytes (image-bytes t))]
      (jtms/reset-touched! t)
      (doseq [[k op] (map-indexed vector (gen-ops (java.util.Random. (+ 50000 seed)) 60 12))]
        ;; the continuation issues justification ids from 1000 up, as the first stream
        ;; did.  An id the first stream issued is skipped whether or not it is still live:
        ;; the engine never re-binds an id (the oracle's `gen-ops`), and a re-bound one is
        ;; the inconsistent graph whose answer depends on map iteration order
        (when-not (and (= :justify (first op)) (contains? issued (second op)))
          (let [a (apply-op! t op) b (apply-op! r op)]
            (is (result= a b) (str "seed " seed " op " k " " op))
            (is (= (jtms/snapshot t) (jtms/snapshot r)) (str "seed " seed " op " k " " op))))))))

(deftest equal-networks-write-equal-bytes
  (let [t (built 7 80)
        b (image-bytes t)]
    (is (java.util.Arrays/equals b (image-bytes t)) "two images of one network")
    (is (java.util.Arrays/equals b (image-bytes (from-bytes b))) "an image of its own reload")))

(deftest a-misuse-throws
  (let [b (image-bytes (built 3 40))]
    (testing "into a network that already holds nodes"
      (is (thrown? IllegalStateException
                   (dense/read-image! (built 4 10) (DataInputStream. (ByteArrayInputStream. b))))))
    (testing "bytes that are not an image"
      (is (thrown? IllegalArgumentException (from-bytes (byte-array 64)))))))
