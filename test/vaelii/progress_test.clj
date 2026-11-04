;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.progress-test
  "The progress lines of a long loop (`vaelii.impl.progress`), read off a captured
  `*log-fn*` under a clock the test moves."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [taoensso.trove :as trove]
            [vaelii.impl.logging :as logging]
            [vaelii.impl.progress :as progress]))

(defn- run-loop
  "The messages a loop of `n` ticks over `total` logs when each tick takes `step-s`
  seconds of the test's clock."
  [n total step-s]
  (let [now (atom 0)
        out (atom [])]
    (binding [trove/*log-fn* (fn [_ns _coords _level id payload]
                               (swap! out conj [id (:msg (force payload))]))]
      (with-open [r (progress/start ::loop "the loop" total {:clock #(deref now)})]
        (dotimes [_ n]
          (swap! now + (long (* step-s 1e9)))
          (progress/tick! r))))
    @out))

(deftest a-loop-ending-before-the-first-line-logs-nothing
  (is (= [] (run-loop 14 14 1))))

(deftest a-line-each-time-the-elapsed-time-doubles-and-a-closing-line
  (let [msgs (map second (run-loop 100 100 1))]
    (is (= ["the loop: 15 of 100 (15%), 15 s in, about 1.4 min left"
            "the loop: 30 of 100 (30%), 30 s in, about 1.2 min left"
            "the loop: 60 of 100 (60%), 1.0 min in, about 40 s left"
            "the loop: done, 100 in 1.7 min"]
           msgs))
    (is (every? #{::loop} (map first (run-loop 100 100 1))))))

(deftest lines-stand-at-most-max-gap-apart
  (let [msgs (map second (run-loop 3000 nil 1))
        secs (map #(Long/parseLong (str/replace (second (re-find #": ([\d,]+) done" %)) "," ""))
                  (butlast msgs))]
    (is (= [15 30 60 120 240 540 840 1140 1440 1740 2040 2340 2640 2940] secs))
    (is (str/includes? (first msgs) "1/s"))))

(deftest a-projected-total-that-halves-logs-a-line-outside-the-schedule
  ;; one item a second for 60 s, then 100 a second: the projected total time (elapsed
  ;; plus left) falls from 2.8 h to 8 min at 75 s and halves again at 102 s
  (let [now  (atom 0)
        out  (atom [])
        rate (concat (repeat 60 1) (repeat 99 100) [40])]
    (binding [trove/*log-fn* (fn [_ns _coords _level _id payload]
                               (swap! out conj (:msg (force payload))))]
      (with-open [r (progress/start ::loop "the loop" 10000 {:clock #(deref now)})]
        (doseq [n rate]
          (swap! now + 1000000000)
          (progress/tick! r n))))
    (is (= ["the loop: 15 of 10,000 (0%), 15 s in, about 2.8 h left"
            "the loop: 30 of 10,000 (0%), 30 s in, about 2.8 h left"
            "the loop: 60 of 10,000 (1%), 1.0 min in, about 2.8 h left"
            "the loop: 1,560 of 10,000 (16%), 1.3 min in, about 6.8 min left"
            "the loop: 4,260 of 10,000 (43%), 1.7 min in, about 2.3 min left"
            "the loop: 6,060 of 10,000 (61%), 2.0 min in, about 1.3 min left"
            "the loop: done, 10,000 in 2.7 min"]
           @out))))

(deftest a-step-that-ticks-nothing-logs-on-the-timer
  (let [now (atom 0)
        out (atom [])]
    (binding [trove/*log-fn* (fn [_ns _coords _level _id payload]
                               (swap! out conj (:msg (force payload))))]
      (with-open [r (progress/start ::step "the step" nil {:clock #(deref now)})]
        (reset! now 15000000000)
        (#'progress/on-timer! r (fn []))
        (reset! now 20000000000)
        (#'progress/on-timer! r (fn []))))
    (is (= ["the step: 15 s in" "the step: done in 20 s"] @out))))

(deftest the-timer-logs-to-the-log-fn-bound-where-the-reporter-started
  ;; the task runs on a thread of its own, outside the binding, as the timer runs it
  (let [now (atom 0)
        out (atom [])]
    (with-open [r (progress/start ::step "the step" nil {:clock #(deref now) :timer? false})]
      (let [task (binding [trove/*log-fn* (fn [_ns _coords _level _id payload]
                                            (swap! out conj (:msg (force payload))))]
                   (#'progress/timer-task r))]
        (reset! now 15000000000)
        (doto (Thread. ^Runnable task) (.start) (.join))))
    (is (= ["the step: 15 s in"] @out))))

(def ^:dynamic *tag* nil)

(deftest the-timer-conveys-every-binding-to-a-log-fn-vaelii-did-not-install
  (let [now (atom 0)
        out (atom [])]
    (with-open [r (progress/start ::step "the step" nil {:clock #(deref now) :timer? false})]
      (let [task (binding [*tag*          :caller
                           trove/*log-fn* (fn [_ns _coords _level _id payload]
                                            (swap! out conj [*tag* (:msg (force payload))]))]
                   (#'progress/timer-task r))]
        (reset! now 15000000000)
        (doto (Thread. ^Runnable task) (.start) (.join))))
    (is (= [[:caller "the step: 15 s in"]] @out))))

(deftest the-timer-reads-the-binding-frame-it-was-made-in-not-a-copy
  (let [now (atom 0)
        out (atom [])]
    (with-open [r (progress/start ::step "the step" nil {:clock #(deref now) :timer? false})]
      (binding [*tag*          :made
                trove/*log-fn* (fn [_ns _coords _level _id payload]
                                 (swap! out conj [*tag* (:msg (force payload))]))]
        (let [task (#'progress/timer-task r)]
          (set! *tag* :set-after)
          (reset! now 15000000000)
          (doto (Thread. ^Runnable task) (.start) (.join)))))
    (is (= [[:set-after "the step: 15 s in"]] @out))))

(deftest the-timer-thread-keeps-no-binding-of-a-task-it-ran
  (with-open [r (progress/start ::step "the step" nil {:clock (constantly 0) :timer? false})]
    (let [task  (binding [*tag* :caller] (#'progress/timer-task r))
          after (promise)]
      (doto (Thread. ^Runnable #(do (task) (deliver after (thread-bound? #'*tag*))))
        (.start) (.join))
      (is (false? @after)))))

(deftest a-reporter-started-while-the-log-drops-info-logs-on-the-timer-once-the-level-is-raised
  ;; the dial and the root `*log-fn*` are process-wide, so both are put back
  (let [root  (.getRawRoot #'trove/*log-fn*)
        level (logging/current-level)
        now   (atom 0)
        runs  (atom [])]
    (try
      (logging/set-level :warn)
      (with-open [r (progress/start ::step "the step" nil)]
        (is (instance? java.util.concurrent.Future
                       (.get ^java.util.concurrent.atomic.AtomicReference (:timer r)))))
      (let [printed (with-out-str
                      (with-open [r (progress/start ::step "the step" nil
                                                    {:clock #(deref now) :timer? false})]
                        (let [task (#'progress/timer-task r)
                              slot ^java.util.concurrent.atomic.AtomicReference (:timer r)
                              fire #(do (some-> ^java.util.concurrent.Future (.get slot)
                                                (.cancel false))
                                        (doto (Thread. ^Runnable task) (.start) (.join))
                                        (swap! runs conj (.get slot)))]
                          (reset! now 15000000000)
                          (fire)
                          (logging/set-level :info)
                          (reset! now 30000000000)
                          (fire))))]
        (is (= ["the step: 30 s in" "the step: done in 30 s"]
               (map second (re-seq #"\d\d:\d\d:\d\d (.*)" printed))))
        (is (every? #(.isCancelled ^java.util.concurrent.Future %) @runs)
            "each fire cancels the run the fire before it scheduled, and the close cancels the last"))
      (finally
        (reset! @#'logging/dial level)
        (alter-var-root #'trove/*log-fn* (constantly root))))))

(deftest a-loop-over-no-items-schedules-no-timer
  (let [timer? (fn [total]
                 (with-open [r (progress/start ::loop "the loop" total)]
                   (let [^java.util.concurrent.atomic.AtomicReference t (:timer r)]
                     (instance? java.util.concurrent.Future (.get t)))))]
    (is (= [false true true] (map timer? [0 1 nil])))))

(deftest a-closed-loops-timer-task-leaves-the-timer-queue
  (let [^java.util.concurrent.ScheduledThreadPoolExecutor timer @#'progress/timer
        f (with-open [r (progress/start ::loop "the loop" 1)]
            (let [^java.util.concurrent.atomic.AtomicReference t (:timer r)]
              (.get t)))]
    (is (instance? java.util.concurrent.Future f))
    (is (not (.contains (.getQueue timer) f)))))

(deftest a-reload-that-keeps-an-earlier-loads-executor-still-schedules
  ;; `defonce` keeps the executor an earlier load of the namespace built, whatever its class
  (let [earlier (java.util.concurrent.Executors/newSingleThreadScheduledExecutor)]
    (try
      (with-redefs [progress/timer earlier]
        (with-open [r (progress/start ::loop "the loop" 1)]
          (let [^java.util.concurrent.atomic.AtomicReference t (:timer r)]
            (is (instance? java.util.concurrent.Future (.get t))))))
      (finally (.shutdownNow earlier)))))

(deftest ticks-from-several-threads-are-each-counted
  (with-open [r (progress/start ::loop "the loop" nil)]
    (run! deref (doall (for [_ (range 8)] (future (dotimes [_ 10000] (progress/tick! r))))))
    (is (= 80000 (.get ^java.util.concurrent.atomic.AtomicLong (:done r))))))

(deftest each-ticks-once-per-element-handed-out
  (with-open [r (progress/start ::loop "the loop" 100)]
    (is (= 4950 (reduce + (progress/each r (range 100)))))
    (is (= 100 (.get ^java.util.concurrent.atomic.AtomicLong (:done r))))))

(deftest a-running-total-counts-the-loop-up-to-it
  (with-open [r (progress/start ::loop "the loop" nil)]
    (let [f (progress/on-progress r)]
      (f {:derived 5})
      (f {:derived 3})
      (f {:derived 12})
      (is (= 12 (.get ^java.util.concurrent.atomic.AtomicLong (:done r)))))))
