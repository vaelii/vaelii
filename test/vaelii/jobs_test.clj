;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jobs-test
  "The job registry: one mechanism for every long operation, and the four properties that
  make it one — a status vocabulary that does not vary by job kind, a writer claim only one
  job holds, a cancellation that never interrupts a job writing a KB, and a report that
  outlives the job without outliving its usefulness."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.jobs :as jobs]))

;; The registry is process-global, so every test starts and ends with it empty.
(use-fixtures :each (fn [f] (jobs/reset-registry!)
                      (try (f) (finally (jobs/reset-registry!)))))

(defn- settled
  "Block until job `id` settles, and answer it.  Every job below is milliseconds long or is
  released by a promise the test holds, so the deadline is a stuck-test guard rather than a
  timing assumption."
  [id]
  (jobs/wait id 30000))

;; ---- one shape, whatever the work is -------------------------------------

(deftest a-job-runs-reports-and-leaves-a-report
  (let [reached (promise)
        id      (jobs/submit {:label "Count to three" :kind :test :result-url "/stats"}
                             (fn [progress!]
                               (progress! {:phase :counting :done 2 :total 3})
                               (deliver reached true)
                               {:derived 7}))]
    (is (string? id))
    (is @reached)
    (let [j (settled id)]
      (is (= :done (:status j)))
      (is (= "Count to three" (:label j)))
      (is (= :test (:kind j)))
      (is (= {:derived 7} (:summary j)) "what the work returned is the job's report")
      (is (= "/stats" (:result-url j)))
      (is (number? (:elapsed-ms j)))
      (testing "the last reading a finished job took says it finished, rather than naming
                the phase it happened to stop in"
        (is (= :done (get-in j [:progress :phase])))
        (is (= 2 (get-in j [:progress :done])))
        (is (= 3 (get-in j [:progress :total])))))
    (testing "and the view is safe to render: no cancel flag, no future, no KB"
      (let [j (jobs/job id)]
        (is (nil? (:cancel j)))
        (is (nil? (:future j)))
        (is (nil? (:writes j)))
        (is (false? (:writes? j)))))))

(deftest a-failing-job-keeps-its-message-and-where-it-got-to
  (let [id (settled (jobs/submit {:label "Break" :kind :test}
                                 (fn [progress!]
                                   (progress! {:phase :reading :done 41})
                                   (throw (ex-info "the dump names a format this build
                                                    cannot read" {:type :unsupported-format})))))]
    (is (= :failed (:status id)))
    (is (re-find #"cannot read" (:error id)))
    (testing "a failed job's last reading is where it stopped, which is the whole of what
              it has to say about the failure"
      (is (= :reading (get-in id [:progress :phase])))
      (is (= 41 (get-in id [:progress :done]))))))

(deftest the-list-is-newest-first-and-latest-is-by-kind
  (let [a (settled (jobs/submit {:label "One" :kind :export} (constantly {})))
        b (settled (jobs/submit {:label "Two" :kind :chain} (constantly {})))
        c (settled (jobs/submit {:label "Three" :kind :export} (constantly {})))]
    (is (= ["Three" "Two" "One"] (mapv :label (jobs/jobs))))
    (is (= (:id c) (:id (jobs/latest :export))) "the newest of that kind, settled or not")
    (is (= (:id b) (:id (jobs/latest :chain))))
    (is (nil? (jobs/latest :load)))
    (is (= (:id a) (:id (jobs/job (:id a)))))
    (is (empty? (jobs/running)))))

;; ---- the fast path -------------------------------------------------------

(deftest the-fast-path-answers-with-the-job-and-the-slow-one-with-a-job-still-running
  (let [release (promise)
        id      (jobs/submit {:label "Wait for the test" :kind :test}
                             (fn [_] @release {:done true}))]
    (testing "a job that has not settled inside the window is answered as it stands —
              which is what sends a caller to the progress screen rather than to a result
              that does not exist yet"
      (is (= :running (:status (jobs/wait id 30)))))
    (deliver release true)
    (is (= :done (:status (settled id))))
    (testing "and a job that settled before the window closes is answered finished, which
              is the whole of the fast path"
      (is (= :done (:status (jobs/wait id jobs/fast-path-ms)))))))

;; ---- one writer, and the refusal names it -------------------------------

(deftest one-writing-job-at-a-time-and-the-refusal-names-the-holder
  (let [release (promise)
        kb      {::a-kb true}
        id      (jobs/submit {:label "Chain Base KB" :kind :chain :writes kb}
                             (fn [_] @release {}))]
    (is (= id (:id (jobs/writer))))
    (testing "a second job that writes is refused rather than queued: two writers are not
              serializable, and a queue would make the second one's timings meaningless"
      (let [e (try (jobs/submit {:label "Load a corpus" :kind :load :writes true}
                                (constantly {}))
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= :job-busy (:type (ex-data e))))
        (is (= id (:holder (ex-data e))) "the refusal names the job holding the writer")
        (is (re-find #"Chain Base KB" (.getMessage ^Exception e)))))
    (testing "a job that writes no KB runs beside it — an export writes the filesystem, so
              refusing it would be a rule about this process's busyness"
      (is (= :done (:status (settled (jobs/submit {:label "Export" :kind :export}
                                                  (constantly {})))))))
    (testing "the per-KB question is asked by identity, so a job filling one KB is no
              reason to refuse a write to another"
      (is (true? (jobs/writes-kb? kb)))
      (is (false? (jobs/writes-kb? {::a-kb true})) "an equal map is not the same KB")
      (is (false? (jobs/writes-kb? nil))))
    (deliver release true)
    (settled id)
    (testing "and the claim is released when the job settles"
      (is (nil? (jobs/writer)))
      (is (false? (jobs/writes-kb? kb))))))

;; ---- cancellation, in its two tiers -------------------------------------

(deftest cancelling-a-kb-writing-job-is-cooperative-and-never-an-interrupt
  (let [ticks (atom 0)
        kb    {::a-kb true}
        id    (jobs/submit {:label "Chain" :kind :chain :writes kb}
                           (fn [progress!]
                             ;; the shape every long operation in the engine has: a loop
                             ;; that reports, and stops when the report throws
                             (dotimes [_ 100000]
                               (swap! ticks inc)
                               (progress! {:phase :chaining :done @ticks}))
                             {:finished-anyway true}))]
    (is (true? (jobs/cancel! id)))
    (testing "the flag is set and the status says so before the work has noticed"
      (is (#{:cancelling :cancelled} (:status (jobs/job id)))))
    (let [j (settled id)]
      (is (= :cancelled (:status j)))
      (is (nil? (:summary j)) "it never reached its return value")
      (is (pos? @ticks) "it ran, and stopped at a progress report rather than mid-write"))))

(deftest a-job-that-writes-nothing-can-be-interrupted-as-well
  (let [id (jobs/submit {:label "Sleep" :kind :test :interruptible? true}
                        (fn [_] (Thread/sleep 60000) {:woke true}))]
    (is (true? (jobs/cancel! id)))
    (let [j (jobs/wait id 5000)]
      (is (= :cancelled (:status j))
          "an interrupt is indistinguishable from a cancellation, not as a failure")
      (is (nil? (:summary j))))))

(defn- deref-hook
  "An atom façade over `real` that answers **one** deref — the first taken by the thread
  in `armed` — with `(on-deref)`, and delegates everything else, writes included.  The
  registry is a `defonce` atom read through a var, so a façade in that var is how a test
  gets between `cancel!`'s single read of a job and what it does with what it read.  A
  race forced this way is a race that happens every run: the pre-state is snapshotted
  before the barrier and handed back afterwards, rather than raced for."
  [real armed on-deref]
  (reify
    clojure.lang.IDeref
    (deref [_] (if (compare-and-set! armed (Thread/currentThread) nil) (on-deref) @real))
    clojure.lang.IAtom
    (swap [_ f] (swap! real f))
    (swap [_ f a] (swap! real f a))
    (swap [_ f a b] (swap! real f a b))
    (swap [_ f a b args] (apply swap! real f a b args))
    (compareAndSet [_ o n] (compare-and-set! real o n))
    (reset [_ v] (reset! real v))))

(deftest a-cancel-that-lost-the-race-sends-no-interrupt-at-all
  ;; `cancel!` decides from one read of the registry, and the job can settle between that
  ;; read and the interrupt.  Past the body's unwind the thread belongs to the pool, so an
  ;; interrupt sent then lands on whatever runs next — a task nobody cancelled, unwinding
  ;; on somebody else's request.  The stale read is forced rather than waited for: the hook
  ;; hands `cancel!` the registry as it stood a moment ago, having in the meantime released
  ;; the work and waited for its future, so the job is genuinely finished by the time that
  ;; read is acted on.
  ;;
  ;; The witness is a thread of the test's own, standing for the pool thread running the
  ;; next task, because that thread's own flag is not a witness: a worker back in `getTask`
  ;; clears a stray interrupt when it wakes.  What is observable, and what the fence
  ;; promises, is that no interrupt is sent at all.
  (let [release  (promise)
        id       (jobs/submit {:label "Finishes first" :kind :test :interruptible? true}
                              (fn [_] @release {:ok true}))
        seen     (promise)
        stand-in (doto (Thread. ^Runnable
                        (fn []
                          (try (.await (java.util.concurrent.CountDownLatch. 1))
                               (catch InterruptedException _
                                 (deliver seen :interrupted)))))
                   (.setDaemon true)
                   (.start))
        real     @#'jobs/state
        armed    (atom (Thread/currentThread))
        stale    (fn []
                   (let [s @real]
                     (deliver release true)
                     (is (not= :timeout (deref (:future (get-in s [:jobs id])) 30000 :timeout))
                         "the work has unwound, and its thread is the pool's again")
                     (assoc-in s [:jobs id :thread] (doto (promise) (deliver stand-in)))))]
    (with-redefs-fn {#'jobs/state (deref-hook real armed stale)}
      (fn [] (is (true? (jobs/cancel! id)))))
    (is (= :done (:status (jobs/job id))) "the job had already finished")
    (is (= :still-waiting (deref seen 250 :still-waiting))
        "and nothing was interrupted on its behalf, the thread no longer being its own")
    (.interrupt stand-in)))

(deftest an-interrupted-canceller-restores-its-own-flag
  ;; The other side of the same bounded wait: it is interruptible, and it clears the
  ;; *caller's* flag on the way out.  Left cleared, an `InterruptedException` propagates
  ;; out of `cancel!` into the handler that called it and the interrupt is lost with it.
  ;; The hook hands the canceller a job that has not published its thread, so the wait
  ;; really waits, and the interrupt lands there.
  (let [release     (promise)
        id          (jobs/submit {:label "Never noticed" :kind :test :interruptible? true}
                                 (fn [_] @release {}))
        real        @#'jobs/state
        armed       (atom nil)
        waiting     (promise)
        outcome     (promise)
        unpublished (fn []
                      (let [s @real]
                        (deliver waiting true)
                        (assoc-in s [:jobs id :thread] (promise))))]
    (with-redefs-fn {#'jobs/state (deref-hook real armed unpublished)}
      (fn []
        (let [canceller (Thread. ^Runnable
                         (fn []
                           (let [answer (try (jobs/cancel! id)
                                             (catch Throwable t t))]
                             ;; reading the flag is also what clears it, so this
                             ;; thread dies as clean as it would have started
                             (deliver outcome [answer (Thread/interrupted)]))))]
          (reset! armed canceller)
          (.start canceller)
          (is (deref waiting 30000 nil))
          (.interrupt canceller)
          (.join canceller 30000))))
    (let [[answer flag] (deref outcome 30000 [::none ::none])]
      (is (true? answer) "the interrupt did not propagate out of `cancel!`")
      (is (true? flag) "and the flag that wait cleared was put back for the caller to read"))
    (deliver release true)
    (is (= :done (:status (settled id))))))

(deftest cancelling-a-settled-job-changes-nothing-and-answers-false
  ;; the answer is about the *run*, not about the registry: a settled job keeps its report
  ;; there for an hour, so "is the id still listed" and "was there anything to stop" are
  ;; different questions, and a caller that cannot tell them apart reports a cancellation
  ;; over a load that finished or a dump already written
  (testing "a run in progress is one to stop"
    (let [id (jobs/submit {:label "Sleep" :kind :test :interruptible? true}
                          (fn [_] (Thread/sleep 60000) {:woke true}))]
      (is (true? (jobs/cancel! id)))
      (is (= :cancelled (:status (settled id))))))
  (testing "a job that has already settled is not, though the registry still holds it"
    (let [id (settled (jobs/submit {:label "Quick" :kind :test} (constantly {:ok true})))]
      (is (false? (jobs/cancel! (:id id))))
      (is (= :done (:status (jobs/job (:id id)))) "and asking did not un-finish it")))
  (testing "and neither is an id the registry never held"
    (is (false? (jobs/cancel! "no-such-job")))))

;; ---- the report outlives the job; a running job outlives every deadline -----

(deftest a-report-ages-out-and-an-unsettled-job-never-does
  ;; `sweep` is a pure function of the registry's state, which is what makes the ages
  ;; testable without waiting an hour or reaching for a clock
  (let [t      (System/currentTimeMillis)
        hours  (fn [n] (- t (* n 60 60 1000)))
        before {:jobs  {"1" {:id "1" :status :done    :started (hours 3) :finished (hours 3)}
                        "2" {:id "2" :status :done    :started (hours 1) :finished t}
                        "3" {:id "3" :status :running :started (hours 2)}
                        "4" {:id "4" :status :running :started (hours 99)}}
                :order ["1" "2" "3" "4"]}
        after  (#'jobs/sweep before)]
    (is (= ["2" "3" "4"] (:order after)))
    (testing "a finished report ages out, so the screen is not a log"
      (is (nil? (get-in after [:jobs "1"])))
      (is (some? (get-in after [:jobs "2"]))))
    (testing "an unsettled job is kept at any age, because forgetting one is releasing its
              writer claim and a thread still running is still writing — there is no age at
              which that becomes safe"
      (is (some? (get-in after [:jobs "3"])))
      (is (some? (get-in after [:jobs "4"])) "ninety-nine hours in, and still counted"))))

(deftest the-writer-claim-survives-a-sweep-run-by-a-job-that-claims-nothing
  ;; The hole this closes, and the reason it needed a *second* job to open: `submit`'s writer
  ;; test reads the registry before the sweep in its own registration, so a writing job
  ;; could never sweep the wedged writer out of its own way — but an export claims no writer,
  ;; skips that test, and sweeps.  Dropping the wedged job there released the claim, and the
  ;; next writing job was admitted beside a thread still writing the same KB.
  (let [release (promise)
        kb      (Object.)                                 ; identity is all `writes-kb?` reads
        loader  (jobs/submit {:label "Load a corpus" :kind :load :writes kb}
                             (fn [_] @release {:ok true}))]
    (try
      ;; a hundred hours pass, and the loader's thread is exactly where it was
      (swap! @#'jobs/state update-in [:jobs loader :started] - (* 100 60 60 1000))
      (settled (jobs/submit {:label "Write a dump" :kind :export} (constantly {:files 1})))
      (testing "the export's sweep left the writer alone"
        (is (= "Load a corpus" (:label (jobs/writer))))
        (is (true? (jobs/writes-kb? kb)))
        (is (some? (jobs/job loader))))
      (testing "so a second writing job is still refused, and still names the holder"
        (let [e (try (jobs/submit {:label "Chain it" :kind :chain :writes kb} (constantly {}))
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (= :job-busy (:type (ex-data e))))
          (is (= loader (:holder (ex-data e))))))
      (finally (deliver release true) (settled loader)))))

(deftest a-job-the-registry-has-dropped-is-not-recreated-by-its-own-settling
  ;; Every write to a job is guarded, and this is the one that made the guard necessary: the
  ;; *completion* swap.  Unguarded, a job released after the registry forgot it files
  ;; `{:status :done :finished …}` under an id nothing holds — a job with no `:started`,
  ;; absent from `:order` so no listing shows it, permanent, and enough to make `job` throw
  ;; on the way to rendering it.  Neither `sweep` nor `reset-registry!` drops a running
  ;; job, so the drop is made by hand: what a job past every bound looks like to the map.
  (let [release (promise)
        id      (jobs/submit {:label "Outlives the registry" :kind :test}
                             (fn [_] @release {:done true}))
        ;; the future is the only handle left once the registry has forgotten the job
        f       (:future (get-in @@#'jobs/state [:jobs id]))]
    (swap! @#'jobs/state (fn [s] (-> s
                                     (update :jobs dissoc id)
                                     (update :order #(vec (remove #{id} %))))))
    (deliver release true)
    ;; the completion swap runs before the body returns, so a resolved future means it has
    ;; had its chance to file — no sleep, and nothing timing-dependent to assert against
    (is (not= :timeout (deref f 30000 :timeout)))
    (is (empty? (:jobs @@#'jobs/state)) "nothing was filed under an id nobody holds")
    (is (nil? (jobs/job id)) "and asking for it answers nil rather than throwing")
    (is (empty? (jobs/jobs)))))

(deftest a-progress-report-from-a-swept-job-files-nothing
  ;; the other half of the sweep: a wedged job's thread keeps reporting, and writing under
  ;; an id the registry has dropped would file half a job — a progress reading with no
  ;; `:started`, which every view then subtracts from
  (let [reported (promise)
        id       (jobs/submit {:label "Keeps talking" :kind :test}
                              (fn [progress!]
                                (deliver reported progress!)
                                (progress! {:phase :working :done 1})
                                {}))]
    (settled id)
    (let [progress! @reported]
      ;; the registry drops the job while the callback it handed out is still live, which
      ;; is what a sweep does to a wedged one
      (jobs/reset-registry!)
      (progress! {:phase :still-here :done 2})
      (is (nil? (jobs/job id)))
      (is (empty? (jobs/jobs)))
      (is (empty? (jobs/running))))))

(deftest resetting-waits-for-a-running-job-to-stop-before-forgetting-it
  ;; forgetting a job releases its writer claim, so a reset that dropped a running one
  ;; would leave its thread writing with nobody able to see it — the next writing job
  ;; admitted beside it, a test fixture clearing the KB it is still filling.  The job
  ;; here is released from another thread while the reset is waiting, and the reset
  ;; must not return until the job's thread has actually stopped.
  (let [release  (promise)
        reported (promise)
        stopped  (promise)
        id       (jobs/submit {:label "Chain it" :kind :chain :writes ::some-kb}
                              (fn [progress!]
                                (try
                                  (progress! {:phase :chaining :done 1})
                                  (deliver reported true)
                                  @release
                                  ;; the cancel the reset sent lands here
                                  (progress! {:phase :chaining :done 2})
                                  {}
                                  (finally (deliver stopped true)))))]
    (is (deref reported 30000 nil))
    (future (Thread/sleep 150) (deliver release true))
    (jobs/reset-registry!)
    (is (realized? stopped) "the reset returned only after the thread unwound")
    (is (empty? (jobs/jobs)) "and the settled job was forgotten")
    (is (nil? (jobs/writer)))
    (is (= id (jobs/submit {:label "Next" :kind :test} (constantly {})))
        "with nothing kept, the id counter restarts")
    (testing "and a writing job is admitted now that the writer is really released"
      (is (string? (jobs/submit {:label "Chain again" :kind :chain :writes ::some-kb}
                                (constantly {})))))
    (doseq [j (jobs/jobs)] (settled (:id j)))))

(deftest a-job-that-will-not-stop-is-kept-through-a-reset-and-still-holds-the-writer
  ;; the other outcome of the bounded wait: a job that never reaches a progress report
  ;; cannot be cancelled cooperatively, and a reset that forgot it would be the sweep's
  ;; forbidden drop by another name.  So it stays, still the writer, with its id reserved.
  (with-redefs-fn {#'jobs/reset-wait-ms 100}
    (fn []
      (let [release (promise)
            id      (jobs/submit {:label "Load a corpus" :kind :load :writes true}
                                 (fn [_] @release {}))]
        (try
          (jobs/reset-registry!)
          (is (= id (:id (jobs/writer))) "kept, and still this process's writer")
          (is (= :cancelling (:status (jobs/job id))) "asked to stop, and not yet stopped")
          (let [e (try (jobs/submit {:label "Chain it" :kind :chain :writes true} (constantly {}))
                       (catch clojure.lang.ExceptionInfo e e))]
            (is (= :job-busy (:type (ex-data e))) "so a second writer is still refused"))
          (is (not= id (jobs/submit {:label "Reads only" :kind :test} (constantly {})))
              "and the id counter did not restart over a kept job")
          (finally
            (deliver release true)
            (settled id)))))))

(deftest cancelling-a-settled-job-leaves-its-terminal-status
  ;; the :cancelling write goes through update-job! guarded on the job not having
  ;; settled: stamped over a just-filed :done, the job never settled, the sweep kept
  ;; it, `writer` kept naming it, and every later writing job was refused against
  ;; work that had already finished
  (let [id (jobs/submit {:label "Done already" :kind :test} (constantly {:ok true}))]
    (settled id)
    (jobs/cancel! id)
    (is (= :done (:status (jobs/job id)))
        "a settled status is terminal, whatever a late cancel asks")))
