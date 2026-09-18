;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-jobs-test
  "The browser's jobs screen, and the fast path that keeps a small operation feeling small:
  what `/jobs` shows, what happens to a chaining run that outlasts a request, and the
  refusal a second writer gets."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

;; The fast-path test measures wall-clock: a base KB that chains inside 250 ms.  On the
;; shipped default the entailment mints a type per declared argument position, so the base
;; KB is larger and chains more, and the run spills to a job.  The chaining runs on a job
;; thread, which reads the *root* value of `*assertive-arg-types?*` rather than any
;; test-thread binding — so this namespace pins the root off for the duration and restores
;; it.  These tests are about the job mechanism, not the entailment (`argtype-entail-test`
;; covers that).
(use-fixtures :once
  (fn [f]
    (let [orig checks/*assertive-arg-types?*]
      (alter-var-root #'checks/*assertive-arg-types?* (constantly false))
      (try (f)
           (finally (alter-var-root #'checks/*assertive-arg-types?* (constantly orig)))))))

;; `catalog/reset-registry!` cancels every job and waits for each to stop before it
;; forgets them, so by the time `tu/clear-kb!` runs no chaining thread is still writing
;; the KB it clears — a run that outlasted the fast path under load is drained here
;; rather than orphaned into the next test's writer refusal.  The check after it is the
;; claim made explicit: nothing is running when the KB is handed back.
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/fresh) core-context/load-into)]
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f)
             (finally
               (catalog/reset-registry!)
               (is (empty? (jobs/running)) "the reset left no job running")
               (tu/clear-kb! kb)))))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- POST [uri params & [headers]]
  (*app* {:request-method :post :uri uri :params params :headers (or headers {})}))

;; ---- what the screen shows ----------------------------------------------

(deftest the-screen-says-nothing-has-run-and-then-what-did
  (testing "an empty registry is a sentence, not a blank list"
    (let [body (:body (GET "/jobs"))]
      (is (= 200 (:status (GET "/jobs"))))
      (is (re-find #"Nothing has run yet" body))
      (is (not (re-find #"hx-trigger=\"every" body)) "and nothing polls")))
  (POST "/chain" {})
  ;; the fast path answers synchronously on an idle box, but under matrix load the chain can
  ;; outlast the request and still be `tag-running` when the screen is read.  This test is
  ;; about what a *finished* run shows, so wait for the one job to settle first; that the
  ;; fast path finishes inside the request is its own test below.
  (jobs/wait (:id (first (jobs/jobs))) 30000)
  (testing "a finished run is on the screen with its report and the page its result is on"
    (let [body (:body (GET "/jobs"))]
      (is (re-find #"Chain Base KB" body))
      (is (re-find #"tag-done" body))
      (is (re-find #"href=\"/stats\"" body))
      (is (not (re-find #"/jobs/cancel" body)) "a finished job offers no cancel"))))

(deftest the-header-carries-the-running-count-and-the-panel-swaps-it-out-of-band
  (testing "the way in is in the chrome, since the reader who wants it navigated away"
    (let [body (:body (GET "/"))]
      (is (re-find #"href=\"/jobs\"" body))
      (is (re-find #"id=\"job-count\"" body))
      (is (not (re-find #"job-count-on" body)) "nothing runs, so the badge is unpainted")))
  (testing "the fragment ships a fresh copy out of band, because the header sits outside
            the region a swap replaces"
    (let [body (:body (GET "/jobs/rows"))]
      (is (re-find #"id=\"jobs\"" body))
      (is (re-find #"hx-swap-oob=\"true\"[^>]*id=\"job-count\"" body))
      (is (= 1 (count (re-seq #"id=\"job-count\"" body)))
          "one element with that id, or every later swap resolves against the wrong one"))))

(deftest a-running-job-is-watched-by-the-same-self-terminating-poll-as-every-panel
  (with-redefs [jobs/running (constantly [{:id "9" :label "Load a corpus" :kind :load
                                           :status :running :writes? true
                                           :progress {:phase :records :done 12}}])
                jobs/jobs    (constantly [{:id "9" :label "Load a corpus" :kind :load
                                           :status :running :writes? true
                                           :started 0 :elapsed-ms 1200
                                           :progress {:phase :records :done 12}}])]
    (let [body (:body (GET "/jobs/rows"))]
      (is (re-find #"hx-trigger=\"every 1s\"" body))
      (is (re-find #"hx-target=\"this\"" body))
      (is (re-find #"hx-indicator=\"unset\"" body)
          "a poll is not a request the reader made, so it does not sweep the page bar")
      (is (re-find #"job-count-on" body) "and the badge counts it")
      (is (re-find #"kb-progress" body) "with the same bar a load shows on /kbs")
      (is (re-find #"/jobs/cancel" body) "and the one control that stops it"))))

;; ---- the 250 ms fast path ------------------------------------------------

(deftest a-run-that-finishes-inside-the-fast-path-answers-with-its-result
  ;; the whole point of the fast path: chaining a two-hundred-sentex KB is milliseconds, and
  ;; a tool that answered it with a spinner and a second round trip would feel slower than
  ;; the one it replaced
  (let [r (POST "/chain" {"max-derivations" "5000"})]
    (is (= 200 (:status r)))
    (is (re-find #"Forward chaining derived" (:body r)) "the stats page it changed")
    (is (not (re-find #"<h2>Jobs</h2>" (:body r))) "and no progress page at all")
    (testing "it ran as a job all the same, so it is on the screen afterwards"
      (is (= :chain (:kind (first (jobs/jobs))))))))

(deftest a-run-that-outlasts-the-fast-path-answers-with-the-jobs-screen
  ;; driven at the helper rather than through a KB big enough to be slow: the job is
  ;; released by a promise this test holds, so which branch is taken is not a timing race
  (let [release (promise)
        answer  (#'web/job-answer
                 {:kb tu/*kb* :types (delay #{})}
                 #(jobs/submit {:label "Chain Base KB" :kind :chain :writes tu/*kb*}
                               (fn [_] @release {:derived 3}))
                 (fn [_] {:status 200 :body "the result page"}))]
    (is (re-find #"<h2>Jobs</h2>" (:body answer)))
    (is (re-find #"Chain Base KB" (:body answer)))
    (is (re-find #"tag-running" (:body answer)))
    (deliver release true)
    (is (= :done (:status (jobs/wait (:id (first (jobs/jobs))) 30000))))
    (testing "and the result is where the screen said it would be"
      (is (re-find #"href=\"/stats\"" (:body (GET "/jobs")))))))

;; ---- one writer, and cancelling ------------------------------------------

(deftest a-second-writing-job-is-refused-by-a-page-naming-the-one-that-holds-the-writer
  (let [release (promise)
        id      (jobs/submit {:label "Load a corpus" :kind :load :writes true}
                             (fn [_] @release {}))]
    (try
      (let [r (POST "/chain" {})]
        (is (= 200 (:status r)) "a refusal is a page, not a status htmx would not swap")
        (is (re-find #"already running" (:body r)))
        (is (re-find #"Load a corpus" (:body r)) "and it names the holder")
        (is (re-find #"<h2>Jobs</h2>" (:body r)) "on the screen the cancel is on"))
      (finally
        (deliver release true)
        (jobs/wait id 30000)))))

(deftest cancelling-is-a-post-that-is-origin-checked-and-says-what-it-found
  ;; two promises rather than a spin loop, so which reading the stopped card shows is not
  ;; a scheduling question: the job reports once and blocks, the test waits for that
  ;; report before posting the cancel, and the report the job makes on release is the one
  ;; the flag turns into the throw.  A loop reporting until cancelled leaves the card's
  ;; reading — and whether there is one at all — decided by how far the work thread got
  ;; before the flag was set, which on a loaded box is nowhere.
  (let [release  (promise)
        reported (promise)
        id       (jobs/submit {:label "Chain Base KB" :kind :chain :writes tu/*kb*}
                              (fn [progress!]
                                (progress! {:phase :chaining :done 12})
                                (deliver reported true)
                                @release
                                (progress! {:phase :chaining :done 12})
                                {:derived 0}))]
    (is (deref reported 30000 nil) "the job reported before anything asked it to stop")
    (testing "a cross-origin caller cannot stop this process's work"
      (is (= 403 (:status (POST "/jobs/cancel" {"id" id}
                            {"host" "localhost:3000" "origin" "http://evil.example"})))))
    (testing "and it is not reachable by navigation"
      (is (= 405 (:status (GET "/jobs/cancel")))))
    (let [r (POST "/jobs/cancel" {"id" id})]
      (is (= 200 (:status r)))
      (is (re-find #"<h2>Jobs</h2>" (:body r)))
      (deliver release true)
      (let [j (jobs/wait id 30000)]
        (is (= :cancelled (:status j))
            "it stopped at a progress report, which is where a cancel lands")))
    (testing "and the screen says what landed: a stopped job reached no return value, so
              its last progress reading is the only account of what is in the KB"
      (let [body (:body (GET "/jobs"))]
        (is (re-find #"tag-cancelled" body))
        (is (re-find #"Reached <b>12</b> at chaining" body) "the reading it stopped on")
        (is (re-find #"before it stopped — that much is in the KB" body))))
    (testing "cancelling a job the registry no longer holds is reported, not an error"
      (let [r (POST "/jobs/cancel" {"id" "no-such-job"})]
        (is (= 200 (:status r)))
        (is (re-find #"No job no-such-job" (:body r)))))))

(deftest running-the-rules-as-a-job-is-still-a-run-the-kb-records
  ;; a job rather than a request changes who watches it, not what it does — and the form
  ;; says what stopping one leaves, which is the claim `forward-chain`'s own docstring
  ;; makes: the conclusions are placed as they are made, so an aborted fixpoint is a KB
  ;; holding a prefix of the run rather than a corrupt one
  (let [before (:runs (v/chain-stats tu/*kb*) 0)]
    (POST "/chain" {"max-derivations" "5000"})
    ;; the run is a job, and the request's only bounded promise is the fast path — under
    ;; load it can still be going when the request returns, so wait for it: the claim
    ;; here is what a run records, not how fast it settles
    (is (= :done (:status (jobs/wait (:id (first (jobs/jobs))) 30000))))
    (is (= (inc before) (:runs (v/chain-stats tu/*kb*))))
    (testing "and the form says what a cancel would leave behind, since a reader who stops
              one needs to know what they are left with"
      (let [body (:body (GET "/stats"))]
        (is (re-find #"name=\"max-derivations\"" body) "with the bound on the form")
        (is (re-find #"a stopped run leaves the conclusions it had already placed" body))))))
