;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-caches-test
  "The browser's cache screen: what it shows, what its one control does, and — the part
  legacy skipped — that anything links to it at all.

  A diagnostics page nobody can navigate to is a page nobody reads, so the links off
  `/stats`, `/kbs` and `/jobs` are asserted here rather than left to review."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.config :as config]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/fresh) core-context/load-into)]
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f) (finally (catalog/reset-registry!) (tu/clear-kb! kb)
                          ;; the cache profile is process-wide, so a scale a test set is
                          ;; put back before the next one reads a limit
                          (caches/reset-profile)))))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- POST [uri params & [headers]]
  (*app* {:request-method :post :uri uri :params params :headers (or headers {})}))

;; ---- what the screen shows ----------------------------------------------

(deftest the-screen-lists-the-caches-with-the-unit-each-one-counts
  (let [{:keys [status body]} (GET "/caches")]
    (is (= 200 status))
    (is (re-find #"id=\"caches\"" body))
    (is (re-find #"Literal matches" body))
    (is (re-find #"Symbol pool" body))
    (testing "a column of bare integers compares nothing, so every row names its unit"
      (is (re-find #"<th>Unit</th>" body))
      (is (re-find #"literals" body))
      (is (re-find #"symbols" body)))
    (testing "and the caches it cannot count are on the list rather than left off it"
      (is (re-find #"Justification dedup" body))
      (is (re-find #"built and dropped inside a single chaining run or search step" body)))))

(deftest a-per-process-counter-is-not-rendered-as-a-per-kb-one
  ;; The literal cache's entries belong to this KB and its hit counters are global across
  ;; every KB in the process. The page has to say the second, or a reader takes another
  ;; KB's work for this one's.
  (let [body (:body (GET "/caches"))]
    (is (re-find #"rates: this process" body))
    (is (re-find #"this KB" body))))

(deftest the-heap-strip-is-the-one-kbs-already-draws
  (let [body (:body (GET "/caches"))]
    (is (re-find #"id=\"kb-memory\"" body) "reused, not redrawn")))

(deftest the-panel-polls-only-while-something-is-running
  (testing "an idle process stops asking"
    (is (not (re-find #"hx-trigger=\"every" (:body (GET "/caches/rows"))))))
  (testing "and a running job is exactly when these numbers move"
    (with-redefs [jobs/running (constantly [{:id "9" :label "Load a corpus" :kind :load
                                             :status :running :writes? true
                                             :progress {:phase :records :done 12}}])]
      (let [body (:body (GET "/caches/rows"))]
        (is (= 200 (:status (GET "/caches/rows"))))
        (is (re-find #"hx-trigger=\"every 2s\"" body))
        (is (re-find #"id=\"caches\"" body))))))

;; ---- the profiler -------------------------------------------------------

(deftest with-the-dependency-absent-the-page-says-so-rather-than-linking-nowhere
  ;; `lein test` runs without the `:repl` profile, so this is the absent case, and it is
  ;; the one worth pinning: a dead link to a port nothing is listening on is the failure
  ;; a `requiring-resolve` call site exists to avoid.
  (let [body (:body (GET "/caches"))]
    (is (re-find #"<h3>Profiler</h3>" body))
    (is (re-find #"Not on the classpath" body))
    (is (not (re-find #"localhost:8080" body)))))

(deftest the-profiler-ui-starts-once-however-many-callers-ask-at-once
  ;; Two entry points call `start-profiler`, and a namespace reload calls it again — but a
  ;; read of the state followed by a start is two steps, and two threads both pass the read
  ;; before either has started anything.  The second start then binds the port the first is
  ;; already listening on, which is the thing the state exists to prevent.  Eight threads
  ;; released from one latch, and the dependency stubbed so nothing real binds a port.
  (let [starts (atom 0)
        gate   (java.util.concurrent.CountDownLatch. 1)
        state  @#'web/profiler-state]
    (try
      (with-redefs-fn {#'config/profiler?      (constantly true)
                       #'web/profiler-serve-ui (constantly (fn [_port] (swap! starts inc)))}
        (fn []
          (let [threads (into [] (repeatedly 8 #(doto (Thread. ^Runnable
                                                       (fn [] (.await gate)
                                                         (web/start-profiler)))
                                                  (.start))))]
            (.countDown gate)
            (doseq [^Thread t threads] (.join t 30000)))))
      (is (= 1 @starts) "one UI, whoever asked")
      (is (= {:port (config/profiler-port)} @state) "and the state names the port it is on")
      (finally (reset! state nil)))))

(deftest a-profiler-that-would-not-start-leaves-the-claim-free
  ;; The claim is released on the way out of a failed start: nothing holds the port, so a
  ;; later call — the other entry point, or a reload — must be free to try again rather
  ;; than find the state permanently claimed by an attempt that started nothing.
  (let [attempts (atom 0)
        state    @#'web/profiler-state]
    (try
      (with-redefs-fn {#'config/profiler?      (constantly true)
                       #'web/profiler-serve-ui (constantly (fn [_port]
                                                             (swap! attempts inc)
                                                             (throw (java.net.BindException. "in use"))))}
        (fn []
          (web/start-profiler)
          (is (nil? @state) "the failed start put the state back")
          (web/start-profiler)
          (is (= 2 @attempts) "so the next caller got its turn")))
      (finally (reset! state nil)))))

;; ---- the clear ----------------------------------------------------------

(deftest the-clear-is-post-only-and-origin-checked
  (testing "refuses a cross-origin caller"
    (is (= 403 (:status (POST "/caches/clear" {}
                          {"host" "localhost:3000" "origin" "http://evil.example"})))))
  (testing "and is not reachable by navigation"
    (is (= 405 (:status (GET "/caches/clear"))))))

(deftest the-clear-says-what-it-dropped-and-leaves-belief-alone
  (v/assert tu/*kb* '(genl dog animal) 'CxCore)
  (doall (v/prove tu/*kb* '(genl dog ?x) 'CxCore))
  (let [{:keys [status body]} (POST "/caches/clear" {})]
    (is (= 200 status))
    (is (re-find #"Dropped" body))
    (is (re-find #"No belief moved" body))
    (is (re-find #"id=\"caches\"" body) "and answers with the page it changed"))
  (is (v/ask? tu/*kb* '(genl dog animal) 'CxCore)
      "nothing that was believed stopped being believed")
  (testing "the copy names the rows a clear leaves alone rather than hard-coding them"
    (let [body (:body (GET "/caches"))
          kept (->> (v/caches tu/*kb*) (remove :clearable?) (map :label))]
      (is (seq kept))
      (is (re-find #"Left alone: " body))
      (doseq [label kept]
        (is (str/includes? body label))))))

(deftest the-clear-says-where-it-reaches-past-this-kb
  ;; The literal cache's rates are the process's, and the button does not touch them —
  ;; `clear-caches` is called with no opts, so `:counters?` stays off. A control beside
  ;; a process-wide rate has to say the rate keeps running, and say it from the rows
  ;; rather than from a cache named in prose that would outlive it.
  (let [body (:body (GET "/caches"))
        wide (->> (v/caches tu/*kb*)
                  (filter #(and (:clearable? %) (= :process (:counters %))))
                  (map :label))]
    (is (seq wide))
    (is (re-find #"Wider than this KB: " body))
    (doseq [label wide]
      (is (str/includes? body label)))
    (is (re-find #"drops this KB&apos;s entries alone and leaves those counters running" body))
    (is (re-find #"zeroing them is clear-caches&apos; :counters\? option" body)
        "and names the API option that does reach them, which is what a reader who
        wanted the rates zeroed goes looking for")))

(deftest a-cache-that-cannot-be-read-renders-as-unreadable-not-as-empty
  ;; In a column of dashes the two are indistinguishable, and the page is worth most
  ;; while something is already wrong.
  (let [reg @#'caches/registry]
    (try
      (caches/register-cache
       {:cache :probe-web-unreadable :label "Probe cache" :scope :kb :unit "probes"
        :limit nil :counters nil :note "a probe."
        :read (fn [_] (throw (ex-info "the read blew up" {})))})
      (let [{:keys [status body]} (GET "/caches")]
        (is (= 200 status) "one broken row does not take the page down")
        (is (re-find #"Probe cache" body))
        (is (re-find #"Could not be read \(ExceptionInfo: the read blew up\)" body))
        (is (re-find #"Literal matches" body) "and every other row still rendered"))
      (finally (swap! reg dissoc :probe-web-unreadable)))))

;; ---- the scale ----------------------------------------------------------

(deftest the-scale-control-is-post-only-and-origin-checked
  (testing "refuses a cross-origin caller"
    (is (= 403 (:status (POST "/caches/scale" {"scale" "0.5"}
                          {"host" "localhost:3000" "origin" "http://evil.example"})))))
  (testing "and is not reachable by navigation"
    (is (= 405 (:status (GET "/caches/scale"))))))

(deftest setting-the-scale-moves-every-counted-limit-and-says-so
  (let [{:keys [status body]} (POST "/caches/scale" {"scale" "0.5"})]
    (is (= 200 status))
    (is (re-find #"Cache scale set to 0.5" body))
    (is (re-find #"id=\"caches\"" body) "and answers with the page it changed"))
  (is (= 0.5 (:scale (v/cache-profile))) "the process now holds the smaller bounds")
  (is (= 2048 (:limit (first (filter #(= :literal-matches (:cache %)) (v/caches tu/*kb*)))))
      "half the shipped 4096"))

(deftest a-scale-that-is-not-a-number-changes-nothing
  (let [{:keys [status body]} (POST "/caches/scale" {"scale" "big"})]
    (is (= 200 status))
    (is (re-find #"must be a number 0 or more" body))
    (is (re-find #"nothing changed" body)))
  (is (= 1.0 (:scale (v/cache-profile))) "the scale is unmoved"))

;; ---- the anchor a diagnostics page lives or dies by ----------------------

(deftest something-links-to-it
  ;; A page with no anchor pointing at it is a page nobody reads, whatever it shows.
  ;; These three are where a reader asking "why is this slow" lands.
  (doseq [uri ["/stats" "/kbs" "/jobs"]]
    (testing uri
      (is (re-find #"href=\"/caches\"" (:body (GET uri)))))))
