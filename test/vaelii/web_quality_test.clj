;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-quality-test
  "The health report (`/quality`): `kb-quality` run as a read job from the page's button,
  its seven readings rendered from the job's reading alone, and the attached-daemon case."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.access :as acc]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.host.serve :as serve]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

(def ^:private never-fired
  "More never-firing rules than the reading's default list cap of 25, so the page's list
  is capped."
  30)

;; CxUniverse holds `never-fired` rules `(implies (qsrc_N ?x) (qdst_N ?x))` and no fact of
;; any `qsrc_N`, so none fires.
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/empty-kb) tu/load-core!)]
      (doseq [i (range never-fired)]
        (v/assert kb (list 'implies (list (symbol (str "qsrc_" i)) '?x)
                           (list (symbol (str "qdst_" i)) '?x))
                  'CxUniverse))
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f)
             (finally
               (jobs/reset-registry!)
               (catalog/reset-registry!)
               (tu/clear-kb! kb)))))))

(defn- GET [uri] (*app* {:request-method :get :uri uri}))

(defn- POST [uri] (*app* {:request-method :post :uri uri :scheme :http :params {} :headers {}}))

(defn- run-report!
  "Press the run button and wait for the job it started; answer the settled job."
  []
  (POST "/quality/run")
  (jobs/wait (:id (first (jobs/jobs))) 60000))

(defn- reading [j] (:quality (meta (:summary j))))

(deftest the-page-renders-every-reading-in-the-report-order
  (let [j        (run-report!)
        q        (reading j)
        body     (:body (GET "/quality"))
        headings (map second (re-seq #"(?m)^## (.+)$" (v/quality-report q)))]
    (is (= :done (:status j)))
    (is (= 7 (count headings)))
    (is (= headings
           (filter (set headings)
                   (map #(-> % (str/replace #"(?s)<button.*?</button>" "")
                             (str/replace #"<[^>]+>" "") str/trim)
                        (re-seq #"(?s)<h2 class=\"panel-title\">.*?</h2>" body))))
        "one framed region per reading, in quality-report's order, under its headings")
    (is (re-find #"Read \d{4}-\d\d-\d\d \d\d:\d\d from <b>Base KB</b>" body)
        "the page names when the reading finished and which catalog entry it read")
    (testing "a listed handle is a link to its sentex"
      (doseq [{h :handle} (:never (:rules q))]
        (is (str/includes? body (str "href=\"/sentex/" h "\"")))))
    (testing "a capped list says how many it left out, from the reading's count"
      (is (= 25 (count (:never (:rules q)))))
      (is (str/includes? body (str "showing 25 of " (:never-count (:rules q))))))))

(deftest a-page-load-runs-no-reading
  (let [body (:body (GET "/quality"))]
    (is (str/includes? body "No reading of"))
    (is (str/includes? body "action=\"/quality/run\""))
    (is (empty? (jobs/jobs)) "no job ran"))
  (testing "the statistics page and the quality page link each other"
    (is (str/includes? (:body (GET "/stats")) "href=\"/quality\""))
    (is (str/includes? (:body (GET "/quality")) "href=\"/stats\""))))

(deftest a-cancelled-reading-leaves-no-reading-on-the-page
  (let [real @#'jobs/progress-fn
        j    (with-redefs-fn
               {#'jobs/progress-fn
                (fn [id cancel]
                  (let [p (real id cancel)]
                    (fn [m]
                      (when (= :taxonomy (:phase m)) (jobs/cancel! id))
                      (p m))))}
               run-report!)
        body (:body (GET "/quality"))]
    (is (= :cancelled (:status j)))
    (is (nil? (reading j)))
    (is (str/includes? body "It filed no reading."))
    (is (not (str/includes? body "panel-title")) "no reading's region is rendered")))

(deftest an-unregistered-kb-reads-no-reading-of-another-unregistered-kb
  (catalog/reset-registry!)
  (let [other (v/open-kb tu/plain-memory-space)]
    (try
      (is (= :done (:status (run-report!))))
      (is (str/includes? (:body (GET "/quality")) "Rules that never fire"))
      (is (str/includes? (:body ((web/app other) {:request-method :get :uri "/quality"}))
                         "No reading of"))
      (finally (v/clear! other)))))

(deftest a-cross-origin-run-is-refused
  (is (= 403 (:status (*app* {:request-method :post :uri "/quality/run" :scheme :http
                              :params {} :headers {"origin" "http://evil.example"
                                                   "host" "localhost"}}))))
  (is (empty? (jobs/jobs))))

(deftest an-attached-reading-runs-on-the-daemon-and-offers-no-cancel
  (let [server (serve/start tu/*kb* {:port 0 :token nil})]
    (try
      (binding [*app* (web/app (acc/remote "localhost" (serve/port server)))]
        (let [j (run-report!)]
          (is (= :done (:status j)))
          (is (= (:total (:rules (v/kb-quality tu/*kb*))) (:total (:rules (reading j)))))
          (is (string? (:no-cancel j)) "the job carries the reason it offers no cancel")
          (is (str/includes? (:body (GET "/quality")) "Rules that never fire"))))
      (finally (.stop ^org.eclipse.jetty.server.Server server)))))
