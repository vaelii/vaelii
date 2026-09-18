;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-funnel-test
  "The chaining funnel (`/funnel`): every forward rule and what chaining did with it —
  placed, refused (and why), or silent.  Read off the standing refusal ledger and the
  justification graph, so it needs no per-run instrumentation; the core read
  (`chain-report`) is exercised directly as well as through the page."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

;; Three forward rules, one of each kind the funnel classifies:
;;  - fires:   (p ?x) -> (q ?x), with (p A) — asserting it auto-chains and places (q A)
;;  - silent:  (unfired ?x) -> (never ?x), nothing it needs is ever believed
;;  - blocked: a defeasible (bird ?x) -> (flies ?x) its own exceptWhen (penguin ?x) blocks
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/fresh) core-context/load-into)]
      (v/assert-rule kb '[(p ?x)] '(q ?x) 'CxFunnel {:direction :forward})
      (v/assert kb '(p A) 'CxFunnel)
      (v/assert-rule kb '[(unfired ?x)] '(never ?x) 'CxFunnel {:direction :forward})
      (v/assert kb (list 'exceptWhen '(penguin ?x)
                         (list 'set/defaultRule (list 'set/forwardRule (list 'implies '(bird ?x) '(flies ?x)))))
                'CxFunnel)
      ;; the exception must already hold when the rule fires, or (flies Opus) is placed and
      ;; only *later* defeated — a defeat, not a placement-time refusal, and the funnel would
      ;; read the rule as firing.  penguin first, then bird, then a fixpoint to be sure.
      (v/assert kb '(penguin Opus) 'CxFunnel)
      (v/assert kb '(bird Opus) 'CxFunnel)
      (v/forward-chain kb)
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f)
             (finally
               (doseq [j (jobs/running)] (jobs/cancel! (:id j)))
               (doseq [j (jobs/running)] (jobs/wait (:id j) 60000))
               (jobs/reset-registry!)
               (catalog/reset-registry!)
               (tu/clear-kb! kb)))))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- POST [uri params] (*app* {:request-method :post :uri uri :params params :headers {}}))

;; ---- the page ------------------------------------------------------------

(deftest funnel-page-classifies-every-forward-rule
  (let [r (GET "/funnel")
        b (:body r)]
    (is (= 200 (:status r)))
    (is (re-find #"The chaining funnel" b))
    (testing "the three states are each on the page as a status tag (not just the legend)"
      (is (re-find #">fires</span>" b))
      (is (re-find #">blocked</span>" b))
      (is (re-find #">silent</span>" b)))
    (testing "a blocked rule names why it is blocked — the category and the exception itself"
      (is (re-find #">exception<" b))
      (is (re-find #"penguin" b))                       ; the exceptWhen query, named
      (is (re-find #"no antecedent set completed" b)))
    (testing "the summary counts the three kinds"
      (is (re-find #"forward rules" b))
      (is (re-find #"fire" b)))))

(deftest funnel-links-to-the-rules-and-back-from-stats
  (testing "each rule row links to its sentex page"
    (is (re-find #"href=\"/sentex/" (:body (GET "/funnel")))))
  (testing "stats offers the way in"
    (is (re-find #"href=\"/funnel\"" (:body (GET "/stats"))))))

(deftest funnel-post-runs-a-chaining-job-and-lands-back-on-the-funnel
  (let [r (POST "/funnel" {})]
    (is (= 200 (:status r)))
    ;; the run settles inside the fast path on an idle box; wait for it either way, then the
    ;; funnel it lands on still classifies the rules
    (jobs/wait (:id (first (jobs/jobs))) 30000)
    (let [b (:body (GET "/funnel"))]
      (is (re-find #"The chaining funnel" b))
      (is (re-find #">fires<" b)))))

;; ---- the read behind it --------------------------------------------------

(deftest chain-report-classifies-fires-blocked-silent
  (let [rows   (v/chain-report tu/*kb*)
        by     (group-by :status rows)
        fires  (:fires by)
        blocked (:blocked by)
        silent (:silent by)]
    (is (seq fires)   "the p->q rule fired")
    (is (seq blocked) "the bird->flies rule was blocked")
    (is (seq silent)  "the unfired->never rule stayed silent")
    (testing "a firing rule placed at least one conclusion"
      (is (every? #(pos? (long (:placed %))) fires)))
    (testing "a silent rule placed nothing and refused nothing"
      (is (every? #(and (zero? (long (:placed %))) (= 0 (:refused %))) silent)))
    (testing "a blocked rule's refusal names the exception, and the row carries its query"
      (is (some (fn [row]
                  (some #(= :exception (:reason %)) (:refusals row)))
                blocked))
      (is (some #(seq (:excepts %)) blocked)
          "the exceptWhen query is on the row, so the page can name it"))))
