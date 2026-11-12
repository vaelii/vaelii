;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inflight-test
  "`vaelii.browser.inflight`: a page load past its wait is answered with a waiting page and
  goes on reading, a second load of it joins the first, and the finished read answers the
  load that comes back for it. Driven with a handler that blocks on a promise, so no test
  here waits on a KB."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.browser.inflight :as inflight]))

(defn- with-detach-ms [ms f]
  (let [old (System/getProperty "vaelii.browser.detach-ms")]
    (System/setProperty "vaelii.browser.detach-ms" (str ms))
    (try (f)
         (finally (if old
                    (System/setProperty "vaelii.browser.detach-ms" old)
                    (System/clearProperty "vaelii.browser.detach-ms"))))))

(defn- req
  ([uri] (req uri {}))
  ([uri headers] {:request-method :get :uri uri :query-string "q=1" :headers headers
                  :session "s1"}))

(defn- waiting [_ e] {:status 200 :body "waiting" :id (:id e)})

(defn- guarded [h] (inflight/wrap h waiting :session))

(defn- await-status [id want]
  (while (not= want (inflight/status id))
    (Thread/sleep 10))
  (inflight/status id))

(deftest a-fast-page-is-answered-as-usual
  (with-detach-ms Long/MAX_VALUE
    #(is (= {:status 200 :body "page"}
            ((guarded (fn [_] {:status 200 :body "page"})) (req "/fast"))))))

(deftest a-slow-page-is-released-joined-and-answered-from-its-finished-read
  (with-detach-ms 30
    (fn []
      (let [release (promise)
            calls (atom 0)
            h     (guarded (fn [_] (swap! calls inc) @release {:status 200 :body "slow page"}))
            first (h (req "/slow"))]
        (testing "past the wait, the waiting page"
          (is (= "waiting" (:body first)))
          (is (= :running (inflight/status (:id first)))))
        (testing "listed while it reads"
          (is (some #(= (:id first) (:id %)) (inflight/running))))
        (testing "a second load joins the read rather than starting another"
          (is (= (:id first) (:id (h (req "/slow")))))
          (is (= 1 @calls)))
        (testing "a load in another session is a read of its own"
          (h (assoc (req "/slow") :session "s2"))
          (is (= 2 @calls)))
        (deliver release true)
        (is (= :done (await-status (:id first) :done)))
        (testing "the load that comes back is answered from the finished read, once"
          (is (= "slow page" (:body (h (req "/slow")))))
          (is (= 2 @calls))
          (is (nil? (inflight/status (:id first)))))
        (testing "and the load after that reads again"
          (is (= "slow page" (:body (h (req "/slow")))))
          (is (= 3 @calls)))))))

(deftest the-read-computes-the-whole-document
  ;; so a boosted load and a plain reload share it
  (with-detach-ms Long/MAX_VALUE
    (fn []
      (let [seen (atom nil)
            h    (guarded (fn [r] (reset! seen (:headers r)) {:status 200 :body "doc"}))]
        (h (req "/page" {"hx-request" "true" "hx-boosted" "true" "accept" "text/html"}))
        (is (= {"accept" "text/html"} @seen))))))

(deftest only-a-page-load-is-guarded
  (with-detach-ms 1
    (fn []
      (let [slow (fn [_] (Thread/sleep 30) {:status 200 :body "part"})
            h    (guarded slow)]
        (testing "an htmx request for part of a page runs on its own request"
          (is (= "part" (:body (h (req "/part" {"hx-request" "true"})))))
          (is (= "part" (:body (h (req "/part" {"hx-request" "true" "hx-target" "x"}))))))
        (testing "a write, a static file and /health too"
          (is (= "part" (:body (h (assoc (req "/assert") :request-method :post)))))
          (is (= "part" (:body (h (req "/vaelii.css")))))
          (is (= "part" (:body (h (req "/health"))))))
        (testing "a boosted navigation is a page load"
          (is (= "waiting" (:body (h (req "/nav" {"hx-request" "true"
                                                  "hx-boosted" "true"}))))))))))

(deftest a-page-that-throws-throws
  (with-detach-ms Long/MAX_VALUE
    #(is (thrown-with-msg? clojure.lang.ExceptionInfo #"broken"
                           ((guarded (fn [_] (throw (ex-info "broken" {})))) (req "/bad"))))))
