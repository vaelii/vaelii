;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-params-test
  "The browser's parameters, read one way: absent takes the route's default, and a value
  the route cannot read is refused — a 400 page naming the parameter, or the empty
  fragment on a continuation route (docs/web.md, \"A parameter the page cannot read is a
  400, not a default\").  One row per route, since each route reads its own parameters
  and the refusal is kept or lost route by route."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.impl.caches :as caches]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

(use-fixtures :once
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (tu/load-starter! (tu/empty-kb))]
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "starter")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f)
             (finally (catalog/reset-registry!) (tu/clear-kb! kb)))))))

(use-fixtures :each
  (tu/neutral)
  (fn [f]
    (try (f)
         (finally (jobs/reset-registry!)
                  ;; the cache profile is process-wide, so a scale a test set is put back
                  (caches/reset-profile)))))

(defn- qs [m]
  (str/join "&" (for [[k x] m]
                  (str (name k) "=" (java.net.URLEncoder/encode (str x) "UTF-8")))))

(defn- GET [uri & [params]]
  (*app* (cond-> {:request-method :get :uri uri}
           (seq params) (assoc :query-string (qs params)))))

(defn- esc
  "`s` as the page's HTML writes it into text."
  [s]
  (-> (str s) (str/replace "&" "&amp;") (str/replace "\"" "&quot;")
      (str/replace "<" "&lt;") (str/replace ">" "&gt;")))

(defn- POST [uri params]
  ;; wrap-params merges into an existing :params, so a test hands the form values over
  ;; directly — the values a form POST would carry
  (*app* {:request-method :post :uri uri :scheme :http :params params}))

(def ^:private unreadable-values
  "`[label request parameter value]`: one value per route the route cannot read.  The value
  is what the page must quote back."
  [["/levels q"           #(GET "/levels" {:q "("})                        "q" "("]
   ["/levels ctx"         #(GET "/levels" {:q "(animal ?x)" :ctx "("})      "ctx" "("]
   ["/levels ctx number"  #(GET "/levels" {:q "(animal ?x)" :ctx "42"})     "ctx" "42"]
   ["/inference q"        #(GET "/inference" {:q "("})                     "q" "("]
   ["/inference ctx"      #(GET "/inference" {:q "(animal ?x)" :ctx "("})   "ctx" "("]
   ["/network ctx"        #(GET "/network" {:ctx "("})                     "ctx" "("]
   ["/network ctx number" #(GET "/network" {:ctx "42"})                    "ctx" "42"]
   ["/term q"             #(GET "/term" {:q "("})                          "q" "("]
   ["/assert q"           #(GET "/assert" {:q "("})                        "q" "("]
   ["GET /edit handles"   #(GET "/edit" {:handles "abc"})                  "handles" "abc"]
   ["GET /edit q"         #(GET "/edit" {:q "("})                          "q" "("]
   ["GET /retract"        #(GET "/retract" {:handles "1,abc"})             "handles" "1,abc"]
   ["/sentex/:id"         #(GET "/sentex/abc")                             "id" "abc"]
   ["/sentex/:id past a long" #(GET "/sentex/9223372036854775808")         "id" "9223372036854775808"]
   ["/why/:id"            #(GET "/why/abc")                                "id" "abc"]
   ["/justification/:id"  #(GET "/justification/abc")                      "id" "abc"]
   ["GET /demo first"     #(GET "/demo" {:first "abc"})                    "first" "abc"]
   ["POST /demo first"    #(POST "/demo" {"do" "start" "first" "abc"})     "first" "abc"]
   ["POST /demo do"       #(POST "/demo" {"do" "bogus"})                   "do" "bogus"]
   ["POST /reasoning id"  #(POST "/reasoning" {"id" "bogus"})              "id" "bogus"]
   ["POST /edit"          #(POST "/edit" {"handles" "abc" "text" "CxUniverse\n(genl dog animal)"})
    "handles" "abc"]
   ["POST /edit/preview"  #(POST "/edit/preview" {"handles" "abc" "text" "CxUniverse\n(genl dog animal)"})
    "handles" "abc"]
   ["POST /retract"       #(POST "/retract" {"handles" "abc"})             "handles" "abc"]
   ["POST /kbs/export variant"     #(POST "/kbs/export" {"dir" "/nonexistent-x" "variant" "xyz"})
    "variant" "xyz"]
   ["POST /kbs/export compression" #(POST "/kbs/export" {"dir" "/nonexistent-x" "compression" "xyz"})
    "compression" "xyz"]
   ["POST /caches/scale"          #(POST "/caches/scale" {"scale" "abc"})     "scale" "abc"]
   ["POST /caches/scale negative" #(POST "/caches/scale" {"scale" "-1"})      "scale" "-1"]
   ["POST /caches/scale NaN"      #(POST "/caches/scale" {"scale" "NaN"})     "scale" "NaN"]
   ["POST /caches/scale Infinity" #(POST "/caches/scale" {"scale" "Infinity"}) "scale" "Infinity"]])

(deftest every-unreadable-parameter-is-a-400-page-naming-it
  (doseq [[label request param value] unreadable-values]
    (testing label
      (let [{:keys [status body]} (request)]
        (is (= 400 status))
        (is (str/includes? body (str "<code>" param "</code>")) "the page names the parameter")
        (is (str/includes? body (str "<code>" (esc (pr-str value)) "</code>"))
            "and quotes the value it could not read")))))

(def ^:private no-default
  "`[label request parameter]`: a parameter the route exists to act on, with no default
  to fall back on, sent absent."
  [["POST /retract"       #(POST "/retract" {})       "handles"]
   ["POST /jobs/cancel"   #(POST "/jobs/cancel" {})   "id"]
   ["POST /kbs/load"      #(POST "/kbs/load" {})      "id"]
   ["POST /kbs/unload"    #(POST "/kbs/unload" {})    "key"]
   ["POST /kbs/activate"  #(POST "/kbs/activate" {})  "key"]
   ["POST /demo"          #(POST "/demo" {})          "do"]
   ["POST /reasoning"     #(POST "/reasoning" {})     "id"]
   ["POST /caches/scale"  #(POST "/caches/scale" {})  "scale"]])

(deftest a-parameter-with-no-default-is-refused-when-absent
  (doseq [[label request param] no-default]
    (testing label
      (let [{:keys [status body]} (request)]
        (is (= 400 status))
        (is (str/includes? body (str "<code>" param "</code>")))))))

(deftest nothing-is-written-on-a-value-the-route-could-not-read
  (tu/with-terms [tmpkind]
    (let [text (str "CxUniverse\n(genl " tmpkind " thing)")]
      (testing "a handle list with an element that does not read asserts nothing"
        (is (= 400 (:status (POST "/edit" {"handles" "abc" "text" text}))))
        (is (nil? (v/handle-of tu/*kb* (list 'genl tmpkind 'thing) 'CxUniverse))))
      (testing "and a handle that reads and names nothing stored is the unknown-handle
                problem, not a new sentence"
        (let [{:keys [status body]} (POST "/edit" {"handles" "999999999" "text" text})]
          (is (= 200 status))
          (is (str/includes? body "unknown-handle"))
          (is (str/includes? body "Nothing was written"))
          (is (not (str/includes? body "Saved"))))
        (is (nil? (v/handle-of tu/*kb* (list 'genl tmpkind 'thing) 'CxUniverse))))
      (testing "the preview says what the save would"
        (is (str/includes? (:body (POST "/edit/preview" {"handles" "999999999" "text" text}))
                           "unknown-handle"))))))

(deftest a-cache-scale-the-route-refuses-changes-nothing
  (doseq [raw ["abc" "-1" "NaN" "Infinity" "1e400"]]
    (is (= 400 (:status (POST "/caches/scale" {"scale" raw}))) raw))
  (is (= 1.0 (:scale (v/cache-profile))) "the scale is unmoved")
  (testing "and a finite one still sets it"
    (is (= 200 (:status (POST "/caches/scale" {"scale" "2"}))))
    (is (= 2.0 (:scale (v/cache-profile))))))

(deftest a-continuation-answers-the-empty-fragment-for-a-value-it-cannot-read
  ;; htmx swaps only a 2xx, so a 400 would leave the sentinel to be fetched again; read as
  ;; the start, an offset of `abc` appended the first page to the list being scrolled
  (let [first-page (GET "/term/rows" {:q "genl" :g "0"})]
    (is (= 200 (:status first-page)))
    (is (not (str/blank? (:body first-page))) "an absent offset is the start"))
  (doseq [[uri params] [["/term/rows"   {:q "genl" :g "0"}]
                        ["/find/rows"   {:q "a"}]
                        ["/tree/rows"   {:rel "genl" :node "thing"}]
                        ["/front/rows"  {:section "predicates"}]
                        ["/stats/rows"  {:section "contexts"}]
                        ["/levels/rows" {:q "(genl ?x thing)" :ctx "CxUniverse" :level "1"}]
                        ["/funnel/rows" {}]]
          offset ["abc" "-5"]]
    (testing (str uri " offset=" offset)
      (let [{:keys [status body]} (GET uri (assoc params :offset offset))]
        (is (= 200 status))
        (is (str/blank? body)))))
  (testing "an unreadable context on the levels continuation ends the list rather than
            continuing it as every context's"
    (let [{:keys [status body]} (GET "/levels/rows" {:q "(genl ?x thing)" :ctx "(" :level "1"})]
      (is (= 200 status))
      (is (str/blank? body)))))

(deftest an-id-the-catalog-does-not-hold-is-named-on-the-page
  (testing "a source id reaches load-source, whose refusal names the ids there are"
    (let [{:keys [status body]} (POST "/kbs/load" {"id" "nosuch"})]
      (is (= 200 status))
      (is (str/includes? body "no KB source &quot;nosuch&quot;"))))
  (doseq [route ["/kbs/unload" "/kbs/activate"]]
    (testing route
      (let [{:keys [status body]} (POST route {"key" "nosuch"})]
        (is (= 200 status))
        (is (str/includes? body "No loaded KB has the key &quot;nosuch&quot;")))))
  (is (= "base" (catalog/active)) "and the active KB is the one it was"))

(deftest a-not-found-id-quotes-the-number-it-read
  (doseq [uri ["/sentex/999999999" "/why/999999999" "/justification/999999999"]]
    (let [{:keys [status body]} (GET uri)]
      (is (= 200 status) uri)
      (is (str/includes? body "#999999999") uri))))

(deftest a-search-pattern-past-the-cap-says-it-is-too-long
  (let [q (apply str "^" (repeat 128 "a"))
        {:keys [status body]} (GET "/find" {:q q})]
    (is (= 400 status))
    (is (str/includes? body "129 characters long"))
    (is (str/includes? body "128"))
    (is (not (str/includes? body "Not a valid regular expression"))
        "the pattern is refused for its length, not as a bad regex"))
  (testing "a pattern that does not compile says so, as a 400"
    (let [{:keys [status body]} (GET "/find" {:q "["})]
      (is (= 400 status))
      (is (str/includes? body "Not a valid regular expression")))))

(deftest a-page-swaps-its-own-400-into-main
  ;; `bad-parameter`'s page is what a form on the page gets back when it sends a value the
  ;; route refuses, and htmx swaps only a 2xx unless the script says otherwise
  (let [js (slurp (io/resource "public/vaelii.js"))]
    (is (str/includes? js "htmx:beforeSwap"))
    (is (re-find #"status === 400 && d\.target && d\.target\.id === \"main\"" js))))
