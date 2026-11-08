;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-lists-test
  "The lists on `/stats`: whole-KB lists of the defeats, the contradictions, the unary
  predicates with no genl but `thing` and the held facts and rules, each run as a read job
  from its button, and its rows paged."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

;;   CxUniverse  (genl mammal_t thing) (genl dog_t mammal_t) (disjoint mammal_t reptile_t)
;;     ├─ CxL    (reptile_t Rex) default
;;     └─ CxR    (dog_t Rex) monotonic
;;   CxJ sees CxL and CxR, so the default member is defeated there.
;;   (wobbles W) and (not (wobbles W)) at one strength: a represented dilemma.
;;   lonely_t declares no genl, thingly_t only (genl thingly_t thing).
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/empty-kb) tu/load-core!)]
      (doseq [[c up] '[[CxL CxUniverse] [CxR CxUniverse] [CxJ CxL] [CxJ CxR]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse))
      (doseq [s '[(genl mammal_t thing) (genl dog_t mammal_t) (disjoint mammal_t reptile_t)
                  (unary_predicate lonely_t) (unary_predicate thingly_t)
                  (genl thingly_t thing)]]
        (v/assert kb s 'CxUniverse))
      (v/assert kb '(reptile_t Rex) 'CxL)
      (v/assert kb '(dog_t Rex) 'CxR {:strength :monotonic})
      (v/assert kb '(wobbles W) 'CxDilemma)
      (v/assert kb '(not (wobbles W)) 'CxDilemma)
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f)
             (finally
               (jobs/reset-registry!)
               (catalog/reset-registry!)
               (tu/clear-kb! kb)))))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- POST [uri params]
  (*app* {:request-method :post :uri uri :scheme :http :params params :headers {}}))

(defn- run-list [which]
  (POST "/lists/run" {"list" which}))

(deftest the-page-reads-nothing-until-a-button-is-pressed
  (let [b (:body (GET "/lists"))]
    (is (re-find #"Defeats" b))
    (is (re-find #"Contradictions" b))
    (is (re-find #"Unary predicates without a genl" b))
    (is (empty? (jobs/jobs)) "no list ran")
    (is (re-find #"(?s)<nav class=\"menubar\">.*href=\"/stats\"" (:body (GET "/")))
        "the menubar links the page holding them")))

(deftest the-stats-page-counts-the-defeats-and-contradictions-stored
  (let [b (:body (GET "/stats"))]
    (doseq [[title f] {"Defeats" 'defeat "Contradictions" 'contradicts}]
      (is (pos? (v/count-with-functor tu/*kb* f)))
      (is (re-find (re-pattern (str "<th>" title "</th><td class=\"num\">"
                                    (v/count-with-functor tu/*kb* f) "</td>"))
                   b)))
    (is (empty? (jobs/jobs)) "the counts run no list")))

(deftest a-list-a-stored-zero-empties-offers-no-button
  (let [other (v/open-kb tu/plain-memory-space)]
    (try
      (let [b (:body ((web/app other) {:request-method :get :uri "/stats"}))]
        (is (re-find #"<th>Defeats</th><td class=\"num\">0</td>" b))
        (is (not (re-find #"value=\"defeats\"" b)))
        (is (re-find #"value=\"contradictions\"" b) "inert tuples are outside the count"))
      (finally (v/clear! other)))))

(deftest an-empty-run-answers-with-the-stats-page
  (let [other (v/open-kb tu/plain-memory-space)]
    (try
      (let [r ((web/app other) {:request-method :post :uri "/lists/run" :scheme :http
                                :params {"list" "contradictions"} :headers {}})]
        (is (= 200 (:status r)))
        (is (re-find #"Contradictions: none\." (:body r)))
        (is (re-find #"<h2[^>]*>Statistics" (:body r)))
        (is (= "/stats" (get-in r [:headers "HX-Push-Url"])))
        (is (re-find #"Last run: none" (:body r)) "and the row links no empty result"))
      (finally (v/clear! other)))))

(deftest the-defeats-list-holds-the-defeated-sentex
  (let [r (run-list "defeats")
        j (first (jobs/jobs))]
    (is (= 200 (:status r)))
    (is (= :list (:kind j)))
    (is (= :done (:status j)))
    (is (= (count (v/sentexes-with-functor tu/*kb* 'defeat {:believed? true}))
           (:rows (:summary j))))
    (is (pos? (:rows (:summary j))))
    (is (re-find #"reptile_t" (:body r)))
    (is (re-find #"the defeat" (:body r)))
    (is (= (str "/lists/result?job=" (:id j)) (get-in r [:headers "HX-Push-Url"])))
    (testing "the result has a page of its own, and the lists page links it"
      (is (re-find #"reptile_t" (:body (GET "/lists/result" (str "job=" (:id j))))))
      (is (re-find #"Last run" (:body (GET "/lists")))))))

(deftest the-contradictions-list-holds-dilemmas-and-conflicts
  (run-list "contradictions")
  (let [j (first (jobs/jobs))
        b (:body (GET "/lists/result" (str "job=" (:id j))))]
    (is (= (+ (count (v/contradictions tu/*kb*)) (count (v/conflicts tu/*kb*)))
           (:rows (:summary j))))
    (is (re-find #"dilemma" b))
    (is (re-find #"wobbles" b))
    (is (not-any? :grounds (:rows (meta (:summary j)))) "the rows are read without grounds")))

(deftest the-clash-reports-leave-their-grounds-off-when-asked
  (let [kb tu/*kb*
        ds (v/contradictions kb)]
    (is (seq ds))
    (is (every? #(contains? % :grounds) ds))
    (is (= (map #(dissoc % :grounds) ds) (v/contradictions kb nil {:grounds? false})))
    (is (= (v/contradictions kb) (v/contradictions kb nil {:grounds? true})))
    (is (= (map #(dissoc % :grounds) (v/conflicts kb)) (v/conflicts kb {:grounds? false})))
    (testing "a misspelt or mistyped option is refused rather than read as the default"
      (is (= :unknown-option (:type (ex-data (try (v/conflicts kb {:grounds false})
                                                  (catch Exception e e))))))
      (is (= :unknown-option (:type (ex-data (try (v/contradictions kb nil {:grounds? "no"})
                                                  (catch Exception e e)))))))))

(deftest a-types-stored-members-are-read-off-the-index
  (let [kb tu/*kb*]
    (is (= #{'lonely_t 'thingly_t}
           (into #{} (filter '#{lonely_t thingly_t}) (v/stored-first-args kb 'unary_predicate))))
    (is (contains? (v/stored-first-args kb 'reptile_t) 'Rex)
        "a membership defeated in one context is still stored")
    (is (empty? (v/stored-first-args kb 'no_such_type_t)))))

(deftest the-orphan-list-holds-types-with-no-genl-but-thing
  (run-list "orphan-types")
  (let [j     (first (jobs/jobs))
        terms (set (map :term (:rows (meta (:summary j)))))]
    (is (= :done (:status j)))
    (is (contains? terms 'lonely_t) "no genl at all")
    (is (contains? terms 'thingly_t) "genl thing only")
    (is (not (contains? terms 'dog_t)) "a genl below thing")
    (is (not (contains? terms 'thing)) "the root is not an orphan")
    (is (re-find #"genl thing only" (:body (GET "/lists/result" (str "job=" (:id j))))))))

(deftest rows-continue-a-page-at-a-time
  (run-list "orphan-types")
  (let [j (first (jobs/jobs))
        n (:rows (:summary j))]
    (is (= 200 (:status (GET "/lists/rows" (str "job=" (:id j) "&offset=0")))))
    (is (= (min n 200)
           (count (re-seq #"<li>" (:body (GET "/lists/rows" (str "job=" (:id j) "&offset=0")))))))
    (is (= 400 (:status (GET "/lists/rows" (str "job=" (:id j) "&offset=x")))))
    (is (re-find #"gone" (:body (GET "/lists/rows" "job=nope&offset=0"))))))

(deftest a-bad-list-or-a-gone-job-is-said-so
  (is (= 400 (:status (run-list "everything"))))
  (is (empty? (jobs/jobs)))
  (is (re-find #"is gone" (:body (GET "/lists/result" "job=nope")))))

(deftest an-unregistered-kb-reads-no-list-run-of-another-unregistered-kb
  (catalog/reset-registry!)
  (let [other (v/open-kb tu/plain-memory-space)]
    (try
      (run-list "defeats")
      (jobs/wait (:id (first (jobs/jobs))) 60000)
      (is (re-find #"Last run: " (:body (GET "/lists"))))
      (is (not (re-find #"Last run: "
                        (:body ((web/app other) {:request-method :get :uri "/lists"})))))
      (finally (v/clear! other)))))

(deftest a-cross-origin-run-is-refused
  (is (= 403 (:status (*app* {:request-method :post :uri "/lists/run" :scheme :http
                              :params {"list" "defeats"}
                              :headers {"origin" "http://evil.example"
                                        "host" "localhost"}}))))
  (is (empty? (jobs/jobs))))

;; ---- the held facts and rules, which /stats offers and does not read ------------

(deftest a-stats-page-load-reads-no-held-sentex
  ;; `violations` fetches every held sentex and convicted firing from the record store and
  ;; sorts them by content: minutes on a corpus, on every load.  The page counts and lists
  ;; the filed ledger and offers the rest as a job.
  (let [scan! (fn [& _] (throw (ex-info "a /stats load read the held entries" {})))]
    (with-redefs [checks/held-argument-entries     scan!
                  checks/forced-conclusion-entries scan!]
      (let [r (GET "/stats")]
        (is (= 200 (:status r)))
        (is (re-find #"Scan for held facts and rules" (:body r)))
        (is (re-find #"action=\"/lists/run\"" (:body r)))
        (is (re-find #"value=\"held\"" (:body r)))
        (is (= 200 (:status (GET "/stats/rows" "section=violations&offset=0"))))
        (is (empty? (jobs/jobs)) "no job ran")))))

(deftest the-held-scan-is-a-read-job-listing-what-the-stats-page-does-not
  (tu/without-entailing
   (tu/with-terms [person_t rock_t parentOf Rock Mary]
     (let [kb   tu/*kb*
           fact (list parentOf Rock Mary)]
       (doseq [s [(list 'genl person_t 'thing) (list 'genl rock_t 'thing)
                  (list 'disjoint person_t rock_t) (list rock_t Rock) (list person_t Mary)
                  fact (list 'arg parentOf 1 person_t)]]
         (v/assert kb s 'CxUniverse))
       (is (not (re-find #"inert-argument" (:body (GET "/stats"))))
           "the page load lists no held fact")
       (let [r (run-list "held")
             j (first (jobs/jobs))]
         (is (= 200 (:status r)))
         (is (= [:list "held" :done] [(:kind j) (:list j) (:status j)]))
         (is (false? (:writes? j)) "it claims no writer")
         (is (= [fact] (mapv :sentence (:rows (meta (:summary j))))))
         (is (re-find #"inert-argument" (:body r))))))))
