;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-closure-test
  "A type's whole closure (`/closure`): every supertype or every subtype, drawn in rows by
  longest path, and the term page's buttons to it."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

;;            thing
;;              |
;;            top_t
;;           /     \
;;       left_t   right_t
;;           \     /
;;           base_t       and base_t ⊂ top_t stated too, which the reduced order leaves out
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/empty-kb) tu/load-core!)]
      (doseq [s '[(genl top_t thing) (genl left_t top_t) (genl right_t top_t)
                  (genl base_t left_t) (genl base_t right_t) (genl base_t top_t)]]
        (v/assert kb s 'CxUniverse))
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f)
             (finally (catalog/reset-registry!) (tu/clear-kb! kb)))))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- rows
  "The page's row list, each row as the set of term names it links."
  [body]
  (let [ol (second (re-find #"(?s)<ol class=\"closure-rows\"[^>]*>(.*?)</ol>" body))]
    (mapv #(set (map second (re-seq #">([a-z0-9_]+)</a>" %)))
          (map second (re-seq #"(?s)<li>(.*?)</li>" ol)))))

(deftest all-genls-narrow-to-thing
  (let [r (GET "/closure" "dir=genls&q=base_t")]
    (is (= 200 (:status r)))
    (is (= [#{"base_t"} #{"left_t" "right_t"} #{"top_t"} #{"thing"}] (rows (:body r)))
        "each type on the row of its longest path: top_t above both of its subtypes")
    (is (re-find #"<svg" (:body r)))
    (testing "an arrow per edge of the reduced order, not one for base_t ⊂ top_t"
      (is (= 5 (count (re-seq #"class=\"g-edge g-genl\"" (:body r))))))))

(deftest all-specs-widen-from-the-term
  (is (= [#{"top_t"} #{"left_t" "right_t"} #{"base_t"}]
         (rows (:body (GET "/closure" "dir=specs&q=top_t"))))))

(deftest the-term-page-links-both-directions
  (let [b (:body (GET "/term" "q=left_t"))]
    (is (re-find #"href=\"/closure\?dir=genls&amp;q=left_t\"" b))
    (is (re-find #"href=\"/closure\?dir=specs&amp;q=left_t\"" b)))
  (testing "a type with nothing below it gets no All specs"
    (let [b (:body (GET "/term" "q=base_t"))]
      (is (re-find #"dir=genls" b))
      (is (not (re-find #"dir=specs" b))))))

(deftest a-wide-closure-stops-at-the-cap
  (doseq [i (range 260)]
    (v/assert tu/*kb* (list 'genl (symbol (str "leaf" i "_t")) 'base_t) 'CxUniverse))
  (let [b (:body (GET "/closure" "dir=specs&q=base_t"))]
    (is (re-find #"More than 250 subtypes" b))
    (is (= 251 (reduce + (map count (rows b)))))))

(deftest a-bad-direction-or-term-is-a-400
  (is (= 400 (:status (GET "/closure" "dir=sideways&q=base_t"))))
  (is (= 400 (:status (GET "/closure" "dir=genls")))))
