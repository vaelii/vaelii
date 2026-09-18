;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-reasoning-test
  "`/reasoning` — the gallery of worked examples.

  The page's whole claim is that it is *computed*, so these tests attack the two ways a
  gallery like this normally lies. It must **added no work to look at**: every read-only
  card is answered on render, so rendering the page has to leave the KB byte-identical.
  And it must **name what it reasons from**: each card links the stored sentexes behind
  its verdict, and a card whose sentexes are absent has to say so instead of answering.

  What each card actually answers is `examples_test`'s business — that one runs the
  table against the KB. This one is about the page."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.examples :as ex]
            [vaelii.browser.sandbox :as sandbox]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

(use-fixtures :once
  (fn [f]
    (let [kb (tu/fresh)]
      (tu/load-starter! kb)
      (binding [tu/*kb* kb, *app* (web/app kb)] (f))
      (tu/clear-kb! kb))))
(use-fixtures :each (tu/neutral))

(defn- GET [uri] (*app* {:request-method :get :uri uri :headers {}}))

(defn- text-of
  "The page as a reader sees it — a rendered sentence is a nest of role-coloured links,
  so a test asking what the page *says* asks it of the text and not of the markup."
  [body]
  (-> body (str/replace #"<[^>]+>" " ") (str/replace #"\s+" " ")))

(defn- card
  "One example's card, sliced out by its id so an assertion about one card cannot be
  satisfied by a neighbour."
  [body id]
  (let [i (str/index-of body (str "id=\"ex-" id "\""))
        j (when i (str/index-of body "<section class=\"ex-card\"" (inc i)))]
    (when i (subs body i (or j (count body))))))

;; ---- it renders, and it is a read ---------------------------------------

(deftest the-gallery-renders-every-group
  (let [r (GET "/reasoning")]
    (is (= 200 (:status r)))
    (doseq [g ex/groups]
      (is (str/includes? (:body r) g) (str "group " g)))
    (testing "and every example has a card"
      (doseq [e ex/examples]
        (is (some? (card (:body r) (:id e))) (:id e))))))

(deftest the-gallery-is-reachable-from-the-header-and-the-front-page
  (is (str/includes? (:body (GET "/")) "href=\"/reasoning\""))
  (is (re-find #"class=\"menubar\"[\s\S]{0,400}href=\"/reasoning\"" (:body (GET "/")))))

(tu/deftest-kb looking-at-the-gallery-writes-nothing
  ;; the read-only cards are answered on every render.  A page that grew the KB each
  ;; time it was opened would be a bug nobody notices until the store fills up — and the
  ;; sandbox cards must not be established just by being looked at, either
  (let [before-sx (v/sentex-count kb)
        before-j  (count (v/violations kb))]
    (dotimes [_ 3] (GET "/reasoning"))
    (is (= before-sx (v/sentex-count kb)))
    (is (= before-j (count (v/violations kb))) "and derived nothing that had to be dropped")))

;; ---- what a card shows --------------------------------------------------

(tu/deftest-kb a-read-only-card-shows-its-verdict-and-the-level-that-gave-it
  (let [c (card (:body (GET "/reasoning")) "genl-chain")
        t (text-of c)]
    (is (str/includes? t "Answered") "the KB was actually asked")
    (is (str/includes? t "at level 5") "and the card names the machinery that answered")
    (testing "a closure answer says outright that there is no record to link"
      (is (str/includes? t "No record"))
      (is (not (str/includes? c "/why/"))))))

(tu/deftest-kb a-card-links-the-sentexes-it-reasons-from
  ;; the line that makes the page checkable: every claim on a card is about these
  ;; handles, and a reader can open each one
  (let [c (card (:body (GET "/reasoning")) "arg-preserving")
        h (v/handle-of kb '(largerThan mammal insect) 'CxSize)]
    (is (nat-int? h))
    (is (str/includes? c (str "/sentex/" h))
        "the premise the inheritance runs from is linked, not merely described")
    (is (not (str/includes? (text-of c) "not in this KB")))))

(tu/deftest-kb a-derived-answer-links-its-proof
  (let [c (card (:body (GET "/reasoning")) "metadata-to-type")]
    (is (str/includes? c "/why/") "a card with a record offers the whole proof")
    (is (str/includes? (text-of c) "Answered"))))

(tu/deftest-kb a-card-the-example-expects-no-answer-to-says-so
  (let [t (text-of (card (:body (GET "/reasoning")) "arg-preserving-stops"))]
    (is (str/includes? t "Not answered"))
    (is (str/includes? t "that is what the example is about")
        "an expected non-answer is the finding, not a failure")))

(tu/deftest-kb a-card-whose-sentexes-this-kb-lacks-does-not-answer
  ;; the honest failure mode, driven through the page rather than the table: retract
  ;; what a card reasons from and the card stops claiming
  (tu/with-terms [nowhere Zork]
    (with-redefs [ex/examples (conj (vec ex/examples)
                                    {:id "fabricated" :group "Taxonomy"
                                     :title "A card this KB cannot support"
                                     :shows "Whatever it says, the KB does not hold the sentexes it names."
                                     :rests-on [[(list nowhere Zork) 'CxWell]]
                                     :goal (list nowhere Zork) :context 'CxWell
                                     :expect :yes})]
      (let [t (text-of (card (:body (GET "/reasoning")) "fabricated"))]
        (is (str/includes? t "not in this KB") "the missing dependency is named")
        (is (str/includes? t "Not available in this KB"))
        (is (not (str/includes? t "Answered")))))))

;; ---- the ones that need individuals -------------------------------------

(defn- cookie-of [resp]
  (some-> (get-in resp [:headers "Set-Cookie"]) (str/split #";") first))

(tu/deftest-kb a-sandbox-card-offers-a-button-before-it-offers-a-verdict
  (let [c (card (:body (GET "/reasoning")) "grandparent")]
    (is (str/includes? c "Run it in my sandbox"))
    (is (not (str/includes? (text-of c) "Answered"))
        "nothing is claimed until the reader has established the premises")))

(tu/deftest-kb running-a-card-establishes-its-premises-and-answers
  (let [open   (GET "/reasoning")
        cookie (cookie-of open)
        ;; the sandbox is named by the session token, not by the page: nothing is
        ;; created until a write, so the first GET has no context to name
        sbx    (sandbox/context-for (second (str/split cookie #"=" 2)))]
    (try
      (let [r (*app* {:request-method :post :uri "/reasoning"
                      :params {"id" "grandparent"}
                      :headers {"cookie" cookie "host" "localhost:3000"}})
            c (card (:body r) "grandparent")]
        (is (= 200 (:status r)))
        (is (str/includes? (text-of c) "Answered") "the verdict replaces the button")
        (is (str/includes? c "/why/") "and the join has a proof to open")
        (testing "the premises are really in the sandbox, at real handles"
          (is (some? (v/handle-of kb '(parentOf AdaEx BenEx) sbx)))
          (is (some? (v/handle-of kb '(grandparentOf AdaEx CalEx) sbx))
              "and the conclusion was derived, not asserted"))
        (testing "re-running stores nothing further"
          (let [n (v/sentex-count kb)]
            (*app* {:request-method :post :uri "/reasoning"
                    :params {"id" "grandparent"}
                    :headers {"cookie" cookie "host" "localhost:3000"}})
            (is (= n (v/sentex-count kb))))))
      (finally (when sbx (sandbox/reset! kb sbx))))))

(deftest the-write-is-origin-checked-like-every-other
  ;; a page on another site must not be able to make this browser's KB do work
  (is (= 403 (:status (*app* {:request-method :post :uri "/reasoning"
                              :params {"id" "grandparent"}
                              :headers {"host" "localhost:3000"
                                        "origin" "http://evil.example"}})))))
