;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-inference-test
  "The inference debugger (`/inference`): the search tree the node engine builds for a
  goal, and the same goal under several tacticians side by side.

  One assertion is the contract and the rest are the surface: every complete tactician
  finds the same answers, and the page **verifies** that rather than asserting it.  The
  core reads behind it (`search-tree` / `compare-tacticians`) are exercised directly too,
  because a page test that agreed for the wrong reason would still be green."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

;; A four-node chain A->B->C->D and two rules concluding `anc` — one hop, one recursive —
;; so a goal has several derivations at several depths, which is what a tactician
;; comparison needs to have anything to agree about.
(use-fixtures :once
  (fn [f]
    (let [kb (tu/fresh)]
      (doseq [[a b] (partition 2 1 '[A B C D])]
        (v/assert kb (list 'edgeOf a b) 'CxSmoke))
      (v/assert-rule kb '[(edgeOf ?x ?y)] '(anc ?x ?y) 'CxSmoke {:direction :backward})
      (v/assert-rule kb '[(edgeOf ?x ?y) (anc ?y ?z)] '(anc ?x ?z) 'CxSmoke {:direction :backward})
      (binding [tu/*kb* kb, *app* (web/app kb)] (f))
      (tu/clear-kb! kb))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

;; `(anc ?x ?z)` @ CxSmoke, depth 4 — url-encoded (?→%3F, space→%20)
(def ^:private goal-qs "q=(anc%20%3Fx%20%3Fz)&ctx=CxSmoke&d=4")

;; ---- the page ------------------------------------------------------------

(deftest search-page-runs-a-goal-and-draws-the-tree
  (let [r (GET "/inference" goal-qs)]
    (is (= 200 (:status r)))
    (let [b (:body r)]
      (testing "the three sections render"
        (is (re-find #"The search, stepped through" b))
        (is (re-find #"Tacticians, side by side" b))
        (is (re-find #"The search tree" b)))
      (testing "the tree has a root node and at least one rule rewrite"
        (is (re-find #"node-0" b))          ; the root's summary anchor
        (is (re-find #"the query" b))       ; the root is the query, not a rewrite
        (is (re-find #"rule #" b)))         ; a child came off a rule
      (testing "the answers are listed and reachable back into the tree"
        (is (re-find #"#node-" b))          ; an answer links to the node it came off
        (is (re-find #"answer" b)))
      (testing "the run reports whether the tree is whole or a prefix"
        (is (re-find #"frontier emptied" b))))))  ; this small search completes

(deftest the-tacticians-agree-and-the-page-says-so-from-a-comparison
  (let [b (:body (GET "/inference" goal-qs))]
    (testing "every tactician in the default spread is tabled"
      (doseq [t ["ground-first" "cost" "depth-first" "breadth-first"]]
        (is (re-find (re-pattern t) b))))
    (testing "the identity property is verified, not merely claimed"
      (is (re-find #"verdict-agree" b))
      (is (re-find #"same answer set across every complete tactician" b))
      (is (not (re-find #"verdict-disagree" b))))
    (testing "the default ordering is marked"
      (is (re-find #"default" b)))))

(deftest search-page-without-a-goal-explains-itself
  (let [r (GET "/inference")]
    (is (= 200 (:status r)))
    (is (re-find #"A goal is a sentence" (:body r)))
    (is (re-find #"<form" (:body r)))))

(deftest search-page-rejects-a-non-goal-rather-than-500ing
  (testing "a bare term is not a goal"
    (let [r (GET "/inference" "q=anc&ctx=CxSmoke")]
      (is (= 200 (:status r)))
      (is (re-find #"Not a goal" (:body r)))))
  (testing "an unparseable goal is rendered, not thrown"
    (let [r (GET "/inference" "q=%28%28%28")]
      (is (= 200 (:status r))))))

(deftest levels-cross-links-to-the-search-for-the-same-goal
  (testing "a single-goal levels page links across"
    (let [b (:body (GET "/levels" "q=(anc%20%3Fx%20%3Fz)&ctx=CxSmoke"))]
      (is (re-find #"Step through the search for this goal" b))
      (is (re-find #"href=\"/inference\?q=" b))))
  (testing "and so does a conjunction's join-plan page"
    (let [r (GET "/levels" "q=%5B(edgeOf%20%3Fx%20%3Fy)%20(anc%20%3Fy%20%3Fz)%5D&ctx=CxSmoke")]
      (is (= 200 (:status r)))
      (is (re-find #"Step through the search for this goal" (:body r))))))

;; ---- the reads behind it -------------------------------------------------

(deftest every-complete-tactician-finds-the-same-answers
  ;; the contract: ordering is a cost decision and never a semantic one.
  (let [rows (v/compare-tacticians tu/*kb* '(anc ?x ?z) 'CxSmoke {:max-depth 4})
        done (filter #(= :complete (:status %)) rows)]
    (is (= 4 (count rows)))
    (is (= 4 (count done)) "the small search completes under every tactician")
    (is (pos? (count (:answers (first done)))) "and it finds answers")
    (is (apply = (map :answers done))
        "every complete tactician returns the same answer set")))

(deftest a-search-that-would-not-finish-reports-a-bound-not-a-hang
  ;; the node engine's termination is the depth bound and nothing else, so a generous
  ;; depth over a recursive rule must stop on the node budget rather than run away.
  (let [tree (v/search-tree tu/*kb* '(anc ?x ?z) 'CxSmoke {:max-depth 10 :node-budget 3})]
    (is (= :bounded (:status tree)))
    (is (true? (:bounded? tree)))
    (is (<= (:expanded (:stats tree)) 4) "it stopped at the budget, near 3")))

(deftest a-wall-clock-bound-reports-timeout-not-a-hang
  ;; the third bound, beside depth and the node budget: a zero-millisecond deadline stops
  ;; the run on the clock and reports :timeout rather than hanging the caller.
  (let [tree (v/search-tree tu/*kb* '(anc ?x ?z) 'CxSmoke {:max-depth 10 :max-ms 0})]
    (is (= :timeout (:status tree)))
    (is (true? (:bounded? tree)))))

(deftest every-tactician-honours-the-wall-clock-bound
  ;; compare-tacticians is bounded the same three ways, reported per row as :status.
  (let [rows (v/compare-tacticians tu/*kb* '(anc ?x ?z) 'CxSmoke {:max-depth 10 :max-ms 0})]
    (is (= 4 (count rows)))
    (is (every? #(= :timeout (:status %)) rows)
        "a zero-ms deadline times out every tactician's run")))

(deftest the-search-page-runs-under-attach-holding-no-session
  ;; the page reads only the public surface, so it renders over a KB nobody registered —
  ;; the --attach shape, where `active-kb-name` falls back to "in-process" — and carries no
  ;; state between requests.
  (let [r1 (GET "/inference" goal-qs)]
    (is (= 200 (:status r1)))
    (is (re-find #"in-process" (:body r1))
        "no active catalog entry backs it — the attach/unregistered label shows")
    (is (re-find #"The search tree" (:body r1)))
    (testing "a second identical request is independent — no session was held"
      (let [b2 (:body (GET "/inference" goal-qs))]
        (is (re-find #"The search tree" b2))))))

(deftest a-depth-the-page-cannot-read-is-refused-rather-than-defaulted
  ;; `?d=` reaching the page as nil is indistinguishable from `?d=` not being there, so a
  ;; typo ran the search at the *default* depth and drew a page that looks exactly like the
  ;; one asked for.  And the form declares `max 12`, which is a promise about the route as
  ;; much as about the control: a URL past it is refused with the range named.
  (let [base "q=(anc%20%3Fx%20%3Fz)&ctx=CxSmoke"]
    (testing "a value that is not a number names itself in the refusal"
      (let [r (GET "/inference" (str base "&d=abc"))]
        (is (= 400 (:status r)))
        (is (re-find #"<code>d</code>" (:body r)))
        (is (re-find #"abc" (:body r)))
        (is (re-find #"1 to 12" (:body r)) "and the refusal names the range the form offers")))
    (testing "so is a depth past the bound the form declares, and one below its minimum"
      (is (= 400 (:status (GET "/inference" (str base "&d=99")))))
      (is (= 400 (:status (GET "/inference" (str base "&d=0"))))))
    (testing "a depth inside the range still runs, and so does no depth at all"
      (is (= 200 (:status (GET "/inference" (str base "&d=4")))))
      (is (= 200 (:status (GET "/inference" (str base "&d=12")))))
      (is (= 200 (:status (GET "/inference" base))))
      (is (= 200 (:status (GET "/inference" (str base "&d="))))
          "an empty control is the control not being submitted, which is the default"))))

(deftest search-tree-answers-are-reachable-to-the-nodes-they-came-off
  (let [{:keys [answers nodes status]} (v/search-tree tu/*kb* '(anc ?x ?z) 'CxSmoke {:max-depth 4})
        ids (set (map :id nodes))]
    (is (= :complete status))
    (is (seq answers))
    (testing "each answer names a node in the tree"
      (is (every? #(contains? ids (:node %)) answers)))
    (testing "each node's estimate total is exactly the sum of its four terms"
      (is (every? (fn [n]
                    (let [{:keys [base size-penalty depth-term tree-term total]} (:estimate n)]
                      (= total (+ base size-penalty depth-term tree-term))))
                  nodes)))))
