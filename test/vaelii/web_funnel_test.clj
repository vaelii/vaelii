;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-funnel-test
  "The chaining funnel (`/funnel`): every forward rule and what chaining did with it —
  placed, refused (and why), or silent.  Read off the standing refusal ledger and the
  justification graph, so it needs no per-run instrumentation; the core read
  (`chain-report`) is exercised directly as well as through the page."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

;; Three forward rules, one of each kind the funnel classifies:
;;  - fires:   (p ?x) -> (q ?x), with (p A) — asserting it auto-chains and places (q A)
;;  - silent:  (unfired ?x) -> (never ?x), nothing it needs is ever believed
;;  - blocked: (bird ?x) & (not (penguin ?x)) -> (flies ?x), its negative antecedent read
;;    under a `closed_extent_predicate` grant, which a stored (penguin Opus) refuses
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/empty-kb) tu/load-core!)]
      (v/assert-rule kb '[(p ?x)] '(q ?x) 'CxFunnel {:direction :forward})
      (v/assert kb '(p A) 'CxFunnel)
      (v/assert-rule kb '[(unfired ?x)] '(never ?x) 'CxFunnel {:direction :forward})
      (v/assert kb '(closed_extent_predicate penguin) 'CxFunnel)
      (v/assert-rule kb '[(bird ?x) (not (penguin ?x))] '(flies ?x) 'CxFunnel {:direction :forward})
      ;; penguin first, so the firing is refused at its placement rather than placed and
      ;; swept; then bird, then a fixpoint to be sure
      (v/assert kb '(penguin Opus) 'CxFunnel)
      (v/assert kb '(bird Opus) 'CxFunnel)
      (v/forward-chain kb)
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f)
             (finally
               (doseq [j (jobs/running)] (jobs/cancel! (:id j)))
               (doseq [j (jobs/running)] (jobs/wait (:id j)))
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
    (testing "a blocked rule names why it is blocked"
      (is (re-find #">naf<" b))
      (is (re-find #"no antecedent set completed" b)))
    (testing "the summary counts the three kinds"
      (is (re-find #"forward rules" b))
      (is (re-find #"fire" b)))))

(deftest the-funnel-continues-like-every-other-list
  ;; a page of 20 cards, so CxUniverse's forward rules and the three above take several pages,
  ;; and every page but the last ends in a sentinel
  (with-redefs [web/funnel-render-cap 20]
    (let [href  #(second (re-find #"hx-get=\"(/funnel/rows\?offset=\d+)\"" %))
          rules #(map second (re-seq #"href=\"/sentex/(\d+)\"" %))
          n     (count (v/chain-report tu/*kb*))
          pages (loop [body (:body (GET "/funnel")), pages []]
                  (let [pages (conj pages body)]
                    (if-let [h (and (< (count pages) 100) (href body))]
                      (let [[uri qs] (str/split h #"\?")] (recur (:body (GET uri qs)) pages))
                      pages)))]
      (is (< 20 n) "more rules than one page holds")
      (is (= "/funnel/rows?offset=20" (href (first pages))) "the first page ends in a sentinel")
      (is (nil? (href (peek pages))) "and the last page ends without one")
      (testing "the pages walk every rule once"
        (let [seen (mapcat rules pages)]
          (is (= (quot (+ n 19) 20) (count pages)))
          (is (= n (count seen) (count (distinct seen)))))))))

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
    (jobs/wait (:id (first (jobs/jobs))))
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
    (testing "a blocked rule's refusal names the closed extent"
      (is (some (fn [row]
                  (some #(= :naf (:reason %)) (:refusals row)))
                blocked)))))

(deftest chain-report-counts-void-firings-apart-from-placed
  ;; an `equals` firing over a predicate the forced-monotonic set does not hold is held
  ;; void; an `unknown` consequent is dropped as not well-formed at every firing, which
  ;; `violations` reports under the rule's handle
  (let [kb tu/*kb*
        mono {:strength :monotonic}
        row  (fn [h] (select-keys (first (filter #(= h (:rule %)) (v/chain-report kb)))
                                  [:placed :void :refused :status]))]
    (tu/with-terms [PairFn Ann Bob Cal Dee linkedQuad bears grownIn AppleTree PearTree Orchard]
      (v/assert kb (list 'reifiable_function PairFn) 'CxUniverse mono)
      (v/assert kb (list 'binary_function PairFn) 'CxUniverse mono)
      (v/assert kb (list 'arity linkedQuad 4) 'CxUniverse mono)
      (let [hv (v/assert kb (list 'set/forwardOnlyRule
                                  (list 'implies (list linkedQuad '?a '?b '?c '?d)
                                        (list 'equals (list PairFn '?a '?b) (list PairFn '?c '?d))))
                         'CxUniverse mono)
            hu (v/assert kb (list 'set/forwardOnlyRule
                                  (list 'implies (list bears '?t '?o) (list 'unknown (list grownIn '?t '?o))))
                         'CxUniverse)]
        (v/assert kb (list linkedQuad Ann Bob Cal Dee) 'CxUniverse mono)
        (v/assert kb (list bears AppleTree Orchard) 'CxUniverse)
        (v/assert kb (list bears PearTree Orchard) 'CxUniverse)
        (is (= {:placed 0 :void 1 :refused 0 :status :blocked} (row hv)))
        (is (= {:placed 0 :void 0 :refused 0 :status :silent} (row hu)))
        (is (= #{[(list 'unknown (list grownIn AppleTree Orchard)) :not-well-formed]
                 [(list 'unknown (list grownIn PearTree Orchard)) :not-well-formed]}
               (into #{} (comp (filter #(= hu (:rule %))) (map (juxt :sentence :violation)))
                     (v/violations kb))))))))

(deftest chain-report-reads-a-firing-the-argument-hold-keeps-out-as-blocked
  ;; the constraint reading, under which the `arg` declaration convicts the conclusion
  (tu/without-entailing
   (let [kb tu/*kb*
         U  'CxUniverse]
     (tu/with-terms [person rock parentOf looksLike Boulder Muffet]
       (v/assert kb (list 'genl person 'thing) U)
       (v/assert kb (list 'genl rock 'thing) U)
       (let [dh (v/assert kb (list 'disjoint person rock) U)
             _  (v/assert kb (list 'arg parentOf 1 person) U)
             _  (v/assert kb (list rock Boulder) U)
             rh (v/assert-rule kb [(list looksLike '?x)] (list parentOf '?x Muffet) U {:direction :forward})
             _  (v/assert kb (list looksLike Boulder) U)
             row #(select-keys (first (filter (fn [r] (= rh (:rule r))) (v/chain-report kb)))
                               [:placed :void :refused :refusals :status])]
         (is (= {:placed 0 :void 0 :refused 1 :status :blocked
                 :refusals [{:state :blocked :reason :constraint
                             :conseq (list parentOf Boulder Muffet) :context U}]}
                (row)))
         (v/retract! kb dh)
         (is (= {:placed 1 :void 0 :refused 0 :refusals nil :status :fires} (row))
             "the retraction that lifts the conviction places the firing"))))))

(deftest chain-report-lists-a-held-conclusion-once-for-every-firing-concluding-it
  (tu/without-entailing
   (let [kb tu/*kb*
         U  'CxUniverse]
     (tu/with-terms [person rock parentOf seenBy Boulder Muffet Ann Bob]
       (v/assert kb (list 'genl person 'thing) U)
       (v/assert kb (list 'genl rock 'thing) U)
       (v/assert kb (list 'disjoint person rock) U)
       (v/assert kb (list 'arg parentOf 1 person) U)
       (v/assert kb (list rock Boulder) U)
       (let [rh (v/assert-rule kb [(list seenBy '?x '?y)] (list parentOf '?x Muffet) U {:direction :forward})]
         (v/assert kb (list seenBy Boulder Ann) U)
         (v/assert kb (list seenBy Boulder Bob) U)
         (is (= {:placed 0 :refused 1 :status :blocked
                 :refusals [{:state :blocked :reason :constraint
                             :conseq (list parentOf Boulder Muffet) :context U}]}
                (select-keys (first (filter #(= rh (:rule %)) (v/chain-report kb)))
                             [:placed :refused :refusals :status]))))))))
