;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bound-value-domains-test
  "Every bound refuses a value outside its domain, by name, at every entry point that
  takes one.

  The key sets were already checked everywhere (`opts/check!`): an option nothing reads is
  `:unknown-option`.  The **value** domains are the other half — a key that *is* read
  holding a value it cannot mean.  Unchecked, the value reaches arithmetic or a call and
  throws a bare `ClassCastException`, which the daemon answers `:internal-error` (500)
  where every sibling refusal is a typed 400.  `opts/bound-domains` is the one table these
  entry points share, and `opts/check-values!` reads it; this holds each entry point to it.

  A bound of **0** is not a bad value — no time at all, no rule expansion, realize nothing
  and hand back a resumable continuation, report at every opportunity — so it is admitted
  where the entry point's own contract admits it, and only a value that is not a number of
  the right kind at all is refused."
  (:require [clojure.test :refer [deftest is testing]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(defn- bad-value?
  "Is the refusal a value refusal — `:unknown-option` with `:mismatch :bad-value`?"
  [d]
  (and (= :unknown-option (:type d)) (= :bad-value (:mismatch d))))

;; ---- the read entry points ------------------------------------------------

(deftest a-search-bound-outside-its-domain-is-refused-by-name
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf anc Ann Bob CxBVD]
      (v/assert kb (list parentOf Ann Bob) CxBVD)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxBVD
                     {:direction :backward})
      (let [g (list anc Ann '?z)]
        (testing "prove / provable? refuse a bad :max-ms, :max-depth and :refuse-depth-cut?"
          (doseq [opts [{:max-ms "x"} {:max-ms :soon} {:max-depth -1} {:max-depth "x"}
                        {:max-depth 1.5} {:max-depth 2 :refuse-depth-cut? "yes"}]]
            (is (bad-value? (tu/refusal-data #(v/prove kb g CxBVD opts))) (pr-str opts))
            (is (bad-value? (tu/refusal-data #(v/provable? kb g CxBVD opts))) (pr-str opts))))
        (testing "ask / ask? refuse a bad :max-ms (their one bound)"
          (doseq [opts [{:max-ms "x"} {:max-ms -1}]]
            (is (bad-value? (tu/refusal-data #(v/ask kb g CxBVD opts))) (pr-str opts))
            (is (bad-value? (tu/refusal-data #(v/ask? kb g CxBVD opts))) (pr-str opts))))
        (testing "query / query? refuse a bad :max-depth"
          (is (bad-value? (tu/refusal-data #(v/query kb g CxBVD {:max-depth "x"}))))
          (is (bad-value? (tu/refusal-data #(v/query? kb g CxBVD {:max-depth -2})))))
        (testing "search-tree and compare-tacticians refuse :max-ms and :node-budget too"
          (doseq [f [v/search-tree v/compare-tacticians]
                  opts [{:max-depth 2 :max-ms "x"} {:max-depth 2 :node-budget "x"}
                        {:max-depth 2 :node-budget -1} {:max-depth 2 :node-budget 1.5}]]
            (is (bad-value? (tu/refusal-data #(f kb g CxBVD opts))) (pr-str [f opts]))))
        (testing "the refusal names the option and the value it was given"
          (let [d (tu/refusal-data #(v/search-tree kb g CxBVD {:max-depth 2 :node-budget "x"}))]
            (is (= :node-budget (:option d)))
            (is (= "x" (:value d)))))
        (testing "a bound of 0 is a real question, not a bad value"
          ;; prove's :max-ms 0 is a deadline of now, so the search exhausts it — a
          ;; :budget-exhausted refusal, which is not the value refusal under test
          (is (not (bad-value? (tu/refusal-data #(v/prove kb g CxBVD {:max-ms 0})))))
          ;; query's :max-depth 0 is the facts-only read, and returns without refusing
          (is (nil? (tu/refusal-data #(doall (v/query kb g CxBVD {:max-depth 0})))))
          (is (= :complete (:status (v/search-tree kb g CxBVD
                                                   {:max-depth 2 :node-budget 5000
                                                    :max-ms 5000})))))))))

(deftest the-anytime-budget-refuses-a-value-outside-its-domain
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxBVD]
      (v/assert kb (list dog Muffet) CxBVD)
      (let [g (list dog '?x)]
        (testing "ask-within and prove-within refuse a bad :max-ms / :max-results"
          (doseq [opts [{:max-ms "x"} {:max-results "x"} {:max-results -1}]]
            (is (bad-value? (tu/refusal-data #(v/ask-within kb g CxBVD opts))) (pr-str opts))
            (is (bad-value? (tu/refusal-data #(v/prove-within kb g CxBVD opts))) (pr-str opts))))
        (testing "prove-within refuses a bad :max-depth / :max-term-growth"
          (is (bad-value? (tu/refusal-data #(v/prove-within kb g CxBVD {:max-depth "x"}))))
          (is (bad-value? (tu/refusal-data #(v/prove-within kb g CxBVD {:max-term-growth "x"})))))
        (testing "prove-within's node-engine arm refuses it before the depth is cast"
          ;; `inference-engine?` takes `(long max-depth)`, so a string depth is a bare cast
          ;; unless the budget's value check has run first
          (binding [v/*query-engine* :inference]
            (is (bad-value? (tu/refusal-data #(v/prove-within kb g CxBVD {:max-depth 2 :max-ms "x"}))))
            (is (bad-value? (tu/refusal-data #(v/prove-within kb g CxBVD {:max-depth "x"}))))))
        (testing "a :max-results of 0 is legal — realize nothing, resume continues"
          (let [r (v/prove-within kb g CxBVD {:max-results 0})]
            (is (= :capped (:status r)))
            (is (fn? (:resume r)))))))))

(deftest the-anytime-key-set-splits-what-ask-reads-from-what-prove-reads
  ;; The same split `ask-opt-keys` / `prove-opt-keys` make for `ask` / `prove`: a depth is
  ;; prove's and a cost tier is ask's, so a bound the entry point does not read is refused
  ;; rather than accepted and ignored.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxBVD]
      (v/assert kb (list dog Muffet) CxBVD)
      (let [g (list dog '?x)]
        (testing "ask-within refuses :max-depth and :max-term-growth — no rule expansion"
          (is (= :unknown-option (:type (tu/refusal-data #(v/ask-within kb g CxBVD {:max-depth 1})))))
          (is (= :unknown-option
                 (:type (tu/refusal-data #(v/ask-within kb g CxBVD {:max-term-growth 1}))))))
        (testing "prove-within refuses :max-cost — an ask concept prove ignores"
          (is (= :unknown-option
                 (:type (tu/refusal-data #(v/prove-within kb g CxBVD {:max-cost :lookup}))))))
        (testing "and the two key sets are the split of the union resume still holds"
          (is (= budget/budget-keys (into budget/ask-budget-keys budget/prove-budget-keys)))
          (is (not (contains? budget/ask-budget-keys :max-depth)))
          (is (not (contains? budget/prove-budget-keys :max-cost))))
        (testing "resume continues either, so it holds the union"
          ;; a prove-within partial resumed under a budget carrying an ask key is still
          ;; accepted — resume is neither entry point and holds the wider key set
          (let [r (v/prove-within kb g CxBVD {:max-results 0})]
            (is (map? (v/resume r {:max-results 1})))))))))

;; ---- the write and chain entry points -------------------------------------

(deftest a-chain-bound-outside-its-domain-is-refused-by-name
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxBVD]
      (v/assert kb (list dog Muffet) CxBVD)
      (testing "forward-chain refuses a bad chain bound or callback, at the entry point —
                before any rule fires"
        (doseq [opts [{:max-depth "x"} {:max-derivations "x"} {:max-derivations -1}
                      {:max-term-depth "x"} {:max-term-depth -1} {:on-progress 5} {:on-progress :nope} {:progress-every-ms "x"}
                      {:max-ms "x"} {:max-ms -1} {:stop? true}]]
          (is (bad-value? (tu/refusal-data #(v/forward-chain kb opts))) (pr-str opts))))
      (testing "assert refuses the same chain bounds it hands the fixpoint, without a rule
                needing to fire"
        (doseq [opts [{:max-depth "x"} {:max-derivations "x"} {:max-term-depth "x"}
                      {:on-progress 5} {:progress-every-ms "x"}]]
          (is (bad-value? (tu/refusal-data #(v/assert kb (list dog 'Rex) CxBVD opts))) (pr-str opts))))
      (testing "assert-rule inherits it through assert"
        (is (bad-value? (tu/refusal-data #(v/assert-rule kb [(list dog '?x)] (list dog '?x) CxBVD
                                                         {:max-depth "x"})))))
      (testing "a :progress-every-ms of 0 is legal — report at every opportunity"
        (is (map? (v/forward-chain kb {:progress-every-ms 0 :on-progress (fn [_])})))))))

(deftest abduce-refuses-a-cap-outside-its-domain
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxBVD]
      (v/assert kb (list dog Muffet) CxBVD)
      (doseq [opts [{:max-hypotheses "x"} {:max-hypotheses -1} {:max-depth "x"}]]
        (is (bad-value? (tu/refusal-data #(v/abduce kb (list dog '?x) CxBVD opts))) (pr-str opts))))))

(deftest kb-quality-refuses-a-non-fn-on-progress
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxBVD]
      (v/assert kb (list dog Muffet) CxBVD)
      (is (bad-value? (tu/refusal-data #(v/kb-quality kb {:on-progress 5}))))
      (is (bad-value? (tu/refusal-data #(v/kb-quality kb {:on-progress :nope}))))
      (testing ":limit stays a positive integer, refused by its own check"
        (is (= :unknown-option (:type (tu/refusal-data #(v/kb-quality kb {:limit 0})))))))))

(deftest the-extent-readers-refuse-a-non-boolean-believed?
  ;; The migration case: `{:believed? \"yes\"}` reads as truthy, so it silently answers the
  ;; believed extent under a value that only looks like `true`.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxBVD]
      (v/assert kb (list dog Muffet) CxBVD)
      (doseq [f [#(v/sentexes-in-context kb CxBVD %)
                 #(v/sentexes-with-functor kb dog %)
                 #(v/sentexes-with-arg kb 1 Muffet %)]]
        (is (bad-value? (tu/refusal-data (fn [] (doall (f {:believed? "yes"}))))))
        (is (bad-value? (tu/refusal-data (fn [] (doall (f {:believed? 1}))))))
        (testing "true, false and nil are all accepted"
          (is (seq? (f {:believed? true})))
          (is (seq? (f {:believed? false})))
          (is (seq? (f {:believed? nil}))))))))

(deftest clear-caches-refuses-a-non-boolean-counters?
  ;; The other migration case.
  (tu/with-neutral-kb [kb tu/fresh]
    (is (bad-value? (tu/refusal-data #(v/clear-caches kb {:counters? "yes"}))))
    (is (bad-value? (tu/refusal-data #(v/clear-caches kb {:counters? 1}))))
    (testing "true and false are both accepted"
      (is (map? (v/clear-caches kb {:counters? false})))
      (is (map? (v/clear-caches kb {:counters? true}))))))

;; ---- the three key-set gaps beside the value gaps -------------------------

(deftest add-evaluatable-refuses-a-key-off-its-key-set
  (tu/with-neutral-kb [kb tu/fresh]
    (testing "a key provers/evaluatable does not read is refused"
      (let [d (tu/refusal-data #(v/add-evaluatable kb 'evenSum (fn [a b] (even? (+ a b)))
                                                   {:bogus 1}))]
        (is (= :unknown-option (:type d)))
        (is (= [:bogus] (:unknown d)))))
    (testing "the four keys it does read still register"
      (is (map? (v/add-evaluatable kb 'sumOf + {:result :first :cost :lookup
                                                :arity 2 :completeness 100}))))))

(deftest set-cache-limit-warns-on-an-unknown-id-rather-than-refusing
  ;; The register fills lazily, so an id nothing has registered *yet* is a warning and a
  ;; recorded override — a not-yet-loaded cache picks it up — not a refusal that would
  ;; reject the configuration a bulk load sets up before touching a lazily-loaded calculus.
  ;; A registered id must name a cache an override moves, which not every registered one is
  ;; (`caches/override-problem`).
  (let [known :literal-matches]
    (try
      (testing "a bad id or a bad limit is still refused by name"
        (is (= :unknown-option (:type (tu/refusal-data #(v/set-cache-limit "not-a-keyword" 5)))))
        (is (= :unknown-option (:type (tu/refusal-data #(v/set-cache-limit known -1)))))
        (is (= :unknown-option (:type (tu/refusal-data #(v/set-cache-limit known 1.5))))))
      (testing "an id naming no registered cache is recorded, not refused"
        (is (not (caches/registered? :no-such-cache)))
        ;; the warning is the daemon doing its job; a test run does not print it
        (binding [trove/*log-fn* (fn [& _] nil)]
          (is (map? (v/set-cache-limit :no-such-cache 5))))
        (is (= 5 (get-in (v/cache-profile) [:overrides :no-such-cache])))
        (testing "and clearing the override with nil takes it back"
          (v/set-cache-limit :no-such-cache nil)
          (is (nil? (get-in (v/cache-profile) [:overrides :no-such-cache])))))
      (testing "a registered id is overridden outright"
        (is (caches/registered? known))
        (v/set-cache-limit known 4096)
        (is (= 4096 (get-in (v/cache-profile) [:overrides known]))))
      (finally
        (v/set-cache-limit :no-such-cache nil)
        (v/set-cache-limit known nil)))))

;; ---- the ordering gap -----------------------------------------------------

(defn- unrecovered-kb
  "A KB with a record stored and belief never built — the state `check-writable!` refuses.
  Built the way `vaelii.unrecovered-writes-test` builds one: a record put around the write
  entry points, then the hazard declared."
  []
  (let [kb (tu/fresh)
        h  (p/put-sentex (:records kb) (sx/sentex '(dog Muffet) 'CxUniverse {}))]
    (p/mark-premise (:records kb) h :default)
    (p/index-sentex (:index kb) (p/get-sentex (:records kb) h) h)
    (kb/note-hazards! kb {:no-belief true})
    kb))

(deftest assert-rule-refuses-an-unrecovered-kb-before-its-range-check
  ;; `assert-rule` ran `check-range-restricted` before `assert`'s unrecovered-KB check, so
  ;; on a KB whose belief was never built it answered `:not-range-restricted` where every
  ;; other write entry point answers `:unrecovered-kb` first.  `checks/check-rule!` makes
  ;; the same range check inside `assert`, so the early call only decided which refusal won.
  (let [kb (unrecovered-kb)]
    (try
      (testing "an unrecovered KB refuses a rule as :unrecovered-kb, not :not-range-restricted"
        ;; the rule is deliberately not range-restricted (?y is unbound), so the old order
        ;; would have caught that first
        (is (= :unrecovered-kb
               (:type (tu/refusal-data #(v/assert-rule kb '[(dog ?x)] '(cat ?y) 'CxUniverse))))))
      (finally (tu/clear-kb! kb))))
  (testing "and on a writable KB the range check still fires — it was not removed"
    (tu/with-neutral-kb [kb tu/fresh]
      (is (= :not-range-restricted
             (:type (tu/refusal-data #(v/assert-rule kb '[(dog ?x)] '(cat ?y) 'CxUniverse))))))))
