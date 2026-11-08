;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.query-test
  "`query` — the public entry point — and its one dial.

  Everything here is about the *dial* and the *goal shape*, which is where the two ways
  to get this wrong live.  `query` takes the same two goal shapes `prove` takes (a
  sentence, or a vector of them that joins on shared variables) and reads one option,
  `:max-depth`, that says how far to expand rules.  The combinations therefore form a
  grid, and the tests below walk it: each goal shape at no depth, at a depth, and at a
  depth that came from a dynamic binding rather than from `opts`.

  What makes the grid worth walking rather than sampling is that a wrong cell does not
  throw.  A goal shape the depth-0 path cannot join, or a depth the resolution misses,
  produces an *empty answer* — indistinguishable, to a caller, from a KB that knows
  nothing.  So the assertions are mostly agreement assertions: the same knowledge read
  two ways has to come back the same, and `prove` is the second way."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inference]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- goal shapes: a conjunction is answerable without a depth -------------
;; A conjunction needs no rule to be a conjunction.  Both conjuncts below are stored
;; facts, so this asks nothing of the rule graph — and it is the reading `query`'s own
;; docstring calls the common case, most of a common-sense KB being facts and closures.

(tu/deftest-kb a-conjunctive-goal-answers-with-no-depth-at-all
  (tu/with-terms [parentOf dog Ann Bob Cid CxQ]
    (v/assert kb (list parentOf Ann Bob) CxQ)
    (v/assert kb (list parentOf Ann Cid) CxQ)
    (v/assert kb (list dog Bob) CxQ)
    (let [goal [(list parentOf Ann '?y) (list dog '?y)]]
      (testing "the shared variable joins — Cid is a child but not a dog"
        (is (= [{'?y Bob}] (vec (v/query kb goal CxQ)))))
      (testing "and `prove`, the other reader that takes a conjunction, agrees"
        (is (= (set (v/prove kb goal CxQ))
               (set (v/query kb goal CxQ)))))
      (testing "`query?` reads the same conjunction rather than testing a vector"
        (is (v/query? kb goal CxQ))
        (is (not (v/query? kb [(list parentOf Ann '?y) (list dog Ann)] CxQ))
            "Ann is nobody's dog, so the join has no solution")))))

(tu/deftest-kb the-goal-shapes-agree-where-they-overlap
  (tu/with-terms [parentOf Ann Bob CxQ]
    (v/assert kb (list parentOf Ann Bob) CxQ)
    (testing "a one-element vector is the bare sentence"
      (is (= (vec (v/query kb (list parentOf Ann '?y) CxQ))
             (vec (v/query kb [(list parentOf Ann '?y)] CxQ)))))
    (testing "an empty conjunction proves trivially, exactly as `prove` says it does"
      (is (= [{}] (vec (v/query kb [] CxQ))))
      (is (= (vec (v/prove kb [] CxQ)) (vec (v/query kb [] CxQ)))))
    (testing "a conjunct nothing answers empties the whole conjunction"
      (is (empty? (v/query kb [(list parentOf Ann '?y) (list parentOf '?y '?z)]
                           CxQ))))))

(tu/deftest-kb a-conjunction-with-no-depth-joins-through-the-registry
  ;; The discriminating case for *which leaf* the depth-0 path uses.  `(genl a c)` here
  ;; is in the cached closure and in no stored sentex, so a conjunction that joins on it
  ;; is answered only by a leaf that is the whole prover registry — which is what `ask`
  ;; reaches for one literal, and what this must reach for several.
  (tu/with-terms [tag_a tag_b tag_c Thing CxQ]
    (v/assert kb (list 'genl tag_a tag_b) CxQ)
    (v/assert kb (list 'genl tag_b tag_c) CxQ)
    (v/assert kb (list tag_a Thing) CxQ)
    (testing "the transitive edge is derived, not stored"
      (is (empty? (v/sentexes-matching kb (list 'genl tag_a tag_c) CxQ)))
      (is (v/ask? kb (list 'genl tag_a tag_c) CxQ)))
    (testing "and a conjunction over it answers with no depth"
      (is (= [{'?x Thing}]
             (vec (v/query kb [(list 'genl tag_a tag_c) (list tag_a '?x)] CxQ)))))))

;; ---- an open functor ---------------------------------------------------

(tu/deftest-kb an-open-functor-answers-every-type-the-term-holds
  ;; `(animal Muffet)` holds through `(dog Muffet)`, so `(?c Muffet)` answers `animal` as
  ;; well as `dog`, and a conjunction over it answers the same whichever literal runs first.
  (tu/with-terms [animal dog cat Muffet CxQ]
    (doseq [t [dog cat]] (v/assert kb (list 'genl t animal) CxQ))
    (v/assert kb (list dog Muffet) CxQ)
    (let [cs   #(set (map (fn [m] (get m '?c)) %))
          open (list '?c Muffet)
          hier (list 'genl '?c animal)]
      (is (v/ask? kb (list animal Muffet) CxQ))
      (is (set/subset? #{dog animal} (cs (v/ask kb open CxQ))))
      (doseq [ranked? [true false]
              goals   [[open hier] [hier open]]]
        (binding [plan/*enabled* ranked?]
          (is (= #{dog animal} (cs (doall (v/query kb goals CxQ))))
              (str "query " goals (when-not ranked? ", unranked")))
          (is (= #{dog animal} (cs (v/prove kb goals CxQ)))
              (str "prove " goals (when-not ranked? ", unranked"))))))))

;; ---- the dial: no depth expands no rule ---------------------------------

(tu/deftest-kb no-depth-anywhere-expands-no-rule
  (tu/with-terms [parentOf anc Ann Bob CxQ]
    (v/assert kb (list parentOf Ann Bob) CxQ)
    ;; backward, so no forward firing stores the conclusion and the only way to it is a
    ;; backchainer looking for it
    (v/assert-rule kb [(list parentOf '?x '?y)] (list anc '?x '?y) CxQ
                   {:direction :backward})
    (let [goal (list anc Ann '?z)]
      ;; The cross-engine sweep (`VAELII_QUERY_ENGINE`) sets `inference/*max-depth*` so
      ;; `prove` can run on the node engine, and `query` does not read it: the answer here
      ;; is the same in every configuration.
      (testing "with no depth the rule is not expanded"
        (is (= [] (vec (v/query kb goal CxQ))))
        (is (false? (v/query? kb goal CxQ)))
        (is (= [] (binding [inference/*max-depth* 3] (vec (v/query kb goal CxQ))))
            "the node engine's own bound is not a depth `query` reads"))
      (testing "a depth reaches it"
        (is (= [{'?z Bob}] (vec (v/query kb goal CxQ {:max-depth 1})))))
      (testing "and `prove`, which needs no depth, reaches it too"
        (is (= [{'?z Bob}] (vec (v/prove kb goal CxQ))))))))

(tu/deftest-kb a-depth-may-come-from-a-dynamic-binding
  ;; The depth is a decision, and a caller makes it in one of two places.  Missing one
  ;; of them is invisible: the read just answers whatever needs no rule.
  (tu/with-terms [parentOf anc Ann Bob Cid CxQ]
    (v/assert kb (list parentOf Ann Bob) CxQ)
    (v/assert kb (list parentOf Bob Cid) CxQ)
    (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxQ
                   {:direction :backward})
    (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                   CxQ {:direction :backward})
    (let [goal (list anc Ann '?z)
          zs   #(set (map (fn [s] (get s '?z)) %))]
      (testing "`opts`"
        (is (= #{Bob Cid} (zs (v/query kb goal CxQ {:max-depth 3})))))
      (testing "`*query-options*` :max-depth — where `prove` reads a depth from too"
        (is (= #{Bob Cid} (binding [v/*query-options* {:max-depth 3}]
                            (zs (v/query kb goal CxQ))))))
      (testing "`opts` wins over a dynamic one rather than being merged with it"
        (is (= #{Bob} (binding [v/*query-options* {:max-depth 3}]
                        (zs (v/query kb goal CxQ {:max-depth 1}))))
            "depth 1 admits one hop, so the two-hop ancestor is out of reach"))
      (testing "a *query-options* naming only a strategy leaves the depth unset"
        (is (= #{} (zs (binding [v/*query-options* :depth-first]
                         (v/query kb goal CxQ)))))
        (is (= #{Bob Cid} (binding [v/*query-options* :depth-first]
                            (zs (v/query kb goal CxQ {:max-depth 3})))))))))

(tu/deftest-kb a-key-query-does-not-read-is-refused-not-handed-to-the-engine
  ;; The node engine reads the keys it knows and ignores the rest, so an open key set here
  ;; would let `{:max-deph 3}` answer facts-only with nothing to say a rule was never
  ;; expanded — the silent-default failure every other entry point refuses.  The key set is the
  ;; union of `query`'s own dial and the engine's, and it is public.
  (tu/with-terms [parentOf anc Ann Bob CxQ]
    (v/assert kb (list parentOf Ann Bob) CxQ)
    (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxQ
                   {:direction :backward})
    (let [goal    (list anc Ann '?z)
          refusal (fn [opts]
                    (try (v/query kb goal CxQ opts) nil
                         (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (testing "every key in the key set is taken"
        (is (= #{:max-depth :max-ms :proof? :strategy :portfolio? :auto? :racers} v/query-opt-keys))
        (is (= [{'?z Bob}] (vec (v/query kb goal CxQ {:max-depth 2 :strategy :depth-first
                                                      :auto? false :portfolio? false
                                                      :racers [:cost :depth-first]}))))
        (is (= [{'?z Bob}] (map :bindings (v/query kb goal CxQ {:max-depth 2 :proof? true})))))
      (testing "a misspelt one is refused by name, at `query` and `query?` alike"
        (doseq [opts [{:max-deph 2} {:proof true :max-depth 2} {:max-depth 2 :strategy :cost :portfolio true}]]
          (let [d (refusal opts)]
            (is (= :unknown-option (:type d)) (pr-str opts))
            (is (= (vec (sort v/query-opt-keys)) (:options d)) "and the refusal names the key set")
            (is (seq (:unknown d))))
          (is (= :unknown-option
                 (:type (try (v/query? kb goal CxQ opts) nil
                             (catch clojure.lang.ExceptionInfo e (ex-data e))))))))
      (testing "a non-map opts is refused the same way"
        (is (= :unknown-option (:type (refusal :oops))))
        (is (= :unknown-option (:type (refusal [:max-depth 2])))))
      (testing "and nil opts is the no-rule-expansion read, as ever"
        (is (= [] (vec (v/query kb goal CxQ nil))))))))

(tu/deftest-kb a-non-map-opts-is-refused-by-name-at-the-existence-entry-points-too
  ;; `provable?` and `ask?` test `(seq opts)` to pick the bounded arm, and `(seq :oops)`
  ;; throws a bare IllegalArgumentException — where `prove` and `ask` refuse the same
  ;; opts by name.  The daemon pads its args to the option arity and hides it; in
  ;; process the four have to agree.
  (tu/with-terms [dog Rex CxQ]
    (v/assert kb (list dog Rex) CxQ)
    (let [goal (list dog Rex)]
      (doseq [[nm f] [["provable?" #(v/provable? kb goal CxQ %)]
                      ["ask?"      #(v/ask? kb goal CxQ %)]
                      ["prove"     #(v/prove kb goal CxQ %)]
                      ["ask"       #(v/ask kb goal CxQ %)]]
              bad [:oops 5 "max-ms"]]
        (let [e (is (thrown? clojure.lang.ExceptionInfo (f bad)) (str nm " " (pr-str bad)))]
          (is (= :unknown-option (:type (ex-data e))) (str nm " " (pr-str bad)))))
      (testing "and an empty map is the unbounded read, as nil is"
        (is (true? (v/provable? kb goal CxQ {})))
        (is (true? (v/ask? kb goal CxQ {})))))))

(tu/deftest-kb a-bounded-query-answers-a-subset-of-what-prove-answers
  ;; The two engines terminate on different things — `query` on its bound, `prove` on the
  ;; data — so within the bound they must agree, and past it `prove` may know more.  A
  ;; disagreement in the other direction would mean the bounded engine inventing an
  ;; answer.
  (tu/with-terms [parentOf anc CxQ]
    (let [n (fn [i] (symbol (str "TmpQChain" i)))]
      (doseq [i (range 5)] (v/assert kb (list parentOf (n i) (n (inc i))) CxQ))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxQ
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     CxQ {:direction :backward})
      (let [goal    (list anc (n 0) '?z)
            proved  (set (v/prove kb goal CxQ))
            bounded #(set (v/query kb goal CxQ {:max-depth %}))]
        (testing "every depth answers a subset of the unbounded search"
          (doseq [d (range 1 7)]
            (is (empty? (set/difference (bounded d) proved))
                (str "depth " d " answered something `prove` did not"))))
        (testing "and a deep enough bound catches up with it exactly"
          (is (= proved (bounded 6))))
        (testing "while a shallow one is a strict subset"
          (is (< (count (bounded 1)) (count proved))))))))

(tu/deftest-kb a-query-under-a-clock-answers-the-same-or-refuses
  (tu/with-terms [parentOf anc dog Ann Bob Cy CxQ]
    (v/assert kb (list parentOf Ann Bob) CxQ)
    (v/assert kb (list parentOf Bob Cy) CxQ)
    (v/assert kb (list dog Ann) CxQ)
    (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxQ
                   {:direction :backward})
    (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                   CxQ {:direction :backward})
    (let [goal    (list anc Ann '?z)
          deep    {:max-depth 4 :max-ms 60000}
          refused #(try (%) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))]
      (testing "a clock that does not pass answers what the read answers without one"
        (doseq [[g opts] [[goal {:max-depth 4}] [goal {:max-depth 4 :portfolio? true}]
                          [(list dog '?x) {}]]]
          (is (= (set (v/query kb g CxQ opts))
                 (set (v/query kb g CxQ (assoc opts :max-ms 60000))))
              (pr-str opts)))
        (is (true? (v/query? kb goal CxQ deep)))
        (is (= (select-keys (v/query-status kb goal CxQ {:max-depth 4}) [:status :answers])
               (select-keys (v/query-status kb goal CxQ deep) [:status :answers])))
        (is (= :true (:verdict (v/argue kb (list anc Ann Cy) CxQ deep)))))
      (testing "a passed clock refuses the answer set rather than return a prefix"
        (doseq [opts [{:max-depth 4 :max-ms 0} {:max-depth 4 :max-ms 0 :portfolio? true}
                      {:max-ms 0}]]
          (is (= :budget-exhausted (refused #(v/query kb goal CxQ opts))) (pr-str opts)))
        (is (= :budget-exhausted
               (refused #(v/argue kb (list anc Ann Cy) CxQ {:max-depth 4 :max-ms 0})))))
      (testing "and query-status reports it"
        (doseq [opts [{:max-depth 4 :max-ms 0} {:max-ms 0}]]
          (is (= :timeout (:status (v/query-status kb goal CxQ opts))) (pr-str opts)))))))

(defn- leaf-calls
  "How many literals the registry leaf answers while `f` runs, and `f`'s value."
  [f]
  (let [n (atom 0) orig provers/solve-goal]
    (with-redefs [provers/solve-goal (fn [& args] (swap! n inc) (apply orig args))]
      [(f) @n])))

(tu/deftest-kb an-existence-question-stops-at-its-first-derivation
  ;; k backward rules each derive the one goal from a fact of its own, so the whole search
  ;; answers the leaf k + 1 times.  An existence question stops at the first derivation:
  ;; its leaf count is the same at every k, on either engine `provable?` routes to.
  (let [cost (fn [k ask]
               (tu/with-terms [qq Cee CxQ]
                 (doseq [_ (range k)]
                   (let [p (tu/tmp-type "pp")]
                     (v/assert kb (list p Cee) CxQ)
                     (v/assert-rule kb [(list p '?x)] (list qq '?x) CxQ
                                    {:direction :backward})))
                 (leaf-calls #(ask (list qq Cee) CxQ))))]
    (doseq [[nm ask] [["provable?" #(v/provable? kb %1 %2)]
                      ["query? at a depth" #(v/query? kb %1 %2 {:max-depth 2})]]]
      (let [[a4 n4]   (cost 4 ask)
            [a16 n16] (cost 16 ask)]
        (is (= [true true] [a4 a16]) nm)
        (is (= n4 n16) (str nm ": " n4 " leaf reads at 4 derivations, " n16 " at 16"))))))

(tu/deftest-kb each-debugger-entry-point-accepts-what-it-actually-reads
  ;; A key set wider than its entry point is the silent default one level in: `search-tree` runs
  ;; under `:proof? true` and never reaches the portfolio path, and `compare-tacticians`
  ;; sets the ordering per row — so `query`'s key set handed to either accepts a key the
  ;; entry point then overwrites.  `{:strategy :cost}` at `compare-tacticians` is the one that
  ;; reads worst: taken, discarded, and four rows come back under the default orderings
  ;; as though the caller had named none.
  (tu/with-terms [parentOf anc Ann Bob CxDbg]
    (v/assert kb (list parentOf Ann Bob) CxDbg)
    (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxDbg
                   {:direction :backward})
    (let [goal (list anc Ann '?z)
          data (fn [f opts] (try (f kb goal CxDbg opts) nil
                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (testing "the key sets are public and are what each entry point reads"
        (is (= #{:max-depth :strategy :node-budget :max-ms} v/search-tree-opt-keys))
        (is (= #{:max-depth :tacticians :node-budget :max-ms} v/compare-tacticians-opt-keys)))
      (testing "search-tree refuses the keys it would overwrite or never read"
        (doseq [opts [{:max-depth 2 :proof? false} {:max-depth 2 :portfolio? true}
                      {:max-depth 2 :auto? true}   {:max-depth 2 :racers [:cost]}
                      {:max-deph 2}]]
          (let [d (data v/search-tree opts)]
            (is (= :unknown-option (:type d)) (pr-str opts))
            (is (= (vec (sort v/search-tree-opt-keys)) (:options d))))))
      (testing "compare-tacticians refuses :strategy, which it sets per row"
        (doseq [opts [{:max-depth 2 :strategy :cost} {:max-depth 2 :proof? true}
                      {:max-depth 2 :portfolio? true}]]
          (let [d (data v/compare-tacticians opts)]
            (is (= :unknown-option (:type d)) (pr-str opts))
            (is (= (vec (sort v/compare-tacticians-opt-keys)) (:options d))))))
      (testing "and every accepted key still answers"
        (is (= :complete (:status (v/search-tree kb goal CxDbg
                                                 {:max-depth 2 :strategy :depth-first
                                                  :node-budget 200 :max-ms 5000}))))
        (is (= [:cost] (mapv :tactician
                             (v/compare-tacticians kb goal CxDbg
                                                   {:max-depth 2 :tacticians [:cost]
                                                    :node-budget 200 :max-ms 5000}))))))))
