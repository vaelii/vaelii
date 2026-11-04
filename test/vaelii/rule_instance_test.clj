;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rule-instance-test
  "A rule's variables are the rule's own, and every *instance* of it needs its own.

Both backward chainers thread one binding map down a derivation path and hand it to
  every expansion on it, so two instances of one rule meet each other there.  The
  collision is between *canonical* names — a stored rule is spelled `?var0 ?var1 …`
  (`sentex/canonicalize-rule`), so every rule in the KB draws from one small pool of
  names and colliding is the normal case rather than the unlucky one.

  What a collision costs is an answer, not time: the unification that should have
  succeeded fails, and the branch under it is never explored.  So each test here asks a
  query whose answer is a closure the KB plainly contains, and asks it of all three
  engines — they must agree with each other and with the closure."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inference]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- node-prove
  "`prove` on the node engine.  The depth is chosen here because the engine has no
  default: 8 covers every derivation these fixtures build."
  [kb goal context]
  (binding [v/*query-engine* :inference, inference/*max-depth* 8]
    (v/prove kb goal context)))

(defn- level-7-prove
  "Backward chaining at level 7 of the lookup stack — the recursive chainer with the
  *registry* as its leaf, `prove`'s search driven lazily and deduplicated by answer."
  [kb goal context]
  (map :bindings (v/lookup kb 7 goal context)))

(defn- all-engines
  "`[prove level-7 node-engine]` answers for `goal`'s variable `var`, each as a set.

  Three engines and not two: the point of the sweep is that independently written
  searches agree.  `ask` is not among them and cannot be — it expands no rule, so it
  has no answer to these questions at all."
  [kb goal context var]
  (mapv #(set (map (fn [s] (get s var)) (doall (% kb goal context))))
        [v/prove level-7-prove node-prove]))

(defn- agree
  "Every engine's answer for `var`, asserted equal to `expected` — and to each other."
  [kb goal context var expected]
  (let [[p b a] (all-engines kb goal context var)]
    (is (= expected p) (str "prove disagrees on " (pr-str goal)))
    (is (= expected b) (str "level 7 disagrees on " (pr-str goal)))
    (is (= expected a) (str "the node engine disagrees on " (pr-str goal)))))

(tu/deftest-kb a-recursive-rule-meets-itself-down-one-path
  ;; (anc ?x ?z) :- (parentOf ?x ?y) (anc ?y ?z) — used twice on one path, the second
  ;; instance's ?x has to be the child where the first's was the grandchild.  Sharing
  ;; the name asks unify to make them equal, which fails, and the query answers only at
  ;; distance one.
  (tu/with-terms [parentOf anc CxChain]
    (let [n (fn [i] (symbol (str "ChainN" i)))]
      (doseq [i (range 4)]
        (v/assert kb (list parentOf (n i) (n (inc i))) CxChain))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxChain
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     CxChain {:direction :backward})
      (testing "the whole ancestor chain, not just the parent"
        (agree kb (list anc (n 0) '?z) CxChain '?z
               (set (map n (range 1 5)))))
      (testing "and read from the other end"
        (agree kb (list anc '?x (n 4)) CxChain '?x
               (set (map n (range 0 4))))))))

(tu/deftest-kb a-left-recursive-rule-meets-itself-too
  (tu/with-terms [parentOf lanc CxLeft]
    (let [n (fn [i] (symbol (str "LeftN" i)))]
      (doseq [i (range 4)]
        (v/assert kb (list parentOf (n i) (n (inc i))) CxLeft))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list lanc '?x '?z) CxLeft
                     {:direction :backward})
      (v/assert-rule kb [(list lanc '?x '?y) (list parentOf '?y '?z)] (list lanc '?x '?z)
                     CxLeft {:direction :backward})
      (agree kb (list lanc (n 0) '?z) CxLeft '?z (set (map n (range 1 5)))))))

(tu/deftest-kb an-inner-rules-variable-does-not-bind-an-outer-rules-sibling
  ;; The outer rule's second conjunct is still unsolved when the first is expanded, so
  ;; its variables are unbound and unmentioned in the bindings — and an inner rule with
  ;; one more variable than the goal asked about (an existential in its antecedent)
  ;; occupies the very same canonical slot.  Merging its answer whole binds the outer
  ;; conjunct's ?var2 to the existential's value, and the conjunct then matches nothing.
  (tu/with-terms [linkA linkB reach side CxReach]
    (tu/with-terms [Start Middle Target Existential]
      (v/assert-rule kb [(list linkA '?a '?b) (list linkB '?b '?c)] (list reach '?a '?c)
                     CxReach {:direction :backward})
      (v/assert-rule kb [(list side '?p '?q '?r)] (list linkA '?p '?q) CxReach
                     {:direction :backward})
      (v/assert kb (list side Start Middle Existential) CxReach)
      (v/assert kb (list linkB Middle Target) CxReach)
      (agree kb (list reach Start '?c) CxReach '?c #{Target}))))

(tu/deftest-kb a-query-may-use-the-names-stored-rules-are-spelled-with
  ;; Nothing stops a caller writing ?var0 / ?var1, and a rule's consequent is stored in
  ;; exactly those.  Crossed over, the two are asked to unify with each other, and the
  ;; occurs check — correctly — refuses the cycle, so the rule does not fire at all.
  (tu/with-terms [edgeX hopX CxHop]
    (tu/with-terms [HopFrom HopTo]
      (v/assert kb (list edgeX HopFrom HopTo) CxHop)
      (v/assert-rule kb [(list edgeX '?m '?n)] (list hopX '?m '?n) CxHop
                     {:direction :backward})
      (testing "straight through"
        (agree kb (list hopX HopFrom '?var1) CxHop '?var1 #{HopTo}))
      (testing "crossed over — the goal's ?var1 sits where the rule's ?var0 does"
        (agree kb (list hopX '?var1 '?var0) CxHop '?var1 #{HopFrom})
        (agree kb (list hopX '?var1 '?var0) CxHop '?var0 #{HopTo})))))

(tu/deftest-kb an-exception-still-blocks-a-renamed-instance
  ;; A guard reads the rule's *own* variable names out of the completed bindings, so a
  ;; renamed instance has to bind them back before asking.  A guard that stopped firing
  ;; under renaming would be an exception that silently lapsed at depth.
  (tu/with-terms [parentOf anc estranged CxGuard]
    (tu/with-terms [GuardA GuardB GuardC]
      (v/assert kb (list parentOf GuardA GuardB) CxGuard)
      (v/assert kb (list parentOf GuardB GuardC) CxGuard)
      (v/assert kb (list estranged GuardB) CxGuard)
      (v/assert kb (list 'exceptWhen (list estranged '?x)
                         (list 'set/defaultRule
                               (list 'implies (list parentOf '?x '?z) (list anc '?x '?z))))
                CxGuard)
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     CxGuard {:direction :backward})
      (testing "the base rule is blocked for the estranged parent at every depth"
        ;; GuardA reaches GuardB by the base rule; the recursive rule would take it on
        ;; to GuardC through (anc GuardB ?z), and *that* firing of the base rule is the
        ;; excepted one.
        (agree kb (list anc GuardA '?z) CxGuard '?z #{GuardB})
        (agree kb (list anc GuardB '?z) CxGuard '?z #{})))))

(tu/deftest-kb renaming-is-deterministic
  ;; The renamed variables reach the caller — `prove` returns raw binding maps — so a
  ;; gensym would make the same query answer differently on every run, in an engine
  ;; whose contract is that it does not.
  (tu/with-terms [parentOf anc CxDet]
    (let [n (fn [i] (symbol (str "DetN" i)))]
      (doseq [i (range 3)]
        (v/assert kb (list parentOf (n i) (n (inc i))) CxDet))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxDet
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     CxDet {:direction :backward})
      ;; the renamed variables are visible only in the DFS's *raw* binding maps; the
      ;; node engine projects onto the query's variables, so it has none to be
      ;; deterministic about
      (let [goal  (list anc (n 0) '?z)
            once  (binding [v/*query-engine* :dfs] (set (v/prove kb goal CxDet)))
            twice (binding [v/*query-engine* :dfs] (set (v/prove kb goal CxDet)))]
        (is (= once twice) "the same query returned different binding maps"))
      ;; The renamed names are not observable through an engine any more — a solution is
      ;; projected onto the query's own variables — so determinism is asserted where it
      ;; is decided.  A gensym here would give an engine whose contract is order
      ;; independence a different answer on every run of one query.
      (testing "and the renaming behind it is deterministic where it happens"
        (let [rule  (first (provers/candidate-rules kb (list anc (n 0) '?z) CxDet))
              taken '#{?var0 ?var1}
              a     (res/freshen-rule rule taken)
              b     (res/freshen-rule rule taken)]
          (is (= (:consequent a) (:consequent b)))
          (is (= (:antecedents a) (:antecedents b)))
          (is (some #(re-find #"'" (name %)) (sx/form-variables (:consequent a)))
              "nothing here needs renaming, so this is not measuring what it claims"))))))

(tu/deftest-kb a-renamed-name-does-not-grow-with-the-depth-of-its-path
  ;; `prove-from` hands `freshen-rule` the names its path holds, and those gain every name
  ;; each expansion mints, so 60 expansions deep the taken set holds 60 renamings of each
  ;; rule variable.  A name searched for along the `?v'`, `?v''` … series is 60 primes long
  ;; there, and each expansion of a chain n deep pays O(n) tries for it.
  (tu/with-terms [parentOf anc CxDeepName]
    (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                   CxDeepName {:direction :backward})
    (let [rule   (first (provers/candidate-rules kb (list anc 'DeepNameA '?z) CxDeepName))
          vars-of #(sx/form-variables (cons (:consequent %) (:antecedents %)))
          taken  (reduce (fn [tk _] (into tk (vars-of (res/freshen-rule rule tk))))
                         (vars-of rule) (range 60))
          fresh  (vars-of (res/freshen-rule rule taken))]
      (is (not-any? taken fresh))
      (is (every? #(<= (count (name %)) 12) fresh) (pr-str fresh))
      (testing "a name the query wrote itself is passed over"
        (let [taken #{'?var0 '?var0'2}]
          (is (= #{'?var0'2'} (set (filter #(re-find #"^\?var0'" (name %))
                                           (vars-of (res/freshen-rule rule taken))))))))))
  (testing "and a backward chain 60 deep is proved to its end"
    (tu/with-terms [linkTo reach CxDeepChain]
      (let [nd #(symbol (str "DeepChainN" %))]
        (v/assert-rule kb [(list linkTo '?x '?y) (list reach '?x)] (list reach '?y) CxDeepChain
                       {:direction :backward})
        (doseq [i (range 60)] (v/assert kb (list linkTo (nd i) (nd (inc i))) CxDeepChain))
        (v/assert kb (list reach (nd 0)) CxDeepChain)
        (is (= (set (map nd (range 61)))
               (set (map #(get % '?w) (v/prove kb (list reach '?w) CxDeepChain {:max-depth 70})))))))))

;; ---- what a solution is a map over ---------------------------------------

(tu/deftest-kb a-solution-is-a-map-over-the-question-not-over-the-proof
  ;; A derivation path accumulates one flat binding map, and every instance it expands
  ;; contributes its own names to it.  Those are scratch — how the search got there, not
  ;; what it was asked — so a solution is cut down to the query's own variables at the
  ;; moment it is finished.  Without that the three engines return three different maps
  ;; for one question, and only `ask` returns the one the asker can read.
  (tu/with-terms [edgeOf anc CxProj]
    (tu/with-terms [PjA PjB PjC]
      (v/assert kb (list edgeOf PjA PjB) CxProj)
      (v/assert kb (list edgeOf PjB PjC) CxProj)
      (v/assert-rule kb [(list edgeOf '?x '?z)] (list anc '?x '?z) CxProj
                     {:direction :backward})
      (v/assert-rule kb [(list edgeOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     CxProj {:direction :backward})
      (testing "every engine keys its answers by the query's variables and nothing else"
        (doseq [[label f] [["prove" v/prove] ["level 7" level-7-prove]
                           ["node engine" node-prove]]]
          (let [sols (doall (f kb (list anc PjA '?z) CxProj))]
            (is (seq sols) label)
            (is (every? #(= #{'?z} (set (keys %))) sols)
                (str label " leaked a variable the asker never wrote: " (pr-str sols))))))
      (testing "and the three of them return the same maps, not merely the same answers"
        (is (= (set (v/prove kb (list anc PjA '?z) CxProj))
               (set (node-prove kb (list anc PjA '?z) CxProj))
               (set (level-7-prove kb (list anc PjA '?z) CxProj))
               #{{'?z PjB} {'?z PjC}})))
      (testing "a ground query asks about no variables, so it answers with an empty map"
        (is (= [{}] (v/prove kb (list anc PjA PjC) CxProj)))
        (is (= [{}] (vec (node-prove kb (list anc PjA PjC) CxProj)))))
      (testing "a query that writes the canonical names is asking about them"
        ;; `?var0` is a spelling, not a reservation: a variable belongs to whoever
        ;; wrote it, and a query using the rules' own names must still be answered.
        (is (= #{{'?var1 PjA '?var0 PjB} {'?var1 PjB '?var0 PjC} {'?var1 PjA '?var0 PjC}}
               (set (v/prove kb (list anc '?var1 '?var0) CxProj)))))
      (testing "a bounded run projects too, and resuming it keeps the projection"
        (let [r (v/prove-within kb (list anc PjA '?z) CxProj {:max-results 1})]
          (is (= :capped (:status r)))
          (is (= #{{'?z PjB} {'?z PjC}}
                 (into (set (:results r)) (:results (v/resume r {}))))))))))
