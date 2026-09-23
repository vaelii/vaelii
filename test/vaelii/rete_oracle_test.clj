;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rete-oracle-test
  "The correctness gate for the incremental matcher (`vaelii.impl.rete`).

  The engine keeps the semi-naive `vaelii.impl.chain` as the **reference**
  implementation and holds the incremental network to it, exactly as the taxonomy
  keeps `closures` / `equality-partition` as reference impls the incremental versions
  are oracle-tested against.  Two layers of oracle:

    * matcher-level — `rete/rete-match-pattern` must return the *same set* as
      `res/match-pattern` for every probe pattern over a populated KB.  This is the
      one place the network can differ, so it is pinned directly.

    * end-to-end — the same randomized sequence of rule/fact asserts and retracts,
      run once through the reference chain and once through the incremental matcher,
      must leave **identical derived content**: the same stored sentexes and the same
      justifications (compared by content, since handles are allocated per run).  The two
      KBs live on the two database pairs the suite reserves (scratch + isolated) so
      they can be stepped in lock-step and compared after *every* operation, which
      localizes any divergence to the op that caused it.

  The same stream, the same two KBs and the same comparison serve a **second** claim,
  because it is the same kind of claim: `chain/*suppress-duplicate-firings*` skips the
  firings a run would otherwise make twice (`witness_order_test`), and that too has to
  leave the derived sentexes and the justification sets alone.  It is bound false on
  one side rather than compared against remembered numbers, so the reference moves
  with the engine.

  The random ontology exercises every invariant the network must preserve: multi-
  antecedent joins with a leading-variable non-trigger antecedent (the case the
  network exists to speed up), recursion + the depth guard, unary subtype fan-out, a
  symmetric predicate matched as a non-trigger antecedent (the mirror probe), a
  deferred `lessThan` antecedent, `exceptWhen` blocking, a `functional` predicate that
  derives an equality twin, sibling-context firings with no common placement, and
  retraction with re-derivation."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rete :as rete]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology (identical on both KBs) ------------------------

(defn build-ontology!
  "CxCore vocabulary + a compact ontology whose rules cover every invariant.  A
  rule set, contexts, a type lattice, disjointness, and metadata — no contingent
  facts (those are the random sequence)."
  [kb]
  (core-context/load-into kb)
  ;; context spindle: Base sees Core; Left and Right are incomparable specs of Base,
  ;; so a rule in Base firing over a Left fact and a Right fact has no common
  ;; placement context (the sibling no-placement case)
  (v/assert kb '(genlCx CxBase CxCore) 'CxCore {:strength :monotonic})
  (v/assert kb '(genlCx CxLeft CxBase) 'CxCore {:strength :monotonic})
  (v/assert kb '(genlCx CxRight CxBase) 'CxCore {:strength :monotonic})
  ;; type lattice
  (doseq [e '[(genl animal thing) (genl dog animal) (genl poodle dog)
              (genl cat animal) (genl bird animal) (genl penguin bird)]]
    (v/assert kb e 'CxBase {:strength :monotonic}))
  ;; predicate lattice — the sub-predicate fan-out is not a unary-only rule.  `fatherOf`
  ;; and `motherOf` sit under a **binary** `parentOf`, `leasesFrom` under a binary
  ;; `owns`, `strictlyBetweenIn` under a **ternary** `betweenIn`; a matcher that fanned
  ;; the functor only at arity 1 agrees with the reference on every unary probe and
  ;; diverges the moment a fact of one of these arrives, so the comparison has to reach
  ;; them (`streams-are-not-vacuous` is what says it does).
  (doseq [e '[(genl fatherOf parentOf) (genl motherOf parentOf)
              (genl leasesFrom owns)
              (genl strictlyBetweenIn betweenIn)]]
    (v/assert kb e 'CxBase {:strength :monotonic}))
  (v/assert kb '(disjoint dog cat) 'CxBase {:strength :monotonic})
  ;; metadata
  (v/assert kb '(symmetric siblingOf) 'CxBase {:strength :monotonic})
  (v/assert kb '(transitive ancestorOf) 'CxBase {:strength :monotonic})
  (v/assert kb '(functional bestFriendOf) 'CxBase {:strength :monotonic})
  ;; rules (all in Base, so they see facts in Left / Right / Base)
  (let [R (fn [ante conseq]
            (v/assert kb (list 'implies ante conseq) 'CxBase))]
    ;; the leading-variable join the network exists to accelerate
    (R '(and (parentOf ?x ?y) (parentOf ?y ?z)) '(grandparentOf ?x ?z))
    ;; recursion + depth guard: right-recursive ancestor
    (R '(parentOf ?x ?y) '(ancestorOf ?x ?y))
    (R '(and (parentOf ?x ?y) (ancestorOf ?y ?z)) '(ancestorOf ?x ?z))
    ;; unary subtype fan-out (a poodle is a dog)
    (R '(dog ?x) '(has_fur ?x))
    ;; type antecedent joined with a relation
    (R '(and (owns ?p ?a) (animal ?a)) '(pet_owner ?p))
    ;; a symmetric predicate as a NON-trigger antecedent — exercises the mirror probe
    ;; inside the matcher (triggered by parentOf, siblingOf joined second)
    (R '(and (parentOf ?x ?y) (siblingOf ?y ?z)) '(uncleAuntOf ?x ?z))
    ;; a deferred antecedent in a forward join (computed, not matched)
    (R '(and (ageOf ?x ?a) (ageOf ?y ?b) (lessThan ?a ?b)) '(youngerThan ?x ?y))
    ;; a **ternary** antecedent, so the sub-predicate fan is driven end to end at an
    ;; arity above one rather than only probed
    (R '(and (betweenIn ?x ?y ?z) (dog ?y)) '(guardedBy ?x ?z)))
  ;; exceptWhen default: birds fly unless penguins
  (v/assert kb '(exceptWhen (penguin ?b) (set/defaultRule (implies (bird ?b) (flies ?b))))
            'CxBase)
  kb)

;; ---- content snapshots, by content not by handle ------------------------

(defn- sx-content [kb id]
  (when-let [s (p/get-sentex (:records kb) id)]
    [(v/sentence-of s) (:context s)]))

(defn stored-content [kb]
  (into #{} (keep #(sx-content kb %)) (p/sentex-ids (:records kb))))

(defn believed-content [kb]
  (into #{} (comp (filter #(v/in? kb %)) (keep #(sx-content kb %)))
        (p/sentex-ids (:records kb))))

(defn justification-content [kb]
  (into #{}
        (keep (fn [id]
                (when-let [d (p/get-justification (:records kb) id)]
                  [(sx-content kb (:informant d))
                   (into #{} (map #(sx-content kb %)) (:antecedents d))
                   (sx-content kb (:consequence d))
                   (:strength d)])))
        (p/justification-ids (:records kb))))

(defn snapshot [kb]
  {:stored   (stored-content kb)
   :believed (believed-content kb)
   :deduced  (justification-content kb)})

(defn diff-report [ref-snap rete-snap]
  (into {}
        (for [k [:stored :believed :deduced]
              :let [only-ref  (set/difference (get ref-snap k) (get rete-snap k))
                    only-rete (set/difference (get rete-snap k) (get ref-snap k))]
              :when (or (seq only-ref) (seq only-rete))]
          [k {:only-reference (vec (take 6 only-ref))
              :only-rete      (vec (take 6 only-rete))}])))

;; ---- running an op on the reference vs the incremental path -------------

(defmacro with-rete [_rete-kb & body]
  `(binding [chain/*matcher* rete/rete-match-pattern] ~@body))

(def ^:private plainly
  "The identity wrapper — the engine's own defaults."
  (fn [thunk] (thunk)))

(def ^:private through-rete
  "Everything the thunk does, matched through the alpha memories."
  (fn [thunk] (binding [chain/*matcher* rete/rete-match-pattern] (thunk))))

(def ^:private without-suppression
  "Everything the thunk does, with every trigger of a firing enumerated."
  (fn [thunk] (binding [chain/*suppress-duplicate-firings* false] (thunk))))

(defn run-op!
  "Apply `op` to `a-kb` inside `a-wrap` and to `b-kb` inside `b-wrap` — each a
  `(fn [thunk])` establishing whatever binding that side is being held to — and return
  their post-op snapshots.  `op` is `[:assert sentence ctx opts]` or
  `[:retract sentence ctx]`.

  An assert is caught on both sides, so a generated sentence a naming check refuses is
  refused symmetrically; a retract runs only when both KBs hold the sentence as-is.
  Both keep the two in lock-step, which is what lets the comparison localize a
  divergence to the op that caused it."
  [a-kb a-wrap b-kb b-wrap op]
  (case (first op)
    :assert
    (let [[_ sentence ctx opts] op]
      (a-wrap #(try (v/assert a-kb sentence ctx opts) (catch Throwable _)))
      (b-wrap #(try (v/assert b-kb sentence ctx opts) (catch Throwable _))))
    :retract
    (let [[_ sentence ctx] op
          ha (v/handle-of a-kb sentence ctx)
          hb (v/handle-of b-kb sentence ctx)]
      (when (and ha hb)
        (a-wrap #(v/retract! a-kb ha))
        (b-wrap #(v/retract! b-kb hb)))))
  [(snapshot a-kb) (snapshot b-kb)])

(defn apply-op!
  "Apply `op` to both KBs — the reference one plainly, the incremental one under the
  rete matcher — and return their post-op snapshots."
  [ref-kb rete-kb op]
  (run-op! ref-kb plainly rete-kb through-rete op))

;; ---- the random op stream -----------------------------------------------

(def ^:private inds (mapv #(symbol (str "I" %)) (range 8)))
(def ^:private ctxs '[CxLeft CxRight CxBase])

(defn- rand-fact [^java.util.Random rng]
  (let [ind #(nth inds (.nextInt rng (count inds)))
        ctx #(nth ctxs (.nextInt rng (count ctxs)))]
    (case (.nextInt rng 14)
      0 [:assert (list 'parentOf (ind) (ind)) (ctx) {:strength :monotonic}]
      1 [:assert (list 'siblingOf (ind) (ind)) (ctx) {:strength :monotonic}]
      2 [:assert (list 'owns (ind) (ind)) (ctx) {:strength :monotonic}]
      3 [:assert (list (nth '[dog poodle cat bird penguin] (.nextInt rng 5)) (ind))
         (ctx) {:strength :monotonic}]
      4 [:assert (list 'ageOf (ind) (.nextInt rng 5)) (ctx) {:strength :monotonic}]
      5 [:assert (list 'bestFriendOf (ind) (ind)) (ctx) {:strength :monotonic}]
      6 [:assert (list 'parentOf (ind) (ind)) (ctx) {}]        ; a :default premise
      7 [:assert (list 'bird (ind)) (ctx) {:strength :monotonic}]
      8 [:retract (list 'parentOf (ind) (ind)) (ctx)]
      ;; sub-predicate facts: a binary and a ternary literal whose functor the fan has
      ;; to walk down to, which no unary shape above reaches
      9  [:assert (list 'fatherOf (ind) (ind)) (ctx) {:strength :monotonic}]
      10 [:assert (list 'motherOf (ind) (ind)) (ctx) {}]       ; a :default sub-predicate
      11 [:assert (list 'leasesFrom (ind) (ind)) (ctx) {:strength :monotonic}]
      12 [:assert (list 'strictlyBetweenIn (ind) (ind) (ind)) (ctx) {:strength :monotonic}]
      13 [:retract (list 'fatherOf (ind) (ind)) (ctx)])))

;; ---- oracle 0: the stream reaches what the oracles compare --------------

(defn- functors-answering
  "The **functors of the sentexes** `res/match-pattern` answers `pattern` with — so a
  functor other than the pattern's own is the sub-predicate fan's footprint, and an
  empty difference means the fan never ran on this pattern."
  [kb pattern]
  (into #{}
        (comp (map first) (keep #(p/get-sentex (:records kb) %)) (map #(first (:sentence %))))
        (res/match-pattern kb pattern '?ctx)))

(deftest streams-are-not-vacuous
  ;; Agreement between two matchers that both saw nothing is worth nothing, and this
  ;; oracle can reach that state without saying so: `apply-op!` wraps each `v/assert` in
  ;; a symmetric `(catch Throwable _)`, which is what keeps the two KBs in lock-step when
  ;; a generated sentence is refused — and equally what would let a change making *every*
  ;; assert throw compare two empty KBs and pass every assertion in this file.
  ;;
  ;; So the stream is measured before it is trusted.  The last three tallies are what the
  ;; ontology's predicate lattice is there for: the fan-out has to be exercised at arity
  ;; 1, 2 **and** 3, since a matcher that fans only unary functors agrees with the
  ;; reference on every unary probe.
  (let [kb  (doto (tu/isolated-fresh) build-ontology!)
        rng (java.util.Random. 4242)]
    (try
      ;; every tally is a **difference** against the ontology's own content: the rules and
      ;; metadata derive a few things on their own, so "there are derived sentexes" is
      ;; true of a KB the stream never touched
      (let [derived-ids #(into #{} (remove (partial v/premise? kb)) (p/sentex-ids (:records kb)))
            base-sx     (stored-content kb)
            base-dv     (derived-ids)
            base-dd     (set (p/justification-ids (:records kb)))]
        (dotimes [_ 120]
          (let [op (rand-fact rng)]
            (case (first op)
              :assert  (let [[_ s c o] op] (try (v/assert kb s c o) (catch Throwable _)))
              :retract (let [[_ s c] op]
                         (when-let [h (v/handle-of kb s c)] (v/retract! kb h))))))
        (let [stored (stored-content kb)]
          (is (seq (set/difference stored base-sx)) "the stream stored nothing at all")
          (is (seq (set/difference (derived-ids) base-dv))
              "the stream derived nothing — every rule stayed inert")
          (is (seq (set/difference (set (p/justification-ids (:records kb))) base-dd))
              "the stream produced no justification, so belief rests on nothing")
          (testing "and the sub-predicate fan ran at each arity the lattice covers"
            (is (seq (disj (functors-answering kb '(animal ?x)) 'animal))
                "no unary subtype ever answered a supertype pattern")
            (is (seq (disj (functors-answering kb '(parentOf ?x ?y)) 'parentOf))
                "no binary sub-predicate ever answered its super's pattern")
            (is (seq (disj (functors-answering kb '(betweenIn ?x ?y ?z)) 'betweenIn))
                "no ternary sub-predicate ever answered its super's pattern"))))
      (finally (tu/clear-kb! kb)))))

;; ---- oracle 1: the matcher returns the reference set --------------------

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))

(deftest matcher-returns-the-reference-set
  (let [rete-kb (doto (tu/isolated-fresh) build-ontology!)]
    (try
      (rete/track! rete-kb)
      ;; populate with facts of varied shapes across contexts
      (with-rete rete-kb
        (doseq [f '[(parentOf I0 I1) (parentOf I1 I2) (parentOf I2 I3)
                    (siblingOf I1 I4) (siblingOf I5 I1)
                    (siblingOf I8 I8)      ; palindrome: the mirror binds it identically
                    (owns I0 I1) (dog I1) (poodle I2) (cat I3) (bird I4) (penguin I5)
                    (ageOf I0 3) (ageOf I1 4) (bestFriendOf I6 I7)
                    ;; sub-predicate facts, so a super's pattern has something to fan to
                    ;; at arity 2 and arity 3
                    (fatherOf I0 I2) (motherOf I3 I4) (leasesFrom I5 I6)
                    (strictlyBetweenIn I0 I1 I2) (betweenIn I3 I4 I5)]]
          (v/assert rete-kb f 'CxBase {:strength :monotonic}))
        ;; every probe pattern must give the same [handle bindings] set both ways
        (doseq [pat '[(parentOf ?x ?y)      ; fully open
                      (parentOf I1 ?z)       ; leading value (trie-selective)
                      (parentOf ?x I2)       ; leading variable (the network's case)
                      (parentOf I0 I1)       ; ground (a test)
                      (parentOf I9 ?z)       ; no matches
                      (siblingOf ?x I1)      ; symmetric, needs the mirror
                      (siblingOf I1 ?y)      ; symmetric, other order
                      ;; symmetric with BOTH arguments open — the structure that pins the
                      ;; dedup key.  One stored fact answers twice and differently (the
                      ;; mirror swaps the bindings), so a dedup keyed on the handle alone
                      ;; drops the second; the palindrome above is the other side of the
                      ;; same key, and must answer exactly once.
                      (siblingOf ?x ?y)
                      (animal ?a)            ; unary subtype fan-out
                      (dog ?a)               ; subtype (poodle satisfies)
                      (bird ?b)
                      (owns ?p ?a)           ; binary fan-out (leasesFrom satisfies)
                      (owns I5 ?a)           ; …with the leading value pinned
                      (fatherOf ?x ?y)       ; the sub-predicate on its own
                      (betweenIn ?x ?y ?z)   ; ternary fan-out (strictlyBetweenIn satisfies)
                      (betweenIn I0 ?y ?z)   ; …with the leading value pinned
                      (ageOf ?x ?a)
                      (grandparentOf ?x ?z)]]
          (is (= (proj (res/match-pattern rete-kb pat '?ctx))
                 (proj (rete/rete-match-pattern rete-kb pat '?ctx)))
              (str "matcher diverged on " (pr-str pat)))))
      (finally (tu/clear-kb! rete-kb) (rete/disengage!)))))

(deftest the-alpha-mirrors-the-store-across-a-retraction
  ;; The alpha memories hold exactly the stored facts (`vaelii.impl.observe`).  A stale
  ;; entry changes no answer — `candidates` is a superset that unification and belief
  ;; filter again — so the oracles above cannot see one, and a removal the store stops
  ;; reporting is RAM the alpha keeps.  So the count is compared with the count a fresh
  ;; back-fill from the store gives.
  (let [kb (doto (tu/isolated-fresh) build-ontology!)]
    (try
      (rete/track! kb)
      (with-rete kb
        (let [h (v/assert kb '(parentOf I0 I1) 'CxBase {:strength :monotonic})]
          (v/assert kb '(parentOf I1 I2) 'CxBase {:strength :monotonic})
          (v/retract! kb h)))
      (let [held (rete/forget-kb! kb)]
        (rete/track! kb)
        (is (= (rete/forget-kb! kb) held)
            "the alpha holds a fact the store no longer does"))
      (finally (tu/clear-kb! kb) (rete/disengage!)))))

;; ---- oracle 2: end-to-end derived-content equivalence -------------------

(deftest ^:slow end-to-end-agrees-with-the-reference-chain
  (dotimes [trial 6]
    (let [ref-kb  (doto (tu/fresh)          build-ontology!)
          rete-kb (doto (tu/isolated-fresh) build-ontology!)]
      (try
        (rete/track! rete-kb)
        ;; the ontologies alone must already agree (rules + metadata derive some things)
        (is (= (snapshot ref-kb) (snapshot rete-kb))
            (str "trial " trial ": ontologies diverged before any fact\n"
                 (pr-str (diff-report (snapshot ref-kb) (snapshot rete-kb)))))
        (let [rng (java.util.Random. (+ 1000 trial))]
          (dotimes [step 60]
            (let [op (rand-fact rng)
                  [rs es] (apply-op! ref-kb rete-kb op)]
              (is (= rs es)
                  (str "trial " trial " step " step " diverged after " (pr-str op) "\n"
                       (pr-str (diff-report rs es)))))))
        (finally
          (tu/clear-kb! ref-kb)
          (tu/clear-kb! rete-kb)
          (rete/disengage!))))))

;; ---- oracle 3: suppressing duplicate firings derives the same thing -----

(deftest ^:slow suppressed-firings-agree-with-every-trigger-enumerated
  (dotimes [trial 6]
    (let [sup-kb (tu/fresh)
          ref-kb (tu/isolated-fresh)]
      (try
        (build-ontology! sup-kb)
        (without-suppression #(build-ontology! ref-kb))
        (is (= (snapshot sup-kb) (snapshot ref-kb))
            (str "trial " trial ": ontologies diverged before any fact\n"
                 (pr-str (diff-report (snapshot ref-kb) (snapshot sup-kb)))))
        (let [rng (java.util.Random. (+ 2000 trial))]
          (dotimes [step 60]
            (let [op (rand-fact rng)
                  [ss rs] (run-op! sup-kb plainly ref-kb without-suppression op)]
              (is (= rs ss)
                  (str "trial " trial " step " step " diverged after " (pr-str op) "\n"
                       (pr-str (diff-report rs ss)))))))
        (finally
          (tu/clear-kb! sup-kb)
          (tu/clear-kb! ref-kb))))))

;; ---- targeted scenarios (deterministic, for localization) ---------------

(defn- run-both [ops]
  (let [ref-kb  (doto (tu/fresh)          build-ontology!)
        rete-kb (doto (tu/isolated-fresh) build-ontology!)]
    (rete/track! rete-kb)
    (let [snaps (mapv #(apply-op! ref-kb rete-kb %) ops)
          ok    (every? (fn [[r e]] (= r e)) snaps)
          bad   (first (keep-indexed (fn [i [r e]] (when (not= r e) [i (diff-report r e)])) snaps))]
      (tu/clear-kb! ref-kb) (tu/clear-kb! rete-kb) (rete/disengage!)
      [ok bad])))

(deftest scenario-grandparent-leading-variable-join
  (let [[ok bad] (run-both '[[:assert (parentOf I0 I1) CxBase {:strength :monotonic}]
                             [:assert (parentOf I1 I2) CxBase {:strength :monotonic}]
                             [:assert (parentOf I2 I3) CxBase {:strength :monotonic}]])]
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-recursion-and-depth
  (let [ops (mapv (fn [i] [:assert (list 'parentOf (nth inds i) (nth inds (inc i)))
                           'CxBase {:strength :monotonic}])
                  (range 6))
        [ok bad] (run-both ops)]
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-exceptwhen-blocking
  (let [[ok bad] (run-both '[[:assert (bird I0) CxBase {:strength :monotonic}]
                             [:assert (penguin I1) CxBase {:strength :monotonic}]
                             ;; I1 is a bird (penguin<bird) but excepted; I0 flies
                             [:assert (bird I1) CxBase {:strength :monotonic}]
                             [:retract (penguin I1) CxBase]])]  ; releases the exception
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-symmetric-non-trigger-antecedent
  (let [[ok bad] (run-both '[[:assert (siblingOf I2 I3) CxBase {:strength :monotonic}]
                             [:assert (parentOf I0 I2) CxBase {:strength :monotonic}]])]
    ;; uncleAuntOf I0 I3 via (parentOf I0 I2)+(siblingOf I2 I3); siblingOf stored sorted
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-functional-twin-derivation
  (let [[ok bad] (run-both '[[:assert (bestFriendOf I0 I1) CxBase {:strength :monotonic}]
                             [:assert (bestFriendOf I0 I2) CxBase {:strength :monotonic}]])]
    ;; two values for a functional predicate derive (equals I1 I2)
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-sibling-context-no-placement
  (let [[ok bad] (run-both '[[:assert (parentOf I0 I1) CxLeft {:strength :monotonic}]
                             [:assert (parentOf I1 I2) CxRight {:strength :monotonic}]])]
    ;; grandparent join across Left and Right: no common descendant, no placement
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-deferred-antecedent
  (let [[ok bad] (run-both '[[:assert (ageOf I0 2) CxBase {:strength :monotonic}]
                             [:assert (ageOf I1 4) CxBase {:strength :monotonic}]
                             [:assert (ageOf I2 3) CxBase {:strength :monotonic}]])]
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-retraction-and-rederivation
  (let [[ok bad] (run-both '[[:assert (parentOf I0 I1) CxBase {:strength :monotonic}]
                             [:assert (parentOf I1 I2) CxBase {:strength :monotonic}]
                             [:retract (parentOf I1 I2) CxBase]
                             [:assert (parentOf I1 I2) CxBase {:strength :monotonic}]])]
    (is ok (str "diverged: " (pr-str bad)))))
