;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arg-root-retrieval-test
  "Oracle for the argument-root retrieval in `res/match-one`.

  The trie narrows only left to right, so a pattern whose first argument is a
  variable but a later argument is ground — `(parentOf ?x Tom)` — forces a full
  fan-out.  `res/*arg-root-retrieval*` lets `match-one` answer that from the
  predicate-scoped argument root (`[:argument-root pred pos term]`) instead, with a
  single set read.  The claim is
  that this changes only *how* candidates are fetched, never *which* sentexes match:
  the root returns a superset of the trie's hits and the existing `unify` filters it
  to the same set.

  This pins that claim the way the taxonomy pins its incremental closures against a
  rebuild — the flag ON must return the identical result set the flag OFF (pure
  trie) does, over patterns generated from the test-world's own stored facts (so they
  actually match, and cover numeric arguments the roots do not index, symmetric
  predicates, both polarities, and every argument position), and end to end through
  `query`, `matches-visible`, `backward`, and `ask`.

  **The fixture loads the world, and the probes below name its cast.** The starter is
  schema — it declares `parentOf` and `birthYearOf` and asserts no instance of either —
  so under a starter-only fixture every comparison here is `#{}` against `#{}`: two
  retrieval paths agreeing about nothing. `probed` is the standing check, and it is why
  the equality below means something."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! world/load-into))))
(use-fixtures :each (tu/neutral))

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))

(defn- probed
  "`results` — the `[off on]` pairs one test compared — with the count that actually
  matched something asserted non-zero.  Two empty sets are equal, so an oracle whose
  fixture stops carrying the facts it probes goes green while checking nothing; this is
  what makes that a failure instead."
  [what results]
  (is (pos? (count (filter (fn [[off on]] (or (seq off) (seq on))) results)))
      (str what ": every comparison was empty on both sides — the fixture is not"
           " carrying the facts these patterns name, so this test proved nothing")))

(defn- both-ways
  "The [handle bindings] set `f` yields with arg-root retrieval off (pure trie) and
  on — the pair the oracle demands be equal."
  [f]
  [(binding [res/*arg-root-retrieval* false] (proj (f)))
   (binding [res/*arg-root-retrieval* true]  (proj (f)))])

(defn- fact-sentences
  "Up to `n` distinct positive bodies of stored ground facts (no rules), sampled
  *evenly* across the world's facts rather than the first `n` — the leading facts
  cluster by predicate, so an even spread spans more functors and argument shapes for
  the same cost.  The handles are sorted first: `sentex-ids` is a set in the store's own
  order, so the same world gives the same sample on every backend.  This is a
  trie-vs-arg-root equivalence oracle, so the sample is a regression net over the fact
  space."
  [kb n]
  (let [all (->> (sort (p/sentex-ids (:records kb)))
                 (keep #(p/get-sentex (:records kb) %))
                 (remove #(some? (:antecedent %)))     ; drop rules
                 (keep sx/body)
                 (filter #(and (sequential? %) (symbol? (nm/functor %))))
                 distinct
                 vec)
        m   (count all)]
    (if (<= m n)
      all
      (mapv #(nth all (quot (* % m) n)) (range n)))))

(defn- var-patterns
  "For a ground fact `(pred a1 a2 …)`, a spread of query patterns that stress the
  trie's weak spot: each single argument blanked to a variable (the leading-variable
  case among them), all blanked, none blanked, a non-matching probe, and the same
  spread with the **functor** blanked — `(?type Muffet)`, where the variable sits at
  path level 0 so every ground argument is stuck behind it.  The all-blank functor
  pattern has nothing indexable to lead with and must stay on the trie."
  [fact]
  (let [[pred & args] fact
        n     (count args)
        open  (fn [idxs] (map-indexed (fn [i a] (if (idxs i) (symbol (str "?v" i)) a)) args))
        blank (fn [idxs] (cons pred (open idxs)))]
    (distinct
     (concat
      [fact]                                          ; fully ground (a test)
      (for [i (range n)] (blank #{i}))                ; one position variable
      [(blank (set (range n)))]                       ; fully open
      (when (pos? n) [(cons pred (cons 'ZzzNoSuchIndividual (rest args)))])
      [(cons '?fn args)]                              ; functor open, arguments ground
      (for [i (range n)] (cons '?fn (open #{i})))     ; functor open + one argument open
      [(cons '?fn (open (set (range n))))]))))        ; nothing pinned at all

(deftest ^:slow match-pattern-arg-root-equals-trie
  ;; 80 sampled facts (each ~8 patterns) rather than the first 250: the exhaustive
  ;; sweep was ~11s for a per-pattern trie-vs-arg-root equality a spread already pins.
  (tu/with-kb [kb]
    (let [pats (mapcat var-patterns (fact-sentences kb 80))]
      (is (seq pats))
      (doseq [pat pats]
        (let [[off on] (both-ways #(res/match-pattern kb pat '?ctx))]
          (is (= off on)
              (str "match-pattern diverged (flag off vs on) on " (pr-str pat)
                   "\n  off: " (pr-str off) "\n  on:  " (pr-str on))))))))

(deftest ^:slow matches-visible-arg-root-equals-trie
  (tu/with-kb [kb]
    ;; context-scoped retrieval walks the same match-one, so the context up-closure
    ;; must not change the answer either
    (probed "matches-visible-arg-root-equals-trie"
            (for [ctx '[CxMantle CxNaturalWorld CxSocialWorld CxUniverse]
                  pat (mapcat var-patterns (fact-sentences kb 48))]    ; sampled, not first 120
              (let [[off on :as both] (both-ways #(res/matches-visible kb pat ctx))]
                (is (= off on) (str "matches-visible diverged on " (pr-str pat) " @ " ctx))
                both)))))

(deftest a-sample-of-the-arg-root-oracle-runs-at-default
  ;; The two sweeps above are `^:slow`, so `lein gate` never runs this harness.  Four
  ;; facts' patterns through both comparisons keep it running at `:default`; the sweeps
  ;; widen the sample to 80 and 48 facts.
  (tu/with-kb [kb]
    (let [pats (mapcat var-patterns (fact-sentences kb 4))]
      (is (seq pats))
      (doseq [pat pats]
        (let [[off on] (both-ways #(res/match-pattern kb pat '?ctx))]
          (is (= off on) (str "match-pattern diverged on " (pr-str pat)))))
      (probed "a-sample-of-the-arg-root-oracle-runs-at-default"
              (for [ctx '[CxMantle CxUniverse]
                    pat pats]
                (let [[off on :as both] (both-ways #(res/matches-visible kb pat ctx))]
                  (is (= off on) (str "matches-visible diverged on " (pr-str pat) " @ " ctx))
                  both))))))

(deftest leading-variable-binary-patterns
  ;; the case the arg root exists for: a bound *second* argument with a variable first
  (tu/with-kb [kb]
    (probed "leading-variable-binary-patterns"
            (for [pred '[parentOf siblingOf marriedTo childOf owns locatedIn]
                  ind  '[Tom Bob Ann Carol Muffet Sam Tweety Dave]]
              (let [pat (list pred (symbol "?x") ind)
                    [off on :as both] (both-ways #(res/match-pattern kb pat '?ctx))]
                (is (= off on) (str "diverged on " (pr-str pat)))
                both)))))

(deftest numeric-argument-stays-on-the-trie
  ;; `birthYearOf` has a numeric year, and a number is not an indexable term, so
  ;; `(birthYearOf ?x 1970)` must fall back to the trie and still return exactly what the
  ;; trie returns.  1970 and 1995 are the world's two; the rest match nothing on purpose,
  ;; since falling back correctly on an absent value is the same claim.
  (tu/with-kb [kb]
    (probed "numeric-argument-stays-on-the-trie"
            (for [yr [1970 1995 1888 2000 42]]
              (let [pat (list 'birthYearOf (symbol "?p") yr)
                    [off on :as both] (both-ways #(res/match-pattern kb pat '?ctx))]
                (is (= off on) (str "diverged on " (pr-str pat)))
                both)))))

;; the case the user asked about: knowing *more* terms.  A shared individual sits at
;; the same argument position across several predicates, so a single argument root is
;; loose; intersecting it with the functor root (and, for a ternary, a second argument
;; root) must still return exactly what the trie does.
(tu/deftest-kb multi-column-narrowing
  (tu/with-terms [Shared P1 P2 P3 X Z Other parentRel sibRel marRel rel]
    ;; Shared appears at position 2 across three binary predicates ...
    (v/assert kb (list parentRel P1 Shared) 'CxMantle {:strength :monotonic})
    (v/assert kb (list sibRel    P2 Shared) 'CxMantle {:strength :monotonic})
    (v/assert kb (list marRel    P3 Shared) 'CxMantle {:strength :monotonic})
    ;; ... and in a ternary predicate with two ground arguments to intersect
    (v/assert kb (list rel X Shared Z) 'CxMantle {:strength :monotonic})
    (v/assert kb (list rel X Other  Z) 'CxMantle {:strength :monotonic})
    (doseq [pat [(list parentRel (symbol "?x") Shared)   ; functor ∩ [2 Shared]
                 (list sibRel    (symbol "?x") Shared)
                 (list marRel    (symbol "?x") Shared)
                 (list rel (symbol "?x") Shared Z)        ; functor ∩ [2 Shared] ∩ [3 Z]
                 (list rel (symbol "?x") (symbol "?y") Z)
                 (list rel X (symbol "?y") Z)]]           ; leading value + later ground
      (let [[off on] (both-ways #(res/match-pattern kb pat '?ctx))]
        (is (= off on) (str "multi-column diverged on " (pr-str pat)
                            "\n  off: " (pr-str off) "\n  on:  " (pr-str on)))))))

;; the public `query` shares the same divert: it routes through `res/raw-match`, so a
;; believed-literal query pinning an argument *after* a variable is answered from the
;; argument root, not a leading-variable fan-out.  Flag on == flag off, over facts this
;; test asserts itself (so the equality is non-vacuous, unlike a probe for a cast that
;; the schema-only starter never loaded).
(tu/deftest-kb query-shares-the-argument-root-chooser
  (tu/with-terms [Shared P1 P2 P3 X Z Other parentRel sibRel marRel rel]
    (v/assert kb (list parentRel P1 Shared) 'CxMantle {:strength :monotonic})
    (v/assert kb (list sibRel    P2 Shared) 'CxMantle {:strength :monotonic})
    (v/assert kb (list marRel    P3 Shared) 'CxMantle {:strength :monotonic})
    (v/assert kb (list rel X Shared Z) 'CxMantle {:strength :monotonic})
    (v/assert kb (list rel X Other  Z) 'CxMantle {:strength :monotonic})
    (letfn [(q [goal ctx flag]
              (binding [res/*arg-root-retrieval* flag]
                (set (map :sentence (v/sentexes-matching kb goal ctx)))))]
      (doseq [ctx  (list 'CxMantle '?ctx)                 ; concrete and wildcard context
              goal [(list parentRel (symbol "?x") Shared)      ; functor ∩ [2 Shared]
                    (list sibRel    (symbol "?x") Shared)
                    (list marRel    (symbol "?x") Shared)
                    (list rel (symbol "?x") Shared Z)           ; functor ∩ [2 Shared] ∩ [3 Z]
                    (list rel (symbol "?x") (symbol "?y") Z)]]  ; a value past the leading vars
        (let [off (q goal ctx false)
              on  (q goal ctx true)]
          (is (= off on) (str "query diverged (flag off vs on) on " (pr-str goal)
                              " @ " ctx "\n  off: " (pr-str off) "\n  on:  " (pr-str on)))
          ;; not vacuous: the leading-variable query actually finds its facts
          (is (seq on) (str "expected matches for " (pr-str goal) " @ " ctx)))))))

(deftest end-to-end-paths-unchanged
  (tu/with-kb [kb]
    (testing "query returns the same believed matches"
      (probed "end-to-end-paths-unchanged/query"
              (for [goal '[(parentOf ?x Ann) (siblingOf ?x Ann) (parentOf Tom ?y)
                           (marriedTo ?x Tom) (owns ?p ?a)]]
                (let [off (binding [res/*arg-root-retrieval* false]
                            (set (map :sentence (v/sentexes-matching kb goal '?ctx))))
                      on  (binding [res/*arg-root-retrieval* true]
                            (set (map :sentence (v/sentexes-matching kb goal '?ctx))))]
                  (is (= off on) (str "query diverged on " (pr-str goal)))
                  [off on]))))
    (testing "backward and ask agree with the trie"
      (doseq [goal '[(grandparentOf ?x Ann) (ancestorOf ?x Ann) (childOf Ann ?y)
                     (uncleOf ?x ?y)]]
        (let [bw-off (binding [res/*arg-root-retrieval* false]
                       (set (v/prove kb goal 'CxMantle)))
              bw-on  (binding [res/*arg-root-retrieval* true]
                       (set (v/prove kb goal 'CxMantle)))
              ask-off (binding [res/*arg-root-retrieval* false]
                        (set (v/ask kb goal '?ctx)))
              ask-on  (binding [res/*arg-root-retrieval* true]
                        (set (v/ask kb goal '?ctx)))]
          (is (= bw-off bw-on) (str "backward diverged on " (pr-str goal)))
          (is (= ask-off ask-on) (str "ask diverged on " (pr-str goal))))))))
