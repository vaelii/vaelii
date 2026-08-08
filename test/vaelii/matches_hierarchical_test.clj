;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.matches-hierarchical-test
  "Oracle for the set-algebra retrieval (`res/matches-hierarchical`).

  `matches-visible` answers `(p a ?x)` visible from `c` by a product of lookups —
  `|context-up(c)|` contexts × `|specs(p)|` sub-predicates.  The hierarchical path
  leads with the bound argument's root (one lookup, spanning every functor and
  context) and filters the predicate and context hierarchies in memory.  The claim is
  it returns the **identical** `[handle bindings]` set.  This pins that against the
  nested fan-out (flag off) over patterns generated from the test-world's own facts,
  across concrete and variable contexts, symmetric predicates, negative literals (the
  fallback), and — with a temporary predicate-genl edge — predicate subsumption.

  **The fixture loads the world, and every probe here depends on it.** The starter is
  schema: it declares `parentOf` and `siblingOf` and asserts no instance of either, and
  the contexts these patterns name (`MantleContext`, `SocialWorldContext`, …) are the
  world's. Loaded without it, each comparison below is `#{}` against `#{}` — two paths
  agreeing about nothing, which is what an oracle looks like when it has stopped
  oracling. `probed` is the standing check against that: it counts the non-empty
  comparisons and fails when a run makes none."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))

(defn- probed
  "`results` — the `[off on]` pairs one test compared — with the count that actually
  matched something asserted non-zero.  An agreeing pair of empty sets is not evidence
  the two paths agree; it is evidence neither was asked anything."
  [what results]
  (is (pos? (count (filter (fn [[off on]] (or (seq off) (seq on))) results)))
      (str what ": every comparison was empty on both sides — the fixture is not"
           " carrying the facts these patterns name, so this test proved nothing")))

(defn- both-ways [f]
  [(binding [res/*hierarchical-retrieval* false] (proj (f)))
   (binding [res/*hierarchical-retrieval* true]  (proj (f)))])

(defn- fact-sentences [kb n]
  (->> (p/sentex-ids (:records kb))
       (keep #(p/get-sentex (:records kb) %))
       (remove #(some? (:antecedent %)))
       (keep sx/body)
       (filter #(and (sequential? %) (symbol? (nm/functor %))))
       distinct
       (take n)))

(defn- var-patterns [fact]
  (let [[pred & args] fact
        n     (count args)
        open  (fn [idxs] (map-indexed (fn [i a] (if (idxs i) (symbol (str "?v" i)) a)) args))
        blank (fn [idxs] (cons pred (open idxs)))]
    (distinct
     (concat [fact]
             (for [i (range n)] (blank #{i}))
             [(blank (set (range n)))]
             (when (pos? n) [(cons pred (cons 'ZzzNoSuch (rest args)))])
             ;; the functor blanked — `(?type Muffet)`.  There is no predicate hierarchy
             ;; to filter by, so the set-algebra path must reach the identical set from
             ;; the argument root alone, and must bind the functor variable.
             [(cons '?fn args)]
             (for [i (range n)] (cons '?fn (open #{i})))
             [(cons '?fn (open (set (range n))))]))))

(def ^:private ctxs '[?ctx MantleContext NaturalWorldContext SocialWorldContext
                      UniverseContext StoriesContext])

(deftest ^:slow hierarchical-equals-nested-fanout
  (tu/with-kb [kb]
    (let [pats (mapcat var-patterns (fact-sentences kb 200))]
      (is (seq pats))
      (doseq [pat pats, ctx ctxs]
        (let [[off on] (both-ways #(res/matches-visible kb pat ctx))]
          (is (= off on)
              (str "diverged on " (pr-str pat) " @ " ctx
                   "\n  off: " (pr-str off) "\n  on:  " (pr-str on))))))))

(deftest symmetric-both-orders
  (tu/with-kb [kb]
    ;; siblingOf is symmetric in the starter — a mirrored fact must be found either way
    (probed "symmetric-both-orders"
            (for [pat '[(siblingOf ?x Ann) (siblingOf Ann ?y) (siblingOf ?x ?y)
                        (marriedTo ?x Tom) (marriedTo Tom ?y)]
                  ctx ctxs]
              (let [[off on :as both] (both-ways #(res/matches-visible kb pat ctx))]
                (is (= off on) (str "symmetric diverged on " (pr-str pat) " @ " ctx))
                both)))))

;; A `not`-headed sentence is rejected by `hierarchical-literal?`, and `matches-hierarchical`
;; then calls the same `matches-visible*` the flag-off branch calls — so comparing the two
;; flag settings on a negative literal compares one function with itself and holds whatever
;; the fallback does.  What is worth pinning is the fallback being taken at all, which is a
;; claim about the predicate rather than about the two paths agreeing.
(deftest negative-literal-falls-back
  (tu/with-kb [kb]
    (doseq [pat '[(not (parentOf ?x Ann)) (not (flies Tweety)) (not (dog ?x))]]
      (is (not (#'res/hierarchical-literal? pat))
          (str "a negative literal must not take the set-algebra path: " (pr-str pat))))
    (probed "negative-literal-falls-back"
            (for [pat '[(not (parentOf ?x Ann)) (not (flies Tweety)) (not (dog ?x))]
                  ctx ctxs]
              (let [[off on :as both] (both-ways #(res/matches-visible kb pat ctx))]
                (is (= off on) (str "negative diverged on " (pr-str pat) " @ " ctx))
                both)))))

(tu/deftest-kb predicate-subsumption-under-hierarchical
  ;; a temporary sub-predicate of the real parentOf: the hierarchical path must fan the
  ;; predicate dimension exactly as the nested one does
  (tu/with-terms [fatherOf A B]
    (v/assert kb (list 'genl fatherOf 'parentOf) 'MantleContext {:strength :monotonic})
    (v/assert kb (list fatherOf A B) 'SocialWorldContext {:strength :monotonic})
    (doseq [pat (list (list 'parentOf (symbol "?x") (symbol "?y"))
                      (list 'parentOf A (symbol "?y"))
                      (list 'parentOf (symbol "?x") B)
                      (list 'parentOf A B))
            ctx '[?ctx SocialWorldContext MantleContext UniverseContext]]
      (let [[off on] (both-ways #(res/matches-visible kb pat ctx))]
        (is (= off on) (str "subsumption+hierarchical diverged on " (pr-str pat) " @ " ctx
                            "\n  off: " (pr-str off) "\n  on:  " (pr-str on)))))))

(tu/deftest-kb end-to-end-ask-and-backward-unchanged
  ;; the consumers of matches-visible must be invariant under the flag
  (tu/with-kb [kb]
    (probed "end-to-end-ask-and-backward-unchanged"
            (for [goal '[(parentOf ?x Ann) (siblingOf Carol ?y) (animal ?x)
                         (grandparentOf ?x Ann) (ancestorOf Tom ?y)]
                  ctx '[?ctx MantleContext NaturalWorldContext]]
              (let [ask-off (binding [res/*hierarchical-retrieval* false] (set (v/ask kb goal ctx)))
                    ask-on  (binding [res/*hierarchical-retrieval* true]  (set (v/ask kb goal ctx)))]
                (is (= ask-off ask-on) (str "ask diverged on " (pr-str goal) " @ " ctx))
                [ask-off ask-on])))))
