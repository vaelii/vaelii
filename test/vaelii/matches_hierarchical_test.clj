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
  the contexts these patterns name (`CxMantle`, `CxSocialWorld`, …) are the
  world's. Loaded without it, each comparison below is `#{}` against `#{}` — two paths
  agreeing about nothing, which is what an oracle looks like when it has stopped
  oracling. `probed` is the standing check against that: it counts the non-empty
  comparisons and fails when a run makes none."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.literal-cache :as lc]
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
  matched something asserted non-zero.  An agreeing pair of empty sets is not evidence
  the two paths agree; it is evidence neither was asked anything."
  [what results]
  (is (pos? (count (filter (fn [[off on]] (or (seq off) (seq on))) results)))
      (str what ": every comparison was empty on both sides — the fixture is not"
           " carrying the facts these patterns name, so this test proved nothing")))

(defn- both-ways [f]
  [(binding [res/*hierarchical-retrieval* false] (proj (f)))
   (binding [res/*hierarchical-retrieval* true]  (proj (f)))])

(defn- lead-sides
  "`f` projected under each `res/*lead-side*` — `:scoped` (one predicate-scoped bucket per
  spec), `:auto` (the count-driven default) and `:agnostic` (the small side, always) —
  plus the `matches-visible` fan-out as ground truth (`:ref`).  The side
  `lead-candidates` reads from is a pure cost decision, so all four must be the identical
  set.

  **The literal cache is off for the comparison, and that is what makes it one.**
  `*lead-side*` is not part of `matches-visible`'s cache key — nothing in the engine
  rebinds it, so keying on it would only fragment the cache — which means the second and
  third arms here would be served the first arm's answer and the oracle would be checking
  a result against itself.  `lead_side_cost_test` pins the same switch off for the cost
  half, and for the same reason."
  [f]
  (binding [lc/*enabled* false]
    {:ref      (binding [res/*hierarchical-retrieval* false]                        (proj (f)))
     :scoped   (binding [res/*hierarchical-retrieval* true, res/*lead-side* :scoped]   (proj (f)))
     :auto     (binding [res/*hierarchical-retrieval* true, res/*lead-side* :auto]     (proj (f)))
     :agnostic (binding [res/*hierarchical-retrieval* true, res/*lead-side* :agnostic] (proj (f)))}))

(defn- fact-sentences
  "Up to `n` distinct positive ground-fact bodies (no rules), sampled *evenly* across
  the world's stored facts rather than taking the first `n` — the leading facts
  cluster by predicate, so an even spread spans more functors for the same cost.
  The handles are sorted first: `sentex-ids` is a set in the store's own order, so the
  same world gives the same sample on every backend.  This is an equivalence oracle, so
  the sample is a regression net over the fact space, not an exhaustive sweep of it."
  [kb n]
  (let [all (->> (sort (p/sentex-ids (:records kb)))
                 (keep #(p/get-sentex (:records kb) %))
                 (remove #(some? (:antecedent %)))
                 (keep sx/body)
                 (filter #(and (sequential? %) (symbol? (nm/functor %))))
                 distinct
                 vec)
        m   (count all)]
    (if (<= m n)
      all
      (mapv #(nth all (quot (* % m) n)) (range n)))))

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

(def ^:private ctxs '[?ctx CxMantle CxNaturalWorld CxSocialWorld
                      CxUniverse CxStories])

(deftest ^:slow hierarchical-equals-nested-fanout
  ;; A sample of the world's facts (each expanded to ~8 patterns) × every context,
  ;; comparing the two retrieval paths.  64 sampled facts rather than the first 200:
  ;; the exhaustive sweep was ~38s for a per-fact equivalence a spread already pins.
  (tu/with-kb [kb]
    (let [pats (mapcat var-patterns (fact-sentences kb 64))]
      (is (seq pats))
      (doseq [pat pats, ctx ctxs]
        (let [[off on] (both-ways #(res/matches-visible kb pat ctx))]
          (is (= off on)
              (str "diverged on " (pr-str pat) " @ " ctx
                   "\n  off: " (pr-str off) "\n  on:  " (pr-str on))))))))

(deftest a-sample-of-the-hierarchical-oracle-runs-at-default
  ;; The sweep above is `^:slow`, so `lein gate` never runs this harness.  Two facts'
  ;; patterns keep it running at `:default`, against the variable context, a leaf and
  ;; the root; the sweep takes 64 facts to all six.  The first read under each of the
  ;; other three builds its visibility closure, about 0.35 s apiece, which is what leaving
  ;; them out saves.
  (tu/with-kb [kb]
    (let [pats (mapcat var-patterns (fact-sentences kb 2))]
      (is (seq pats))
      (doseq [pat pats, ctx '[?ctx CxMantle CxUniverse]]
        (let [[off on] (both-ways #(res/matches-visible kb pat ctx))]
          (is (= off on) (str "diverged on " (pr-str pat) " @ " ctx)))))))

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

(deftest a-symmetric-spec-does-not-mirror-its-plain-super
  ;; `(symmetric Sub)` under `(genl Sub Super)` widens the candidate buckets for a
  ;; `Super` goal — but whether a candidate may match mirrored is that candidate's own
  ;; functor's question.  A stored `(Super A B)` must not answer `(Super ?x A)` through
  ;; the mirror the symmetric sub earned, and the two retrieval paths must agree.
  (tu/with-kb [kb]
    (tu/with-terms [likes adores Karl Lena Mio]
      (v/assert kb (list 'symmetric adores) 'CxUniverse)
      (v/assert kb (list 'genl adores likes) 'CxUniverse)
      (v/assert kb (list likes Karl Lena) 'CxUniverse)     ; plain super, one way
      (v/assert kb (list adores Mio Karl) 'CxUniverse)     ; symmetric sub
      (let [answers (fn [pat]
                      (let [[off on] (both-ways #(res/matches-visible kb pat 'CxUniverse))]
                        (is (= off on) (str "the two paths diverged on " (pr-str pat)))
                        (into #{} (map #(get (second %) '?x)) on)))]
        ;; the sub's own fact answers directly; the super's `(likes Karl Lena)` must
        ;; not come back as `?x = Lena` through a mirror `likes` never declared
        (is (= #{Mio} (answers (list likes '?x Karl))))
        ;; and the mirror still answers where it is declared: the symmetric sub's
        ;; fact read in the order nothing stored
        (is (= #{Mio} (answers (list adores Karl '?x))))))))

;; A `not`-headed sentence is rejected by `hierarchical-literal?`, and `matches-hierarchical`
;; then calls the same `matches-visible*` the flag-off branch calls — so comparing the two
;; flag settings on a negative literal compares one function with itself and holds whatever
;; the fallback does.  What is worth pinning is the fallback being taken at all, which is a
;; claim about the predicate rather than about the two paths agreeing.
(deftest negative-literal-falls-back
  (tu/with-kb [kb]
    (doseq [pat '[(not (parentOf ?x Ann)) (not (hasCapability Tweety flying)) (not (dog ?x))]]
      (is (not (#'res/hierarchical-literal? pat))
          (str "a negative literal must not take the set-algebra path: " (pr-str pat))))
    (probed "negative-literal-falls-back"
            (for [pat '[(not (parentOf ?x Ann)) (not (hasCapability Tweety flying)) (not (dog ?x))]
                  ctx ctxs]
              (let [[off on :as both] (both-ways #(res/matches-visible kb pat ctx))]
                (is (= off on) (str "negative diverged on " (pr-str pat) " @ " ctx))
                both)))))

(tu/deftest-kb predicate-subsumption-under-hierarchical
  ;; a temporary sub-predicate of the real parentOf: the hierarchical path must fan the
  ;; predicate dimension exactly as the nested one does
  (tu/with-terms [fatherOf A B]
    (v/assert kb (list 'genl fatherOf 'parentOf) 'CxMantle {:strength :monotonic})
    (v/assert kb (list fatherOf A B) 'CxSocialWorld {:strength :monotonic})
    (probed "predicate-subsumption-under-hierarchical"
            (for [pat (list (list 'parentOf (symbol "?x") (symbol "?y"))
                            (list 'parentOf A (symbol "?y"))
                            (list 'parentOf (symbol "?x") B)
                            (list 'parentOf A B))
                  ctx '[?ctx CxSocialWorld CxMantle CxUniverse]]
              (let [[off on :as both] (both-ways #(res/matches-visible kb pat ctx))]
                (is (= off on) (str "subsumption+hierarchical diverged on " (pr-str pat) " @ " ctx
                                    "\n  off: " (pr-str off) "\n  on:  " (pr-str on)))
                both)))))

(tu/deftest-kb small-side-lead-agrees-with-scoped-and-reference
  ;; The one cost decision in `lead-candidates` a flag reaches (`res/*lead-side*`): a
  ;; concrete predicate with a spec closure, a ground argument, and a term holding fewer
  ;; postings than there are specs — so `:auto` leads from the predicate-AGNOSTIC bucket
  ;; (`[:argument-slot pos term]`, every functor holding the term), the cold-rebuild small
  ;; side, which the shallow test-world never forces on its own.  Build the
  ;; deep hierarchy here and pin that :scoped, :auto, :agnostic and the matches-visible
  ;; fan-out return the identical set — through the predicate filter (an unrelated
  ;; predicate holds the same term at the same position, so the agnostic bucket returns it
  ;; and `pred-ok?` must drop it) and the context ancestor set (a sibling-context fact the global
  ;; roster sees but a scoped read must not).  This is the form a wrong small side would
  ;; leak on, where the shallow oracle above would stay green.
  (tu/with-terms [broadRel otherRel A B1 B2 Bother CxSib Bsib]
    (let [subs (vec (repeatedly 8 tu/tmp-pred))]
      (doseq [s subs] (v/assert kb (list 'genl s broadRel) 'CxUniverse {:strength :monotonic}))
      (v/assert kb (list (subs 2) A B1)      'CxSocialWorld {:strength :monotonic})
      (v/assert kb (list (subs 5) A B2)      'CxSocialWorld {:strength :monotonic})
      (v/assert kb (list otherRel A Bother)  'CxSocialWorld {:strength :monotonic})  ; predicate decoy
      (v/assert kb (list (subs 3) A Bsib)    CxSib          {:strength :monotonic})  ; sibling-context decoy
      ;; the branch is genuinely the small side: more specs than A has postings, so `:auto`
      ;; reads the agnostic bucket — assert it rather than trust the construction
      (is (> (count (#'res/sub-predicates kb broadRel 'CxSocialWorld))
             (long (p/count-with-arg (:index kb) 1 A)))
          "the constructed KB does not force the small-side branch — retune it")
      ;; the reference fan-out and the small side, as the pair `probed` reads: four sides
      ;; agreeing on nothing is the same non-evidence two do
      (probed "small-side-lead-agrees-with-scoped-and-reference"
              (for [pat (list (list broadRel A '?y) (list broadRel A B1))
                    ctx  '[CxSocialWorld CxUniverse ?ctx]]
                (let [{:keys [ref scoped auto agnostic]} (lead-sides #(res/matches-visible kb pat ctx))]
                  (is (= ref scoped auto agnostic)
                      (str "lead-side diverged on " (pr-str pat) " @ " ctx
                           "\n  ref:      " (pr-str ref)
                           "\n  scoped:   " (pr-str scoped)
                           "\n  auto:     " (pr-str auto)
                           "\n  agnostic: " (pr-str agnostic)))
                  [ref agnostic])))
      ;; and the answer set is exactly the two believed sub-facts, the unrelated predicate
      ;; and the invisible sibling context both correctly excluded from the agnostic lead
      (let [ys (into #{} (map #(get (second %) '?y))
                     (binding [lc/*enabled* false, res/*lead-side* :agnostic]
                       (res/matches-visible kb (list broadRel A '?y) 'CxSocialWorld)))]
        (is (= #{B1 B2} ys) (str "the agnostic lead's answer set is wrong: " (pr-str ys)))))))

(tu/deftest-kb end-to-end-ask-and-backward-unchanged
  ;; the consumers of matches-visible must be invariant under the flag
  (tu/with-kb [kb]
    (probed "end-to-end-ask-and-backward-unchanged"
            (for [goal '[(parentOf ?x Ann) (siblingOf Carol ?y) (animal ?x)
                         (grandparentOf ?x Ann) (ancestorOf Tom ?y)]
                  ctx '[?ctx CxMantle CxNaturalWorld]]
              (let [ask-off (binding [res/*hierarchical-retrieval* false] (set (v/ask kb goal ctx)))
                    ask-on  (binding [res/*hierarchical-retrieval* true]  (set (v/ask kb goal ctx)))]
                (is (= ask-off ask-on) (str "ask diverged on " (pr-str goal) " @ " ctx))
                [ask-off ask-on])))))
