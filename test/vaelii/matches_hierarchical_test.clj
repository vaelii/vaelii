;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.matches-hierarchical-test
  "Oracle for the set-algebra retrieval (`res/matches-hierarchical`).

  `matches-visible` answers `(p a ?x)` visible from `c` by a product of lookups —
  `|context-up(c)|` contexts × `|specs(p)|` sub-predicates.  The hierarchical path
  leads with the bound argument's root (one lookup, spanning every functor and
  context) and filters the predicate and context hierarchies in memory.  The claim is
  it returns the **identical** `[handle bindings]` set.  This tests that against the
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
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
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
  a result against itself.  `lead_side_cost_test` forces the same switch off for the cost
  half, and for the same reason."
  [f]
  (binding [lc/*enabled* false]
    {:ref      (binding [res/*hierarchical-retrieval* false]                        (proj (f)))
     :scoped   (binding [res/*hierarchical-retrieval* true, res/*lead-side* :scoped]   (proj (f)))
     :auto     (binding [res/*hierarchical-retrieval* true, res/*lead-side* :auto]     (proj (f)))
     :agnostic (binding [res/*hierarchical-retrieval* true, res/*lead-side* :agnostic] (proj (f)))}))

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
  ;; the exhaustive sweep was ~38s for a per-fact equivalence a spread already asserts.
  (tu/with-kb [kb]
    (let [pats (mapcat var-patterns (tu/fact-sample kb 64))]
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
    (let [pats (mapcat var-patterns (tu/fact-sample kb 2))]
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
;; the fallback does.  This test asserts that the fallback is taken at all, which is a
;; claim about the predicate rather than about the two paths agreeing.
(deftest negative-literal-falls-back
  (tu/with-kb [kb]
    (doseq [pat '[(not (parentOf ?x Ann)) (not (able Tweety flying)) (not (dog ?x))]]
      (is (not (#'res/hierarchical-literal? pat))
          (str "a negative literal must not take the set-algebra path: " (pr-str pat))))
    (probed "negative-literal-falls-back"
            (for [pat '[(not (parentOf ?x Ann)) (not (able Tweety flying)) (not (dog ?x))]
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
  ;; postings than there are specs — so `:auto` leads from the slot predicate set
  ;; (`[:argument-slot pos term]`, every functor holding the term), the cold-rebuild small
  ;; side, which the shallow test-world never forces on its own.  Build the
  ;; deep hierarchy here and assert that :scoped, :auto, :agnostic and the matches-visible
  ;; fan-out return the identical set — through the predicate filter (an unrelated
  ;; predicate holds the same term at the same position, so the slot predicate set lists it and the
  ;; lead must keep it out) and the context ancestor set (a sibling-context fact the global
  ;; slot predicate set sees but a scoped read must not).  This is the form a wrong small side would
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
             (long (reads/stored-count-with-arg-global (:index kb) 1 A)))
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

(tu/deftest-kb a-match-stored-where-the-reader-cannot-see-is-no-candidate
  ;; The argument roots and the predicate extent end in the context, so a scoped read
  ;; keeps the contexts at the node that the reader's ancestor set holds and reads only
  ;; their leaves.  A matching fact in a context the reader does not see is then no
  ;; candidate, and the answer set is the reference fan-out's on every lead path: one
  ;; scoped column, two intersected columns, a variable functor's slot-set union, the
  ;; predicate extent of a literal with no bound argument, and the trie walk under a
  ;; ground prefix, whose context level keeps the contexts the reader sees.
  (tu/with-terms [rel rel3 A B C Chid Bhid CxHidden]
    (let [seen  (v/assert kb (list rel A B) 'CxSocialWorld {:strength :monotonic})
          hid   (v/assert kb (list rel A Bhid) CxHidden {:strength :monotonic})
          seen3 (v/assert kb (list rel3 A B C) 'CxSocialWorld {:strength :monotonic})
          hid3  (v/assert kb (list rel3 A B Chid) CxHidden {:strength :monotonic})
          up    '#{CxSocialWorld CxUniverse}]
      (v/assert kb (list rel3 A Bhid C) CxHidden {:strength :monotonic})
      (probed "a-match-stored-where-the-reader-cannot-see-is-no-candidate"
              (for [pat (list (list rel A '?y) (list rel '?x Bhid) (list rel3 A '?y C)
                              (list '?fn A '?y) (list rel '?x '?y) (list rel3 A B '?z))
                    ctx '[CxSocialWorld ?ctx]]
                (let [{:keys [ref scoped auto agnostic]} (lead-sides #(res/matches-visible kb pat ctx))]
                  (is (= ref scoped auto agnostic) (str "diverged on " (pr-str pat) " @ " ctx))
                  (when (= 'CxSocialWorld ctx)
                    (is (not-any? #(or (= Bhid (get (second %) '?y)) (= Chid (get (second %) '?z))) ref)
                        (str (pr-str pat) " answered from a context the reader does not see")))
                  [ref auto])))
      (let [ix (:index kb)]
        (is (= #{seen} (set (p/sentexes-with-args ix rel {1 A} '#{CxSocialWorld CxUniverse})))
            "the scoped read returns the visible leaf alone")
        (is (= #{seen hid} (set (p/sentexes-with-args ix rel {1 A} nil)))
            "and the unscoped read every context's")
        (is (= #{} (set (p/sentexes-with-args ix nil {2 Bhid} '#{CxSocialWorld})))
            "the slot-set union is scoped the same way")
        (is (= #{seen} (set (p/sentexes-with-args ix rel [] '#{CxSocialWorld CxUniverse})))
            "and so is the predicate extent")
        (is (= #{seen hid} (set (p/sentexes-with-functor ix rel))))
        (is (#'res/trie-prefix? [A B '?z]) "the literal takes the trie-prefix lead")
        (is (= #{seen3} (set (#'res/lead-candidates kb #{rel3} [A B '?z] nil up)))
            "the trie walk's context level keeps the contexts the reader sees")
        (is (= #{seen3} (p/lookup ix [rel3 A B '?z '?ctx] up)))
        (is (= #{seen3 hid3} (p/lookup ix [rel3 A B '?z '?ctx])) "and nil keeps every context"))
      (testing "an open literal in a ground context reads the predicate extent's leaf there"
        (let [pat (list rel '?x '?y)]
          (is (= (v/sentexes-matching kb pat 'CxSocialWorld)
                 (binding [res/*arg-root-retrieval* false] (v/sentexes-matching kb pat 'CxSocialWorld))))
          (is (= [seen] (map :id (v/sentexes-matching kb pat 'CxSocialWorld)))))))))

(tu/deftest-kb a-ground-prefix-leads-from-the-argument-roots-when-they-hold-fewer-facts-than-the-walk-visits
  ;; `arg-lead` compares the trie count under `[rel3 A B]` with each bound argument's
  ;; facts in the reader's ancestor set.  Four of the five tuples under the prefix sit in
  ;; a context the reader does not see, so the argument roots lead.  A reader that sees
  ;; every tuple, beside `arg-lead-ratio` times as many facts on each argument, keeps the
  ;; walk.  A variable context counts every fact and compares with the argument's own
  ;; contexts, and `B`, stated in fewer contexts than `A`, leads the intersection.  The
  ;; answer set is the reference fan-out's under both leads.
  (tu/with-terms [rel3 A B C CxHidden]
    (let [ix    (:index kb)
          path  [rel3 A B '?z '?ctx]
          g     [[1 A] [2 B]]
          up    '#{CxSocialWorld CxUniverse}
          seen3 (v/assert kb (list rel3 A B C) 'CxSocialWorld {:strength :monotonic})
          pat   (list rel3 A B '?z)
          same? (fn [ctx]
                  (= (proj (binding [lc/*enabled* false res/*hierarchical-retrieval* false]
                             (res/matches-visible kb pat ctx)))
                     (proj (binding [lc/*enabled* false] (res/matches-visible kb pat ctx)))))]
      (dotimes [i 4]
        (v/assert kb (list rel3 A B (symbol (str C "H" i))) CxHidden {:strength :monotonic}))
      (v/assert kb (list rel3 A (symbol (str B "X")) C) 'CxUniverse {:strength :monotonic})
      (is (= g (#'res/arg-lead ix rel3 path g up)))
      (is (= [[2 B] [1 A]] (#'res/arg-lead ix rel3 path g nil)))
      (is (= #{seen3} (set (#'res/lead-candidates kb #{rel3} [A B '?z] nil up))))
      (is (same? 'CxSocialWorld))
      (is (same? '?ctx))
      (dotimes [i (* 5 @#'res/arg-lead-ratio)]
        (v/assert kb (list rel3 A (symbol (str B "W" i)) C) CxHidden {:strength :monotonic})
        (v/assert kb (list rel3 (symbol (str A "W" i)) B C) CxHidden {:strength :monotonic}))
      (is (nil? (#'res/arg-lead ix rel3 path g (conj up CxHidden))))
      (is (nil? (#'res/arg-lead ix rel3 path g nil)))
      (is (= g (#'res/arg-lead ix rel3 path g up)) "the facts the reader cannot see count for nothing")
      (is (same? 'CxSocialWorld))
      (is (same? '?ctx)))))

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

(tu/deftest-kb a-literal-whose-spec-folds-onto-its-comparison-sibling-matches-the-stored-spelling
  ;; `greaterThan` is stored as `lessThan` with its arguments reversed, so a literal on
  ;; `greaterThan`, or on a predicate `greaterThan` is a spec of, matches a stored
  ;; `lessThan` fact.  Every lead and the reference fan-out return the same set.
  (tu/with-terms [A B C relGt]
    (let [h2 (v/assert kb (list 'lessThan B A) 'CxSocialWorld {:strength :monotonic})
          h3 (v/assert kb (list 'lessThan A B C) 'CxSocialWorld {:strength :monotonic})]
      (v/assert kb (list 'genl 'greaterThan relGt) 'CxSocialWorld {:strength :monotonic})
      (doseq [[pat want] [[(list 'greaterThan A B) #{[h2 {}]}]
                          [(list 'greaterThan A '?x) #{[h2 {'?x B}]}]
                          [(list 'greaterThan C B '?z) #{[h3 {'?z A}]}]
                          [(list relGt A B) #{[h2 {}]}]
                          [(list relGt C B A) #{[h3 {}]}]]]
        (is (= {:ref want :scoped want :auto want :agnostic want}
               (lead-sides #(res/matches-visible kb pat 'CxSocialWorld)))
            (pr-str pat)))
      (is (v/ask? kb (list 'greaterThan A B) 'CxSocialWorld)))))
