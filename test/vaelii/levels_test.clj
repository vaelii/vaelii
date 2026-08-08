;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.levels-test
  "The lookup-to-query stack: eight levels of escalating machinery over one goal.

  The tests are written as *isolation* tests — for each level, a goal that the level
  below cannot answer and this one can, so each mechanism is pinned to the level that
  introduces it.  The last group checks the laziness contract: taking one result must
  cost strictly less than taking all of them."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the table ----------------------------------------------------------

(deftest level-table-is-a-contiguous-ladder
  (let [table (v/levels)]
    (testing "eight levels, numbered 0-7, each naming the one below it"
      (is (= 8 (count table)))
      (is (= (range 8) (map :level table)))
      (is (= [:raw :extent :local :visible :typed :closed :solved :proved]
             (map :name table)))
      (is (= (cons nil (map :name (butlast table))) (map :below table))))
    (testing "every level says what it adds"
      (is (every? (comp seq :adds) table)))))

(tu/deftest-kb lookup-rejects-a-level-off-the-ladder
  (is (thrown? clojure.lang.ExceptionInfo (v/lookup kb 8 '(dog Muffet) 'UniverseContext)))
  (is (thrown? clojure.lang.ExceptionInfo (v/lookup kb -1 '(dog Muffet) 'UniverseContext))))

;; ---- level 0: raw handles at an index location --------------------------

(tu/deftest-kb level-0-returns-raw-handles
  (tu/with-terms [dog Muffet StoryContext]
    (let [h (v/assert kb (list dog Muffet) StoryContext)]
      (testing "a sentence goal is turned into an index path"
        (is (= #{h} (set (map :handle (v/lookup kb 0 (list dog Muffet) StoryContext))))))
      (testing "a vector goal *is* the path, addressing the index directly"
        (is (= #{h} (set (map :handle (v/lookup kb 0 [dog Muffet StoryContext] nil))))))
      (testing "nothing is interpreted — no sentence, context or bindings"
        (let [r (first (v/lookup kb 0 (list dog Muffet) StoryContext))]
          (is (= 0 (:level r)))
          (is (every? nil? ((juxt :sentence :context :bindings) r))))))))

;; ---- level 1: one literal context, no unification -----------------------

(tu/deftest-kb level-1-is-context-plus-functor-retrieval
  (tu/with-terms [parentOf Tom Bob Ann Rex StoryContext OtherContext]
    (v/assert kb (list parentOf Tom Bob) StoryContext)
    (v/assert kb (list parentOf Ann Rex) StoryContext)
    (v/assert kb (list parentOf Tom Bob) OtherContext)
    (testing "arguments are not matched — this is candidate retrieval, not a match"
      (let [rs (v/lookup kb 1 (list parentOf Tom Bob) StoryContext)]
        (is (= 2 (count rs)))                        ; (Ann Rex) comes back too
        (is (= #{StoryContext} (set (map :context rs))))))
    (testing "the other context's copy is excluded — no inheritance at level 1"
      (is (= 1 (count (v/lookup kb 1 (list parentOf Tom Bob) OtherContext)))))
    (testing "results carry a handle and the stored sentence, but no bindings"
      (let [r (first (v/lookup kb 1 (list parentOf Tom Bob) StoryContext))]
        (is (integer? (:handle r)))
        (is (seq (:sentence r)))
        (is (nil? (:bindings r)))))))

;; ---- level 2: exact match in one literal context ------------------------

(tu/deftest-kb level-2-unifies-within-one-context
  (tu/with-terms [parentOf Tom Bob Ann Rex StoryContext]
    (v/assert kb (list parentOf Tom Bob) StoryContext)
    (v/assert kb (list parentOf Ann Rex) StoryContext)
    (testing "unification narrows what level 1 merely retrieved"
      (let [rs (v/lookup kb 2 (list parentOf Tom '?who) StoryContext)]
        (is (= 1 (count rs)))
        (is (= Bob (get (:bindings (first rs)) '?who)))))
    (testing "a non-matching goal in the right context yields nothing"
      (is (empty? (v/lookup kb 2 (list parentOf Tom Rex) StoryContext))))))

(tu/deftest-kb level-2-probes-the-symmetric-mirror
  (tu/with-terms [siblingOf Ann Carol StoryContext]
    (v/assert kb (list 'symmetric siblingOf) StoryContext)
    (v/assert kb (list siblingOf Ann Carol) StoryContext)
    (testing "either argument order finds the one stored sentex"
      (is (= 1 (count (v/lookup kb 2 (list siblingOf '?x Carol) StoryContext))))
      (is (= 1 (count (v/lookup kb 2 (list siblingOf Carol '?x) StoryContext)))))))

;; ---- query is the level-2 matcher ---------------------------------------
;; `core/sentexes-matching` *is* level 2 (`res/raw-match`): one literal context, unification,
;; the symmetric mirror, belief-filtered — so it shares `match-one`'s argument-root
;; divert (a goal pinning an argument after a variable is answered from the arg root,
;; not a leading-variable fan-out).  It adds exactly two things level 2 does not do:
;; the `except` visibility filter, the retired-spelling filter, and the equality
;; goal-rewrite.  These pin that identity so `query` and the stack cannot drift apart.

(tu/deftest-kb query-core-is-exactly-level-2
  (tu/with-terms [parentOf siblingOf flies Tom Bob Ann Carol Opus StoryContext]
    (v/assert kb (list 'symmetric siblingOf) StoryContext)
    (v/assert kb (list parentOf Tom Bob)   StoryContext {:strength :monotonic})
    (v/assert kb (list parentOf Tom Ann)   StoryContext {:strength :monotonic})
    (v/assert kb (list parentOf Carol Ann) StoryContext {:strength :monotonic})
    (v/assert kb (list siblingOf Ann Carol) StoryContext {:strength :monotonic})
    (v/assert kb (list 'not (list flies Opus)) StoryContext {:strength :monotonic})
    (letfn [(l2 [goal] (set (map :sentence (v/lookup kb 2 goal StoryContext))))
            (qq [goal] (set (map :sentence (v/sentexes-matching kb goal StoryContext))))]
      (doseq [goal [(list parentOf Tom '?y)        ; leading value, trailing variable
                    (list parentOf '?x Ann)         ; after-a-variable: the arg-root divert
                    (list parentOf Tom Bob)         ; fully ground
                    (list siblingOf '?x Carol)      ; symmetric — the mirror is probed
                    (list siblingOf Carol '?x)
                    (list 'not (list flies Opus))    ; a negation
                    (list flies Opus)                ; positive goal — the negation must not leak
                    (list parentOf '?x '?y)]]        ; fully open
        (is (= (l2 goal) (qq goal))
            (str "query diverged from level 2 on " (pr-str goal)
                 "\n  level2: " (pr-str (l2 goal)) "\n  query:  " (pr-str (qq goal))))))))

(tu/deftest-kb query-adds-the-except-visibility-filter
  ;; the first thing query adds over level 2, and the one place a result climbing the
  ;; stack *disappears* rather than losing its handle: the filter lives in
  ;; `res/matches-visible`, so it enters at level 4 — see
  ;; `an-excepted-fact-is-the-one-answer-that-falls-out-of-the-stack` below.
  ;; A believed `except` hides its target
  (tu/with-terms [likes Bob Ann StoryContext]
    (let [h (v/assert kb (list likes Bob Ann) StoryContext {:strength :monotonic})]
      (testing "with no except, query and level 2 both see the fact"
        (is (= 1 (count (v/sentexes-matching kb (list likes Bob Ann) StoryContext))))
        (is (= 1 (count (v/lookup kb 2 (list likes Bob Ann) StoryContext)))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle h)) StoryContext {:strength :monotonic})]
        (testing "query drops the excepted fact; level 2 (no except filter) keeps it"
          (is (empty? (v/sentexes-matching kb (list likes Bob Ann) StoryContext)))
          (is (= 1 (count (v/lookup kb 2 (list likes Bob Ann) StoryContext)))))
        (testing "retracting the except restores it to query — belief-following"
          (v/retract! kb eh)
          (is (= 1 (count (v/sentexes-matching kb (list likes Bob Ann) StoryContext)))))))))

(tu/deftest-kb query-rewrites-a-retired-spelling-that-level-2-does-not
  ;; the second thing query adds over level 2: a goal naming an equality-retired term
  ;; is rewritten to the class representative, so the old spelling stays a usable
  ;; *question* even though it is no longer a usable *answer* (docs/equality.md)
  (tu/with-terms [likes Bob Ann Annie StoryContext]
    (v/assert kb (list likes Bob Annie) StoryContext {:strength :monotonic})
    (v/assert kb (list 'rewriteOf Ann Annie) StoryContext {:strength :monotonic}) ; Annie deprecated -> Ann
    (testing "the fact migrated to the representative spelling, which query finds"
      (is (= 1 (count (v/sentexes-matching kb (list likes Bob Ann) StoryContext)))))
    (testing "query rewrites the retired spelling in the goal and still finds it"
      (is (= 1 (count (v/sentexes-matching kb (list likes Bob Annie) StoryContext)))))
    (testing "level 2 does not rewrite — the retired spelling is superseded, so it finds nothing"
      (is (empty? (v/lookup kb 2 (list likes Bob Annie) StoryContext))))))

;; ---- level 3: context inheritance via genlContext -----------------------

(tu/deftest-kb level-3-adds-genlContext-inheritance
  (tu/with-terms [parentOf Tom Bob SubContext SuperContext]
    (v/assert kb (list 'genlContext SubContext SuperContext) 'UniverseContext)
    (v/assert kb (list parentOf Tom Bob) SuperContext)
    (testing "level 2 sees only the literal context and misses the inherited fact"
      (is (empty? (v/lookup kb 2 (list parentOf Tom '?y) SubContext))))
    (testing "level 3 sees it through the up-closure, and reports where it is stored"
      (let [rs (v/lookup kb 3 (list parentOf Tom '?y) SubContext)]
        (is (= 1 (count rs)))
        (is (= Bob (get (:bindings (first rs)) '?y)))
        (is (= SuperContext (:context (first rs))))))))

;; ---- level 4: predicate inheritance via the genl spec walk --------------

(tu/deftest-kb level-4-adds-the-genl-spec-walk
  (tu/with-terms [dog animal Muffet StoryContext]
    (v/assert kb (list 'genl dog animal) StoryContext)
    (v/assert kb (list dog Muffet) StoryContext)
    (testing "level 3 matches the type predicate literally and finds nothing"
      (is (empty? (v/lookup kb 3 (list animal '?x) StoryContext))))
    (testing "level 4 fans out over the subtype closure and finds the dog"
      (let [rs (v/lookup kb 4 (list animal '?x) StoryContext)]
        (is (= 1 (count rs)))
        (is (= Muffet (get (:bindings (first rs)) '?x)))
        (is (integer? (:handle (first rs))))))         ; still a stored answer
    (testing "no supertype fact was materialized to make that work"
      (is (empty? (v/lookup kb 2 (list animal Muffet) StoryContext))))))

;; ---- level 5: transitive closure ----------------------------------------

(tu/deftest-kb level-5-adds-transitive-closure
  (tu/with-terms [ancestorOf Ann Bob Carol StoryContext]
    (v/assert kb (list 'transitive ancestorOf) StoryContext)
    (v/assert kb (list ancestorOf Ann Bob) StoryContext)
    (v/assert kb (list ancestorOf Bob Carol) StoryContext)
    (testing "level 4 sees only the stored edge"
      (is (= #{Bob} (set (map #(get (:bindings %) '?x)
                              (v/lookup kb 4 (list ancestorOf Ann '?x) StoryContext))))))
    (testing "level 5 closes the chain to Carol"
      (is (= #{Bob Carol} (set (map #(get (:bindings %) '?x)
                                    (v/lookup kb 5 (list ancestorOf Ann '?x) StoryContext))))))
    (testing "the stored edge keeps its handle; the derived link has none"
      (let [by-x (into {} (map (juxt #(get (:bindings %) '?x) :handle))
                       (v/lookup kb 5 (list ancestorOf Ann '?x) StoryContext))]
        (is (integer? (get by-x Bob)))
        (is (nil? (get by-x Carol)))))))

;; ---- levels 6 and 7: the prover stack, without and with backchaining ----

(tu/deftest-kb level-7-adds-backchaining
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann StoryContext]
    ;; a *backward* rule, so forward chaining never materializes the consequent —
    ;; the only way to reach it is by chaining backwards at level 7
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) StoryContext {:direction :backward})
    (v/assert kb (list parentOf Tom Bob) StoryContext)
    (v/assert kb (list parentOf Bob Ann) StoryContext)
    (testing "no level below 7 derives through the rule"
      (doseq [n (range 0 7)]
        (is (empty? (v/lookup kb n (list grandparentOf Tom '?who) StoryContext))
            (str "level " n " should not backchain"))))
    (testing "level 7 does"
      (let [rs (v/lookup kb 7 (list grandparentOf Tom '?who) StoryContext)]
        (is (= #{Ann} (set (map #(get (:bindings %) '?who) rs))))
        (is (= 7 (:level (first rs))))))))

(tu/deftest-kb level-6-still-answers-from-stored-facts
  (tu/with-terms [parentOf Tom Bob StoryContext]
    (v/assert kb (list parentOf Tom Bob) StoryContext)
    (testing "the fact prover is in the level-6 stack"
      (is (= #{Bob} (set (map #(get (:bindings %) '?y)
                              (v/lookup kb 6 (list parentOf Tom '?y) StoryContext))))))
    (testing "level 7 agrees — backchaining only ever adds"
      (is (= (map :bindings (v/lookup kb 6 (list parentOf Tom '?y) StoryContext))
             (map :bindings (v/lookup kb 7 (list parentOf Tom '?y) StoryContext)))))))

;; ---- the uniform result shape -------------------------------------------

(tu/deftest-kb every-level-returns-the-same-map-shape
  (tu/with-terms [dog animal Muffet StoryContext]
    (v/assert kb (list 'genl dog animal) StoryContext)
    (v/assert kb (list dog Muffet) StoryContext)
    (doseq [n (range 8)]
      (doseq [r (v/lookup kb n (list dog Muffet) StoryContext)]
        (is (= #{:level :handle :sentence :context :bindings} (set (keys r)))
            (str "level " n " result shape"))
        (is (= n (:level r)))))))

;; ---- escalate -----------------------------------------------------------

(tu/deftest-kb escalate-stops-at-the-cheapest-level-that-answers
  (tu/with-terms [dog animal Muffet StoryContext]
    (v/assert kb (list 'genl dog animal) StoryContext)
    (v/assert kb (list dog Muffet) StoryContext)
    (testing "a goal needing the spec walk escalates to level 4 and stops"
      (let [r (v/escalate kb (list animal '?x) StoryContext)]
        (is (= 4 (:level r)))
        (is (= :typed (:name r)))
        (is (= [2 3 4] (:tried r)))                  ; from the default query floor
        (is (= Muffet (get (:bindings (first (:results r))) '?x)))))
    (testing "a goal a plain match answers stops at level 2"
      (is (= 2 (:level (v/escalate kb (list dog Muffet) StoryContext)))))
    (testing "an explicit floor of 0 admits the retrieval levels"
      (is (= 0 (:level (v/escalate kb (list dog Muffet) StoryContext 0)))))
    (testing "an unanswerable goal reports no level, having tried them all"
      (tu/with-terms [cat]
        (let [r (v/escalate kb (list cat '?x) StoryContext)]
          (is (nil? (:level r)))
          (is (= (range 2 8) (:tried r)))
          (is (empty? (:results r))))))))

(tu/deftest-kb escalate-skips-the-retrieval-levels-by-default
  ;; level 1 ignores the goal's arguments, so it answers *any* goal whose functor has
  ;; a fact in the context — including one that is only true transitively.  Escalating
  ;; from 0 would name level 1 as the mechanism, which is wrong; the default floor is
  ;; what keeps escalate honest.
  (tu/with-terms [ancestorOf Ann Bob Carol StoryContext]
    (v/assert kb (list 'transitive ancestorOf) StoryContext)
    (v/assert kb (list ancestorOf Ann Bob) StoryContext)
    (v/assert kb (list ancestorOf Bob Carol) StoryContext)
    (testing "the transitive goal is genuinely answered by the closure, at level 5"
      (is (= 5 (:level (v/escalate kb (list ancestorOf Ann Carol) StoryContext)))))
    (testing "from floor 0, level 1 claims it — on the strength of a different fact"
      (is (= 1 (:level (v/escalate kb (list ancestorOf Ann Carol) StoryContext 0)))))))

;; ---- explain-levels ------------------------------------------------------------

(tu/deftest-kb explain-levels-shows-where-the-answer-appears
  (tu/with-terms [dog animal Muffet StoryContext]
    (v/assert kb (list 'genl dog animal) StoryContext)
    (v/assert kb (list dog Muffet) StoryContext)
    (let [rows (v/explain-levels kb (list animal '?x) StoryContext)
          by-n (into {} (map (juxt :level :count)) rows)]
      (testing "one row per level, named"
        (is (= 8 (count rows)))
        (is (= (range 8) (map :level rows))))
      (testing "the count jumps at level 4 — the spec walk is what answers this goal"
        (is (zero? (by-n 3)))
        (is (pos? (by-n 4))))
      (testing "and every level above still answers it"
        (is (every? pos? (map by-n (range 4 8))))))))

;; ---- monotonicity: what survives the climb, and what does not -----------
;;
;; The stack's whole claim is that a result appearing at level n and not at n-1 is
;; attributable to that level's one mechanism.  That only means something if climbing
;; never *loses* an answer — otherwise a level's contribution is a net of two effects
;; and reads as neither.  These pin the property where it holds, and pin the two
;; joints where it does not so that neither is a surprise.

(tu/deftest-kb the-answer-count-never-falls-as-the-stack-is-climbed
  ;; a KB exercising every mechanism the ladder names — an inherited context, a genl
  ;; hierarchy, a symmetric predicate, a transitive one, a forward rule — swept over
  ;; goal shapes that land on different rungs.  From the query floor up, no level may
  ;; answer less than the level below it.
  (tu/with-terms [dog animal siblingOf ancestorOf barks Muffet Ann Bob Carol
                  StoryContext SubContext]
    (v/assert kb (list 'genlContext SubContext StoryContext) StoryContext)
    (v/assert kb (list 'genl dog animal) StoryContext)
    (v/assert kb (list dog Muffet) StoryContext)
    (v/assert kb (list 'symmetric siblingOf) StoryContext)
    (v/assert kb (list siblingOf Ann Bob) StoryContext)
    (v/assert kb (list 'transitive ancestorOf) StoryContext)
    (v/assert kb (list ancestorOf Ann Bob) StoryContext)
    (v/assert kb (list ancestorOf Bob Carol) StoryContext)
    (v/assert-rule kb [(list dog '?x)] (list barks '?x) StoryContext)
    (doseq [ctx  [StoryContext SubContext]
            goal [(list dog Muffet)          (list dog '?x)
                  (list animal '?x)        (list animal Muffet)
                  (list siblingOf Bob '?w) (list siblingOf '?w Ann)
                  (list ancestorOf Ann '?x) (list ancestorOf Ann Carol)
                  (list barks Muffet)        (list barks '?x)
                  (list 'genl dog '?y)]]
      (let [counts (mapv #(count (v/lookup kb % goal ctx)) (range 2 8))]
        (is (apply <= counts)
            (str "levels 2-7 for " (pr-str goal) " in " ctx " counted " counts))))))

(tu/deftest-kb an-excepted-fact-is-the-one-answer-that-falls-out-of-the-stack
  ;; The `except` visibility filter lives in `res/matches-visible`, which is level 4,
  ;; and `res/raw-match` — levels 2 and 3 — does not read it.  So a sentex a believed
  ;; `except` hides is matched below the filter and gone above it.  Level 4 is right
  ;; and `ask` agrees; what it costs is `escalate`, which names level 2 as the
  ;; machinery sufficient for a goal the engine refuses.  No floor rules that out —
  ;; whether a level over-reports is a property of the KB — so it is pinned instead.
  (tu/with-terms [likes Bob Ann StoryContext]
    (let [h (v/assert kb (list likes Bob Ann) StoryContext {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle h)) StoryContext {:strength :monotonic})
      (let [goal (list likes Bob Ann)]
        (testing "levels 2 and 3 match it; level 4 and everything above drop it"
          (is (= 1 (count (v/lookup kb 2 goal StoryContext))))
          (is (= 1 (count (v/lookup kb 3 goal StoryContext))))
          (is (every? #(empty? (v/lookup kb % goal StoryContext)) (range 4 8))))
        (testing "the engine's own answer is the one level 4 gives"
          (is (empty? (v/ask kb goal StoryContext))))
        (testing "so escalate stops at 2 for a goal nothing above it answers"
          (is (= 2 (:level (v/escalate kb goal StoryContext)))))))))

(tu/deftest-kb level-3-reports-one-fact-once-however-many-names-it-has
  ;; Reading up the cone is what *creates* a retired spelling.  A fact stated above an
  ;; equality merge is believed where it lives — its own context was told nothing —
  ;; while a context below the merge sees both it and the twin migration placed there.
  ;; So the fan-out this level introduces is also what would hand one fact back twice,
  ;; under two names the reader knows denote one thing, and the reader-scoped filter
  ;; belongs to it rather than to the level above (docs/equality.md).
  (tu/with-terms [dog Muffet Rex StoryContext SubContext]
    (v/assert kb (list 'genlContext SubContext StoryContext) StoryContext)
    (v/assert kb (list dog Rex) StoryContext {:strength :monotonic})
    (v/assert kb (list 'sameAs Muffet Rex) SubContext {:strength :monotonic})
    (let [goal (list dog '?x)
          rep  (v/representative kb Rex SubContext)]
      (testing "the merge really did place a twin below, so there are two to confuse"
        (is (= 2 (count (v/sentexes-matching kb goal '?ctx)))))
      (testing "level 3 reports the fact once, under the spelling this reader elected"
        (let [rs (v/lookup kb 3 goal SubContext)]
          (is (= 1 (count rs)))
          (is (= rep (get (:bindings (first rs)) '?x)))))
      (testing "which is what level 4 counts too"
        (is (= 1 (count (v/lookup kb 4 goal SubContext))))))))

(tu/deftest-kb level-5-folds-a-derived-answer-into-the-stored-one-it-repeats
  ;; A closure is built from the very edges level 4 reads, so it re-derives most of
  ;; what it read.  The stored match carries the context it was stored **in** and the
  ;; derived one the context it was **asked** in, so for any fact inherited from a
  ;; general context — which is every taxonomy fact a story context reads — the two
  ;; agree on no field a dedup could naively key on, and one answer comes back twice.
  (tu/with-terms [ancestorOf Ann Bob Carol StoryContext SubContext]
    (v/assert kb (list 'genlContext SubContext StoryContext) StoryContext)
    (v/assert kb (list 'transitive ancestorOf) StoryContext)
    (v/assert kb (list ancestorOf Ann Bob) StoryContext)
    (v/assert kb (list ancestorOf Bob Carol) StoryContext)
    (testing "the ground goal the store already answers is one result, not two"
      (let [rs (v/lookup kb 5 (list ancestorOf Ann Bob) SubContext)]
        (is (= 1 (count rs)))
        (testing "and the survivor is the stored one — the fold keeps the provenance"
          (is (integer? (:handle (first rs)))))))
    (testing "the open goal answers once per answer, the closure link included"
      (let [rs (v/lookup kb 5 (list ancestorOf Ann '?x) SubContext)]
        (is (= #{Bob Carol} (set (map #(get (:bindings %) '?x) rs))))
        (is (= 2 (count rs)))
        (testing "which is what level 6 counts too"
          (is (= (count (v/lookup kb 6 (list ancestorOf Ann '?x) SubContext))
                 (count rs))))))))

(tu/deftest-kb level-5-never-drops-a-stored-match-to-a-derived-one
  ;; The fold is one-way.  Two stored matches carrying one answer are two *facts* —
  ;; the same sentence asserted in two contexts — and level 5 is level 4 plus a
  ;; mechanism, never level 4 minus a duplicate.
  (tu/with-terms [ancestorOf Ann Bob StoryContext OtherContext]
    (v/assert kb (list 'transitive ancestorOf) StoryContext)
    (v/assert kb (list ancestorOf Ann Bob) StoryContext)
    (v/assert kb (list ancestorOf Ann Bob) OtherContext)
    (let [goal (list ancestorOf Ann '?x)]
      (is (= 2 (count (v/lookup kb 4 goal '?ctx))))
      (is (= 2 (count (v/lookup kb 5 goal '?ctx)))))))

(tu/deftest-kb levels-6-and-7-prepare-the-goal-the-way-ask-does
  ;; Level 6 *is* `ask`'s dispatch, and `ask` normalizes its goal before dispatching:
  ;; a term an equality merge retired is rewritten to the class representative, so the
  ;; old spelling stays a usable question.  A level that skipped that step would report
  ;; that *no* level answers a goal the engine answers at the first ask.
  (tu/with-terms [likes Bob Ann Annie StoryContext]
    (v/assert kb (list likes Bob Annie) StoryContext {:strength :monotonic})
    (v/assert kb (list 'rewriteOf Ann Annie) StoryContext {:strength :monotonic})
    (let [goal (list likes Bob Annie)]                    ; Annie is the retired spelling
      (testing "ask answers the retired spelling"
        (is (= 1 (count (v/ask kb goal StoryContext)))))
      (testing "the matching levels do not — they match the goal as written"
        (is (every? #(empty? (v/lookup kb % goal StoryContext)) (range 2 6))))
      (testing "levels 6 and 7 do, because they ask the question ask asks"
        (is (= 1 (count (v/lookup kb 6 goal StoryContext))))
        (is (= 1 (count (v/lookup kb 7 goal StoryContext)))))
      (testing "so escalate names a level instead of reporting that nothing answers"
        (is (= 6 (:level (v/escalate kb goal StoryContext))))))))

;; ---- laziness -----------------------------------------------------------

(defn- counting-store
  "Wrap a RecordStore, counting `get-sentex` calls in `n`.  Every other method
  delegates untouched."
  [inner n]
  (reify p/RecordStore
    (put-sentex        [_ s]   (p/put-sentex inner s))
    (get-sentex        [_ id]  (swap! n inc) (p/get-sentex inner id))
    (delete-sentex!    [_ id]  (p/delete-sentex! inner id))
    (put-justification     [_ d]   (p/put-justification inner d))
    (get-justification     [_ id]  (p/get-justification inner id))
    (delete-justification! [_ id]  (p/delete-justification! inner id))
    (put-provenance    [_ id prov] (p/put-provenance inner id prov))
    (get-provenance    [_ id]  (p/get-provenance inner id))
    (delete-provenance! [_ id] (p/delete-provenance! inner id))
    (next-id           [_]     (p/next-id inner))
    (sentex-ids        [_]     (p/sentex-ids inner))
    (justification-ids     [_]     (p/justification-ids inner))
    (mark-premise      [_ id s] (p/mark-premise inner id s))
    (unmark-premise!   [_ id]  (p/unmark-premise! inner id))
    (premise-ids       [_]     (p/premise-ids inner))
    (premise-strength  [_ id]  (p/premise-strength inner id))
    (clear-records!    [_]     (p/clear-records! inner))))

(tu/deftest-kb taking-one-result-costs-fewer-record-fetches-than-taking-all
  (tu/with-terms [parentOf Tom StoryContext]
    ;; enough facts to clear Clojure's 32-element chunking, so a genuinely lazy seq
    ;; and an eager one cannot be confused
    (let [kids (vec (repeatedly 80 tu/tmp-ind))]
      (doseq [k kids] (v/assert kb (list parentOf Tom k) StoryContext {:chain? false}))
      ;; the four retrieval levels, which are the ones that reach a record per result.
      ;; Levels 5-7 answer through the closures and the registry and fetch no record for
      ;; this goal at all, so their laziness is counted in leaf solves instead — see
      ;; `level-7-streams-its-search-rather-than-running-it-to-completion`.
      (doseq [level [1 2 3 4]]
        (let [n     (atom 0)
              probe (assoc kb :records (counting-store (:records kb) n))
              goal  (list parentOf Tom '?k)
              _     (first (v/lookup probe level goal StoryContext))
              one   @n
              _     (reset! n 0)
              _     (dorun (v/lookup probe level goal StoryContext))
              all   @n]
          (testing (str "level " level " streams record fetches")
            (is (pos? all))
            (is (< one all)
                (str "level " level ": one result fetched " one
                     " records, all results fetched " all))))))))

(tu/deftest-kb level-5-does-not-run-the-closure-for-a-result-the-store-answers
  ;; the closure has no partial answer — computing one link computes the fixpoint — so
  ;; the one thing level 5 can do about its cost is not pay it until the stored half
  ;; runs out.  The fold over the derived half must not force it either: the set of
  ;; answers already carried is built from a seq `lazy-cat` has by then already yielded,
  ;; so it costs nothing a consumer taking one result would not have paid anyway.
  (tu/with-terms [ancestorOf StoryContext SubContext]
    (v/assert kb (list 'genlContext SubContext StoryContext) StoryContext)
    (v/assert kb (list 'transitive ancestorOf) StoryContext)
    (let [n (fn [i] (symbol (str "TmpAnc" i)))]
      (doseq [i (range 20)]
        (v/assert kb (list ancestorOf (n i) (n (inc i))) StoryContext {:chain? false}))
      (let [calls (fn [f] (let [c (atom 0), orig provers/solve-goal-with]
                            (with-redefs [provers/solve-goal-with
                                          (fn [& args] (swap! c inc) (apply orig args))]
                              (f))
                            @c))
            goal  (list ancestorOf (n 0) '?x)]
        (testing "one result comes from the store, and never reaches a prover"
          (is (some? (first (v/lookup kb 5 goal SubContext))))
          (is (zero? (calls #(first (v/lookup kb 5 goal SubContext))))))
        (testing "the whole answer set does run the closure"
          (is (pos? (calls #(dorun (v/lookup kb 5 goal SubContext))))))))))

(tu/deftest-kb level-7-streams-its-search-rather-than-running-it-to-completion
  ;; Level 7 is the one level whose machinery is a whole backward search, and an
  ;; unbounded one — it terminates on the data rather than on a depth.  Unbounded must
  ;; not mean eager: `escalate` climbs until something answers and reads *one* result to
  ;; decide, and the browser pages a level 25 rows at a time, so a level 7 that realized
  ;; its answer set before returning would make merely asking cost the whole search.
  ;;
  ;; Counted in leaf solves, which is the chainer's unit of work — one per goal it hands
  ;; to the registry.
  (tu/with-terms [parentOf anc StoryContext]
    (let [n (fn [i] (symbol (str "TmpLzChain" i)))]
      (doseq [i (range 30)]
        (v/assert kb (list parentOf (n i) (n (inc i))) StoryContext {:chain? false}))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) StoryContext
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     StoryContext {:direction :backward})
      (let [goal  (list anc (n 0) '?z)
            calls (fn [f] (let [c (atom 0), orig provers/solve-goal]
                            (with-redefs [provers/solve-goal
                                          (fn [& args] (swap! c inc) (apply orig args))]
                              (f))
                            @c))
            cost  (fn [k] (calls #(dorun (take k (v/lookup kb 7 goal StoryContext)))))
            all   (calls #(dorun (v/lookup kb 7 goal StoryContext)))]
        (testing "the search really does have a tail to avoid paying for"
          (is (= 30 (count (v/lookup kb 7 goal StoryContext)))
              "every node down the chain is an ancestor of the first")
          (is (pos? (cost 1))))
        (testing "each further answer costs more work than the one before it"
          ;; the discriminating claim, and the one that does not depend on where in the
          ;; space the first answer happens to sit: an eager level reads the *same* count
          ;; for every k, because by the time it returns the search is over
          (let [costs (mapv cost [1 5 10 20])]
            (is (apply < costs)
                (str "leaf solves for taking 1/5/10/20 answers: " costs))
            (is (< (peek costs) all)
                (str "taking 20 of 30 cost " (peek costs) ", all 30 cost " all))))))))

(tu/deftest-kb an-expensive-prover-is-never-invoked-when-a-cheap-one-answers
  (tu/with-terms [parentOf Tom Bob StoryContext]
    (v/assert kb (list parentOf Tom Bob) StoryContext)
    (let [invoked (atom false)
          costly  (reify provers/Prover
                    (applicable?  [_ _ _ _] true)
                    (est-bindings [_ _ _ _] 1)
                    (cost         [_ _ _ _] :search)   ; last (most expensive) tier
                    (completeness [_ _ _ _] 50)
                    (solve        [_ _ _ _] (reset! invoked true) []))]
      (v/add-prover kb costly)
      ;; level 6, because that is the level the registry's own laziness lives at, with no
      ;; chainer between the union and the caller.  Level 7 is lazy too, but its unit is a
      ;; leaf solve rather than a prover's `solve`, so it is the wrong instrument for
      ;; this claim — see `level-7-streams-its-search-rather-than-running-it-to-completion`.
      (testing "taking one answer never reaches the expensive prover's solve"
        (is (some? (first (v/lookup kb 6 (list parentOf Tom '?y) StoryContext))))
        (is (false? @invoked)))
      (testing "taking every answer does"
        (dorun (v/lookup kb 6 (list parentOf Tom '?y) StoryContext))
        (is (true? @invoked))))))

(tu/deftest-kb an-out-of-range-floor-is-refused-not-answered-empty
  ;; `lookup` refuses a level outside 0-7; `escalate` gave a floor above the top an
  ;; empty `tried` and answered {:level nil} — "nothing answered", the plausible
  ;; reading of what is an off-by-one in the caller's arithmetic.
  (tu/with-terms [pp Aa LvContext]
    (v/assert kb (list pp Aa) LvContext)
    (doseq [floor [8 99 -1 :two]]
      (let [e (try (v/escalate kb (list pp Aa) LvContext floor) nil
                   (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= :bad-level (:type e)) (pr-str floor))))))
