;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.equality-test
  "Equality: `rewriteOf`, `sameAs` and `equals` merging into one belief-following
  partition, and the `different` prover that reads it.  See docs/equality.md."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private merge-cost-ctx
  "The context section 10's cost tests work in.  Literal rather than gensym'd, because
  those tests build their own KB on the isolated pair and wipe it, which is what
  `tu/with-cleared-kb` is for."
  'CxMergeCost)

;; ---- helpers -------------------------------------------------------------

(defn- believed?
  "Is `sentence` stored in `context` **and** currently believed?

  Deliberately not `query`: a merge **rewrites goals**, so `query` on the retired
  spelling answers with the representative's sentex.  That is the right behaviour and
  the wrong instrument for asking which spelling the KB actually believes, which is
  what most of these tests are about."
  [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (boolean (and h (v/in? kb h)))))

(defn- stored-not-believed?
  "The signature of a **blocked** spelling: the sentex is still there (handles callers
  hold stay valid) and `in?` reports it unbelieved."
  [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (and (some? h) (some? (v/sentex kb h)) (not (v/in? kb h)))))

(defn- why-sentences
  "Every sentence mentioned anywhere in a `why` graph — the nodes' sentences and the
  rules.  Flattened, because the doc requires that `why` *names* the functional
  declaration and both facts without saying which slot each lands in."
  [w]
  (concat (keep :sentence (vals (:nodes w)))
          (keep :rule (mapcat :support (vals (:nodes w))))))

;; ---- 1. the three relations and one closure ------------------------------

(tu/deftest-kb rewrite-of-deprecates-its-second-argument-whatever-the-spelling
  (tu/with-terms [bornIn Chicago CxName]
    (let [[lo hi] (sort [(tu/tmp-ind "Obama") (tu/tmp-ind "Obama")])]
      ;; the preferred term is `hi`, so lexicographic order cannot explain the outcome
      (v/assert kb (list bornIn lo Chicago) CxName)
      (v/assert kb (list 'rewriteOf hi lo) CxName)
      (testing "the fact is migrated to the preferred term"
        (is (believed? kb (list bornIn hi Chicago) CxName)))
      (testing "and the deprecated spelling is blocked, not deleted"
        (is (stored-not-believed? kb (list bornIn lo Chicago) CxName))))))

(tu/deftest-kb same-as-states-no-preference-so-the-smaller-symbol-represents
  (tu/with-terms [bornIn Chicago CxName]
    (let [[lo hi] (sort [(tu/tmp-ind "Obama") (tu/tmp-ind "Obama")])]
      (v/assert kb (list bornIn hi Chicago) CxName)
      ;; written larger-first, so an implementation that trusted argument order would
      ;; elect `hi` and this test would catch it
      (v/assert kb (list 'sameAs hi lo) CxName)
      (testing "the lexicographically smaller symbol represents the class"
        (is (believed? kb (list bornIn lo Chicago) CxName)))
      (testing "so the fact written under the larger one is the blocked spelling"
        (is (stored-not-believed? kb (list bornIn hi Chicago) CxName))))))

(tu/deftest-kb all-three-relations-merge
  (doseq [rel ['rewriteOf 'sameAs 'equals]]
    (testing (str rel " merges its arguments")
      (tu/with-terms [bornIn Chicago CxName]
        (let [[lo hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])]
          ;; `lo` is both the preferred term of the rewrite and the lexicographic
          ;; winner, so all three relations must agree on it
          (v/assert kb (list bornIn hi Chicago) CxName)
          (v/assert kb (list rel lo hi) CxName)
          (is (believed? kb (list bornIn lo Chicago) CxName)
              (str rel " did not migrate the fact to the representative"))
          (is (stored-not-believed? kb (list bornIn hi Chicago) CxName)
              (str rel " did not block the non-representative spelling")))))))

;; The middle term represents the first edge read alone, so a one-hop election passes
;; the A/B half and fails here.

(tu/deftest-kb a-rewrite-chain-composes-into-one-class-with-one-representative
  (tu/with-terms [bornIn Chicago Berlin CxName]
    (tu/with-terms [A B C]
      (v/assert kb (list bornIn B Chicago) CxName)
      (v/assert kb (list bornIn C Berlin)  CxName)
      (v/assert kb (list 'rewriteOf A B) CxName)
      (v/assert kb (list 'rewriteOf B C) CxName)
      (testing "A represents all three, so both facts read under A"
        (is (believed? kb (list bornIn A Chicago) CxName))
        (is (believed? kb (list bornIn A Berlin)  CxName)))
      (testing "and neither of the two retired spellings is believed"
        (is (stored-not-believed? kb (list bornIn B Chicago) CxName))
        (is (stored-not-believed? kb (list bornIn C Berlin)  CxName)))
      (testing "B is deprecated too, so it does not represent C"
        (is (not (believed? kb (list bornIn B Berlin) CxName)))))))

;; The permutation harness is `order_independence_test`'s, on the isolated pair, so the
;; loop's clears do not empty this namespace's scratch space.

(deftest the-representative-does-not-depend-on-assertion-order
  (tu/with-terms [bornIn worksAt Chicago Acme CxName]
    (let [[lo hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])
          ops     [#(v/assert % (list 'sameAs hi lo) CxName)
                   #(v/assert % (list bornIn  hi Chicago) CxName)
                   #(v/assert % (list worksAt lo Acme) CxName)
                   #(v/assert % (list bornIn  lo Chicago) CxName)]
          observe (fn [kb]
                    ;; the *reading*, never a handle: handles are allocated in
                    ;; assertion order, so one in the map would make every ordering
                    ;; differ for a reason that is not about belief
                    {:born-under-lo  (believed? kb (list bornIn  lo Chicago) CxName)
                     :born-under-hi  (believed? kb (list bornIn  hi Chicago) CxName)
                     :works-under-lo (believed? kb (list worksAt lo Acme)    CxName)
                     :works-under-hi (believed? kb (list worksAt hi Acme)    CxName)
                     :different      (v/ask? kb (list 'different lo hi) CxName)})
          results (into #{} (map (fn [ordering]
                                   (let [k (tu/isolated-fresh)]
                                     (doseq [op ordering] (op k))
                                     (observe k))))
                        (tu/permutations ops))]
      (is (= 1 (count results))
          (str "the representative moved with assertion order — "
               (count results) " distinct outcomes across 24 orderings: "
               (pr-str results)))
      (testing "and the one outcome elects the lexicographically smaller symbol"
        (let [r (first results)]
          (is (true?  (:born-under-lo  r)))
          (is (false? (:born-under-hi  r)))
          (is (true?  (:works-under-lo r)))
          (is (false? (:works-under-hi r)))
          (is (false? (:different r)) "merged terms are not different")))
      (tu/clear-kb! (tu/isolated-test-kb)))))

;; ---- 2. migration --------------------------------------------------------

(tu/deftest-kb the-migrated-twin-is-derived-and-justified-by-the-fact-and-the-equality
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [Pref Dep]
      (let [fact (v/assert kb (list bornIn Dep Chicago) CxName)
            eq   (v/assert kb (list 'rewriteOf Pref Dep) CxName)
            twin (v/handle-of kb (list bornIn Pref Chicago) CxName)]
        (testing "the twin exists and is believed"
          (is (some? twin))
          (is (true? (v/in? kb twin))))
        (testing "it is derived, not asserted"
          (is (false? (v/premise? kb twin)))
          (is (seq (v/supporting-justifications kb twin))))
        (testing "and its justification names the original fact and the equality"
          (let [antes (set (mapcat :antecedents (v/supporting-justifications kb twin)))]
            (is (contains? antes fact) "the original sentex is not an antecedent")
            (is (contains? antes eq)   "the equality sentex is not an antecedent")))))))

;; Superseded, not swept: `exceptWhen` deletes an unsupported conclusion, and a
;; superseded spelling is still the caller's premise.

(tu/deftest-kb the-stale-spelling-is-blocked-and-its-handle-stays-valid
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [Pref Dep]
      (let [h (v/assert kb (list bornIn Dep Chicago) CxName)]
        (v/assert kb (list 'rewriteOf Pref Dep) CxName)
        (testing "the handle the caller holds still resolves to its sentex"
          (is (some? (v/sentex kb h)))
          (is (= (list bornIn Dep Chicago) (:sentence (v/sentex kb h))))
          (is (= h (v/handle-of kb (list bornIn Dep Chicago) CxName))))
        (testing "but it is not believed"
          (is (false? (v/in? kb h)))
          (is (false? (:believed? (v/why-not kb h)))))
        (testing "and it does not match — a raw level-2 lookup sees no believed hit"
          (is (empty? (v/lookup kb 2 (list bornIn Dep Chicago) CxName))))))))

;; The retired spelling stays a usable question though it is no longer an answer, so a
;; caller who has not heard about the merge reads through it.

(tu/deftest-kb a-goal-naming-the-deprecated-term-is-rewritten-and-still-answers
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [Pref Dep]
      (v/assert kb (list bornIn Dep Chicago) CxName)
      (v/assert kb (list 'rewriteOf Pref Dep) CxName)
      (testing "the closed goal answers under either spelling"
        (is (seq (v/sentexes-matching kb (list bornIn Pref Chicago) CxName)))
        (is (seq (v/sentexes-matching kb (list bornIn Dep  Chicago) CxName))
            "the goal was not rewritten to the representative before lookup")
        (is (true? (v/ask? kb (list bornIn Dep Chicago) CxName))))
      (testing "and an open goal binds to the representative, not the retired name"
        (is (= #{Pref} (set (map #(get % '?who)
                                 (v/ask kb (list bornIn '?who Chicago) CxName)))))))))

;; A merge retires a spelling for the contexts below it, and a rule naming that spelling
;; is restated there under the representative, as a fact naming it is.
(tu/deftest-kb a-rule-naming-a-retired-spelling-is-restated-below-the-merge
  (tu/with-terms [bornIn knows CxUpper CxLower]
    (tu/with-terms [Pref Dep]
      (v/assert kb (list 'genlCx CxLower CxUpper) 'CxUniverse)
      (let [rule (list 'implies (list bornIn '?x Dep) (list knows '?x Dep))]
        (v/assert kb rule CxUpper)
        (v/assert kb (list 'rewriteOf Pref Dep) CxLower)
        (testing "the context that states the rule, above the merge, reads it"
          (is (= [CxUpper] (map :context (v/sentexes-matching kb rule CxUpper)))))
        (testing "a context below the merge reads the twin naming Pref, stored there"
          (is (= [[CxLower (list knows '?var0 Pref)]]
                 (map (juxt :context :consequent) (v/sentexes-matching kb rule CxLower)))))))))

(defn- retired-spelling-rule-reading
  "The `knows` sentences CxName believes once `ops` run in order, with the terms read back
  as `Tom`, `Pref` and `Dep`: `:rule` the forward rule `(bornIn ?x Dep) => (knows ?x
  Dep)`, `:fact` `(bornIn Tom Dep)`, `:merge` `(rewriteOf Pref Dep)` at `:monotonic`,
  `:unmerge` its retraction."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bornIn knows CxName Tom Pref Dep]
      (let [eq (list 'rewriteOf Pref Dep)]
        (doseq [op ops]
          (case op
            :rule    (v/assert kb (list 'implies (list bornIn '?x Dep) (list knows '?x Dep)) CxName
                               {:direction :forward})
            :fact    (v/assert kb (list bornIn Tom Dep) CxName)
            :merge   (v/assert kb eq CxName {:strength :monotonic})
            :unmerge (v/retract! kb (v/handle-of kb eq CxName))))
        (into #{} (comp (filter #(believed? kb % CxName))
                        (map #(replace {Tom 'Tom Pref 'Pref Dep 'Dep knows 'knows} %)))
              (for [y [Pref Dep]] (list knows Tom y)))))))

(deftest a-rule-naming-a-retired-spelling-fires-under-the-representative-in-every-order
  (testing "the merge standing: the rule's twin fires on the fact's twin"
    (is (= #{#{'(knows Tom Pref)}}
           (into #{} (map retired-spelling-rule-reading) (tu/permutations [:rule :fact :merge])))))
  (testing "the merge retracted: the KB that never had it"
    (is (= #{#{'(knows Tom Dep)}}
           (into #{} (map #(retired-spelling-rule-reading (concat % [:unmerge])))
                 (tu/permutations [:rule :fact :merge]))
           #{(retired-spelling-rule-reading [:rule :fact])}))))

(tu/deftest-kb merging-two-spellings-of-one-fact-yields-one-handle-with-two-supports
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [Pref Dep]
      (let [pref-h (v/assert kb (list bornIn Pref Chicago) CxName)
            _      (v/assert kb (list bornIn Dep  Chicago) CxName)
            before (count (v/supporting-justifications kb pref-h))]
        (v/assert kb (list 'rewriteOf Pref Dep) CxName)
        (testing "the representative's handle is unchanged"
          (is (= pref-h (v/handle-of kb (list bornIn Pref Chicago) CxName))))
        (testing "it is still the premise the caller asserted"
          (is (true? (v/premise? kb pref-h)))
          (is (true? (v/in? kb pref-h))))
        (testing "and it gained a justification rather than spawning a second sentex"
          (is (> (count (v/supporting-justifications kb pref-h)) before)))
        (testing "exactly one believed sentex carries the predicate"
          (is (= 1 (count (v/sentexes-with-functor kb bornIn {:believed? true})))))))))

(defn- climbed-reading
  "Whether CxName believes `(alive Rex)` once `ops` run in order: `:ground` `(dog Rex)` and
  the forward rule `(animal ?x) => (alive ?x)`, `:e1` `(genl dog mammal)`, `:e2`
  `(genl <upper> animal)`, `:merge` `(rewriteOf mammalia mammal)`, and `:except` /
  `:unexcept` an `except` of the merge stored / retracted."
  [upper ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog mammal mammalia animal alive Rex CxName]
      (let [hs (volatile! {})]
        (doseq [op ops]
          (case op
            :ground   (do (v/assert kb (list dog Rex) CxName)
                          (v/assert kb (list 'implies (list animal '?x) (list alive '?x)) CxName
                                    {:direction :forward}))
            :e1       (v/assert kb (list 'genl dog mammal) CxName)
            :e2       (v/assert kb (list 'genl ({:mammal mammal :mammalia mammalia} upper) animal)
                                CxName)
            :merge    (vswap! hs assoc :merge (v/assert kb (list 'rewriteOf mammalia mammal) CxName
                                                        {:strength :monotonic}))
            :except   (v/assert kb (list 'except (list 'sentexHandle (:merge @hs))) CxName
                                {:strength :monotonic})
            :unexcept (v/retract! kb (v/handle-of kb (list 'except (list 'sentexHandle (:merge @hs)))
                                                  CxName))))
        (boolean (some->> (v/handle-of kb (list alive Rex) CxName) (#(v/believed? kb % CxName))))))))

;; A merge restates a `genl` edge as a twin, and a twin edge brings the facts under it to
;; the rules above it as an asserted edge does.  A firing that climbed the retired edge
;; is withdrawn at the merge and drawn again over the twin, so `(alive Rex)` is believed
;; in every order: the merge last, an edge after the merge, and the merge's twins made
;; when an `except` of it leaves.
(deftest a-firing-that-climbed-a-merged-type-s-edge-holds-in-every-arrival-order
  (doseq [upper [:mammal :mammalia]]
    (is (= #{true} (into #{} (map #(climbed-reading upper %))
                         (tu/permutations [:ground :e1 :e2 :merge])))
        (str upper)))
  (is (= #{true} (into #{} (map #(climbed-reading :mammalia (concat [:merge :except] % [:unexcept])))
                       (tu/permutations [:ground :e1 :e2])))
      "the except leaves"))

;; ---- 3. congruence -------------------------------------------------------
;; Every other test puts the merged term in top-level argument position, so this is the
;; one test of a nested occurrence (docs/equality.md, "Congruence comes free").

(tu/deftest-kb a-merged-term-nested-inside-a-compound-is-rewritten-too
  (tu/with-terms [reportedThat livesIn Ann Bob CxStory]
    (tu/with-terms [Pref Dep]
      ;; Dep occurs only at depth 2 — never as an argument of the stored literal
      (v/assert kb (list reportedThat Ann (list livesIn Bob Dep)) CxStory)
      (v/assert kb (list 'rewriteOf Pref Dep) CxStory)
      (testing "the nested occurrence is rewritten, so the congruent twin exists"
        (is (believed? kb (list reportedThat Ann (list livesIn Bob Pref)) CxStory)))
      (testing "and the nested stale spelling is blocked like a flat one"
        (is (stored-not-believed? kb (list reportedThat Ann (list livesIn Bob Dep))
                                  CxStory))))))

;; `handle-of` probes both argument orders of a symmetric literal, so it would hide a
;; textual substitution; the stored sentence is read directly.

(tu/deftest-kb migration-re-canonicalizes-a-symmetric-literal-rather-than-substituting
  (tu/with-terms [siblingOf CxKin]
    (let [[lo mid hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])]
      (v/assert kb (list 'symmetric siblingOf) CxKin)
      ;; stored canonically as (siblingOf lo mid)
      (v/assert kb (list siblingOf mid lo) CxKin)
      ;; retire `lo` in favour of `hi`, which sorts *after* mid
      (v/assert kb (list 'rewriteOf hi lo) CxKin)
      (let [twin (v/handle-of kb (list siblingOf mid hi) CxKin)]
        (testing "the twin exists"
          (is (some? twin)))
        (testing "and its stored sentence is re-canonicalized, not textually rewritten"
          (is (= (list siblingOf mid hi) (:sentence (v/sentex kb twin)))
              "the merge substituted textually and left (siblingOf hi mid) stored"))))))

;; ---- 4. retraction -------------------------------------------------------
;; Both halves: a twin left stored would make the term count wrong, and an original left
;; superseded would withhold the caller's premise.

(tu/deftest-kb retracting-the-equality-sweeps-the-twins-and-revives-the-originals
  (tu/with-terms [bornIn worksAt Chicago Acme CxName]
    (tu/with-terms [Pref Dep]
      (let [f1 (v/assert kb (list bornIn  Dep Chicago) CxName)
            f2 (v/assert kb (list worksAt Dep Acme)    CxName)
            eq (v/assert kb (list 'rewriteOf Pref Dep) CxName)]
        (testing "both twins exist while the equality holds"
          (is (believed? kb (list bornIn  Pref Chicago) CxName))
          (is (believed? kb (list worksAt Pref Acme)    CxName)))
        (v/retract! kb eq)
        (testing "the twins are swept — collected, not merely disbelieved"
          (is (nil? (v/handle-of kb (list bornIn  Pref Chicago) CxName)))
          (is (nil? (v/handle-of kb (list worksAt Pref Acme)    CxName))))
        (testing "and the originals are unblocked"
          (is (true? (v/in? kb f1)))
          (is (true? (v/in? kb f2)))
          (is (seq (v/sentexes-matching kb (list bornIn Dep Chicago) CxName))))
        (testing "so the two symbols are different again"
          (is (true? (v/ask? kb (list 'different Pref Dep) CxName))))))))

;; ---- 5. `different` ------------------------------------------------------
;; All three phases in one test, because the claim is the transition.

(tu/deftest-kb different-tracks-the-closure-in-both-directions
  (tu/with-terms [CxName]
    (tu/with-terms [Pref Dep]
      (testing "two unmerged symbols are different by the unique-name assumption"
        (is (true? (v/ask? kb (list 'different Pref Dep) CxName))))
      (let [eq (v/assert kb (list 'sameAs Pref Dep) CxName)]
        (testing "once merged they are not"
          (is (false? (v/ask? kb (list 'different Pref Dep) CxName))))
        (v/retract! kb eq)
        (testing "and retracting the merge restores the difference — the closure split"
          (is (true? (v/ask? kb (list 'different Pref Dep) CxName))))))))

(tu/deftest-kb different-is-variable-arity-and-pairwise
  (tu/with-terms [CxName]
    (tu/with-terms [A B C]
      (testing "three pairwise-distinct symbols"
        (is (true? (v/ask? kb (list 'different A B C) CxName))))
      ;; merge the pair that is *not* first, so a first-pair-only check is caught
      (v/assert kb (list 'sameAs B C) CxName)
      (testing "merging any one pair falsifies the whole literal"
        (is (false? (v/ask? kb (list 'different A B C) CxName))))
      (testing "while the untouched pair is still different"
        (is (true? (v/ask? kb (list 'different A B) CxName)))))))

(tu/deftest-kb different-is-not-assertible
  (tu/with-terms [CxName]
    (tu/with-terms [A B]
      (testing "asserting it is rejected"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'different A B) CxName))))
      (testing "and the refusal stores nothing"
        (is (nil? (v/handle-of kb (list 'different A B) CxName)))
        (is (zero? (v/count-with-functor kb 'different)))
        (is (empty? (v/find-sentexes kb 'different)))))))

;; An open goal makes the prover inapplicable, so `ask` yields nothing and the goal drops
;; out of `query-plan`, which lists applicable provers only.

(tu/deftest-kb an-open-different-is-refused-rather-than-enumerated
  (tu/with-terms [bornIn Chicago CxName]
    (tu/with-terms [A B C]
      (doseq [x [A B C]] (v/assert kb (list bornIn x Chicago) CxName))
      (testing "the ground goal is claimed by some prover — the control"
        (is (seq (v/query-plan kb (list 'different A B) CxName))))
      (testing "an unbound argument makes that prover inapplicable"
        ;; named by count rather than by class, since the doc names no prover
        (is (< (count (v/query-plan kb (list 'different '?x B) CxName))
               (count (v/query-plan kb (list 'different A   B) CxName)))
            "a prover claimed an open `different` goal"))
      (testing "and nothing enumerated the KB looking for non-B terms"
        (is (empty? (v/ask kb (list 'different '?x B)  CxName)))
        (is (empty? (v/ask kb (list 'different '?x '?y) CxName)))))))

;; `different` is never stored, so a rule antecedent is the one place a chain merge could
;; happen: two `different` literals sharing a variable stay two literals, where
;; `(lessThan ?a ?b)` and `(lessThan ?b ?c)` merge.

(tu/deftest-kb a-different-chain-in-a-rule-antecedent-is-not-merged
  (tu/with-terms [triple item CxStory]
    (let [rh (v/assert-rule kb [(list item '?a) (list item '?b) (list item '?c)
                                (list 'different '?a '?b)
                                (list 'different '?b '?c)]
                            (list triple '?a '?b '?c)
                            CxStory {:direction :forward})
          antes (:antecedent (v/sentex kb rh))
          diffs (filter #(= 'different (first %)) antes)]
      (testing "both literals survive — no chain merge"
        (is (= 2 (count diffs))
            (str "the two `different` literals were merged into "
                 (pr-str diffs) " — `different` is not transitive")))
      (testing "and neither grew an argument"
        (is (every? #(= 3 (count %)) diffs)))
      (testing "the rule fires for a binding the merged form would have rejected"
        ;; a=c is allowed: the rule constrains a≠b and b≠c and says nothing about a,c
        (tu/with-terms [X Y]
          (v/assert kb (list item X) CxStory)
          (v/assert kb (list item Y) CxStory)
          (is (seq (v/sentexes-matching kb (list triple X Y X) CxStory))
              "a merged (different ?a ?b ?c) would have blocked a = c")))
      (testing "and a rule assert does not store a `different` fact"
        (is (zero? (v/count-with-functor kb 'different)))))))

(tu/deftest-kb a-rule-concluding-an-equality-from-a-different-antecedent-is-rejected
  (tu/with-terms [candidate CxMerge]
    (tu/with-terms [Anchor]
      (testing "the one-rule cycle through negation is refused at assert time"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert-rule kb [(list candidate '?x)
                                        (list 'different '?x Anchor)]
                                    (list 'sameAs '?x Anchor)
                                    CxMerge {:direction :forward}))))
      (testing "and the refusal leaves no rule behind"
        (is (empty? (v/sentexes-in-context kb CxMerge)))))))

;; ---- 6. `functional` -----------------------------------------------------
;; Only the `handle-of` of the derived `equals` depends on which relation the merge
;; derives; the merging assertions hold for any of the three.

(tu/deftest-kb functional-derives-an-equality-instead-of-throwing
  (tu/with-terms [motherOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (testing "the second value does not throw"
        (is (some? (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic}))))
      (testing "the two values are merged, so they are no longer different"
        (is (false? (v/ask? kb (list 'different lo hi) CxFam))))
      (testing "and a fact about either reads under the representative"
        (v/assert kb (list caresFor hi Tom) CxFam)
        (is (believed? kb (list caresFor lo Tom) CxFam)))
      (testing "the derived equality is itself a sentex"
        (is (some? (v/handle-of kb (list 'equals lo hi) CxFam)))))))

(tu/deftest-kb a-merge-rests-on-every-functional-declaration-not-on-one-of-them
  ;; Retracts the first declaration of one predicate and the second of another, so no
  ;; single chosen handle passes both (docs/defenses.md, "A functional merge rests on
  ;; every declaration of the convicting mark").
  (tu/with-terms [Tom CxFam CxStory]
    (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxFam 'CxUniverse) 'CxUniverse)
    (doseq [retire [:first :second]]
      (let [motherOf (tu/fresh-term :predicate "motherOf")
            [lo hi]  (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
            h1       (v/assert kb (list 'functional motherOf) CxFam)
            h2       (v/assert kb (list 'functional motherOf) CxStory)]
        (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
        (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
        (is (v/same-class? kb lo hi)
            "the merge is derived while both declarations stand")
        (testing (str "retiring the " (name retire) " declaration leaves the merge")
          (v/retract! kb (if (= retire :first) h1 h2))
          (is (v/same-class? kb lo hi)
              (str "the surviving declaration licenses the same equality, so the merge "
                   "stands — it never rested on one arbitrary handle")))))))

;; The inspectable half; the reversible half is the next test.

(tu/deftest-kb why-on-a-functional-merge-names-the-declaration-and-both-facts
  (tu/with-terms [motherOf Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
      (let [eq (v/handle-of kb (list 'equals lo hi) CxFam)]
        (is (some? eq) "no derived equality to explain")
        (let [tree (tu/why-root kb eq)
              said (set (why-sentences (v/why kb eq)))]
          (testing "it is derived, not a premise"
            (is (true?  (:believed? tree)))
            (is (false? (:premise?  tree)))
            (is (seq (:support tree))))
          (testing "and the argument names the declaration and both facts"
            (is (contains? said (list 'functional motherOf))
                "why does not name the functional declaration that caused the merge")
            (is (contains? said (list motherOf Tom lo)))
            (is (contains? said (list motherOf Tom hi)))))))))

(tu/deftest-kb retracting-either-functional-fact-un-merges-the-values
  (tu/with-terms [motherOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (let [second-fact (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})]
        (v/assert kb (list caresFor hi Tom) CxFam)
        (testing "merged while both facts stand"
          (is (false? (v/ask? kb (list 'different lo hi) CxFam)))
          (is (believed? kb (list caresFor lo Tom) CxFam)))
        (v/retract! kb second-fact)
        (testing "retracting one of them un-merges"
          (is (true? (v/ask? kb (list 'different lo hi) CxFam)))
          (is (nil?  (v/handle-of kb (list 'equals lo hi) CxFam))))
        (testing "and the migrated twin is swept while the original revives"
          (is (nil? (v/handle-of kb (list caresFor lo Tom) CxFam)))
          (is (true? (believed? kb (list caresFor hi Tom) CxFam))))))))

(tu/deftest-kb a-fact-in-cxuniverse-merges-with-one-in-a-context-no-edge-names
  (doseq [mark '[functional anti_symmetric] flip? [false true]]
    (tu/with-terms [rel Kid Ann Bea CxFam]
      (let [[fa fb] (if (= 'functional mark)
                      [(list rel Kid Ann) (list rel Kid Bea)]
                      [(list rel Ann Bea) (list rel Bea Ann)])]
        (v/assert kb (list mark rel) CxFam)
        (doseq [[f c] (cond-> [[fa 'CxUniverse] [fb CxFam]] flip? reverse)]
          (v/assert kb f c {:strength :monotonic}))
        (testing (str mark (when flip? ", the CxUniverse fact last"))
          (is (some? (v/handle-of kb (list 'equals Ann Bea) CxFam))))))))

(tu/deftest-kb a-collision-merges-only-when-both-facts-are-monotonic
  ;; A merge rests on `:monotonic` evidence alone (docs/reference.md, decisions 6 and
  ;; 13): with a `:default` member the collision is a nogood, in either arrival order.
  (doseq [mark    ['functional 'anti_symmetric]
          [sa sb] [[:monotonic :default] [:monotonic :monotonic] [:default :default]]
          flip?   [false true]]
    (tu/with-terms [rel Kid Ann Bea CxFam]
      (let [[fa fb] (if (= 'functional mark)
                      [(list rel Kid Ann) (list rel Kid Bea)]
                      [(list rel Ann Bea) (list rel Bea Ann)])
            both?   (= :monotonic sa sb)
            ;; read at the context: an `anti_symmetric` loser is decided by its reader
            held?   #(boolean (v/believed? kb (v/handle-of kb % CxFam) CxFam))
            dilemma (fn [] (some #(= #{fa fb} (into #{} (map :sentence) (:sides %)))
                                 (v/contradictions kb)))]
        (v/assert kb (list mark rel) CxFam)
        (doseq [[f st] (cond-> [[fa sa] [fb sb]] flip? reverse)]
          (v/assert kb f CxFam {:strength st}))
        (testing (str mark " " sa " beside " sb (when flip? ", the second first"))
          (is (= both? (v/same-class? kb Ann Bea)))
          (is (= both? (some? (v/handle-of kb (list 'equals Ann Bea) CxFam))))
          (when-not both?
            (is (held? fa))
            (is (= (= :default sa) (held? fb)))
            (is (= (= :default sa) (boolean (dilemma))))))))))

;; A member's class also moves under an unchanged label, through a justification of it
;; arriving or leaving, and the merge follows the class as it follows a write.
(defn- collision-with-route
  "Write in a fresh context a `mark` over a fresh `rel`, a `:monotonic` forward rule
  `(route ?x ?y) => (rel ?x ?y)`, the `:monotonic` tuple `fa`, the `:default` tuple `fb`,
  and the `:monotonic` `route` twin of `fb`, which makes `fb` `:monotonic`: the route
  first when `route-first?`, else last."
  [kb mark route-first?]
  (tu/with-terms [rel route Kid Ann Bea CxFam]
    (let [[fa fb] (if (= 'functional mark)
                    [(list rel Kid Ann) (list rel Kid Bea)]
                    [(list rel Ann Bea) (list rel Bea Ann)])
          r       (cons route (rest fb))]
      (v/assert kb (list mark rel) CxFam)
      (v/assert kb (list 'set/forwardRule (list 'implies (list route '?x '?y) (list rel '?x '?y)))
                CxFam {:strength :monotonic})
      (when route-first? (v/assert kb r CxFam {:strength :monotonic}))
      (v/assert kb fa CxFam {:strength :monotonic})
      (v/assert kb fb CxFam {:strength :default})
      (when-not route-first? (v/assert kb r CxFam {:strength :monotonic}))
      {:fa fa :fb fb :route r :a Ann :b Bea :cx CxFam})))

(defn- held-at?
  "Is `s` stored at `cx` and believed there?  An `anti_symmetric` loser is decided by its
  reader."
  [kb s cx]
  (boolean (some->> (v/handle-of kb s cx) (#(v/believed? kb % cx)))))

(tu/deftest-kb a-merge-follows-its-members-classes-when-a-route-moves
  (doseq [mark '[functional anti_symmetric]]
    (testing (str mark ", the route retracted after the merge: fb is the unique :default member")
      (let [{:keys [fa fb route a b cx]} (collision-with-route kb mark true)]
        (is (true? (v/same-class? kb a b)))
        (v/retract! kb (v/handle-of kb route cx))
        (is (false? (v/same-class? kb a b)))
        (is (true? (held-at? kb fa cx)))
        (is (false? (held-at? kb fb cx)))))
    (testing (str mark ", the route arriving after fb merges as it does arriving first")
      (let [{:keys [a b]} (collision-with-route kb mark false)]
        (is (true? (v/same-class? kb a b)))))))

(tu/deftest-kb a-reader-re-decides-a-merging-converse-pair-when-a-member-s-class-drops
  ;; the reader decides the pair while it merges, so its answer watches both members;
  ;; the functional sequence first leaves the reader's answer cached before the drop
  (let [{f-route :route f-cx :cx} (collision-with-route kb 'functional false)]
    (v/retract! kb (v/handle-of kb f-route f-cx)))
  (let [{:keys [fa fb route cx]} (collision-with-route kb 'anti_symmetric false)]
    (v/retract! kb (v/handle-of kb route cx))
    (is (true? (held-at? kb fa cx)))
    (is (false? (held-at? kb fb cx)))))

;; The tests above write the declaration first; these write it after the facts
;; (`special/equate-existing`), and the KB merges the same values.

(tu/deftest-kb a-functional-declaration-arriving-after-the-facts-merges-them-too
  (tu/with-terms [motherOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
      (testing "before the declaration the two values are simply two values"
        (is (true? (v/ask? kb (list 'different lo hi) CxFam))))
      (v/assert kb (list 'functional motherOf) CxFam)
      (testing "the declaration merges what it now says was always one thing"
        (is (false? (v/ask? kb (list 'different lo hi) CxFam))))
      (testing "the derived equality is a sentex here too"
        (is (some? (v/handle-of kb (list 'equals lo hi) CxFam))))
      (testing "and a fact about either reads under the representative"
        (v/assert kb (list caresFor hi Tom) CxFam)
        (is (believed? kb (list caresFor lo Tom) CxFam))))))

(tu/deftest-kb the-functional-declaration-reaches-the-same-belief-from-either-end
  ;; the oracle for the test above: the same three sentences in the two orders that
  ;; matter, compared on what the KB *believes* rather than on what it stored
  (tu/with-terms [motherOf Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
          decl (list 'functional motherOf)
          f1   (list motherOf Tom lo)
          f2   (list motherOf Tom hi)
          reading (fn [] [(v/ask? kb (list 'different lo hi) CxFam)
                          (v/representative kb lo)
                          (v/representative kb hi)
                          (some? (v/handle-of kb (list 'equals lo hi) CxFam))])]
      (doseq [s [decl f1 f2]] (v/assert kb s CxFam))
      (let [declaration-first (reading)]
        (doseq [s [decl f1 f2]]
          (when-let [h (v/handle-of kb s CxFam)] (v/retract! kb h)))
        (doseq [s [f2 f1 decl]] (v/assert kb s CxFam))
        (is (= declaration-first (reading))
            "the same three sentences believe different things in the two orders")))))

(tu/deftest-kb a-retroactive-functional-merge-carries-the-same-argument
  ;; a retroactive merge names the same three sentexes a forward one does
  (tu/with-terms [motherOf Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
      (v/assert kb (list 'functional motherOf) CxFam)
      (let [eq (v/handle-of kb (list 'equals lo hi) CxFam)]
        (is (some? eq) "no derived equality to explain")
        (let [said (set (why-sentences (v/why kb eq)))]
          (is (contains? said (list 'functional motherOf)))
          (is (contains? said (list motherOf Tom lo)))
          (is (contains? said (list motherOf Tom hi))))))))

(tu/deftest-kb retracting-a-retroactive-functional-declaration-un-merges
  ;; the declaration is an antecedent whichever order it arrived in
  (tu/with-terms [motherOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list motherOf Tom hi) CxFam {:strength :monotonic})
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list caresFor hi Tom) CxFam)
      (testing "merged while the declaration stands"
        (is (false? (v/ask? kb (list 'different lo hi) CxFam)))
        (is (believed? kb (list caresFor lo Tom) CxFam)))
      (v/retract! kb (v/handle-of kb (list 'functional motherOf) CxFam))
      (testing "retracting the declaration un-merges the values it merged"
        (is (true? (v/ask? kb (list 'different lo hi) CxFam)))
        (is (nil?  (v/handle-of kb (list 'equals lo hi) CxFam))))
      (testing "and the migrated twin goes with it"
        (is (nil? (v/handle-of kb (list caresFor lo Tom) CxFam)))
        (is (true? (believed? kb (list caresFor hi Tom) CxFam)))))))

(tu/deftest-kb a-retroactive-declaration-collapses-a-whole-slot-not-one-pair
  ;; three spellings of one mother: the sweep is over the predicate's extent, so every
  ;; value in the slot lands in one class rather than the first pair it happens to meet
  (tu/with-terms [motherOf Tom CxFam]
    (let [[a b c] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (doseq [m [a b c]] (v/assert kb (list motherOf Tom m) CxFam {:strength :monotonic}))
      (v/assert kb (list 'functional motherOf) CxFam)
      (testing "all three collapse to one representative"
        (is (= 1 (count (distinct (map #(v/representative kb %) [a b c]))))
            (str "three values did not reach one class: "
                 (pr-str (mapv #(v/representative kb %) [a b c]))))))))

(tu/deftest-kb a-functional-merge-a-rule-triggered-displaces-the-spelling-too
  ;; The second value arrives as a rule's conclusion, so the merge happens inside the
  ;; chaining run.  The twin is stored and the restated spelling stops being believed
  ;; there, as `recover` would rebuild them.
  (tu/with-terms [motherOf parentOf caresFor Tom CxFam]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) CxFam)
      (v/assert kb (list motherOf Tom lo) CxFam {:strength :monotonic})
      (v/assert kb (list caresFor hi Tom) CxFam)
      (v/assert-rule kb [(list parentOf '?x '?y)] (list motherOf '?x '?y) CxFam {:direction :forward})
      (v/assert kb (list parentOf Tom hi) CxFam {:strength :monotonic})
      (testing "the derived second value merges"
        (is (v/same-class? kb lo hi)))
      (testing "and the fact under the retired spelling is restated, not doubled"
        (is (believed? kb (list caresFor lo Tom) CxFam))
        (is (stored-not-believed? kb (list caresFor hi Tom) CxFam))))))

;; ---- 7. an equality a rule concluded -------------------------------------
;; The live/rebuilt half is `recovery-test/recover-agrees-about-a-rule-concluded-equality`.
;; All three relations, because the derivation path dispatches on the functor: the two
;; symmetric ones elect the smaller spelling and `rewriteOf` elects its first argument,
;; so a fact written `(alias lo hi)` retires `hi` under every one of them.

(defn- rule-concluded-merge!
  "Assert a rule concluding `(rel ?x ?y)` from a fact of `aliasOf`, plus one fact naming
  the spelling the merge retires, and fire it.  `aliasOf` is declared on the
  forced-monotonic set where the rule is stated, since a firing concludes an equality
  only from forced-monotonic antecedents.  Returns `[lo hi]` — the elected representative and the retired
  spelling."
  [kb rel aliasOf caresFor Tom context]
  (let [[lo hi] (sort [(tu/tmp-ind "Ann") (tu/tmp-ind "Ann")])]
    (v/assert kb (list 'forced_monotonic_predicate aliasOf) context)
    (v/assert-rule kb [(list aliasOf '?x '?y)] (list rel '?x '?y) context {:direction :forward})
    (v/assert kb (list caresFor hi Tom) context)
    (v/assert kb (list aliasOf lo hi) context)
    [lo hi]))

(tu/deftest-kb a-rule-concluding-an-equality-merges-like-an-asserted-one
  (doseq [rel '[rewriteOf sameAs equals]]
    (testing (str "a rule concluding " rel)
      (tu/with-terms [aliasOf caresFor CxAlias]
        (tu/with-terms [Tom]
          (let [[lo hi] (rule-concluded-merge! kb rel aliasOf caresFor Tom CxAlias)]
            (testing "the conclusion is stored and believed"
              (is (believed? kb (list rel lo hi) CxAlias)))
            (testing "and the closure holds the edge it states"
              (is (v/same-class? kb lo hi)
                  (str "the equality closure never learned the rule's conclusion "
                       (pr-str (list rel lo hi))))
              (is (= lo (v/representative kb hi))))
            (testing "the retired spelling is blocked and its restatement believed"
              (is (stored-not-believed? kb (list caresFor hi Tom) CxAlias))
              (is (believed? kb (list caresFor lo Tom) CxAlias)))
            (testing "and the only violation is the one the merge itself creates"
              ;; `rewriteOf` files one, and it is the merge rather than the derivation
              ;; that files it: the antecedent fact names both terms, so migration
              ;; restates it as `(alias lo lo)`, the rule fires again on the
              ;; restatement, and a self-edge is what `wff` refuses.  `(sameAs A A)` is
              ;; accepted, so the two symmetric relations file nothing.
              (is (= (if (= rel 'rewriteOf) #{:not-well-formed} #{})
                     (set (map :violation (v/violations kb))))
                  (str "unexpected violations: " (pr-str (v/violations kb)))))
            (v/clear-violations! kb)))))))

(tu/deftest-kb a-twin-a-derived-merge-created-fires-the-rules-that-match-it
  ;; The second antecedent holds of the representative and not of the retired spelling,
  ;; so the join cannot succeed before the merge and the conclusion cannot be the
  ;; migrated twin of an earlier firing: the twin's return to the agenda is the only
  ;; route to it.
  (tu/with-terms [aliasOf caresFor lives devotedTo Tom CxAlias]
    (v/assert-rule kb [(list caresFor '?x '?y) (list lives '?x)]
                   (list devotedTo '?x '?y) CxAlias {:direction :forward})
    (let [[lo hi] (sort [(tu/tmp-ind "Ann") (tu/tmp-ind "Ann")])]
      (v/assert kb (list lives lo) CxAlias)
      ;; a firing concludes an equality only from forced-monotonic antecedents
      (v/assert kb (list 'forced_monotonic_predicate aliasOf) CxAlias)
      (v/assert-rule kb [(list aliasOf '?x '?y)] (list 'sameAs '?x '?y) CxAlias {:direction :forward})
      (v/assert kb (list caresFor hi Tom) CxAlias)
      (is (nil? (v/handle-of kb (list devotedTo hi Tom) CxAlias))
          "the join must not succeed before the merge, or the twin proves nothing")
      (v/assert kb (list aliasOf lo hi) CxAlias)
      (is (v/same-class? kb lo hi))
      (is (believed? kb (list devotedTo lo Tom) CxAlias)
          "the twin never reached the agenda: nothing fired off the restated fact"))))

(defn- stated-and-derived-merge-reading
  "The sentences CxAlias believes once `ops` run in order, with `lo` and `hi` read back as
  `Lo` and `Hi`: `:fact` `(aliasOf lo hi)`, `:rule` `(aliasOf ?x ?y) => (sameAs ?x ?y)`,
  `:merge` the premise `(sameAs lo hi)`, `:unmerge` its retraction, all `:monotonic`."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [aliasOf CxAlias]
      (let [[lo hi] (sort [(tu/tmp-ind "Ann") (tu/tmp-ind "Ann")])
            m       {:strength :monotonic}]
        (v/assert kb (list 'forced_monotonic_predicate aliasOf) CxAlias)
        (doseq [op ops]
          (case op
            :fact    (v/assert kb (list aliasOf lo hi) CxAlias m)
            :rule    (v/assert-rule kb [(list aliasOf '?x '?y)] (list 'sameAs '?x '?y) CxAlias
                                    (assoc m :direction :forward))
            :merge   (v/assert kb (list 'sameAs lo hi) CxAlias m)
            :unmerge (v/retract! kb (v/handle-of kb (list 'sameAs lo hi) CxAlias))))
        (into #{} (comp (filter #(believed? kb % CxAlias))
                        (map #(replace {lo 'Lo hi 'Hi aliasOf 'aliasOf} %)))
              (for [r [aliasOf 'sameAs], [a b] [[lo lo] [lo hi] [hi hi]]] (list r a b)))))))

(deftest a-merge-stated-and-derived-reads-alike-in-every-arrival-order
  ;; With the premise last, the firing over `(aliasOf Lo Hi)` is stored as a second
  ;; justification of the merge, which the withdrawal at the merge keeps
  ;; (`settle/merge-support`); with the premise first, the spelling is superseded on
  ;; arrival and that firing is made only once the premise leaves.  Belief agrees.
  (doseq [tail [[] [:unmerge]]]
    (is (= #{#{'(aliasOf Lo Lo) '(sameAs Lo Hi) '(sameAs Lo Lo)}}
           (into #{} (map #(stated-and-derived-merge-reading (concat % tail)))
                 (tu/permutations [:fact :rule :merge])))
        (pr-str tail))))

;; ---- 8. disjointness -----------------------------------------------------
;; Dropping the twin would leave the member restated second under its old spelling.

(tu/deftest-kb a-merge-that-creates-a-disjointness-clash-stores-the-twin-and-reports-it
  (tu/with-terms [dog cat CxPet]
    (tu/with-terms [Rex Fluffy]
      (v/assert kb (list 'disjoint dog cat) CxPet {:strength :monotonic})
      (v/assert kb (list dog Rex)    CxPet)
      (v/assert kb (list cat Fluffy) CxPet)
      (v/assert kb (list 'sameAs Rex Fluffy) CxPet)
      (let [[rep other] (sort [Rex Fluffy])
            [t-rep t-other] (if (= rep Rex) [dog cat] [cat dog])]
        (testing "both memberships are restated under the representative and believed"
          (is (believed? kb (list t-rep rep) CxPet))
          (is (believed? kb (list t-other rep) CxPet))
          (is (stored-not-believed? kb (list t-other other) CxPet)))
        (testing "the clash is a reported dilemma, and nothing is filed in violations"
          (is (some #(and (= :disjoint (:kind %))
                          (= #{(list dog rep) (list cat rep)} (set (map :sentence (:sides %)))))
                    (v/contradictions kb)))
          (is (not-any? #(= :disjoint (:violation %)) (v/violations kb))))))))

(tu/deftest-kb a-clash-member-out-at-the-merge-takes-the-representative-when-its-defeater-goes
  ;; `(dog Bea)` is OUT when the merge arrives, defeated by the :monotonic `(cat Bea)`;
  ;; its twin is stored OUT beside it, so retracting `(cat Bea)` leaves the KB a KB
  ;; built without `(cat Bea)` would be: `(dog Ann)` believed, `(dog Bea)` superseded
  (tu/with-terms [dog cat CxZoo]
    (tu/with-terms [Ann Bea]
      (let [[rep other] (sort [Ann Bea])]
        (v/assert kb (list 'disjoint dog cat) CxZoo {:strength :monotonic})
        (v/assert kb (list cat other) CxZoo {:strength :monotonic})
        (v/assert kb (list dog other) CxZoo)
        (v/assert kb (list 'equals rep other) CxZoo {:strength :monotonic})
        (is (believed? kb (list cat rep) CxZoo))
        (is (stored-not-believed? kb (list dog rep) CxZoo))
        (v/retract! kb (v/handle-of kb (list cat other) CxZoo))
        (is (believed? kb (list dog rep) CxZoo))
        (is (stored-not-believed? kb (list dog other) CxZoo))))))

;; ---- 9. well-formedness --------------------------------------------------
;; The two-edge cycle and a longer one, because a check comparing only the two arguments
;; of the arriving edge passes the first and misses the second.

(tu/deftest-kb a-rewrite-of-cycle-is-rejected
  (tu/with-terms [CxName]
    (tu/with-terms [A B C]
      (testing "the two-edge cycle"
        (v/assert kb (list 'rewriteOf A B) CxName)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'rewriteOf B A) CxName))))
      (testing "the three-edge cycle, which a pairwise check would miss"
        (v/assert kb (list 'rewriteOf B C) CxName)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'rewriteOf C A) CxName))))
      (testing "and a refused edge leaves nothing stored"
        (is (nil? (v/handle-of kb (list 'rewriteOf B A) CxName)))
        (is (nil? (v/handle-of kb (list 'rewriteOf C A) CxName)))))))

(tu/deftest-kb a-rewrite-of-self-edge-is-rejected
  (tu/with-terms [CxName]
    (tu/with-terms [A]
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'rewriteOf A A) CxName)))
      (is (nil? (v/handle-of kb (list 'rewriteOf A A) CxName))))))

(tu/deftest-kb a-reflexive-same-as-is-stored-and-merges-nothing
  (tu/with-terms [A CxName]
    (is (some? (v/assert kb (list 'sameAs A A) CxName)))
    (is (= #{A} (set (v/equiv-class kb A CxName))))))

;; ---- 10. what the supersession reconcile costs ---------------------------
;; `special/refresh-supersessions` reconciles the superseded spellings on the write path
;; (docs/equality.md, "The reconcile in step 2 runs on the write path").  The cost tests
;; count `kb/rewrite-term*` calls, one per displaced spelling re-examined, and the three
;; after them are the cases the narrowed reconcile must not miss.

(defn- counting-rewrites
  "Run `f`, returning the number of `kb/rewrite-term*` calls it caused."
  [f]
  (let [n    (atom 0)
        orig kb/rewrite-term*]
    (with-redefs [kb/rewrite-term* (fn [& args] (swap! n inc) (apply orig args))]
      (f))
    @n))

(defn- merges!
  "n `(sameAs …)` merges, each displacing exactly one stored fact: the fact is written
  under the larger spelling and the smaller one wins the content-keyed election."
  [kb n]
  (dotimes [i n]
    (v/assert kb (list 'eqcBorn (symbol (str "EqcHi" i)) 'EqcPlace) merge-cost-ctx)
    (v/assert kb (list 'sameAs (symbol (str "EqcAa" i)) (symbol (str "EqcHi" i)))
              merge-cost-ctx)))

(deftest one-unrelated-retraction-does-not-re-examine-every-standing-merge
  (testing "a retraction naming no merged term costs the reconcile nothing, at any
            standing merge count"
    ;; The region this settle moved is the one plain fact and what rested on it.  No
    ;; equality edge moved, no rewrite rule moved and no context edge moved, so no
    ;; standing entry can have stopped holding — and none is re-examined.
    (let [cost (fn [n]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (merges! kb n)
                   (let [h (v/assert kb '(eqc_plain EqcTarget) merge-cost-ctx)]
                     (counting-rewrites #(v/retract! kb h)))))
          few  (cost 10)
          many (cost 40)]
      (is (= 0 few many)
          (str "an unrelated retraction re-examined the standing merges: " few
               " (10 merges) / " many " (40 merges) rewrites")))))

(deftest loading-merges-does-not-re-examine-the-merges-already-standing
  (testing "asserting one more merge re-examines what it displaced, not the whole set"
    ;; The other half of the same claim, and the one that makes a corpus load linear.
    ;; Migration walks the class the new edge moved and hands the reconcile its own
    ;; output; every other entry belongs to a class this edge did not touch.
    (let [cost (fn [standing]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (merges! kb standing)
                   (v/assert kb '(eqcBorn EqcHiZ EqcPlace) merge-cost-ctx)
                   (counting-rewrites
                    #(v/assert kb '(sameAs EqcAaZ EqcHiZ) merge-cost-ctx))))
          few  (cost 10)
          many (cost 40)]
      (is (= few many)
          (str "one more merge cost more on a KB with more standing merges: " few
               " (10 standing) / " many " (40 standing) rewrites")))))

;; The three cases the narrowing must not miss.  Each moves something the region alone
;; does not describe, and each leaves a spelling hidden that should have come back.

(deftest un-merging-one-pair-revives-it-with-other-merges-standing
  (testing "retracting one sameAs among many revives exactly its own spelling"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merges! kb 20)
      (let [eq (v/handle-of kb '(sameAs EqcAa7 EqcHi7) merge-cost-ctx)
            f7 (v/handle-of kb '(eqcBorn EqcHi7 EqcPlace) merge-cost-ctx)
            f8 (v/handle-of kb '(eqcBorn EqcHi8 EqcPlace) merge-cost-ctx)]
        (is (false? (v/in? kb f7)) "displaced while the merge stands")
        (v/retract! kb eq)
        (is (true? (v/in? kb f7))
            "the un-merged spelling is believed again: the entry was re-examined")
        (is (false? (v/in? kb f8))
            "and the pair beside it, whose merge still stands, is still displaced")))))

(deftest un-merging-a-derived-equality-revives-its-spelling-too
  (testing "a merge nobody asserted, withdrawn by a retraction that never names it"
    ;; The retracted handle is a `motherOf` fact; the equality it supported is derived
    ;; (`functional`), so the thing that stopped displacing the spelling is not in the
    ;; region under its own name.  The closure moving is the whole of what says so.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merges! kb 20)
      (v/assert kb '(functional eqcMotherOf) merge-cost-ctx)
      (v/assert kb '(eqcMotherOf EqcTom EqcMaryA) merge-cost-ctx {:strength :monotonic})
      (let [second-fact (v/assert kb '(eqcMotherOf EqcTom EqcMaryB) merge-cost-ctx {:strength :monotonic})]
        (v/assert kb '(eqcCaresFor EqcMaryB EqcTom) merge-cost-ctx)
        (let [orig (v/handle-of kb '(eqcCaresFor EqcMaryB EqcTom) merge-cost-ctx)]
          (is (false? (v/in? kb orig))
              "displaced by the derived merge, which elected the smaller spelling")
          (v/retract! kb second-fact)
          (is (true? (v/in? kb orig))
              "and believed again once the derived merge goes, twenty merges standing"))))))

(deftest dropping-a-schematic-rewrite-revives-what-it-normalized
  (testing "an equation leaving re-normalizes the sentences it reached"
    ;; The channel a class comparison cannot see: a schematic rewrite displaces a
    ;; spelling by normalizing its *terms*, so the entry it produced names no merged
    ;; symbol at all.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merges! kb 20)
      (v/assert kb '(eqcKnows EqcRoot (eqc_dad_of (eqc_dad_of EqcRoot))) merge-cost-ctx)
      (let [orig (v/handle-of kb '(eqcKnows EqcRoot (eqc_dad_of (eqc_dad_of EqcRoot)))
                              merge-cost-ctx)
            rule (v/assert kb '(equals (eqc_dad_of (eqc_dad_of ?x)) (eqc_grandad_of ?x))
                           merge-cost-ctx)]
        (is (false? (v/in? kb orig)) "normalized away while the equation stands")
        (v/retract! kb rule)
        (is (true? (v/in? kb orig))
            "and believed again once nothing normalizes it")))))

;; The equality relations' arguments are mentions, so a merge does not rewrite a denial
;; of the merge into `(not (sameAs A A))`.

(tu/deftest-kb a-denial-of-an-equality-leaves-a-default-merge-standing-in-either-order
  ;; the equality relations are in the baseline forced-monotonic set, so on this bare KB too
  ;; the merge is never a loser and a :monotonic denial of it loses to it (decision 13);
  ;; the merge keeps the strength it was written at
  (doseq [denial-first? [false true]]
    (tu/with-terms [A B]
      (let [deny  #(v/assert kb (list 'not (list 'sameAs A B)) 'CxUniverse {:strength :monotonic})
            _     (when denial-first? (deny))
            merge (v/assert kb (list 'sameAs A B) 'CxUniverse)
            d     (if denial-first? (v/handle-of kb (list 'not (list 'sameAs A B)) 'CxUniverse) (deny))]
        (is (v/same-class? kb A B) (str "denial first: " denial-first?))
        (is (= :default (v/defeat-class kb merge)))
        (is (not (v/in? kb d)) "the denial loses")))))

(deftest the-mention-set-mirrors-the-canonical-equality-predicate-set
  ;; `res/equality-mention-heads` is `rewrite/equality-relations`, a copy of
  ;; `kb/equality-predicates` — `kb` requires `resolution`, so the canonical set cannot be
  ;; required back into it.  Keep the two equal, or a relation added to one and not the
  ;; other rewrites the mentions of the relation it forgot.
  (is (= kb/equality-predicates @#'res/equality-mention-heads)))

;; ---- a stated equation is answered ----------------------------------------

;; Each column is one read: `ask?`, `prove` and `sentexes-matching` (docs/equality.md,
;; "Answering an equation").

(defn- equation-reads
  "Every read of `pred` over `a` / `b` / `c`, where `(pred a b)` and `(sameAs b c)` are
  stated in `ctx`."
  [kb pred a b c ctx]
  {:stated    (v/ask? kb (list pred a b) ctx)
   :symmetric (v/ask? kb (list pred b a) ctx)
   :reflexive (v/ask? kb (list pred a a) ctx)
   :chain     (v/ask? kb (list pred a c) ctx)
   :open      (set (map #(get % '?y) (v/ask kb (list pred a '?y) ctx)))
   :prove     (count (v/prove kb (list pred a b) ctx))
   :matching  (count (v/sentexes-matching kb (list pred a b) ctx))})

(tu/deftest-kb a-stated-equation-is-answered-by-every-read
  (doseq [pred ['sameAs 'equals]]
    (testing (str pred " is reflexive, symmetric and transitive through the closure")
      (tu/with-terms [CxEq]
        (let [[a b c] (sort [(tu/tmp-ind "Eq") (tu/tmp-ind "Eq") (tu/tmp-ind "Eq")])]
          (v/assert kb (list pred a b) CxEq {:strength :monotonic})
          (v/assert kb (list 'sameAs b c) CxEq {:strength :monotonic})
          (is (= {:stated true :symmetric true :reflexive true :chain true
                  :open #{a b c} :prove 1 :matching 1}
                 (equation-reads kb pred a b c CxEq))))))))

(tu/deftest-kb a-stated-rewrite-of-is-answered-through-reader-representatives
  ;; The stored preference stays directed. Its public relation normalizes both
  ;; endpoints before matching, so a visible edge can witness a canonical self pair.
  ;; It does not assert that self pair or change raw record/provenance reads.
  (tu/with-terms [CxEq]
    (let [[a b c] (sort [(tu/tmp-ind "Rw") (tu/tmp-ind "Rw") (tu/tmp-ind "Rw")])]
      (v/assert kb (list 'rewriteOf a b) CxEq {:strength :monotonic})
      (v/assert kb (list 'sameAs b c) CxEq {:strength :monotonic})
      (is (= {:stated true :symmetric true :reflexive true :chain true
              :open #{a} :prove 1 :matching 1}
             (equation-reads kb 'rewriteOf a b c CxEq))))))

(tu/deftest-kb an-equation-is-answered-only-where-it-is-visible
  ;; The closure read is scoped like `same-class?`: a context outside the equation's
  ;; ancestor set was told nothing, so the unique-name assumption still holds there.
  (tu/with-terms [CxEq CxElsewhere]
    (let [[a b] (sort [(tu/tmp-ind "Vis") (tu/tmp-ind "Vis")])]
      (v/assert kb (list 'sameAs a b) CxEq {:strength :monotonic})
      (testing "visible where stated"
        (is (true? (v/ask? kb (list 'sameAs b a) CxEq))))
      (testing "not visible from a context that does not inherit it"
        (is (false? (v/ask? kb (list 'sameAs b a) CxElsewhere)))
        (is (= #{a} (set (map #(get % '?y) (v/ask kb (list 'sameAs a '?y) CxElsewhere)))))
        (is (true? (v/ask? kb (list 'different a b) CxElsewhere)))))))

(tu/deftest-kb a-ground-instance-of-a-schematic-equation-is-answered
  ;; Each side of a ground `equals` is a term, normalized at its own root: the instance
  ;; of `(equals (fatherOf (fatherOf ?x)) (grandfather_of ?x))` at `Bob` reaches one
  ;; normal form, and an instance of nothing does not.
  (tu/with-terms [fatherOf grandfather_of Bob Ann CxEq]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))
              CxEq)
    (is (true? (v/ask? kb (list 'equals (list fatherOf (list fatherOf Bob))
                                (list grandfather_of Bob))
                       CxEq)))
    (is (false? (v/ask? kb (list 'equals (list fatherOf (list fatherOf Bob))
                                 (list grandfather_of Ann))
                        CxEq)))))

;; ---- a `different` guard is order-independent ----------------------------

(deftest a-different-guarded-firing-is-withdrawn-by-a-fact-that-arrives-after-it
  ;; `different` names no handle a justification could carry, so the rule is re-checked
  ;; (`rules/different-flip-predicates`, `chain/different-blocks?`).  Both arrival orders
  ;; run against each flip source.
  (doseq [[label flip!]
          [["sameAs — a merge puts the two names in one class"
            (fn [kb a b] (v/assert kb (list 'sameAs a b) 'CxUniverse))]
           ["indeterminate_term — a member is exempt from the unique-name assumption"
            (fn [kb a _] (v/assert kb (list 'indeterminate_term a) 'CxUniverse))]
           ["a declared subkind of it — reached through the genls fan, not by name"
            (fn [kb a _]
              (tu/with-terms [vague_kind]
                (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
                (v/assert kb (list vague_kind a) 'CxUniverse)))]]]
    (testing label
      (let [believed (doall
                      (for [order [:guard-then-fact :fact-then-guard]]
                        (tu/with-kb [kb]
                          (tu/with-terms [pRel qRel Aa Bb]
                            (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
                            (v/assert kb (list 'binary_predicate qRel) 'CxUniverse)
                            (when (= order :fact-then-guard) (flip! kb Aa Bb))
                            (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                                              (list 'different '?x '?y))
                                               (list qRel '?x '?y))
                                      'CxUniverse {:direction :forward})
                            (v/assert kb (list pRel Aa Bb) 'CxUniverse)
                            (when (= order :guard-then-fact) (flip! kb Aa Bb))
                            [(v/ask? kb (list 'different Aa Bb) 'CxUniverse)
                             (v/ask? kb (list qRel Aa Bb) 'CxUniverse)]))))]
        (is (apply = believed)
            (str "the same knowledge in either order yields the same beliefs; got "
                 (pr-str (vec believed))))
        (is (= [false false] (first believed))
            "and the answer is the one the guard licenses: no difference, no conclusion")))))

(tu/deftest-kb a-different-guarded-firing-comes-back-when-the-withdrawing-fact-leaves
  ;; The release direction, which the block alone does not give: retracting the fact that
  ;; suspended the unique-name assumption restores the difference, and the firing it
  ;; guarded is re-derived rather than left withdrawn.
  (tu/with-terms [pRel qRel Aa Bb]
    (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
    (v/assert kb (list 'binary_predicate qRel) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list pRel '?x '?y) (list 'different '?x '?y))
                       (list qRel '?x '?y))
              'CxUniverse {:direction :forward})
    (v/assert kb (list 'indeterminate_term Aa) 'CxUniverse)
    (v/assert kb (list pRel Aa Bb) 'CxUniverse)
    (is (not (v/ask? kb (list qRel Aa Bb) 'CxUniverse))
        "exempt from the UNA, so the guard does not hold and nothing is concluded")
    (v/retract! kb (v/handle-of kb (list 'indeterminate_term Aa) 'CxUniverse))
    (is (v/ask? kb (list qRel Aa Bb) 'CxUniverse)
        "and the conclusion arrives once the exemption goes, with no re-assertion")))

(deftest a-different-guarded-firing-comes-back-through-the-subkind-channel-too
  ;; The release direction through the channel the flip set reaches by fan-out rather than
  ;; by name.  A kind declared `(genl K indeterminate_term)` makes its members exempt from
  ;; the unique-name assumption, and the exemption rests on **two** sentences — the edge
  ;; and the membership — so withdrawing either restores the difference and owes the
  ;; firing back.  `different-flip-predicates` names `genl` outright and reaches the
  ;; membership through `special/recheck-on-predicate`'s `genls-global` fan, and neither
  ;; route has a blocked justification to move: the guard refuses the firing at its
  ;; placement, and the refusal record is what the re-check re-decides.
  (doseq [[label lift!]
          [["the membership retracted — reached through the genls fan"
            (fn [kb k a] (v/retract! kb (v/handle-of kb (list k a) 'CxUniverse)))]
           ["the genl edge retracted — the edge is what made the kind indeterminate"
            (fn [kb k _] (v/retract! kb (v/handle-of kb (list 'genl k 'indeterminate_term)
                                                     'CxUniverse)))]]]
    (testing label
      (tu/with-cleared-kb [kb tu/isolated-fresh]
        (tu/with-terms [pRel qRel Aa Bb vague_kind]
          (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
          (v/assert kb (list 'binary_predicate qRel) 'CxUniverse)
          (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                            (list 'different '?x '?y))
                             (list qRel '?x '?y))
                    'CxUniverse {:direction :forward})
          (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
          (v/assert kb (list vague_kind Aa) 'CxUniverse)
          (v/assert kb (list pRel Aa Bb) 'CxUniverse)
          (is (not (v/ask? kb (list qRel Aa Bb) 'CxUniverse))
              "exempt from the UNA, so the guard does not hold and nothing is concluded")
          (lift! kb vague_kind Aa)
          (is (v/ask? kb (list 'different Aa Bb) 'CxUniverse)
              "the exemption is gone, so the two are provably different again")
          (is (v/ask? kb (list qRel Aa Bb) 'CxUniverse)
              "and the firing the guard licensed arrives, with no re-assertion"))))))

;; A merge can withdraw a `different` guard and never release one, so it re-decides the
;; firings binding a term of the merged class and joins the rule nowhere
;; (`special/recheck-equality-edge`'s `{::merged class}` marker).  Eight firings; one
;; merge joins the pair of the first, one joins a term of the second to a term no firing
;; names.

(deftest a-merge-re-decides-only-the-different-guarded-firings-naming-its-class
  (tu/with-shipped-config
    (let [join    @#'chain/join-antecedent
          guard   chain/different-blocks?
          reading (fn [order count?]
                    (tu/with-neutral-kb [kb tu/fresh]
                      (tu/with-terms [pRel qRel Cc]
                        (let [as     (mapv #(tu/tmp-ind (str "A" %)) (range 8))
                              bs     (mapv #(tu/tmp-ind (str "B" %)) (range 8))
                              tally  (atom {:rows 0 :asks 0})
                              merges #(do (v/assert kb (list 'sameAs (as 0) (bs 0)) 'CxUniverse
                                                    {:strength :monotonic})
                                          (v/assert kb (list 'sameAs (as 1) Cc) 'CxUniverse
                                                    {:strength :monotonic}))]
                          (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
                          (v/assert kb (list 'binary_predicate qRel) 'CxUniverse)
                          (doseq [op order]
                            (case op
                              :rule   (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                                                        (list 'different '?x '?y))
                                                         (list qRel '?x '?y))
                                                'CxUniverse {:direction :forward})
                              :facts  (doseq [i (range 8)]
                                        (v/assert kb (list pRel (as i) (bs i)) 'CxUniverse))
                              :merges (if count?
                                        (with-redefs-fn
                                          {#'chain/join-antecedent
                                           (fn [& a] (let [r (apply join a)]
                                                       (swap! tally update :rows + (count r)) r))
                                           #'chain/different-blocks?
                                           (fn [& a] (swap! tally update :asks inc) (apply guard a))}
                                          merges)
                                        (merges))))
                          {:tally @tally
                           :believed (vec (for [i (range 8)]
                                            (v/ask? kb (list qRel (as i) (bs i)) 'CxUniverse)))}))))]
      (let [{:keys [tally believed]} (reading [:rule :facts :merges] true)]
        (is (= 0 (:rows tally)) "neither merge joins the rule")
        (is (<= (:asks tally) 4) "the guard is asked of the two firings naming a merged term")
        (is (= (into [false] (repeat 7 true)) believed)))
      (is (= #{(into [false] (repeat 7 true))}
             (set (map #(:believed (reading % false)) (tu/permutations [:rule :facts :merges]))))
          "every arrival order believes the same firings"))))

(def ^:private undone {:unmerge :merge :unac :ac :unindet :indet :unedge :edge})

(defn- different-guard-reading
  "What the forward rule `(pRel ?x ?y) ∧ (different ?x ?y) ⇒ (qRel ?x ?y)`, stated in
  `home`, leaves believed once `ops` run in order: `(different Aa y)` and `(qRel Aa y)`
  asked at `home`, then at `there`, where `y` is `Cc` when `ops` holds `:fact-ac` and `Bb`
  otherwise.  `:rule`, `:fact` `(pRel Aa Bb)` and `:fact-ac` `(pRel Aa Cc)` are stated in
  `home`, and `:plain` states the rule without its `different`; `:merge`
  `(sameAs Aa Bb)`, `:bc` `(sameAs Bb Cc)`, `:ac` `(sameAs Aa Cc)` and `:indet`
  `(indeterminate_term Aa)` are stated in `there`; `:edge` is `(genlCx there home)`; each
  key of `undone` retracts the statement its value names.  `home` and `there` are
  `:main`, `:other` or `:universe`."
  [home there ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [pRel qRel Aa Bb Cc CxMain CxOther]
      (let [cx     {:main CxMain :other CxOther :universe 'CxUniverse}
            h      (cx home)
            t      (cx there)
            y      (if (some #{:fact-ac} ops) Cc Bb)
            stated {:merge [(list 'sameAs Aa Bb) t]
                    :bc    [(list 'sameAs Bb Cc) t]
                    :ac    [(list 'sameAs Aa Cc) t]
                    :indet [(list 'indeterminate_term Aa) t]
                    :edge  [(list 'genlCx t h) 'CxUniverse]}]
        (doseq [op ops]
          (case op
            :rule (v/assert kb (list 'implies (list 'and (list pRel '?x '?y) (list 'different '?x '?y))
                                     (list qRel '?x '?y))
                            h {:direction :forward})
            :plain (v/assert kb (list 'implies (list pRel '?x '?y) (list qRel '?x '?y))
                             h {:direction :forward})
            :fact (v/assert kb (list pRel Aa Bb) h)
            :fact-ac (v/assert kb (list pRel Aa Cc) h)
            (:merge :bc :ac :indet :edge) (let [[sen c] (stated op)] (v/assert kb sen c {:strength :monotonic}))
            (let [[sen c] (stated (undone op))] (v/retract! kb (v/handle-of kb sen c)))))
        (vec (for [c [h t], g [(list 'different Aa y) (list qRel Aa y)]]
               (v/ask? kb g c)))))))

(deftest a-different-guard-reads-only-the-merges-its-placement-sees-in-every-order
  (doseq [[label there expected]
          [["a merge in a context the placement does not see" :other [true true false false]]
           ["a merge at the placement" :main [false false false false]]]]
    (testing label
      (let [orders (tu/permutations [:rule :fact :merge])]
        (is (= #{expected} (set (map #(different-guard-reading :main there %) orders))))
        (testing "and retracting the merge gives the reading of a load without it"
          (is (= #{(different-guard-reading :main there [:rule :fact])}
                 (set (map #(different-guard-reading :main there (concat % [:unmerge])) orders)))))))))

(deftest a-merge-below-the-placement-defeats-a-different-guarded-firing-there-in-every-order
  ;; CxOther sees CxMain through the edge, and the merge or the membership only CxOther
  ;; sees blocks the conclusion there and nowhere above it: a guard defeat placed at
  ;; CxOther, resting on the merge or the membership (`chain/different-guard-placements`).
  (doseq [[label flip unflip] [["a merge" :merge :unmerge]
                               ["an indeterminate_term membership" :indet :unindet]]]
    (testing label
      (let [orders (tu/permutations [:rule :fact flip :edge])]
        (is (= #{[true true false false]}
               (set (map #(different-guard-reading :main :other %) orders))))
        (testing "and retracting the flip or the edge gives the reading of a load without it"
          (is (= #{(different-guard-reading :main :other [:rule :fact :edge])}
                 (set (map #(different-guard-reading :main :other (concat % [unflip])) orders))))
          (is (= #{(different-guard-reading :main :other [:rule :fact flip])}
                 (set (map #(different-guard-reading :main :other (concat % [:unedge])) orders)))))))))

(deftest a-merge-below-the-placement-with-a-stated-name-defeats-a-different-guarded-firing-there-in-every-order
  (let [reading (fn [ops]
                  (tu/with-neutral-kb [kb tu/fresh]
                    (tu/with-terms [pRel qRel Ab Bb Kk CxMain CxOther]
                      (let [M      {:strength :monotonic}
                            stated {:edge  [(list 'genlCx CxOther CxMain) 'CxUniverse M]
                                    :rule  [(list 'implies (list 'and (list pRel '?x '?y) (list 'different '?x '?y))
                                                  (list qRel '?x '?y)) CxMain {:direction :forward}]
                                    :fact  [(list pRel Kk Bb) CxMain {}]
                                    :indet [(list 'indeterminate_term Ab) CxMain M]
                                    :merge [(list 'sameAs Ab Kk) CxOther M]}]
                        (doseq [op ops]
                          (if (= :unmerge op)
                            (v/retract! kb (apply v/handle-of kb (butlast (stated :merge))))
                            (apply v/assert kb (stated op))))
                        (vec (for [c [CxMain CxOther], g [(list 'different Kk Bb) (list qRel Kk Bb)]]
                               (v/ask? kb g c)))))))
        orders  (map #(cons :edge %) (tu/permutations [:rule :fact :indet :merge]))]
    (is (= #{[true true false false]} (set (map reading orders)))
        (str "Ab sorts before Kk, so CxOther elects the stated name, and the defeat rests on"
             " Ab's membership and the merge"))
    (is (= #{[true true true true]} (set (map #(reading (concat % [:unmerge])) orders)))
        "retracting the merge lifts the defeat")))

(defn- restatement-link-rows
  "The merges in CxOther restate the conclusion CxMain stores into CxOther, which sees it
  through the edge.  The restatement's justification names the edge and every merge on
  one path from each displaced term to its representative (`special/migrate-into`), so
  retracting a link withdraws it and a surviving path restates it again.  `orders-of`
  gives the arrival orders a row's ops are run in."
  [orders-of]
  (doseq [[label ops undo]
          [["the context edge" [:plain :fact :merge :edge] [:unedge]]
           ["one link of a chain of merges" [:plain :fact-ac :merge :bc :edge] [:unmerge]]
           ["the direct merge of a triangle, which leaves a path"
            [:plain :fact-ac :merge :bc :ac :edge] [:unac]]
           ["both merges at Aa of a triangle" [:plain :fact-ac :merge :bc :ac :edge] [:unac :unmerge]]]]
    (testing label
      (let [orders (orders-of ops)]
        (is (= #{[true true false true]}
               (set (map #(different-guard-reading :main :other %) orders))))
        (is (= #{(different-guard-reading :main :other (remove (set (map undone undo)) ops))}
               (set (map #(different-guard-reading :main :other (concat % undo)) orders))))))))

(deftest ^:slow a-restatement-is-withdrawn-with-a-link-it-rests-on-in-every-order
  (restatement-link-rows tu/permutations))

(deftest a-restatement-is-withdrawn-with-a-link-it-rests-on-with-the-rule-and-fact-first
  ;; the sampled twin of the sweep above: the merges and the edge in every order
  (restatement-link-rows (fn [ops] (map #(concat (take 2 ops) %) (tu/permutations (drop 2 ops))))))

(deftest the-predall-indeterminacy-example-agrees-in-every-order
  ;; docs/predall.md, "A `different` guard is re-checked, not supported".
  (let [orders (tu/permutations [:rule :fact :indet])]
    (is (= #{[false false false false]}
           (set (map #(different-guard-reading :universe :universe %) orders))))
    (is (= #{[true true true true]}
           (set (map #(different-guard-reading :universe :universe (concat % [:unindet])) orders))))))
