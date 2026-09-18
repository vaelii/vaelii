;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.stratification-edge-test
  "Stratification when a **taxonomy edge** is what closes the cycle, rather than a
  rule.  See the Stratification section of
  [docs/exceptions.md](../../docs/exceptions.md).

  Both kinds of edge in the rule dependency graph fan out over the genl **spec**
  closure, so a cycle through negation can exist purely because of a `genl` edge: an
  exception on `flightless` is reached by a stored `(penguin Opus)` the moment
  `(genl penguin flightless)` holds.  `stratification_test` covers the case where the
  edge is already there and a rule arrives last; this namespace covers the other
  order, where both rules are stored and the **edge** arrives last.

  Three things to pin, and they are the same three the rule path pins:

  * the edge that closes a cycle is **refused**, and leaves nothing behind — neither
    a sentex nor a taxonomy closure that learned it;
  * an edge that closes nothing is accepted, so the refusal above is attributable to
    the cycle and not to the mere presence of an excepted rule;
  * the walk is **skipped entirely** when no stored rule carries a negative edge, which
    is every rule in the bundled starter and therefore every ordinary `genl` assert.
    Asserted by counting `wff/negation-cycle` calls, not by a clock.

  Plus the derivation path, where the answer is different by necessity: forward
  chaining cannot throw, so a derived edge that would close a cycle is dropped and
  reported in `(v/violations kb)` alongside the definitional constraints.

  House rules as everywhere: gensym'd temporaries via `tu/with-terms`, engine
  vocabulary (`genl`, `genlCx`, `set/defaultRule`, `exceptWhen`) literal, and the
  neutral fixture asserts the KB is restored."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wff :as wff]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- except-rule
  "The shape docs/exceptions.md writes: an exception query wrapping a defeasible rule."
  [exception antes conseq]
  (list 'exceptWhen exception (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq)))))

(defn- refusal
  "Assert, and return the `ex-data` of the refusal — nil if the assert went through.
  Reading the data rather than catching bare `ExceptionInfo` is what distinguishes a
  stratification refusal from a well-formedness or naming one, which would pass a
  `thrown?` test for the wrong reason."
  [kb sentence context]
  (try (v/assert kb sentence context) nil
       (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- walks
  "Run `f`, returning how many times it walked the rule dependency graph.  Counting
  the search calls measures the fast path exactly; a timing test would measure the
  machine."
  [f]
  (let [n    (atom 0)
        orig wff/negation-cycle]
    (with-redefs [wff/negation-cycle (fn [& args] (swap! n inc) (apply orig args))]
      (f))
    @n))

(defn- cycle-shaped-rules!
  "The two rules of the cycle, with the `genl` edge that closes it **not** asserted:

    R1  excepts-on `flightless`, concludes `p`
    R2  depends-on `p`,          concludes `penguin`

  Stratified as it stands — nothing concludes `flightless`.  Adding
  `(genl penguin flightless)` puts `penguin` in `specs(flightless)`, so R1's negative
  edge reaches R2 and R2's positive edge reaches back: a cycle through negation."
  [kb {:keys [base p flightless penguin ctx]}]
  (v/assert kb (except-rule (list flightless '?x) [(list base '?x)] (list p '?x)) ctx)
  (v/assert kb (vr/rule-sentence [(list p '?x)] (list penguin '?x)) ctx {:direction :forward}))

;; ---- the edge that closes the cycle is refused ---------------------------
;; DECISION: the `genl` assert is the operation at fault, so the **edge** is what is
;; refused — the same answer `wff` already gives an edge that would make the taxonomy
;; cyclic, and the one that keeps stored state stratified at all times.

(tu/deftest-kb a-genl-edge-that-closes-a-cycle-between-stored-rules-is-refused
  (tu/with-terms [base p flightless penguin CxEdge]
    (let [terms {:base base :p p :flightless flightless :penguin penguin :ctx CxEdge}]
      (cycle-shaped-rules! kb terms)
      (let [data (refusal kb (list 'genl penguin flightless) CxEdge)]
        (testing "the edge is refused, and says why"
          (is (= :not-stratified (:type data))))
        (testing "the refusal names the cycle it would have created"
          (is (seq (:cycle data))))))))

(tu/deftest-kb a-genl-edge-that-closes-nothing-is-accepted
  ;; The control for the test above.  Same two rules, same excepted rule in the KB,
  ;; a `genl` edge that simply does not put anything in the exception's spec closure
  ;; — so the refusal above is attributable to the **cycle** and not to "there is an
  ;; exception around, refuse edges".
  (tu/with-terms [base p flightless penguin unrelated CxEdge]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxEdge})
    (is (v/assert kb (list 'genl penguin unrelated) CxEdge)
        "penguin under an unrelated supertype crosses no negative edge")
    (is (tax/genl?-global (reasoning/taxonomy kb) penguin unrelated)
        "and the accepted edge did reach the closures")))

(tu/deftest-kb the-same-edge-is-accepted-when-the-rule-carries-no-exception
  ;; The second control, one step further out: identical rule *shapes*, identical
  ;; edge, but R1 states no exception — so the graph has no negative edge at all and
  ;; the cycle it would close is ordinary positive recursion, which is a supported
  ;; feature rather than a violation.
  (tu/with-terms [base p flightless penguin CxPlain]
    (is (v/assert kb (vr/rule-sentence [(list base '?x)] (list p '?x)) CxPlain {:direction :forward}))
    (is (v/assert kb (vr/rule-sentence [(list p '?x)] (list penguin '?x)) CxPlain {:direction :forward}))
    (is (v/assert kb (list 'genl penguin flightless) CxPlain))))

;; ---- a genlCx edge takes the same path ------------------------------
;; DECISION: the trigger sits on **both** transitive relations, the way
;; `recheck-every-exception` does, so the two edge kinds cannot drift apart.  Today
;; only a `genl` edge can actually move the graph — the dependency graph is over
;; *predicates* and mentions no context, so a `genlCx` edge adds no graph edge
;; and the walk finds nothing.  This test pins that reading: the check runs (the walk
;; is counted) and the edge is accepted.

(tu/deftest-kb a-genlCx-edge-runs-the-same-check-and-is-accepted
  (tu/with-terms [base p flightless penguin CxEdge CxSub]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxEdge})
    (let [n (walks #(v/assert kb (list 'genlCx CxSub CxEdge) CxSub))]
      (testing "the edge kind is checked, not skipped"
        (is (pos? n)))
      (testing "and is accepted: the graph is over predicates, so no context edge is in it"
        (is (tax/sees? (reasoning/taxonomy kb) CxSub CxEdge))))))

;; ---- a refused edge leaves nothing behind --------------------------------

(tu/deftest-kb a-refused-edge-leaves-neither-a-sentex-nor-a-closure
  ;; The check runs before the sentex is created *and* before the taxonomy is
  ;; touched: it adds the edge to a detached copy of the taxonomy to ask the
  ;; question.  A half-applied refusal would leave the closures claiming an edge no
  ;; sentex supports, which `recover` would then disagree with.
  (tu/with-terms [base p flightless penguin CxEdge]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxEdge})
    (let [before-sx    (tu/sentex-ids kb)
          before-dd    (tu/justification-ids kb)
          before-edges (tax/genl-edges (reasoning/taxonomy kb))
          data         (refusal kb (list 'genl penguin flightless) CxEdge)]
      (is (= :not-stratified (:type data)))
      (is (= before-sx (tu/sentex-ids kb))    "no sentex was stored")
      (is (= before-dd (tu/justification-ids kb)) "no justification was stored")
      (testing "and the cached closures never learned the edge"
        (is (= before-edges (tax/genl-edges (reasoning/taxonomy kb))))
        (is (not (tax/genl?-global (reasoning/taxonomy kb) penguin flightless)))
        (is (not (contains? (tax/specs-global (reasoning/taxonomy kb) flightless) penguin)))))))

;; ---- the fast path ------------------------------------------------------
;; Every rule in the bundled starter is unexcepted, so a regression here would slow
;; every ordinary `genl` assert in the ontology.

(tu/deftest-kb an-edge-change-walks-nothing-when-no-rule-carries-an-exception
  (tu/with-terms [base p CxFast]
    (v/assert kb (vr/rule-sentence [(list base '?x)] (list p '?x)) CxFast {:direction :forward})
    (testing "no exception anywhere: the edge assert does not walk the graph at all"
      (tu/with-terms [sub super]
        (is (zero? (walks #(v/assert kb (list 'genl sub super) CxFast))))))
    (testing "control: one excepted rule in the KB and the same operation does walk"
      (tu/with-terms [exc otherBase other sub super]
        (v/assert kb (except-rule (list exc '?x) [(list otherBase '?x)] (list other '?x))
                  CxFast)
        (is (pos? (walks #(v/assert kb (list 'genl sub super) CxFast))))))))

;; ---- the derivation path -------------------------------------------------
;; DECISION: a *derived* edge is **dropped and reported**, not thrown.  Forward
;; chaining is a fixpoint and an exception escaping one rule firing would make the
;; resulting belief set depend on which rule fired first — the same reasoning that
;; puts the definitional constraints in `violations` rather than in a throw.  Dropping
;; rather than merely reporting is what keeps the invariant: an unstratified edge that
;; was only *reported* would still be in the taxonomy.

(tu/deftest-kb a-derived-edge-that-would-close-a-cycle-is-dropped-and-reported
  (tu/with-terms [base p flightless penguin subtypeMarker noted CxDerive]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxDerive})
    ;; a rule that *concludes* a genl edge, plus an innocuous one firing on the same
    ;; fact — chaining must finish the run, not abort at the bad conclusion
    (v/assert kb (vr/rule-sentence [(list subtypeMarker '?t)] (list 'genl '?t flightless))
              CxDerive {:direction :forward})
    (v/assert kb (vr/rule-sentence [(list subtypeMarker '?t)] (list noted '?t))
              CxDerive {:direction :forward})
    (v/assert kb (list subtypeMarker penguin) CxDerive)
    (let [vs (v/violations kb)]
      (testing "the conclusion is reported as inadmissible, with the cycle"
        (is (= [:not-stratified] (mapv :violation vs)))
        (is (seq (:cycle (:detail (first vs))))))
      (testing "and dropped: no sentex, and the closures never learned it"
        (is (empty? (v/sentexes-matching kb (list 'genl penguin flightless) '?ctx)))
        (is (not (tax/genl?-global (reasoning/taxonomy kb) penguin flightless))))
      (testing "chaining still ran to a fixpoint rather than aborting"
        (is (seq (v/sentexes-matching kb (list noted penguin) '?ctx)))))))

;; ---- the probe's memo is its own -----------------------------------------
;; The stratification probe asks its question of a detached copy of the taxonomy, and
;; the read memo is a **side atom** inside that value — so a copy that kept the
;; reference would let the probe write closures computed over the refused edge into
;; the live memo, stamped one gen ahead of the live relation.  Those entries answer
;; real reads the moment the live gen catches up.  The sequence below arranges exactly
;; that catch-up: a retraction bumps the gen without an intervening closure read (an
;; assert's own checks would recompute-and-clear on the way in; a retraction runs no
;; checks), so a shared memo would serve the refused edge as a real subtype.

(tu/deftest-kb a-refused-edge-does-not-poison-the-closure-memo-through-the-probe
  (tu/with-terms [base p flightless penguin sub super CxEdge]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxEdge})
    (let [h    (v/assert kb (list 'genl sub super) CxEdge)
          data (refusal kb (list 'genl penguin flightless) CxEdge)]
      (is (= :not-stratified (:type data)) "the probe ran and the edge was refused")
      (v/retract! kb h)
      (testing "the closure read after the gen catch-up never sees the refused edge"
        (is (not (contains? (tax/specs-global (reasoning/taxonomy kb) flightless) penguin)))
        (is (not (contains? (tax/genls-global (reasoning/taxonomy kb) penguin) flightless)))))))

(tu/deftest-kb a-derived-edge-that-closes-no-cycle-is-placed-normally
  ;; The control for the drop above: same derivation, same excepted rule in the KB,
  ;; an edge that crosses no negative edge — so it lands and reaches the closures.
  (tu/with-terms [base p flightless penguin unrelated subtypeMarker CxDerive]
    (cycle-shaped-rules! kb {:base base :p p :flightless flightless :penguin penguin
                             :ctx CxDerive})
    (v/assert kb (vr/rule-sentence [(list subtypeMarker '?t)] (list 'genl '?t unrelated))
              CxDerive {:direction :forward})
    (v/assert kb (list subtypeMarker penguin) CxDerive)
    (is (empty? (v/violations kb)))
    (is (seq (v/sentexes-matching kb (list 'genl penguin unrelated) '?ctx)))
    (is (tax/genl?-global (reasoning/taxonomy kb) penguin unrelated)
        "a derived edge reaches the taxonomy through integrate-transitive")))

;; ---- the consequent-var-pred rule and negation ---------------------------
;;
;; A rule concluding `(?p ?x)` could conclude *any*
;; predicate once `?p` binds, so the stratification check treats it as a concluder of the
;; predicate its NAF antecedent depends on — `rules/direct-concluders` folds in the
;; `p/var-consequent-key` catch-all.  Without that a one-rule negation cycle slips the entry point.

(tu/deftest-kb a-variable-consequent-rule-that-could-conclude-its-own-naf-is-refused
  (tu/with-terms [bar foo]
    (let [rule (vr/rule-sentence [(list bar '?p '?x) (list 'unknown (list foo '?x))]
                                 '(?p ?x))
          data (refusal kb rule 'CxNaturalWorld)]
      (is (= :not-stratified (:type data))
          "it could conclude foo while depending on foo's absence — an unstratified rule"))))

(tu/deftest-kb a-variable-consequent-rule-with-no-naf-is-accepted
  ;; the control: the refusal above is the cycle, not the mere presence of a variable
  ;; consequent — a var-consequent rule with a monotonic antecedent asserts cleanly.
  (tu/with-terms [holds]
    (let [h (v/assert kb (vr/rule-sentence [(list holds '?p '?x '?y)] '(?p ?x ?y))
                      'CxNaturalWorld {:direction :forward})]
      (is (some? h))
      (v/retract! kb h))))

;; The other two negative-antecedent forms fold into the same cycle: `check-stratified`
;; treats the exception's predicates and the aggregate bodies' predicates as negative
;; edges exactly as it does `unknown`, and a variable consequent concludes any of them.

(tu/deftest-kb a-variable-consequent-rule-excepted-on-its-own-conclusion-is-refused
  ;; the `exceptWhen` branch: the rule's exception reads `foo`, and its variable consequent
  ;; `(?p ?x)` could conclude `foo` — a one-rule negation cycle through the exception.
  (tu/with-terms [bar foo]
    (let [rule (list 'exceptWhen (list foo '?x)
                     (vr/rule-sentence [(list bar '?p '?x)] '(?p ?x)))
          data (refusal kb rule 'CxNaturalWorld)]
      (is (= :not-stratified (:type data))
          "it could conclude foo while excepted when foo holds — an unstratified rule"))))

(tu/deftest-kb a-variable-consequent-rule-aggregating-its-own-conclusion-is-refused
  ;; the aggregate branch: the rule counts over `foo`, and its variable consequent `(?p ?x)`
  ;; could conclude `foo` — the count has no settled answer, so the rule is refused.
  (tu/with-terms [bar foo]
    (let [rule (vr/rule-sentence [(list bar '?p '?x)
                                  (list 'agg/count '?n '?v (list foo '?v))]
                                 '(?p ?x))
          data (refusal kb rule 'CxNaturalWorld)]
      (is (= :not-stratified (:type data))
          "it could conclude foo while counting foo's extent — an unstratified rule"))))
