;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-edge-test
  "The ASP edge solver (`vaelii.impl.asp.edge`) behind the `solve-types/Solver` protocol.

  Two halves.  The first drives `edge-solver` directly with hand-built `Program`s
  — no KB, no store — because the translation is a pure function of the program
  and that is the level the encoding is worth pinning at: minimal defeat, caller
  priority respected, and above all a tie broken the *same way* regardless of the
  order the knowledge arrived.  This half is the backend's real coverage and is
  unaffected by anything below it.

  The second installs it on a live KB through `set-solver`.  The engine routes no
  default/default rebuttal to any solver,
  because a `P`/`¬P` pair at `:default` is a **represented dilemma** rather than a tie
  to be broken (docs/exceptions.md, \"What surfaces where\").  So a Nixon diamond in a
  KB does not settle to one side, and the KB-level property worth pinning is the
  negative one: installing a real ASP backend does not change belief, is never
  consulted, and cannot quietly re-introduce arbitration.  Arbitration remains the
  right answer for nogoods that are *not* plain rebuttals, which is why the protocol and
  its encoding are still tested at full strength above.

  Everything here is skipped when no ASP backend is reachable: `edge-solver`
  deliberately falls back to `local-solver` in that case, so running these without
  clingo or clasp would silently assert the stub's behaviour instead of the
  solver's and prove nothing.

  No `:each` fixture.  The permutation tests below build a fresh KB
  per ordering, and `tu/fresh` clears the scratch databases — which would pull the
  ground out from under a namespace-wide fixture KB and fail teardown against a
  baseline that no longer exists.  The KB tests therefore take the inline
  `tu/with-neutral-kb` route `test_util` documents for a namespace whose tests need
  different baselines."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.atoms :as atoms]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

(defn- decide
  "Run `edge-solver` over a program built from `contested` / `nogoods` / `content`."
  [contested nogoods content]
  (solve-types/solve edge/edge-solver (solve/program contested nogoods content)))

(defn- sentences
  "What each of `handles` asserts, per `content` — so an assertion can name the
  *claim* that lost rather than the handle, which is the whole point of the
  content keying."
  [content handles]
  (into #{} (map #(get-in content [% :sentence])) handles))

(deftest the-program-text-does-not-depend-on-nogood-arrival-order
  ;; translate sorts the nogoods by their members' content keys before anything is
  ;; emitted: settle hands them in arrival order, and every emission — violation
  ;; atoms, constraints, minimize, show — walks that seq, so an unsorted one
  ;; rendered two logically identical programs as different ASPIF text
  (when asp?
    (let [content {1 {:sentence '(a X) :context 'C} 2 {:sentence '(not (a X)) :context 'C}
                   3 {:sentence '(b X) :context 'C} 4 {:sentence '(not (b X)) :context 'C}}
          n1      {:nogood #{1 2} :priority 0 :sentence '(contradicts A)}
          n2      {:nogood #{3 4} :priority 0 :sentence '(contradicts B)}
          text    (fn [ngs] (:aspif (edge/translate (solve/program #{1 2 3 4} ngs content))))]
      (is (= (text [n1 n2]) (text [n2 n1]))))))

(deftest a-cardinality-bound-renders-one-weight-constraint-and-prunes
  ;; A `:cardinalities` entry is ONE weight-body statement, not the C(n, k+1) subset
  ;; nogoods a hand-written encoding needs — and it prunes the models like a hard nogood.
  (when asp?
    (let [content {1 {:sentence '(p a) :context 'C} 2 {:sentence '(p b) :context 'C}
                   3 {:sentence '(p c) :context 'C} 4 {:sentence '(p d) :context 'C}}
          card    (fn [members] {:op :at-most :k 2 :members members :hard true :priority 1
                                 :sentence '(cardinalityBound :at-most 2 (p ?x))})
          prog    (fn [members] (solve/program #{1 2 3 4} [] content [(card members)]))
          text    (fn [members] (:aspif (edge/translate (prog members))))]
      (testing "the bound is one headless weight body of lower-bound k+1 over the members"
        (is (re-find #"(?m)^1 0 0 1 3 4 " (text #{1 2 3 4}))))
      (testing "the program text does not depend on the member set's order"
        (is (= (text #{1 2 3 4}) (text #{4 3 2 1}))))
      (testing "it prunes: keep-belief wants all four, the hard cap allows two"
        (let [t (edge/translate (prog #{1 2 3 4}))
              r (solver/solve t :label)]
          (is (contains? #{:optimum :sat} (:status r)))
          (is (= 2 (count (edge/kept-of t r)))))))))

;; ---- 1. the encoding, driven directly ----------------------------------

(deftest a-tie-defeats-exactly-one-side
  (when asp?
    (let [content {1 {:sentence '(pacifist Nixon) :context 'C}
                   2 {:sentence '(not (pacifist Nixon)) :context 'C}}
          r (decide #{1 2} [{:nogood #{1 2} :priority 0 :sentence '(contradicts X)}] content)]
      (testing "one of the two contested defaults gives way, not both"
        (is (= 1 (count (:defeat r)))))
      (testing "and nothing is left unsatisfiable"
        (is (empty? (:violated r)))))))

(deftest the-tie-break-does-not-depend-on-assertion-order
  ;; The engine-wide invariant (docs/nmtms.md): handles are allocated in assertion
  ;; order, so if the outcome tracked handles the Nixon diamond would elect
  ;; whichever side was typed first.  Same two claims, handles swapped — the same
  ;; *claim* must lose both times.
  (when asp?
    (let [ng [{:nogood #{1 2} :priority 0 :sentence '(contradicts X)}]
          c1 {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}}
          c2 {1 {:sentence '(b) :context 'C} 2 {:sentence '(a) :context 'C}}
          r1 (decide #{1 2} ng c1)
          r2 (decide #{1 2} ng c2)]
      (testing "each run defeats one side"
        (is (= 1 (count (:defeat r1))))
        (is (= 1 (count (:defeat r2)))))
      (testing "and it is the same sentence both times, though the handle differs"
        (is (= (sentences c1 (:defeat r1))
               (sentences c2 (:defeat r2))))))))

(deftest defeat-is-minimal-across-overlapping-nogoods
  ;; 1-2 and 2-3 both contested.  Defeating the shared member satisfies both, so a
  ;; solver that optimizes globally finds the one-atom cover; defeating 1 and 3
  ;; would also satisfy both but costs twice as much belief.
  (when asp?
    (let [content {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}
                   3 {:sentence '(c) :context 'C}}
          r (decide #{1 2 3}
                    [{:nogood #{1 2} :priority 0 :sentence 'A}
                     {:nogood #{2 3} :priority 0 :sentence 'B}]
                    content)]
      (testing "the shared member is the single casualty"
        (is (= #{2} (:defeat r))))
      (is (empty? (:violated r))))))

(deftest an-uncontested-program-defeats-nothing
  (when asp?
    (let [content {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}}
          r (decide #{1 2} [] content)]
      (testing "no contradictions, no losses"
        (is (empty? (:defeat r)))
        (is (empty? (:violated r)))))))

(deftest a-higher-priority-nogood-is-satisfied-first
  ;; Both nogoods can be satisfied here, so priority shows up as *which* member is
  ;; sacrificed: giving up 2 settles both, and the high-priority pair keeps its
  ;; other member.
  (when asp?
    (let [content {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}
                   3 {:sentence '(c) :context 'C}}
          r (decide #{1 2 3}
                    [{:nogood #{1 2} :priority 10 :sentence 'HIGH}
                     {:nogood #{2 3} :priority 0  :sentence 'LOW}]
                    content)]
      (is (= 1 (count (:defeat r))))
      (is (empty? (:violated r))))))

;; ---- 2. installed on a live KB -----------------------------------------

(deftest a-neg-nogood-is-an-at-least-one
  ;; `:neg` members are forbidden to be *absent* together.  Soft, its witness fires
  ;; only on the whole signed body — never as an unconditional fact — so a satisfied
  ;; at-least-one steers nothing and reports nothing.
  (when asp?
    (let [content {1 {:sentence '(col N K1) :context 'C}
                   2 {:sentence '(col N K2) :context 'C}}]
      (testing "a satisfied soft at-least-one reports no violation and defeats nothing"
        (let [r (decide #{1 2} [{:neg #{1 2} :priority 0 :sentence '(atleastone)}] content)]
          (is (empty? (:violated r)))
          (is (empty? (:defeat r)))))
      (testing "against a hard exclusion, the at-least-one is met by keeping exactly one"
        (let [r (decide #{1 2} [{:nogood #{1 2} :hard true :sentence '(excl)}
                                {:neg #{1 2} :priority 0 :sentence '(atleastone)}]
                        content)]
          (is (= 1 (count (:defeat r))) "one gives way to the exclusion")
          (is (empty? (:violated r)) "and the at-least-one is met, not violated"))))))

(deftest a-fixed-neg-member-makes-the-nogood-vacuous
  ;; A `:neg` member outside the contested set is assumed true — present — so the
  ;; at-least-one holds no matter what is decided.  Hard, the constraint must not
  ;; tighten into `:- a1.`; soft, it must not penalize anything.
  (when asp?
    (let [content {1 {:sentence '(col N K1) :context 'C}}]
      (testing "hard"
        (let [r (decide #{1} [{:nogood #{1} :neg #{2} :hard true :sentence '(excl)}]
                        content)]
          (is (empty? (:defeat r)))
          (is (empty? (:violated r)))))
      (testing "soft"
        (let [r (decide #{1} [{:neg #{1 2} :priority 0 :sentence '(atleastone)}] content)]
          (is (empty? (:defeat r)))
          (is (empty? (:violated r))))))))

(deftest the-asp-solver-does-not-decide-a-nixon-diamond
  ;; The backend above can decide this shape and would, given the program.  It is
  ;; never given the program: the engine reports a default/default rebuttal as a
  ;; dilemma instead.  Installing a real solver must therefore leave the KB reading
  ;; exactly as it does with the built-in stub — otherwise the semantics of a KB would
  ;; depend on which backend happened to be reachable, which is the one thing an
  ;; opt-in backend must never do.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
            nixon (tu/tmp-ind)]
        (v/set-solver kb edge/edge-solver)
        (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
        (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
        (v/assert kb (list quaker nixon)     'CxUniverse)
        (v/assert kb (list republican nixon) 'CxUniverse)
        (testing "both sides of the dilemma survive, at :default"
          (let [pos (v/handle-of kb (list pacifist nixon)             'CxUniverse)
                neg (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)]
            (is (true? (v/in? kb pos)))
            (is (true? (v/in? kb neg)))
            (is (= :default (v/defeat-class kb pos)))
            (is (= :default (v/defeat-class kb neg)))))
        (testing "the backend was never handed a program"
          (is (nil? (v/last-program kb))))
        (testing "and the pair is indistinguishable from a dilemma, not an unsatisfiable conflict"
          (is (= 1 (count (v/contradictions kb))))
          (is (empty? (v/conflicts kb))))))))

;; ---- 3. the order-independence invariant, with the ASP solver installed -

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

(defn- isolated-kb
  "A cleared KB on the suite's isolated database pair rather than the shared
  scratch space.

  Deliberate: this test rebuilds a KB once per ordering, and `tu/fresh` flushes the
  scratch space every time.  Run inside the full suite that would repeatedly wipe the
  KB a *different* namespace is holding open through a `:once` fixture — the tests
  pass alone and fail together, which is the worst way to find out.  `test-util`
  owns the isolated space for exactly this."
  []
  (tu/isolated-fresh))

(defn- outcomes-with-edge-solver
  "Every ordering of `ops`, each on a fresh KB with `edge-solver` installed, read
  through `observe`.  Returns the set of distinct outcomes."
  [ops observe]
  (into #{}
        (map (fn [order]
               (let [kb (isolated-kb)]
                 (v/set-solver kb edge/edge-solver)
                 (doseq [op order] (op kb))
                 (observe kb))))
        (permutations ops)))

(deftest the-outcome-is-order-independent-with-the-asp-solver-installed
  ;; The invariant `order_independence_test` pins for the stub, re-run with the real
  ;; backend installed.  The engine routes this shape to no solver, so what the
  ;; permutation catches is not "does the ASP encoding pick a stable winner" but "does
  ;; the presence of a backend perturb the outcome under *any* ordering" — a single
  ;; ordering that reached the solver would show up here as a second distinct outcome,
  ;; which is exactly the regression worth a 24-way sweep.
  ;;
  ;; The strength of the assertion matters as much as before.  Comparing whole
  ;; readings rather than a per-ordering boolean is what makes a one-off flip visible;
  ;; "some outcome is stable" would pass while the engine was order-dependent.
  (when asp?
    (let [ops [#(v/assert % (default-rule '[(quaker ?x)]     '(pacifist ?x))       'CxUniverse)
               #(v/assert % (default-rule '[(republican ?x)] '(not (pacifist ?x))) 'CxUniverse)
               #(v/assert % '(quaker Nixon)     'CxUniverse)
               #(v/assert % '(republican Nixon) 'CxUniverse)]
          observe (fn [kb]
                    {:pacifist       (boolean (seq (v/sentexes-matching kb '(pacifist Nixon) 'CxUniverse)))
                     :not-pacifist   (boolean (seq (v/sentexes-matching kb '(not (pacifist Nixon)) 'CxUniverse)))
                     :contradictions (count (v/contradictions kb))
                     :conflicts      (count (v/conflicts kb))
                     :solved?        (some? (v/last-program kb))})
          os (outcomes-with-edge-solver ops observe)]
      (testing "all 24 orderings read identically"
        (is (= 1 (count os))
            (str "order-dependent with the ASP solver installed: " (pr-str os))))
      (testing "and the agreed reading is a coexisting dilemma the backend never saw"
        (let [r (first os)]
          (is (true? (:pacifist r)))
          (is (true? (:not-pacifist r)))
          (is (= 1 (:contradictions r)))
          (is (zero? (:conflicts r)))
          (is (false? (:solved? r)))))
      (tu/clear-kb! (tu/isolated-test-kb)))))

(deftest translation-is-deterministic
  ;; Same program twice must render byte-identical ASPIF: if atom allocation drifted
  ;; the text would too, and a solver's arbitrary choice among optima could drift
  ;; with it even when the encoding is otherwise correct.
  (when asp?
    (let [mk #(solve/program #{1 2}
                             [{:nogood #{1 2} :priority 0 :sentence 'X}]
                             {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}})]
      (is (= (:aspif (edge/translate (mk))) (:aspif (edge/translate (mk))))))))

(deftest content-order-not-handle-order-drives-atom-allocation
  ;; The same two claims under swapped handles.  The rendered text cannot be equal —
  ;; labels embed the handle, so `s1`/`s2` necessarily swap — but the *claim to atom*
  ;; mapping must not: whichever handle carries `(a)` has to receive the same atom id
  ;; both times, or the program the solver optimizes depends on assertion order even
  ;; when the encoding is otherwise sound.
  ;;
  ;; This is also what catches an unsorted rule body: `:nogood` is a set, so a body
  ;; built by plain iteration renders in hash order rather than content order.
  (when asp?
    (let [mk (fn [content]
               (edge/translate
                (solve/program #{1 2} [{:nogood #{1 2} :priority 0 :sentence 'X}] content)))
          t1 (mk {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}})
          t2 (mk {1 {:sentence '(b) :context 'C} 2 {:sentence '(a) :context 'C}})
          atom-for (fn [t handle] (atoms/atom-of-sentex (:table t) handle))]
      (testing "the claim (a) gets the same atom whichever handle carries it"
        (is (= (atom-for t1 1) (atom-for t2 2))))
      (testing "and so does (b)"
        (is (= (atom-for t1 2) (atom-for t2 1))))
      (testing "the two programs differ only where labels carry the handle"
        (is (= (remove #(str/starts-with? % "4 ") (str/split-lines (:aspif t1)))
               (remove #(str/starts-with? % "4 ") (str/split-lines (:aspif t2)))))))))

(deftest an-empty-program-needs-no-solver
  ;; Nothing contested and nothing to satisfy: `translate` yields no ASPIF at all,
  ;; and the solver is never invoked.
  (let [t (edge/translate (solve/program #{} [] {}))]
    (is (nil? (:aspif t)))
    (is (= {:defeat #{} :violated []}
           (solve-types/solve edge/edge-solver (solve/program #{} [] {}))))))

;; ---- a result that is not an answer ------------------------------------
;;
;; A backend that was interrupted (the time limit, a signal) hands back no witness.
;; Every reader maps an atom's absence to *defeated* / *not kept*, so read as an
;; answer an empty result defeats every contested assumption — the exact opposite
;; of "decide nothing".  No backend is needed to pin this: `solver/solve` is the
;; protocol, and a stub answer in its shape is what arrives either way.

(def ^:private two-choices
  (solve/program #{1 2}
                 [{:nogood #{1 2} :priority 1 :sentence '(contradicts a b)}]
                 {1 {:sentence '(a) :context 'Cx} 2 {:sentence '(b) :context 'Cx}}))

;; Two nogoods sharing a member, with the handles arranged so the stub's greedy
;; per-nogood choice and the global optimum land on *different* sides: the stub
;; defeats {1,3} and ASP defeats {2}.  This is the structure that makes degradation
;; visible — on `two-choices` above the two solvers happen to agree.
(def ^:private shared-member
  (solve/program #{1 2 3}
                 [{:nogood #{1 2} :priority 0 :sentence '(contradicts c a)}
                  {:nogood #{2 3} :priority 0 :sentence '(contradicts a b)}]
                 {1 {:sentence '(c) :context 'Cx}
                  2 {:sentence '(a) :context 'Cx}
                  3 {:sentence '(b) :context 'Cx}}))

(defn- with-backend-answering
  "Run `f` with a backend present whose every solve returns `result`."
  [result f]
  (with-redefs [solver/available?    (constantly true)
                solver/solve         (fn [_ _] result)
                solver/classify-both (fn [_] {:cautious result :brave result})]
    (f)))

(deftest an-interrupted-solve-is-not-read-as-defeat-everything
  (doseq [status [:interrupted :unknown]]
    (with-backend-answering {:status status :atoms [] :cost nil :raw nil}
      (fn []
        (testing (str "edge-solver on " status " decides nothing at all")
          (let [r (solve-types/solve edge/edge-solver two-choices)]
            (is (empty? (:defeat r)) "not one side, not both — none")
            (is (= :solver-failed (:type (ex-data (:error r)))))
            (is (= status (:status (ex-data (:error r)))))))
        (testing (str "and the imperative readers refuse " status " as :solver-failed")
          (doseq [f [#(edge/kept-of (edge/translate two-choices)
                                    {:status status :atoms []})
                     #(edge/enumerate-optima two-choices)
                     #(edge/classify-program two-choices)]]
            (let [e (is (thrown? clojure.lang.ExceptionInfo (f)))]
              (is (= :solver-failed (:type (ex-data e))))
              (is (= status (:status (ex-data e)))))))))))

(deftest belief-does-not-depend-on-whether-the-solve-finished
  ;; The reason `edge-solver` refuses instead of degrading whenever a backend is
  ;; present.  The stub and ASP disagree on this program, so falling back would make
  ;; the *answer* — not merely the latency — a function of the wall clock: a settle
  ;; whose round 1 timed out and whose round 2 did not would end at a belief set
  ;; neither solver would produce, on knowledge that never changed.
  (when asp?
    (let [decided (solve-types/solve edge/edge-solver shared-member)
          stub    (solve-types/solve solve/local-solver shared-member)]
      (testing "the two solvers really do disagree here, or this test proves nothing"
        (is (= #{2} (:defeat decided)) "ASP spends one defeat on the shared member")
        (is (= #{1 3} (:defeat stub)) "the stub spends two"))
      (testing "an interrupted labeling solve yields the stub's answer from neither"
        (let [real solver/solve
              r (with-redefs [solver/solve (fn [aspif mode]
                                             (if (= mode :label)
                                               {:status :interrupted :atoms [] :cost nil :raw nil}
                                               (real aspif mode)))]
                  (solve-types/solve edge/edge-solver shared-member))]
          (is (empty? (:defeat r)))
          (is (not= (:defeat stub) (:defeat r))))))))

(deftest a-decided-nothing-result-is-distinguishable-from-keeping-everything
  ;; An empty `:defeat` is otherwise a perfectly good answer — *nothing had to give
  ;; way* — so a caller that materializes what a solve kept cannot tell the two apart
  ;; from the defeat set alone.  `:error` is the bit that tells them apart, and
  ;; `asp.label` raises it rather than committing a world nobody computed.
  (when asp?
    (testing "a program with nothing to satisfy really does defeat nothing, and errs not"
      (let [r (solve-types/solve edge/edge-solver
                                 (solve/program #{1 2} []
                                                {1 {:sentence '(a) :context 'Cx}
                                                 2 {:sentence '(b) :context 'Cx}}))]
        (is (empty? (:defeat r)))
        (is (nil? (:error r)))))
    (testing "an interrupted solve defeats nothing either, and says why"
      (with-backend-answering {:status :interrupted :atoms [] :cost nil :raw nil}
        (fn []
          (let [r (solve-types/solve edge/edge-solver shared-member)]
            (is (empty? (:defeat r)))
            (is (= :solver-failed (:type (ex-data (:error r)))))))))))

(deftest a-backend-that-throws-does-not-unwind-the-arbitration
  ;; `resolve-contradictions` reaches the solver after an earlier round has already
  ;; defeated things, so an exception escaping the protocol leaves a half-arbitrated KB:
  ;; round 1's defeats landed, `:conflicts` stale, `settle-finish` never reached.  The
  ;; three currencies a backend fails in all read as one decided-nothing result.
  (doseq [[what thrown expected-type]
          [["clingo's chk!"      (ex-info "clingo solve failed: out of memory"
                                          {:type :solver-failed :op "solve"})   :solver-failed]
           ["a missing clasp"    (ex-info "clasp binary not found: clasp"
                                          {:type :solver-unavailable :binary "clasp"}) :solver-unavailable]
           ["a JNA link Error"   (UnsatisfiedLinkError. "clingo_control_new")   :solver-failed]]]
    (with-redefs [solver/available? (constantly true)
                  solver/solve      (fn [_ _] (throw thrown))]
      (testing (str what " comes back as a result, not a throw")
        (let [r (solve-types/solve edge/edge-solver two-choices)]
          (is (empty? (:defeat r)) "nothing was decided")
          (is (= expected-type (:type (ex-data (:error r)))))
          (is (identical? thrown (ex-cause (:error r))) "the original failure is the cause"))))))

(deftest an-unsat-result-keeps-its-documented-reading
  ;; `:unsat` is a definite answer — no model — and each reader has its own word for
  ;; it: the edge solver degrades, a labeling keeps nothing, an enumeration is empty.
  (with-backend-answering {:status :unsat :atoms [] :cost nil :raw nil}
    (fn []
      (is (= (solve-types/solve solve/local-solver two-choices)
             (solve-types/solve edge/edge-solver two-choices)))
      (is (= #{} (edge/kept-of (edge/translate two-choices) {:status :unsat :atoms []})))
      (is (= [] (edge/enumerate-optima two-choices))))))

(deftest the-violated-reading-does-not-depend-on-nogood-arrival-order
  ;; Two constraints over the same members at the same priority — a shape two constraint
  ;; rules grounding to the same choice heads produce — differ only in their `:sentence`,
  ;; which `translate`'s nogood key omits.  A stable sort then leaves the tie to arrival
  ;; order, and the reading permutes with it.  Belief never does; the report is what the
  ;; caller sees, and it owes the same content order everything else here owes.
  ;;
  ;; A hard at-least-one forces the single choice true, so all three soft nogoods
  ;; forbidding it are violated at once — `:violated` comes back empty for anything the
  ;; engine itself builds (every contradiction it sends has a contested member, and
  ;; defeating that member satisfies it), so a caller's own program is what reaches it.
  (let [force {:neg #{1} :hard true :sentence '(mustHold)}
        ng1   {:nogood #{1} :priority 0 :sentence '(contradicts aaa)}
        ng2   {:nogood #{1} :priority 0 :sentence '(contradicts bbb)}
        hi    {:nogood #{1} :priority 9 :sentence '(contradicts zzz)}
        prog (fn [ngs] (solve/program #{1} (conj (vec ngs) force)
                                      {1 {:sentence '(live) :context 'Cx}}))
        seen (fn [ngs] (mapv :sentence (:violated (solve-types/solve edge/edge-solver (prog ngs)))))]
    (when asp?
      (testing "the same three nogoods in either order read identically"
        (is (= (seen [ng1 ng2 hi]) (seen [hi ng2 ng1]))))
      (testing "highest caller priority first, then content — the Solver contract"
        (is (= '[(contradicts zzz) (contradicts aaa) (contradicts bbb)]
               (seen [ng2 ng1 hi])))))))

;; ---- what the time limit bounds ----------------------------------------

(defn- backend-solves
  "The solve modes `f` runs through the backend, in order.  `classify-both` is two
  enumerations over one control — one `control_new`, two searches — so it counts as the
  two solves it is, which is what the budget is spent on."
  [f]
  (let [seen  (atom [])
        solve solver/solve
        both  solver/classify-both]
    (with-redefs [solver/solve         (fn [a m] (swap! seen conj m) (solve a m))
                  solver/classify-both (fn [a]
                                         (swap! seen into [:classify-true :classify-supportable])
                                         (both a))]
      (f))
    @seen))

(deftest the-time-limit-bounds-one-solve-and-an-operation-makes-several
  ;; `VAELII_ASP_TIME_LIMIT` is a per-solve budget, and a solve runs on the single
  ;; writer — so what an operation actually holds the writer for is the budget times
  ;; the number of solves it makes.  Measured at a 1-second budget on a program that
  ;; finishes under neither: one solve returns after ~1015 ms and `classify-both` after
  ;; 2049 ms, both of them correctly cancelled on time.
  ;;
  ;; docs/asp.md tabulates the multipliers.  This is what keeps the table honest: a
  ;; second solve added to an operation is a doubling of the writer's exposure, and it
  ;; should not be possible to add one without saying so.
  (when asp?
    (testing "one program, one solve"
      (is (= [:label] (backend-solves #(solve-types/solve edge/edge-solver two-choices))))
      (is (= [:all-optima] (backend-solves #(edge/enumerate-optima two-choices)))))
    (testing "classification is two — cautious, then brave"
      (is (= [:classify-true :classify-supportable]
             (backend-solves #(edge/classify-program two-choices)))))
    (testing "labeling a dilemma is three: the classification's two, then the labeling"
      (tu/with-neutral-kb [kb tu/fresh]
        (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
              nixon (tu/tmp-ind)]
          (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
          (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
          (v/assert kb (list quaker nixon)     'CxUniverse)
          (v/assert kb (list republican nixon) 'CxUniverse)
          (is (= [:classify-true :classify-supportable :label]
                 (backend-solves
                  #(v/assert kb (list 'do/labeling (tu/tmp-ctx "Labeling")) 'CxUniverse)))))))))

(deftest an-irreducible-clash-still-bypasses-the-solver
  ;; Two monotonic claims that contradict cannot be arbitrated by defeating one —
  ;; `settle` classifies that as hard and reports it directly, so installing an ASP
  ;; backend must not change the outcome.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [happy (tu/tmp-pred) tom (tu/tmp-ind)]
        (v/set-solver kb edge/edge-solver)
        (v/assert kb (list happy tom) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list 'not (list happy tom)) 'CxUniverse {:strength :monotonic})
        (testing "the clash is reported, once"
          (is (= 1 (count (v/conflicts kb)))))
        (testing "and neither known-true belief was dropped to manufacture consistency"
          (is (seq (v/sentexes-matching kb (list happy tom) 'CxUniverse)))
          (is (seq (v/sentexes-matching kb (list 'not (list happy tom)) 'CxUniverse))))))))
