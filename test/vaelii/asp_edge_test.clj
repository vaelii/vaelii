;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-edge-test
  "`vaelii.impl.asp.edge`: the encoding over hand-built `Program`s (minimal defeat, caller
  priority, content-keyed ties), the readers' handling of a result that is not an answer,
  and, on a live KB, that installing `edge-solver` leaves a represented dilemma undecided
  under every arrival order.  Each test runs only with an ASP backend reachable, since
  without one `edge-solver` is `local-solver`.

  No `:each` fixture: the permutation test rebuilds a KB per ordering on the isolated
  space, so the KB tests take `tu/with-neutral-kb` inline."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.atoms :as atoms]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.config :as config]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- decide
  "Run `edge-solver` over a program built from `contested` / `nogoods` / `content`."
  [contested nogoods content]
  (solve-types/solve edge/edge-solver (solve/program contested nogoods content)))

(defn- sentences
  "What each of `handles` asserts, per `content`."
  [content handles]
  (into #{} (map #(get-in content [% :sentence])) handles))

(deftest the-program-text-does-not-depend-on-nogood-arrival-order
  (tu/with-requirement asp? "no ASP solver on this box"
    (let [content {1 {:sentence '(a X) :context 'C} 2 {:sentence '(not (a X)) :context 'C}
                   3 {:sentence '(b X) :context 'C} 4 {:sentence '(not (b X)) :context 'C}}
          n1      {:nogood #{1 2} :priority 0 :sentence '(contradicts A)}
          n2      {:nogood #{3 4} :priority 0 :sentence '(contradicts B)}
          text    (fn [ngs] (:aspif (edge/translate (solve/program #{1 2 3 4} ngs content))))]
      (is (= (text [n1 n2]) (text [n2 n1]))))))

(deftest a-cardinality-bound-renders-one-weight-constraint-and-prunes
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

(deftest a-weighted-bound-renders-each-member-at-its-weight-and-prunes-by-them
  (when asp?
    (let [content {1 {:sentence '(p a) :context 'C} 2 {:sentence '(p b) :context 'C}
                   3 {:sentence '(p c) :context 'C} 4 {:sentence '(p d) :context 'C}}
          card    {:op :at-most :k 5 :members #{1 2 3 4} :weights {1 4 2 3 3 2 4 0}
                   :hard true :priority 1 :sentence '(sumBound :at-most 5 (p ?x))}
          t       (edge/translate (solve/program #{1 2 3 4} [] content [card]))]
      (testing "one headless weight body of lower-bound k+1, a zero weight dropped"
        (is (re-find #"(?m)^1 0 0 1 6 3 1 4 2 3 3 2$" (:aspif t))))
      (testing "it prunes by weight: within 5 the most members kept is three (3 + 2 + 0)"
        (let [r (solver/solve t :label)]
          (is (= '#{(p b) (p c) (p d)} (sentences content (edge/kept-of t r)))))))))

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
  (tu/with-requirement asp? "no ASP solver on this box"
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
  ;; both nogoods can be satisfied, so priority shows as which member is given up
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
  ;; a soft nogood's violation atom fires only on the whole signed body
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
  ;; a fixed `:neg` member is present: hard, no `:- a1.`; soft, no penalty
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
  ;; the engine hands a default/default rebuttal to no solver, so belief reads as it does
  ;; with the stub
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
            nixon (tu/tmp-ind)]
        (v/set-solver kb edge/edge-solver)
        (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
        (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
        (v/assert kb (list quaker nixon)     'CxUniverse)
        (v/assert kb (list republican nixon) 'CxUniverse)
        (testing "both sides of the dilemma survive, at :default"
          (let [pos (v/handle-of kb (list pacifist nixon)             'CxUniverse)
                neg (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)]
            (is (true? (v/believed? kb pos)))
            (is (true? (v/believed? kb neg)))
            (is (= :default (v/defeat-class kb pos)))
            (is (= :default (v/defeat-class kb neg)))))
        (testing "the backend was never handed a program"
          (is (nil? (v/last-program kb))))
        (testing "and the pair is reported as a dilemma, not an unsatisfiable conflict"
          (is (= 1 (count (v/contradictions kb))))
          (is (empty? (v/conflicts kb))))))))

;; ---- 3. the order-independence invariant, with the ASP solver installed -

(defn- isolated-kb
  "A cleared KB on the suite's isolated space: this test rebuilds a KB per ordering, and
  `tu/fresh` would clear the scratch space another namespace's `:once` fixture holds."
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
        (tu/permutations ops)))

(deftest the-outcome-is-order-independent-with-the-asp-solver-installed
  ;; `order_independence_test`'s claim with a backend installed: one ordering that reached
  ;; the solver shows as a second distinct whole reading
  (tu/with-requirement asp? "no ASP solver on this box"
    (let [ops [#(v/assert % (tu/default-rule '[(quaker ?x)]     '(pacifist ?x))       'CxUniverse)
               #(v/assert % (tu/default-rule '[(republican ?x)] '(not (pacifist ?x))) 'CxUniverse)
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
  (when asp?
    (let [mk #(solve/program #{1 2}
                             [{:nogood #{1 2} :priority 0 :sentence 'X}]
                             {1 {:sentence '(a) :context 'C} 2 {:sentence '(b) :context 'C}})]
      (is (= (:aspif (edge/translate (mk))) (:aspif (edge/translate (mk))))))))

(deftest content-order-not-handle-order-drives-atom-allocation
  ;; labels embed the handle, so the text differs; the claim-to-atom map must not.  An
  ;; unsorted rule body renders a `:nogood` set in hash order, which this also catches.
  (tu/with-requirement asp? "no ASP solver on this box"
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
  (let [t (edge/translate (solve/program #{} [] {}))]
    (is (nil? (:aspif t)))
    (is (= {:defeat #{} :violated []}
           (solve-types/solve edge/edge-solver (solve/program #{} [] {}))))))

;; ---- a result that is not an answer ------------------------------------
;; A stub `solver/solve` answer in the backend's shape (docs/asp.md, "Refuse rather than
;; degrade, whenever a backend is present").

(def ^:private two-choices
  (solve/program #{1 2}
                 [{:nogood #{1 2} :priority 1 :sentence '(contradicts a b)}]
                 {1 {:sentence '(a) :context 'Cx} 2 {:sentence '(b) :context 'Cx}}))

;; the stub defeats {1,3} and ASP defeats {2}; on `two-choices` the two agree
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
  ;; the three ways a backend fails all read as one decided-nothing result
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

(deftest a-jvm-error-escapes-the-solve-and-an-interrupt-keeps-its-flag
  (with-redefs [solver/available? (constantly true)
                solver/solve      (fn [_ _] (throw (OutOfMemoryError. "heap")))]
    (is (thrown? OutOfMemoryError (solve-types/solve edge/edge-solver two-choices))))
  (with-redefs [solver/available? (constantly true)
                solver/solve      (fn [_ _] (throw (InterruptedException. "stop the settle")))]
    (let [r     (solve-types/solve edge/edge-solver two-choices)
          flag? (Thread/interrupted)]
      (is (empty? (:defeat r)) "nothing was decided")
      (is (instance? InterruptedException (ex-cause (:error r))))
      (is flag? "the interrupt flag is set again on the solving thread"))))

(deftest an-unsat-result-keeps-its-documented-reading
  (with-backend-answering {:status :unsat :atoms [] :cost nil :raw nil}
    (fn []
      (is (= (solve-types/solve solve/local-solver two-choices)
             (solve-types/solve edge/edge-solver two-choices)))
      (is (= #{} (edge/kept-of (edge/translate two-choices) {:status :unsat :atoms []})))
      (is (= [] (edge/enumerate-optima two-choices))))))

(deftest the-violated-reading-does-not-depend-on-nogood-arrival-order
  ;; two nogoods differing only in `:sentence`, which `translate`'s key omits; the hard
  ;; at-least-one forces the choice true, so all three soft nogoods are violated
  (let [force {:neg #{1} :hard true :sentence '(mustHold)}
        ng1   {:nogood #{1} :priority 0 :sentence '(contradicts aaa)}
        ng2   {:nogood #{1} :priority 0 :sentence '(contradicts bbb)}
        hi    {:nogood #{1} :priority 9 :sentence '(contradicts zzz)}
        prog (fn [ngs] (solve/program #{1} (conj (vec ngs) force)
                                      {1 {:sentence '(live) :context 'Cx}}))
        seen (fn [ngs] (mapv :sentence (:violated (solve-types/solve edge/edge-solver (prog ngs)))))]
    (tu/with-requirement asp? "no ASP solver on this box"
      (testing "the same three nogoods in either order read identically"
        (is (= (seen [ng1 ng2 hi]) (seen [hi ng2 ng1]))))
      (testing "highest caller priority first, then content — the Solver contract"
        (is (= '[(contradicts zzz) (contradicts aaa) (contradicts bbb)]
               (seen [ng2 ng1 hi])))))))

;; ---- what the time limit bounds ----------------------------------------

(defn- backend-solves
  "The solve modes `f` runs through the backend, in order, `classify-both` counted as its
  two enumerations."
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
  ;; the counts docs/asp.md, "The time limit", tabulates
  (when asp?
    (testing "one program, one solve"
      (is (= [:label] (backend-solves #(solve-types/solve edge/edge-solver two-choices))))
      (is (= [:all-optima] (backend-solves #(edge/enumerate-optima two-choices)))))
    (testing "classification is two — cautious, then brave"
      (is (= [:classify-true :classify-supportable]
             (backend-solves #(edge/classify-program two-choices)))))
    (let [labeling-solves
          (fn []
            (tu/with-neutral-kb [kb tu/fresh]
              (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
                    nixon (tu/tmp-ind)]
                (v/assert kb (tu/default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
                (v/assert kb (tu/default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
                (v/assert kb (list quaker nixon)     'CxUniverse)
                (v/assert kb (list republican nixon) 'CxUniverse)
                (backend-solves
                 #(v/assert kb (list 'do/labeling (tu/tmp-ctx "Labeling")) 'CxUniverse)))))]
      (testing "labeling a dilemma the solve-free bracket enumerates is none"
        (is (= [] (labeling-solves))))
      (testing "past the bracket's caps it is three: the classification's two, then the labeling"
        (with-redefs [config/classify-max-cluster-members (constantly 1)]
          (is (= [:classify-true :classify-supportable :label] (labeling-solves))))))))

(deftest an-irreducible-clash-still-bypasses-the-solver
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
