;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-solver-test
  "The backend facade's routing policy, pinned pure — what AUTO does at the size
  cutoff, and what it does when only one backend can run at all — plus the typed
  refusal a missing clasp binary earns, and what the in-process backend does when a
  native call fails.  No solve here needs libclingo or a real clasp: the policy fn
  takes its facts as arguments, the refusal test points the binary var at a name
  nothing resolves, and the clingo test stands in for the whole C API by redefining
  the one fn every native call goes through."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.asp.clasp :as clasp]
            [vaelii.impl.asp.clingo :as clingo]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.solve :as solve])
  (:import [com.sun.jna.ptr PointerByReference]))

(def ^:private choose #'solver/choose-backend)

(deftest auto-routes-on-size-and-degrades-on-availability
  (testing "small prefers in-process, large prefers the fork"
    (is (= :clingo (choose nil true 100 3000 true)))
    (is (= :clasp  (choose nil true 9000 3000 true))))
  (testing "past the cutoff clasp is preferred only when it can actually run"
    (is (= :clingo (choose nil true 9000 3000 false))
        "a loadable clingo on a large program is a cost regression; routing to a
        binary the machine does not have is a refusal available? promised away"))
  (testing "no clingo means clasp at any size"
    (is (= :clasp (choose nil false 100 3000 true)))
    (is (= :clasp (choose nil false 9000 3000 false))))
  (testing "explicit config is honored verbatim, clingo falling back when unloadable"
    (is (= :clasp  (choose :clasp true 100 3000 true)))
    (is (= :clingo (choose :clingo true 9000 3000 true)))
    (is (= :clasp  (choose :clingo false 100 3000 true)))))

(deftest a-missing-clasp-binary-is-a-typed-refusal
  ;; `shell/sh` execs directly — no shell, so no exit-127 convention — and the
  ;; IOException it throws comes back as the `:type` callers discriminate on
  (binding [clasp/*clasp-binary* "vaelii-no-such-binary"]
    (is (false? (clasp/available?)))
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (clasp/solve "asp 1 0 0\n0\n" :label)))]
      (is (= :solver-unavailable (:type (ex-data e)))))))

(deftest a-failing-handle-close-does-not-replace-the-failure-that-caused-it
  ;; `drain-handle` closes the solve handle in a `finally`, because freeing a control
  ;; with one still open is undefined behaviour.  A `finally` that throws *replaces*
  ;; the exception on its way out, and the one it would replace is the informative
  ;; one: `chk!` names the native call that returned zero in `:op`, and nothing else
  ;; records which it was.  Both halves fail here — the drain and the close — and the
  ;; drain's failure is the one that must come out.
  (let [drain #'clingo/drain-handle
        seen  (atom [])]
    (with-redefs [clingo/ci (fn [nm & _]
                              (swap! seen conj nm)
                              (if (= nm "clingo_solve_handle_close")
                                (throw (UnsatisfiedLinkError. "clingo_solve_handle_close"))
                                0))]                        ; 0 ⇒ chk! refuses
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (drain (PointerByReference.) 0 :optimal (constantly []))))]
        (testing "the drain's own failure survives, naming the call that failed"
          (is (= :solver-failed (:type (ex-data e))))
          (is (= "resume" (:op (ex-data e)))))))
    (testing "and the close was still attempted, which is what the finally is for"
      (is (some #{"clingo_solve_handle_close"} @seen)))))

(deftest a-drain-keeps-only-the-models-its-mode-reads
  ;; A search streams: a 400-node colouring at a two-second budget yields 618 models to
  ;; a `:label` solve that reads one and 184 to a cautious enumeration that reads the
  ;; last, every one of them a map of freshly marshaled atom-label strings.  What
  ;; retention may not do is change the answer, so the two facts `finalize` needs from
  ;; the models it never sees — the optimum cost, and whether any model came back
  ;; optimality-proven — are folded in as they pass rather than read off what was kept.
  (let [keep' #'clingo/keep-model
        m     (fn [atoms cost opt?] {:atoms atoms :cost cost :optimal? opt?})
        fold  (fn [retain ms]
                (reduce #(keep' %1 %2 retain) {:models [] :optimum nil :any-optimal? false} ms))
        ;; costs improving, then a plateau at the optimum
        stream [(m ["a"] [3] false) (m ["b"] [2] false) (m ["c"] [1] true) (m ["d"] [1] true)]]
    (testing ":optimal keeps the plateau at the best cost and drops what it beat"
      (let [r (fold :optimal stream)]
        (is (= [["c"] ["d"]] (mapv :atoms (:models r))))
        (is (= [1] (:optimum r)))
        (is (true? (:any-optimal? r)))))
    (testing ":last keeps one — the one a classify enumeration converges to"
      (let [r (fold :last stream)]
        (is (= [["d"]] (mapv :atoms (:models r))))
        (is (= [1] (:optimum r)) "and the optimum a dropped model set still stands")))
    (testing "a proven flag on a dropped model still counts, so the status cannot slip"
      (is (true? (:any-optimal? (fold :last [(m ["a"] [1] true) (m ["b"] [1] false)])))))
    (testing "no minimize statement: every cost empty, nothing beats anything"
      (let [r (fold :optimal [(m ["a"] [] false) (m ["b"] [] false)])]
        (is (= 2 (count (:models r))))
        (is (nil? (:optimum r)))))))

(deftest a-solve-with-no-objective-reads-one-model-of-a-program-with-many
  ;; `:label` streams every improving model so a cancelled optimization keeps its best.
  ;; A program with no objective has nothing to improve, and the same flags enumerate
  ;; every model: a 10k-node 3-coloring's solve ran to the time limit and parsed
  ;; gigabytes of witnesses.  `:sat` stops at the first, and so does a `:label` solve
  ;; handed a program with no minimize statement, whichever caller built it.  Twelve
  ;; unconstrained choices have 4,096 models.
  (let [ids     (set (range 1 13))
        content (into {} (map (fn [i] [i {:sentence (list 'chosen i) :context 'C}])) ids)
        bare    (edge/translate (solve/program ids [] content)
                                {:tiebreak? false :keep-belief? false})
        kept    (edge/translate (solve/program ids [] content) {:tiebreak? false})]
    (when (clasp/available?)
      (testing "clasp"
        (doseq [mode [:sat :label]]
          (let [r (clasp/solve (:aspif bare) mode)]
            (is (= :sat (:status r)) (str mode))
            (is (= 1 (count (-> r :raw :Call first :Witnesses))) (str mode))))
        (testing "a program with an objective still solves to its optimum"
          (let [r (clasp/solve (:aspif kept) :label)]
            (is (= :optimum (:status r)))
            (is (= 12 (count (:atoms r))) "every unconstrained choice is kept")))))
    (when (clingo/available?)
      (testing "clingo"
        (doseq [mode [:sat :label]]
          (let [r (clingo/solve bare mode)]
            (is (= :sat (:status r)) (str mode))
            (is (= 1 (count (-> r :raw :models))) (str mode))))
        (testing "a program with an objective still solves to its optimum"
          (let [r (clingo/solve kept :label)]
            ;; clingo flags no model proven under `--opt-mode=opt`, so a finished
            ;; optimization reads `:sat` here where clasp says `:optimum`; `edge` reads
            ;; both as an answer set
            (is (contains? #{:optimum :sat} (:status r)))
            (is (= 12 (count (:atoms r))))))))))

(deftest content-key-survives-an-ambient-print-length
  ;; the key decides which side of a tie gives way; under a REPL's *print-length*
  ;; two sentences sharing a prefix elided to one key, and the arbitration fell
  ;; back to arrival order — the exact dependence the key exists to remove
  (let [program {:content {1 {:sentence '(likes Ann Bo Cy Dee) :context 'C}
                           2 {:sentence '(likes Ann Bo Cy Eve) :context 'C}}}]
    (binding [*print-length* 2 *print-level* 1]
      (is (not= (solve/content-key program 1) (solve/content-key program 2))))))
