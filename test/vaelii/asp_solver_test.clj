;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-solver-test
  "The backend facade's routing policy, tested as a pure function — what AUTO does at the size
  cutoff, and what it does when only one backend can run at all — plus the typed
  refusal a missing or a wedged clasp binary earns, and what the in-process backend
  does when a native call fails.  No solve here needs libclingo or a real clasp: the
  policy fn takes its facts as arguments, the refusal tests point the binary var at a
  name nothing resolves or at a `/bin/sh` stub, and the clingo test stands in for the
  whole C API by redefining the one fn every native call goes through."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.asp.clasp :as clasp]
            [vaelii.impl.asp.clingo :as clingo]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.solve :as solve]
            [vaelii.test-util :as tu])
  (:import [com.sun.jna.ptr PointerByReference]
           [java.lang ProcessHandle]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [java.util.concurrent TimeUnit TimeoutException]))

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

(deftest a-jvm-error-loading-clingo-is-not-remembered-as-no-clingo
  ;; the verdict is process-wide, so the test puts back what it found
  (let [verdict @#'solver/clingo-verdict
        before  @verdict
        loaded  {:solve (fn [& _]) :classify-both (fn [& _]) :available? (constantly true)}]
    (try
      (reset! verdict :vaelii.impl.asp.solver/unknown)
      (with-redefs [solver/load-clingo (fn [] (throw (OutOfMemoryError. "heap")))]
        (is (nil? (#'solver/clingo-backend))))
      (with-redefs [solver/load-clingo (constantly loaded)]
        (is (= loaded (#'solver/clingo-backend)) "the next call loads it"))
      (testing "a verdict reached by any other throw is remembered"
        (reset! verdict :vaelii.impl.asp.solver/unknown)
        (with-redefs [solver/load-clingo (fn [] (throw (UnsatisfiedLinkError. "libclingo")))]
          (is (nil? (#'solver/clingo-backend))))
        (with-redefs [solver/load-clingo (constantly loaded)]
          (is (nil? (#'solver/clingo-backend)))))
      (finally (reset! verdict before)))))

(deftest a-missing-clasp-binary-is-a-typed-refusal
  ;; the binary is exec'd directly — no shell, so no exit-127 convention — and the
  ;; IOException that throws comes back as the `:type` callers discriminate on
  (binding [clasp/*clasp-binary* "vaelii-no-such-binary"]
    (is (false? (clasp/available?)))
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (clasp/solve "asp 1 0 0\n0\n" :label)))]
      (is (= :solver-unavailable (:type (ex-data e)))))))

(deftest the-clasp-executable-is-read-from-the-property-then-the-environment
  ;; the property names the executable; a blank one is unset, so the environment
  ;; variable or the default `clasp` answers as it would with no property set
  (let [read  #(#'clasp/configured-binary)
        prior (System/getProperty "vaelii.clasp.bin")]
    (try
      (System/clearProperty "vaelii.clasp.bin")
      (let [unset (read)]
        (System/setProperty "vaelii.clasp.bin" " /opt/clingo/bin/clingo ")
        (is (= "/opt/clingo/bin/clingo" (read)))
        (System/setProperty "vaelii.clasp.bin" "  ")
        (is (= unset (read))))
      (finally (if prior (System/setProperty "vaelii.clasp.bin" prior)
                   (System/clearProperty "vaelii.clasp.bin"))))))

(defn- exits-within?
  "Has process `pid` exited, or does it exit within `ms`?  A killed grandchild is
  reaped by init rather than by the JVM, so its exit is waited for, not sampled."
  [pid ms]
  (if-let [^ProcessHandle h (.orElse (ProcessHandle/of pid) nil)]
    (try (.get (.onExit h) ms TimeUnit/MILLISECONDS) true
         (catch TimeoutException _ false))
    true))

(defn- await-lines
  "Wait up to `ms` for file `f` to hold `n` newline-terminated lines."
  [^java.io.File f n ms]
  (let [end (+ (System/currentTimeMillis) ms)]
    (loop []
      (let [s (when (.exists f) (slurp f))]
        (when-not (or (and s (str/ends-with? s "\n") (= n (count (str/split-lines s))))
                      (> (System/currentTimeMillis) end))
          (Thread/sleep 10)
          (recur))))))

(deftest a-clasp-past-its-deadline-is-killed-with-its-children-and-reads-as-unavailable
  ;; The stub ignores `--time-limit` and sleeps in a child, as a wedged clasp would.  The
  ;; 500 ms deadline starts once the stub has written both pids, and the solve's future is
  ;; bounded at 15 s, so a missing watchdog reads as `::hung` instead of stalling 30 s.
  (tu/with-requirement (not tu/windows?) "the stub is a #!/bin/sh script, which Windows does not exec"
    (let [dir  (.toFile (Files/createTempDirectory "vaelii-clasp-stub" (make-array FileAttribute 0)))
          pids (io/file dir "pids")
          stub (io/file dir "clasp")]
      (try
        (spit stub (str "#!/bin/sh\necho $$ > '" pids "'\nsleep 30 &\necho $! >> '" pids "'\nwait\n"))
        (.setExecutable stub true)
        (with-redefs [clasp/deadline-ms (fn [_] (await-lines pids 2 5000) 500)]
          (binding [clasp/*clasp-binary* (str stub)]
            (let [r (deref (future (try (clasp/solve "asp 1 0 0\n0\n" :label)
                                        (catch clojure.lang.ExceptionInfo e (ex-data e))))
                           15000 ::hung)]
              (is (= :solver-unavailable (:type r)))
              (is (= [] (remove #(exits-within? % 5000)
                                (map parse-long (str/split-lines (slurp pids)))))
                  "the stub and its child are gone"))))
        (finally
          (run! #(.delete ^java.io.File %) (reverse (file-seq dir))))))))

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
  ;; under an ambient *print-length* two sentences sharing a prefix would elide to one
  ;; key, and the order would fall back to arrival
  (let [program {:content {1 {:sentence '(likes Ann Bo Cy Dee) :context 'C}
                           2 {:sentence '(likes Ann Bo Cy Eve) :context 'C}}}]
    (binding [*print-length* 2 *print-level* 1]
      (is (not= (solve/content-key program 1) (solve/content-key program 2))))))
