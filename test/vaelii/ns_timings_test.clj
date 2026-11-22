;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ns-timings-test
  "`scripts/lib/ns-timings.sh`'s rerun of the slow namespaces, three runs each in one JVM,
  the prediction that decides whether it runs, and the `VAELII_TEST_NS_REPEAT` hook; and
  `scripts/lib/failed-selectors.sh`'s stage, which the CI step pipes the run through next.

  The libraries run from copies in a scratch directory.  A `lein` script there stands in
  for Leiningen on PATH, and a bash function for `lein test` before the stage.  The script
  logs each call, runs each namespace as often as the hook asks, and its first run sleeps
  for the build a JVM makes once.  No real `lein`, and nothing under the stage, runs a JVM."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :as t :refer [deftest is testing]]
            [vaelii.ns-counts :as nsc]
            [vaelii.test-util :as tu]))

(def ^:private dumps-first "vaelii.shared-dumps-test")

(def ^:private fake-lein
  "Each run of a namespace sleeps 0.1 s, and the call's first run 1.5 s more, the
  once-per-JVM build.  Each call appends its namespaces to `calls`.  The output ends as
  `lein test`'s does."
  (str "#!/usr/bin/env bash\n"
       "shift\n"
       "echo \"$*\" >> calls\n"
       "build=1.5\n"
       "for ns in \"$@\"; do for _ in $(seq \"${VAELII_TEST_NS_REPEAT:-1}\"); do\n"
       "  echo \"lein test $ns\"; sleep 0.1; sleep \"$build\"; build=0\n"
       "done; done\n"
       "echo 'Ran 1 tests containing 1 assertions.'\n"
       "echo '0 failures, 0 errors.'\n"))

(defn- in-tree
  "Run bash `script` after sourcing the library, in a scratch tree holding the library,
  the stand-in `lein` and the dumps namespace's file, and answer the shell result."
  [script]
  (tu/with-tmp
    (fn [root]
      (let [dir (io/file root)]
        (doseq [[path text] {"scripts/lib/ns-timings.sh"           (slurp "scripts/lib/ns-timings.sh")
                             "bin/lein"                            fake-lein
                             "test/vaelii/shared_dumps_test.clj"   (str "(ns " dumps-first ")\n")}]
          (io/make-parents (io/file dir path))
          (spit (io/file dir path) text))
        (.setExecutable (io/file dir "bin/lein") true)
        (let [env (into {} (System/getenv))]
          (shell/sh tu/bash "-c" (str ". scripts/lib/ns-timings.sh\n" script)
                    :dir dir
                    :env (assoc env "PATH" (str (tu/posix-path (io/file dir "bin")) ":" (get env "PATH")))))))))

(defn- rows [tsv]
  (into {} (for [line (str/split-lines tsv) :when (str/includes? line "\t")
                 :let [[k v] (str/split line #"\t")]]
             [k (parse-double v)])))

(deftest a-rerun-is-not-billed-the-dump-builds
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees no file this JVM writes"
    (let [{:keys [exit out err]}
          (in-tree (str "printf '" dumps-first "\\t9.00\\nt.slow-test\\t5.00\\n' > t.tsv\n"
                        "ns_timings_rerun t.tsv t.slow-test > /dev/null\n"
                        "cat t.tsv\n"))
          r (rows out)]
      (is (zero? exit) err)
      (is (< (r "t.slow-test") 1.0) "the rerun's row is the namespace's own 0.1 s, not the 1.5 s build")
      (is (= 9.0 (r dumps-first)) "the dumps namespace's first-pass row is left as it was"))))

(deftest a-rerun-runs-every-slow-namespace-three-times-in-one-jvm
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees no file this JVM writes"
    (let [{:keys [exit out err]}
          (in-tree (str "printf 't.a-test\\t5.00\\nt.b-test\\t5.00\\nt.c-test\\t5.00\\n' > t.tsv\n"
                        "ns_timings_rerun t.tsv t.a-test t.b-test | grep -c '^lein test '\n"
                        "cat calls t.tsv\n"))
          [runs & more] (str/split-lines out)
          r (rows out)]
      (is (zero? exit) err)
      (is (= "6" runs) "each of the two namespaces runs three times")
      (is (= "t.a-test t.b-test" (first more)) "in one call to lein, so one JVM")
      (is (every? #(< (r %) 1.0) ["t.a-test" "t.b-test"]) "and each row takes its smallest time")
      (is (= 5.0 (r "t.c-test")) "a namespace the rerun does not name keeps its row"))))

(deftest the-rerun-prediction-counts-each-slow-namespace-three-times-and-the-dump-builds-once
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees no file this JVM writes"
    (let [fits (fn [slow]
                 (in-tree (str "printf '" dumps-first "\\t70\\nt.a-test\\t10\\nt.b-test\\t10\\n"
                               "t.c-test\\t30\\n' > b.tsv\n"
                               "ns_timings_rerun_fits b.tsv 150 " slow "\n")))]
      ;; the job has 150 s left; a and b rerun in 3 × 20 + 70 = 130 s, c in 3 × 30 + 70 = 160 s
      (is (zero? (:exit (fits "t.a-test t.b-test"))))
      (let [{:keys [exit out]} (fits "t.c-test")]
        (is (= 1 exit))
        (is (str/includes? out "the rerun (160 s) would not finish in the 150 s the job has left") out)))))

(deftest the-repeat-hook-runs-a-namespace-n-times-and-sums-its-counters
  ;; `report` is bound so the probe prints no `lein test` line into this run's log.  The
  ;; finally restores the run's own hook, which `VAELII_TEST_NS_REPEAT` may have set.
  (let [probe   (create-ns (gensym "vaelii.repeat-probe"))
        ran     (atom 0)
        root    @#'t/test-ns
        repeats @#'nsc/repeats
        before  @repeats]
    (intern probe (with-meta 'probe {:test #(do (swap! ran inc) (t/is true))}) nil)
    (try
      (nsc/install-repeat! 2)
      (nsc/install-repeat! 3)
      (let [c (binding [t/report #(when (= :pass (:type %)) (t/inc-report-counter :pass))]
                (t/test-ns probe))]
        (is (= 3 @ran) "the namespace's test runs three times, under one wrapper")
        (is (= {:test 3 :pass 3} (select-keys c [:test :pass])) "and the counters sum the runs"))
      (finally
        (alter-var-root #'t/test-ns (constantly root))
        (reset! repeats before)
        (remove-ns (ns-name probe))))))

;; ---- annotate_failed_selectors -------------------------------------------
;;
;; Here rather than in a namespace of their own, so the stage adds no namespace to any
;; CI shard.  `produce` stands in for `lein test`; nothing under these tests runs a JVM.

(def ^:private selector-libs
  ["scripts/lib/failed-selectors.sh" "scripts/lib/ns-timings.sh"
   "scripts/lib/suite-marks.sh" "scripts/lib/revision.sh"])

(defn- annotate
  "Run bash `script` in a scratch tree holding copies of `selector-libs` and the test file
  of namespace `a.x-test`, after `prelude`, the two libraries the CI step sources, and
  `produce CODE LINE…`, which prints each LINE and returns CODE as `lein test` would.  The
  default prelude is the CI step's: `bash -e` and `set -o pipefail`.  A library the
  checkout lacks is not copied, so its absence fails the assertions, not this helper."
  ([script] (annotate "set -eo pipefail" script))
  ([prelude script]
   (tu/with-tmp
     (fn [root]
       (let [dir (io/file root)]
         (doseq [path selector-libs :when (.exists (io/file path))]
           (io/make-parents (io/file dir path))
           (io/copy (io/file path) (io/file dir path)))
         (io/make-parents (io/file dir "test/a/x_test.clj"))
         (spit (io/file dir "test/a/x_test.clj") "(ns a.x-test)\n")
         (shell/sh tu/bash "-c" (str prelude "\n"
                                     ". scripts/lib/ns-timings.sh\n"
                                     ". scripts/lib/failed-selectors.sh\n"
                                     "produce() { local c=$1; shift; printf '%s\\n' \"$@\"; return \"$c\"; }\n"
                                     script)
                   :dir dir))))))

(def ^:private stage
  "annotate_failed_selectors memory 2/4 target/ci/test-memory-shard-2.log test-memory-shard-2-logs")

(def ^:private where
  "target/ci/test-memory-shard-2.log (artifact test-memory-shard-2-logs).")

(defn- error-line
  "The annotation for failing test `id`; namespace `a.x-test` has a file in the tree."
  [id]
  (str "::error " (when (str/starts-with? id "a.x-test/") "file=test/a/x_test.clj,")
       "title=" id " fails (memory%2C shard 2/4)::"
       id " fails in the memory leg, shard 2/4. Its output is in " where))

(defn- warning-line [msg]
  (str "::warning title=Unannotated failures (memory%2C shard 2/4)::" msg
       " Every failure is in " where))

(defn- sh-quote [s] (str "'" (str/replace s "'" "'\\''") "'"))
(defn- produce [code lines] (str "produce " code " " (str/join " " (map sh-quote lines))))
(defn- text [lines] (apply str (map #(str % "\n") lines)))

(defmacro ^:private with-bash [& body]
  `(tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees no file this JVM writes"
     ~@body))

(deftest a-green-run-passes-through-the-annotations-unchanged-and-unannotated
  (with-bash
    (let [run ["lein test a.x-test" "" "Testing a.x-test" "Ran 2 tests containing 5 assertions."
               "0 failures, 0 errors."]
          {:keys [exit out err]} (annotate (str (produce 0 run) " | " stage))]
      (is (zero? exit) err)
      (is (= (text run) out) "every line is forwarded as it came")
      (is (= "" err) "and nothing is annotated"))))

(deftest each-failing-test-is-annotated-once-by-name-and-never-with-its-report
  (with-bash
    (let [run ["lein test a.x-test" ""
               "lein test :only a.x-test/one" ""
               "FAIL in (one) (x_test.clj:3)"
               "expected: (= token \"s3cr3t-value\")"
               "lein test :only a.x-test/one"
               "lein test :only a.x-test/two"
               "lein test b.y-test"
               "lein test :only b.y-test/three?"
               "lein test :only a.x-test/one"
               "Ran 4 tests containing 9 assertions." "4 failures, 0 errors."]
          {:keys [exit out err]} (annotate (str (produce 1 run) " | " stage))]
      (is (= 1 exit) "the run's own status")
      (is (= (text run) out))
      (is (= (text (map error-line ["a.x-test/one" "a.x-test/two" "b.y-test/three?"])) err)
          "one annotation per test, in the order they failed, a file only where the tree has one")
      (is (not (str/includes? err "s3cr3t")) "the failure report stays in the log"))))

(deftest an-annotation-is-written-while-the-run-is-still-going
  (with-bash
    (let [{:keys [exit out err]}
          (annotate (str "p() { printf 'lein test :only a.x-test/one\\n'\n"
                         "  for _ in $(seq 100); do\n"
                         "    if grep -q '^::error' err.txt 2>/dev/null; then echo seen; return 0; fi\n"
                         "    sleep 0.05\n"
                         "  done\n"
                         "  echo unseen; }\n"
                         "p | " stage " 2> err.txt\n"))]
      (is (zero? exit) err)
      (is (= "lein test :only a.x-test/one\nseen\n" out)
          "the producer saw the annotation before it finished"))))

(deftest past-the-cap-one-line-counts-the-rest-and-the-run-is-read-to-its-end
  (with-bash
    (testing "a cap of 2"
      (let [run (concat ["lein test a.x-test"]
                        (map #(str "lein test :only a.x-test/t" %) [1 2 3 1 4 5])
                        ["Ran 5 tests containing 5 assertions." "5 failures, 0 errors." "after the summary"])
            {:keys [exit out err]} (annotate (str "FAILED_SELECTOR_ANNOTATIONS_MAX=2\n"
                                                  (produce 7 run) " | " stage))]
        (is (= 7 exit) "the run's own status")
        (is (= (text run) out) "every line, the ones past the cap included")
        (is (= (text [(error-line "a.x-test/t1") (error-line "a.x-test/t2")
                      (warning-line "3 more failing tests past the cap of 2 are not annotated.")])
               err))))
    (testing "the default cap is 10, GitHub's limit of error annotations for one step"
      (doseq [[n more] [[12 "2 more failing tests past the cap of 10 are not annotated."]
                        [11 "1 more failing test past the cap of 10 is not annotated."]]]
        (let [run (map #(str "lein test :only a.x-test/t" %) (range n))
              {:keys [exit err]} (annotate (str (produce 1 run) " | " stage))
              lines (str/split-lines err)]
          (is (= 1 exit))
          (is (= 11 (count lines)))
          (is (= (map #(error-line (str "a.x-test/t" %)) (range 10)) (butlast lines)))
          (is (= (warning-line more) (last lines))))))))

(deftest a-marker-that-names-no-test-is-forwarded-and-counted-but-never-echoed
  (with-bash
    (let [id200 (str "a.x-test/" (apply str (repeat 191 \v)))
          bad   ["lein test :only a.x-test/one::error::pwned"
                 "lein test :only a.x-test/two%0A::error file=evil::pwned"
                 "lein test :only a.x-test/has space"
                 "lein test :only a.x-test"
                 "lein test :only /one"
                 "lein test :only a.x-test/"
                 "lein test :only a.x-test/three,title=pwned"
                 (str "lein test :only " id200 "v")
                 "lein test :only a.x-test/four\r"
                 "lein test :only "]
          run   (concat ["lein test a.x-test"] bad
                        ["  lein test :only a.x-test/five" (str "lein test :only " id200)])
          {:keys [exit out err]} (annotate (str (produce 1 run) " | " stage))]
      (is (= 1 exit))
      (is (= (text run) out) "every line is forwarded byte for byte, the carriage return too")
      (is (= (text [(error-line id200)
                    (warning-line (str "10 failure markers that do not name one namespace/test"
                                       " are not annotated."))])
             err)
          "a 200-character name is annotated, a 201-character one is not, an indented line is no marker")
      (is (not-any? #(str/includes? err %) ["pwned" "evil"]))
      (is (every? #(< (count %) 1024) (str/split-lines err)) "each annotation is bounded"))))

(deftest every-field-of-an-annotation-is-validated-and-escaped
  (with-bash
    (let [{:keys [exit out err]}
          (annotate (str "gh_escape_property $'a%b\\r\\nc:d,e'; echo\n"
                         "gh_escape_data $'a%b\\r\\nc:d,e'; echo\n"))]
      (is (zero? exit) err)
      (is (= "a%25b%0D%0Ac%3Ad%2Ce\na%25b%0D%0Ac:d,e\n" out)))
    (let [{:keys [exit err]}
          (annotate (str (produce 1 ["lein test :only a.x-test/one"])
                         " | annotate_failed_selectors 'a,b::c' 1:2 $'x\\ny' 'a%b' > /dev/null"))]
      (is (= 1 exit))
      (is (= (str "::error file=test/a/x_test.clj,title=a.x-test/one fails ((invalid)%2C shard (invalid))"
                  "::a.x-test/one fails in the (invalid) leg, shard (invalid)."
                  " Its output is in (invalid) (artifact (invalid)).\n")
             err)
          "an argument that is not what CI passes is replaced, not quoted"))))

(deftest the-pipeline-status-is-the-one-it-was-without-the-stage
  (with-bash
    (testing "through the CI step's own pipe, the status is the run's and the log is whole"
      (doseq [code [0 1 7]]
        (let [run ["lein test a.x-test" "lein test :only a.x-test/one" "Ran 1 tests containing 1 assertions."
                   "1 failures, 0 errors."]
              {:keys [exit out]}
              (annotate (str "printf '%s\\n' " (str/join " " (map sh-quote run)) " > want.txt\n"
                             "trap 's=$?; cmp -s log.txt want.txt || exit 99; exit $s' EXIT\n"
                             (produce code run) " | ns_timings t.tsv | " stage " | tee log.txt"))]
          (is (= code exit) (str "a run that exits " code))
          (is (= (text run) out)))))
    (testing "a closed annotation sink fails nothing"
      (let [{:keys [exit out]} (annotate (str (produce 0 ["lein test :only a.x-test/one"]) " | " stage " 2>&-"))]
        (is (zero? exit))
        (is (= "lein test :only a.x-test/one\n" out))))
    (testing "a consumer that fails or stops reading fails the pipe exactly as it did"
      (let [big (str "big() { local c=$1 i; printf 'lein test :only a.x-test/one\\n'\n"
                     "  for ((i = 0; i < 20000; i++)); do printf 'line %d\\n' \"$i\"; done\n"
                     "  printf 'lein test :only a.x-test/two\\n'; return \"$c\"; }\n")]
        (doseq [errexit ["set -e" "set +e"]
                pipe    ["" "trap '' PIPE"]
                consumer ["exit 3" "head -n 1 > /dev/null" "tee /nonexistent-dir/log > /dev/null"]
                code    [0 1]]
          (let [prelude (str errexit "\nset -o pipefail\n" pipe)
                before  (annotate prelude (str big "big " code " | ns_timings t.tsv | " consumer))
                after   (annotate prelude (str big "big " code " | ns_timings t.tsv | " stage " | " consumer))]
            (is (= (:exit before) (:exit after))
                (pr-str [errexit pipe consumer code]))))))))

(deftest the-annotated-tests-are-the-ones-suite-marks-reads-off-the-log
  (with-bash
    (let [run ["lein test a.x-test" "lein test :only a.x-test/one" "lein test :only a.x-test/one"
               "lein test b.y-test" "lein test :only b.y-test/odd?!*<>=+-name"
               "lein test :only a.x-test/two" "2 failures, 0 errors."]
          {:keys [exit out err]}
          (annotate "set +e"
                    (str "SUITE_PROGRESS=lines . scripts/lib/suite-marks.sh\n"
                         (produce 1 run) " | " stage " > run.log 2> ann.txt\n"
                         "failing_tests run.log; echo --; cat ann.txt\n"))
          [listed annotations] (str/split out #"--\n")]
      (is (zero? exit) err)
      (is (= (sort (str/split-lines listed))
             (sort (map #(second (re-find #"title=(\S+) fails" %)) (str/split-lines (or annotations ""))))))
      (is (= ["a.x-test/one" "a.x-test/two" "b.y-test/odd?!*<>=+-name"] (str/split-lines listed))))))
