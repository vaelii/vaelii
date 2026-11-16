;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ns-timings-test
  "`scripts/lib/ns-timings.sh`'s rerun of the slow namespaces, three runs each in one JVM,
  the prediction that decides whether it runs, and the `VAELII_TEST_NS_REPEAT` hook.

  The library runs from a copy in a scratch directory, and a `lein` script there stands
  in for Leiningen on PATH.  It logs each call, runs each namespace as often as the hook
  asks, and its first run sleeps for the build a JVM makes once.  No real `lein` runs."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :as t :refer [deftest is]]
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
