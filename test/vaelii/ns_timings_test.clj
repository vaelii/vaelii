;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ns-timings-test
  "`scripts/lib/ns-timings.sh`'s rerun of a slow namespace, which runs the namespace that
  builds the shared test dumps before it, and the prediction that decides whether it runs.

  The library runs from a copy in a scratch directory, and a `lein` script there stands
  in for Leiningen on PATH.  It prints a `lein test` line per namespace and sleeps for
  each, and the first namespace of a call also sleeps for the build a JVM makes once.
  No KB is opened and no real `lein` runs."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [vaelii.test-util :as tu]))

(def ^:private dumps-first "vaelii.shared-dumps-test")

(def ^:private fake-lein
  "Each namespace sleeps 0.1 s, and the first of a call 1.5 s more, the once-per-JVM
  build.  The output ends as `lein test`'s does."
  (str "#!/usr/bin/env bash\n"
       "shift\n"
       "build=1.5\n"
       "for ns in \"$@\"; do echo \"lein test $ns\"; sleep 0.1; sleep \"$build\"; build=0; done\n"
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
  (into {} (for [line (str/split-lines tsv) :let [[k v] (str/split line #"\t")]]
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

(deftest the-rerun-prediction-counts-the-dump-builds-once-per-rerun
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees no file this JVM writes"
    (let [fits (fn [slow]
                 (in-tree (str "printf '" dumps-first "\\t70\\nt.a-test\\t10\\nt.b-test\\t10\\n' > b.tsv\n"
                               "ns_timings_rerun_fits b.tsv '" dumps-first " t.a-test t.b-test' " slow "\n")))]
      ;; the shard is 90 s; one rerun is 70 + 10 = 80 s, two are 160 s
      (is (zero? (:exit (fits "t.a-test"))))
      (let [{:keys [exit out]} (fits "t.a-test t.b-test")]
        (is (= 1 exit))
        (is (str/includes? out "the rerun (160 s) would take longer than the shard (90 s)") out)))))
