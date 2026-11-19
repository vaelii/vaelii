;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ci-weights-test
  "`scripts/ci-weights.sh`'s --check and --list forms, and --accept with --out, over
  timing files written to a scratch tree that holds a copy of the script."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.test-util :as tu]))

(def ^:private baseline
  {"a-test" 100, "b-test" 40, "c-test" 20, "d-test" 10, "e-test" 1,
   "f-test" 100, "g-test" 40, "h-test" 20, "i-test" 10, "j-test" 1})

(def ^:private shards [["a-test" "b-test" "c-test" "d-test" "e-test"]
                       ["f-test" "g-test" "h-test" "i-test" "j-test"]])

(defn- tsv [m] (str/join (for [[n w] (sort m)] (str n "\t" w "\n"))))

(defn- check
  "Run the `form` (\"--check\", \"--list\" or \"--out\") of a copy of the script over
  the two `shards`, each namespace taking `(secs ns weight)` seconds, plus the `extra`
  rows in shard 1.  `accept`'s `:new` rows are the copy's committed weights and its
  `:old` rows the file `--accept` names.  Answer the exit, stdout and the rows --out
  wrote."
  ([form secs extra] (check form secs extra nil))
  ([form secs extra {:keys [old new]}]
   (tu/with-tmp
     (fn [root]
       (let [rows  (fn [nss] (str/join (for [n nss] (format "%s\t%.2f\n" n (double (secs n (baseline n)))))))
             ;; --out writes a row for each namespace whose file is under test/
             files (cond-> (into {"scripts/ci-weights.sh" (slurp "scripts/ci-weights.sh")
                                  "baseline.tsv"          (str "# weights\n" (tsv baseline))
                                  "t/1-of-2.tsv"          (str (rows (first shards)) extra)
                                  "t/2-of-2.tsv"          (rows (second shards))}
                                 (for [n (keys baseline)] [(str "test/" (str/replace n "-" "_") ".clj") ""]))
                     new (assoc "scripts/ci-test-weights-disk.tsv" (tsv new) "old.tsv" (tsv old)))
             path  #(tu/posix-path (io/file root %))]
         (doseq [[f text] files]
           (io/make-parents (io/file root f))
           (spit (io/file root f) text))
         (let [r (apply shell/sh tu/bash (path "scripts/ci-weights.sh") "--from" (path "t") "--leg" "disk"
                        (concat (if (= form "--out") ["--out" (path "out.tsv")] [form (path "baseline.tsv")])
                                (when new ["--accept" (path "old.tsv")])))
               out (io/file root "out.tsv")]
           (cond-> (select-keys r [:exit :out])
             (.exists out) (assoc :rows (into {} (for [line (str/split-lines (slurp out))
                                                       :when (not (str/starts-with? line "#"))
                                                       :let [[k v] (str/split line #"\t")]]
                                                   [k (parse-double v)]))))))))))

(def ^:private shard-1? (set (first shards)))

(deftest the-check-fails-a-namespace-or-a-leg-that-runner-speed-does-not-account-for
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees no file this JVM writes"
    (doseq [[label secs extra want named]
            [["one shard at 0.6x and the other at 1.4x"
              (fn [n w] (* w (if (shard-1? n) 0.6 1.4))) nil 0 nil]
             ["one namespace at 3x its shard's speed and 80 s over"
              (fn [n w] (if (= n "b-test") (* 3 w) w)) nil 1 "b-test"]
             ["a shard's first namespace at 3x and 200 s over, which pays the JVM's start-up"
              (fn [n w] (if (= n "a-test") (* 3 w) w)) nil 0 nil]
             ["one namespace at 3x its shard's speed and 20 s over"
              (fn [n w] (if (= n "d-test") (* 3 w) w)) nil 0 nil]
             ["every namespace at 1.4x"
              (fn [_ w] (* 1.4 w)) nil 3 nil]
             ["a namespace the baseline does not name, at 500 s"
              (fn [_ w] w) "new-test\t500\n" 0 nil]]]
      (testing label
        (let [{:keys [exit out]} (check "--check" secs extra)
              listed (check "--list" secs extra)]
          (is (= want exit) out)
          (is (= (some? named) (boolean (re-find #"(?m)^\| " out))) out)
          (when named (is (str/includes? out (str "| " named " |")) out))
          (is (= {:exit 0 :out (if named (str named "\n") "")} listed)))))))

(deftest the-check-refuses-a-timing-set-missing-a-shard-and-the-list-reads-one-shard
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees no file this JVM writes"
    (tu/with-tmp
      (fn [root]
        (spit (io/file root "baseline.tsv") "a-test\t10\nb-test\t10\nc-test\t10\n")
        (.mkdir (io/file root "t"))
        (spit (io/file root "t" "1-of-2.tsv") "b-test\t10\na-test\t100\nc-test\t10\n")
        (let [run (fn [form] (shell/sh tu/bash "scripts/ci-weights.sh" "--from" (tu/posix-path (io/file root "t"))
                                       "--leg" "disk" form (tu/posix-path (io/file root "baseline.tsv"))))
              {:keys [exit err]} (run "--check")]
          (is (= 1 exit))
          (is (str/includes? err "does not hold one <shard>-of-<total>.tsv per shard"))
          (is (= {:exit 0 :out "a-test\n"} (select-keys (run "--list") [:exit :out]))))))))

(deftest a-row-the-change-sets-in-the-committed-weights-raises-that-namespaces-figure
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees no file this JVM writes"
    ;; b-test is set higher, c-test lower, and d-test holds the same stale figure on both sides
    (let [accept {:old {"b-test" 40, "c-test" 20, "d-test" 999}
                  :new {"b-test" 150, "c-test" 5, "d-test" 999}}
          secs   (fn [n w] (if (= n "b-test") (* 3 w) w))
          plain  (check "--check" secs nil)
          {:keys [exit out]} (check "--check" secs nil accept)]
      (is (= 1 (:exit plain)) "without --accept, b-test fails the check")
      (is (str/includes? (:out plain) "replace the row of each namespace in scripts/ci-test-weights-disk.tsv with its row below")
          (:out plain))
      (is (str/includes? (:out plain) "```\nb-test\t120.00\n```") "the row to paste, at the shard's speed of 1")
      (is (= 0 exit) out)
      (is (str/includes? out "This change raises 1 baseline figure(s) in scripts/ci-test-weights-disk.tsv") out)
      (is (= {:exit 0 :out ""} (check "--list" secs nil accept)))
      (let [{:keys [exit rows]} (check "--out" secs nil accept)]
        (is (= 0 exit))
        (is (= {"b-test" 150.0 "c-test" 20.0 "d-test" 10.0} (select-keys rows ["b-test" "c-test" "d-test"]))
            "a set row raises its measured figure, and a lowered or stale row leaves it")))))
