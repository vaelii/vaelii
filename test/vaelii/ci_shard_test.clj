;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ci-shard-test
  "`scripts/ci-shard.sh`'s order inside a shard: policy 1 of `scripts/ci-test-history.tsv`.

  The history moves namespaces within a shard and never between shards, and a history
  the script cannot trust is ignored whole, for the order the script printed before it
  read one.  The script runs from a copy in a scratch directory over a tree of empty
  `*_test.clj` files and weights and histories written here, so the namespaces, their
  costs and their failure counts are the test's own.  No KB is opened and no `lein`
  runs; the last test reads the checked-in files, still only through the script."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(def ^:private weights
  "Seconds per namespace.  `t.g-test` has none and is weighted at the mean, 12.67."
  {"t.a-test" 10, "t.b-test" 10, "t.c-test" 30, "t.d-test" 5, "t.e-test" 20, "t.f-test" 1})

(def ^:private namespaces (conj (vec (sort (keys weights))) "t.g-test"))

(def ^:private header "# policy: 1\n# status: current\n")

(def ^:private history
  "Ties on count (a, b, f), on count and weight (a, b), and a namespace the tree has not
  got (zz)."
  (str "# a comment\n" header "\n"
       "t.d-test\t3\nt.b-test\t1\nt.a-test\t1\nt.f-test\t1\nt.zz-test\t9\nt.c-test\t0\n"))

(defn- with-tree
  "Call `f` with a scratch directory holding a copy of `scripts/ci-shard.sh`, a test
  tree of `namespaces` and `w.tsv` of `weights`."
  [f]
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees neither this checkout nor the scratch directory"
    (let [dir (.toFile (Files/createTempDirectory "vaelii-ci-shard-" (into-array FileAttribute [])))]
      (try (io/make-parents (io/file dir "scripts/ci-shard.sh"))
           (io/copy (io/file "scripts/ci-shard.sh") (io/file dir "scripts/ci-shard.sh"))
           (doseq [ns namespaces
                   :let [p (str "test/" (-> ns (str/replace "." "/") (str/replace "-" "_")) ".clj")]]
             (io/make-parents (io/file dir p))
             (spit (io/file dir p) (str "(ns " ns ")\n")))
           (spit (io/file dir "w.tsv")
                 (str "# weights\n" (str/join (map (fn [[k v]] (str k "\t" v "\n")) weights))))
           (f dir)
           (finally (doseq [^File x (reverse (file-seq dir))] (.delete x)))))))

(defn- shard
  "`{:nss [...] :err \"...\"}` from shard `n` of `of` over the tree in `dir`, with
  `hist` as the history file (nil: no history file at all)."
  [^File dir hist n of]
  (let [h (io/file dir "h.tsv")]
    (.delete h)
    (when hist (spit h hist))
    (let [{:keys [exit out err]} (shell/sh tu/bash (tu/posix-path (io/file dir "scripts/ci-shard.sh"))
                                           (str n) (str of) "--weights" "w.tsv" "--history" "h.tsv"
                                           :dir dir)]
      (is (zero? exit) err)
      {:nss (vec (remove str/blank? (str/split-lines out))) :err err})))

(defn- nss [dir hist n of] (:nss (shard dir hist n of)))

(def ^:private alternating
  "One shard, no usable history: heaviest first is c e g a b d f, printed lightest,
  heaviest, second lightest, ..."
  ["t.f-test" "t.c-test" "t.d-test" "t.e-test" "t.b-test" "t.g-test" "t.a-test"])

(deftest a-shard-runs-recurring-failures-first-then-the-costly-then-by-name
  (with-tree
    (fn [dir]
      (let [{:keys [nss err]} (shard dir history 1 1)]
        (is (= ["t.d-test"                       ; 3 failures
                "t.a-test" "t.b-test" "t.f-test" ; 1 each: 10s, 10s by name, then 1s
                "t.c-test" "t.e-test" "t.g-test"] ; none: 30s, then 20s against 12.67s
               nss))
        (is (str/includes? err "order: recurring failures first"))
        (is (not (some #{"t.zz-test"} nss)) "a namespace the tree lacks is not run")))))

(deftest a-history-the-script-cannot-trust-leaves-the-order-it-had-before
  (with-tree
    (fn [dir]
      (is (= alternating (nss dir nil 1 1)) "no history file")
      (doseq [[why hist] {"empty file"        ""
                          "no rows"           header
                          "stale"             (str/replace history "status: current" "status: stale")
                          "no status"         (str/replace history "# status: current\n" "")
                          "two statuses"      (str/replace history "# status: current\n" "# status: current\n# status: stale\n")
                          "another policy"    (str/replace history "policy: 1" "policy: 2")
                          "no policy"         (str/replace history "# policy: 1\n" "")
                          "negative count"    (str history "t.e-test\t-1\n")
                          "fractional count"  (str history "t.e-test\t1.5\n")
                          "exponent count"    (str history "t.e-test\t1e3\n")
                          "leading zero"      (str history "t.e-test\t01\n")
                          "huge count"        (str history "t.e-test\t99999999\n")
                          "third column"      (str history "t.e-test\t1\textra\n")
                          "space for tab"     (str history "t.e-test 1\n")
                          "carriage return"   (str/replace history "\n" "\r\n")
                          "duplicate row"     (str history "t.d-test\t3\n")
                          "upper case"        (str history "T.E-test\t1\n")
                          "shell in the name" (str history "$(touch pwned)\t1\n")
                          "shell in a count"  (str history "t.e-test\t`touch pwned`\n")}]
        (testing why
          (let [{:keys [nss err]} (shard dir hist 1 1)]
            (is (= alternating nss))
            (is (str/includes? err "history h.tsv ignored"))
            (is (not (.exists (io/file dir "pwned"))) "nothing in the file runs")))))))

(deftest the-history-moves-no-namespace-between-shards
  (with-tree
    (fn [dir]
      (doseq [of [1 2 3 4 7 9]]
        (testing (str of " shards")
          (let [with    (mapv #(nss dir history % of) (range 1 (inc of)))
                without (mapv #(nss dir nil % of) (range 1 (inc of)))]
            (is (= (map frequencies without) (map frequencies with)) "each shard holds the same namespaces")
            (is (= (frequencies namespaces) (frequencies (apply concat with)))
                "every namespace runs, once")))))))

(deftest the-checked-in-history-is-read-and-moves-no-namespace-between-shards
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which does not see this checkout"
    (doseq [leg ["memory" "disk"]]
      (testing leg
        (let [run (fn [n & more]
                    (let [{:keys [exit out err]} (apply shell/sh tu/bash "scripts/ci-shard.sh" (str n) "8" "--leg" leg more)]
                      (is (zero? exit) err)
                      {:nss (str/split-lines out) :err err}))
              with    (mapv run (range 1 9))
              without (mapv #(run % "--history" "target/no-such-history.tsv") (range 1 9))]
          (is (every? #(str/includes? (:err %) "order: recurring failures first") with)
              "scripts/ci-test-history.tsv is a history the script trusts")
          (is (= (map (comp frequencies :nss) without) (map (comp frequencies :nss) with)))
          (is (apply distinct? (mapcat :nss with))))))))
