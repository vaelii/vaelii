;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cli-test
  "The command-line driver (`vaelii.impl.cli`).  `dispatch` takes data args and is the
  whole engine surface the shell and REPL both call, so testing it (plus the arg/option
  parsing that feeds it) covers the CLI without spawning a process."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as catalog]
            [vaelii.impl.cli :as cli]
            [vaelii.impl.io.import :as imp]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest parse-opts-splits-positionals-and-flags
  (testing "--k v pairs and bare --flags, positionals kept in order"
    (is (= [["assert" "(dog Muffet)" "Ctx"] {:dir "/tmp/kb" :strength "monotonic"}]
           (cli/parse-opts ["assert" "(dog Muffet)" "--dir" "/tmp/kb" "Ctx" "--strength" "monotonic"]))))
  (testing "--memory / --starter are boolean flags"
    (is (= [[] {:memory true :starter true}] (cli/parse-opts ["--memory" "--starter"])))))

(deftest read-forms-parses-a-line-of-edn
  (is (= [(list 'dog '?x) 'MyContext] (cli/read-forms "(dog ?x) MyContext")))
  (is (= [] (cli/read-forms "   "))))

(tu/deftest-kb dispatch-runs-the-core-commands
  (tu/with-terms [dog animal Muffet CliContext]
    (testing "assert returns a handle; query returns the matching sentences"
      (is (nat-int? (cli/dispatch kb "assert" [(list dog Muffet) CliContext] {})))
      (is (= [(list dog Muffet)] (cli/dispatch kb "match" [(list dog '?x) CliContext] {}))))
    (testing "assert-rule / genl feed ask and provable? (specificity)"
      (cli/dispatch kb "assert" [(list 'genl dog animal) CliContext] {})
      (is (true? (cli/dispatch kb "provable?" [(list animal Muffet) CliContext] {})))
      (is (some #(= Muffet (get % '?x)) (cli/dispatch kb "ask" [(list animal '?x) CliContext] {}))))
    (testing "handle-of + why give a proof tree"
      (let [h (cli/dispatch kb "handle-of" [(list dog Muffet) CliContext] {})]
        (is (nat-int? h))
        (is (map? (cli/dispatch kb "why" [h] {})))
        (is (true? (cli/dispatch kb "in" [h] {})))))
    (testing "types lists the genl hierarchy nodes (dog is one after the genl edge)"
      (is (contains? (set (cli/dispatch kb "types" [] {})) dog))
      (is (coll? (cli/dispatch kb "contexts" [] {}))))
    (testing "an unknown command throws with the command list"
      (is (thrown? clojure.lang.ExceptionInfo (cli/dispatch kb "frobnicate" [] {}))))
    (testing "retract tears the fact down"
      (let [h (cli/dispatch kb "handle-of" [(list dog Muffet) CliContext] {})]
        (cli/dispatch kb "retract" [h] {})
        (is (empty? (cli/dispatch kb "match" [(list dog Muffet) CliContext] {})))))))

(tu/deftest-kb strength-option-marks-an-assert-monotonic
  (tu/with-terms [cat Felix CliContext]
    (cli/dispatch kb "assert" [(list cat Felix) CliContext] {:strength "monotonic"})
    (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list cat Felix) CliContext))))))

(deftest read-arg-keeps-a-path-a-path
  (testing "an argv string that reads as EDN is data — a sentence, a context, a handle"
    (is (= (list 'dog 'Muffet) (cli/read-arg "(dog Muffet)")))
    (is (= 'NaturalWorldContext (cli/read-arg "NaturalWorldContext")))
    (is (= 3 (cli/read-arg "3"))))
  (testing "and one that reads as none is the string it already was, which is what an
            absolute filesystem path is: /var/lib/vaelii has two slashes and is no symbol"
    (is (= "/var/lib/vaelii" (cli/read-arg "/var/lib/vaelii"))))
  (testing "a path the reader *does* accept comes back as a symbol, so a command taking
            one reads it as text either way — which is why the path arms coerce"
    (is (= "./kbs/a-dump" (str (cli/read-arg "./kbs/a-dump"))))))

(tu/deftest-kb export-writes-a-dump-the-catalog-offers-and-the-importer-reads
  (let [root (.toFile (Files/createTempDirectory "vaelii-cli-export-"
                                                 (into-array FileAttribute [])))
        dump (io/file root "a-dump")]
    (try
      (tu/with-terms [dog Muffet ExportContext]
        (cli/dispatch kb "assert" [(list dog Muffet) ExportContext] {})
        (let [summary (cli/dispatch kb "export" [(.getPath dump)] {:compression "none"})]
          (testing "the command answers with the writer's own summary"
            (is (= :records (:variant summary)))
            (is (= (v/sentex-count kb) (:sentexes summary)))
            (is (pos? (:bytes summary))))
          (testing "what it wrote is a dump — the marker the catalog keys on"
            (is (= :dump (catalog/classify dump)))
            (is (= :vaelii/export (:format (imp/read-meta dump)))))
          (testing "and the importer reads it back whole"
            ;; its own space: the suite's scratch block is this KB's, and clearing it
            ;; from under a running test is what the block exists to prevent
            (let [target (v/open-kb {:backend :memory :space 66
                                     :recover? false})]
              (try
                (imp/import-dump target (.getPath dump) {:belief? false})
                (is (= (v/sentex-count kb) (v/sentex-count target)))
                (is (some? (v/handle-of target (list dog Muffet) ExportContext)))
                (finally (v/clear! target)))))
          (testing "--variant and --compression are the writer's own keywords, read from
                    the strings a shell hands over"
            (let [with-index (io/file root "with-index")
                  s (cli/dispatch kb "export" [(.getPath with-index)]
                                  {:variant "records+index" :compression "none"})]
              (is (= :records+index (:variant s)))
              (is (pos? (:index-entries s)))))
          (testing "exporting into a directory that already holds one is refused, in the
                    writer's words — the same message every surface reports"
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"is not empty"
                                  (cli/dispatch kb "export" [(.getPath dump)] {}))))))
      (finally (doseq [^File f (reverse (file-seq root))] (.delete f))))))

(tu/deftest-kb load-reads-edn-entries-and-asserts-them-in-one-batch
  (tu/with-terms [dog cat Muffet Felix LoadContext]
    (let [f (File/createTempFile "vaelii-cli-load" ".edn")]
      (try
        (spit f (pr-str [[(list dog Muffet) LoadContext] [(list cat Felix) LoadContext]]))
        (is (= {:loaded 2 :stored 2} (cli/dispatch kb "load" [(.getPath f)] {})))
        (is (seq (v/sentexes-matching kb (list dog Muffet) LoadContext)))
        (is (seq (v/sentexes-matching kb (list cat Felix) LoadContext)))
        (finally (.delete f))))))

(tu/deftest-kb load-reports-entries-and-stored-sentexes-separately
  ;; `assert` answers the existing handle for a sentence already stored, so a file of
  ;; duplicates reports what it *did* — one stored sentex — beside what it read.  A
  ;; bare "loaded 3" reports the input's size as though it were the write's.
  (tu/with-terms [dog Muffet DupContext]
    (let [f (File/createTempFile "vaelii-cli-dup" ".edn")]
      (try
        (spit f (pr-str [[(list dog Muffet) DupContext]
                         [(list dog Muffet) DupContext]
                         [(list dog Muffet) DupContext]]))
        (is (= {:loaded 3 :stored 1} (cli/dispatch kb "load" [(.getPath f)] {})))
        (is (= 1 (count (v/sentexes-matching kb (list dog '?x) DupContext))))
        (finally (.delete f))))))

(deftest a-flag-missing-its-value-is-refused-not-bound-nil
  ;; `--strength` at the end of a line would otherwise bind nil, and the assert lands
  ;; at :default — the exact class the flag was written to escape — with `--dir` the
  ;; same shape: the KB opens in memory and evaporates at process exit.
  (doseq [flag ["--strength" "--dir" "--depth"]]
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (cli/parse-opts ["assert" "(dog Muffet)" "Ctx" flag]))
                (str flag " with no value is refused"))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= flag (:flag (ex-data e))))
      (is (re-find #"needs a value" (ex-message e)))))
  (testing "a flag with its value still parses"
    (is (= [["assert"] {:strength "monotonic"}]
           (cli/parse-opts ["assert" "--strength" "monotonic"])))))

(deftest memory-forces-the-memory-backend-and-contradicts-dir
  (testing "--memory alone opens the in-process KB"
    (let [kb (cli/open-kb-from {:memory true})]
      (is (nil? (:dir kb)) "no directory: the memory backend")))
  (testing "--memory --dir is a contradiction, refused rather than resolved by a guess"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (cli/open-kb-from {:memory true :dir "/tmp/vaelii-nowhere"})))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (re-find #"contradict" (ex-message e))))))

(tu/deftest-kb the-repl-loop-survives-a-stack-overflowing-line
  ;; A deeply nested EDN line raises StackOverflowError out of `read-forms` — past
  ;; `Exception`, so a `catch Exception` loop dies on a line of input.  The loop
  ;; catches `Throwable`, as the browser's untrusted-EDN reads do, prints one line and
  ;; reads the next.
  (let [deep (str (apply str (repeat 100000 "[")) (apply str (repeat 100000 "]")))
        out  (with-out-str
               (with-in-str (str "why " deep "\ntypes\nexit\n")
                 (#'cli/repl-loop kb {})))]
    (is (re-find #"error: StackOverflowError" out)
        "the overflow is reported as an ordinary error line")
    (is (re-find #"bye" out) "and the loop survived it to reach exit")))

(deftest an-unknown-flag-is-refused-not-keywordized
  ;; `--strenght monotonic` keywordized in silence stored known-true content at
  ;; :default — the exact sentence the flag-with-no-value refusal exists for,
  ;; reached from the other side — and a misspelt `--dir` opened the in-memory KB.
  (doseq [args [["assert" "(dog Muffet)" "C" "--strenght" "monotonic"]
                ["query" "(dog ?x)" "C" "--dept" "3"]
                ["load" "/tmp/x.edn" "--dri" "/tmp/kb"]]]
    (let [e (try (cli/parse-opts args) nil
                 (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :unknown-option (:type e)) (pr-str args)))))

(deftest a-short-command-line-names-the-missing-argument
  ;; `dispatch` reaches into `args` with `nth`, so a line missing its context
  ;; raised `IndexOutOfBoundsException` — caught and printed as one line, so
  ;; `lein cli assert '(dog Rex)'` answered `error: IndexOutOfBoundsException`:
  ;; true about a vector, and no help to someone who left off a context.
  (testing "too few operands is refused, naming the command and the count"
    (let [e (try (cli/check-arity! "assert" ['(dog Rex)]) nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e) "a one-operand assert is refused")
      (is (= :unknown-option (:type (ex-data e))))
      (is (= {:cmd "assert" :given 1 :takes [2 2]}
             (select-keys (ex-data e) [:cmd :given :takes])))
      (is (re-find #"assert takes 2 arguments, given 1" (ex-message e)))
      (is (re-find #"usage: assert" (ex-message e))
          "and the message carries the usage line")))
  (testing "too many is refused too — a dropped context stores somewhere else"
    (let [e (try (cli/check-arity! "assert" ['(dog Rex) 'AContext 'BContext]) nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= 3 (:given (ex-data e))))))
  (testing "an optional last operand takes either count"
    (is (nil? (cli/check-arity! "why-not" ['(dog Rex)])))
    (is (nil? (cli/check-arity! "why-not" ['(dog Rex) 'AContext])))
    (is (nil? (cli/check-arity! "isa" ['Rex 'dog])))
    (is (nil? (cli/check-arity! "isa" ['Rex 'dog 'AContext]))))
  (testing "a zero-operand command refuses operands"
    (is (nil? (cli/check-arity! "types" [])))
    (is (thrown? clojure.lang.ExceptionInfo (cli/check-arity! "types" ['x]))))
  (testing "an unknown command is dispatch's to refuse, not this one's"
    (is (nil? (cli/check-arity! "nosuchcommand" [])))))

(deftest the-usage-text-covers-every-command-the-table-knows
  ;; One table feeds both the arity check and `help`, so a command cannot be
  ;; advertised at an arity it does not take, or added without a usage line.
  (let [u (cli/usage)]
    (doseq [c cli/commands]
      ;; `(?=\s|$)` rather than `\b`: `query?` and `provable?` end in a non-word
      ;; character, so a word boundary never lands after them.
      (is (re-find (re-pattern (str "(?m)^  " (java.util.regex.Pattern/quote c) "(?=\\s|$)")) u)
          (str c " has a usage line")))
    (is (re-find #"Quote every argument" u)
        "the shell-quoting trap is stated, since `[` dies in zsh before the JVM starts")
    (is (= (count cli/commands) (count (distinct cli/commands)))))
  (testing "--help is a boolean flag rather than an unknown one"
    (is (= [[] {:help true}] (cli/parse-opts ["--help"])))))
