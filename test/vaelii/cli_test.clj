;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cli-test
  "The command-line driver (`vaelii.host.cli`).  `dispatch` takes data args and is the
  whole engine surface the shell and REPL both call, so testing it (plus the arg/option
  parsing that feeds it) covers the CLI without spawning a process."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pp]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.core :as v]
            [vaelii.host.cli :as cli]
            [vaelii.impl.io.import :as imp]
            [vaelii.impl.reasoning-image :as ri]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-cli-" nm "-")
                                      (into-array FileAttribute []))))

(defn- rm-rf! [^File d]
  (doseq [^File f (reverse (file-seq d))] (.delete f)))

(deftest parse-opts-splits-positionals-and-flags
  (testing "--k v pairs and bare --flags, positionals kept in order"
    (is (= [["assert" "(dog Muffet)" "Ctx"] {:dir "/tmp/kb" :strength "monotonic"}]
           (cli/parse-opts ["assert" "(dog Muffet)" "--dir" "/tmp/kb" "Ctx" "--strength" "monotonic"]))))
  (testing "--memory / --starter are boolean flags"
    (is (= [[] {:memory true :starter true}] (cli/parse-opts ["--memory" "--starter"])))))

(deftest read-forms-parses-a-line-of-edn
  (is (= [(list 'dog '?x) 'CxMy] (cli/read-forms "(dog ?x) CxMy")))
  (is (= [] (cli/read-forms "   "))))

(tu/deftest-kb dispatch-runs-the-core-commands
  (tu/with-terms [dog animal Muffet CxCli]
    (testing "assert returns a handle; query returns the matching sentences"
      (is (nat-int? (cli/dispatch kb "assert" [(list dog Muffet) CxCli] {})))
      (is (= [(list dog Muffet)] (cli/dispatch kb "match" [(list dog '?x) CxCli] {}))))
    (testing "assert-rule / genl feed ask and provable? (specificity)"
      (cli/dispatch kb "assert" [(list 'genl dog animal) CxCli] {})
      (is (true? (cli/dispatch kb "provable?" [(list animal Muffet) CxCli] {})))
      (is (some #(= Muffet (get % '?x)) (cli/dispatch kb "ask" [(list animal '?x) CxCli] {}))))
    (testing "handle-of + why give a proof tree"
      (let [h (cli/dispatch kb "handle-of" [(list dog Muffet) CxCli] {})]
        (is (nat-int? h))
        (is (map? (cli/dispatch kb "why" [h] {})))
        (is (true? (cli/dispatch kb "in" [h] {})))))
    (testing "types lists the genl hierarchy nodes (dog is one after the genl edge)"
      (is (contains? (set (cli/dispatch kb "types" [] {})) dog))
      (is (coll? (cli/dispatch kb "contexts" [] {}))))
    (testing "an unknown command throws with the command list"
      (is (thrown? clojure.lang.ExceptionInfo (cli/dispatch kb "frobnicate" [] {}))))
    (testing "retract tears the fact down"
      (let [h (cli/dispatch kb "handle-of" [(list dog Muffet) CxCli] {})]
        (cli/dispatch kb "retract" [h] {})
        (is (empty? (cli/dispatch kb "match" [(list dog Muffet) CxCli] {})))))))

(tu/deftest-kb a-command-word-the-table-does-not-know-is-refused-with-the-table
  ;; The refusal is for a typo at the shell.  Dispatched as nothing it would exit 0
  ;; having run no command — `asserr '(dog Muffet)' CxCli` is indistinguishable from a stored fact to
  ;; whoever typed it — so the word comes back named, with the roster of the ones that
  ;; do exist for a shell to print.
  (let [e (is (thrown? clojure.lang.ExceptionInfo (cli/dispatch kb "frobnicate" [] {})))
        d (ex-data e)]
    (is (= :unknown-command (:type d)))
    (is (= "frobnicate" (:cmd d)))
    (is (= cli/commands (:commands d)))))

(deftest an-answer-set-prints-the-same-however-the-knowledge-arrived
  ;; `match`, `query` and `ask` answer sets, and a set has no order of its own — so what
  ;; reached stdout was whichever order the retrieval enumerated, and two loads of one KB
  ;; printed the same knowledge differently.  A script diffing two runs read that as a
  ;; change in the KB.  `types` and `contexts` in the same table were already sorted.
  (let [facts   (for [n ["Ann" "Bob" "Cid" "Dee" "Eve" "Fay" "Gus" "Hal" "Ivy" "Jo"]]
                  (list 'dog (symbol n)))
        run     (fn [order]
                  (tu/with-cleared-kb [kb tu/isolated-fresh]
                    (doseq [f order] (v/assert kb f 'CxCliOrder))
                    (mapv #(with-out-str (pp/pprint
                                          (cli/dispatch kb % [(list 'dog '?x) 'CxCliOrder] {})))
                          ["match" "query" "ask"])))
        forward (run facts)
        reverse* (run (reverse facts))]
    (is (= 10 (count facts)) "ten distinct facts, so an order has something to differ about")
    (is (= forward reverse*)
        "the three set-answering commands print identically for the two arrival orders")
    (testing "and what they print is the whole answer, not a sorted prefix of it"
      ;; `match` prints sentences and the other two print binding maps, so the thing every
      ;; answer carries once is the individual it is about
      (doseq [out forward]
        (is (= 10 (count (re-seq #"Ann|Bob|Cid|Dee|Eve|Fay|Gus|Hal|Ivy|Jo" out))))))))

(tu/deftest-kb prove-keeps-the-order-its-derivations-were-found-in
  ;; The exception to the rule above, and stated so it is not tidied away later: `prove`
  ;; answers one solution per derivation, and which derivation came first is a reading of
  ;; the search rather than an artifact of storage.
  (tu/with-terms [dog animal Muffet CxCliProve]
    (v/assert kb (list dog Muffet) CxCliProve)
    (v/assert kb (list 'genl dog animal) CxCliProve)
    (let [sols (cli/dispatch kb "prove" [(list animal '?x) CxCliProve] {})]
      (is (seq sols))
      (is (= (vec (v/prove kb (list animal '?x) CxCliProve)) (vec sols))
          "handed back in the order the search produced, not re-ordered into a set answer"))))

(tu/deftest-kb quality-answers-in-prose-because-four-distributions-are-not-a-value-to-read
  ;; the one command whose answer is a document rather than data — and the consumer that
  ;; keeps `kb-quality` and `quality-report` exercised as a pair
  (tu/with-terms [a_type pOne]
    (v/assert-rule kb [(list a_type '?x)] (list pOne '?x) 'CxUniverse)
    (let [out (cli/dispatch kb "quality" [] {})]
      (is (string? out) "a string, so `show` prints it as written rather than pprinting it")
      (is (re-find #"# KB quality" out))
      (is (re-find #"1 rules — \*\*1 never fired\*\*" out) "the rule nothing matched")
      (is (re-find #"## Taxonomy coverage" out)))))

(tu/deftest-kb strength-option-marks-an-assert-monotonic
  (tu/with-terms [cat Felix CxCli]
    (cli/dispatch kb "assert" [(list cat Felix) CxCli] {:strength "monotonic"})
    (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list cat Felix) CxCli))))))

(deftest read-arg-keeps-a-path-a-path
  (testing "an argv string that reads as EDN is data — a sentence, a context, a handle"
    (is (= (list 'dog 'Muffet) (cli/read-arg "(dog Muffet)")))
    (is (= 'CxNaturalWorld (cli/read-arg "CxNaturalWorld")))
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
      (tu/with-terms [dog Muffet CxExport]
        (cli/dispatch kb "assert" [(list dog Muffet) CxExport] {})
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
                (is (some? (v/handle-of target (list dog Muffet) CxExport)))
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

(tu/deftest-kb load-reads-a-text-kb-file-and-asserts-it
  ;; The text KB format — the file name is the context, so `load` takes no context
  ;; argument and one file's forms all land in one place.
  (tu/with-terms [dog cat Muffet Felix CxLoad]
    (let [d (temp-dir "load")
          f (io/file d (str CxLoad ".txt"))]
      (try
        (spit f (str ";; a comment, which the reader skips\n"
                     (pr-str (list dog Muffet)) "\n"
                     (pr-str (list cat Felix)) "\n"))
        (let [r (cli/dispatch kb "load" [(.getPath f)] {})]
          (is (= 2 (:sentences r)))
          (is (= 1 (:contexts r)))
          (is (= [(str CxLoad ".txt")] (:files r))))
        (is (seq (v/sentexes-matching kb (list dog Muffet) CxLoad)))
        (is (seq (v/sentexes-matching kb (list cat Felix) CxLoad)))
        (finally (rm-rf! d))))))

(tu/deftest-kb load-reads-a-directory-of-context-files
  ;; A whole text KB is a directory of `Cx<Name>.txt`, and `load` reads it in one
  ;; order-insensitive pass — so a context resting on another's content loads whichever
  ;; file name sorts first.
  (tu/with-terms [dog cat Muffet Felix CxOne CxTwo]
    (let [d (temp-dir "loaddir")]
      (try
        (spit (io/file d (str CxOne ".txt")) (str (pr-str (list dog Muffet)) "\n"))
        (spit (io/file d (str CxTwo ".txt")) (str (pr-str (list cat Felix)) "\n"))
        (spit (io/file d "README") "not a context file")
        (let [r (cli/dispatch kb "load" [(.getPath d)] {})]
          (is (= 2 (:sentences r)) "the README is not a context file")
          (is (= 2 (:contexts r))))
        (is (seq (v/sentexes-matching kb (list dog Muffet) CxOne)))
        (is (seq (v/sentexes-matching kb (list cat Felix) CxTwo)))
        (finally (rm-rf! d))))))

(tu/deftest-kb export-format-text-writes-a-text-kb-that-load-reads-back
  (tu/with-terms [dog cat Muffet Felix CxRound]
    (let [d (temp-dir "text")]
      (try
        (rm-rf! d)
        (v/assert kb (list 'genlCx CxRound 'CxUniverse) 'CxUniverse)
        (v/assert kb (list dog Muffet) CxRound)
        (v/assert kb (list cat Felix) CxRound {:strength :monotonic})
        (let [r (cli/dispatch kb "export" [(.getPath d)] {:format "text"})]
          (is (contains? (set (:files r)) (str CxRound ".txt")))
          (is (pos? (:sentences r))))
        (testing "a dump option beside --format text is refused rather than dropped"
          (let [e (try (cli/dispatch kb "export" [(.getPath d)]
                                     {:format "text" :compression "gzip"})
                       nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
            (is (= :unknown-option (:type e)))))
        (finally (rm-rf! d))))))

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

(defn- snapshot-store!
  "A temporary directory holding a closed `:disk-snapshot` store with a taxonomy edge and
  a membership in it, and so a reasoning image and an index image."
  ^String []
  (let [dir (str (Files/createTempDirectory "vaelii-cli-store" (make-array FileAttribute 0)))
        kb  (v/open-kb {:backend :disk-snapshot :dir dir})]
    (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(dog Rex) 'CxUniverse)
    (v/close! kb)
    dir))

(deftest dir-opens-a-store-under-the-backend-its-files-name
  ;; `--dir` opened every directory as `:disk-log`. A `:disk-snapshot` store opened that way
  ;; finds no index log, so every read answered nothing although the records were on disk.
  (let [dir (snapshot-store!)]
    (try
      (let [kb (cli/open-kb-from {:dir dir})]
        (try
          (is (= ['(genl dog animal)]
                 (mapv v/sentence-of (v/sentexes-matching kb '(genl dog ?x) 'CxUniverse))))
          (finally (v/close! kb))))
      (finally (rm-rf! (io/file dir))))))

(deftest upgrade-rebuilds-a-stale-reasoning-image-and-leaves-a-current-one
  (let [dir      (snapshot-store!)
        manifest (io/file dir "reasoning" "manifest.edn")]
    (try
      (is (.exists manifest) "closing a KB built assert by assert writes its first image")
      (testing "an image this build wrote is installed, and the manifest is left as it was"
        (let [before (slurp manifest)
              r      (cli/upgrade! dir)]
          (is (= :disk-snapshot (:backend r)))
          (is (= :current (:reasoning r)))
          (is (= before (slurp manifest)))))
      (testing "an image stamped with other engine source is declined, rebuilt and restamped"
        (spit manifest (pr-str (assoc (edn/read-string (slurp manifest)) :source "stale")))
        (let [r (cli/upgrade! dir)]
          (is (= :rebuilt (:reasoning r)))
          (is (not= "stale" (:source (edn/read-string (slurp manifest)))))
          (is (= :current (:reasoning (cli/upgrade! dir)))
              "the restamped image is current for the next upgrade")))
      (finally (rm-rf! (io/file dir)))))
  (testing "a directory holding no store is refused, and no store is created in it"
    (let [dir (str (Files/createTempDirectory "vaelii-cli-empty" (make-array FileAttribute 0)))]
      (try
        (let [e (is (thrown? clojure.lang.ExceptionInfo (cli/upgrade! dir)))]
          (is (= :unknown-source (:type (ex-data e))))
          (is (empty? (.list (io/file dir)))))
        (finally (rm-rf! (io/file dir)))))))

(deftest upgrade-trusts-a-restamped-source-or-verifies-it-by-a-recover
  (let [dir      (snapshot-store!)
        manifest (io/file dir "reasoning" "manifest.edn")
        stale!   #(spit manifest (pr-str (assoc (edn/read-string (slurp manifest)) :source "stale")))]
    (try
      (stale!)
      (is (= :rebuilt (:reasoning (cli/upgrade! dir)))
          "a recover writes the image the cases below start from")
      (testing "an image this build wrote is left as it was"
        (is (= :current (:reasoning (cli/upgrade! dir)))))
      (testing "--verify recovers under this build and compares the two images"
        (stale!)
        (let [r (cli/upgrade! dir {:verify true})]
          (is (= :rebuilt (:reasoning r)))
          (is (= {:labels :same :against "stale"} (select-keys (:verify r) [:labels :against])))
          (is (not (.exists (io/file dir "reasoning.prev"))) "the old image is deleted once compared")))
      (finally (rm-rf! (io/file dir))))))

(deftest compare-images-reads-a-belief-change-off-the-labels
  (let [a (snapshot-store!)
        b (snapshot-store!)]
    (try
      (let [kb (v/open-kb {:backend :disk-snapshot :dir b})]
        (v/assert kb '(dog Fido) 'CxUniverse)
        (v/close! kb))
      (is (= {:labels :same :network :same :state :same}
             (ri/compare-images (io/file a "reasoning") (io/file a "reasoning"))))
      (is (= :differs (:labels (ri/compare-images (io/file a "reasoning") (io/file b "reasoning"))))
          "a store with one more believed sentex believes a different set")
      (finally (rm-rf! (io/file a)) (rm-rf! (io/file b))))))

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
                ["load" "/tmp/kb-text" "--dri" "/tmp/kb"]]]
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
      (is (= :bad-args (:type (ex-data e)))
          "`:bad-args`, the keyword for an operation given the wrong number of arguments —
           not `:unknown-option`, which would tell a caller a flag was bad when every flag
           on the line may be one this command reads")
      (is (= {:op "assert" :given 1 :takes [2 2]}
             (select-keys (ex-data e) [:op :given :takes]))
          "and `:op` is the word `serve` already names a wire call's operation with")
      (is (re-find #"assert takes 2 arguments, given 1" (ex-message e)))
      (is (re-find #"usage: assert" (ex-message e))
          "and the message carries the usage line")))
  (testing "too many is refused too — a dropped context stores somewhere else"
    (let [e (try (cli/check-arity! "assert" ['(dog Rex) 'CxA 'CxB]) nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= 3 (:given (ex-data e))))))
  (testing "an optional last operand takes either count"
    (is (nil? (cli/check-arity! "why-not" ['(dog Rex)])))
    (is (nil? (cli/check-arity! "why-not" ['(dog Rex) 'CxA])))
    (is (nil? (cli/check-arity! "isa" ['Rex 'dog])))
    (is (nil? (cli/check-arity! "isa" ['Rex 'dog 'CxA]))))
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

(tu/deftest-kb assert-rule-carries-the-strength-flag
  ;; parsed one line up and never passed, --strength monotonic stored the rule at
  ;; :default — where the first contradicting default could defeat known-true content
  (tu/with-terms [dog animal CxCli]
    (let [h (cli/dispatch kb "assert-rule"
                          [[(list dog '?x)] (list animal '?x) CxCli]
                          {:strength "monotonic"})]
      (is (= :monotonic (:strength (v/sentex kb h)))
          "the flag reaches the stored rule's record"))))

(deftest a-flag-is-not-a-value-for-the-flag-before-it
  ;; `--dir --starter` once opened a durable KB in a directory literally named
  ;; --starter, took its writer lock, and loaded no schema
  (let [e (is (thrown? clojure.lang.ExceptionInfo
                       (cli/parse-opts ["assert" "(dog Rex)" "C" "--dir" "--starter"])))]
    (is (= :unknown-option (:type (ex-data e))))
    (is (re-find #"--starter" (ex-message e)) "the refusal names the swallowed flag")))

(deftest a-flag-a-command-does-not-read-is-refused-rather-than-dropped
  ;; The roster `parse-opts` holds says which flags exist; this one says which command
  ;; may carry which. `match … --strength monotonic` bound the option, ran a read that
  ;; never looks at it, and reported nothing — indistinguishable from a strength that
  ;; was applied.
  (testing "a real flag on a command that does not read it"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (cli/check-flags! "match" {:strength "monotonic"})))
          d (ex-data e)]
      (is (= :unknown-option (:type d)))
      (is (= "match" (:cmd d)))
      (is (= ["--strength"] (:unread d)) "the refusal names the flag it cannot honour")
      (is (re-find #"no options of its own" (ex-message e)))))
  (testing "and one the command does read is admitted, as are the driver's own"
    (is (nil? (cli/check-flags! "assert" {:strength "monotonic"})))
    (is (nil? (cli/check-flags! "match" {:dir "/tmp/kb" :starter true})))
    (is (nil? (cli/check-flags! "export" {:variant "records" :compression "gzip"}))))
  (testing "a command reading one value flag does not thereby read the others"
    (let [d (ex-data (is (thrown? clojure.lang.ExceptionInfo
                                  (cli/check-flags! "query" {:strength "monotonic"}))))]
      (is (= ["--strength"] (:unread d)))
      (is (= ["--depth"] (:reads d)) "and the message says what it does read")))
  (testing "repl carries the union — its options are fixed at start and each line reuses them"
    (is (nil? (cli/check-flags! "repl" {:strength "monotonic" :depth "3"
                                        :variant "records" :compression "gzip"}))))
  (testing "an unknown command word is left to the unknown-command report"
    (is (nil? (cli/check-flags! "nosuchcmd" {:strength "monotonic"}))))
  (testing "and so is no command at all, which is the repl by another spelling"
    ;; `-main` drops into the loop on a bare `lein cli --strength monotonic`, so the
    ;; flags belong to the session exactly as they do after the word `repl`
    (is (nil? (cli/check-flags! nil {:strength "monotonic" :depth "3"})))))
