;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.multi-jvm-test
  "The cross-process contracts, each observed from a second JVM because there is nowhere
  else to observe it from.

  Not \"integration tests\" — the whole suite is that already, and CONTRIBUTING.md §5
  says so in as many words — and not end-to-end either: four of the five watch one
  contract from the only vantage that can see it, rather than walking a user's path
  through a stack.  What they share is the **process boundary**, which is also what makes
  them expensive, so they carry `^:multi-jvm` and no selector reaches them.  `lein test`,
  `lein test :all` and `lein gate` all pass over this file; `lein test-multi-jvm` and
  `deep.yml`'s job run it.

  What each one is *for* — the claim it turns from prose into a test:

  | the claim | where it is written | why one JVM cannot check it |
  |---|---|---|
  | a second writer is refused by name | `disk/lock.clj`, `docs/storage.md` | `tryLock` **throws** inside one JVM and returns nil across two, so a single-process test takes the other branch |
  | a killed writer leaves no lock to reap | `disk/lock.clj` | the OS releases on exit, and a JVM cannot watch its own |
  | a KB another process wrote opens cold | `docs/storage.md` | two KBs over one directory **share** the store in-process, and every process-global cache survives a `close-dir!` |
  | daemon and CLI cannot own one directory | `docs/operations.md` | the daemon is the other process |
  | a killed logged writer restores to a prefix of its operations | `vaelii.impl.seal` | SIGKILL stops the writer inside an operation, a frame append or a seal, and a process cannot do that to itself and read the result |

  **These own their directories and touch no shared space.**  Every KB here is a fresh
  temp directory, so the suite's scratch/isolated block is not involved and there is
  nothing for a net-neutrality fixture to check.  A child gets its own directory too:
  two suites over one directory colliding on the single-writer lock is what
  `scripts/test-parallel.sh` refuses to shard into, and here it is the subject.

  **The last test in this file carries no mark on purpose.**  It is a source scan, it
  forks nothing, and it runs in `:default` — where it has to run, since what it checks is
  that nobody added a forking test *without* the mark and dropped a JVM fork into the
  fast gate."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.cli :as cli]
            [vaelii.client :as vc]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.lock :as lock]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.seal :as seal]
            [vaelii.multi-jvm :as mj])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- with-tmp
  "Run `(f dir)` in a fresh temp directory, closing any stores this JVM opened on it and
  deleting it afterwards — `disk_backend_test`'s shape, and for its reason: the
  durability daemon must not outlive the directory."
  [f]
  (let [dir (str (Files/createTempDirectory "vaelii-mj-" (into-array FileAttribute [])))]
    (try (f dir)
         (finally
           (backend/close-dir! dir)
           (doseq [^File x (reverse (file-seq (io/file dir)))] (.delete x))))))

;; ---- the child programs --------------------------------------------------
;;
;; Each is a whole program, held as text and run by `clojure.main` in the child.  They
;; are short on purpose: a child that fails is diagnosed from its transcript, and a
;; transcript is only readable if the program that produced it fits on a screen.  Every
;; one drops the log level first, because a child's trove output shares the stream the
;; parent synchronizes on.

(def ^:private holder-program
  "Open the directory, say so, and hold the lock until told to let go.  The second writer
  the lock exists to refuse."
  "(require '[vaelii.core :as v])
   (v/set-log-level :error)
   (let [dir (first *command-line-args*)
         kb  (v/open-kb {:backend :disk-log :dir dir :recover? false})]
     (println \"##vaelii## held\")
     (flush)
     (read-line)                      ; the parent decides when the lock goes back
     (v/close! kb)
     (println \"##vaelii## released\")
     (flush))")

(def ^:private writer-program
  "Write a small KB, close it cleanly, exit.  What the parent then opens cold."
  "(require '[vaelii.core :as v])
   (v/set-log-level :error)
   (let [dir (first *command-line-args*)
         kb  (v/open-kb {:backend :disk-log :dir dir :recover? false})]
     (v/assert kb '(genl mj_dog mjAnimal) 'CxUniverse {:strength :monotonic})
     (v/assert kb '(mj_dog MjFido) 'CxUniverse {:strength :monotonic})
     (println (str \"##vaelii## wrote \" (v/handle-of kb '(mj_dog MjFido) 'CxUniverse)))
     (v/close! kb)
     (println \"##vaelii## closed\")
     (flush))")

(def ^:private daemon-program
  "Own a directory and serve it, the posture `docs/operations.md` calls the canonical
  single writer.  Binds port 0 and reports what it got, so nothing here guesses a port."
  "(require '[vaelii.core :as v] '[vaelii.serve :as serve])
   (v/set-log-level :error)
   (let [dir (first *command-line-args*)
         kb  (v/open-kb {:backend :disk-log :dir dir :recover? false})
         _   (v/assert kb '(genl mj_dog mjAnimal) 'CxUniverse {:strength :monotonic})
         _   (v/assert kb '(mj_dog MjFido) 'CxUniverse {:strength :monotonic})
         srv (serve/start kb {:port 0 :token nil})]
     (println (str \"##vaelii## port \" (serve/port srv)))
     (flush)
     (read-line)
     (.stop srv))")

;; ---- the tests -----------------------------------------------------------

(deftest ^:multi-jvm a-second-jvm-holding-the-directory-is-refused-by-name
  ;; `disk_backend_test` stages the overlapping-lock branch with a second FileChannel and
  ;; pins the cross-process message as a string, saying in its own comment that no
  ;; single-JVM test can stage the branch that matters.  This is that branch: `tryLock`
  ;; returning nil, the diagnosis reading the holder tag off the file, and the tag naming
  ;; a process that really exists.  A regression here is two writers appending to one log.
  (with-tmp
    (fn [dir]
      (mj/with-child [child holder-program dir]
        (mj/await-marker! child "held")
        (is (not (lock/held? dir)) "the lock is the child's — this JVM has no entry for it")
        (let [e (try (v/open-kb {:backend :disk-log :dir dir :recover? false})
                     nil
                     (catch clojure.lang.ExceptionInfo t t))
              d (ex-data e)]
          (is (some? e) "the open is refused rather than tearing the logs")
          (is (= :disk-locked (:type d)))
          ;; `:same-jvm? true` marks the overlapping-lock branch, and only that one, so
          ;; what this asserts is that we are NOT in the branch disk_backend_test stages.
          (is (not (:same-jvm? d))
              "and diagnosed as another process, not as this one's own channel")
          (is (re-find #"locked by another JVM" (ex-message e)))
          (is (str/includes? (str (:holder d)) (str (mj/pid child)))
              (str "the holder tag names the child's pid: " (pr-str (:holder d)))))
        (testing "and the directory is handed back when that process lets go"
          (mj/tell! child "release")
          (mj/await-marker! child "released")
          (is (zero? (mj/await-exit! child)) "the child closed cleanly")
          (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
            (is (lock/held? dir) "this JVM now holds it")
            (v/close! kb)))))))

(deftest ^:multi-jvm a-killed-writer-leaves-no-lock-to-reap
  ;; "The OS releases it when the JVM exits, so a crash leaves no stale lock to reap"
  ;; (disk/lock.clj).  Unfalsifiable from inside one process: a JVM cannot watch its own
  ;; exit, and a clean `close!` tests the code path rather than the OS guarantee the
  ;; comment is actually claiming.  Were it wrong, a crashed writer would lock its own KB
  ;; out forever and the fix would be an operator deleting a file nobody documented.
  (with-tmp
    (fn [dir]
      (mj/with-child [child holder-program dir]
        (mj/await-marker! child "held")
        (mj/kill! child)                      ; SIGKILL — no shutdown hook, no close!
        (is (not (.isAlive ^Process (:process child))) "the writer is gone, uncleanly"))
      (testing "the next opener takes the directory with no reaping step"
        (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
          (is (lock/held? dir))
          (is (.exists (io/file dir ".vaelii.lock"))
              "the lock FILE is still there — it is the OS lock that was released")
          (v/close! kb))))))

(deftest ^:multi-jvm a-kb-another-process-wrote-opens-cold-and-recovers
  ;; `close-then-reopen-from-disk-survives` reopens after `close-dir!`, which re-reads the
  ;; logs — but leaves every process-global structure warm: the symbol intern pool
  ;; (`docs/storage.md`: "static, process-wide and shared by every KB"), the backend and
  ;; durability registries, the condemned-image state.  A frame that resolves only
  ;; because this process already knows the symbol is durable to that test and lost on a
  ;; real restart, which the operator sees as "it worked yesterday".  Here the writer is
  ;; a process that has exited, so nothing in RAM can be answering.
  (with-tmp
    (fn [dir]
      (let [written (mj/with-child [child writer-program dir]
                      (let [h (mj/await-marker! child "wrote")]
                        (mj/await-marker! child "closed")
                        (is (zero? (mj/await-exit! child)) "the writer exited cleanly")
                        (Long/parseLong h)))]
        (is (pos? written) "the child reported the handle it wrote")
        (testing "this process opens the directory it never wrote to"
          (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? :auto})]
            (try
              (is (some? (v/handle-of kb '(mj_dog MjFido) 'CxUniverse))
                  "the record the other process stored is readable")
              (is (= written (v/handle-of kb '(mj_dog MjFido) 'CxUniverse))
                  "at the same handle, so the id survived the process it was minted in")
              (is (seq (v/sentexes-matching kb '(mj_dog ?x) 'CxUniverse))
                  "and is believed, not merely stored")
              (is (v/isa? kb 'MjFido 'mjAnimal)
                  "with the taxonomy rebuilt from a store this JVM did not derive")
              (finally (v/close! kb)))))))))

(deftest ^:multi-jvm a-daemon-in-another-process-answers-this-one-s-client
  ;; Every daemon test in the suite runs jetty in the test JVM: a real socket, a real
  ;; client, one process.  That checks the wire and cannot check the posture the wire is
  ;; FOR — `docs/operations.md`: "one JVM owns one KB and every client reaches it through
  ;; that one process", which is also `docs/koinii.md`'s whole argument for the `wire`
  ;; medium existing.  Here the KB is genuinely somewhere else.
  (with-tmp
    (fn [dir]
      (mj/with-child [child daemon-program dir]
        (let [port (Long/parseLong (mj/await-marker! child "port"))
              conn (vc/client "localhost" port {:token nil :timeout-ms 20000})]
          (is (pos? port) "the daemon reported the port it bound")
          (testing "a read crosses the boundary"
            (is (vc/ask? conn '(mj_dog MjFido) 'CxUniverse)
                "the client sees what the daemon's own process asserted"))
          (testing "and a write does, landing in the other process's KB"
            (vc/assert conn '(mj_dog MjRex) 'CxUniverse {:strength :monotonic})
            (is (vc/ask? conn '(mj_dog MjRex) 'CxUniverse))
            (is (seq (vc/sentexes-matching conn '(mj_dog ?x) 'CxUniverse))
                "and is matched by a pattern the daemon grounds"))
          (testing "the CLI cannot take a directory the daemon owns"
            ;; docs/operations.md: "The CLI with `--dir` takes the same lock, so it and a
            ;; daemon cannot own one directory at once."  The entry point is the CLI's own, so
            ;; what is checked is the refusal an operator actually meets.
            (let [e (try (cli/open-kb-from {:dir dir})
                         nil
                         (catch clojure.lang.ExceptionInfo t t))]
              (is (some? e) "`lein cli --dir` is refused while the daemon holds it")
              (is (= :disk-locked (:type (ex-data e))))
              (is (str/includes? (str (:holder (ex-data e))) (str (mj/pid child)))
                  "naming the daemon as the holder"))))))))

;; ---- a logged writer, killed -----------------------------------------------

(def ^:private crash-workload
  "The logged writer's operations, as one source text the child and this process both
  evaluate: `:setup` runs before the log's first seal, then `(op kb i)` for i from 0.  An
  even i asserts a new fact; an odd i retracts a fact `:setup` stored, so the log fsyncs
  that operation's frame before the retraction writes."
  "{:setup (fn [kb]
            (vaelii.core/assert
             kb '(set/forwardRule (implies (and (mjc_animal ?x)) (mjc_mortal ?x))) 'CxUniverse)
            (dotimes [i 200]
              (vaelii.core/assert kb (list 'mjc_animal (symbol (str \"MjcOld\" i))) 'CxUniverse)))
    :op    (fn [kb i]
             (if (even? i)
               (vaelii.core/assert kb (list 'mjc_animal (symbol (str \"MjcNew\" i))) 'CxUniverse)
               (vaelii.core/retract!
                kb (vaelii.core/handle-of
                    kb (list 'mjc_animal (symbol (str \"MjcOld\" (quot i 2)))) 'CxUniverse))))}")

(def ^:private crash-ops
  "How many operations the logged writer runs when nothing kills it."
  400)

(def ^:private logged-writer-program
  "Open a `:disk-snapshot` directory, run `crash-workload`'s setup, attach an operation
  log, and run the operations, saying after each one that it returned.  The parent kills
  it part-way; a writer that finishes first waits to be killed."
  (str "(require '[vaelii.core :as v] '[vaelii.impl.seal :as seal])
   (v/set-log-level :error)
   (def workload " crash-workload ")
   (let [dir (first *command-line-args*)
         kb  (v/open-kb {:backend :disk-snapshot :dir dir :recover? false})
         _   ((:setup workload) kb)
         lkb (seal/attach! kb)]
     (println \"##vaelii## sealed\")
     (flush)
     (dotimes [i " crash-ops "]
       ((:op workload) lkb i)
       (println (str \"##vaelii## done \" i))
       (flush))
     (println \"##vaelii## finished\")
     (flush)
     (read-line))"))

(defn- logged-view
  "Every sentex `kb`'s records hold, as `[sentence context believed?]`."
  [kb]
  (into #{} (keep (fn [h]
                    (when-let [sx (p/get-sentex (:records kb) h)]
                      [(pr-str (:sentence sx)) (pr-str (:context sx)) (boolean (v/in? kb h))])))
        (p/sentex-ids (:records kb))))

(defn- matching-prefix
  "The number m of `crash-workload` operations, `from` <= m <= `crash-ops`, after which a
  fresh directory's view is `want`, or nil when no such m exists."
  [want from]
  (let [{:keys [setup op]} (eval (read-string crash-workload))]
    (with-tmp
      (fn [dir]
        (let [kb (v/open-kb {:backend :disk-snapshot :dir dir :recover? false})]
          (try
            (setup kb)
            (dotimes [i from] (op kb i))
            (loop [m from]
              (cond (= want (logged-view kb)) m
                    (>= m crash-ops)          nil
                    :else                     (do (op kb m) (recur (inc m)))))
            (finally (v/close! kb))))))))

(deftest ^:multi-jvm a-killed-logged-writer-restores-to-a-prefix-of-its-operations
  ;; `vaelii.impl.seal`: a restore brings a directory to the state its last durable
  ;; operation left.  SIGKILL stops the writer inside whichever operation, frame append or
  ;; drift seal it had reached, and the page cache keeps every byte it wrote, so each
  ;; state a kill leaves is one the log and the seal have to account for.
  (with-tmp
    (fn [dir]
      (let [done (mj/with-child [child logged-writer-program dir]
                   (mj/await-marker! child "sealed")
                   (let [i (loop []
                             (let [i (Long/parseLong (mj/await-marker! child "done"))]
                               (if (< i 60) (recur) i)))]
                     (mj/kill! child)
                     (inc i)))
            kb (v/open-kb {:backend :disk-snapshot :dir dir :recover? false})
            r  (seal/restore! kb)]
        (try
          (if (:restored r)
            (let [m (matching-prefix (logged-view (:kb r)) done)]
              (is (some? m)
                  "the restored records and belief are those of a prefix of the operations")
              (is (and m (>= (long m) (long done)))
                  (str "and the prefix holds the " done " operations the writer reported done")))
            (is (#{:index :reasoning} (when (vector? (:reason r)) (first (:reason r))))
                (str "a declined restore names an image, which only a kill inside a seal"
                     " leaves: " (pr-str (dissoc r :kb)))))
          (finally (v/close! (or (:kb r) kb))))))))

;; ---- the mark, checked over the sources ----------------------------------
;;
;; `llm_test` holds the same shape for `^:llm`, and for the same reason: a mark is a
;; promise, and a promise nothing checks is kept until the first time it is not.  Here
;; the promise is required twice over — an unmarked test forks JVMs inside `lein
;; gate`, and a marked one nothing names never runs at all — so both directions are
;; checked: every forking test carries the mark, and the marked set is a roster.
;;
;; The patterns live in `def`s rather than inside a test body, so this scan does not
;; flag itself.  A scanner that fails on its own source is worse than no scanner.

(def ^:private helper-ns
  "The namespace that forks.  Matched in a file's `ns` form to find *which* files fork,
  and then in each file at whatever alias that file bound — a scan keyed on the
  conventional alias would miss the file that spelled it differently."
  #"vaelii\.multi-jvm")

(def ^:private raw-fork
  "Forking without the helper.  `ProcessHandle` is deliberately absent: `disk_backend_test`
  reads its own pid with it and forks nothing."
  #"ProcessBuilder")

(def ^:private mark-pattern
  "The mark as it is written on a `deftest` name.  With the caret, since a test whose
  NAME contains the words — the roster test below does — is not a marked test."
  #"\^:multi-jvm")

(def ^:private roster
  "Every test that forks a JVM, by name.  A roster rather than a count, so adding one is
  a visible change in this file: these run under no selector but their own, and a
  cross-process test nobody can see is a cross-process test nobody runs."
  #{"a-second-jvm-holding-the-directory-is-refused-by-name"
    "a-killed-writer-leaves-no-lock-to-reap"
    "a-kb-another-process-wrote-opens-cold-and-recovers"
    "a-daemon-in-another-process-answers-this-one-s-client"
    "a-killed-logged-writer-restores-to-a-prefix-of-its-operations"})

(defn- test-sources
  "Every test namespace's source, as `path -> text`."
  []
  (into {} (for [^File f (file-seq (io/file "test"))
                 :when (str/ends-with? (.getName f) "_test.clj")]
             [(.getPath f) (slurp f)])))

(defn- top-level-forms
  "The source text of each top-level form — split on a `(` in column zero rather than
  read, since what is under test is the text a reviewer sees, metadata included."
  [text]
  (let [lines  (vec (str/split-lines text))
        starts (keep-indexed (fn [i line] (when (str/starts-with? line "(") i)) lines)]
    (for [[from to] (map vector starts (concat (rest starts) [(count lines)]))]
      (str/join "\n" (subvec lines from to)))))

(defn- fork-pattern
  "How forking is spelled *in this file*: the alias it bound the helper to, or — when it
  names the helper without one — the helper itself.  nil when the file cannot fork."
  [text]
  (when (re-find helper-ns text)
    (if-let [alias (second (re-find #"\[vaelii\.multi-jvm\s+:as\s+([^\]\s]+)\]" text))]
      (re-pattern (str (java.util.regex.Pattern/quote (str alias "/"))))
      helper-ns)))

(defn- test-forms
  "The `deftest` forms of one file, as `{:name :form}`."
  [text]
  (for [form (top-level-forms text)
        :let [[_ nm] (re-find #"^\((?:tu/)?deftest(?:-kb)?\s+(?:\^\S+\s+)*([^\s\n]+)" form)]
        :when nm]
    {:name nm :form form}))

(defn- forking-tests
  "Every test in the tree whose own source forks a JVM."
  []
  (for [[path text] (test-sources)
        :let [alias-pat (fork-pattern text)]
        {:keys [name form]} (test-forms text)
        :when (or (re-find raw-fork form) (and alias-pat (re-find alias-pat form)))]
    {:path path :name name :head (first (str/split-lines form))}))

(deftest a-test-that-forks-a-jvm-carries-the-multi-jvm-mark
  (let [forking  (forking-tests)
        unmarked (remove #(re-find mark-pattern (:head %)) forking)]
    (is (seq forking) "the scan found the tests that fork a JVM")
    (is (empty? unmarked)
        (str "these fork a JVM without `^:multi-jvm`, so `lein test` would run them: "
             (pr-str (map (juxt :path :name) unmarked))))
    (testing "and the marked tests are the ones we think they are"
      (is (= roster (into #{} (map :name) forking))
          "a forking test was added or renamed without updating the roster above"))))
