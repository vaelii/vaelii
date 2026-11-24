;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.multi-jvm
  "Forking a second JVM, for the tests that cannot be written without one.

  Not a test namespace — support, the way `vaelii.world` and `vaelii.test-util` are, so
  `lein test` never selects it.  What it is scaffolding *for* is `vaelii.multi-jvm-test`
  and the `^:multi-jvm` mark it carries (CONTRIBUTING.md §5).

  **A child is `java -cp` on this JVM's own classpath**, never `lein`.  Leiningen resolves
  the classpath once, into `java.class.path` — `src`, `test`, the resource directories and
  every jar — so a child inherits it for the cost of reading a system property.  Shelling
  out to `lein classpath` per child would charge each one a dependency resolution, and
  spawning `lein` itself would charge twenty seconds of boot for three seconds of work.

  **The handshake is a marker line, never a sleep.**  A child prints `##vaelii## <word>`
  when it reaches a state the parent is waiting for, and the parent blocks on that line
  with a deadline.  The prefix is there because a child's own logging shares the stream:
  a bare `HELD` would match a trove line quoting the word.  Nothing here polls, and
  nothing waits a fixed interval and hopes.

  Every child's stderr is folded into its stdout and kept, so a failure reports the
  child's transcript — a stack trace in a process the test framework cannot see is
  otherwise a timeout with no cause attached."
  (:require [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.io BufferedWriter File]
           [java.lang.management ManagementFactory]
           [java.util.concurrent LinkedBlockingQueue TimeUnit]))

(def marker
  "The prefix a child puts on a line the parent is allowed to synchronize on.  Long
  enough that nothing else in the stream carries it."
  "##vaelii##")

(defn- java-binary
  "This JVM's own `java`, rather than whatever is first on `PATH` — the child has to be
  the version the classpath was built for."
  ^String []
  (str (System/getProperty "java.home") File/separator "bin" File/separator "java"))

(defn- inherited-options
  "This JVM's own `--` options — `project.clj`'s native-access and `sun.misc.Unsafe`
  flags, and a profile's `--add-opens` — so a child runs under the permissions the parent
  does, and its transcript carries no JDK warning the parent's run does not.  The
  `-Xmx` options come along in order, so a child's heap ceiling is the parent's."
  []
  (filterv #(or (str/starts-with? % "--") (str/starts-with? % "-Xmx"))
           (.getInputArguments (ManagementFactory/getRuntimeMXBean))))

(def ^:private default-signals
  "A `python3` prefix that sets every ignored signal back to its default and then execs
  the child in place, so the child keeps the pid the parent spawned.  An ignored signal
  survives `exec`, and `nohup` starts a run with SIGHUP ignored.  HotSpot installs no
  shutdown handler for a SIGHUP ignored at startup, so without the prefix a child under
  such a run outlives `signal!`.  Python ignores SIGPIPE and SIGXFSZ itself, and the same
  loop resets those."
  ["python3" "-I" "-c"
   (str "import os, signal, sys\n"
        "for s in signal.valid_signals():\n"
        "    try:\n"
        "        if signal.getsignal(s) == signal.SIG_IGN: signal.signal(s, signal.SIG_DFL)\n"
        "    except (OSError, ValueError): pass\n"
        "os.execv(sys.argv[1], sys.argv[1:])\n")])

(defn- pump!
  "Drain `proc`'s merged output into `queue`, keeping every line in `transcript`.  A
  daemon thread, so a child that outlives its test cannot hold the JVM open; the read
  throws when the process dies, which is the normal end and not an error."
  [proc queue transcript]
  (doto (Thread.
         (fn []
           (try
             (with-open [r (io/reader (.getInputStream ^Process proc))]
               (doseq [line (line-seq r)]
                 (swap! transcript conj line)
                 (.put ^LinkedBlockingQueue queue line)))
             (catch Exception _ nil)))
         "vaelii-child-output")
    (.setDaemon true)
    (.start)))

(defn spawn!
  "Start `source` (a Clojure program, as text) in a child JVM and return a handle.

  `args` reach the child as `*command-line-args*`, stringified.  The source is written to
  a temp file rather than passed with `-e`: a program long enough to be worth reading is
  long enough that quoting it as one argument stops being reviewable."
  [source & args]
  (let [script (File/createTempFile "vaelii-child-" ".clj")
        _      (spit script source)
        cmd    (-> default-signals
                   (conj (java-binary))
                   (into (inherited-options))
                   (into ["-cp" (System/getProperty "java.class.path")
                          "clojure.main" (.getPath script)])
                   (into (map str args)))
        proc   (-> (ProcessBuilder. ^java.util.List cmd)
                   (.redirectErrorStream true)
                   (.start))
        queue  (LinkedBlockingQueue.)
        transcript (atom [])]
    (pump! proc queue transcript)
    {:process proc :queue queue :transcript transcript :script script
     :stdin (io/writer (.getOutputStream proc))}))

(defn pid
  "The child's process id — what the lock file's holder tag has to name."
  [child]
  (.pid ^Process (:process child)))

(defn transcript
  "Every line the child has printed, for a failure message."
  [child]
  @(:transcript child))

(defn await-marker!
  "Block until the child prints `##vaelii## <word>`, and return whatever it wrote after
  the word — `\"\"` when the marker is the whole line.  So a child says *that* it reached
  a state with the word, and says *what* it found with the remainder: the port it bound,
  the handle it wrote.

  Throws with the transcript attached on timeout — the diagnosis a test wants is what the
  child said instead, which is almost always a stack trace it printed and exited on."
  ([child word] (await-marker! child word 90000))
  ([child word timeout-ms]
   (let [want     (str marker " " word)
         deadline (+ (System/currentTimeMillis) timeout-ms)]
     (loop []
       (let [left (- deadline (System/currentTimeMillis))]
         (when-not (pos? left)
           (throw (ex-info (str "child never printed " (pr-str want))
                           {:type ::no-marker :want want :transcript (transcript child)})))
         (if-let [line (.poll ^LinkedBlockingQueue (:queue child) left TimeUnit/MILLISECONDS)]
           (cond
             (= want line)                          ""
             (.startsWith ^String line (str want " ")) (subs line (inc (count want)))
             :else                                  (recur))
           (recur)))))))

(defn tell!
  "Send `line` to the child's stdin.  How a child blocked on `read-line` is released."
  [child line]
  (doto ^BufferedWriter (:stdin child)
    (.write (str line "\n"))
    (.flush)))

(defn await-exit!
  "Wait for the child to exit and return its status, or throw with the transcript."
  ([child] (await-exit! child 90000))
  ([child timeout-ms]
   (if (.waitFor ^Process (:process child) timeout-ms TimeUnit/MILLISECONDS)
     (.exitValue ^Process (:process child))
     (throw (ex-info "child did not exit"
                     {:type ::no-exit :transcript (transcript child)})))))

(defn kill!
  "SIGKILL the child and wait for the OS to reap it — the crash a clean shutdown cannot
  stage.  Returns when the process is gone, so what a test asserts next is asserted
  against a directory whose writer no longer exists."
  [child]
  (.destroyForcibly ^Process (:process child))
  (.waitFor ^Process (:process child) 30 TimeUnit/SECONDS))

(defn signal!
  "Send the child signal `sig`, a name `kill` takes (\"HUP\", \"TERM\").  A JVM runs its
  shutdown hooks for either, so this is how a test stages a clean stop the child did not
  ask for."
  [child sig]
  (let [argv (into-array String ["kill" (str "-" sig) (str (pid child))])]
    (.waitFor (.start (ProcessBuilder. ^"[Ljava.lang.String;" argv)))))

(defn close!
  "Kill the child if it is still up, and drop its script."
  [child]
  (try (kill! child) (catch Exception _ nil))
  (.delete ^File (:script child)))

(defmacro with-child
  "Run `body` with `binding` bound to a child running `source` (plus `args`), killing it
  and deleting its script afterwards however the body leaves."
  [[binding source & args] & body]
  `(let [~binding (spawn! ~source ~@args)]
     (try ~@body (finally (close! ~binding)))))
