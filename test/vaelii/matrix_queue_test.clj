;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.matrix-queue-test
  "The matrix's shared state and the gate slots in `scripts/lib/slots.sh`, and the refusal
  `scripts/test-matrix.sh` gives during the cooldown after a red run.

  Each test runs the shell in a scratch git repository of its own, so the lock, the
  queue and the `red` file it writes land in that repository's `.git/vaelii-matrix`, and
  the gate slots in its `.git/box-state`, never where a live matrix or `lein gate` reads
  them."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files StandardCopyOption]
           [java.nio.file.attribute FileAttribute]))

(def ^:private checkout (.getCanonicalPath (io/file ".")))

(def ^:private env
  "This JVM's environment less the variables the scripts read, so a caller's session
  id, cooldown or git directory cannot reach the scratch repository."
  (apply dissoc (into {} (System/getenv))
         "EDIT_SESSION" "MATRIX_RED_COOLDOWN" "MATRIX_REQUESTED_BY" "MATRIX_OWED_MAX"
         "MATRIX_YIELD" "MATRIX_JOBS" "TEST_MATRIX_OUT" "GIT_DIR" "GIT_WORK_TREE"
         "GIT_INDEX_FILE" "GATE_MAX_CONCURRENT" "GATE_NO_WAIT" "PERF_NO_WAIT"))

(defn- box-state
  "The scratch repository's `VAELII_BOX_STATE_DIR`, in place of the box's."
  [^File dir]
  (tu/posix-path (io/file dir ".git" "box-state")))

(defn- run [^File dir extra & args]
  (apply shell/sh (concat args [:dir dir :env (merge env {"VAELII_BOX_STATE_DIR" (box-state dir)}
                                                     extra)])))

(defn- git! [^File dir & args]
  (let [{:keys [exit err out]} (apply run dir {} "git" "-c" "user.name=t" "-c" "user.email=t@t"
                                      "-c" "commit.gpgsign=false" args)]
    (assert (zero? exit) err)
    (str/trim out)))

(defn- with-repo
  "Call `f` with a scratch repository holding two commits, and delete it after."
  [f]
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees neither this checkout nor the scratch repository"
    (let [dir (.toFile (Files/createTempDirectory "vaelii-matrix-" (into-array FileAttribute [])))]
      (try (git! dir "init" "-q")
           (git! dir "commit" "-q" "--allow-empty" "-m" "one")
           (git! dir "commit" "-q" "--allow-empty" "-m" "two")
           (f dir)
           (finally (doseq [^File x (reverse (file-seq dir))] (.delete x)))))))

(defn- slots
  "Run `body` in `dir` with `scripts/lib/slots.sh` sourced; its trimmed stdout."
  ([dir body] (slots dir {} body))
  ([dir extra body]
   (let [{:keys [exit out err]} (run dir extra tu/bash "-c"
                                     (str ". " (tu/posix-path checkout) "/scripts/lib/slots.sh && " body))]
     (assert (zero? exit) err)
     (str/trim out))))

(def ^:private bash-path
  "The absolute path of `tu/bash`, for a stub's `#!`: Termux has no `/usr/bin/env`."
  (delay (:out (shell/sh tu/bash "-c" "printf %s \"$BASH\""))))

(defn- live-holder
  "A shell fragment that starts a process whose command line names `script` as `$h`, and
  kills it on exit.  `exec -a` cannot rename `sleep`: a multi-call coreutils (Termux,
  busybox) dispatches on argv[0]."
  [^File dir script]
  (spit (io/file dir script) "trap 'kill $! 2>/dev/null; exit' TERM\nsleep 300 &\nwait\n")
  (str "{ \"$BASH\" " script " & h=$!; trap 'kill $h' EXIT; }"))

(deftest a-queue-take-merges-the-requests-and-empties-the-queue
  (with-repo
    (fn [dir]
      (let [one (git! dir "rev-parse" "HEAD~1")
            two (git! dir "rev-parse" "HEAD")]
        (testing "the commit every baseline descends from, the selector, the requesters joined"
          ;; a line queued before requesters were recorded has two fields, and adds none
          (slots dir (str "printf '%s :default\\n' " two " >>\"$(matrix_state_dir)/queue\""))
          (slots dir (str "matrix_queue_add " two " :default user:b"))
          (slots dir (str "matrix_queue_add " one " :default session:a"))
          (is (= (str one " :default session:a,user:b") (slots dir "matrix_queue_take"))))
        (testing "a take empties the queue"
          (is (= "" (slots dir "matrix_queue_take"))))
        (testing "requests under different selectors run at :all"
          (slots dir (str "matrix_queue_add " two " :default user:b"))
          (slots dir (str "matrix_queue_add " two " :slow user:b"))
          (is (= (str two " :all user:b") (slots dir "matrix_queue_take"))))))))

(deftest the-requester-is-the-session-else-the-login
  (with-repo
    (fn [dir]
      (is (= "session:s1" (slots dir {"EDIT_SESSION" "s1"} "matrix_requester")))
      (is (= "user:someone" (slots dir {"USER" "someone"} "matrix_requester"))))))

(deftest a-stale-lock-is-broken-only-while-it-holds-the-line-read
  (with-repo
    (fn [dir]
      (let [lock (fn [] (slots dir "cat \"$(matrix_state_dir)/lock\" 2>/dev/null || true"))]
        (slots dir "printf 'stale\\n' >|\"$(matrix_state_dir)/lock\"")
        (slots dir "lock_break_stale \"$(matrix_state_dir)/lock\" stale")
        (is (= "" (lock)) "the stale line is removed")
        (slots dir "printf 'live\\n' >|\"$(matrix_state_dir)/lock\"")
        (slots dir "lock_break_stale \"$(matrix_state_dir)/lock\" stale")
        (is (= "live" (lock)) "a lock taken since the read stays")
        (slots dir "rm \"$(matrix_state_dir)/lock\" && : >\"$(matrix_state_dir)/lock\"")
        (slots dir "lock_break_stale \"$(matrix_state_dir)/lock\" ''")
        (is (true? (.exists (io/file dir ".git/vaelii-matrix/lock")))
            "an empty lock under a minute old is a take in progress, and stays")
        (slots dir "touch -t 202001010000 \"$(matrix_state_dir)/lock\"")
        (slots dir "lock_break_stale \"$(matrix_state_dir)/lock\" ''")
        (is (false? (.exists (io/file dir ".git/vaelii-matrix/lock")))
            "an empty lock a minute old is a taker killed before its write, and is broken")
        (is (= "" (slots dir "ls \"$(matrix_state_dir)\" | grep -F .stale. || true"))
            "no renamed copy is left behind")))))

(deftest a-gate-slot-is-taken-only-while-one-is-free-or-stale
  (with-repo
    (fn [dir]
      ;; `gate_slot_take` reads a slot as held while its pid is alive and runs gate.sh or
      ;; test-parallel.sh. The shell starts that holder itself as `$h`, so this test forks no
      ;; JVM (multi_jvm_test).
      (let [take-slot (fn [slot-2]
                        (run dir {"GATE_NO_WAIT" "1"} tu/bash "-c"
                             (str ". " (tu/posix-path checkout) "/scripts/lib/slots.sh"
                                  " && " (live-holder dir "gate.sh")
                                  " && d=$(box_state_dir)"
                                  " && printf '%s\\n' \"$h abc 0 user:a lein gate\" >|\"$d/gate-lock.1\""
                                  " && printf '%s\\n' \"" slot-2 "\" >|\"$d/gate-lock.2\""
                                  " && gate_slot_take lein gate && basename \"$GATE_SLOT\"")))]
        (let [{:keys [exit err]} (take-slot "$h abc 0 user:b lein gate")]
          (is (= 75 exit) "GATE_NO_WAIT exits 75 while both slots are held")
          (is (and (str/includes? err "user:a") (str/includes? err "user:b"))
              "the refusal names every holder"))
        ;; above macOS's and Linux's default pid ceilings, so no process holds it
        (let [{:keys [exit out]} (take-slot "9999999 abc 0 user:c lein gate")]
          (is (= 0 exit))
          (is (= "gate-lock.2" (str/trim out)) "a dead holder's slot is broken and taken"))
        (is (= "" (slots dir {"GATE_MAX_CONCURRENT" "0" "GATE_NO_WAIT" "1"}
                         "gate_slot_take lein gate && printf %s \"$GATE_SLOT\""))
            "a cap of 0 takes no slot")))))

(deftest a-gate-slot-taken-in-one-clone-is-held-in-every-clone
  (with-repo
    (fn [^File a]
      (with-repo
        (fn [^File b]
          ;; `a` takes the one slot from a live test-parallel.sh, as a `lein test-parallel`
          ;; outside `lein gate` does, and writes `taken`; `b` reads the same box state.
          (spit (io/file a "test-parallel.sh")
                (str ". " (tu/posix-path checkout) "/scripts/lib/slots.sh\n"
                     "gate_slot_take lein test-parallel :default && : >taken\n"
                     "trap 'kill $! 2>/dev/null; exit' TERM\nsleep 300 &\nwait\n"))
          (let [a-path (tu/posix-path a)
                {:keys [exit err]}
                (run b {"VAELII_BOX_STATE_DIR" (box-state a) "GATE_MAX_CONCURRENT" "1"
                        "GATE_NO_WAIT" "1"}
                     tu/bash "-c"
                     (str ". " (tu/posix-path checkout) "/scripts/lib/slots.sh"
                          " && { (cd " a-path " && exec \"$BASH\" test-parallel.sh) & h=$!;"
                          " trap 'kill $h' EXIT; }"
                          " && for _ in $(seq 200); do [[ -e " a-path "/taken ]] && break; sleep 0.1; done"
                          " && gate_slot_take lein gate"))]
            (is (= 75 exit) "GATE_NO_WAIT exits 75 in `b` while `a` holds the slot")
            (is (str/includes? err "lein test-parallel :default") "the refusal names the command")
            (is (str/includes? err (.getName a)) "and the checkout the holder runs in")))))))

(deftest the-locks-take-and-restore-without-hard-links
  (with-repo
    (fn [^File dir]
      ;; Android refuses link(2); this `ln` refuses every call the same way
      (let [stub (io/file dir "nolink/ln")
            env' {"PATH" (str (tu/posix-path (.getParentFile stub)) ":" (get env "PATH"))}]
        (io/make-parents stub)
        (spit stub (str "#!" @bash-path "\nexit 1\n"))
        (.setExecutable stub true)
        (slots dir env' "printf 'live\\n' >|\"$(matrix_state_dir)/lock\"")
        (slots dir env' "lock_break_stale \"$(matrix_state_dir)/lock\" stale")
        (is (= "live" (slots dir "cat \"$(matrix_state_dir)/lock\""))
            "a lock taken since the read goes back")
        (is (= "" (slots dir env' (str "matrix_lock_take abc /r"
                                       " && [[ \"$(cut -d' ' -f2 \"$(matrix_state_dir)/lock\")\" == abc ]]"
                                       " || printf refused")))
            "the matrix lock breaks a dead holder's line and is taken")
        ;; the take runs beside a watchdog, so a take that never succeeds fails in 20s
        ;; rather than waiting forever on the dead holder it keeps breaking
        (is (= "gate-lock"
               (slots dir (assoc env' "GATE_MAX_CONCURRENT" "1")
                      (str "printf '9999999 abc 0 user:c lein gate\\n' >|\"$(box_state_dir)/gate-lock\""
                           " && { gate_slot_take lein gate && basename \"$GATE_SLOT\"; } & p=$!"
                           "; { sleep 20; kill $p; } 2>/dev/null & w=$!"
                           "; wait $p; kill $w 2>/dev/null; true")))
            "a dead holder's slot is broken and taken")))))

(deftest the-configurations-a-yield-stopped-are-listed-until-a-run-takes-them
  (with-repo
    (fn [dir]
      (slots dir "matrix_yield_stopped_add rete disk-log")
      (slots dir "matrix_yield_stopped_add rete")
      (is (= "disk-log\nrete" (slots dir "matrix_yield_stopped")) "each listed once")
      (slots dir "matrix_yield_stopped_take rete memory")
      (is (= "disk-log" (slots dir "matrix_yield_stopped")) "a take removes what it names")
      (slots dir "matrix_yield_stopped_take disk-log")
      (is (= "" (slots dir "matrix_yield_stopped"))))))

(deftest the-cooldown-holds-from-a-red-until-it-expires-or-a-green
  (with-repo
    (fn [dir]
      (let [red (fn [age] (slots dir (str "printf '%s /r\\n' $(( $(date +%s) - " age " ))"
                                          " >|\"$(matrix_state_dir)/red\"")))]
        (slots dir "matrix_red_mark /r")
        (is (str/ends-with? (slots dir "matrix_red_recent") " /r") "a red just marked holds")
        (is (= "" (slots dir {"MATRIX_RED_COOLDOWN" "0"} "matrix_red_recent"))
            "a cooldown of 0 turns it off")
        (red 1801)
        (is (= "" (slots dir "matrix_red_recent")) "past the default 1800 seconds it lapses")
        (is (not= "" (slots dir {"MATRIX_RED_COOLDOWN" "3600"} "matrix_red_recent"))
            "a longer cooldown still holds it")
        (red 0)
        (slots dir "matrix_red_clear")
        (is (= "" (slots dir "matrix_red_recent")) "a green clears it")))))

(defn- copy-scripts! [^File dir]
  (doseq [rel (cons "scripts/test-matrix.sh"
                    (for [^File f (.listFiles (io/file checkout "scripts/lib"))]
                      (str "scripts/lib/" (.getName f))))]
    (let [to (io/file dir rel)]
      (io/make-parents to)
      (Files/copy (.toPath (io/file checkout rel)) (.toPath to)
                  ^"[Ljava.nio.file.CopyOption;" (into-array [StandardCopyOption/REPLACE_EXISTING])))))

(deftest a-matrix-in-the-cooldown-refuses-and-names-the-red-run
  (with-repo
    (fn [^File dir]
      (copy-scripts! dir)
      (let [run-dir (io/file dir "logs/test-matrix/run-1")
            t       "vaelii.some-test/a-failing-test"]
        (.mkdirs run-dir)
        (spit (io/file run-dir "summary.tsv")
              (str "config\tkind\trevision\tstate\tseconds\tsummary\tcounts\n"
                   "rete\tsweep\tabc12345\tfailed\t60\t\t\n"
                   "disk-snapshot\tbackend\tabc12345\tfailed\t60\t\t\n"
                   "overlay\tbackend\tabc12345\tfailed\t60\t\t\n"))
        (spit (io/file run-dir "failures.tsv") (str t "\tdisk-snapshot\n" t "\trete\n"))
        (spit (io/file run-dir "requested-by") "session:s1\n")
        (spit (io/file run-dir "queue-dropped") "0123456789ab :default session:s2,user:u\n")
        (slots dir (str "matrix_red_mark " (tu/posix-path run-dir)))
        (let [{:keys [exit out]} (run dir {} tu/bash "scripts/test-matrix.sh" "--no-tty" "memory")]
          (is (= 75 exit) "the refusal is exit 75, the not-started status")
          (testing "the notice names the red run and whose it was"
            (is (str/includes? out (tu/posix-path run-dir)))
            (is (str/includes? out "revision:   abc12345"))
            (is (str/includes? out "in charge:  session:s1")))
          (testing "the requests the red run dropped are named"
            (is (str/includes? out "session:s2, user:u (--owed=01234567 :default), not run")))
          (testing "each failing test with its configurations and a one-configuration re-run"
            (is (str/includes? out (str t " — disk-snapshot rete")))
            (is (str/includes? out (str "env VAELII_TEST_BACKEND=disk-snapshot lein test :only " t))))
          (testing "a configuration that failed without naming a test points at its log"
            (is (str/includes? out "overlay — no failing test named")))
          (is (not (.exists (io/file dir ".git/vaelii-matrix/lock"))) "no lock was taken"))))))

(def ^:private fake-lein
  "The body of a `lein`, below its `#!`: its first call exits `$FAKE_FIRST` at once, its
  second and third sleep until killed, and later calls pass.  `mkdir` numbers the calls
  atomically."
  (str "k=1; until mkdir \"$FAKE/s$k\" 2>/dev/null; do k=$((k + 1)); done\n"
       "(( k == 1 )) && exit \"${FAKE_FIRST:-0}\"\n"
       "(( k <= 3 )) && exec sleep 300\n"
       "exit 0\n"))

(defn- run-owed-behind-a-request
  "In a fresh repository whose last commit owes the three disk configurations, queue a
  request and run `--owed` over a fake `lein`; the run's result and the repository."
  [^File dir first-exit]
  (copy-scripts! dir)
  (spit (io/file dir ".gitignore") "scripts/\nlogs/\ntestbench/\nfake/\n")
  (io/make-parents (io/file dir "src/vaelii/impl/disk/x.clj"))
  (spit (io/file dir "src/vaelii/impl/disk/x.clj") "x\n")
  (git! dir "add" ".")
  (git! dir "commit" "-q" "-m" "three")
  (let [fake (io/file dir "fake")
        lein (io/file fake "bin/lein")
        base (git! dir "rev-parse" "HEAD~1")]
    (io/make-parents lein)
    (spit lein (str "#!" @bash-path "\n" fake-lein))
    (.setExecutable lein true)
    (slots dir (str "matrix_queue_add " base " :default session:waiting"))
    (run dir {"FAKE" (tu/posix-path fake) "FAKE_FIRST" (str first-exit) "MATRIX_JOBS" "3"
              "PATH" (str (tu/posix-path (io/file fake "bin")) ":" (get env "PATH"))}
         tu/bash "scripts/test-matrix.sh" "--no-tty" (str "--owed=" base))))

(defn- summaries [^File dir]
  ;; `run-*` only: `latest` links to one of them
  (->> (.listFiles (io/file dir "logs/test-matrix"))
       (filter #(str/starts-with? (.getName ^File %) "run-"))
       (keep #(let [f (io/file % "summary.tsv")] (when (.exists f) (slurp f))))))

(deftest ^:slow an-owed-run-behind-a-queued-request-ends-at-its-first-verdict
  (testing "a green first verdict yields: the rest stop, and the next matrix runs them"
    (with-repo
      (fn [^File dir]
        (let [{:keys [exit out]} (run-owed-behind-a-request dir 0)
              ;; the yield starts the next matrix detached; wait for it to release the lock
              done? #(and (= 2 (count (summaries dir)))
                          (not (.exists (io/file dir ".git/vaelii-matrix/lock"))))
              _     (loop [n 0] (when (and (not (done?)) (< n 300)) (Thread/sleep 200) (recur (inc n))))
              rows  (summaries dir)]
          (is (= 75 exit) "a yield exits 75, the queued status")
          (is (str/includes? out "yielded to a queued request"))
          (is (= [0 2] (sort (map #(count (re-seq #"\tstopped\t" %)) rows)))
              "the yielding run stopped two, and the next matrix stopped none")
          (is (= "" (slots dir "matrix_yield_stopped"))
              "the next matrix took the two stopped configurations off `yield-stopped`")
          (is (= 0 (:exit (run dir {} tu/bash "scripts/test-matrix.sh" "--no-tty"
                               "--covered=HEAD~1..HEAD")))
              "the next matrix covers every configuration the yielding run stopped")))))
  (testing "a red first verdict halts the run and drops the queue"
    (with-repo
      (fn [^File dir]
        (let [{:keys [exit]} (run-owed-behind-a-request dir 1)]
          (is (= 1 exit))
          (is (= 1 (count (summaries dir))) "no next matrix starts")
          (is (= 2 (count (re-seq #"\tstopped\t" (first (summaries dir))))))
          (is (not= "" (slots dir "matrix_red_recent")) "the cooldown holds"))))))
