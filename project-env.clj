;; The major version of the JDK evaluating this file, which is the one leiningen
;; launches the project JVM on. The top-level `:jvm-opts` and the `:zgc` profile
;; name flags that only some versions accept, and an unrecognized `--` or `-XX:`
;; flag stops the JVM from booting.
(def jdk-major
  (Integer/parseInt
   (second (re-find #"^(?:1\.)?(\d+)" (System/getProperty "java.specification.version")))))

;; The bash every script alias runs, and the one the suite runs scripts with (the
;; `:test` profile hands it on as `vaelii.test.bash`).  `VAELII_BASH` when set; else, on
;; Windows, Git's, when it is installed; else whatever `bash` resolves to.  Windows needs
;; the middle step because it resolves a bare `bash` in System32 *before* `PATH`, so
;; where WSL is installed `bash` is WSL's whatever `PATH` says — a Linux that sees
;; neither this JVM's paths nor its environment, and needs its own copy of every tool.
;; Git's bash runs the Windows ones.  `VAELII_BASH=bash` asks for WSL's regardless.
;; Git's is looked for beside a `git.exe` on `PATH` (an install's `cmd\`, next to its
;; `bin\`), then where the machine-wide, per-user and Scoop installs put it.
(def bash
  (or (some-> (System/getenv "VAELII_BASH") .trim not-empty)
      (when (.startsWith (.toLowerCase (System/getProperty "os.name")) "windows")
        ;; the OS's own variables, read through `env`: config_surface_test's scan is
        ;; for vaelii's switches, and none of these is one
        (let [env      #(some-> (System/getenv %) not-empty)
              on-path  (for [d (.split (str (env "PATH")) java.io.File/pathSeparator)
                             :when (and (not-empty d) (.isFile (java.io.File. d "git.exe")))]
                         (some-> (java.io.File. d) .getParentFile (java.io.File. "bin/bash.exe")))
              installs (keep (fn [[base sub]] (some-> (env base) (java.io.File. sub)))
                             [["ProgramFiles" "Git/bin/bash.exe"]
                              ["LOCALAPPDATA" "Programs/Git/bin/bash.exe"]
                              ["SCOOP" "apps/git/current/bin/bash.exe"]
                              ["USERPROFILE" "scoop/apps/git/current/bin/bash.exe"]])]
          ;; `/`-separated: lein-shell reads `\` as its escape and would drop each one
          (some #(when (.isFile ^java.io.File %) (.replace (.getPath ^java.io.File %) \\ \/))
                (concat on-path installs))))
      "bash"))

;; The `:test` profile's heap and collector flags. A test JVM's live set after a full
;; collection is 0.22-0.43 GB (three matrix configurations, 2026-10-10), and with no
;; `-Xmx` the ceiling is a quarter of RAM, so G1 grew each JVM to 1-2 GB of mostly dead
;; young generation; a dozen of them beside a full-KB load paged the machine.
;;
;; `VAELII_TEST_HEAP` sets the ceiling, 4g by default. A `JVM_OPTS` that already names
;; `-Xmx` keeps it (`lein test-full-kb` passes `VAELII_HEAP`'s there), because leiningen
;; places these flags after `JVM_OPTS` and the last `-Xmx` wins. The free-ratio pair and
;; the periodic collection return freed heap to the OS between tests. Two parallel and
;; one concurrent collector thread per JVM keep a dozen concurrent suites from running
;; ~100 collector threads on ten cores.
;;
;; `VAELII_TEST_TMPDIR` becomes the test JVM's `java.io.tmpdir`, which every directory a
;; test builds is created under: the disk backends' stores, `tu/temp-dir` and the
;; `^:fuzz` probes. A RAM disk there keeps the suite's stores and fsyncs off the SSD.
(def test-jvm-opts
  (let [heap     (some-> (System/getenv "VAELII_TEST_HEAP") .trim not-empty)
        tmpdir   (some-> (System/getenv "VAELII_TEST_TMPDIR") .trim not-empty)
        ;; the launcher's variable, read through `env` for the reason `bash` gives
        env      #(System/getenv %)
        jvm-opts (str (env "JVM_OPTS"))]
    (cond-> ["-XX:MinHeapFreeRatio=10" "-XX:MaxHeapFreeRatio=30"
             "-XX:G1PeriodicGCInterval=15000" "-XX:ParallelGCThreads=2" "-XX:ConcGCThreads=1"]
      (or heap (not (re-find #"-Xmx" jvm-opts))) (conj (str "-Xmx" (or heap "4g")))
      tmpdir                                     (conj (str "-Djava.io.tmpdir=" tmpdir)))))
