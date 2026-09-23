(defproject com.vaelii/vaelii "0.21.1-SNAPSHOT"
  :description "Vaelii — a contextualized common-sense knowledge base with a
                count-aware trie index, forward/backward inference,
                and JTMS truth maintenance, over an in-memory or on-disk store."
  :url "https://github.com/vaelii/vaelii"
  :license {:name "SSPL-1.0"
            :url "https://www.mongodb.com/licensing/server-side-public-license"}
  ;; Generated into the POM. A Clojars page without it offers a reader no route
  ;; from the artifact back to the source it was built from.
  :scm {:name "git" :url "https://github.com/vaelii/vaelii"}
  ;; `lein deploy clojars` reads the credentials from the environment rather than
  ;; from here — a token in project.clj is a token in the public tree. The pair is
  ;; CLOJARS_USERNAME and a Clojars DEPLOY TOKEN as CLOJARS_PASSWORD, never the
  ;; account password; ~/.lein/credentials.clj.gpg is the other supported route
  ;; and needs no change here.
  ;;
  ;; `:sign-releases false` because Clojars does not require a signature and the
  ;; default is to try: without a GPG key on the machine the deploy fails at the
  ;; signing step, after the artifact has been built and named.
  :deploy-repositories [["clojars" {:url "https://repo.clojars.org/"
                                    :username :env/clojars_username
                                    :password :env/clojars_password
                                    :sign-releases false}]]
  ;; README states this too, so it is refused rather than claimed. 2.10 rather than
  ;; 2.9 because `:preserve-eval-meta` below needs it: on 2.9 the key is silently
  ;; ignored and every `lein run` prints the reflection warning it exists to suppress.
  :min-lein-version "2.10.0"
  :dependencies [[org.clojure/clojure "1.12.6"]
                 [com.taoensso/nippy "3.9.0"]
                 [com.taoensso/trove "1.2.0"]
                 [metosin/reitit-ring "0.10.1"]
                 [ring/ring-core "1.15.5"]
                 [ring/ring-jetty-adapter "1.15.5"]
                 ;; escapes body position as well as attributes, so KB content and
                 ;; query params cannot inject markup (docs/web.md)
                 [hiccup "2.0.0"]
                 ;; clasp's `--outf=2` JSON, and libclingo through JNA (docs/asp.md)
                 [cheshire "6.2.0"]
                 [net.java.dev.jna/jna "5.19.1"]
                 ;; the dense and columnar index backends, both off by default
                 ;; (docs/density.md)
                 [org.roaringbitmap/RoaringBitmap "1.6.23"]
                 [it.unimi.dsi/fastutil-core "8.5.19"]
                 ;; XZ (LZMA2) for the exporter's `:xz`. nippy brings it transitively;
                 ;; naming it is what makes the codec a promise rather than an accident
                 ;; of somebody else's dependency graph (docs/api.md).
                 [org.tukaani/xz "1.12"]]
  :main ^:skip-aot vaelii.core
  :target-path "target/%s"
  ;; an unhinted interop call names itself at compile time instead of paying a silent
  ;; runtime lookup.  The flag only warns — but `scripts/check-reflection.sh` greps the
  ;; output and fails on it, so a warning does stop the build: `lein lint`'s `reflect`
  ;; row compiles src and bench, and `scripts/gate.sh` reads the test stage's log for
  ;; the tree that pass does not compile.  Both halves are covered, and the allow-list
  ;; is empty because a warning here is a defect to fix at the call site with a hint.
  :global-vars {*warn-on-reflection* true}
  ;; leiningen `pr-str`s the form it evaluates into a temp file, and that drops
  ;; metadata — including the `^Class` hint in leiningen's own `run` form, which the
  ;; line above then reports as a reflection warning on every `lein run`. This keeps
  ;; the hint. Needs lein 2.10+; an older one ignores the key.
  :preserve-eval-meta true
  ;; Three marks, each deferring a test for its own reason: `^:slow` a test costing
  ;; about a second or more, `^:llm` one that can reach a model provider, `^:multi-jvm`
  ;; one that forks a second JVM. What each selects, and the separate consent gate
  ;; beside the llm one: CONTRIBUTING.md §5.
  ;; **Two of the three are opt-in only**, so neither `:default` nor `:all` selects
  ;; them and every other selector has to exclude them by name. `:all` is therefore
  ;; not `(complement :llm)`: a complement of one mark silently adopts the next one
  ;; added, which is how a forked JVM would end up in the fast gate.
  ;; `[m & _]`, not `#(… %)`: `lein test :slow some.ns` hands the selector the trailing
  ;; `some.ns` as an argument — leiningen splits namespaces (symbols) from selectors and
  ;; passes the var metadata first, then any tokens after the selector — so a one-arg
  ;; selector throws ArityException there. Swallow the rest; filter on the metadata alone.
  ;; **A bare keyword is not a shorthand for that**, and it fails the same way and
  ;; silently: `(:llm m "some.ns")` is a lookup with a DEFAULT, so the trailing
  ;; namespace becomes the answer for every test whose metadata lacks the key, and
  ;; `lein test :llm some.ns` runs the whole suite instead of one marked namespace.
  ;; Every selector here is a fn for that reason.
  :test-selectors {:default   (fn [m & _] (not (or (:slow m) (:llm m) (:multi-jvm m) (:fuzz m))))
                   :slow      (fn [m & _] (and (:slow m) (not (or (:llm m) (:multi-jvm m) (:fuzz m)))))
                   :llm       (fn [m & _] (boolean (:llm m)))
                   :multi-jvm (fn [m & _] (boolean (:multi-jvm m)))
                   :fuzz      (fn [m & _] (boolean (:fuzz m)))
                   :all       (fn [m & _] (not (or (:llm m) (:multi-jvm m) (:fuzz m))))}
  ;; Leiningen's `:base` profile supplies the project JVM's `:jvm-opts` when the
  ;; project sets none, and `:base` appends `-XX:+TieredCompilation
  ;; -XX:TieredStopAtLevel=1` whenever the LEIN_JVM_OPTS environment variable
  ;; contains "Tiered" (leiningen.core.project/tiered-jvm-opts). That variable is
  ;; set to shorten leiningen's OWN startup, and leiningen passes the cap on to
  ;; every JVM it forks for the project, so `lein test`, `lein perf` and `lein run`
  ;; compiled the engine with C1 alone and never reached C2. Declaring the vector
  ;; here replaces `:base`'s copy, which carries `^:displace`, and the tiered pair
  ;; stops reaching a project JVM. `-XX:-OmitStackTraceInFastThrow` is `:base`'s
  ;; other entry and is restored here because replacing the vector drops it too:
  ;; the flag reads backwards and KEEPS the stack trace on a repeated implicit
  ;; throw, which a test failure needs to name its site.
  ;;
  ;; This vector cannot reach leiningen's own JVM, which keeps the cap, and a
  ;; plugin task runs there. cljfmt is the one such task, and at C1 alone `lein
  ;; cljfmt check` takes 69-95 s against 31-36 s, so `lint-cljfmt`, `fix` and
  ;; scripts/lint.sh start a second lein with LEIN_JVM_OPTS naming no cap.
  ;;
  ;; No heap size and no collector flag: sizing and `-XX:+UseZGC` stay in the
  ;; profiles that ask for them (`:bench`, `:zgc`), and a profile's `:jvm-opts`
  ;; concatenates onto this vector rather than replacing it.
  :jvm-opts ["-XX:-OmitStackTraceInFastThrow"]
  :profiles {;; `:aot :all` plus a no-op SLF4J binding: silences Jetty's "no providers"
             ;; line inside the standalone jar. Not top-level `:dependencies` — that would
             ;; make it a transitive dependency of every application that depends on
             ;; vaelii, where it can win SLF4J's provider race against the host's own
             ;; logging backend and silence that instead (vaelii.impl.logging holds the
             ;; same line: no backend installs itself unless asked). `:uberjar` is never
             ;; part of the default active profile set, so it never reaches `lein
             ;; pom`/`lein deploy` either — the `:dev` copy below covers `lein
             ;; run`/`test`/`serve`/`browser`, and is dropped when the standalone jar is
             ;; assembled, so this needs its own copy at the same version.
             ;;
             ;; The merge rule keeps every dependency's licence and notice text. Lein
             ;; copies the first jar's entry at a path and drops the rest without a
             ;; word, and `META-INF/LICENSE`/`NOTICE` sit at the same path in many jars:
             ;; commons-codec, the two Jackson dataformats, JNA and both SLF4J jars lost
             ;; theirs, and Apache-2.0 §4(d) and MIT both require the text to travel
             ;; with a redistribution (the Docker image ships this jar). Distinct texts
             ;; are concatenated and a text already present is not repeated.
             :uberjar {:aot :all
                       :dependencies [[org.slf4j/slf4j-nop "2.0.19"]]
                       :uberjar-merge-with
                       {#"^(META-INF/)?(LICENSE|NOTICE)(\.txt|\.md)?$"
                        [slurp
                         (fn [new prev]
                           (if (.contains ^String prev new) prev (str prev "\n\n" new)))
                         spit]}}
             ;; point JNA at libclingo (docs/asp.md). `VAELII_CLINGO_LIB` names the
             ;; directory holding it; the default is Homebrew's on Apple silicon, which
             ;; is where a macOS `brew install clingo` puts it and nowhere a Linux
             ;; package manager does — set the variable there (/usr/lib,
             ;; /usr/local/lib, /usr/lib/x86_64-linux-gnu).
             :with-clingo {:jvm-opts [~(str "-Djna.library.path="
                                            (or (System/getenv "VAELII_CLINGO_LIB")
                                                "/opt/homebrew/lib"))]}
             ;; static analysis, dev-only so none of it reaches an uberjar. Keep
             ;; lein-cloverage's version in step with scripts/coverage.sh, which injects
             ;; the same plugin at the root level so `cloverage` registers under
             ;; `with-profile +test`.
             ;;
             ;; The :uberjar copy of slf4j-nop above covers the standalone jar; :dev is
             ;; part of the default active profile set, so this copy is what silences
             ;; Jetty for `lein run`, `lein test`, `lein serve` and `lein browser`. A
             ;; :dev dependency carries Maven scope `test` in the generated POM
             ;; (leiningen.core.project's default-profile-metadata), so `lein pom`/`lein
             ;; deploy` declare it but a consumer's tooling never resolves it
             ;; transitively — docs/operations.md, "Neither server logs a request".
             :dev {:dependencies [[org.slf4j/slf4j-nop "2.0.19"]
                                  ;; dev-only hot reload: `vaelii.browser.reload` reads the
                                  ;; watched sources' ns forms and dependency graph with
                                  ;; tools.namespace and reloads the changed namespaces before
                                  ;; each request (web/hot-reloading, on only under
                                  ;; scripts/start-vaelii-dev.sh, which sets VAELII_DEV).
                                  ;; Never in the jar — like the profiler, a dev/repl-profile
                                  ;; dependency.
                                  [org.clojure/tools.namespace "1.5.0"]]
                   :plugins [[dev.weavejester/lein-cljfmt "0.16.5"]
                             [lein-shell "0.5.0"]
                             [lein-cloverage "1.2.4"]]}
             ;; property-based tests, in :test rather than :dev because a local
             ;; gitignored profiles.clj may redefine :dev and replace it wholesale
             :test {:dependencies [[org.clojure/test.check "1.1.3"]]
                    ;; Quiet the engine's own logging under test. Trove's default
                    ;; backend is the console one at `:info` and nothing sets it, so
                    ;; a GREEN run printed 777 lines of `:warn`/`:info` — two thirds
                    ;; of the suite's output, and none of it a verdict. The suite
                    ;; provokes those on purpose: `::dropped-conclusion`,
                    ;; `:no-placement` and the aggregate refusals are what the
                    ;; assertions are checking for, so the log is the test working.
                    ;;
                    ;; The floor is `:error`, not off — an unexpected error still
                    ;; prints next to the failure it explains. Turn the rest back on
                    ;; when a red run needs them: `VAELII_TEST_LOG_LEVEL=info lein test`.
                    ;;
                    ;; It is the engine's own dial (`vaelii.core/set-log-level`) rather
                    ;; than a second mechanism spelled the same way: a suite quieted by
                    ;; a private copy of the install would keep passing the day the
                    ;; public one stopped working. A level outside the five is refused
                    ;; here, so a typo fails the run rather than silencing it.
                    ;;
                    ;; Runtime `resolve` rather than the symbol itself because
                    ;; injections compile as one `do`: a var in the same form as the
                    ;; `require` that loads it is not there to resolve yet.
                    ;;
                    ;; `VAELII_TEST_NS_COUNTS` prints one assertion count per namespace
                    ;; (`vaelii.ns-counts`), for the run whose total moved.  Off unless
                    ;; set true (`config/prop-bool`, as the harness switches read, so
                    ;; `=0` is off), and inert when on: it reads counters clojure.test
                    ;; already maintains.  Installed here rather than from a test namespace so it
                    ;; is in place before the first one loads, and so the counting cannot
                    ;; depend on which namespace happened to require it.
                    :injections
                    [(require 'vaelii.impl.logging 'vaelii.impl.config)
                     ((resolve 'vaelii.impl.logging/set-level)
                      (keyword (or (System/getenv "VAELII_TEST_LOG_LEVEL") "error")))
                     (let [prop-bool (resolve 'vaelii.impl.config/prop-bool)]
                       (when (prop-bool "VAELII_TEST_NS_COUNTS" false)
                         (require 'vaelii.ns-counts)
                         ((resolve 'vaelii.ns-counts/install!))))]}
             ;; sampling profiler for a repl: `(prof/profile (…))`, flamegraphs under
             ;; /tmp/clj-async-profiler/results/, `(prof/serve-ui 8080)`. The -XX pair
             ;; keeps inlined frames off their caller's line; the attach flag is how it
             ;; starts without a separate agent.
             :repl {:dependencies [[com.clojure-goes-fast/clj-async-profiler "2.0.0-beta1"]]
                    :jvm-opts ["-Djdk.attach.allowAttachSelf"
                               "-XX:+UnlockDiagnosticVMOptions"
                               "-XX:+DebugNonSafepoints"]}
             ;; the benchmark harnesses, on their own source path so they never ship.
             ;; They build a whole index in the heap, and jol sizes a KB structurally
             ;; (`bench-scale`) — the --add-opens and self-attach are what let it read
             ;; field layout rather than estimate it.
             ;;
             ;; Quiet under the harnesses for the reason `:test` is, and the reading is
             ;; the verdict here in the way the assertion is there. A workload provokes
             ;; the engine's own logging *by construction* — the clash rows drop
             ;; conclusions, and every `fresh-kb` opens over the space the row before it
             ;; filled — so `lein perf` printed 1,307 log lines around its verdicts, and
             ;; the row that failed was somewhere in them. Same floor at `:error`, same
             ;; escape hatch: `VAELII_BENCH_LOG_LEVEL=info lein perf` when a reading needs
             ;; explaining, and a level outside the five fails the run rather than
             ;; silencing it.
             :bench {:source-paths ["bench"]
                     :dependencies [[org.openjdk.jol/jol-core "0.17"]
                                    [org.roaringbitmap/RoaringBitmap "1.6.23"]
                                    [it.unimi.dsi/fastutil-core "8.5.19"]]
                     :jvm-opts ["-Xmx6g" "--add-opens=java.base/java.lang=ALL-UNNAMED"
                                "-Djdk.attach.allowAttachSelf=true"
                                ;; jol sizes a hidden class (a lambda) without Unsafe's
                                ;; field offsets, which a JDK 17+ refuses for one
                                "-Djol.magicFieldOffset=true"]
                     :injections
                     [(require 'vaelii.impl.logging)
                      ((resolve 'vaelii.impl.logging/set-level)
                       (keyword (or (System/getenv "VAELII_BENCH_LOG_LEVEL") "error")))]}
             ;; `lein browser`: the browser running inside a repl with a reload channel
             ;; into it. Both halves bind loopback — a write route with no auth beside
             ;; an nREPL is a remote shell (CONTRIBUTING.md §6).
             :browser {:repl-options
                       {:host "127.0.0.1"
                        :init (do ((requiring-resolve 'vaelii.browser.web/dev-repl)) nil)}}
             ;; generational ZGC, asked for per task: `lein with-profile +zgc <task>`.
             ;;
             ;; Detected off the running JDK rather than written as a static vector,
             ;; because **no single line is correct and boot-safe across 17/21/25**.
             ;; Bare `-XX:+UseZGC`
             ;; is generational from 23 (the platform default there, where naming the
             ;; mode flag only warns); on 21-22 the explicit `-XX:+ZGenerational` is
             ;; *required* or the collector is non-generational; before 21 the mode does
             ;; not exist and naming the flag is fatal-unrecognized, so the JVM does not
             ;; boot at all. `-XX:+IgnoreUnrecognizedVMOptions` is not the shortcut it
             ;; looks like — it turns every later `-XX:` typo into a warn-and-skip.
             ;;
             ;; A profile rather than a top-level `:jvm-opts`, and the measurement is
             ;; why. `lein perf`, two alternating passes at a fixed 6 GiB heap: the JDK
             ;; default took 40.7-41.2 s at 1493-1510 MB peak RSS, generational ZGC
             ;; 55.5-55.9 s at 6224-6258 MB — 36% slower while holding 4.2x the resident
             ;; set, and ZGC alone tripped the `:negation-arbitration` growth bound on
             ;; both passes. A concurrent collector earns its throughput cost on a live
             ;; set of tens of gigabytes, and this engine's peak here is 1.5 GB. So the
             ;; default collector is what the build runs on, a top-level entry would
             ;; select the collector for the test and perf stages as well, and perf
             ;; judges the *growth* between two sizes — moving the collector under it
             ;; moves the thing it measures. The flags stay correct for a JVM that has
             ;; its own reason to ask.
             ;;
             ;; One `~` around the whole vector: leiningen resolves `unquote` and not
             ;; `unquote-splicing`, so `~@` does not work here.
             :zgc {:jvm-opts ~(let [v     (System/getProperty "java.specification.version")
                                    major (Integer/parseInt
                                           (second (re-find #"^(?:1\.)?(\d+)" v)))]
                                (if (<= 21 major 22)
                                  ["-XX:+UseZGC" "-XX:+ZGenerational"]
                                  ["-XX:+UseZGC"]))}
             ;; outdated-dependency report, isolated from every other classpath
             :antq {:dependencies [[com.github.liquidz/antq "2.11.1276"]]}}
  ;; indent rules come from an optional cljfmt-indents.edn at the repo root, so a
  ;; custom macro can be taught to cljfmt without editing this file.
  ;; `:parallel?` checks and fixes the files through `pmap`: 11 s against 25 s.
  :cljfmt {:parallel?                       true
           :indentation?                    true
           :indent-line-comments?           true
           :remove-surrounding-whitespace?  true
           :remove-trailing-whitespace?     true
           :insert-missing-whitespace?      true
           :remove-consecutive-blank-lines? true
           :sort-ns-references?             true
           ;; `clojure.edn/read-string`, never `clojure.core`'s: this file is untracked,
           ;; so a pull request can add it, and lein evaluates project.clj on *every*
           ;; invocation.  `core/read-string` honours `#=(...)` reader-eval, which would
           ;; make checking out a contributor's branch and typing `lein test` arbitrary
           ;; code execution on the reviewer's machine.
           :extra-indents ~(let [f (java.io.File. "cljfmt-indents.edn")]
                             (if (.exists f)
                               (do (require 'clojure.edn)
                                   ((resolve 'clojure.edn/read-string) (slurp f)))
                               {}))}
  ;; `lein lint` is the unified report; the lint-* aliases run one check each, and
  ;; `lein fix` reformats in place.
  :aliases {"lint"            ["shell" "bash" "scripts/lint.sh"]
            "lint-glossary"   ["shell" "bash" "scripts/lint-glossary.sh"]
            "lint-versions"   ["shell" "bash" "scripts/lint-versions.sh"]
            "lint-links"      ["shell" "python3" "scripts/check-doc-links.py" "--public-view"]
            "lint-drift"      ["shell" "python3" "scripts/check-doc-drift.py"]
            "lint-kondo"      ["shell" "clj-kondo" "--lint" "src" "test" "bench"]
            "lint-cljfmt"     ["shell" "env" "LEIN_JVM_OPTS=-XX:+TieredCompilation" "lein" "cljfmt" "check"]
            ;; the script owns the roster, so this alias and scripts/lint.sh check
            ;; the same list — restating it here is how one of them goes short
            "lint-shellcheck" ["shell" "bash" "scripts/lint-shellcheck.sh"]
            ;; the two ratchets: a compile pass whose warnings fail, and a public var
            ;; nothing references.  Both are in scripts/lint.sh too, so `lein gate`
            ;; picks them up inside the suite's wall clock; these are the one-offs.
            "lint-reflect"    ["shell" "bash" "scripts/check-reflection.sh"]
            "lint-unused"     ["shell" "python3" "scripts/check-unused-publics.py"]
            ;; the prose budget: metaphor and aphorism against scripts/prose-baseline.txt.
            ;; `lein lint-prose -- --update` lowers a stale budget; it never raises one
            "lint-prose"      ["shell" "python3" "scripts/check-prose.py"]
            ;; the `authorship` CI gate's rules, against synthetic commits — the gate
            ;; runs only on a pull request, so this is where they are exercised first
            ;; lint, the suite and the perf claims in one run, not fail-fast
            ;; (scripts/gate.sh says why)
            "gate"            ["shell" "bash" "scripts/gate.sh"]
            ;; the release gate: `gate` (lint + test) plus the perf stage, for a tag
            ;; or a perf-sensitive land.  The fast `gate` drops perf and only asks
            ;; for it; this always runs it.  See scripts/gate.sh's PERF header.
            "release-gate"    ["shell" "bash" "scripts/gate.sh" "--release"]
            ;; rewrite the three goldens — the published API surface, the extension
            ;; seams, the config surface — from the live tree.  `test` is already on a
            ;; plain `run`'s classpath here, so no profile is needed.  Read
            ;; `vaelii.regen-goldens` before reaching for it: regenerating is how a
            ;; deliberate surface change is recorded, and never how a red golden is
            ;; silenced
            "regen-goldens"   ["run" "-m" "vaelii.regen-goldens"]
            ;; rewrite the client's wrapper sections from the daemon's op table — one
            ;; wrapper per op, spelled as `vaelii.core` spells the fn.  Generated rather
            ;; than macroexpanded because the client requires neither the table nor the
            ;; engine, and read `vaelii.regen-client` before reaching for it: a red
            ;; `client_surface_test` is an op somebody added, not a chore
            "regen-client"    ["run" "-m" "vaelii.regen-client"]
            ;; the suite across JVMs — what the gate's test stage runs.  Memory stores
            ;; only: a durable half is one lock and three usable space blocks, so the
            ;; script refuses one rather than sharding into it.
            "test-parallel"   ["shell" "bash" "scripts/test-parallel.sh"]
            ;; the cross-process tests, which run only when named — `:multi-jvm` is
            ;; opt-in, so `lein test`, `lein test :all` and the gate all pass over
            ;; them.  An alias because a selector nothing types is a selector nothing
            ;; runs: this is the name `deep.yml` and a reviewer both reach for.
            ;; through scripts/test-selector.sh, so a selector no gate reaches still
            ;; leaves a report and a row in the run ledger — a run nothing recorded is
            ;; one nobody can say happened, which for these two is the whole question
            "test-multi-jvm"  ["shell" "bash" "scripts/test-selector.sh" ":multi-jvm"]
            ;; the exhaustive truncation sweep, opt-in for a different reason than
            ;; `:multi-jvm`: it is not that no other selector *can* run it, it is that
            ;; no configuration *varies* it — the sweep names its own four backends, so
            ;; a matrix row would repeat identical work.  Once, not once per row.  Set
            ;; `VAELII_TEST_TMPDIR` to a tmpfs: a couple of minutes rather than ten.
            "test-fuzz"       ["shell" "bash" "scripts/test-selector.sh" ":fuzz"]
            ;; feeds the README deps badge, via scripts/update-badges.sh --deps
            "antq"            ["with-profile" "+antq" "run" "-m" "antq.core" "--skip=pom"]
            ;; the whole suite once per backend — seven record×index pairs plus the
            ;; overlay decorator (scripts/test-backends.sh).  The trailing `~(…)` hands
            ;; the script leiningen's terminal state, because lein-shell pipes its
            ;; stdout and the script cannot otherwise tell whether the real output is a
            ;; terminal — the compact marks under one, greppable lines into a pipe
            ;; (scripts/lib/suite-marks.sh).  test-sweeps and test-shuffle carry it too.
            "test-backends"   ["shell" "bash" "scripts/test-backends.sh"
                               ~(if (System/console) "--tty" "--no-tty")]
            ;; and once per alternative implementation — the dense TMS, the sweep
            ;; chainer, the node engine, one of its tacticians, the reference
            ;; context retrieval (scripts/test-sweeps.sh).  The other axis, and
            ;; together with the line above it is what `deep.yml` runs
            "test-sweeps"     ["shell" "bash" "scripts/test-sweeps.sh"
                               ~(if (System/console) "--tty" "--no-tty")]
            ;; ...and both at once, one JVM per configuration, as many at a time as
            ;; the box has cores for: ~13 minutes against the ~55 the two scripts
            ;; above take in sequence, and the one to run when a change owes the
            ;; matrix (scripts/test-matrix.sh).  The launch order is shuffled and the
            ;; seed printed, so a run stopped early covers a random subset of the
            ;; roster; `--ordered` schedules the longest configuration first instead
            "test-matrix"     ["shell" "bash" "scripts/test-matrix.sh"
                               ~(if (System/console) "--tty" "--no-tty")]
            ;; the whole matrix in a random order, memory first, stopping at the
            ;; first configuration that fails — the smoke test the full matrix is
            ;; not.  `lein test-shuffle -n` prints the shuffled plan; the seed it
            ;; reports replays the order (scripts/test-shuffle.sh).  The trailing
            ;; `~(…)` hands the script leiningen's terminal state so the graph is the
            ;; compact marks under a terminal and the greppable lines into a pipe,
            ;; the same as the two matrix scripts above (scripts/lib/suite-marks.sh).
            "test-shuffle"    ["shell" "bash" "scripts/test-shuffle.sh"
                               ~(if (System/console) "--tty" "--no-tty")]
            ;; a release step, not a gate: who does this release's Breaking
            ;; entries break?  Reads each entry's `*Breaks:*` tokens and greps
            ;; the sibling checkouts for them (scripts/check-breaking-siblings.sh)
            "check-siblings"  ["shell" "bash" "scripts/check-breaking-siblings.sh"]
            "fix"             ["shell" "env" "LEIN_JVM_OPTS=-XX:+TieredCompilation" "lein" "cljfmt" "fix"]
            "bench-memory"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.memory"]
            "bench-memconjoin" ["with-profile" "+bench" "run" "-m" "vaelii.bench.memconjoin"]
            "bench-scale"     ["with-profile" "+bench" "run" "-m" "vaelii.bench.scale"]
            "bench-settlephases" ["with-profile" "+bench" "run" "-m" "vaelii.bench.settle-phases"]
            "bench-postings"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.postings"]
            "bench-survey"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.survey"]
            "bench-densetrie" ["with-profile" "+bench" "run" "-m" "vaelii.bench.densetrie"]
            "bench-records"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.records"]
            "bench-walk"      ["with-profile" "+bench" "run" "-m" "vaelii.bench.walk"]
            "bench-witness"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.witness"]
            "bench-jtms"      ["with-profile" "+bench" "run" "-m" "vaelii.bench.jtms"]
            "bench-backward"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.backward"]
            "bench-forward"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.forward"]
            "bench-plan"      ["with-profile" "+bench" "run" "-m" "vaelii.bench.plan"]
            ;; what shape of question a KB is asked, and what its index does with each
            ;; shape.  The `corpus` arm resolves the `:cyc-corpus` reader off the
            ;; classpath; scripts/link-checkouts.sh puts it there (docs/foreign.md).
            "bench-profile"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.profile"]
            ;; the index bake-off — one corpus, one workload, N layouts, and the access
            ;; path each goal took beside how long it took.  Its `corpus` arm needs the
            ;; `:cyc-corpus` reader on the classpath, as bench-profile's does.
            "bench-index"     ["with-profile" "+bench" "run" "-m" "vaelii.bench.index"]
            ;; the bake-off's structural counterpart — objects and bytes on the walk,
            ;; counted rather than timed, over the same layout table.  No corpus arm,
            ;; so it reads no foreign format.
            "bench-alloc"     ["with-profile" "+bench" "run" "-m" "vaelii.bench.alloc"]
            "bench-qcn"       ["with-profile" "+bench" "run" "-m" "vaelii.bench.qcn"]
            ;; the metric half of time beside the qualitative one: what a closure costs
            ;; from nothing, what an arriving constraint costs the answer after it, and
            ;; what a repeat ask costs when nothing moved (docs/stp.md, "Cost")
            "bench-stp"       ["with-profile" "+bench" "run" "-m" "vaelii.bench.stp"]
            "bench-qcnchain"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.qcnchain"]
            "bench-aggchain"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.aggchain"]
            "bench-corpus"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.corpus"]
            "bench-reindex"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.reindex"]
            "bench-residency" ["with-profile" "+bench" "run" "-m" "vaelii.bench.residency"]
            ;; the whole-KB budget beside `bench-residency`'s one structure: every
            ;; resident structure at two sizes, extrapolated to a named target
            "bench-budget"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.budget"]
            "bench-cyclic"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.cyclic"]
            "bench-checks"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.checks"]
            ;; the argument-root index's cost on the belief-settle (recover) hot path —
            ;; a micro probe (returned-vs-matched) and an end-to-end reindex+recover, the
            ;; shared judge for the index-layout experiment (docs: bench/…/argindex.clj)
            "bench-argindex"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.argindex"]
            "bench-inherit"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.inherit"]
            "bench-tactics"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.tactics"]
            ;; would a cross-query subgoal table be hit?  The census over the fables'
            ;; question set, the commonsense examples and the debugger's render, and the
            ;; A/B that prices a prototype one.  Reads the test-world, so it wants
            ;; `test/` on the classpath, which leiningen puts there
            "bench-subgoal"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.subgoal"]
            ;; the two per-firing reads `perf` cannot gate: a cost that is constant per
            ;; operation moves both of a ratio's readings, so it gets a report and a
            ;; per-firing number instead of a bound
            "bench-hotreads"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.hotreads"]
            ;; where a bulk load's wall clock goes, phase by phase — a cumulative peel,
            ;; so the deltas sum to the baseline (docs/storage.md, "What a bulk load costs")
            "bench-loadphase" ["with-profile" "+bench" "run" "-m" "vaelii.bench.loadphase"]
            ;; where `recover`'s per-open wall clock goes, step by step — a faithful replay
            ;; of its body timed apart (persistence-prompts/01-recover-decomposition.md).
            ;; Large sizes want heap: `lein update-in :jvm-opts conj '"-Xmx24g"' -- …`
            "bench-recoverphase" ["with-profile" "+bench" "run" "-m" "vaelii.bench.recoverphase"]
            ;; the rebuildable caches' resident bytes and the KB-quality readings, in one
            ;; JVM because both sit behind the same expensive corpus load.  A corpus run
            ;; resolves the `:cyc-corpus` reader off the classpath; link it with
            ;; scripts/link-checkouts.sh first (docs/foreign.md).
            "bench-caches"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.caches"]
            ;; the performance *gate*, as against the bench-* reports above: scaling
            ;; claims as growth ratios, non-zero exit on a regression.  Behind a
            ;; script rather than pointing straight at the harness so the report is
            ;; kept and one row lands in the run ledger — scripts/perf.sh says why
            ;; the ledger writer is shell for every runner and not Clojure for this
            ;; one.  Arguments pass through: `lein perf --quick`, `--only <name>`,
            ;; `--tolerance <x>` are unchanged
            "perf"            ["shell" "bash" "scripts/perf.sh"]
            "browser"         ["with-profile" "+browser" "repl"]
            ;; the daemon and the CLI (docs/operations.md)
            "serve"           ["run" "-m" "vaelii.serve"]
            "cli"             ["run" "-m" "vaelii.cli"]}
  ;; `:timeout` is how many milliseconds `lein repl` waits for the project JVM to ack
  ;; its nREPL server, and leiningen's default is 60000. The `:init` form runs BEFORE
  ;; `nrepl.server/start-server` in that JVM — leiningen.repl/server-forms hands the
  ;; form to `eval-in-project` as the init argument, which `eval-in-project` evaluates
  ;; ahead of the body — so `lein browser`'s whole boot is counted against the wait:
  ;; `vaelii.browser.web/dev-repl` opens the KB and then `load-kb-dir` loads
  ;; VAELII_KB_DIR. A disk KB whose recover runs past 60 s therefore aborts the client
  ;; with "REPL server launch timed out", and the project JVM it abandons keeps running
  ;; and keeps the single-writer lock, so the retry then fails on the lock as well.
  ;; `lein browser :headless` and a CIDER jack-in take the headless branch, which blocks
  ;; before the ack wait and never reads this key.
  :repl-options {:init-ns vaelii.core
                 :timeout 600000})
