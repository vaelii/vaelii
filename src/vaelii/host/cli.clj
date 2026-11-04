;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.cli
  "A command-line driver for a KB — the shell dual of the in-process API, launched with
  `lein run -m vaelii.host.cli <cmd> <args…>`.  It runs the engine in-process (no
  daemon); to talk to a running daemon use `vaelii.host.client` instead.

    lein run -m vaelii.host.cli assert  '(dog Muffet)'  CxNaturalWorld --dir /tmp/kb
    lein run -m vaelii.host.cli query   '(dog ?x)'    CxNaturalWorld --dir /tmp/kb
    lein run -m vaelii.host.cli why     3                                 --dir /tmp/kb
    lein run -m vaelii.host.cli export  /tmp/dump                         --dir /tmp/kb
    lein run -m vaelii.host.cli repl --starter          # interactive, starter schema
    lein cli help                                      # every command and what it takes

  `help` is a word rather than only a flag because Leiningen answers `lein cli --help`
  itself, printing the alias expansion — the flag never reaches this namespace through
  the alias, though it does through the full `lein run -m vaelii.host.cli --help`.

  **Backend.**  `--dir <path>` opens the store there under the backend its files were
  written by (`v/store-backend`), or a new durable `:disk-log` store when it holds none —
  recovered on open, so a fact asserted in one invocation is there in the next.  A `--dir`
  whose parent does not exist is refused (`open-kb-from`) rather than created.
  `upgrade` opens a store, brings its reasoning image and index image up to this build, and
  closes it (`upgrade!`); `--verify` recovers anyway and compares the two images,
  `--trust` keeps an image written under other engine source, and `--sync` brings the
  shipped contexts to what this engine ships.
  With no `--dir` the KB is
  in-memory and lives only for the process — useful for `repl` or a single compound
  session, pointless across one-shot commands.  `--starter` loads the shipped schema
  (types, contexts, relation rules) so you can explore the ontology.  `--strength
  monotonic` marks an `assert` or `assert-rule` known-true.  `export` takes `--variant
  records|records+index` and `--compression gzip|xz|none`.

  **A flag belongs to the commands that read it** (`command-flags`), and one carried by
  a command that does not is refused rather than dropped — those three are the driver's
  and go anywhere, the rest do not.  A *value* it cannot honour is refused on the same
  argument: `--format texr` and `--depth twice` name nothing.

  **stdout is the answer.**  `err!` keeps a refusal off it, and `on-stderr` keeps the
  engine's own log lines off it too — Trove's console backend prints to `*out*`, which
  here is what a script redirects.  A refusal is one stderr line, `error: [<:type>]
  <message>` (`refusal-line`), so a script branches on the keyword and not on the prose.

  **One writer.**  A `--dir` KB takes the single-writer file lock (docs/storage.md), so
  the CLI and a daemon cannot own the same directory at once — by design.  `diff` and
  `upgrade` open no KB of the run's (`without-a-kb`), so `diff` answers beside a daemon
  that holds `--dir`."
  (:require [clojure.edn :as edn]
            [clojure.pprint :as pp]
            [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.host.starter :as starter]
            [vaelii.host.sync :as sync]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.reasoning-image :as ri])
  (:import [java.io File PushbackReader StringReader]))

;; ---- arg + option parsing ------------------------------------------------

(def ^:private value-flags
  "Every value-taking flag spelling the driver knows — what `parse-opts` will bind at
  all, as against which command may carry which, that being `command-flags`' answer
  one entry point further in.  A flag outside it is refused, not keywordized: `--strenght monotonic`
  accepted in silence would store known-true content at `:default` — the exact
  sentence the flag-with-no-value refusal beside it exists for, reached from the
  other side — and a misspelt `--dir` would open the in-memory KB, gone at exit."
  #{"--dir" "--strength" "--depth" "--variant" "--compression" "--format"
    "--context" "--nearest"})

(def ^:private bare-flags
  "Every flag spelling the driver binds to `true`, taking no value."
  #{"--help" "--memory" "--starter" "--verify" "--trust" "--sync"})

(defn parse-opts
  "Split raw args into `[positionals opts]`.  `--k v` becomes `{:k v}`, a bare flag
  (`bare-flags`) becomes `{:flag true}`; everything else is a positional, in order.

  A value-taking flag with no value is refused (`:unknown-option`) rather than bound
  nil: `assert … --strength` with nothing after it would otherwise store at `:default`
  — the exact class the flag was written to escape — and `--dir` at the end of a line
  would open the in-memory KB, gone at process exit.  A flag the accepted-flag list does
  not name is refused the same way."
  [args]
  (loop [as args, pos [], opts {}]
    (if (empty? as)
      [pos opts]
      (let [a (first as)]
        (cond
          (not (str/starts-with? a "--")) (recur (rest as) (conj pos a) opts)
          (bare-flags a)
          (recur (rest as) pos (assoc opts (keyword (subs a 2)) true))
          (not (value-flags a))
          (throw (ex-info (str "unknown flag: " a " — the driver reads "
                               (str/join ", " (sort (into bare-flags value-flags)))
                               ", and a command reads only its own of those")
                          {:type :unknown-option :mismatch :unknown-key :flag a}))
          :else (let [v (second as)]
                  ;; a following flag is not a value: `--dir --starter` otherwise opens
                  ;; a directory literally named `--starter` and never loads the schema
                  (if (and (some? v) (not (str/starts-with? v "--")))
                    (recur (drop 2 as) pos (assoc opts (keyword (subs a 2)) v))
                    (throw (ex-info (str a " needs a value and "
                                         (if v (str "the next word is the flag " v)
                                             "the line ends after it")
                                         " — write " a " <value>")
                                    {:type :unknown-option :mismatch :missing-value :flag a})))))))))

(defn read-arg
  "One argv string as data: the EDN it reads as (a sentence, a context symbol, a handle) and
  the **raw string** when it reads as none, which is what a filesystem path is
  (`/var/lib/vaelii` is not a symbol).  **One argument is one form**: `edn/read-string`
  drops a second form, so `assert '(dog Muffet) (cat Felix)' CxWell` would store the dog
  and exit 0; a second form is refused (`:bad-args`, as a wrong operand count is).  A
  string that reads as no form, or as none because it is empty, stays the string.  `cmd`
  names the command in the refusal and is the `:op` every `:bad-args` throw carries."
  [cmd s]
  (let [r     (PushbackReader. (StringReader. (str s)))
        form  (try (edn/read {:eof ::eof} r) (catch Exception _ ::unreadable))]
    (if (or (= ::unreadable form) (= ::eof form))
      s
      (let [more (try (edn/read {:eof ::eof} r) (catch Exception _ ::unreadable))]
        (if (= ::eof more)
          form
          (throw (ex-info (str cmd ": one argument is one form, and " (pr-str (str s))
                               " holds more than one — quote each argument separately")
                          {:type :bad-args :op cmd :arg (str s)})))))))

(defn read-forms
  "Every EDN form in `s`, in order — how a REPL line's args (`(dog ?x) CxMy`) are
  parsed into data."
  [s]
  (let [r (PushbackReader. (StringReader. s))]
    (loop [acc []]
      (let [form (edn/read {:eof ::eof} r)]
        (if (= form ::eof) acc (recur (conj acc form)))))))

;; ---- the command table ---------------------------------------------------
;; `dispatch` takes args **already parsed to data** (a sentence is a list, a context a
;; symbol, a handle a long), so `-main` (which edn-reads each argv string) and the REPL
;; (which reads forms off the line) share one implementation.

(defn- in-content-order
  "An answer **set**, in a printed content order.  `match`, `query` and `ask` answer with a
  set, which has no order of its own, so two loads of the same knowledge would print
  differently and a diff of the outputs would read as a KB change; `types` and `contexts`
  are sorted for that reason.  `prove` is **not** here: it answers one solution per
  derivation in DFS order, which is part of what a proof says."
  [answers]
  (nm/by-print-key answers))

(defn- diff-text-kbs
  "`diff`'s answer: the two text KBs its operands name, compared by content."
  [args]
  (v/kb-diff (str (nth args 0)) (str (nth args 1))))

(def command-table
  "Every command word, in the order `--help` prints it: `[word min max operands gloss run]`,
  where `run` is `(fn [kb args o])` and `o` is `{:strength :depth :ctx :nearest :opts}`.

  `max` is nil for a command whose last operand is optional.  One table rather than
  two, because the arity a command *takes* and the arity `--help` *advertises* going
  out of step is how a usage message starts lying — and `dispatch` reaches into `args`
  with `nth`, so an unchecked short line raises `IndexOutOfBoundsException`, whose
  message is the class name and names neither the command nor the argument."
  [["assert"      2 2   "'<sentence>' <CxName>"        "store a fact"
    (fn [kb [s c] o] (v/assert kb s c (:strength o)))]
   ["assert-rule" 3 3   "'[<antecedents>]' '<consequent>' <CxName>" "store a rule"
    (fn [kb [a c x] o] (v/assert-rule kb a c x (:strength o)))]
   ["match"       2 2   "'<pattern>' <CxName>"         "stored, believed literals, in content order"
    (fn [kb [p c] _] (in-content-order (map v/sentence-of (v/sentexes-matching kb p c))))]
   ["query"       2 2   "'<goal>' <CxName>"            "the default read, in content order (--depth N to expand rules)"
    (fn [kb [g c] o] (in-content-order (v/query kb g c (:depth o))))]
   ["query?"      2 2   "'<goal>' <CxName>"            "the same, as a boolean"
    (fn [kb [g c] o] (v/query? kb g c (:depth o)))]
   ["ask"         2 2   "'<goal>' <CxName>"            "the prover registry, in content order; no rule expansion"
    (fn [kb [g c] _] (in-content-order (v/ask kb g c)))]
   ["prove"       2 2   "'<goal>' <CxName>"            "backward chaining; one solution per derivation, in DFS order"
    (fn [kb [g c] _] (v/prove kb g c))]
   ["provable?"   2 2   "'<goal>' <CxName>"            "the same, as a boolean"
    (fn [kb [g c] _] (v/provable? kb g c))]
   ["retract"     1 1   "<handle>"                      "remove a sentex and what it solely supported"
    (fn [kb [h] _] (v/retract! kb h))]
   ["why"         1 1   "<handle>"                      "the proof tree behind a belief"
    (fn [kb [h] _] (v/why kb h))]
   ;; `--nearest N` runs a bounded backward search naming the rules that came closest
   ;; (docs/api.md); it takes a goal, never a handle (`check-args!`)
   ["why-not"     1 2   "'<goal>' [<CxName>]"          "why a goal is not believed (--nearest N: the rules that nearly fired)"
    (fn [kb [g c] o]
      (cond
        (:nearest o) (v/why-not kb g (or c '?ctx) (:nearest o))
        (nil? c)     (v/why-not kb g)
        :else        (v/why-not kb g c)))]
   ["in"          1 1   "<handle>"                      "is it believed?"
    (fn [kb [h] _] (v/in? kb h))]
   ["isa"         2 3   "<Individual> <type> [<CxName>]" "type membership, via genl"
    (fn [kb args _] (apply v/isa? kb args))]
   ["types-of"    1 2   "<Individual> [<CxName>]"      "the types asserted of it, not their supertypes"
    (fn [kb args _] (apply v/types-of kb args))]
   ["describe"    1 1   "<term>"                        "everything the KB holds about one term (--context C)"
    (fn [kb [t] o] (v/describe kb t (:ctx o)))]
   ["handle-of"   2 2   "'<sentence>' <CxName>"        "the handle a sentence is stored under"
    (fn [kb [s c] _] (v/handle-of kb s c))]
   ;; `by-print-key`, never bare `sort`: a NAT type node keyed with `str` collapses under
   ;; an ambient print bound
   ["types"       0 0   ""                              "types in the genl hierarchy"
    (fn [kb _ _] (nm/by-print-key (v/types kb)))]
   ["contexts"    0 0   ""                              "contexts in the genlCx hierarchy"
    (fn [kb _ _] (sort (v/contexts kb)))]
   ["conflicts"   0 0   ""                              "irreducible :monotonic clashes, both still believed"
    (fn [kb _ _] (v/conflicts kb))]
   ["contradictions" 0 0 ""                             "coexisting P/¬P pairs at :default"
    (fn [kb _ _] (v/contradictions kb))]
   ;; the one command that answers in prose: `show` prints the Markdown string as written
   ["quality"     0 0   ""                              "a report on the knowledge: unfired rules, skew, depth, coverage"
    (fn [kb _ _] (v/quality-report (v/kb-quality kb)))]
   ["load"        1 1   "<path>"                        "assert a text KB: a Cx*.txt file, or a directory of them"
    (fn [kb [path] _] (dissoc (v/load-text! kb (str path)) :elapsed-ms))]
   ;; a dump (the KB's state) and a text KB (its premises) are two entry points
   ;; (docs/api.md); `check-args!` refuses a `--format` other than `text`, and a dump's
   ;; flags beside `--format text`.  The dump flags are the writer's own keywords.
   ["export"      1 1   "<dest>"                        "write a dump (--variant, --compression), or a text KB (--format text)"
    (fn [kb [dest] o]
      (let [opts (:opts o)]
        (if (= "text" (:format opts))
          (v/export-text! kb (str dest))
          (v/export! kb (str dest)
                     (cond-> {}
                       (:variant opts)     (assoc :variant (keyword (:variant opts)))
                       (:compression opts) (assoc :compression (keyword (:compression opts))))))))]
   ;; both operands are text KBs on disk; `run` answers it without opening a KB
   ;; (`without-a-kb`), so this runner is the REPL's
   ["diff"        2 2   "<a> <b>"                       "what two text KBs disagree about, as content"
    (fn [_ args _] (diff-text-kbs args))]
   ;; `upgrade!` opens and closes the store itself, and two KBs over one directory share
   ;; its stores, so inside the REPL the close would close the store under the caller
   ["upgrade"     0 0   ""                              "bring the --dir store's reasoning and index images up to this build"
    (fn [_ _ _]
      (throw (ex-info (str "upgrade opens and closes its own KB — run `lein cli"
                           " upgrade --dir <path>` from the shell, not inside the repl")
                      {:type :unknown-command :cmd "upgrade"
                       :commands (mapv first command-table)})))]
   ["repl"        0 0   ""                              "the interactive loop" nil]])

(def commands
  "The command words `dispatch` knows, for the usage message and `unknown command`."
  (mapv first command-table))

(def ^:private arity-of
  "command word -> `[min max operands]`, for `check-arity!`."
  (into {} (map (fn [[c mn mx ops]] [c [mn mx ops]])) command-table))

(defn check-arity!
  "Refuse a command line with the wrong number of operands, naming what the command takes
  and what it got.  A short line would reach `dispatch`'s `nth` as
  `IndexOutOfBoundsException`, and a *long* line would drop the extra operand in silence,
  storing a fact somewhere other than where it was meant to go."
  [cmd args]
  (when-some [[mn mx ops] (arity-of cmd)]
    (let [n (count args)]
      (when (or (< n mn) (and mx (> n mx)))
        (throw (ex-info (str cmd " takes " (if (and mx (= mn mx))
                                             (str mn " argument" (when (not= 1 mn) "s"))
                                             (str mn "–" (or mx "any") " arguments"))
                             ", given " n
                             "\n  usage: " cmd (when (seq ops) (str " " ops))
                             "\n  quote every argument: the shell eats ( ) [ ] and ?")
                        ;; `:bad-args`, not `:unknown-option`: the operands are the wrong
                        ;; number, and every flag on the line may be one this command reads.
                        ;; `:op` is the word `serve` already refuses a wire call's argument
                        ;; count under.
                        {:type :bad-args :op cmd :given n :takes [mn mx]}))))))

(def ^:private driver-flags
  "The flags that say which KB to open rather than what a command does with it.  They
  apply to every command, so `check-flags!` admits them everywhere."
  #{:dir :memory :starter :help})

(def ^:private command-flags
  "The value flags each command reads, keyed by command word; a command absent from the
  map reads none.  This is `assert-opt-keys`' rule at the shell entry point (docs/api.md): an
  option is a request, and one the entry point cannot honour is refused rather than dropped.
  `match … --strength monotonic` accepted and ignored reads from the outside exactly
  like a strength that was applied.

  `repl` is the union on purpose — its options are fixed at session start and every
  line reuses them (`repl-loop`), so a flag there belongs to whichever line reads it."
  {"assert"      #{:strength}
   "assert-rule" #{:strength}
   "query"       #{:depth}
   "query?"      #{:depth}
   "export"      #{:variant :compression :format}
   "describe"    #{:context}
   "why-not"     #{:nearest}
   "upgrade"     #{:verify :trust :sync}})

(defn- flag-names [ks] (str/join ", " (map #(str "--" (name %)) (sort ks))))

(defn count-option
  "The whole number `flag` carries, refused **by name** when its value is not one.

  `Long/parseLong` on the raw string reports `For input string: \"twice\"` — one line and
  exit 1, so no stack trace, but the line names neither the flag nor the command and is
  java.lang's rather than the engine's.  That is the sentence `check-arity!` exists to
  stop being printed for an operand count, reached one argument in."
  [flag s]
  (try (Long/parseLong (str s))
       (catch NumberFormatException _
         (throw (ex-info (str flag " takes a whole number, given " (pr-str (str s)))
                         {:type :unknown-option :mismatch :bad-value
                          :flag flag :value (str s)})))))

(defn check-args!
  "Refuse what `dispatch` refuses of a command line without reading a KB: the operand count
  (`check-arity!`), a whole-number flag's value (`count-option`), `--nearest` beside a
  handle, and an `export --format` that names nothing or comes with a dump's flags.  `-main`
  asks this before it opens the KB, so a refused line leaves no `--dir` store behind and
  `--starter` loads nothing; `dispatch` asks it again for the lines a REPL session runs.
  `args` are data, as `dispatch` takes them."
  [cmd args opts]
  (check-arity! cmd args)
  (when-let [d (:depth opts)] (count-option "--depth" d))
  (when-let [n (:nearest opts)] (count-option "--nearest" n))
  (case cmd
    ;; This command takes a **goal** or a **handle** (one integer operand is a handle, as
    ;; `why`'s is), and `--nearest` belongs to the goal alone: a stored handle has no near
    ;; misses to look for.  The pairing is refused rather than dropped, which is
    ;; `check-flags!`'s rule one level in: a flag honoured for one operand shape and
    ;; ignored for the other reads identically from outside.
    "why-not"
    (when (and (:nearest opts) (integer? (first args)))
      (throw (ex-info (str "--nearest takes a goal, not a handle: handle "
                           (first args) " is stored, so :not-stored is not"
                           " the answer it can get and there is no rule to"
                           " look for.  Write the sentence and its context.")
                      {:type :unknown-option :mismatch :conflict :flag "--nearest"
                       :handle (first args)})))
    ;; `--format` names the one alternative to a dump, so a value that is not `text` names
    ;; nothing, and `--format texr` is refused (`check-flags!`'s rule one value in).
    ;; `--variant` and `--compression` describe a dump, so they are refused beside
    ;; `--format text` rather than ignored.
    "export"
    (when-let [f (:format opts)]
      (when (not= "text" f)
        (throw (ex-info (str "unknown --format " f
                             " — export writes a dump, or a text KB"
                             " with --format text")
                        {:type :unknown-option :mismatch :bad-value
                         :flag "--format" :value f :takes ["text"]})))
      (when-let [ignored (seq (sort (filter opts [:variant :compression])))]
        (throw (ex-info (str "--format text writes a text KB, which has no "
                             (str/join " and no " (map name ignored))
                             " — those describe an export dump")
                        {:type :unknown-option :mismatch :conflict :unknown (vec ignored)
                         :options [:format]}))))
    nil))

(defn check-flags!
  "Refuse a flag `cmd` does not read, naming what it does read.  `-main` calls this rather
  than `dispatch`, since the REPL reuses one option map for every line, so a session opened
  `--strength monotonic` must not have a later `match` line refused for the session's flag.
  The line naming `repl` is checked against the union, and the lines inside it against
  nothing.  An unknown command word is left alone: `-main` reports `:unknown-command`."
  [cmd opts]
  (when (some #{cmd} commands)
    (let [allowed (if (= cmd "repl")
                    (reduce into #{} (vals command-flags))
                    (get command-flags cmd #{}))
          unread  (remove (into driver-flags allowed) (keys opts))]
      (when (seq unread)
        (throw (ex-info (str cmd " does not read " (flag-names unread) " — it reads "
                             (if (seq allowed) (flag-names allowed) "no options of its own")
                             ".  A flag a command cannot honour is dropped in silence"
                             " otherwise, which reads exactly like one that was applied.")
                        {:type :unknown-option :mismatch :unknown-key :cmd cmd
                         :unread (mapv #(str "--" (name %)) (sort unread))
                         :reads  (mapv #(str "--" (name %)) (sort allowed))}))))))

(defn usage
  "The `--help` text: every command, its operands and a one-line gloss."
  []
  (let [w (apply max (map (fn [[c _ _ ops]] (count (str c " " ops))) command-table))]
    (str "vaelii — a command-line driver for a KB\n\n"
         "  lein cli <command> [args…] [--dir <path>] [--starter] [--memory]\n\n"
         "Quote every argument. A shell eats parens, brackets and `?`:\n"
         "  lein cli assert '(dog Muffet)' CxNaturalWorld --dir /tmp/kb\n"
         "  lein cli match  '(dog ?x)'   CxNaturalWorld --dir /tmp/kb\n\n"
         "Commands:\n"
         (str/join "\n"
                   (for [[c _ _ ops gloss] command-table]
                     (str "  " (format (str "%-" w "s")
                                       (str c (when (seq ops) (str " " ops))))
                          "   " gloss)))
         "\n\nOptions.  The first three name the KB and go with any command; the rest"
         " belong to\nthe commands named beside them, and are refused elsewhere:\n"
         "  --dir <path>          the store there, under its own backend, or a new :disk-log\n"
         "                        store (recovered on open); absent, in-memory.  Its parent\n"
         "                        must exist: the CLI creates the KB's directory, nothing above\n"
         "  --memory              the in-memory KB, said explicitly\n"
         "  --starter             load the shipped starter schema\n"
         "  --strength <s>        assert, assert-rule: :monotonic instead of :default\n"
         "  --depth <n>           query, query?: how far to expand rules\n"
         "  --variant <v>         export: records | records+index\n"
         "  --compression <c>     export: gzip | xz | none\n"
         "  --format text         export: a text KB instead of a dump — one Cx<Name>.txt\n"
         "                        per context, the format `load` reads\n"
         "  --context <CxName>    describe: the vantage to read from; absent, every context\n"
         "  --nearest <n>         why-not: run a bounded search and name the n rules that\n"
         "                        came closest, with the antecedent each is missing\n"
         "  --verify              upgrade: recover anyway, and report whether belief changed\n"
         "  --trust               upgrade: keep an image written under other engine source,\n"
         "                        and rebuild only images the records moved behind\n"
         "  --sync                upgrade: then rewrite what a release renamed, and bring the\n"
         "                        shipped contexts to what this engine ships, one change\n"
         "                        at a time (writes the store)\n"         "  (repl takes all six — its options are fixed at start and each line reuses them)\n")))

(defn dispatch
  "Run one command against `kb` and return its result (a handle, a seq of sentences /
  solutions, a proof tree, …).  `args` are data; `opts` is the parsed option map.

  **A command that answers a set answers it sorted** (`in-content-order`): `match`,
  `query` and `ask` alongside `types` and `contexts`, so one KB prints the same output
  however its knowledge arrived.  `prove` keeps the DFS's order, which is a reading rather
  than an artifact."
  [kb cmd args opts]
  (check-args! cmd args opts)
  (if-some [run (some (fn [[c _ _ _ _ run]] (when (= c cmd) run)) command-table)]
    (run kb args
         {:strength (when-let [s (:strength opts)] {:strength (keyword s)})
          ;; `--depth n` says how far to expand rules.  Absent, the read needs no rule
          ;; (`query`'s contract), and there is no default to supply here either.
          :depth    (when-let [d (:depth opts)] {:max-depth (count-option "--depth" d)})
          ;; `--context C` names the vantage a read takes; absent, `?ctx` reads every context
          :ctx      (if-let [c (:context opts)] (symbol (str c)) '?ctx)
          :nearest  (when-let [n (:nearest opts)] {:nearest (count-option "--nearest" n)})
          :opts     opts})
    (throw (ex-info (str "unknown command: " cmd " — want one of "
                         (str/join ", " commands))
                    {:type :unknown-command :cmd cmd :commands commands}))))

;; ---- KB construction -----------------------------------------------------

(defn open-kb-from
  "Build the KB a run operates on from the parsed `opts`: `:dir` -> durable disk (recovered,
  with the reasoners the store records registered), else in-memory, which `:memory` also
  names explicitly, so `--memory --dir <path>` is refused.  `:starter` loads the shipped
  schema.  **A `--dir` whose parent does not exist is refused** (`:unknown-source`) and
  nothing is created, since the store creates every missing path component and a mistyped
  path would answer a read with `[]` at exit 0.  The CLI creates the KB's own directory and
  nothing above it, which is how a new KB is made from the shell.  A throw from the
  `:starter` load closes the KB before it propagates."
  [{:keys [dir starter memory] :as _opts}]
  (when (and memory dir)
    (throw (ex-info (str "--memory and --dir " dir " contradict — a memory KB has no"
                         " directory.  Drop one: --dir for the durable KB, --memory"
                         " (or neither) for the in-process one.")
                    {:type :unknown-option :mismatch :conflict :flags ["--memory" "--dir"]})))
  (when dir
    (let [f      (.getAbsoluteFile (File. (str dir)))
          parent (.getParentFile f)]
      (when (and (not (.exists f)) parent (not (.exists parent)))
        (throw (ex-info (str "no KB at --dir " dir ": it does not exist, and neither does its"
                             " parent " (.getPath parent) ".  The CLI creates a new KB's own"
                             " directory and nothing above it, so a mistyped path is refused"
                             " rather than answered from an empty store.  Check the path, or"
                             " create the parent first (mkdir -p " (.getPath parent) ").")
                        {:type :unknown-source :path (str dir) :missing (.getPath parent)})))))
  (let [kb (if dir
             (v/open-kb {:backend (or (v/store-backend dir) :disk-log) :dir dir
                         :reasoners :stored})
             (v/open-kb {}))]
    (when starter
      (try (starter/load-sources kb [:starter])
           (catch Throwable t
             (try (v/close! kb) (catch Throwable c (.addSuppressed t c)))
             (throw t))))
    kb))

(defn- sync-line
  "One change of `upgrade --sync`'s step-by-step sync as a progress line on stderr."
  [{:keys [done total op]}]
  (binding [*out* *err*]
    (println (str "sync " done "/" total
                  (when op (str " " (name (:op op)) " " (pr-str (:form op)) " in " (:context op)))))))

(defn upgrade!
  "Bring the store in `dir` up to this build, and report what that took.  Opens the store
  under the backend its files were written by, with `:recover? :auto`: a reasoning image this
  build can install is installed, and one written under another layout, engine source or
  policies is declined, belief is recovered from the records, and the recover writes a new
  image.  Closing the store writes the index image a rebuilt index leaves due.  Returns

    {:dir :backend
     :reasoning :current | :rebuilt | :written | :no-image
     :image  {:format :network :written-at :source}   ; the manifest now on disk, :source cut to 12
     :index  :current | :rewritten | :no-image
     :verify …                                        ; with :verify only
     :sync {:added :removed :forwarded :refused} :renames {:rewritten …}}  ; with :sync only

  `:reasoning`: `:current` is an image it installed; `:rebuilt` one it declined and replaced;
  `:written` the first image of a store that held none; `:no-image` a backend that keeps none.
  Without `:sync` the records are never rewritten.  Options:

  - `:verify` moves the image to `reasoning.prev/` before the open, so the open recovers from
    the records, then compares the two (`reasoning-image/compare-images`) and deletes the old
    one.  `:verify` in the result is `{:against source :labels :network :state}`, or one
    keyword: `:no-previous-image`, `:no-image`, `:layout-changed` or `:records-moved`.
  - `:trust` opens with `:recover? :trust`: belief is recovered only when the records
    moved.  It refuses `:verify` (`:unknown-option`).
  - `:sync` rewrites what a release renamed (`sync/rename!`) and syncs the shipped contexts
    (`sync/sync-each!`, a progress line per change on stderr) after the open and `:verify`.
    A KB whose `v/write-hazards` is not empty is not synced: `:sync` is `{:skipped [hazard …]}`.

  A directory holding no store is refused (`:unknown-source`).  `!` because the image it
  replaces cannot be read back."
  ([dir] (upgrade! dir {}))
  ([dir {:keys [verify trust] sync? :sync}]
   (let [backend   (or (v/store-backend dir)
                       (throw (ex-info (str "no store at " dir " — upgrade opens an existing"
                                            " store and creates none")
                                       {:type :unknown-source :path (str dir)})))
         _         (when (and verify trust)
                     (throw (ex-info (str "upgrade was given --verify and --trust — --verify"
                                          " recovers belief under this build and --trust"
                                          " keeps the image's; pass one")
                                     {:type :unknown-option :mismatch :conflict
                                      :flags ["--verify" "--trust"]})))
         bdir      (File. (str dir) ^String ri/dir-name)
         prev      (File. (str dir) (str ri/dir-name ".prev"))
         manifest  (File. bdir "manifest.edn")
         index     (File. (str dir) "index/snapshot.meta")
         mtime     (fn [^File f] (when (.exists f) (.lastModified f)))
         short     (fn [^String s] (some-> s (subs 0 (min 12 (count s)))))
         had?      (.exists manifest)
         old       (ri/read-manifest bdir)
         i0        (mtime index)]
     (when verify
       ;; a `reasoning.prev/` left by an interrupted --verify holds an image this build declined
       (ri/delete-image! prev)
       (ri/move-image! bdir prev))
     (let [kb       (v/open-kb {:backend backend :dir (str dir) :recover? (if trust :trust :auto)
                                :reasoners :stored})
           [opened verified synced renamed]
           (try
             ;; the open's image is read before the sync moves the records the close then
             ;; writes a new image for, so `:reasoning` and `:verify` describe the open
             (let [opened   (ri/read-manifest bdir)
                   verified (when verify
                              (cond
                                (nil? old)    :no-previous-image
                                (nil? opened) :no-image
                                (not= (select-keys old [:format :network])
                                      (select-keys opened [:format :network])) :layout-changed
                                (not= (:records old) (:records opened))    :records-moved
                                :else (assoc (ri/compare-images prev bdir)
                                             :against (short (:source old)))))
                   [synced renamed]
                   (when sync?
                     (if-let [hz (not-empty (v/write-hazards kb))]
                       [{:skipped (vec (sort (keys hz)))}]
                       (let [renamed (sync/rename! kb)]
                         [(sync/sync-each! kb sync-line) renamed])))]
               [opened verified synced renamed])
             (finally (v/close! kb)))
           i1       (mtime index)
           fresh    (ri/read-manifest bdir)
           opened   (or opened fresh)]
       (when verify
         (if fresh (ri/delete-image! prev) (ri/move-image! prev bdir)))
       (cond-> {:dir     (str dir)
                :backend backend
                :reasoning (cond (nil? opened)    :no-image
                                 (not had?)       :written
                                 (= old opened)   :current
                                 :else            :rebuilt)
                :image   (some-> fresh
                                 (select-keys [:format :network :written-at])
                                 (assoc :source (short (:source fresh))))
                :index   (cond (nil? i1) :no-image (= i0 i1) :current :else :rewritten)}
         verify (assoc :verify verified)
         sync?   (assoc :sync synced)
         renamed (assoc :renames renamed))))))

;; ---- the shell -----------------------------------------------------------

(defn- show [x] (if (coll? x) (pp/pprint x) (println x)))

(defn on-stderr
  "A log fn that writes where `f` does, with `*out*` bound to `*err*`.  The engine's `log!`
  calls go through Trove's console backend, which prints to `*out*` (docs/operations.md,
  \"Logging\"), and `*out*` here is a script's `lein cli match … > answers.edn`: at `:info`
  an ordinary `export` or a starter load lands lines inside the answer.  A wrapper, not a
  level, since the daemon and the browser want the lines where they are."
  [f]
  (fn [& args] (binding [*out* *err*] (apply f args))))

(defn- err!
  "One diagnostic line on **stderr** — a refusal must not land inside the data a
  script is reading off stdout."
  [& parts]
  (binding [*out* *err*] (apply println parts)))

(defn refusal-line
  "The line a refusal prints: `error: [<:type>] <message>`.

  The `:type` is what a caller branches on (docs/troubleshooting.md), and every other
  surface carries it — the daemon on the wire, the browser as a chip.  A shell reads
  only the line, so the keyword goes on it, in brackets straight after `error: `, and
  the message after it is the engine's own words, unchanged.  A throwable carrying no `:type` — a
  `FileNotFoundException`, a `StackOverflowError` — is `:internal-error`, the class the
  daemon answers one with, so the bracket is on every refusal line and never empty."
  [^Throwable e]
  (str "error: [" (or (:type (ex-data e)) :internal-error) "] "
       (or (ex-message e) (.getName (class e)))))

(defn- repl-loop
  "Interactive loop: each line is `<cmd> <edn-forms…>` (no `--flags` — options are
  fixed at repl start).  Holds `kb` in-process, so a memory KB accumulates for the
  session.  Ends on `exit` / `quit` / EOF."
  [kb opts]
  (println "vaelii repl —" (str/join " " commands) "— or help, or exit")
  (loop []
    (print "vaelii> ") (flush)
    (when-let [line (read-line)]
      (let [line (str/trim line)]
        (cond
          (#{"exit" "quit"} line) (println "bye")
          (str/blank? line)       (recur)
          (#{"help" "--help"} line) (do (println (usage)) (recur))
          ;; `Throwable`, as the browser's untrusted-EDN reads: a deeply nested line
          ;; raises `StackOverflowError` out of `read-forms`, and the loop dying on a
          ;; line of input is the one thing a shell must not do
          :else (do (try
                      (let [cmd  (re-find #"^\S+" line)
                            rest* (str/triml (subs line (count cmd)))]
                        (if (= cmd "repl")
                          (println "already in a repl")
                          (show (dispatch kb cmd (read-forms rest*) opts))))
                      (catch Throwable e
                        ;; stdout on purpose, alone among the error paths: the REPL is a
                        ;; conversation, and its errors belong in the transcript beside
                        ;; the line that caused them — nothing scripts this stream
                        (println (refusal-line e))))
                    (recur)))))))

(defn- upgrade-from-the-shell
  "`upgrade`'s arm of `without-a-kb`: `--dir` is the store it brings up to this build, and
  `--memory` or `--starter` name a KB it does not open, so each is refused."
  [_args opts]
  (cond
    (nil? (:dir opts))
    (throw (ex-info "upgrade needs --dir <path>, the store to bring up to this build"
                    {:type :unknown-option :mismatch :missing-value :flag "--dir"}))
    (or (:memory opts) (:starter opts))
    (throw (ex-info (str "upgrade reads --dir alone — --memory and --starter"
                         " name a KB it does not open")
                    {:type :unknown-option :mismatch :conflict
                     :flags (vec (keep #(when (% opts) (str "--" (name %)))
                                       [:memory :starter]))}))
    ;; the recover an upgrade pays is the longest open a store has: the memory guard lowers
    ;; the cache profile's pressure as the heap fills, and the closure cache evicts to the
    ;; lowered bound on its next store, so no list of KBs is needed for the guard to reach it
    :else (do (v/install-memory-guard! {:kbs (constantly nil)})
              (upgrade! (:dir opts) (select-keys opts [:verify :trust :sync])))))

(def ^:private without-a-kb
  "The commands `run` answers without opening the run's KB, each with the fn that answers it
  from `[args opts]`.  Opening a `--dir` KB takes the directory's single-writer lock, so a
  command that reads no KB would be refused whenever a daemon owns the directory.
  `upgrade` opens and closes a store of its own (`upgrade!`); `diff` reads two text KBs into
  KBs of their own.  `--dir`, `--memory` and `--starter` name the run's KB and change
  nothing they print."
  {"upgrade" upgrade-from-the-shell
   "diff"    (fn [args _opts] (diff-text-kbs args))})

(defn run
  "Parse `argv`, open the KB, run the command and print its result; return the exit status.
  With `repl` (or no command) it drops into the interactive loop.  **Every refusal is one
  line on stderr and exit 1** (`refusal-line`), naming its `:type`.  An unknown command word
  is exit 2, with the command list and the `help` pointer after the line.  **Everything that
  needs no KB is answered before one is opened** (it would take the single-writer lock and
  may create a store): `help`, the flag and operand checks, and the commands in
  `without-a-kb`.  It catches `Throwable`, since a missing `load` file raises
  `FileNotFoundException` and a deeply nested EDN argument raises `StackOverflowError`."
  [argv]
  (try
    (let [[positionals opts] (parse-opts argv)
          [cmd & args]       positionals
          session?           (or (nil? cmd) (= cmd "repl"))]
      (if (or (:help opts) (= cmd "help"))
        (do (println (usage)) 0)
        (do
          (check-flags! cmd opts)
          (if (and (not session?) (not (some #{cmd} commands)))
            (do (err! (refusal-line (ex-info (str "unknown command: " cmd)
                                             {:type :unknown-command :cmd cmd
                                              :commands commands})))
                (err! "commands:" (str/join " " commands))
                (err! "`lein cli help` for what each one takes")
                2)
            (let [args (when-not session?
                         (let [args (mapv #(read-arg cmd %) args)]
                           (check-args! cmd args opts)
                           args))]
              (if-let [answer (without-a-kb cmd)]
                (show (answer args opts))
                (let [kb (open-kb-from opts)]
                  (try
                    (if session?
                      (repl-loop kb opts)
                      (show (dispatch kb cmd args opts)))
                    (catch Throwable t
                      (try (v/close! kb) (catch Throwable _ nil))
                      (throw t)))
                  (v/close! kb)))
              0)))))
    (catch Throwable e
      (err! (refusal-line e))
      1)))

(defn -main
  "Run one command (`run`) and leave with its exit status."
  [& argv]
  ;; `alter-var-root` rather than a `binding`: the durable store's compaction and fsync
  ;; lines come off the durability scheduler's own thread, which no thread-local binding
  ;; here reaches.  Installed before anything opens a KB, over the engine's console
  ;; backend at `:info` or the level `VAELII_LOG_LEVEL` installed at load.
  (when-not (v/log-level) (v/set-log-level :info))
  (alter-var-root #'trove/*log-fn* on-stderr)
  (let [status (run argv)]
    (when-not (zero? status)
      (System/exit status))))
