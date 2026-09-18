;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.config-surface-test
  "The configuration surface, pinned: every `VAELII_*` environment variable and every
  `vaelii.*` JVM system property the build reads, collected from the sources at runtime
  and frozen against `test/golden/config-surface.edn`.

  **Why a golden and not a roster.** `kb/opt-keys` and its eleven neighbours are public
  *because* a caller should be able to ask \"is this a real option?\", and a caller that
  can ask does not have to find out from a wrong answer.  Nothing outside a map carries
  that promise: a misspelt environment variable is unset, a renamed one is unset, and
  the process runs on the default reporting nothing.  So the names are pinned here
  instead, and the pin is what makes a rename a failing test rather than a support
  ticket — deployment scripts, systemd units and `docs/operations.md` reference them by
  name.

  ## On failure

  - **A REMOVED name is breaking.**  Restore it, or take the CHANGELOG entry:
    CONTRIBUTING §3.8 files a renamed or deleted switch as **Breaking**, with the
    migration line naming the new spelling.
  - **An ADDED name is not noise.**  Run `regenerate-golden!` and commit the golden in
    the same commit as the switch.  This is the half that gets waived, and it is the
    half that makes the golden a record rather than a ratchet: a new name nobody wrote a
    table row for is how a surface grows six undocumented switches, one at a time.

  ## What the scan reads

  Five forms over `src/`, `test/`, `bench/`, `project.clj` and `scripts/*.sh`, all
  normalized to the name as it is spelled where it is set:

  - `(System/getenv \"VAELII_…\")` — a literal environment variable.
  - `(System/getProperty \"vaelii.…\")` — a literal system property.
  - `(prop-bool \"…\")` / `prop-long` / `prop-double` / `prop-enum`, alias-qualified or
    not — `vaelii.impl.config`'s readers, which take the name as an **argument**.
    Twelve of the twenty-one properties reach `System/getProperty` only this way, so a
    scanner built on the two literal forms alone finds under half of them and reports
    itself complete.  `the-scan-catches-the-helper-form` is the test that says so.
  - `(raw \"…\")` — the reader **under** those helpers, called with a literal name where a
    switch has no domain to parse: an empty domain has nothing for `prop-enum` to accept,
    so the reader is called directly and the value is refused whatever it says.  A
    refused switch is still a name the build reads — `check!` reads it at every
    `open-kb`, and an operator whose unit file sets it meets the refusal — so it belongs
    on this surface exactly as much as one with a default.  Leaving the form unscanned is
    how such a name drops off the golden and out of the table while the code still fails
    every open on it.
  - `${VAELII_…}` in a shell script.  One regex over `.sh` text rather than a shell
    parser, and it is enough because the name carries its own prefix.

  The Clojure forms sit at three depths on purpose, and the two tests below keep them
  apart: the literal pair is what a naive scanner sees, the helper form is what the
  domain-carrying switches hide behind, and `raw` is what the domain-*less* one does.
  Each depth is asserted to reach switches the depths above it do not, so widening one
  form to cover another's job makes that assertion unfalsifiable rather than making it
  pass.

  A name is an environment variable when it is spelled in caps and a system property
  otherwise — the same rule `config/raw` dispatches on, and nothing in the tree names a
  switch both ways.

  This namespace spells the forms in order to test them, so it is the one source file
  the scan skips: its own matches are not the tree's."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.config :as config])
  (:import [java.io File]))

(def ^:private golden-file "test/golden/config-surface.edn")
(def ^:private doc-file "docs/operations.md")
(def ^:private self-file "test/vaelii/config_surface_test.clj")

;; ---- the scan -----------------------------------------------------------

(def clj-forms
  "The four Clojure spellings of a read, each capturing the switch's name.  The last two
  are the ones worth having, and for the same reason at two depths: `prop-long` takes the
  name as an argument and `raw` is what `prop-long` itself calls, so a property read
  either way appears in no `System/getProperty` literal anywhere."
  [#"System/getenv\s+\"([A-Z][A-Z0-9_]*)\""
   #"System/getProperty\s+\"(vaelii\.[a-z0-9.-]+)\""
   #"\((?:[a-z][\w.-]*/)?prop-(?:bool|long|double|enum)\s+\"([A-Za-z][\w.-]*)\""
   #"\((?:[a-z][\w.-]*/)?raw\s+\"([A-Za-z][\w.-]*)\""])

(def shell-form
  "`${VAELII_…}` in a shell script.  Deliberately prefix-anchored: a regex for every
  `${CAPS}` collects each script's own local variables, and telling those from a knob
  needs a shell parser."
  #"\$\{(VAELII_[A-Z0-9_]+)")

(def ^:private not-a-switch
  "Names the scan finds that configure nothing, each with why.  Explicit rather than a
  pattern — a pattern excusing `vaelii.test.*` would excuse a real switch the day
  somebody names one `vaelii.test.mode`."
  {"vaelii.test.bool"
   (str "config_test's probe for `prop-bool` itself. The reader takes the name as an "
        "argument, so exercising it needs a name; nothing reads this one.")})

(defn- clj-sources []
  (->> (concat (mapcat (comp file-seq io/file) ["src" "test" "bench"])
               [(io/file "project.clj")])
       (filter #(.isFile ^File %))
       (filter #(str/ends-with? (.getPath ^File %) ".clj"))
       (remove #(= self-file (.getPath ^File %)))))

(defn- shell-sources []
  (->> (file-seq (io/file "scripts"))
       (filter #(.isFile ^File %))
       (filter #(str/ends-with? (.getPath ^File %) ".sh"))))

(defn scan-text
  "Every switch `text` names under `forms`, as a set.  Separated from the file walk so
  the scanner is testable on a string — which is how the helper form is asserted without
  planting a fake switch in a source file."
  [forms text]
  (into #{} (mapcat (fn [rx] (map second (re-seq rx text)))) forms))

(defn- sites-in
  "`{name [\"path:line\" …]}` for one file, in line order."
  [forms ^File f]
  (let [path (.getPath f)]
    (->> (str/split-lines (slurp f))
         (map-indexed (fn [i line] [(inc i) line]))
         (reduce (fn [acc [n line]]
                   (reduce (fn [acc nm] (update acc nm (fnil conj []) (str path ":" n)))
                           acc
                           (mapcat (fn [rx] (map second (re-seq rx line))) forms)))
                 {}))))

(defn surface-sites
  "`{name [\"path:line\" …]}` over the whole tree, the names that configure nothing
  dropped."
  []
  (apply dissoc
         (apply merge-with into
                (concat (map (partial sites-in clj-forms) (clj-sources))
                        (map (partial sites-in [shell-form]) (shell-sources))))
         (keys not-a-switch)))

(defn- env-var? [nm] (some? (re-find #"^[A-Z]" nm)))

(defn current-surface
  "`{:env-vars #{…} :properties #{…}}` as the sources read today."
  []
  (let [names (keys (surface-sites))]
    {:env-vars   (into (sorted-set) (filter env-var?) names)
     :properties (into (sorted-set) (remove env-var?) names)}))

(defn regenerate-golden!
  "Rewrite `test/golden/config-surface.edn` from the sources.  Call it from a REPL after
  a **deliberate** change to the surface — adding a switch, or removing one with the
  CHANGELOG entry beside it — and commit the golden in that same commit."
  []
  (let [{:keys [env-vars properties]} (current-surface)]
    (spit golden-file
          (str ";; Frozen configuration surface — every VAELII_* environment variable\n"
               ";; and vaelii.* system property the build reads.\n"
               ";; Regenerate: (vaelii.config-surface-test/regenerate-golden!), and read\n"
               ";; that namespace's docstring first — a removed name is a breaking change.\n"
               ";; Each one has a row in docs/operations.md, which the same test checks.\n"
               (with-out-str
                 (pprint/pprint {:env-vars (vec env-vars)
                                 :properties (vec properties)}))))))

(defn- golden []
  (let [{:keys [env-vars properties]} (edn/read-string (slurp golden-file))]
    {:env-vars (set env-vars) :properties (set properties)}))

;; ---- the pin, both ways -------------------------------------------------

(deftest the-configuration-surface-is-frozen
  (let [current (current-surface)
        frozen  (golden)]
    (doseq [k [:env-vars :properties]]
      (let [removed (set/difference (frozen k) (current k))
            added   (set/difference (current k) (frozen k))]
        (is (empty? removed)
            (str "BREAKING: " (name k) " removed or renamed: " (sort removed)
                 ". Deployment scripts, systemd units and docs/operations.md name"
                 " these — restore them, or take the CONTRIBUTING §3.8 Breaking entry"
                 " with the migration line, and regenerate the golden in that commit."))
        (is (empty? added)
            (str "New " (name k) ": " (sort added) " — this extends the published"
                 " surface. Run (vaelii.config-surface-test/regenerate-golden!), give"
                 " each one a row in docs/operations.md, and commit the golden in this"
                 " same commit."))))))

(deftest the-scan-catches-the-helper-form
  ;; The assertion a scanner built on the two literal forms alone cannot make, and the
  ;; ten switches such a scanner misses are the argument for it: a reader that takes the
  ;; name as an argument shadows the literal the scan looks for.
  (testing "a switch read through a config helper is found"
    (doseq [form ["(prop-long \"vaelii.disk.nonsense\" 1 0 nil)"
                  "(config/prop-bool \"vaelii.disk.nonsense\" false)"
                  "(prop-double \"vaelii.disk.nonsense\" 0.5 0 1)"
                  "(prop-enum \"VAELII_NONSENSE\" {} nil \"a nonsense\")"]]
      (is (seq (set/intersection #{"vaelii.disk.nonsense" "VAELII_NONSENSE"}
                                 (scan-text clj-forms form)))
          (str "the scan missed " form))))
  (testing "and the helper form is the ONLY way most of the store's switches are read"
    ;; So a scanner that dropped the third regex would lose these nine and report a
    ;; complete surface: this is the assertion that fails when somebody simplifies it.
    ;; `src/` alone, because a test that saves and restores a property around a case
    ;; names it literally without reading it as configuration.
    (let [literal-only (into #{}
                             (comp (filter #(str/starts-with? (.getPath ^File %) "src/"))
                                   (mapcat #(scan-text (subvec clj-forms 0 2) (slurp %))))
                             (clj-sources))]
      (doseq [nm ["vaelii.disk.auto-compact" "vaelii.disk.fsync" "vaelii.disk.compress"
                  "vaelii.disk.tokens" "vaelii.disk.cache" "vaelii.disk.sync-ms"
                  "vaelii.disk.compact-dead-ratio" "vaelii.disk.compact-min-interval-ms"
                  "vaelii.disk.lock"]]
        (is (not (contains? literal-only nm))
            (str nm " now has a literal System/getProperty read too — if that is"
                 " deliberate, drop it from this list; the point of the list is that"
                 " the two literal forms alone do not see these."))))))

(deftest the-scan-catches-the-domainless-form
  ;; The third depth, and the one a scanner arrives at last: a switch whose domain is
  ;; EMPTY has nothing for `prop-enum` to accept, so it is read straight off `raw` and
  ;; refused whatever it says.  `vaelii.index.snapshot` is that switch — `check!` calls
  ;; its reader at every `open-kb`, so an operator with `-Dvaelii.index.snapshot=true` in
  ;; a unit file meets a hard refusal — and a scan blind to the form drops the name from
  ;; the golden and its row from the table while the code goes on failing every open on
  ;; it.  A refused switch is one the build reads.
  (testing "a switch read straight off `raw` is found"
    (doseq [form ["(raw \"vaelii.disk.nonsense\")"
                  "(config/raw \"VAELII_NONSENSE\")"]]
      (is (seq (set/intersection #{"vaelii.disk.nonsense" "VAELII_NONSENSE"}
                                 (scan-text clj-forms form)))
          (str "the scan missed " form))))
  (testing "and the tree's own one is on the surface"
    (is (contains? (set (keys (surface-sites))) "vaelii.index.snapshot")
        "the refused switch is a name the build reads, so it is pinned like any other"))
  (testing "which neither shallower depth reaches"
    ;; The assertion that keeps the fourth regex from being redundant with the third:
    ;; over `src/`, no literal read and no `prop-*` helper names this switch.  If one
    ;; ever does, the reader grew a domain and this whole form is somebody's dead weight.
    (let [shallower (into #{}
                          (comp (filter #(str/starts-with? (.getPath ^File %) "src/"))
                                (mapcat #(scan-text (subvec clj-forms 0 3) (slurp %))))
                          (clj-sources))]
      (is (not (contains? shallower "vaelii.index.snapshot"))
          (str "vaelii.index.snapshot is now read literally or through a prop-* helper"
               " — if that is deliberate it has a domain, and this test is describing a"
               " reader that no longer exists")))))

;; ---- and the roster the engine reads it through -------------------------

(deftest the-roster-names-only-switches-the-build-reads
  ;; `config/switches` is the other half of this pin.  The golden says which names the
  ;; tree reads; the roster says which ones `check!` walks — and the roster is what makes
  ;; a reader without a `check!` line a load failure (`check-switches!`).  Neither can see
  ;; the other: `check-switches!` runs at namespace load and cannot read files, and the
  ;; scan reads `(prop-bool "…")` forms rather than the roster's plain strings.  So a row
  ;; naming a switch that no reader reads — a typo in a `:names` vector, or a name kept
  ;; after its reader stopped reading it — passes load and every open, and `check!` calls
  ;; a reader that checks something else.  This is the assertion that catches it.
  (let [scanned (set (keys (surface-sites)))
        ghosts  (remove scanned config/switch-names)]
    (is (empty? ghosts)
        (str "config/switches names " (pr-str (vec ghosts)) ", which no reader in the"
             " tree reads. A `:names` entry is a claim about what its `:reader` reads;"
             " fix the spelling, or drop the name with the reader that stopped reading"
             " it."))))

(deftest every-switch-config-reads-is-on-the-roster
  ;; The converse, over this namespace alone.  `check-switches!` proves every *reader* has
  ;; a row; nothing there proves the row's names are all of what the reader reads, because
  ;; a var carries no record of the strings inside it.  Scanning `config.clj` does: every
  ;; name it reads is one `check!` must reach, and a second name added to a reader — as
  ;; `asp-solver` has, property first and environment variable second — without being
  ;; added to its row is a spelling that is never checked and silently wins or loses to
  ;; the one that is.
  (let [in-config (set (keys (sites-in clj-forms (io/file "src/vaelii/impl/config.clj"))))
        missing   (remove (set config/switch-names) in-config)]
    (is (empty? missing)
        (str "vaelii.impl.config reads " (pr-str (vec (sort missing))) " and no row on"
             " `config/switches` names it, so `check!` never reads it at the open."))))

;; ---- and the table that describes it ------------------------------------

(def ^:private unpinned
  "Switches `docs/operations.md` documents that this scan cannot reach, each with the
  reason.  Every one is shell-only and unprefixed, which is exactly what puts it out
  of range: `${VAELII_…}` is name-shaped enough for one regex, `${GATE_JOBS}` is not,
  and a regex for every `${CAPS}` collects each script's own locals.  A rename of one of
  these is caught by review rather than by this test."
  {"GATE_JOBS"         "scripts/gate.sh, the test stage's shard count"
   "PERF_TOLERANCE"    "scripts/gate.sh, passed through to `lein perf --tolerance`"
   "TEST_BACKENDS_OUT" "scripts/test-backends.sh, its log directory"
   "TEST_SWEEPS_OUT"   "scripts/test-sweeps.sh, its log directory"
   "SUITE_PROGRESS"    "scripts/lib/suite-marks.sh, marks or one line per namespace"
   "TEST_MATRIX_OUT"   "scripts/test-matrix.sh, its log directory"
   "MATRIX_JOBS"       "scripts/test-matrix.sh, how many configurations run at once"
   "MATRIX_JVM_OPTS"   "scripts/test-matrix.sh, extra JVM_OPTS for every configuration"
   "TEST_MATRIX_SEED"  "scripts/test-matrix.sh, the seed its launch order is shuffled with"
   "MATRIX_HEARTBEAT"  "scripts/test-matrix.sh, seconds between its progress lines"})

(deftest an-unpinned-switch-is-read-by-the-script-it-names
  ;; The hatch is a hand-kept list that the ghost-row check reads as *real* — `real` is
  ;; the scanned names plus these keys — so adding an entry is all it takes to document a
  ;; switch nothing reads.  Ten entries stand here today.  What keeps it
  ;; honest is that each reason already names the file that reads the switch, which makes
  ;; the claim checkable without a regex for every `${CAPS}` in every script.
  (doseq [[nm why] (sort-by key unpinned)]
    (let [path (second (re-find #"(scripts/[\w./-]+?)[,\s]" why))]
      (is (some? path)
          (str nm ": its reason names no file, so nothing here can check it"))
      (when path
        (let [f (io/file path)]
          (is (.exists f) (str nm ": names " path ", which is not in the tree"))
          (when (.exists f)
            (is (str/includes? (slurp f) nm)
                (str nm ": " path " does not read it — a switch nothing reads is a row"
                     " in docs/operations.md describing nothing"))))))))

(def ^:private undocumented-by-design
  "Switches the scan finds that the table deliberately has no row for.

  Empty, and that is the finding rather than an oversight: the table groups by who sets
  a switch — operator, developer, CI and bench — so there is a place in it for every
  name the tree reads, and a switch with nowhere to go is a switch somebody would have
  to guess at.  A name belongs here only when a row would misdescribe the surface
  rather than describe it, and it carries the sentence saying which."
  {})

(defn- config-section
  "The lines of `docs/operations.md` under the configuration heading, up to the next
  `##`.  Scoped to that section so the option table at the top of the file, and any
  other table added later, are not read as claims about switches."
  []
  (->> (str/split-lines (slurp doc-file))
       (drop-while #(not (str/starts-with? % "## Configuration")))
       rest
       (take-while #(not (str/starts-with? % "## ")))))

(defn documented
  "`{name \"path:line\"}` off the table: every row whose first cell is a backticked name
  and whose second is a backticked citation.

  A citation is `path:N` or `path:N+`, the second being a **floor** — named at or after
  line N. The floor is what rows carry, since an exact line drifts under any edit above
  it; both spellings parse here and
  `every-citation-in-the-table-resolves-to-a-line-that-names-the-switch` reads the
  difference."
  []
  (into {}
        (keep (fn [line]
                (when (str/starts-with? (str/triml line) "|")
                  (let [cells (mapv str/trim (str/split line #"\|"))
                        nm    (second (re-matches #"`([A-Za-z][\w.-]*)`" (get cells 1 "")))
                        cite  (second (re-matches #"`([\w./-]+:\d+\+?)`" (get cells 2 "")))]
                    (when (and nm cite) [nm cite])))))
        (config-section)))

(deftest every-switch-the-code-reads-has-a-row-in-the-operational-doc
  (let [rows    (set (keys (documented)))
        missing (-> (set (keys (surface-sites)))
                    (set/difference rows)
                    (set/difference (set (keys undocumented-by-design))))]
    (is (empty? missing)
        (str "no row in " doc-file " for: " (sort missing)
             ". A switch nothing documents is one an operator finds by reading the"
             " source. Give each a row — name, where it is read, its legal values, its"
             " default, and what it decides — or list it in `undocumented-by-design`"
             " with the sentence saying why a row would misdescribe it."))))

(deftest every-switch-the-doc-documents-is-one-the-code-reads
  ;; The reverse, and the one a doc-only edit introduces: a row for a name nothing reads
  ;; is the same lie as a name with no row, and it is the more convincing of the two.
  (let [real  (into (set (keys (surface-sites))) (keys unpinned))
        ghost (set/difference (set (keys (documented))) real)]
    (is (empty? ghost)
        (str "rows in " doc-file " for switches nothing reads: " (sort ghost)
             ". Either the name is misspelt, or the reader it described is gone and the"
             " row went with it."))))

(deftest every-citation-in-the-table-resolves-to-a-line-that-names-the-switch
  ;; What makes a citation worth carrying: it is checked. A citation nothing verifies is
  ;; a table a reader trusts and lands in the wrong place from.
  ;;
  ;; **The anchor is a floor, not an address** — `file:5800+` reads "start reading at
  ;; line 5800; the switch is named at or below it". An exact `file:5800` was checked
  ;; exactly, and every one of them broke the moment anything above it was edited: a
  ;; comment added six screens up failed this test with a diff that had nothing to do
  ;; with configuration, and the fix was always to retype a number nobody is indistinguishable from a
  ;; number.
  ;;
  ;; The floor is checked against the file's **first** mention of the switch, not
  ;; against any mention at or below it. Searching downward for any hit was the obvious
  ;; reading and it is too weak to catch anything: `VAELII_WEB_PORT` is named in a
  ;; docstring, in `--port` help text and in a startup line, so a floor a hundred lines
  ;; *past* the read still found one of them and passed. `floor <= first-mention` keeps
  ;; the whole point — insertion above moves the first mention down and the floor still
  ;; holds, without bound — while a floor that has drifted past what it cites fails,
  ;; which is the one thing a citation must not do quietly. The exact form is still
  ;; honoured where a row wants it.
  (let [sites (surface-sites)]
    (doseq [[nm cite] (sort (documented))]
      (let [[path n] (str/split cite #":")
            floor?   (str/ends-with? n "+")
            start    (parse-long (str/replace n #"\+$" ""))
            f        (io/file path)
            ls       (when (.isFile f) (vec (str/split-lines (slurp f))))
            first-at (when ls
                       (first (keep-indexed
                               (fn [i l] (when (str/includes? l nm) (inc i))) ls)))]
        (is (some? ls) (str nm ": " cite " names no file"))
        (when ls
          (if floor?
            (is (and first-at (<= start first-at))
                (str nm ": the floor " cite " does not hold — "
                     (if first-at
                       (str path " first names it at line " first-at
                            ", above the floor, so the floor has drifted past what it cites")
                       (str "nothing in " path " names it at all"))
                     (when-let [real (seq (sites nm))]
                       (str "; it is read at " (str/join ", " real)))))
            (is (when-let [l (get ls (dec start))] (str/includes? l nm))
                (str nm ": " cite " does not name it"
                     (when-let [real (seq (sites nm))]
                       (str " — it is read at " (str/join ", " real)))))))))))

(deftest a-citation-floor-is-round-so-it-survives-an-edit-above-it
  ;; The floor only buys drift-tolerance if it is actually below the read, and rounding
  ;; is what makes that true by construction rather than by luck. A floor typed at the
  ;; exact read line is one deletion above from being wrong again, which is the failure
  ;; this whole form exists to retire.
  (doseq [[nm cite] (sort (documented))
          :let [[_ n] (str/split cite #":")]
          :when (str/ends-with? n "+")]
    (is (zero? (mod (parse-long (str/replace n #"\+$" "")) 10))
        (str nm ": the floor " cite " is not rounded — round it down to a multiple of 10"
             " so an edit above it has somewhere to go"))))

;; ---- and the validator that holds the roster to it ----------------------

(deftest the-roster-validator-refuses-a-half-wired-roster
  ;; What a load-time validator does not otherwise prove.  `check-switches!` runs once,
  ;; over one table, in a namespace that loads — so every branch it has ever taken is the
  ;; one that throws nothing, and a `remove` written the wrong way round reads exactly
  ;; like a roster with nothing wrong.  These drive it over tables that ARE wrong, which
  ;; is the only way to learn that it would say so.
  (let [check   @#'config/check-switches!
        refusal (fn [switches exempt publics]
                  (try (check switches exempt publics) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e))))
        row     (fn [reader & {:keys [names read-at] :or {read-at :open}}]
                  {:names (or names ["vaelii.test.name"]) :reader reader :read-at read-at})]
    (testing "the live tables pass, which is what the namespace load asserts"
      (is (= config/switches
             (check config/switches @#'config/not-a-switch-reader
                    (set (keys (ns-publics 'vaelii.impl.config)))))))
    (testing "a public var that is neither on the roster nor excused"
      ;; the rule the table exists for, and the one the old `:arglists` scan could not
      ;; state: `some-var` here stands for a switch read at the root of a `def`, which
      ;; carries no arglists and so was invisible to the scan while being exactly the
      ;; read `check!` would never make
      (let [data (refusal [] {} '#{some-var})]
        (is (= :bad-table-entry (:type data)))
        (is (= :unrostered-reader (:mismatch data)))
        (is (= 'some-var (:reader data)))))
    (testing "an exemption for something that is no longer public here"
      (is (= :stale-exemption (:mismatch (refusal [] '{gone "why"} #{})))))
    (testing "a var both rostered and excused, which is one of the two wrong about it"
      (is (= :exempt-and-rostered
             (:mismatch (refusal [(row #'clojure.core/inc)] '{inc "why"} '#{inc})))))
    (testing "an exemption with no reason, which is a suppression spelled longer"
      (is (= :blank-exemption (:mismatch (refusal [] '{inc ""} '#{inc}))))
      (is (= :blank-exemption (:mismatch (refusal [] '{inc nil} '#{inc})))))
    (testing "a row naming no switch, which `check!` calls and `switch-names` omits"
      (is (= :no-names
             (:mismatch (refusal [(row #'clojure.core/inc :names [])] {} '#{inc})))))
    (testing "a row reading at an entry point outside the vocabulary"
      (is (= :read-at
             (:mismatch (refusal [(row #'clojure.core/inc :read-at :sometimes)] {} '#{inc})))))
    (testing "two rows claiming one name, where which reader wins is the walk order"
      (is (= :duplicate-name
             (:mismatch (refusal [(row #'clojure.core/inc) (row #'clojure.core/dec)]
                                 {} '#{inc dec})))))))
