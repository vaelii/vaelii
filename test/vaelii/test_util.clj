;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.test-util
  "Shared test scaffolding that keeps every test **net-neutral** to KB content.

  A test must leave the KB exactly as it found it.  Two mechanisms enforce that:

    * gensym'd temporary terms — a test that asserts invents its individuals,
      predicates, types, and contexts with `tmp-ind` / `tmp-pred` / `tmp-type` /
      `tmp-ctx`, so its content is provably disjoint from any baseline ontology
      and can never collide with a real term.
    * the neutral fixtures — after each test the fixture retracts everything the
      test added (dependency-directed, so derived consequences fall away too) and
      then asserts the live sentex/justification/premise sets are back to their
      baseline.  The assertion is a genuine invariant: it fails only when retraction
      leaves residue, i.e. a real teardown gap.

  Fixture recipes:

    ;; a shared KB loaded once (starter / CxCore), neutral per test
    (use-fixtures :once (tu/loaded tu/load-starter!))
    (use-fixtures :each (tu/neutral))

    ;; a fresh KB rebuilt per test (empty or CxCore-loaded), neutral per test
    (use-fixtures :each (tu/neutral-fresh tu/fresh))

    ;; an inline KB inside one deftest (varied baselines in one file)
    (tu/with-neutral-kb [kb tu/fresh] ...)"
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [is]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.llm.ollama :as ollama]
            [vaelii.host.seed :as seed]
            [vaelii.host.starter :as starter]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.config :as config]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; ---- the switches, and the pin that hands their defaults back -----------
;;
;; Every switch below installs its implementation by ALTERING A ROOT: a replacement no
;; `binding` sees and no test undoes, which is exactly what a whole-suite sweep wants,
;; since the claim it tests is that the alternative answers identically.
;;
;; A **counted** gate wants the opposite.  A budget or a cost shape is a claim about one
;; configuration, so `assert_cost_test`, `lead_side_cost_test` and `join_lead_cost_test`
;; have to measure the shipped reader whichever sweep is running.  `chain/join-matches` is
;; the sharp edge: it takes its argument lead only under the reference matcher, so a gate
;; inheriting `VAELII_RETE=1` measures a join nobody wrote it about — which is what
;; `join_lead_cost_test` did until its fixture pinned the matcher.
;;
;; So the roots are READ here, before a single switch installs itself, and handed back by
;; `with-shipped-config`.  Read rather than restated: a default written down a second time
;; is a default that drifts, and a captured one cannot.

(def sweeps
  "The six configurations `scripts/test-sweeps.sh` runs, as data: the environment
  variable that selects each, and the vars whose root it replaces.  `test_util_test`
  holds the spellings against `scripts/lib/suite-configs.sh`, so a sweep added to that
  table without a row here fails — and the row is where its vars are named, which is what
  puts them in `shipped-defaults` for a counted gate to pin back.

  `VAELII_TEST_TMS` names none, and that is not an omission: the TMS is a KB **option**,
  chosen per `open-kb` rather than installed over a var, so a gate pins it by naming it in
  its space (`assert_cost_test`'s `cost-space`) and no binding could."
  [{:env "VAELII_TEST_TMS"       :vars []}
   {:env "VAELII_RETE"           :vars ['vaelii.impl.chain/*matcher*]}
   {:env "VAELII_HIER"           :vars ['vaelii.impl.resolution/*hierarchical-retrieval*]}
   {:env "VAELII_PLAN"           :vars ['vaelii.impl.plan/*enabled*]}
   {:env "VAELII_QUERY_ENGINE"   :vars ['vaelii.core/*query-engine*
                                        'vaelii.impl.inference/*max-depth*]}
   {:env "VAELII_QUERY_STRATEGY" :vars ['vaelii.core/*query-options*]}])

(def read-path-vars
  "The switches that decide **which reader answers**, short of replacing the matcher.  No
  sweep installs one — they are here because a counted gate is measured under them just
  the same, and one pin is better than the three that drifted.

  `*lead-side*` is the one measured to carry weight: `:scoped` leads a join from one
  predicate-scoped bucket per spec, which takes `join_lead_cost_test`'s reading from flat
  (32 at either width) to 27 against 39 — the structure that file exists to hold, inverted by
  a var it does not name.  The rest are pinned because `assert_cost_test` prices exact
  per-family budgets and each of them moves which family answers; both gates hold that
  claim with a test rather than asserting it here."
  ['vaelii.impl.resolution/*arg-root-retrieval*
   'vaelii.impl.resolution/*structural-index*
   'vaelii.impl.resolution/*lead-side*
   'vaelii.impl.sentex/*min-indexed-depth*])

(defn- naming-var
  "The var, other than the switch `vr`, whose root is the function `f`, or nil.  First the
  var `f`'s class names (`vaelii.impl.resolution$match_pattern` names
  `#'vaelii.impl.resolution/match-pattern`), then any non-dynamic `vaelii.*` var holding
  `f` itself."
  [vr f]
  (let [owner (some-> (class f) .getName clojure.lang.Compiler/demunge symbol)
        named (when (namespace owner) (find-var owner))]
    (if (and named (not= named vr) (identical? f (var-get named)))
      named
      (first (for [n     (all-ns)
                   :when (str/starts-with? (str (ns-name n)) "vaelii.")
                   [_ x] (ns-interns n)
                   :when (and (not= x vr) (not (:dynamic (meta x))) (identical? f (var-get x)))]
               x)))))

(def shipped-defaults
  "`{var -> default}` for every var the two rosters name, read before the switches below
  install themselves — so this is what the engine ships and not a transcription of it.

  A default that is a function another var defines is held as that var: `*matcher*`'s is
  `#'vaelii.impl.resolution/match-pattern`, not the function value.  An engine reload
  (`vaelii.reload-test`, the development browser) redefines the function, and a captured
  value would bind the code from before the reload — `chain/join-matches` then fails its
  `identical?` test against the reloaded `res/match-pattern` and walks the trie.
  `shipped-value` reads a default back."
  (into {} (map (fn [sym] (let [vr (requiring-resolve sym) root (var-get vr)]
                            [vr (or (when (fn? root) (naming-var vr root)) root)])))
        (concat (mapcat :vars sweeps) read-path-vars)))

(defn shipped-value
  "The shipped default of the rostered switch `vr` as it stands now: the root read at load,
  or the current root of the var `shipped-defaults` holds for a function-valued one."
  [vr]
  (let [d (get shipped-defaults vr)]
    (if (var? d) (var-get d) d)))

(defn- shipped-bindings
  "`{var -> shipped-value}` for the rostered switches `vars`, read at the call."
  [vars]
  (into {} (map (fn [vr] [vr (shipped-value vr)])) vars))

(defn with-shipped-config*
  "Functional core of `with-shipped-config`."
  [f]
  (with-bindings* (shipped-bindings (keys shipped-defaults)) f))

(defmacro with-shipped-config
  "Run `body` with every implementation switch bound to its shipped default, whatever the
  run inherited.  What a counted gate measures inside, and preferred to standing aside
  under the sweep: a gate that skips is a gate not running on the configuration somebody
  is currently changing.

  It **binds**, so a gate whose own axis is one of these binds it within and wins:
  `(with-shipped-config (binding [res/*lead-side* :scoped] …))`."
  [& body]
  `(with-shipped-config* (fn [] ~@body)))

(defn pinning
  "A `:each` fixture binding just the named vars back to the roots the engine SHIPS,
  whatever switch the run installed — the surgical half of `with-shipped-config`, for a
  file that answers FOR one implementation and so must keep answering for it under the
  sweep that replaces it.  `plan_test` measures which order the planner chooses, a
  question `VAELII_PLAN=0` deletes rather than reorders.

  One rather than all, deliberately: `with-shipped-config` would also take the file off
  the node engine, the alternative matcher and the reference retrieval, and a file that
  stops running under five sweeps to answer for one has traded a stand-aside for a
  larger one.  Pinning is what a file does INSTEAD of standing aside — the assertion
  count is identical under every configuration, which is what `config_expected_delta`
  reads.

  Every var must be one `shipped-defaults` rosters: an unrostered var is a pin that
  binds nil, which installs a third reader rather than the shipped one."
  [vars]
  (doseq [vr vars]
    (when-not (contains? shipped-defaults vr)
      (throw (ex-info (str vr " is not a rostered switch — name it in "
                           "`sweeps` or `read-path-vars` before pinning it")
                      {:type :unrostered-pin :var vr}))))
  ;; the bindings are read per call, so a function-valued default follows a reload
  (fn [f] (with-bindings* (shipped-bindings vars) f)))

(defmacro without-entailing
  "Run `body` with the argument declarations read as **constraints only** — the opt-out
  reading (`VAELII_ASSERTIVE_ARG_TYPES=0`), whatever the root is set to.  Entailing is on
  by default (docs/argtypes.md), so this is the reading a test pins when it asserts the
  constraint-only behavior rather than the shipped one.

  `with-pinned`'s job for the one switch it cannot do: `shipped-defaults` captures each
  root at *this* namespace's load, and this root is set at `vaelii.impl.checks`'s, which
  is earlier — so a capture would record the sweep's value as the shipped one.  The
  default is written out here instead, in the one place that has to state it.

  A test wants this when what it asserts is the **refusal**: with the entailment on there
  is no `:arg-type` conviction of a symbol argument to assert, because the declaration
  mints the type it demands rather than testing for it (docs/argtypes.md)."
  [& body]
  `(binding [checks/*assertive-arg-types?* false] ~@body))

(defmacro with-entailing
  "Run `body` with the argument declarations read as **entailments** — the shipped
  default reading, pinned regardless of the root so a run under
  `VAELII_ASSERTIVE_ARG_TYPES=0` still measures it.  The mirror of `without-entailing`,
  for a test whose subject is the entailment itself — what it mints, or what its
  per-assert read cost is."
  [& body]
  `(binding [checks/*assertive-arg-types?* true] ~@body))

(defmacro with-pinned
  "`pinning` around one test rather than a namespace's fixture, for a file the sweep
  should keep running everywhere else.  Prefer it: a fixture pins every test in the
  file, and a file loses a sweep it was passing under to answer for one test that was
  not.

    (tu/with-pinned [#'plan/*enabled*] …)"
  [vars & body]
  `((pinning ~vars) (fn [] ~@body)))

;; Run the *whole* suite through the incremental forward-chaining matcher
;; (`vaelii.impl.rete`) rather than the reference `chain` when `VAELII_RETE` is set.
;; A regression harness only — the default (unset) leaves the reference matcher in
;; place, so ordinary runs are untouched.  Loaded before any test, since every test
;; namespace requires this one.
;;
;; Read through `config/prop-bool` and not for presence: a switch whose every value
;; means *on* answers `VAELII_RETE=0` with the sweep the operator just turned off, and
;; an exported-but-empty variable with a sweep they never asked for.  The harness
;; switches take the same vocabulary as the engine's, so a spelling learned once works
;; everywhere.
(when (config/prop-bool "VAELII_RETE" false)
  ((requiring-resolve 'vaelii.impl.rete/enable!)))

;; And the same shape for the backward half: `VAELII_QUERY_ENGINE=inference` runs every
;; test's `prove` on the node engine (`vaelii.impl.inference`) instead of the goal-stack
;; DFS.  That is the cross-engine parity sweep — the two executors must be
;; failing-set-identical, exactly as the storage backends must be — and it is a root
;; binding rather than a fixture because it has to cover a lazily realized seq that
;; outlives whatever thread frame set it up.
(defn query-engine-override
  "The engine `VAELII_QUERY_ENGINE` names, or nil.  Read by tests that pin a
  DFS-specific artifact and must stand aside when the sweep is running.

  The domain is `*query-engine*`'s own three, refused rather than passed through: a
  bare `(keyword …)` turns a typo into an engine `case` falls off the end of, so the
  sweep runs the default and reports a clean pass for a configuration nothing ran."
  []
  (config/prop-enum "VAELII_QUERY_ENGINE"
                    {"dfs" :dfs "inference" :inference "hybrid" :hybrid}
                    nil
                    "dfs, inference, or hybrid"))

(when-let [e (query-engine-override)]
  (alter-var-root #'v/*query-engine* (constantly e))
  ;; The node engine has no default depth bound and refuses to start without one — the
  ;; depth a query needs is a property of the data, so the *caller* chooses.  For a sweep
  ;; the caller is the suite, and 8 is what the fixtures' derivations reach.
  (alter-var-root (requiring-resolve 'vaelii.impl.inference/*max-depth*) (constantly 8)))

;; `VAELII_QUERY_STRATEGY=breadth-first` runs the whole suite under one of the node
;; engine's tacticians (`vaelii.impl.tactics`).  Ordering is a cost decision and never a
;; semantic one, so every tactician must be failing-set-identical with every other — and
;; the suite is a far larger completeness sweep than any test written for the purpose.
;; Only meaningful beside `VAELII_QUERY_ENGINE=inference`; the DFS has one order and ignores
;; it.
(defn query-strategy-override
  "The tactician `VAELII_QUERY_STRATEGY` names, or nil.

  The domain is `tactics/tacticians` itself and not a copy of its keys, so a tactician
  added there is spellable here the same day and one removed stops being accepted
  without a second edit.  A misspelt tactician is refused for the reason a misspelt
  engine is: every one of them is complete, so the wrong name is a sweep that runs the
  default order and passes, saying nothing about the tactician it named."
  []
  (let [roster    @(requiring-resolve 'vaelii.impl.tactics/tacticians)
        spellings (into {} (map (juxt name identity)) (keys roster))]
    (config/prop-enum "VAELII_QUERY_STRATEGY" spellings nil
                      (str "one of " (str/join ", " (sort (keys spellings)))))))

(when-let [s (query-strategy-override)]
  (alter-var-root #'v/*query-options* (constantly s)))

;; The set-algebra retrieval (`res/matches-hierarchical`) is the default; set
;; `VAELII_HIER=0` to route every context-scoped match through the reference nested
;; fan-out instead, so the whole suite can be run against the fallback path.  Spelled
;; positively, so the value says what it selects: a switch whose name carries the
;; negation reads `=0` as *on*, which is the one thing a reader must not have to work
;; out at a glance.
(when-not (config/prop-bool "VAELII_HIER" true)
  (alter-var-root (requiring-resolve 'vaelii.impl.resolution/*hierarchical-retrieval*)
                  (constantly false)))

;; `VAELII_PLAN=0` runs a conjunction's generators in the order they were written — the
;; cost ranking off, the readiness discipline still on — which is the ranking's own claim
;; put to the whole suite: ranking is a cost decision and must never change the answer
;; *set* (`vaelii.impl.plan/*enabled*`).  `plan_test` makes that claim over every
;; permutation of one conjunction; this makes it over every conjunction the suite runs,
;; the same shape `VAELII_HIER` takes for retrieval.
;;
;; **The claim does not hold unqualified, and the sweep is what established that.**  Six
;; tests pin the ranking back rather than stand aside, because in each the ranking is
;; what supplies an answer: a registered evaluatable's placement, where the event
;; calculus stops, and — the one that is not about a single query — the completeness of
;; incremental forward chaining over a prover extent that grows.  docs/inference.md,
;; "Where the ranking is required", carries all three with their witnesses.
;;
;; Spelled positively for `VAELII_HIER`'s reason — the value says what it selects.
(when-not (config/prop-bool "VAELII_PLAN" true)
  (alter-var-root (requiring-resolve 'vaelii.impl.plan/*enabled*) (constantly false)))

;; ---- KBs on the scratch databases ---------------------------------------
;;
;; The suite owns a **block of two** db numbers, named by its top:
;;
;;   scratch   top     the shared db nearly every test runs on
;;   isolated  top-1   for a test that rebuilds a KB in a loop and so would
;;                     clear the scratch db out from under a `:once` fixture
;;
;; The number keys the store: the in-memory backend keys its process-global
;; registry by db number (so a KB rebuilt over the same number sees the same
;; records — the restart the recovery tests rely on), and the disk backend derives
;; its directory from it.  `VAELII_TEST_SPACE` moves the block, so two disk runs
;; can use distinct directories at once.

(def ^:private block-top
  (if-let [s (System/getenv "VAELII_TEST_SPACE")]
    (let [n (try (Long/parseLong (str/trim s))
                 (catch NumberFormatException _
                   (throw (ex-info (str "VAELII_TEST_SPACE must be a space number, got " (pr-str s))
                                   {:value s}))))]
      ;; the block is [n-1, n], and 0 is the default KB's db number
      (when-not (<= 5 n 15)
        (throw (ex-info (str "VAELII_TEST_SPACE must be between 5 and 15 — it names the top of a "
                             "two-database block, and the block must clear db number 0 "
                             "(the default KB).  Got " n ".")
                        {:value n})))
      n)
    15))

;; The storage the whole suite runs on.  `:memory` (default) keeps everything in RAM
;; with no external dependency; `VAELII_TEST_BACKEND=disk-log` runs every test against the
;; on-disk stores (the durability parity gate).  Either way the db number names a shared
;; store, so the block/isolated split and `fresh`'s clear behave identically.
;;
;; The value is a `:backend` name, `<records>-<index>` (`disk-memory`, `memory-columnar`)
;; — every legal record×index pair has one, so the env var needs no second spelling.
;; `scripts/test-backends.sh` runs every one of them.
;;
;; `overlay` is the odd one: it names a *decorator* rather than a store, so the opts it
;; expands to are built per space by `space-opts` below.
(def ^:private storage
  (if-let [b (some-> (System/getenv "VAELII_TEST_BACKEND") str/trim str/lower-case not-empty)]
    {:backend (keyword b)}
    {:backend :memory}))

;; The truth-maintenance representation the whole suite runs on — `:dense` (default, the
;; engine default since the corpus-scale memory win) or `VAELII_TEST_TMS=reference` for
;; the persistent-map baseline.  Same gate as the storage backend:
;; `jtms_dense_oracle_test` proves the two agree op-by-op, and running the suite through
;; the reference one proves the *engine* agrees on the baseline the default replaced.
(def ^:private tms-kind
  (if-let [t (System/getenv "VAELII_TEST_TMS")]
    (keyword (str/lower-case (str/trim t)))
    :dense))

;; :recover? false — a test KB is built over databases the *previous* test run may
;; have left populated, and `fresh` clears right after construction, so the
;; unrecovered-store warning would be noise on nearly every build.

(defn- space-opts
  "The KB opts for one of the suite's spaces, on whatever storage the run selected.
  `overlay` is spelled out here rather than in `storage`, because a fork is a decorator
  over *two* stores: the suite's own space becomes the writable overlay, and the base is an
  empty space beside it — which is exactly the gate, a fork over nothing behaving as the
  thing it forked."
  [s]
  (let [common {:recover? false :tms tms-kind}]
    (if (= :overlay (:backend storage))
      (merge common {:backend :overlay
                     :base    {:backend :memory :space [::base s]}
                     :overlay {:backend :memory :space s}})
      (merge {:space s} common storage))))

(def scratch-space  (space-opts block-top))
(def isolated-space (space-opts (- block-top 1)))

(def plain-memory-space
  "A plain in-RAM KB beside `*kb*`, whatever storage the run selected — for a test
  that needs a second, backend-independent KB (an export parity source, a round-trip
  target).  Its own derived space, so it shares a store with nothing: not the process
  default, and not the fork's writable half under the overlay run.  `(assoc
  scratch-space :backend :memory)` is not this: under the overlay run that spelling
  drags the template's `:base`/`:overlay` halves along — a contradiction `open-kb`
  refuses — and, carrying no top-level space, would land on the process default."
  {:backend :memory
   :space [::plain block-top]
   :recover? false :tms tms-kind})

;; ---- live model calls -----------------------------------------------------

(defn live-llm?
  "May this run talk to a real model?  **No, unless asked in so many words.**

  `lein test` makes no LLM call: a reachable Ollama on the machine is not consent, a
  credential in the environment is not consent, and a suite whose answers depend on
  what a model happened to say is neither hermetic nor reproducible.  Everything the
  pipeline does is tested against the offline stub.  Set `VAELII_LLM_LIVE=1` to opt
  into the live tier."
  []
  (contains? #{"1" "true" "yes"}
             (some-> (System/getenv "VAELII_LLM_LIVE") str/trim str/lower-case)))

(defn live-model
  "The model a live test runs against, or **nil with a printed reason** — the one helper
  every `^:llm` test opens with, so the three ways such a test cannot run are answered in
  one place and in one order.

  Opting in is checked **first**, before the host is so much as probed: a reachable Ollama
  is not consent.  Then reachability, then whether the host has actually pulled the model
  — a host that is up but has never seen the model fails in a way that is indistinguishable from a bug in
  the code under test.

  `what` names the tier in the skip line.  `opts`: `:model` (default
  `ollama/configured-model`) and `:env`, the variable that names it — omitted for a model
  a test pins, where there is no variable to point anybody at.

  One helper rather than a copy per file so that the consent path is one path: the source
  scan in `vaelii.llm-test` follows a test's calls to `live-llm?` to prove it asked, and a
  helper hoisted here is followed the same as one defined beside the test."
  ([what] (live-model what {}))
  ([what {:keys [model env] :or {env "VAELII_OLLAMA_MODEL"}}]
   (let [model (or model (ollama/configured-model))]
     (cond
       (not (live-llm?))
       (do (println (str "  [skip] " what ": set VAELII_LLM_LIVE=1 to opt in")) nil)

       (not (ollama/available? {:timeout-ms 2000}))
       (do (println (str "  [skip] " what ": no server at " (ollama/base-url)
                         " — set VAELII_OLLAMA_HOST to point at one"))
           nil)

       (nil? (ollama/capabilities model))
       (do (println (str "  [skip] " what ": " (ollama/base-url) " has no model " model
                         (when env (str " — set " env))))
           nil)

       :else model))))

(defn test-kb
  "A KB on the shared scratch space."
  []
  (v/open-kb scratch-space))

(defn isolated-test-kb
  "A KB on the isolated space, for a test that rebuilds a KB in a loop: `fresh`
  clears the scratch space every call, which would wipe a KB another namespace is
  holding open through a `:once` fixture.  Such tests pass alone and fail together
  — the worst way to find out."
  []
  (v/open-kb isolated-space))

;; ---- the supporter-visibility audit -----------------------------------------
;;
;; `VAELII_AUDIT_SUPPORT=<dir>` makes teardown write every stored justification whose
;; conclusion's context does not see the context of one of its supporters — an antecedent,
;; or the rule a firing names as its informant.  One EDN map per line, into a file per JVM
;; (`<dir>/<pid>.edn`), so parallel shards never interleave a line.  Unset, teardown reads
;; the environment once at load and does nothing else.

(def ^:private support-audit-dir (System/getenv "VAELII_AUDIT_SUPPORT"))

(defn- unseen-supporters
  "The supporters of justification `j` whose context `j`'s conclusion's context does not
  see, as `[{:sentence :context :rule?}]`.  A sentex with no context is seen from every
  context, so it is never one of them."
  [kb j]
  (let [recs (:records kb)
        cctx (:context (p/get-sentex recs (:consequence j)))
        inf  (:informant j)]
    (when cctx
      (into []
            (keep (fn [[h rule?]]
                    (when-let [s (p/get-sentex recs h)]
                      (when (and (:context s) (not (v/sees? kb cctx (:context s))))
                        {:sentence (:sentence s) :context (:context s) :rule? rule?}))))
            (cond-> (mapv #(vector % false) (:antecedents j))
              (integer? inf) (conj [inf true]))))))

(def ^:private ^java.util.Map support-audited
  "The justification ids already audited, per live KB.  Weak on the KB, so a KB a test
  drops takes its entry with it; a KB outlives the tests it serves, so its baseline is
  read once rather than once per test."
  (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

(defn audit-support!
  "Write every justification stored in `kb` and not yet audited for it that rests on a
  supporter its conclusion's context does not see, when `VAELII_AUDIT_SUPPORT` names a
  directory.  Called on a live KB only, before teardown retracts or clears, so the
  records and the taxonomy the visibility is read from describe one state.  Never throws:
  a failure is written as an `:audit-error` line, so the audit cannot change a test's
  outcome."
  [kb]
  (when support-audit-dir
    (let [out  (File. ^String support-audit-dir
                      (str (.pid (java.lang.ProcessHandle/current)) ".edn"))
          test (some-> clojure.test/*testing-vars* first symbol)
          recs (:records kb)
          seen (or (.get support-audited kb) #{})
          jids (remove seen (p/justification-ids recs))]
      (.put support-audited kb (into seen jids))
      (try
        (doseq [jid jids
                :let [j (p/get-justification recs jid)]
                :when j
                :let [unseen (unseen-supporters kb j)]
                :when (seq unseen)
                :let [c (p/get-sentex recs (:consequence j))]]
          (spit out
                (str (pr-str {:test       test
                              :informant  (let [inf (:informant j)]
                                            (if (integer? inf)
                                              (let [r (p/get-sentex recs inf)]
                                                (or (:sentence r)
                                                    (list 'implies (:antecedent r) (:consequent r))))
                                              inf))
                              :conclusion {:sentence (:sentence c) :context (:context c)}
                              :believed?  (boolean (v/in? kb (:consequence j)))
                              :unseen     unseen})
                     "\n")
                :append true))
        (catch Throwable e
          (spit out (str (pr-str {:test test :audit-error (str e)}) "\n") :append true))))))

(defn clear-kb!
  "Wipe the stores under a KB the fixtures hand back over and over.  `v/clear!` without
  the durability daemon's flush, plus the one piece of in-memory state a wipe must take
  with it: the refusal record is keyed by rule handle and retired when the rule departs,
  so nothing else drops the entries of rules this call just deleted."
  [kb]
  (p/clear-records! (:records kb))
  (p/clear-index!   (:index kb))
  ;; the same release `v/clear!` makes, and for its reason: a write hazard is a claim
  ;; about the records that were here, and a wipe is the one moment that knows there are
  ;; none.  `kb/write-hazards` reads emptiness without retiring anything — an importer
  ;; declares its hazard while the store is still empty — so a fixture that wipes and
  ;; hands the KB back has to say so, or the next test's own asserts are refused against
  ;; a hazard declared for records it did not write.
  (kb/note-hazards! kb {:no-belief false :no-index false})
  (some-> (reasoning/refused kb) (reset! {})))

(defn fresh
  "An empty, cleared KB on the shared scratch space."
  [] (doto (test-kb) (clear-kb!)))

;; ---- the starter ontology, built once and copied ------------------------

(def starter-build-space
  "The space the starter dump is built on: a plain in-RAM KB of its own, never the
  shared scratch one.  A `:once` fixture in another namespace holds a KB open on
  `scratch-space` for the length of that namespace and `fresh` wipes what it finds, so
  building here would wipe it.  Plain memory whatever storage the run selected, for
  `plain-memory-space`'s reason and because a dump is backend-portable — what is
  exported is the record store, and every backend holds the same records."
  {:backend :memory
   :space [::starter block-top]
   :recover? false :tms tms-kind})

(defn- temp-dump-dir
  "A new, empty directory under `java.io.tmpdir` whose name starts with `prefix`.
  `Files/createTempDirectory` creates it atomically under a name no existing entry has,
  so two test JVMs building a dump at the same moment get two directories."
  ^File [prefix]
  (.toFile (Files/createTempDirectory prefix (make-array FileAttribute 0))))

(defn- build-dump
  "Build a KB on `space` with `load`, export it into a new directory named from `prefix`,
  and answer that directory's path.

  The export is the `:records+index` variant with its reasoning image, so `import!`
  restores the records, the justifications and the premise marks, replays the index
  entries and installs the image.  The entries and the image are each a cache checked
  against the records they land beside — the index rebuilt, belief recovered, when they
  do not describe them — so an import produces what `load` produces.  Replaying the index
  rather than rebuilding it takes a warm starter import from 135 ms to 94 ms, and a CxCore
  one from 57 ms to 44 ms.

  The space is cleared first, for `fresh`'s reason: it is opened `:recover? false` over
  databases a previous run may have populated, and a write into a KB whose belief was
  never built is refused (`:type :unrecovered-kb`).  The directory is deleted on JVM exit,
  deepest entry first, since `deleteOnExit` runs its queue in reverse insertion order and
  will not remove a directory holding files."
  [prefix space load]
  (let [dir (temp-dump-dir prefix)
        kb  (doto (v/open-kb space) (clear-kb!))]
    (load kb)
    (v/export! kb (.getPath dir) {:variant :records+index})
    (clear-kb! kb)
    (.deleteOnExit dir)
    (run! #(.deleteOnExit ^File %) (file-seq dir))
    (.getPath dir)))

(def ^:private starter-dump
  "An export dump of the starter ontology, built **once per JVM** and read back by
  `load-starter!`.

  `starter/load-into` re-asserts all 3,200+ sentexes through the full write path, and
  that path is not linear in the ontology's size.  64% of the load is its 28 `genlCx`
  edges: each one sweeps the facts its widened ancestor set newly exposes and re-derives
  the functional equalities over them (`special/equate-under-context-edge`), which for
  one edge over the loaded starter is 145 ms and ~5,100 index queries.  Measured on this
  tree: `load-into` 2,980 ms, `export!` 181 ms, `import!` 94 ms warm.

  A dump is a copy of the KB rather than a shortcut past building one (`build-dump`).
  `starter_copy_test` pins that — same sentences, same contexts, same truth, same
  strength, same belief."
  (delay (build-dump "vaelii-starter-" starter-build-space starter/load-into)))

(defn load-starter!
  "Load the starter ontology into `kb` and return `kb` — `starter/load-into`'s result,
  restored from the dump `starter-dump` builds once per JVM rather than re-asserted.

  A `:once` fixture calls this:

    (use-fixtures :once (tu/loaded tu/load-starter!))

  A test *about the load path itself* — what `load-into` asserts, in what order, or what
  it refuses — calls `starter/load-into` directly and pays for it, since a restored dump
  answers a different question."
  [kb]
  (v/import! kb @starter-dump {:belief? true})
  kb)

;; ---- CxCore, built once and copied --------------------------------------

(def core-build-space
  "The space the CxCore dump is built on, `starter-build-space`'s counterpart: a plain
  in-RAM KB of its own, never the shared scratch one, for the same reason — a `:once`
  fixture in another namespace holds `scratch-space` open and `fresh` wipes what it
  finds, so building here would wipe it.  Plain memory whatever storage the run selected,
  since a dump is backend-portable."
  {:backend :memory
   :space [::core block-top]
   :recover? false :tms tms-kind})

(def ^:private core-context-dump
  "An export dump of the CxCore vocabulary context, built **once per JVM** and read back
  by `load-core!`, mirroring `starter-dump`.

  `core-context/load-into` re-asserts the whole `CxCore.txt` through the full write path,
  and the `neutral-fresh` fixtures rebuild a fresh core KB per test, so that cost is paid
  once for every such test.  A restored dump reaches the same state (`build-dump`) —
  `core_copy_test` pins that, the genlCx edge `load-into` wires first included, because
  belief does not depend on the order the records were written."
  (delay (build-dump "vaelii-core-" core-build-space core-context/load-into)))

(defn load-core!
  "Load the CxCore vocabulary into `kb` and return `kb` — `core-context/load-into`'s
  result, restored from the dump `core-context-dump` builds once per JVM rather than
  re-asserted, as `load-starter!` does for the starter.

  A test *about the load path itself* — what `load-into` asserts, in what order, or the
  `(genlCx CxUniverse CxCore)` edge it wires first — calls `core-context/load-into`
  directly and pays for it, since a restored dump answers a different question."
  [kb]
  (v/import! kb @core-context-dump {:belief? true})
  kb)

;; ---- any fixture KB, built once per key and copied ---------------------

(def ^:private keyed-dumps
  "`load-dumped!`'s dumps, one delay per key, each built on its own space the first time
  a fixture asks for it."
  (atom {}))

(defn load-dumped!
  "Load into `kb` the KB `build` makes of an empty one, and return `kb` — restored from a
  dump built once per JVM for `key` rather than rebuilt, as `load-core!` does for CxCore.

    (defn- channel-kb []
      (tu/load-dumped! (tu/fresh) ::channel-kb
                       #(doto % (core-context/load-into) (sa/load-speech-acts))))

  `key` names what `build` makes, so two fixtures building different KBs must pass two
  keys; a namespaced keyword keeps them apart.  `build` may only assert: a dump carries
  the records, the index and belief, and nothing else the KB holds.  A prover is added
  after the restore, since provers are not KB content."
  [kb key build]
  (let [space {:backend :memory :space [::dump key block-top]
               :recover? false :tms tms-kind}
        dump  (get (swap! keyed-dumps update key
                          #(or % (delay (build-dump "vaelii-fixture-" space build))))
                   key)]
    (v/import! kb @dump {:belief? true})
    kb))

(defn load-core-with!
  "Load CxCore and then the theory files `theories` names into `kb`, and return `kb` —
  `core-context/load-into` followed by `seed/load-context` over each `[context dir]`
  pair in order, restored through `load-dumped!`, one dump per distinct `theories`.

    (use-fixtures :each (tu/neutral-fresh
                         #(doto (tu/fresh)
                            (tu/load-core-with! '[[CxSpace \"upper\"] [CxTime \"upper\"]])
                            (v/add-prover (space/spatial-prover)))))

  A per-test fixture asserting CxCore and two `kb/upper` files cost 600-1,200 ms a test;
  the restore costs what `load-core!`'s does, plus the theories' records.  A test about
  loading a theory file calls `seed/load-context` directly."
  [kb theories]
  (let [theories (vec theories)]
    (load-dumped! kb [::theories theories]
                  (fn [kb]
                    (core-context/load-into kb)
                    (doseq [[context dir] theories] (seed/load-context kb context dir))))))

(defn isolated-fresh
  "An empty, cleared KB on the isolated space.  See `isolated-test-kb`."
  [] (doto (isolated-test-kb) (clear-kb!)))

;; ---- gensym'd temporary terms (naming-invariant by construction) --------
;; predicate  bare lowercase, uncommitted in arity -> tmppred1
;; individual CapitalCamelCase                -> Tmp2
;; type       lowercase, snake_case only when the base is  -> tmpdog3 / tmp_t3
;; context    CapitalCamelCase, Cx prefix    -> CxTmp4

(defn- alnum "Letters and digits only — individuals and predicates admit no underscore."
  [s] (str/replace (str s) #"[^A-Za-z0-9]" ""))

(defn- snake "Lowercase, non-alphanumerics folded to _ — the form a type must have."
  [s] (str/lower-case (str/replace (str s) #"[^A-Za-z0-9]+" "_")))

(defn- cap [s] (if (seq s) (str (str/upper-case (subs s 0 1)) (subs s 1)) s))

(defn neighbours-built
  "Neighbour sets the transitive-closure walk **built** while `f` ran — the miss half of
  `observe/note-neighbours!`, one store retrieval each.  Answers the count; `f`'s own
  value is the caller's to capture.

  The engine counts these, so a test asking whether a walk happened reads a number rather
  than redefining `res/matches-visible` to tally calls.  That interception could not tell a
  walk's probe from a `FactProver` lookup of the same predicate except by the `?rv` the
  walk's patterns happen to carry, and it pinned the arity of a function whose shape is
  none of the asking test's business."
  [f]
  (let [before (:misses (observe/neighbour-counts))]
    (f)
    (- (:misses (observe/neighbour-counts)) before)))

(defn sole-answer
  "The one binding map `answers` holds, plus the assertion that there is exactly one.

  `ask`, `query` and `prove` promise a **set** of answers and no order, so
  `(first (v/ask …))` reads whichever answer the reader happened to produce first.  That
  is a claim about the KB when the set is a singleton and a claim about the executor's
  ordering when it is not, the two are indistinguishable at the call site, and the second
  passes right up until a tactician reorders it or the fixture grows a second witness.
  `VAELII_QUERY_STRATEGY` exists to reorder exactly this, and order independence is one
  of the four properties the engine holds everywhere — so a test that quietly depends on
  an order is worth failing where it is written rather than under a sweep.

  `what` names the goal for the failure message.  The first answer comes back whatever
  the count, so a fixture that grew a second one fails on this line rather than on a
  `nil` three lines further down."
  ([answers] (sole-answer answers nil))
  ([answers what]
   (let [as (vec answers)]
     (is (= 1 (count as))
         (str "expected exactly one answer"
              (when what (str " for " (pr-str what)))
              ", got " (count as) " — `first` on this would be an assertion about the "
              "reader's order: " (pr-str as)))
     (first as))))

(defn fresh-term
  "A gensym'd temporary term of `role`, naming it after `base` so a failure reads
  `tmpdog17` / `TmpMuffet17` rather than an anonymous `tmp_t17`.  The generated name
  satisfies the naming invariant for its role by construction.

  A `:type` temp keeps the **base's own spelling**: a base already carrying an
  underscore (`physical_object`) becomes snake_case, a bare lowercase word (`dog`)
  becomes another bare lowercase word.  That distinction is required.  A
  snake_case functor names a type and is therefore legal only as a *unary* predicate
  (`vaelii.impl.naming/problems`), so spelling every type temp with underscores would
  commit it to arity 1 — a commitment a test writing `dog` or `likes` never made,
  since a bare lowercase word satisfies the predicate *and* the type convention and is
  disambiguated by arity rather than by the symbol.  Left bare, the temp is usable
  either way; writing the base with an underscore is how a test says \"a type, and
  only a type\".

  A `:predicate` temp is **bare lowercase** for the same reason read the other way.
  The naming rule is a biconditional now — snake_case is arity 1 and camelCase is arity
  2 and above — so a camelCase temp would commit to being a relation exactly as an
  underscored one commits to being a kind, and a test that wrote `wabPremise` as a base
  made neither commitment.  The base's own capitals are folded out (`wabPremise` ⇒
  `tmpwabpremise17`), which is the one spelling both conventions admit; a test that
  wants the commitment writes the base with an underscore and takes a `:type` temp."
  [role base]
  (case role
    :type       (let [n (snake base)]
                  (if (str/includes? n "_")
                    (gensym (str "tmp_" n "_"))
                    (gensym (str "tmp" n))))
    :predicate  (gensym (str "tmp" (str/lower-case (alnum base))))
    :individual (gensym (str "Tmp" (cap (alnum base))))
    :context    (symbol (str "Cx" (gensym (str "Tmp" (cap (alnum (str/replace (str base) #"^Cx" "")))))))))

(defn term-role
  "The role a symbol *looks* like, by the KB's own naming invariants — so a test
  writes the term the way the ontology would, and gets a matching temporary."
  [sym]
  (let [n (name sym)]
    (cond
      (re-matches #"Cx[A-Z][A-Za-z0-9]*" n)      :context
      (re-matches #"[A-Z][A-Za-z0-9]*" n)        :individual
      (re-matches #"[a-z][a-z0-9_]*" n)          :type        ; all-lowercase => a type
      (re-matches #"[a-z][a-zA-Z0-9]*" n)        :predicate   ; camelCase => a predicate
      :else (throw (ex-info (str "no naming role for " sym) {:symbol sym})))))

(defmacro with-terms
  "Bind each symbol to a gensym'd temporary term, hiding the gensym plumbing.  The
  *role* is inferred from the symbol's own shape, and the generated name embeds it:

    (with-terms [dog Muffet parentOf CxStory]
      (v/assert kb (list dog Muffet) CxStory))
    ;; dog -> tmpdog17   Muffet -> TmpMuffet18
    ;; parentOf -> tmpParentOf19   CxStory -> CxTmpStory20

  So the test is indistinguishable from the ontology it is about, while every term stays unique and
  disposable (see the net-neutrality guarantee above).  A bare base like `dog` stays
  bare (`tmpdog17`) so the temp is not committed to arity 1; see `fresh-term`."
  [syms & body]
  (assert (and (vector? syms) (every? simple-symbol? syms))
          "with-terms takes a vector of plain symbols")
  `(let [~@(mapcat (fn [s] [s `(fresh-term ~(term-role s) '~s)]) syms)]
     ~@body))

;; the anonymous forms, kept for callers that don't care about the name
(defn tmp-ind  ([] (gensym "Tmp"))            ([base] (fresh-term :individual base)))
(defn tmp-pred ([] (gensym "tmppred"))        ([base] (fresh-term :predicate  base)))
(defn tmp-type ([] (gensym "tmp_t"))          ([base] (fresh-term :type       base)))
(defn tmp-ctx  ([] (symbol (str "Cx" (gensym "Tmp"))))
  ([base] (fresh-term :context base)))

;; ---- query helpers -------------------------------------------------------

(defn first-if-singleton
  "Returns the first element if `coll` has exactly one item, otherwise nil.
  Useful when a query must return *the* match, and zero or multiple is an error."
  [coll]
  (let [s (seq coll)]
    (when (and s (nil? (next s)))
      (first s))))

(defn sentex-matching
  "Returns the unique sentex matching `sentence` in `context`, or nil.
  Nil when zero or more than one match — ambiguity is not a match."
  [kb sentence context]
  (first-if-singleton (v/sentexes-matching kb sentence context)))

;; ---- content snapshots + auto-teardown ----------------------------------

(defn sentex-ids    [kb] (set (p/sentex-ids    (:records kb))))
(defn justification-ids [kb] (set (p/justification-ids (:records kb))))
(defn premise-ids   [kb] (set (p/premise-ids   (:records kb))))

(defn baseline
  "The three record sets teardown is judged against: what is stored, what justifies it,
  and which of it is *asserted* rather than derived.

  The third is the one a caller would not think to snapshot, and is the reason this is a
  map rather than three reads at each call site.  A premise mark is not visible in either
  of the other two — a test that asserts a sentence the baseline already holds as a
  derived conclusion adds no sentex and no justification, and leaves the handle marked a
  premise.  It then stands on its own for every test after it, believed with nothing
  supporting it, which is exactly the poisoning the neutrality contract exists to refuse."
  [kb]
  {:sentexes       (sentex-ids kb)
   :justifications (justification-ids kb)
   :premises       (premise-ids kb)})

(defn content-count [kb]
  {:sentexes   (count (p/sentex-ids    (:records kb)))
   :justifications (count (p/justification-ids (:records kb)))})

(defn- retract-added!
  "Retract every premise the test added since `before` (a set of sentex ids).
  Dependency-directed retraction sweeps the derived consequences, so the KB
  returns to its baseline.  Loops to a fixpoint in case teardown order matters."
  [kb before]
  (loop [guard 0]
    (let [prems (premise-ids kb)
          added (filter #(and (prems %) (not (contains? before %)))
                        (p/sentex-ids (:records kb)))]
      (when (and (seq added) (< guard 50))
        (doseq [h added] (try (v/retract! kb h) (catch Throwable _)))
        (recur (inc guard))))))

(defn stored-terms
  "Every symbol term the *records* mention — the term roster's oracle, computed the
  expensive way (a walk over every stored sentex)."
  [kb]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat (fn [sx] (conj (v/indexable-terms sx) (:context sx))))
              (filter symbol?))
        (p/sentex-ids (:records kb))))

(defn assert-neutral!
  "Retract the test's additions and assert the KB is restored to the `baseline` it was
  snapshotted at — **set equality on all three, so both directions are checked**.

  A leak is the obvious failure and the one retraction causes.  A *removal* is the one
  that hides: a test that retracts a sentex the baseline held leaves the shared `:once`
  KB short for every test after it in the namespace, and a difference computed only as
  `now - before` is empty in exactly that case.  So the message names which direction
  broke, since the two are repaired at opposite ends.

  The premise set is reported on its own line because it moves for its own reasons and
  is repaired at its own end.  A premise mark on a *baseline* handle is put there by an
  `assert` of a sentence the KB already derived and taken off by a `retract!` of one it
  had asserted, and neither of those moves a record count — so this is the only check
  that sees either."
  [kb before]
  (audit-support! kb)
  (retract-added! kb (:sentexes before))
  (let [{before-sx :sentexes before-dd :justifications before-pm :premises} before
        now-sx  (sentex-ids kb)
        now-dd  (justification-ids kb)
        leak-sx (set/difference now-sx before-sx)
        leak-dd (set/difference now-dd before-dd)
        lost-sx (set/difference before-sx now-sx)
        lost-dd (set/difference before-dd now-dd)]
    (is (and (= before-sx now-sx) (= before-dd now-dd))
        (str "KB not restored after teardown — leaked "
             (count leak-sx) " sentex(es), " (count leak-dd) " justification(s) "
             (pr-str (mapv #(v/sentence-of (v/sentex kb %)) (take 8 leak-sx)))
             "; lost " (count lost-sx) " sentex(es), " (count lost-dd) " justification(s) "
             ;; a lost sentex has no record left to print, so the handles are the report
             (pr-str (vec (take 8 lost-sx)))))
    ;; Premise identity, over the handles that survived: a premise on a sentex the
    ;; retraction already swept is the leak above and not a second one, and reporting it
    ;; twice would send the reader after two bugs.
    (let [now-pm  (premise-ids kb)
          leak-pm (set/intersection (set/difference now-pm before-pm) now-sx)
          lost-pm (set/intersection (set/difference before-pm now-pm) now-sx)]
      (is (empty? (set/union leak-pm lost-pm))
          (str "premise marks not restored after teardown — " (count leak-pm)
               " baseline sentex(es) left asserted "
               (pr-str (mapv #(v/sentence-of (v/sentex kb %)) (take 8 leak-pm)))
               ", " (count lost-pm) " left derived that were asserted "
               (pr-str (mapv #(v/sentence-of (v/sentex kb %)) (take 8 lost-pm)))))))
  ;; the index's term roster is an absolute invariant, not a delta: it must equal the
  ;; names the surviving records mention.  A term left behind by an incomplete unindex
  ;; shows up here even when the record sets balance.
  (let [stored (stored-terms kb)
        listed (set (v/terms kb))]
    (is (= stored listed)
        (str "term roster drifted from the records — "
             (count (set/difference listed stored)) " stale, "
             (count (set/difference stored listed)) " missing: "
             (pr-str (vec (take 8 (set/union (set/difference listed stored)
                                             (set/difference stored listed)))))))))

;; ---- fixtures -----------------------------------------------------------

(def ^:dynamic *kb*
  "The KB under test, bound by the fixtures below.  Tests reach it through
  `with-kb` / `deftest-kb` rather than touching the var, so a test namespace needs
  no `*kb*` of its own."
  nil)

(defmacro with-kb
  "Bind `sym` to the KB under test:

    (with-kb [kb] (v/assert kb …))

  **The binding vector takes the symbol and nothing else**, and an init form is refused
  at macroexpansion rather than ignored.  The form that resembles a `let` and is not one
  is `(with-kb [k (fresh)] …)`: it binds the fixture's KB, and whatever the init says it
  never runs — so a helper called twice in one test runs its second arm over everything
  the first left, and a test comparing two arrangements compares the second against the
  first instead of against the same baseline.  Nothing in the reading says so, which is
  why this refuses the spelling instead of quietly honouring half of it.

  Evaluating the init is not the fix, which matters so nobody re-derives it: a
  `fresh` **mid-test** clears the store the `:each` fixture recorded its baseline against,
  and the net-neutrality check then reports a leak for content the clear removed.  A test
  wanting a genuinely separate KB gives each arm its own gensym'd terms (`with-terms`
  inside the arm), or builds over a cleared store with `with-cleared-kb`."
  [binding & body]
  (when-not (and (vector? binding) (= 1 (count binding)))
    (throw (ex-info (str "with-kb takes a one-symbol binding vector [sym], got "
                         (pr-str binding)
                         " — an init form here would never be evaluated; give each arm its"
                         " own with-terms, or use with-cleared-kb")
                    {:type :bad-binding :binding binding})))
  `(let [~(first binding) *kb*] ~@body))

(defmacro deftest-kb
  "A `deftest` whose body has **`kb`** already bound to the KB under test — the
  fixture plumbing stays out of the test:

    (deftest-kb a-dog-is-an-animal
      (with-terms [dog Muffet]
        (v/assert kb (list dog Muffet) 'CxUniverse)))"
  [name & body]
  `(clojure.test/deftest ~name (let [~'kb *kb*] ~@body)))

(defn loaded
  "A `:once` fixture: build a fresh KB, run `load-fn` on it, bind it for the whole
  namespace, and clear at the end.  Pair with `neutral`."
  [load-fn]
  (fn [f]
    (let [kb (fresh)]
      (load-fn kb)
      ;; `finally`, like every sibling fixture: an Error escaping the namespace's
      ;; tests would otherwise leave the shared scratch space populated for whatever
      ;; namespace runs next
      (try (binding [*kb* kb] (f))
           (finally (clear-kb! kb))))))

(defn neutral
  "An `:each` fixture guarding net-neutrality of the KB bound by a `:once` fixture.
  Snapshots content, runs the test, retracts the additions, and asserts the KB is
  back to baseline."
  []
  (fn [f]
    (let [kb *kb*
          before (baseline kb)]
      (try (f)
           (finally (assert-neutral! kb before))))))

(defn neutral-fresh
  "An `:each` fixture that builds a KB with `build-fn` (e.g. `tu/fresh`, or
  `#(doto (tu/fresh) (tu/load-core!))` for one needing CxCore's vocabulary), binds it, and
  guards net-neutrality per test.  A test *about* the CxCore load path builds with
  `#(doto (tu/fresh) (core-context/load-into))` instead, paying the load rather than
  restoring the dump."
  [build-fn]
  (fn [f]
    (let [kb (build-fn)]
      (binding [*kb* kb]
        (let [before (baseline kb)]
          (try (f)
               (finally (assert-neutral! kb before))))))))

(defn neutral-kb*
  "Functional core of `with-neutral-kb`."
  [build-fn body]
  (let [kb     (build-fn)
        before (baseline kb)]
    (try (body kb)
         (finally (assert-neutral! kb before)))))

(defmacro with-neutral-kb
  "For a deftest that builds its own KB inline (a namespace whose tests need
  different baselines): build with `build-fn`, bind it to `sym`, run the body, then
  retract the additions and assert net-neutrality.

    (with-neutral-kb [kb tu/fresh] (v/assert kb …))"
  [[sym build-fn] & body]
  `(neutral-kb* ~build-fn (fn [~sym] ~@body)))

(defn cleared-kb*
  "Functional core of `with-cleared-kb`."
  [build-fn body]
  (let [kb (build-fn)]
    (try (body kb)
         (finally
           (audit-support! kb)
           (clear-kb! kb)
           (is (= {:sentexes 0 :justifications 0} (content-count kb))
               "durable store not empty after clear teardown")))))

(defmacro with-cleared-kb
  "For a persistence test that intentionally mutates the durable store across a
  restart (a second KB over the same scratch dbs): build, run the body, then FLUSH
  and assert the store is empty.  Flushing is the honest teardown when the durable
  store itself is the subject under test.

    (with-cleared-kb [kb starter-kb] …)"
  [[sym build-fn] & body]
  `(cleared-kb* ~build-fn (fn [~sym] ~@body)))
