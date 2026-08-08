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
      then asserts the live sentex/justification sets are back to their baseline.  The
      assertion is a genuine invariant: it fails only when retraction leaves
      residue, i.e. a real teardown gap.

  Fixture recipes:

    ;; a shared KB loaded once (starter / CoreContext), neutral per test
    (use-fixtures :once (tu/loaded starter/load-into))
    (use-fixtures :each (tu/neutral))

    ;; a fresh KB rebuilt per test (empty or CoreContext-loaded), neutral per test
    (use-fixtures :each (tu/neutral-fresh tu/fresh))

    ;; an inline KB inside one deftest (varied baselines in one file)
    (tu/with-neutral-kb [kb tu/fresh] ...)"
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [is]]
            [vaelii.core :as v]
            [vaelii.impl.config :as config]
            [vaelii.impl.protocols :as p]))

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
;; with no external dependency; `VAELII_TEST_BACKEND=disk` runs every test against the
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

;; The truth-maintenance representation the whole suite runs on — `:reference`
;; (default) or `VAELII_TEST_TMS=dense` for `vaelii.impl.dense-jtms`.  Same gate as the
;; storage backend: `jtms_dense_oracle_test` proves the two agree op-by-op, and running
;; the suite through the dense one proves the *engine* agrees.
(def ^:private tms-kind
  (if-let [t (System/getenv "VAELII_TEST_TMS")]
    (keyword (str/lower-case (str/trim t)))
    :reference))

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

(defn clear-kb!
  "Wipe the stores under a KB the fixtures hand back over and over.  `v/clear!` without
  the durability daemon's flush, plus the one piece of in-memory state a wipe must take
  with it: the refusal record is keyed by rule handle and retired when the rule departs,
  so nothing else drops the entries of rules this call just deleted."
  [kb]
  (p/clear-records! (:records kb))
  (p/clear-index!   (:index kb))
  (some-> (:refused kb) (reset! {})))

(defn fresh
  "An empty, cleared KB on the shared scratch space."
  [] (doto (test-kb) (clear-kb!)))

(defn isolated-fresh
  "An empty, cleared KB on the isolated space.  See `isolated-test-kb`."
  [] (doto (isolated-test-kb) (clear-kb!)))

;; ---- gensym'd temporary terms (naming-invariant by construction) --------
;; predicate  camelCase, lowercase-initial   -> tmpP1
;; individual CapitalCamelCase                -> Tmp2
;; type       lowercase, snake_case only when the base is  -> tmpdog3 / tmp_t3
;; context    CapitalCamelCase ending Context -> Tmp4Context

(defn- alnum "Letters and digits only — individuals and predicates admit no underscore."
  [s] (str/replace (str s) #"[^A-Za-z0-9]" ""))

(defn- snake "Lowercase, non-alphanumerics folded to _ — the shape a type must have."
  [s] (str/lower-case (str/replace (str s) #"[^A-Za-z0-9]+" "_")))

(defn- cap [s] (if (seq s) (str (str/upper-case (subs s 0 1)) (subs s 1)) s))

(defn fresh-term
  "A gensym'd temporary term of `role`, naming it after `base` so a failure reads
  `tmpdog17` / `TmpMuffet17` rather than an anonymous `tmp_t17`.  The generated name
  satisfies the naming invariant for its role by construction.

  A `:type` temp keeps the **base's own spelling**: a base already carrying an
  underscore (`physical_object`) becomes snake_case, a bare lowercase word (`dog`)
  becomes another bare lowercase word.  That distinction is load-bearing.  A
  snake_case functor names a type and is therefore legal only as a *unary* predicate
  (`vaelii.impl.naming/problems`), so spelling every type temp with underscores would
  commit it to arity 1 — a commitment a test writing `dog` or `likes` never made,
  since a bare lowercase word satisfies the predicate *and* the type convention and is
  disambiguated by arity rather than by the symbol.  Left bare, the temp is usable
  either way; writing the base with an underscore is how a test says \"a type, and
  only a type\"."
  [role base]
  (case role
    :type       (let [n (snake base)]
                  (if (str/includes? n "_")
                    (gensym (str "tmp_" n "_"))
                    (gensym (str "tmp" n))))
    :predicate  (gensym (str "tmp" (cap (alnum base))))
    :individual (gensym (str "Tmp" (cap (alnum base))))
    :context    (symbol (str (gensym (str "Tmp" (cap (alnum (str/replace (str base) #"Context$" "")))))
                             "Context"))))

(defn term-role
  "The role a symbol *looks* like, by the KB's own naming invariants — so a test
  writes the term the way the ontology would, and gets a matching temporary."
  [sym]
  (let [n (name sym)]
    (cond
      (re-matches #"[A-Z][A-Za-z0-9]*Context" n) :context
      (re-matches #"[A-Z][A-Za-z0-9]*" n)        :individual
      (re-matches #"[a-z][a-z0-9_]*" n)          :type        ; all-lowercase => a type
      (re-matches #"[a-z][a-zA-Z0-9]*" n)        :predicate   ; camelCase => a predicate
      :else (throw (ex-info (str "no naming role for " sym) {:symbol sym})))))

(defmacro with-terms
  "Bind each symbol to a gensym'd temporary term, hiding the gensym plumbing.  The
  *role* is inferred from the symbol's own shape, and the generated name embeds it:

    (with-terms [dog Muffet parentOf StoryContext]
      (v/assert kb (list dog Muffet) StoryContext))
    ;; dog -> tmpdog17   Muffet -> TmpMuffet18
    ;; parentOf -> tmpParentOf19   StoryContext -> TmpStory20Context

  So the test reads like the ontology it is about, while every term stays unique and
  disposable (see the net-neutrality guarantee above).  A bare base like `dog` stays
  bare (`tmpdog17`) so the temp is not committed to arity 1; see `fresh-term`."
  [syms & body]
  (assert (and (vector? syms) (every? simple-symbol? syms))
          "with-terms takes a vector of plain symbols")
  `(let [~@(mapcat (fn [s] [s `(fresh-term ~(term-role s) '~s)]) syms)]
     ~@body))

;; the anonymous forms, kept for callers that don't care about the name
(defn tmp-ind  ([] (gensym "Tmp"))            ([base] (fresh-term :individual base)))
(defn tmp-pred ([] (gensym "tmpP"))           ([base] (fresh-term :predicate  base)))
(defn tmp-type ([] (gensym "tmp_t"))          ([base] (fresh-term :type       base)))
(defn tmp-ctx  ([] (symbol (str (gensym "Tmp") "Context")))
  ([base] (fresh-term :context base)))

;; ---- content snapshots + auto-teardown ----------------------------------

(defn sentex-ids    [kb] (set (p/sentex-ids    (:records kb))))
(defn justification-ids [kb] (set (p/justification-ids (:records kb))))
(defn premise-ids   [kb] (set (p/premise-ids   (:records kb))))

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
  "Retract the test's additions and assert the KB is restored to its baseline
  sentex/justification sets — **set equality, so both directions are checked**.

  A leak is the obvious failure and the one retraction causes.  A *removal* is the one
  that hides: a test that retracts a sentex the baseline held leaves the shared `:once`
  KB short for every test after it in the namespace, and a difference computed only as
  `now - before` is empty in exactly that case.  So the message names which direction
  broke, since the two are repaired at opposite ends."
  [kb before-sx before-dd]
  (retract-added! kb before-sx)
  (let [now-sx  (sentex-ids kb)
        now-dd  (justification-ids kb)
        leak-sx (set/difference now-sx before-sx)
        leak-dd (set/difference now-dd before-dd)
        lost-sx (set/difference before-sx now-sx)
        lost-dd (set/difference before-dd now-dd)]
    (is (and (= before-sx now-sx) (= before-dd now-dd))
        (str "KB not restored after teardown — leaked "
             (count leak-sx) " sentex(es), " (count leak-dd) " justification(s) "
             (pr-str (mapv #(:sentence (v/sentex kb %)) (take 8 leak-sx)))
             "; lost " (count lost-sx) " sentex(es), " (count lost-dd) " justification(s) "
             ;; a lost sentex has no record left to print, so the handles are the report
             (pr-str (vec (take 8 lost-sx))))))
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

    (with-kb [kb] (v/assert kb …))"
  [[sym] & body]
  `(let [~sym *kb*] ~@body))

(defmacro deftest-kb
  "A `deftest` whose body has **`kb`** already bound to the KB under test — the
  fixture plumbing stays out of the test:

    (deftest-kb a-dog-is-an-animal
      (with-terms [dog Muffet]
        (v/assert kb (list dog Muffet) 'UniverseContext)))"
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

(defn with-fresh
  "A `:once` fixture binding an empty cleared KB.  Pair with `neutral`."
  []
  (loaded (fn [_])))

(defn neutral
  "An `:each` fixture guarding net-neutrality of the KB bound by a `:once` fixture.
  Snapshots content, runs the test, retracts the additions, and asserts the KB is
  back to baseline."
  []
  (fn [f]
    (let [kb *kb*
          before-sx (sentex-ids kb)
          before-dd (justification-ids kb)]
      (try (f)
           (finally (assert-neutral! kb before-sx before-dd))))))

(defn neutral-fresh
  "An `:each` fixture that builds a KB with `build-fn` (e.g. `tu/fresh`, or
  `#(doto (tu/fresh) (core-context/load-into))`), binds it, and guards net-neutrality per
  test."
  [build-fn]
  (fn [f]
    (let [kb (build-fn)]
      (binding [*kb* kb]
        (let [before-sx (sentex-ids kb)
              before-dd (justification-ids kb)]
          (try (f)
               (finally (assert-neutral! kb before-sx before-dd))))))))

(defn neutral-kb*
  "Functional core of `with-neutral-kb`."
  [build-fn body]
  (let [kb (build-fn)
        before-sx (sentex-ids kb)
        before-dd (justification-ids kb)]
    (try (body kb)
         (finally (assert-neutral! kb before-sx before-dd)))))

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
