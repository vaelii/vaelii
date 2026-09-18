;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.test-util-test
  "The harness's own refusals — `vaelii.test-util` checked the way it checks the engine.

  A test utility that accepts a shape and quietly does something else with it is worse
  than one that throws, because what it breaks is the *evidence*: a test still runs, still
  passes, and no longer means what it says.  `with-kb` is the case that motivated this
  namespace — its binding vector is indistinguishable from a `let`'s and takes a symbol only, so an init
  form written there is refused at macroexpansion rather than dropped.

  **No fixture here.**  These tests are about the harness rather than about a
  KB, and one of them calls `fresh` in the middle of a test — which is precisely what the
  `:each` net-neutrality fixture exists to catch, since a clear removes the content that
  fixture recorded its baseline against.  Adding no KB is what leaves the space as it was
  found."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.test-util :as tu]))

(defn- refusal
  "The `ex-info` refusing `form`, or nil if it expanded.  `macroexpand-1` wraps a macro's
  own throw in a `CompilerException` (phase `:macro-syntax-check`), so the reading a test
  wants is one or more causes down — and discriminating on `:type` rather than on the
  message is the convention every `ex-info` in this project is written for."
  [form]
  (try (let [_ (macroexpand-1 form)] nil)
       (catch Throwable t
         (loop [e t]
           (cond (nil? e)                                   nil
                 (instance? clojure.lang.ExceptionInfo e)   e
                 :else                                      (recur (ex-cause e)))))))

(defn- recorded
  "The `clojure.test` reports `f` emits, captured instead of counted — so a test can
  assert that a harness helper FAILS without failing itself.  `with-redefs` on the
  multimethod is the documented way in: `do-report` is what `is` calls."
  [f]
  (let [out (atom [])]
    (with-redefs [clojure.test/do-report #(swap! out conj %)]
      (f))
    @out))

(deftest with-kb-takes-a-symbol-and-refuses-an-init-form
  (testing "the one-symbol form is what expands"
    (is (seq? (macroexpand-1 '(vaelii.test-util/with-kb [k] :body))))
    (is (nil? (refusal '(vaelii.test-util/with-kb [k] :body)))))
  (testing "an init form is refused rather than silently dropped"
    ;; The shape this exists for.  `(with-kb [k (fresh)] …)` gives the impression that it binds a
    ;; cleared KB and binds the fixture's instead — so a helper called twice in one test
    ;; runs its second arm over everything the first left, and a test comparing two
    ;; arrangements compares them against different baselines while still passing.
    (let [e (refusal '(vaelii.test-util/with-kb [k (vaelii.test-util/fresh)] :body))]
      (is (some? e) "an init form must not expand")
      (is (= :bad-binding (:type (ex-data e))))
      (is (re-find #"one-symbol binding vector" (ex-message e))
          "and the message says what to write instead")))
  (testing "and every other binding shape is refused too"
    (doseq [form ['(vaelii.test-util/with-kb [a b c] :body)
                  '(vaelii.test-util/with-kb [] :body)
                  '(vaelii.test-util/with-kb k :body)]]
      (is (= :bad-binding (:type (ex-data (refusal form))))
          (str "expected a refusal for " (pr-str form))))))

(deftest fresh-hands-back-a-cleared-kb
  ;; The other half of the same story: `fresh` really does clear, which is why calling it
  ;; mid-test is a live hazard rather than a no-op.  Tests needing a genuinely separate KB
  ;; give each arm its own `with-terms` (`exposure_test`'s budgeted-sweep pair) or build
  ;; over a cleared store with `with-cleared-kb`.
  (let [kb (tu/fresh)]
    (is (some? kb))
    (is (= {:sentexes 0 :justifications 0} (tu/content-count kb))
        "fresh means empty, not merely bound")))

;; ---- the sweep roster, against the table the scripts read ---------------

(defn- sweep-envs-in-the-shell-table
  "The environment variables `scripts/lib/suite-configs.sh` selects its sweeps with, read
  out of `SWEEP_ENVS` — the shell half of a roster the Clojure half has to match.  Read as
  text rather than by running bash: what is wanted is the *spellings*, and a name spelt
  only in one of the two files is the whole finding."
  []
  (let [txt   (slurp (io/file "scripts/lib/suite-configs.sh"))
        block (second (re-find #"(?s)SWEEP_ENVS=\((.*?)\n\)" txt))]
    (set (map second (re-seq #"\b(VAELII_[A-Z_]+)=" (or block ""))))))

(deftest every-sweep-is-rostered-with-the-vars-it-replaces
  ;; The gap this closes.  A sweep installs its implementation by altering a ROOT, and a
  ;; counted gate (`assert_cost_test`, `lead_side_cost_test`, `join_lead_cost_test`) is a
  ;; claim about one configuration — so every root a sweep replaces has to be a root
  ;; `tu/shipped-defaults` can hand back.  `VAELII_RETE` was not, and
  ;; `join_lead_cost_test` measured the alpha matcher's join for as long as that was true.
  ;; Adding a sweep to the shell table now fails here until it is rostered, and rostering
  ;; it is where its vars get named.
  (let [shell    (sweep-envs-in-the-shell-table)
        rostered (set (map :env tu/sweeps))]
    (is (seq shell) "the SWEEP_ENVS block was found and parsed — the finding is not an empty read")
    (is (= shell rostered)
        (str "the sweep roster and scripts/lib/suite-configs.sh disagree: "
             "only in the shell " (sort (set/difference shell rostered))
             ", only in tu/sweeps " (sort (set/difference rostered shell))))
    (testing "and every var a sweep names is one the pin can hand back"
      (doseq [sym (mapcat :vars tu/sweeps)]
        (is (contains? tu/shipped-defaults (requiring-resolve sym))
            (str sym " is rostered but absent from tu/shipped-defaults"))))))

(defn- owed-map-rows
  "`config_owed_for_path`'s case arms, as `[path-pattern configs]` pairs, read out of
  `scripts/lib/suite-configs.sh` as text — `sweep-envs-in-the-shell-table`'s reason, and
  the same method: what is wanted is the spellings, and a spelling only one side has is
  the whole finding."
  []
  (let [txt    (slurp (io/file "scripts/lib/suite-configs.sh"))
        block  (second (re-find #"(?s)config_owed_for_path\(\) \{(.*?)\n\}" txt))
        joined (str/replace (or block "") #"\\\n\s*" " ")]
    (for [[_ pats owed] (re-seq #"(?m)^\s*([^#\n)]+?)\)\s+printf '([^']*)'" joined)
          pat            (str/split pats #"\|")
          :let           [pat (str/trim pat)]
          :when          (seq pat)]
      [pat (str/split (str/trim owed) #"\s+")])))

(defn- shell-roster
  "`ALL_BACKENDS` and `ALL_SWEEPS`, off the same file."
  []
  (let [txt  (slurp (io/file "scripts/lib/suite-configs.sh"))
        grab (fn [nm]
               (-> (re-find (re-pattern (str "(?s)" nm "=\\((.*?)\\)")) txt)
                   second (or "") str/trim (str/split #"\s+") set))]
    (into (grab "ALL_BACKENDS") (grab "ALL_SWEEPS"))))

(deftest every-path-the-matrix-map-names-is-one-the-tree-has
  ;; `lein test-matrix --owed` runs what the changed files owe, and a row naming a file
  ;; that does not exist is a row that never fires: the change owes nothing, silently,
  ;; which is the shape `--owed` exists to refuse.  A renamed namespace is how a row goes
  ;; stale, and it goes stale without a symptom — the matrix simply stops being run for
  ;; it.  `src/vaelii/impl/equality.clj` was such a row.
  (let [rows (owed-map-rows)]
    (is (seq rows) "the case block was found and parsed — the finding is not an empty read")
    (doseq [[pat _] rows]
      (is (.exists (io/file (str/replace pat #"/\*$" "")))
          (str pat " names nothing in the tree — the change it stands for owes no "
               "configuration, and nothing says so")))))

(deftest every-configuration-the-matrix-map-owes-is-one-a-runner-knows
  ;; The other half: a row may only name a configuration or a group word, since
  ;; `expand_configs` silently drops anything in neither table — so a typo there is also
  ;; a change that quietly owes less than the map says.
  (let [known (into #{"backends" "sweeps" "routine" "full"} (shell-roster))]
    (doseq [[pat owed] (owed-map-rows)
            c          owed]
      (is (contains? known c)
          (str pat " owes " c ", which is neither a configuration nor a group word")))))

(deftest the-pin-hands-back-a-shipped-default-a-sweep-replaced
  ;; The property the gates rely on, over the var that actually bit: whatever the root
  ;; says, the pin reads the reference matcher inside.  Written against a `binding` rather
  ;; than an `alter-var-root` so the test itself leaves no root moved.
  (let [matcher   (requiring-resolve 'vaelii.impl.chain/*matcher*)
        reference (tu/shipped-value matcher)]
    (is (some? reference) "the matcher is rostered")
    (is (= (requiring-resolve 'vaelii.impl.resolution/match-pattern)
           (get tu/shipped-defaults matcher))
        "the matcher's default is held as the var that defines it, so a reload reaches it")
    (with-bindings* {matcher ::something-else}
      (fn []
        (is (= ::something-else (var-get matcher)) "the sweep's replacement is what is installed")
        (tu/with-shipped-config
          (is (identical? reference (var-get matcher))
              "and inside the pin the shipped reader is what answers"))))))

;; ---- sole-answer ---------------------------------------------------------

(deftest sole-answer-returns-the-one-and-says-so-when-there-are-two
  ;; The harness's own refusal, in this namespace's sense: what `sole-answer` must not do
  ;; is accept a two-answer set and hand back one of them, which is `first`'s whole
  ;; behaviour and the reason the call sites moved off it.
  (testing "one answer comes back, and nothing is asserted about the reader"
    (is (= '{?d 3} (tu/sole-answer ['{?d 3}]))))
  (testing "an empty set is not an answer either"
    (is (= :fail (:type (last (recorded #(tu/sole-answer [])))))))
  (testing "two answers fail, and the message carries both"
    (let [[result] (recorded #(tu/sole-answer ['{?d 3} '{?d 4}] '(temporalDistance P R ?d)))]
      (is (= :fail (:type result)))
      (is (re-find #"got 2" (:message result)))
      (is (re-find #"temporalDistance" (:message result))
          "the goal is named, so the failure says which query grew a second answer"))))
