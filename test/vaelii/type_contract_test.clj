;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.type-contract-test
  "The `:type` vocabulary, pinned as a roster.  Every refusal in the tree carries a
  plain `:type` keyword, and callers discriminate on that one vocabulary — so a new
  or renamed `:type` is a contract change, and this test makes it a *visible* one:
  the scan below collects every literal on the refusal surface from the sources at
  runtime (the same read-the-source pattern as `llm_test`'s roster), and the
  checked-in roster goes stale until someone updates it deliberately, changelog in
  hand.

  What counts as the refusal surface, exactly — the scan is a lexer pass plus a
  regex, and its honesty is these three rules:

  - a literal `:type :<kw>` inside an `(ex-info …)` **or `(ExceptionInfo. …)`** form, at
    any depth — the constructor is called directly where a refusal is counted often
    enough that building the stack trace shows up (`naming/invariant-error`), and a scan
    reading only `ex-info` would have taken `:naming` off the surface the moment the
    other spelling of it went away;
  - a literal `:type :<kw>` inside a map literal that also carries `:message` or
    `:ok false` — the problem-map and wire-reply shapes, which are built as values
    and thrown or sent elsewhere;
  - the two defaulted spellings, which carry no literal `:type :<kw>` pair:
    `(:type (ex-data e) :<kw>)` and `(update :type #(or % :<kw>))`.

  Deliberately excluded, because a `:type` key is not only an error key: the LLM
  stream event maps (`:text`, `:tool-use`, `:done`, …), the ASP statement kinds in
  `aspif.clj`, the catalog's option-descriptor maps (`:flag`, `:slider`, …), and
  `dissoc` key lists — none is a refusal a caller discriminates on, and none sits
  in an `ex-info` or beside a `:message`/`:ok false`.

  A `:type` whose value is a **symbol** is the one shape a source scan cannot answer:
  the keyword is behind a var, so the roster comparison would silently lose it. Rather
  than read past it, the scan collects those separately and `symbol-valued-types` below
  names every one, so a new one fails until somebody says what it is."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]))

(defn- delimiter-analysis
  "One string- and comment-aware pass over `src`: `:pairs` maps each opening
  delimiter's position to its closer's, and `:stacks` maps each position named in
  `snapshot-at` to the stack of enclosing opener positions, innermost last.
  Character literals (`\\(`) and string escapes are skipped, so a delimiter in
  either cannot unbalance the count."
  [^String src snapshot-at]
  (let [want (set snapshot-at)
        n    (.length src)]
    (loop [i 0, mode :code, stack [], pairs (transient {}), stacks (transient {})]
      (if (>= i n)
        {:pairs (persistent! pairs) :stacks (persistent! stacks)}
        (let [c      (.charAt src i)
              stacks (if (want i) (assoc! stacks i stack) stacks)]
          (case mode
            :code
            (cond
              (= c \")  (recur (inc i) :string stack pairs stacks)
              (= c \;)  (recur (inc i) :comment stack pairs stacks)
              (= c \\)  (recur (+ i 2) :code stack pairs stacks)
              (or (= c \() (= c \[) (= c \{))
              (recur (inc i) :code (conj stack i) pairs stacks)
              (or (= c \)) (= c \]) (= c \}))
              (if (seq stack)
                (recur (inc i) :code (pop stack) (assoc! pairs (peek stack) i) stacks)
                (recur (inc i) :code stack pairs stacks))
              :else (recur (inc i) :code stack pairs stacks))
            :string
            (cond
              (= c \\) (recur (+ i 2) :string stack pairs stacks)
              (= c \") (recur (inc i) :code stack pairs stacks)
              :else    (recur (inc i) :string stack pairs stacks))
            :comment
            (recur (inc i) (if (= c \newline) :code :comment) stack pairs stacks)))))))

(def ^:private literal-type
  #":type\s+:([A-Za-z][A-Za-z0-9-]*)")

(def ^:private symbolic-type
  "A `:type` whose value is a **symbol** — the keyword is behind a var, so the scan can
  read the name of the var and not the keyword it holds.

  The lookbehind is what separates a key/value pair from a *lookup*: `(:type p)` reads a
  type off a problem map and is the commonest use of the word in the tree, while
  `{:type cancelled}` writes one.  Only the second puts a keyword on the surface."
  #"(?<![(]):type\s+([a-z][A-Za-z0-9*?!<>=-]*)[\s)\}]")

(def ^:private defaulted-types
  "The two spellings that put a `:type` on the surface with no literal key/value
  pair to scan: the ex-data lookup default and the client's `or` fallback."
  [#"\(:type\s+\(ex-data\s+[^)]*\)\s+:([A-Za-z][A-Za-z0-9-]*)\)"
   #"update\s+:type\s+#\(or\s+%\s+:([A-Za-z][A-Za-z0-9-]*)\)"])

(defn- matches-of
  "Every match of `pat` in `src`, as `{:name :pos}` — position included, since
  classification needs the enclosing forms."
  [^String src ^java.util.regex.Pattern pat]
  (let [m (re-matcher pat src)]
    (loop [out []]
      (if (.find m)
        (recur (conj out {:name (.group m 1) :pos (.start m)}))
        out))))

(defn- refusal-surface
  "Both halves of the refusal surface in one source string, per the rules in the
  namespace docstring: `:keywords`, the `:type` keywords a caller discriminates on, and
  `:symbols`, the names of the vars standing where a keyword literal would be.

  One classifier for both, because they are the same question asked of two spellings —
  scanning the symbols separately would be a second set of rules to drift from the first."
  [^String src]
  (let [lits (matches-of src literal-type)
        syms (matches-of src symbolic-type)
        {:keys [pairs stacks]} (delimiter-analysis src (map :pos (into lits syms)))
        n (.length src)
        ex-info-open? (fn [p]
                        (and (= \( (.charAt src p))
                             (some? (re-find #"^\(\s*(?:ex-info|ExceptionInfo\.)[\s(\"]"
                                             (subs src p (min n (+ p 20)))))))
        on-surface?
        (fn [pos]
          (let [stack    (get stacks pos)
                map-open (last (filter #(= \{ (.charAt src ^long %)) stack))
                map-text (when map-open
                           (subs src map-open (min n (inc (get pairs map-open n)))))]
            (or (some ex-info-open? stack)
                (and map-text
                     (or (str/includes? map-text ":message")
                         (str/includes? map-text ":ok false"))))))
        defaulted (for [pat defaulted-types
                        [_ kw] (re-seq pat src)]
                    (keyword kw))]
    {:keywords (into (set defaulted)
                     (comp (filter (comp on-surface? :pos)) (map (comp keyword :name)))
                     lits)
     :symbols  (into #{} (comp (filter (comp on-surface? :pos)) (map :name)) syms)}))

(defn- refusal-types
  "The refusal-surface `:type` keywords in one source string."
  [^String src]
  (:keywords (refusal-surface src)))

(defn- symbol-valued
  "The refusal-surface `:type` **symbol** names in one source string."
  [^String src]
  (:symbols (refusal-surface src)))

(def ^:private roster
  "Every `:type` on the refusal surface, by hand.  Going stale is the feature: a new
  or renamed keyword fails the comparison below until it is added here deliberately —
  with a changelog entry, since callers discriminate on it (CONTRIBUTING.md §3.8)."
  #{:already-loaded :anti-symmetric :anti-transitive :arg-constraint-kind :arg-genl :arg-position
    :arg-type :arg-variable :arity :asymmetric :bad-algebra :bad-arg
    :bad-args :bad-cursor :bad-foreign-manifest :bad-handle :bad-host
    :bad-level :bad-registrant :bad-reply
    :bad-snapshot :bad-table-entry :base-is-overlay :body-too-large
    :compaction-failed :context-escape :cross-origin :daemon-error :damaged-dictionary
    :disjoint :disk-locked :duplicate-handle :duplicate-tokens :error
    :exception-not-closed :export-busy :frozen-base :functional
    :incomplete-racer :inter-arg-type :internal-error :irreflexive :job-busy
    :labeling-inconsistent :labeling-run-blocked
    :llm-api-error :llm-bad-credential :llm-bad-response :llm-encode
    :llm-no-credential :llm-not-applicable :llm-timeout
    :malformed-entry :malformed-record :missing-resource :naf-justification
    :naf-not-closed
    :naming :no-base :no-depth-bound :no-destination
    :no-dump :no-foreign-reader :not-a-directory :not-assertible
    :not-checkable :not-defeasible :not-edn :not-empty :not-encodable :not-indexable
    :not-a-report :not-found :not-ground :not-in-process :not-range-restricted :not-stratified
    :not-watchable :not-well-formed :quantified-conjunction :quantifier-not-local
    :quoted-arg-type
    :report-only
    :reserved-family :reset :shape :solver-failed :solver-unavailable
    :stacked-fork :stale-index-layout :still-exporting :still-loading :still-stopping
    :too-many-subscriptions :too-many-waiters
    :torn-snapshot :truncated-dump :unauthorized :unbound-deferred :unforkable-index :unknown-backend
    :unknown-command :unknown-entry :unknown-frame :unknown-framing :unknown-handle
    :unknown-op :unknown-option :unknown-source :unknown-subscription :unknown-tactician
    :unparseable :unreadable :unreadable-store :unrecovered-kb :unrecovered-premise
    :unreleased :unsupported-compression
    :unsupported-format :unsupported-platform :unsupported-variant :unsupported-version})

(def ^:private symbol-valued-types
  "Every `:type` in the tree whose value is a symbol rather than a keyword literal, by
  hand — and what each one is, since the scan can only read the var's name.

  `cancelled` is `vaelii.impl.jobs`'s `::cancelled`, the namespaced keyword a cancelled
  `progress!` throws and the only thing that tells a cancelled job from a failed one. It
  is deliberately not in `roster`: the roster is the *plain-keyword* refusal vocabulary a
  caller discriminates on, and this one is read by the job registry beside it rather than
  by a caller of the API.

  `ty` is `serve`'s `(:type (ex-data e))` put back on the wire — a **pass-through** of
  whatever the caught refusal already carried, so it mints no vocabulary of its own and
  every keyword it can hold is in `roster` by way of the throw it came from."
  #{"cancelled" "ty"})

(defn- source-files
  "Every engine source file to scan for the `:type` roster — every `.clj` under `src/`
  **except the `koinii/` subtree**.  koinii is a coordination library layered on the
  public API (`docs/koinii.md`), not the engine, and it namespaces its own refusals
  (`:koinii/…`) as a deliberate subsystem vocabulary rather than adding to this flat
  caller-visible one; those are koinii's contract, tracked in koinii's own tests, and a
  scan that folded them in would both churn this roster on koinii's active development and
  collapse every `:koinii/x` to a bare `:koinii` (the regex stops at `/`).  When koinii is
  extracted to its own module the exclusion becomes the module boundary."
  []
  (->> (file-seq (io/file "src"))
       (filter #(.isFile ^java.io.File %))
       (map #(.getPath ^java.io.File %))
       (filter #(str/ends-with? % ".clj"))
       (remove #(str/includes? % "/koinii/"))
       sort))

(deftest a-symbol-valued-type-is-named-rather-than-read-past
  ;; The one shape a source scan cannot answer: the keyword sits behind a var, so the
  ;; roster comparison below would drop it in silence — present in neither `found` nor
  ;; `roster`, both differences empty, green forever while the vocabulary moved.
  (let [files (source-files)
        found (transduce (map (comp symbol-valued slurp)) into #{} files)]
    (is (= symbol-valued-types found)
        (str "a `:type` behind a var is one this scan reports and cannot resolve — name "
             "it above with what it is, or give it a keyword literal.  New: "
             (pr-str (sort (set/difference found symbol-valued-types)))
             ", gone: "
             (pr-str (sort (set/difference symbol-valued-types found)))))))

(deftest the-type-vocabulary-is-the-roster
  (let [files (source-files)
        found (transduce (map (comp refusal-types slurp)) into #{} files)]
    (is (seq files) "the scan found the sources")
    (is (< 50 (count found))
        "the scan collects the vocabulary — a near-empty read means the lexer or
        the rules broke, not that the tree stopped refusing things")
    (testing "a :type the roster does not name is a new piece of caller-visible
              vocabulary — add it here deliberately, with its changelog entry"
      (is (empty? (sort (set/difference found roster)))))
    (testing "a roster entry the tree no longer spells is a rename or a removal —
              both are the same contract change, seen from the other side"
      (is (empty? (sort (set/difference roster found)))))))
