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

  Two more questions are asked of the same scan, because a keyword is not the whole of
  what a caller catches:

  - **what it carries.**  A caller that has branched on the keyword reads the `ex-data`
    next, and what is in the map is decided one throw at a time.  `carried` pins, for
    every `:type` raised in more than one place, the keys all of its throws agree on —
    so a new throw that drops one narrows what a `catch` can act on and fails here
    rather than in somebody's `catch` a release later.  Where the throws agree on
    nothing, `carries-nothing` says why.
  - **whose vocabulary it is.**  `source-files` excludes the koinii subtree because
    koinii spells its refusals `:koinii/…` rather than adding to this flat one — which
    means a koinii refusal spelled *without* the prefix lands in neither vocabulary and
    nothing sees it.  `a-koinii-refusal-is-namespaced` reads that subtree for exactly
    that.

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

(defn delimiter-analysis
  "One string- and comment-aware pass over `src`: `:pairs` maps each opening
  delimiter's position to its closer's, and `:stacks` maps each position named in
  `snapshot-at` to the stack of enclosing opener positions, innermost last.
  Character literals (`\\(`) and string escapes are skipped, so a delimiter in
  either cannot unbalance the count.

  Public because `refusal_roster_test` asks the same question of `test/` — which form
  encloses this keyword — and a second lexer beside this one would be a second set of
  rules to drift from it."
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

(def keyword-type
  "A `:type` whose value is a keyword written out, namespaced or not.  The namespace segment
  is read because koinii spells its refusals `:koinii/…`, and a pattern stopping at the
  slash would collapse all twenty of them to a bare `:koinii`."
  #":type\s+:([A-Za-z][A-Za-z0-9-]*(?:/[A-Za-z][A-Za-z0-9-]*)?)")

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

(defn- token-char?
  "A character that continues a symbol, keyword or number token — anything that is not
  whitespace, a delimiter, a string quote or the start of a comment."
  [^Character c]
  (not (or (Character/isWhitespace c)
           (contains? #{\, \( \) \[ \] \{ \} \" \;} c))))

(defn- datum-end
  "The position just past the one datum starting at `i`, `close` at most.

  A nested collection is stepped over whole through `pairs`, and a string, a character
  literal and a reader-macro prefix are each read by the rules `delimiter-analysis`
  reads them by — so a delimiter inside any of them cannot knock the walk out of step.
  A prefix (`#`, `^`, `'`, `` ` ``, `~`, `@`) decorates the datum after it rather than
  being one, so `@holder` and `#(f %)` each count once."
  [^String src pairs ^long i ^long close]
  (if (>= i close)
    close
    (let [c (.charAt src i)]
      (cond
        (contains? #{\# \^ \' \` \~ \@} c) (recur src pairs (inc i) close)
        (= c \") (loop [j (inc i)]
                   (cond (>= j close)          close
                         (= \\ (.charAt src j)) (recur (+ j 2))
                         (= \" (.charAt src j)) (inc j)
                         :else                  (recur (inc j))))
        (= c \\) (loop [j (+ i 2)]
                   (if (and (< j close) (token-char? (.charAt src j))) (recur (inc j)) j))
        (contains? #{\( \[ \{} c) (inc (long (get pairs i close)))
        :else (loop [j i]
                (if (and (< j close) (token-char? (.charAt src j))) (recur (inc j)) j))))))

(defn- map-data
  "Every datum of the map literal opening at `open`, in order, as the text of each —
  keys at the even indices and their values at the odd ones.

  Pairing by position is the only way to tell a key from a value here: a refusal map
  holds keywords on both sides (`{:type :shape :message …}`), so a scan that collected
  every keyword in the map would report the `:type` values themselves as payload."
  [^String src pairs ^long open]
  (let [close (long (get pairs open (dec (.length src))))]
    (loop [i (inc open), out []]
      (if (>= i close)
        out
        (let [c (.charAt src i)]
          (cond
            (or (Character/isWhitespace c) (= c \,)) (recur (inc i) out)
            (= c \;) (recur (long (let [nl (str/index-of src "\n" i)]
                                    (if (and nl (< (long nl) close)) (inc (long nl)) close)))
                            out)
            ;; `max (inc i)` is the walk's guarantee of progress: a stray closing
            ;; delimiter is not a token character, so `datum-end` would answer `i` and
            ;; the loop would stand still on it.  Balanced source never puts one here —
            ;; but this reads whatever is in `src/`, and a hang is a worse way to learn
            ;; that than a wrong key.
            :else (let [e (min close (max (inc i) (long (datum-end src pairs i close))))]
                    (recur e (conj out (subs src i e))))))))))

(defn- map-keys
  "The keys of the map literal opening at `open` — `map-data`'s even indices."
  [^String src pairs ^long open]
  (vec (take-nth 2 (map-data src pairs open))))

(defn- map-value
  "The text of the value written under `k` in the map literal opening at `open`, or nil
  when the map has no such key.  Only a key *position* counts: `{:mismatch :x}` answers
  `\":x\"` and `{:x :mismatch}` answers nil, which is the same rule `map-keys` reads by."
  [^String src pairs ^long open k]
  (let [data (map-data src pairs open)]
    (some (fn [i] (when (= k (nth data i)) (nth data (inc i) nil)))
          (range 0 (dec (count data)) 2))))

(def ^:private plain-key
  "A map key a caller can read off an `ex-data` by name: a keyword, one colon, no
  namespace.  A symbol key is one the throw computes (`{:type :naf-not-closed kind lit}`
  spells its key `:unknown` or `:aggregate` depending on the antecedent), and a caller
  holding the refusal has no fixed name to look it up under."
  #"^:([A-Za-z][A-Za-z0-9-]*)$")

(defn- refusal-surface
  "The refusal surface in one source string, three ways: `:keywords`, the `:type`
  keywords a caller discriminates on; `:symbols`, the names of the vars standing where a
  keyword literal would be; and `:sites`, one `{:type :keys}` per throw — the keyword and
  the plain keys of the `ex-data` map it is written in.

  One classifier for all three, because they are the same question asked of three
  spellings — scanning any of them separately would be a second set of rules to drift
  from the first.

  A `:type` reached through one of the `defaulted-types` spellings has no map of its own,
  so it puts a keyword on the surface and no site: there is no `ex-data` literal to read
  keys out of, only whatever the caught refusal already carried."
  [^String src]
  (let [kws  (matches-of src keyword-type)
        syms (matches-of src symbolic-type)
        {:keys [pairs stacks]} (delimiter-analysis src (map :pos (into kws syms)))
        n (.length src)
        ex-info-open? (fn [p]
                        (and (= \( (.charAt src p))
                             (some? (re-find #"^\(\s*(?:ex-info|ExceptionInfo\.)[\s(\"]"
                                             (subs src p (min n (+ p 20)))))))
        innermost-map (fn [pos]
                        (last (filter #(= \{ (.charAt src ^long %)) (get stacks pos))))
        payload-map
        (fn [pos]
          ;; the `ex-data` map literal this `:type` is written in, or nil when there is
          ;; none — an `ex-info` handed `(assoc …)` or `(merge …)` has a payload no source
          ;; scan can read, and the innermost `{` on the stack then belongs to some
          ;; enclosing form rather than to this throw.
          (let [mp (innermost-map pos)
                ex (last (filter ex-info-open? (get stacks pos)))]
            (when (and mp (or (nil? ex) (< (long ex) (long mp)))) mp)))
        on-surface?
        (fn [pos]
          (let [map-open (innermost-map pos)
                map-text (when map-open
                           (subs src map-open (min n (inc (get pairs map-open n)))))]
            (or (some ex-info-open? (get stacks pos))
                (and map-text
                     (or (str/includes? map-text ":message")
                         (str/includes? map-text ":ok false"))))))
        defaulted (for [pat defaulted-types
                        [_ kw] (re-seq pat src)]
                    (keyword kw))
        on-surface (filterv (comp on-surface? :pos) kws)]
    {:keywords (into (set defaulted) (map (comp keyword :name)) on-surface)
     :symbols  (into #{} (comp (filter (comp on-surface? :pos)) (map :name)) syms)
     :opaque   (into #{}
                     (comp (filter (fn [{:keys [pos]}]
                                     (and (some ex-info-open? (get stacks pos))
                                          (nil? (payload-map pos)))))
                           (map (comp keyword :name)))
                     on-surface)
     :sites    (into []
                     (keep (fn [{:keys [name pos]}]
                             (when-let [open (payload-map pos)]
                               {:type (keyword name)
                                :mismatch (map-value src pairs open ":mismatch")
                                :keys (into #{}
                                            (comp (keep #(second (re-matches plain-key %)))
                                                  (map keyword)
                                                  (remove #{:type}))
                                            (map-keys src pairs open))})))
                     on-surface)}))

(defn refusal-types
  "The refusal-surface `:type` keywords in one source string.

  Public because `refusal_roster_test` asks the same sources the same question, one step
  further on: not *what* the vocabulary is but whether each word of it is tested and
  written down."
  [^String src]
  (:keywords (refusal-surface src)))

(defn- symbol-valued
  "The refusal-surface `:type` **symbol** names in one source string."
  [^String src]
  (:symbols (refusal-surface src)))

(defn- refusal-sites
  "One `{:type :keys}` per throw in one source string — what each refusal is written to
  carry, as opposed to which keywords exist."
  [^String src]
  (:sites (refusal-surface src)))

(defn- opaque-payloads
  "The `:type` keywords in one source string thrown with an `ex-data` the scan cannot
  read — built by `assoc`, `merge` or a helper rather than written as a map literal."
  [^String src]
  (:opaque (refusal-surface src)))

(defn- carried-by
  "For each `:type` raised at more than one site across `files`, the keys **every** one of
  its throws carries — the intersection, which is the whole of what a caller catching the
  keyword can rely on being there.

  A keyword raised at one site is left out: one throw cannot disagree with itself, so
  pinning its keys would copy the form rather than check it."
  [files]
  (let [by-type (->> files
                     (mapcat (comp refusal-sites slurp))
                     (group-by :type))]
    (into {}
          (comp (filter (fn [[_ sites]] (< 1 (count sites))))
                (map (fn [[ty sites]]
                       [ty (reduce set/intersection (map :keys sites))])))
          by-type)))

;; ---- the discriminants, which are a vocabulary too -----------------------

(def ^:private discriminant-helpers
  "The refusal helpers that write `:mismatch` as a **parameter** — `{:type … :mismatch
  mismatch}` — mapped to the `:type` each raises.  Their discriminants are literals at
  the *call* sites instead, which is where the scan reads them.

  Pinned rather than discovered, and the count is checked: a third helper is a third
  place a discriminant can be minted, and one this list does not name is one whose
  values land in no vocabulary at all — which is the hole the whole roster below exists
  to close, reopened one indirection down."
  {"refuse-table!" :bad-table-entry     ; kb
   "refuse"        :bad-table-entry})   ; predicates/check-facets

(def ^:private computed-discriminants
  "Helper calls whose discriminant is not a literal either — `[helper argument]` to the
  values it can take and why they are not written out.  The scan can read a keyword and
  cannot read a `let`, so these are stated, as `symbol-valued-types` states the `:type`s
  behind a var.

  `owed-facets` answers `facet -> [rule reason]` for the three ways an entry can be
  committed to a facet it does not carry, and `check-facets` refuses under the rule as
  the discriminant — so the rule names are the vocabulary and the table that mints them
  is one map."
  {["refuse" "rule"] {:type   :bad-table-entry
                      :values #{:implication :family-lane :recheck}
                      :why    "predicates/owed-facets' three rules, one per reason a facet is owed"}})

(def ^:private helper-call
  "A call to one of `discriminant-helpers`, with its first argument — the discriminant,
  written as a keyword at all but the `computed-discriminants` sites."
  #"\((refuse-table!|refuse)\s+(:?[A-Za-z][A-Za-z0-9-]*)")

(defn- discriminants-in
  "`{:type #{:mismatch …}}` for one source string: the literal `:mismatch` values written
  in a refusal's payload, plus the ones the helpers above are called with.

  Second value is the count of payloads whose `:mismatch` is a symbol — the helpers'
  own throws, which the caller checks against `discriminant-helpers` so that a new
  helper cannot quietly take its values out of the scan's reach."
  [^String src]
  (let [sites   (refusal-sites src)
        literal (reduce (fn [m {:keys [type mismatch]}]
                          (if (and mismatch (str/starts-with? mismatch ":"))
                            (update m type (fnil conj #{}) (keyword (subs mismatch 1)))
                            m))
                        {} sites)
        called  (reduce (fn [m [_ helper arg]]
                          (let [ty (discriminant-helpers helper)]
                            (if (str/starts-with? arg ":")
                              (update m ty (fnil conj #{}) (keyword (subs arg 1)))
                              (let [{:keys [type values]} (computed-discriminants [helper arg])]
                                (cond-> m values (update type (fnil into #{}) values))))))
                        literal (re-seq helper-call src))]
    [called
     (count (filter (fn [{:keys [mismatch]}]
                      (and mismatch (not (str/starts-with? mismatch ":"))))
                    sites))
     (into #{} (comp (remove (fn [[_ helper arg]]
                               (or (str/starts-with? arg ":")
                                   (computed-discriminants [helper arg]))))
                     (map (fn [[_ helper arg]] [helper arg])))
           (re-seq helper-call src))]))

(def ^:private roster
  "Every `:type` on the refusal surface, by hand.  Going stale is the feature: a new
  or renamed keyword fails the comparison below until it is added here deliberately —
  with a changelog entry, since callers discriminate on it (CONTRIBUTING.md §3.8)."
  #{:already-loaded :anti-symmetric :anti-transitive :arg-constraint-kind :arg-genl :arg-position
    :arg-type :arg-variable :argument-family-ceiling :arity :asymmetric :bad-algebra :bad-arg
    :bad-args :bad-batch :bad-cursor :bad-foreign-manifest :bad-handle :bad-host
    :bad-level :bad-pattern :bad-registrant :bad-reply
    :bad-snapshot :bad-table-entry :base-is-overlay :body-too-large :budget-exhausted
    :choice-head-not-positive
    :compaction-failed :context-escape :cover :cross-origin :daemon-error :damaged-dictionary
    :disallowed-class
    :disjoint :disjunction-too-wide :disk-locked :duplicate-handle :duplicate-tokens :error
    :exception-not-closed :export-busy :frozen-base :functional :handle-ceiling
    :incomplete-racer :inter-arg-type :internal-error :irreflexive :job-busy
    :labeling-inconsistent :labeling-run-blocked
    :llm-api-error :llm-bad-credential :llm-bad-response :llm-encode
    :llm-no-credential :llm-not-applicable :llm-timeout
    :malformed-entry :malformed-manifest :malformed-record :manifest-too-large
    :missing-adapter :missing-resource :naf-justification
    :naf-not-closed
    :naming :nippy-version-moved :nippy-version-unreadable
    :no-base :no-depth-bound :no-destination
    :no-dump :no-foreign-reader :not-a-directory :not-assertible
    :not-checkable :not-defeasible :not-edn :not-empty :not-encodable :not-indexable
    :not-a-report :not-found :not-ground :not-in-process :not-range-restricted :not-stratified
    :not-watchable :not-well-formed :over-ceiling :pattern-too-costly
    :quantifier-not-local :quoted-arg-type
    :report-only
    :reset :shape :short-transfer :solver-failed :solver-unavailable
    :stacked-batch
    :stacked-fork :stale-index-layout :stale-index-records :still-exporting :still-loading :still-stopping
    :too-many-subscriptions :too-many-waiters
    :torn-snapshot :truncated-dump :unauthorized :unbound-deferred :unforkable-index :unknown-backend
    :unknown-command :unknown-entry :unknown-frame :unknown-framing :unknown-handle
    :unknown-op :unknown-option :unknown-source :unknown-subscription :unknown-tactician
    :unminted-nat
    :unparseable :unreadable :unreadable-store :unrecovered-kb :unrecovered-premise
    :unreleased :unsupported-compression :unsupported-context
    :unsupported-format :unsupported-platform :unsupported-variant :unsupported-version})

(def ^:private symbol-valued-types
  "Every `:type` in the tree whose value is a symbol rather than a keyword literal, by
  hand — and what each one is, since the scan can only read the var's name.

  `cancelled` is `vaelii.browser.jobs`'s `::cancelled`, the namespaced keyword a cancelled
  `progress!` throws and the only thing that tells a cancelled job from a failed one. It
  is deliberately not in `roster`: the roster is the *plain-keyword* refusal vocabulary a
  caller discriminates on, and this one is read by the job registry beside it rather than
  by a caller of the API.

  `ty` is `serve`'s `(:type (ex-data e))` put back on the wire — a **pass-through** of
  whatever the caught refusal already carried, so it mints no vocabulary of its own and
  every keyword it can hold is in `roster` by way of the throw it came from."
  #{"cancelled" "ty"})

(def ^:private carried
  "What a caller catching a refusal can **read** — for every `:type` the tree raises in
  more than one place, the keys present in the `ex-data` of every one of its throws.

  The `:type` is the contract and the message is prose, which leaves a caller who has
  branched on the keyword with one question the roster above cannot answer: what is in
  the map. That is answered site by site, so without this nothing notices when two throws
  of one keyword disagree — a twelfth `:unknown-backend` that names no `:axis`, or a
  `:disk-locked` that drops the `:holder`, compiles and passes every other check here.

  A keyword raised for several conditions carries a **discriminant** as well, and the
  convention is `:mismatch` — `:bad-table-entry` was first, `:unknown-option` and
  `:unknown-backend` followed. What is pinned here is only that every throw carries the
  key; the values are their own vocabulary and are pinned in `discriminants`, for the
  reason this table exists one level up — a field left open is a roster with none of the
  checking, and three validators had three spellings for a row with no arm before
  anything compared them.

  **Only the multi-site refusals are here**, and that is the whole of what this can
  check: one throw cannot disagree with itself, so pinning a single-site refusal's keys
  would copy the form rather than check it. One of those carries a question for
  its row in troubleshooting's `:type` index, which is where a caller holding the keyword
  looks.

  An empty set is a refusal whose throws share no key at all. It is not a failure to fix
  here — several are two shapes of one condition and honestly have nothing in common —
  but it is a hole in what a `catch` can act on, so each one is named in
  `carries-nothing` with the reason."
  {:arg-constraint-kind     #{:message :predicate}
   ;; the instance and subtype argument-type refusals, each raised by its singular arm
   ;; (args-problem / genls-problem) and its covering twin (covering-args-problem /
   ;; covering-genls-problem) — the same payload at both
   :arg-genl                #{:message :sentence :arg :expected :position}
   :arg-type                #{:message :sentence :arg :expected :position}
   :arity                   #{:message :opposing-handle :predicate :sentence}
   :bad-arg                 #{:arg :value}
   :bad-args                #{:op}
   :bad-cursor              #{:cursor :token}
   :bad-foreign-manifest    #{:url}
   :bad-handle              #{}
   :bad-level               #{}
   :bad-registrant          #{:key :label :value}
   :bad-reply               #{:status}
   :bad-snapshot            #{:expected :magic :part :path}
   :bad-table-entry         #{:mismatch}
   :base-is-overlay         #{}
   :body-too-large          #{}
   :compaction-failed       #{:log}
   ;; two arms of one condition: `checks/disjoint-problems` names the opposing
   ;; membership's handle, and `checks/cascade-clash` reads a pair the cascade
   ;; supplies both sides of, which no stored sentex witnesses — so the handle is
   ;; the key they do not share
   :disjoint                #{:message :sentence :types}
   :disk-locked             #{:dir :holder}
   :duplicate-handle        #{:handle}
   :exception-not-closed    #{:unbound}
   ;; the conditional refusal, raised by interArg's arm (inter-args-problem) and by the
   ;; homogeneity arm (inter-args-homogeneity-problem) — the same payload at both
   :inter-arg-type          #{:message :sentence :arg :expected :position
                              :trigger :trigger-type :trigger-position}
   :labeling-run-blocked    #{:believed :into :orphaned}
   :llm-api-error           #{}
   :missing-adapter         #{:coordinate :records}
   :missing-resource        #{}
   :naf-not-closed          #{:antecedents :unbound}
   :naming                  #{:context :sentence}
   :no-foreign-reader       #{:kind}
   :not-a-directory         #{:dir}
   :not-assertible          #{}
   :not-edn                 #{}
   :not-empty               #{}
   ;; the daemon's unrouted-path reply and the browser's reply to `POST /op` while it
   ;; reads a remote daemon — both wire replies, in the daemon's shape
   :not-found               #{:error :ok}
   :not-ground              #{:context}
   :not-indexable           #{:sentence}
   :not-range-restricted    #{:antecedents :consequent :problems}
   :not-stratified          #{:context :cycle}
   :not-watchable           #{}
   :not-well-formed         #{}
   :pattern-too-costly      #{:scope}
   :shape                   #{}
   :solver-failed           #{}
   :still-exporting         #{}
   :still-loading           #{}
   :torn-snapshot           #{}
   :truncated-dump          #{}
   :unauthorized            #{}
   :unknown-backend         #{:axis :kind :mismatch}
   :unknown-command         #{:cmd :commands}
   :unknown-frame           #{}
   :unknown-handle          #{}
   :unknown-option          #{:mismatch}
   :unknown-source          #{}
   :unknown-subscription    #{:token}
   :unknown-tactician       #{:known :tactician}
   :unparseable             #{:entry :in :index :message}
   :unreadable              #{:message}
   :unreadable-store        #{}
   :unrecovered-kb          #{:hazards :message :operation :repair}
   :unreleased              #{}
   :unsupported-compression #{}
   :unsupported-context     #{:context}
   :unsupported-variant     #{:variant}})

(def ^:private discriminants
  "Every `:mismatch` value each `:type` is raised with, by hand — the discriminant
  vocabulary, pinned the way `roster` pins the `:type` one and going stale for the same
  reason.

  **The hole this closes.** `carried` pins that a multi-site refusal carries `:mismatch`
  and says outright that the values are left to the entry points: \"the values live with the
  entry points that raise them.\" That is an open field, and an open field is a roster with
  none of the checking — the rule `predicates/check-facets` refuses a declaration for
  breaking, one level down, in this vocabulary's own discriminant. Left open, two
  validators mint two spellings of one condition and nothing compares them, which is how
  `:unarmed-axis`, `:unarmed-reading` and `:no-arm` came to be three words for a row
  with no arm.

  **What each list is for is not the same.** `:unknown-option` and `:unknown-backend`
  are caught by callers and branched on, and `docs/troubleshooting.md` enumerates both —
  held to this roster by `a-doc-that-enumerates-discriminants-names-all-of-them`, since
  a prose list is a roster too. `:bad-table-entry` is raised at namespace load and its
  caller is the build: the value is read by whoever is looking at the failure, so the
  vocabulary is pinned here and not spelled out in a table cell forty rows long."
  {:bad-table-entry
   #{:arbitrable :blank-exemption :blank-title :cached :checked :duplicate-name
     :duplicate-reading :duplicate-title :enumeration :exempt-and-rostered :family
     :family-lane :family-roster :illegal-pair :image-axis :implication :inert :no-arm
     :no-names :partial-cache-triple :reach :read-at :reading :recheck
     :reserved-name :stale-exemption :stops-short :storage :sweep-reach :sweeps
     :unarmed-axis :unarmed-reading :undeclared-arm :unknown-axis :unnamed-pair
     :unrostered-arm :unrostered-reader :vocabulary}
   :unknown-backend
   #{:illegal-pair :illegal-position :reserved-name :unknown-name}
   :unknown-option
   #{:bad-value :conflict :missing-companion :missing-value :not-a-map :unknown-key}})

(def ^:private carries-nothing
  "The refusals raised in more than one place whose throws share **no** key, each with
  why. A caller catching one of these has the keyword, the message and nothing it can
  read by name.

  Most are two shapes of one condition and the reason says so — a wire reply beside the
  throw behind it, a classpath resource beside a file, a solver that ran beside one that
  never started. None of them is a keyword doing several jobs: those carry `:mismatch`
  and are pinned in `carried` instead."
  {:bad-handle
   "one entry point names the `:handle` it could not read; the batch entry point names the `:entry` it
    came from and its `:index` in the batch, because a bad handle in a batch is useless
    without knowing which entry held it."

   :bad-level
   "`lookup` names the `:level` it was given and `escalate` the `:floor` — the key is each
    entry point's own word for the number, and neither entry point has anything to say about the other's."

   :base-is-overlay
   "the fork's own half and its base are the two arguments the caller passed in, so there
    is nothing here the call site does not already have."

   :body-too-large
   "one is thrown with the `:limit` it exceeded, the other is the wire reply the daemon
    sends back — `:ok false` and prose. The reply shape and the throw shape share the
    keyword and nothing else, which is true of every refusal `serve` mirrors."

   :llm-api-error
   "a refusal from the status line carries `:status` and `:body`; one from an error inside
    a 200 body or a stream chunk carries what the provider called it, and the two
    providers do not call it the same thing."

   :missing-resource
   "a classpath resource is named by `:resource` and a file by `:path` — what is missing is
    the thing the caller can go and look for, and those are looked for in different places."

   :not-assertible
   "`:form` names the offending sub-form and `:sentence` the whole one it sat in; a refusal
    about an imperative's own head has only the head, so it names it `:sentence` and there
    is no sub-form to point at."

   :not-edn
   "the wire reply and the throw behind it, as with `:body-too-large`."

   :not-empty
   "exporting names the `:dir` that is not empty and how many `:entries` are in it;
    importing names the `:sentex-count` of the KB that is not. Both refuse a non-empty
    thing and the things are not the same kind."

   :not-watchable
   "four entry points refuse a watch, and each names what it could not watch: a `:f` that is not a
    function, a `:goal` that is not a pattern, a `:context` that does not exist."

   :not-well-formed
   "eight of the twelve name the `:sentence`. The four that do not are refusing a fragment
    before there is a sentence to name — a `forall` body, an aggregate's census, an
    `exceptWhen` — and they name the fragment instead."

   :shape
   "seventeen of the eighteen carry `:message`, because they are the problem maps `check`
    and `check-edit` **return** rather than throw, and a problem map is read for its
    prose. The eighteenth is a plain throw whose prose is the exception's own message."

   :solver-failed
   "a solver that ran and failed carries what the process gave back — `:exit`, `:err`,
    `:out`, `:argv`; one that never started carries the `:op` or the `:mode` it would have
    run. There is nothing an unstarted process could put under the first set of keys."

   :still-exporting
   "the catalog throws it with the `:key` of the entry an unload was asked for; the browser
    answers `POST /op` with it as a wire reply, `:ok false` and prose, while an export walks
    the active KB. The reply shape and the throw shape share the keyword and nothing else,
    as with `:body-too-large`."

   :still-loading
   "the catalog throws it with the `:key` of the entry an export was asked for; the browser
    answers `POST /op` with it as a wire reply while a job writes the active KB. The same
    two shapes as `:still-exporting`."

   :torn-snapshot
   "the dense root table and the index snapshot tear differently, and each names the count
    it was reading when the tear showed: `:entries` against `:expected`, or `:loaded`
    against what the file said was `:durable`."

   :truncated-dump
   "the framing layer measures bytes — `:length` against `:max` — and the reader counts
    records, `:read` against `:stated`. Both are the dump running out early, seen from the
    two layers that can see it."

   :unauthorized
   "the wire reply and the throw behind it, as with `:body-too-large`."

   :unknown-frame
   "the record codec names the `:tag` it read and the index KV log the `:op` — two framings,
    each with its own word for the byte it did not recognize."

   :unknown-handle
   "the same two entry points as `:bad-handle`, refusing a handle that is well formed and not
    stored rather than one that is not a handle at all."

   :unknown-source
   "one names the `:kind` of source the catalog has no reader for; the other is refusing a
    key the catalog does not hold, which the caller passed in and already has."

   :unreadable-store
   "the catalog names the `:path` it could not read and the disk store the `:file` and its
    `:root` — the same failure at one level and at two."

   :unreleased
   "the catalog names the `:key` and `:backend` of the KB still open; the lock names the
    `:dir` and the `:holder` still holding it. One is about a registry entry and the other
    about a file."

   :unsupported-compression
   "three name the `:compression` keyword the caller asked for. The fourth is a codec named
    in a dump and not on the classpath, so it names the `:codec` class to add rather than
    a keyword the caller chose."})

(def ^:private unnamespaced-koinii-refusals
  "koinii spells its refusals `:koinii/…` so that an app layered on the public API adds
  no words to the engine's flat caller-visible vocabulary. One predates the rule.

  `:arbiter-is-party` shipped bare, and is named that way in
  [docs/koinii.md](../../docs/koinii.md), in troubleshooting's `:type` index and in the
  changelog entry that introduced it. Renaming it is a contract change for anyone
  catching it, not a tidy-up, so it stays until one is being made anyway."
  {:arbiter-is-party
   "shipped un-namespaced and documented that way in docs/koinii.md, troubleshooting.md
    and the changelog; renaming it is a breaking change for a caller that catches it."})

(defn all-source-files
  "Every `.clj` under `src/`, koinii included.  `refusal_roster_test` scans this wider
  set: whether a refusal is tested and written down is a question about every refusal the
  tree can raise, and koinii's are raised at the same public entry points the engine's are."
  []
  (->> (file-seq (io/file "src"))
       (filter #(.isFile ^java.io.File %))
       (map #(.getPath ^java.io.File %))
       (filter #(str/ends-with? % ".clj"))
       sort))

(defn source-files
  "Every engine source file to scan for the `:type` roster — every `.clj` under `src/`
  **except the `koinii/` subtree**.  koinii is an application layered on the public API
  (`docs/koinii.md`), not the engine, and it namespaces its own refusals (`:koinii/…`) as
  a deliberate subsystem vocabulary rather than adding to this flat caller-visible one;
  those are koinii's contract, tracked in koinii's own tests, and folding them in would
  churn this roster on koinii's active development.  The directory koinii lives in is that
  boundary — the same line `spi_surface_test` draws — and extracting it to its own repo
  would only move it.

  What the exclusion cannot do is police itself: a koinii refusal spelled without the
  prefix is a word added to the engine's vocabulary by something that is not the engine,
  and it is invisible here precisely because this list drops the file it lives in.
  `a-koinii-refusal-is-namespaced` scans `all-source-files` for that one thing."
  []
  (remove #(str/includes? % "/koinii/") (all-source-files)))

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

(deftest a-refusal-raised-twice-carries-the-same-thing-both-times
  (let [found (carried-by (source-files))]
    (is (< 20 (count found))
        "the scan reads the throw sites — an empty read would make every check below
        pass on two empty maps")
    (testing "a keyword the tree now raises in more than one place is a new payload
              contract — pin what its throws agree on"
      (is (empty? (sort (set/difference (set (keys found)) (set (keys carried)))))))
    (testing "one it no longer raises twice has no agreement left to check"
      (is (empty? (sort (set/difference (set (keys carried)) (set (keys found)))))))
    (testing "and what they agree on is what the table says: a throw that drops a key
              its siblings carry narrows what a `catch` can read, which is a contract
              change however local the edit looked"
      (doseq [[ty keys*] (sort-by key carried)
              :when      (contains? found ty)]
        (is (= keys* (get found ty))
            (str ty " carries " (pr-str (sort (get found ty)))
                 " at every throw, not " (pr-str (sort keys*))
                 " — either put the key back at the throw that dropped it, or pin the"
                 " narrower set here and say so in the changelog"))))))

(deftest a-refusal-writes-its-ex-data-as-a-map-literal
  ;; The check above reads throw sites out of the source, so a payload it cannot read is
  ;; a site that silently does not count — and an intersection computed over the throws
  ;; the scan happened to see is not the intersection. Two `:unknown-backend` throws were
  ;; built `(assoc axes :type …)` and were exactly that: invisible, and free to drop a
  ;; key `carried` claims every throw carries.
  (let [files  (source-files)
        opaque (transduce (map (comp opaque-payloads slurp)) into #{} files)]
    (is (seq files) "the sources were scanned")
    (is (empty? (sort opaque))
        (str "a refusal whose `ex-data` is assembled rather than written: "
             (pr-str (sort opaque))
             ". Write the map out at the throw — `carried` is computed from map literals,"
             " so a payload built by `assoc` or `merge` is one this file cannot hold"
             " anything to."))))

(deftest a-refusal-that-carries-nothing-is-one-somebody-explained
  (let [found  (carried-by (source-files))
        hollow (into #{} (comp (filter (comp empty? val)) (map key)) found)]
    (testing "a refusal whose throws share no key is a keyword a `catch` cannot act on —
              say why here, or give the throws a key in common"
      (is (empty? (sort (set/difference hollow (set (keys carries-nothing)))))))
    (testing "and an explanation for a refusal whose throws now agree on something is
              one that outlived its reason"
      (is (empty? (sort (set/difference (set (keys carries-nothing)) hollow)))))
    (testing "each says why in a sentence, not in a word"
      (doseq [[ty why] (sort-by key carries-nothing)]
        (is (and (string? why) (< 40 (count why)))
            (str ty " needs a reason a reader can act on"))))))

(deftest a-koinii-refusal-is-namespaced
  (let [koinii (filter #(str/includes? % "/koinii/") (all-source-files))
        found  (transduce (map (comp refusal-types slurp)) into #{} koinii)
        bare   (into #{} (remove namespace) found)]
    (is (seq koinii) "the koinii sources were scanned")
    (is (< 10 (count found)) "and its refusals were read")
    (testing "a koinii refusal without the `:koinii/` prefix is a word added to the
              engine's vocabulary by something that is not the engine — `source-files`
              excludes this subtree, so nothing else here would see it"
      (is (empty? (sort (set/difference bare (set (keys unnamespaced-koinii-refusals)))))))
    (testing "and an exception for one that is now namespaced is a stale entry"
      (is (empty? (sort (set/difference (set (keys unnamespaced-koinii-refusals)) bare)))))))

(deftest the-discriminant-vocabulary-is-the-roster
  ;; The same question `the-type-vocabulary-is-the-roster` asks of `:type`, asked one
  ;; level in.  `carried` pins that a multi-site refusal carries `:mismatch` and leaves
  ;; the values to the entry points; this is what stops that from meaning nobody has the list.
  (let [results (map (comp discriminants-in slurp) (source-files))
        found   (apply merge-with into (map first results))
        symbolic (reduce + (map second results))
        unpinned (reduce into #{} (map #(nth % 2) results))]
    (is (< 30 (count (:bad-table-entry found)))
        "the scan collects the discriminants — a near-empty read means the lexer or the
        helper pattern broke, not that the validators stopped saying which way")
    (testing "a `:mismatch` value the roster does not name is a new word in a vocabulary
              a reader of the failure reads — add it here, and check first that it is not
              a second spelling of a condition another validator already names"
      (doseq [[ty vs] (sort-by key found)]
        (is (empty? (sort (set/difference vs (get discriminants ty #{}))))
            (str ty ": " (pr-str (sort (set/difference vs (get discriminants ty #{}))))))))
    (testing "and a roster entry no throw raises is one that outlived its rule"
      (doseq [[ty vs] (sort-by key discriminants)]
        (is (empty? (sort (set/difference vs (get found ty #{}))))
            (str ty ": " (pr-str (sort (set/difference vs (get found ty #{}))))))))
    (testing "every helper that writes `:mismatch` from a parameter is named, so its
              call sites are read: an unnamed one takes its values out of the scan"
      (is (= (count discriminant-helpers) symbolic)
          (str symbolic " payloads write `:mismatch` as a symbol and "
               (count discriminant-helpers) " helpers are named — a new one has to be"
               " added to `discriminant-helpers` with the `:type` it raises")))
    (testing "and a helper called with a discriminant that is neither a keyword nor a
              pinned computation is a value nothing can enumerate"
      (is (empty? unpinned)
          (str "name these in `computed-discriminants` with the values they take: "
               (pr-str (sort unpinned)))))))

(deftest a-doc-that-enumerates-discriminants-names-all-of-them
  ;; The half of the vocabulary a caller actually branches on is written out in
  ;; `docs/troubleshooting.md`, and a prose list is a roster with none of the checking —
  ;; the failure mode the roster above exists to retire, one file over.  A row that names
  ;; two or more discriminants is claiming to be the list, and is held to it; a row that
  ;; says only "`:mismatch` says which" claims nothing and is left alone.
  (let [doc   (slurp "docs/troubleshooting.md")
        rows  (filter #(str/starts-with? % "| `:") (str/split-lines doc))
        kws   (fn [line] (into #{} (map (comp keyword second))
                               (re-seq #"`:([a-z][a-z0-9-]*)`" line)))]
    (is (seq rows) "the troubleshooting index was read")
    (doseq [[ty values] (sort-by key discriminants)
            line        rows
            :when       (str/starts-with? line (str "| `" ty "` |"))
            :let        [named (kws line)
                         listed (set/intersection named values)]
            :when       (< 1 (count listed))]
      (let [allowed (into #{ty :mismatch} (get carried ty))
            extra   (set/difference named values allowed)]
        (is (empty? (sort (set/difference values named)))
            (str "docs/troubleshooting.md's row for " ty " enumerates its `:mismatch`"
                 " values and leaves out "
                 (pr-str (sort (set/difference values named)))
                 " — a partial list is indistinguishable from the whole one"))
        (is (empty? (sort extra))
            (str "the same row names " (pr-str (sort extra)) ", which is neither a"
                 " discriminant of " ty " nor a key its throws carry"))))))
