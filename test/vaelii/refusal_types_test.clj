;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.refusal-types-test
  "Every refusal the tree can raise, checked for the two things that make a refusal
  usable: **a test provokes it**, and **a reader can look it up**.

  `type_contract_test` asserts the `:type` vocabulary — which words exist. This asks the
  next question of each word, and it is the question a list of names cannot answer: a
  keyword nothing throws at in a test is a branch nobody has run, and a keyword written
  down nowhere is a `:type` a caller meets in a `catch` with no way to find out what it
  means. Both failures are invisible to every other check here, because both leave the
  code compiling and the suite green.

  ## The two halves, and where each is satisfied

  - **Tested.** Some test provokes the refusal and discriminates on `:type` in its
    `ex-data`. The scan reads `test/` for a keyword literal sitting inside a top-level
    form that also reads `:type` or `ex-data` — a `deftest` is that form, so the two
    common spellings both count: the keyword compared in place
    (`(is (= :arity (:type (ex-data e))))`) and the type pulled out first and compared to
    a keyword a few lines down. It is a **floor, not a proof**: the scan cannot tell that
    the assertion is about *that* keyword, only that a test asserting on `:type` names it.
    What it does catch is the case worth catching — a refusal no test in the tree names
    at all.

  - **Written down.** The keyword appears in [`docs/troubleshooting.md`](../../docs/troubleshooting.md)
    or [`docs/defenses.md`](../../docs/defenses.md). The two are not interchangeable, and
    which one takes an entry follows from what each page is for: **troubleshooting is
    indexed by symptom**, so a refusal an operator or a caller meets belongs there, under
    the symptom that produced it or in the `:type` index that page closes with;
    **defenses is entry-by-entry with the code**, so a refusal belongs there only when the
    argument for refusing *rather than accepting* is the thing recorded here. Nearly
    every entry is troubleshooting's. A refusal whose mechanism is described on a
    subsystem page is documented there too — the index row is what makes it *findable*
    from the keyword alone, which is all a caller holding one has.

  ## On failure

  - **A refusal no test provokes.** Write the test — one that reaches the throw and
    checks the `:type` in its `ex-data`, never the message text. If the throw is genuinely
    out of a test's reach — it needs a crash at a precise instant, or a store damaged in a
    way no entry point can produce — add it to `unprovokable` with the one line saying why, the
    way `caches_test`'s `not-a-cache-bound` excuses a constant.
  - **A refusal written down nowhere.** Give it a row in troubleshooting's `:type` index,
    with what a caller would have observed and the page that owns the mechanism.
  - **An excuse for a refusal the tree no longer throws, or that a test now provokes.**
    Take the entry out. An excuse outliving its reason is what makes the next reader
    distrust the whole list."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.type-contract-test :as tc])
  (:import [java.io File]))

;; ---- what the tree throws ------------------------------------------------

(defn- thrown-types
  "Every refusal `:type` the sources raise, koinii included."
  []
  (transduce (map (comp tc/refusal-types slurp)) into #{} (tc/all-source-files)))

;; ---- what the tests provoke ----------------------------------------------

(def ^:private keyword-literal
  #":([A-Za-z][A-Za-z0-9-]*(?:/[A-Za-z][A-Za-z0-9-]*)?)")

(def ^:private list-holding-tests
  "The test files that name refusal keywords as **data** rather than asserting on them:
  this namespace and the two vocabulary tests beside it. Scanning them would make every keyword
  its own coverage, which is the one way a coverage test can be green and mean nothing."
  #{"refusal_types_test.clj" "type_contract_test.clj" "violation_kinds_test.clj"})

(defn- test-files []
  (->> (file-seq (io/file "test"))
       (filter #(.isFile ^File %))
       (map #(.getPath ^File %))
       (filter #(str/ends-with? % ".clj"))
       (remove #(list-holding-tests (.getName (io/file ^String %))))
       sort))

(def ^:private defn-form
  #"\(defn-?\s+(?:\^\S+\s+)*([a-zA-Z][^\s\[\](){}]*)")

(defn- matches-of [^String src ^java.util.regex.Pattern pat]
  (let [m (re-matcher pat src)]
    (loop [out []]
      (if (.find m)
        (recur (conj out {:name (.group m 1) :pos (.start m)}))
        out))))

(defn- blank-prose
  "`src` with every string body and comment blanked to spaces — length, offsets,
  newlines and delimiters all preserved, so `delimiter-analysis` reads the blanked
  text exactly as it reads the original.

  The scan below collects keyword literals by regex, and a keyword named in a
  docstring or a `;;` comment is prose, not coverage: fed raw source, a refusal
  keyword listed in a ns docstring counted as \"a test provokes it\", and a refusal
  whose only mention in `test/` was a comment was silently excused — invisible to
  `unprovokable`'s staleness check too, since no entry names it.  Blanking is the
  same lexer walk `delimiter-analysis` makes (`:code` / `:string` / `:comment`, char
  literals and string escapes skipped), applied to the text instead of the stack."
  ^String [^String src]
  (let [n   (.length src)
        out (char-array src)]
    (loop [i 0, mode :code]
      (when (< i n)
        (let [c (.charAt src i)]
          (case mode
            :code
            (cond
              (= c \") (recur (inc i) :string)
              (= c \;) (recur (inc i) :comment)
              (= c \\) (recur (+ i 2) :code)
              :else    (recur (inc i) :code))
            :string
            (cond
              (= c \\) (do (aset out i \space)
                           (when (< (inc i) n) (aset out (inc i) \space))
                           (recur (+ i 2) :string))
              (= c \") (recur (inc i) :code)
              :else    (do (when-not (= c \newline) (aset out i \space))
                           (recur (inc i) :string)))
            :comment
            (if (= c \newline)
              (recur (inc i) :code)
              (do (aset out i \space) (recur (inc i) :comment)))))))
    (String. out)))

(defn- type-helpers
  "The names of the fns `src` defines whose body text satisfies `reads?`. Three characters
  at least: a one- or two-letter name occurs inside half the identifiers in a file, and a
  substring test on it would read every form as evidence."
  [^String src reads?]
  (let [defs  (matches-of src defn-form)
        pairs (:pairs (tc/delimiter-analysis src (map :pos defs)))
        n     (.length src)]
    (into #{}
          (comp (filter #(reads? (subs src (:pos %) (min n (inc (get pairs (:pos %) n))))))
                (map :name)
                (filter #(<= 3 (count %))))
          defs)))

(def ^:private shared-type-helpers
  "The `vaelii.test-util` fns that return a thrown refusal's `:type`, which a test calls as
  `tu/<name>`. The needle is the read itself: test-util also builds terms and fixtures whose
  bodies name `:type` for another reason."
  (delay (into #{}
               (map #(str "tu/" %))
               (type-helpers (blank-prose (slurp "test/vaelii/test_util.clj"))
                             #(str/includes? % "(:type (ex-data")))))

(defn- asserted-in
  "Every keyword literal in one test source that sits inside a top-level form which reads
  a refusal's `:type` — directly, or through one of the file's own helpers.

  The top-level form is the unit because that is the unit a test is written in: a
  `deftest` that catches a refusal, pulls its `:type` out and compares it to a keyword
  three lines later has both halves in one form and neither next to the other.

  **The helpers are read too**, because a namespace that checks more than one refusal
  writes one — a `refusal` or an `ex-type` that returns `(:type (ex-data e))` and leaves
  the keyword alone at the call site with no `:type` in sight. Taking those as evidence is
  what keeps the scan from reporting a well-tested namespace as untested."
  [^String src]
  (let [lits    (matches-of src keyword-literal)
        {:keys [pairs stacks]} (tc/delimiter-analysis src (map :pos lits))
        n       (.length src)
        span    (fn [^long p] (subs src p (min n (inc (get pairs p n)))))
        shared  @shared-type-helpers
        helpers (into shared
                      (type-helpers src (fn [body] (or (str/includes? body ":type")
                                                       (some #(str/includes? body %) shared)))))
        spans   (volatile! {})
        about-types?
        (fn [pos]
          (when-let [top (first (get stacks pos))]
            (let [text (or (get @spans top)
                           (let [t (span top)] (vswap! spans assoc top t) t))]
              (or (str/includes? text "ex-data")
                  (str/includes? text ":type")
                  (some #(str/includes? text %) helpers)))))]
    (into #{} (comp (filter (comp about-types? :pos)) (map (comp keyword :name))) lits)))

(defn- asserted-types []
  (transduce (map (comp asserted-in blank-prose slurp)) into #{} (test-files)))

;; ---- what the docs name --------------------------------------------------

(def ^:private doc-files ["docs/troubleshooting.md" "docs/defenses.md"])

(defn- documented-types
  "Every refusal keyword named in the two pages, read out of their code spans — the
  backticked keyword a doc writes, and the keywords inside a fenced example. Prose
  outside a code span does not count: a page that happened to use the word is not a page
  that documented the refusal."
  []
  (into #{}
        (comp (map slurp)
              (mapcat #(re-seq #"`([^`]*)`" %))
              (map second)
              (mapcat #(re-seq keyword-literal %))
              (map (comp keyword second)))
        doc-files))

;; ---- the excuses ---------------------------------------------------------

(def ^:private unprovokable
  "Refusals no test in this tree reaches, each with the reason. Every other refusal is
  provoked by a test that checks its `:type`; these are the ones where provoking it would
  mean staging a failure the entry points cannot produce."
  {:cover (str "a refuted cover names its membership and its negations, which the entry"
               " point's reads always find, so `assert` stores it and the settle decides it;"
               " the `:type` is carried by the violation the lift, the merge twin and"
               " `abduce` refuse on")})

;; ---- the checks ----------------------------------------------------------

(deftest the-scan-reads-the-tree
  ;; The guard every set-difference test needs: two empty sets differ by nothing, so a
  ;; scan that silently read no files would pass all three checks below forever.
  (is (< 100 (count (thrown-types)))
      "the refusal vocabulary was scanned out of the sources")
  (is (< 100 (count (test-files)))
      "and the test tree was scanned")
  (is (< 10 (count (documented-types)))
      "and the two documentation pages were read"))

(deftest every-refusal-is-one-a-test-provokes
  (let [gap (set/difference (thrown-types) (asserted-types) (set (keys unprovokable)))]
    (is (empty? gap)
        (str "a refusal no test names: " (pr-str (sort gap))
             ". Write a test that provokes it and checks the `:type` in its `ex-data`;"
             " if it cannot be reached from a test, add it to `unprovokable` with the"
             " one line saying why."))))

(deftest every-refusal-is-one-a-reader-can-look-up
  (let [gap (set/difference (thrown-types) (documented-types))]
    (is (empty? gap)
        (str "a refusal named in neither troubleshooting.md nor defenses.md: "
             (pr-str (sort gap))
             ". A caller holding this keyword out of an `ex-data` has nowhere to look it"
             " up — give it a row in troubleshooting's `:type` index."))))

(deftest an-excuse-names-a-refusal-that-is-still-out-of-reach
  (let [thrown   (thrown-types)
        asserted (asserted-types)
        excused  (set (keys unprovokable))]
    (testing "an excuse for a keyword the tree no longer throws is a stale entry"
      (is (empty? (set/difference excused thrown))
          (pr-str (sort (set/difference excused thrown)))))
    (testing "and one a test now provokes is an excuse that outlived its reason"
      (is (empty? (set/intersection excused asserted))
          (pr-str (sort (set/intersection excused asserted)))))
    (testing "each excuse says why in a sentence, not in a word"
      (doseq [[ty why] (sort-by key unprovokable)]
        (is (and (string? why) (< 20 (count why)))
            (str ty " needs a reason a reader can act on"))))))
