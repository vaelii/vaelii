;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.violation-roster-test
  "The ledger's **kinds**, pinned as a roster: every `:violation` keyword the engine can
  file, collected from the sources at runtime and matched against the tables in
  `vaelii.core/violations`' docstring, in both directions and down to the `:detail` keys.

  **Why the docstring is the pin and not a golden file.**  A kind is not a name somebody
  typed into a deployment script; it is what a consumer branches on, and the branch is
  written against the published table.  A kind reaches the ledger by somebody writing a
  map literal in `settle.clj`, which costs one line and updates nothing — so a kind with
  no row is a public surface an operator finds by reading `settle.clj`, and a row for a
  kind nothing files is the more convincing lie of the two: it is what a deleted
  reporting path leaves behind, and nothing else in the tree notices.

  ## What the scan reads

  Two forms, over `src/` with the strings and comments blanked out first:

  - `{:violation :<kind>` — the literal, and the way a kind is normally introduced.
  - `{:violation <anything else>` — a **computed** kind, filed by a site whose keyword is
    an expression: a check's `:type` relabelled into an entry, or a kind handed to a
    shared entry builder several callers file through.  The scan reads the site and
    cannot read the keyword, so `computed-sites` names the kinds each such site can
    produce; the roster of sites itself is scanned, so a new one is a failing test rather
    than a silent widening.

  Blanking the strings is what separates this scan from `config_surface_test`'s plain
  regex, and it is not fastidiousness: the sources **describe** the entry shape in prose
  — `checks/constraint-violation` and `settle/exposed-clashes` both spell a
  `{:violation :…}` map in their docstrings — so a text scan reads the documentation as a
  filing site and the reverse direction stops catching anything.

  `src/vaelii/core.clj` is the one source file the scan skips: it files no entry, and the
  kinds it names are the table this test reads as the roster.

  ## On failure

  - **A kind with no row.**  Give it one — the keyword, what it means, and the `:detail`
    keys it carries — or list it in `undocumented-by-design` with the sentence saying why
    a row would misdescribe it.
  - **A row naming a kind nothing files.**  Either the keyword is misspelt, or the
    reporting path it described is gone and the row went with it.
  - **A row whose `:detail` keys are not the ones the literal builds.**  The row went
    stale under an edit to the entry, which is the failure a roster of names alone cannot
    see."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            ;; for the `:type` roster the hand-listed kinds are checked against — a
            ;; keyword reaching the ledger through a relabel was thrown by something first
            [vaelii.type-contract-test])
  (:import [java.io File]))

(def ^:private doc-file "src/vaelii/core.clj")

;; ---- the scan -----------------------------------------------------------

(defn code-only
  "`text` with every string literal and line comment replaced by spaces, newlines kept.

  Offsets and line numbers survive it, so a match found here can be read back out of the
  original text — which is what lets the `:detail` check parse the entry map while the
  kind scan ignores the docstring three lines above it.  A character literal is consumed
  whole, so the quote in `(= c \\\")` cannot open a string that runs to the end of the
  file and blanks every filing below it."
  [^String text]
  (let [n  (.length text)
        sb (StringBuilder. n)]
    (loop [i 0, mode :code]
      (when (< i n)
        (let [c  (.charAt text i)
              ;; a newline survives blanking, so line numbers hold either side of it
              b  (if (= c \newline) \newline \space)
              b2 (when (< (inc i) n)
                   (if (= (.charAt text (inc i)) \newline) \newline \space))]
          (case mode
            :code    (cond
                       (= c \\) (do (.append sb (char c))
                                    (when (< (inc i) n) (.append sb (.charAt text (inc i))))
                                    (recur (+ i 2) :code))
                       (= c \") (do (.append sb (char b)) (recur (inc i) :string))
                       (= c \;) (do (.append sb (char b)) (recur (inc i) :comment))
                       :else    (do (.append sb (char c)) (recur (inc i) :code)))
            :string  (cond
                       (= c \\) (do (.append sb (char b))
                                    (when b2 (.append sb (char b2)))
                                    (recur (+ i 2) :string))
                       (= c \") (do (.append sb (char b)) (recur (inc i) :code))
                       :else    (do (.append sb (char b)) (recur (inc i) :string)))
            :comment (do (.append sb (char b))
                         (recur (inc i) (if (= c \newline) :code :comment)))))))
    (.toString sb)))

(def literal-form
  "A kind written where it is filed.  Anchored on the opening brace, so a kind read back
  *out* of an entry — `(= :disjoint (:violation v))` — is not mistaken for a filing."
  #"\{:violation\s+:([a-z][a-z0-9-]*)")

(def computed-form
  "A filing site whose kind is an expression: `{:violation kind`, `{:violation (:type
  p)`.  A `{` after the key is deliberately not matched — `constraint-admission` answers
  `{:violation <entry>}`, which wraps a filing rather than being one."
  #"\{:violation\s+([(a-zA-Z][^\s]*)")

(defn- sources []
  (->> (file-seq (io/file "src"))
       (filter #(.isFile ^File %))
       (filter #(str/ends-with? (.getPath ^File %) ".clj"))
       (remove #(= doc-file (.getPath ^File %)))))

(defn- site-name
  "`<file>/<def>` for the top-level definition enclosing character `pos` — the citation
  form this test carries, because a line number in a checked-in map drifts under every
  edit above it and a definition name does not."
  [^String path ^String code pos]
  (let [stem (-> path (str/replace #"^src/vaelii/(impl/)?" "") (str/replace #"\.clj$" ""))
        nm   (->> (re-seq #"(?m)^\(def[a-z-]*\s+(?:\^\S+\s+)?([^\s()]+)" (subs code 0 pos))
                  last
                  second)]
    (str stem "/" (or nm "<top level>"))))

(defn- matches
  "`[[capture site offset] …]` for one regex over one file's blanked text."
  [rx ^String path ^String code]
  (let [m (re-matcher rx code)]
    (loop [out []]
      (if (.find m)
        (recur (conj out [(.group m 1) (site-name path code (.start m)) (.start m)]))
        out))))

(defn filings
  "Every filing site in the tree, as
  `{:literal {kind #{site}} :computed #{site} :entries {kind #{[path offset]}}}`.

  `:entries` carries the literal sites' offsets, which the `:detail` check reads the
  entry map back out of — the offsets hold against the original text because blanking
  substitutes character for character."
  []
  (reduce
   (fn [acc ^File f]
     (let [path (.getPath f)
           code (code-only (slurp f))]
       (as-> acc acc
         (reduce (fn [acc [kw site pos]]
                   (-> acc
                       (update-in [:literal (keyword kw)] (fnil conj #{}) site)
                       (update-in [:entries (keyword kw)] (fnil conj #{}) [path pos])))
                 acc (matches literal-form path code))
         (reduce (fn [acc [_ site _]] (update acc :computed conj site))
                 acc (matches computed-form path code)))))
   {:literal {} :computed #{} :entries {}}
   (sources)))

(defn kinds-at
  "The kinds `rx` finds in group 1 across the blanked sources.

  For a computed site that is a shared builder taking its kind as an argument: the site
  holds no keyword, but every *caller* holds one as a literal, so what `computed-sites`
  claims about it is checkable rather than merely stated.  Blanked text is what makes
  that safe — the builder is named a dozen times in prose explaining itself, and a scan
  over the raw source would read its own documentation as a caller."
  [rx]
  (into #{} (comp (mapcat (fn [^File f] (matches rx (.getPath f) (code-only (slurp f)))))
                  (map (comp keyword first)))
        (sources)))

(defn entry-keys
  "The keys the entry literal at `offset` in `path` puts on a reader's map, beyond the
  shape every entry shares (`:violation` `:sentence` `:context` `:rule`, and the `:run`
  the ledger stamps): its `:detail` keys, plus any it carries at the top level.

  Read as **data**, not matched: an entry's detail is a `cond->` as often as a map — a
  key that rides a condition is still a key a consumer can find, so the conditional arms
  are walked for what they `assoc`.  `nil` for a detail built any other way, which is
  what `detail-not-scannable` exists to answer for."
  [path offset]
  (let [form (binding [*read-eval* false] (read-string (subs (slurp path) offset)))
        top  (remove #{:violation :sentence :context :rule :detail} (keys form))
        d    (:detail form)]
    (cond
      (not (contains? form :detail)) (set top)
      (map? d)                       (into (set top) (keys d))
      (and (seq? d) (= 'cond-> (first d)) (map? (second d)))
      (into (into (set top) (keys (second d)))
            (comp (filter seq?)
                  (filter #(= 'assoc (first %)))
                  (mapcat #(take-nth 2 (rest %)))
                  (filter keyword?))
            (drop 2 d))
      :else nil)))

;; ---- the sites the scan can find but cannot read ------------------------

(def ^:private computed-sites
  "The filing sites whose kind is a keyword computed at run time, each with the kinds it
  can produce and why the scan cannot see them.

  Three of the five relabel a *problem* map's `:type` into a ledger entry, so the kinds
  are the check vocabulary rather than anything written at the filing site.  The other two
  are shared builders: one takes an arm per declared property, and one takes the kind as
  an argument, so its callers hold the keywords and the site holds none.  Listing them
  is a claim this test takes on trust — but which sites exist is not: the scanned set of
  computed sites is checked against these keys, so a sixth one is a failing test, and its
  kinds have to be named here before the roster means anything again."
  {"checks/constraint-admission"
   {:kinds #{:arity :arg-type :inter-arg-type :arg-genl :arg-position :arg-constraint-kind
             :irreflexive :anti-symmetric}
    :why   (str "relabels `(:type p)` off `constraint-problem`, minus the arbitrable "
                "kinds — a firing places one of those and lets `settle` weigh the pair. "
                "`:irreflexive` and `:anti-symmetric` are non-arbitrable refusals (a lone "
                "self tuple, or a converse no merge reconciles), so a firing drops them")}

   "checks/constraint-violation"
   {:kinds #{:arity :arg-type :inter-arg-type :arg-genl :arg-position :arg-constraint-kind
             :disjoint :functional :asymmetric :anti-transitive :irreflexive :anti-symmetric}
    :why   (str "the same relabel over every `constraint-problem` kind, arbitrable ones "
                "included — the decontextualization lift, the equality twin and abduction "
                "refuse where a firing arbitrates")}

   "checks/rule-violation"
   {:kinds #{:naming :not-well-formed :not-stratified :not-range-restricted :not-indexable
             :not-assertible :exception-not-closed :naf-not-closed :quantifier-not-local
             :quantified-conjunction :arg-variable}
    :why   (str "carries out whatever `:type` `check-rule!` threw, defaulting to "
                "`:not-well-formed` — so its kinds are the rule checks' refusal "
                "vocabulary, minted across `checks`, `rules`, `sentex` and `naming`")}

   "settle/constraint-exposure-entries"
   {:kinds #{:functional :asymmetric :anti-transitive}
    :why   (str "one arm per declared property, and the entry names the property that "
                "convicted rather than repeating it as a literal")}

   "settle/cut-notice"
   {:kinds #{:exposure-truncated :arbitration-truncated}
    :why   (str "the one entry a bounded sweep owes when it stopped short, built once "
                "and called with the kind — so the keywords sit at the callers and the "
                "site itself holds none")
    :kinds-at #"\(cut-notice\s+:([a-z][a-z0-9-]*)"}})

(def ^:private undocumented-by-design
  "Kinds the scan finds that the table deliberately has no row for.

  Empty, and that is the finding rather than an oversight: a kind reaches a consumer
  through one public reader, so there is nowhere for an undocumented one to hide — a
  caller branching on `:violation` meets it whether or not anybody wrote it down.  A kind
  belongs here only when a row would misdescribe the ledger rather than describe it, and
  it carries the sentence saying which."
  {})

(def ^:private detail-not-scannable
  "Kinds whose `:detail` keys no reader of the entry literal can see, each with why.  The
  name checks as usual; only the key-for-key comparison stands aside."
  {:aggregate (str "the entry is `(merge {…} detail)` and `detail` is the caller's map, "
                   "so the keys belong to the numeric error rather than to the site")})

;; ---- and the table that describes them ----------------------------------

(defn- docstring-lines
  "The lines of `core/violations`' docstring, from the `defn` to its argument vector.
  Scoped that tightly so a table in a neighbouring docstring is not read as a claim about
  the ledger."
  []
  (->> (str/split-lines (slurp doc-file))
       (drop-while #(not (str/starts-with? % "(defn violations")))
       rest
       (take-while #(not (re-matches #"\s*\[kb\]\s*" %)))))

(defn- row-cells
  "`[entry means detail]` for a table row, nil for anything else in the docstring."
  [line]
  (when (str/starts-with? (str/triml line) "|")
    (let [cells (mapv str/trim (str/split line #"\|"))]
      (when (and (= 4 (count cells)) (re-find #"`:[a-z]" (get cells 1 "")))
        (subvec cells 1)))))

(defn documented
  "`{kind #{detail-key}}` off the roster tables.

  One row may name several kinds — the two unconditional argument constraints share a
  shape and a sentence — and each takes the row's keys.  One kind may take several rows,
  and the keys **union**: `:arity` is a dropped conclusion in one table and a retroactive
  report in another, and the two carry different maps under the same keyword."
  []
  (reduce (fn [acc [kind ks]] (update acc kind (fnil set/union #{}) ks))
          {}
          (into []
                (comp (keep row-cells)
                      (mapcat (fn [[entry _ detail]]
                                (let [ks (into #{} (map (comp keyword second))
                                               (re-seq #"`:([a-z][a-z0-9-]*)`" detail))]
                                  (for [[_ kind] (re-seq #"`:([a-z][a-z0-9-]*)`" entry)]
                                    [(keyword kind) ks])))))
                (docstring-lines))))

;; ---- the pin, both ways -------------------------------------------------

(defn- filed-kinds
  "Every kind the tree can file: the literals, plus what each computed site relabels."
  [scanned]
  (into (set (keys (:literal scanned))) (mapcat :kinds) (vals computed-sites)))

(deftest every-kind-the-code-files-has-a-row-in-the-public-table
  (let [scanned (filings)
        missing (-> (filed-kinds scanned)
                    (set/difference (set (keys (documented))))
                    (set/difference (set (keys undocumented-by-design))))]
    (is (empty? missing)
        (str "no row in " doc-file "'s `violations` docstring for: " (sort missing)
             ". `violations` is public API and its kinds are what a consumer branches on,"
             " so a kind with no row is one an operator finds by reading the source. Give"
             " each a row — the keyword, what it means, and the `:detail` keys it carries"
             " — or list it in `undocumented-by-design` with the sentence saying why a row"
             " would misdescribe it."
             (when-let [sites (seq (select-keys (:literal scanned) missing))]
               (str " Filed at: " (sort (mapcat val sites)) "."))))))

(deftest every-kind-the-table-names-is-one-the-code-files
  ;; The reverse, and the one a doc-only edit introduces: a row for a kind nothing files
  ;; is the same lie as a kind with no row, and it is the more convincing of the two,
  ;; because it survives every reading that starts from the documentation.
  (let [ghost (set/difference (set (keys (documented))) (filed-kinds (filings)))]
    (is (empty? ghost)
        (str "rows in " doc-file "'s `violations` docstring for kinds nothing files: "
             (sort ghost) ". Either the keyword is misspelt, or the reporting path that"
             " filed it is gone and the row went with it."))))

(deftest the-roster-of-computed-filing-sites-is-the-one-the-scan-finds
  ;; What keeps the escape hatch from becoming the hole. `computed-sites` is a hand-kept
  ;; claim about kinds, and a hand-kept claim rots — so the *sites* are scanned, both
  ;; ways: a new relabelling site fails here until somebody says what it can file, and a
  ;; deleted one fails until its kinds come off the table with it.
  (let [found    (:computed (filings))
        declared (set (keys computed-sites))]
    (is (empty? (set/difference found declared))
        (str "filing sites whose kind is computed and which `computed-sites` does not"
             " name: " (sort (set/difference found declared))
             ". The scan reads the site and cannot read the keyword, so name the kinds it"
             " can file — otherwise the roster silently stops covering them."))
    (is (empty? (set/difference declared found))
        (str "`computed-sites` names sites that file nothing: "
             (sort (set/difference declared found))
             ". Drop them, and take any kind they were the only source of off the table"
             " with them."))))

(deftest every-hand-listed-kind-is-a-type-the-tree-still-mints
  ;; The trusted half of `computed-sites` cannot be read off its own site — the kind is a
  ;; `:type` relabelled at run time — but it is not therefore uncheckable. Every one of
  ;; those keywords reaches the ledger *because something threw it*, so each has to be on
  ;; the refusal surface `type_contract_test` pins. That catches the two ways the hand
  ;; list rots without a `:kinds-at`: a kind spelled wrong, and one the tree stopped
  ;; minting. It cannot catch a kind the tree mints and this table omits, which is what
  ;; the `:why` lines are for.
  (let [surface @(resolve 'vaelii.type-contract-test/roster)
        listed  (into #{} (mapcat :kinds) (vals computed-sites))
        strays  (set/difference listed surface
                                ;; the truncation kinds are this namespace's own
                                ;; vocabulary — filed, never thrown, so no `ex-info`
                                ;; carries them and the `:type` roster rightly omits them
                                (into #{} (filter #(str/ends-with? (name %) "-truncated"))
                                      listed))]
    ;; the guard this whole test would otherwise be missing: a `set/difference` against an
    ;; empty set is empty, so a roster that failed to resolve would pass forever
    (is (< 50 (count surface)) "the `:type` roster resolved and is the vocabulary")
    (is (seq listed) "and `computed-sites` names kinds at all")
    (is (empty? strays)
        (str "`computed-sites` names kinds no refusal in the tree carries: " (sort strays)
             ". Either the spelling drifted or the check that threw it is gone."))))

(deftest a-shared-builders-kinds-are-the-ones-its-callers-pass
  ;; The same principle one level in. A site that takes its kind as an argument leaves the
  ;; keywords at its callers, where they are literals — so for that shape the entry need
  ;; not be trusted at all, and `:kinds-at` says how to find them. A caller added with a
  ;; new kind fails here rather than passing unnoticed, which is the failure the trusted
  ;; half of `computed-sites` cannot catch.
  (doseq [[site {:keys [kinds], rx :kinds-at}] (sort-by key computed-sites)
          :when rx]
    (let [passed (kinds-at rx)]
      (is (= kinds passed)
          (str site ": `computed-sites` claims " (sort kinds) " and its callers pass "
               (sort passed) ". A kind a caller passes and the roster does not name is one"
               " the table stops covering; a kind the roster names and nobody passes is a"
               " reporting path that is gone.")))))

(deftest every-documented-detail-shape-is-the-one-the-entry-builds
  ;; The citation check's analogue, and the one that catches a row going stale rather than
  ;; missing: a `:detail` key added to an entry is a key a consumer can read and nothing
  ;; else would notice. Scoped to the kinds filed *only* by a literal — one a computed
  ;; site also files carries that site's shape too (`(dissoc p :type :sentence)`, the
  ;; check's own problem map), and no scan of the filing site can see it.
  (let [{:keys [literal entries]} (filings)
        rows     (documented)
        computed (into #{} (mapcat :kinds) (vals computed-sites))]
    (doseq [[kind sites] (sort-by key literal)
            :when        (and (not (contains? computed kind))
                              (not (contains? detail-not-scannable kind))
                              (contains? rows kind))]
      (let [built (reduce (fn [acc [path pos]]
                            (if-let [ks (entry-keys path pos)] (into acc ks) (reduced nil)))
                          #{} (get entries kind))]
        (is (= (get rows kind) built)
            (str kind ": the table names " (sort (get rows kind))
                 " and the entry builds " (if built (sort built) "nothing a scan can read")
                 " (" (str/join ", " (sort sites)) "). A key a consumer can read and the"
                 " table does not name is a shape nobody documented; a key the table names"
                 " and the entry does not build is one a consumer reads as nil."))))))

(deftest the-scan-reads-the-code-and-not-the-prose-beside-it
  ;; Both halves matter, and the second is the one that decays quietly: were a docstring
  ;; spelling `{:violation :…}` counted as a filing, the reverse direction would pass on
  ;; the documentation alone and catch nothing at all.
  (testing "a literal in code is a filing"
    (is (= #{"x"} (into #{} (map second)
                        (re-seq literal-form (code-only "(f {:violation :x :detail {}})"))))))
  (testing "the same map spelled in a docstring is not"
    (is (empty? (re-seq literal-form
                        (code-only "(defn f \"answers {:violation :x :detail {}}\" [] nil)")))))
  (testing "nor is one in a comment"
    (is (empty? (re-seq literal-form (code-only ";; files {:violation :x}\n")))))
  (testing "and a character literal opens no string that swallows the filings below it"
    (is (= #{"x"} (into #{} (map second)
                        (re-seq literal-form (code-only "(= c \\\") {:violation :x}")))))))
