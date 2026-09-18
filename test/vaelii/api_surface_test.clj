;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.api-surface-test
  "The published API surface, pinned: every public var of the six public namespaces,
  with its arglists, frozen against `test/golden/api-surface.edn`.

  **What this catches that the suite does not.**  `public_api_test` pins which
  namespaces are public — exhaustively, in both directions, so a new file outside
  `impl/`, `host/`, `koinii/` and `browser/` fails there — and then names a handful of entry points per namespace and
  checks they are present.  That is a floor, not a surface: `vaelii.core` alone
  publishes well over a hundred vars, and nothing pins an arglist anywhere.  So a
  removed var no test happens to call, or an arity dropped from one that is called
  only the other way, is a breaking change for every consumer and a green suite here.

  The suite cannot close that on its own, and not for want of coverage.  A commit that
  changes a signature updates the tests that call it in the same commit — correctly,
  and the suite goes green having verified that the new spelling works.  What nobody
  sees is that the old spelling stopped working.  A golden makes that visible where it
  has to be visible, which is the review diff.

  **A pin, not a freeze.**  `boundaries.md` is the rule about what may change;
  this is the record of what did.  Adding a var is compatible and the golden still
  moves, because a surface that grows without anyone reading the diff is how six
  undocumented entry points arrive one at a time — the same argument
  `config_surface_test` makes about switches.

  ## On failure

  - **A REMOVED var, or CHANGED arglists, is breaking.**  Every consumer compiled
    against it: `vaelii-foreign` and the downstream consumers on the roster are in this
    tree's own orbit, and the artifact is on Clojars.  Restore it, or take the CONTRIBUTING §3.8 Breaking
    entry with the migration line naming the new spelling, and regenerate the golden in
    that commit.  `scripts/check-breaking-siblings.sh` reads the `*Breaks:*` tokens off
    that entry, so the entry is what makes the sibling sweep able to find anything.
  - **An ADDED var extends the published surface.**  Run `lein regen-goldens`, give it
    a docstring and a place in `docs/api.md`, and commit the golden in the same commit.

  ## What is pinned, and what is not

  Var **names** and **arglists**, per namespace.  Not docstrings, not metadata, not
  the values — a golden that moved when a docstring was reworded would be regenerated
  without being read, which is the failure mode that makes a golden worthless.

  Arglists are stored as `pr-str` strings rather than as data: a `:or` default holds a
  quote form, and `'x` round-trips through EDN as `(quote x)`, so a golden written as
  data reads back unequal to the surface that wrote it.

  A var tagged `^:no-doc` is out of the contract and skipped, which is the escape hatch
  for something that must be public for wiring and is not a promise.  Nothing carries
  the tag today; it is here so the answer to \"this has to be public but is not API\"
  is a tag rather than an exception in this file.

  The namespace roster is **derived from the tree** — every `.clj` under `src/vaelii`
  outside `impl/`, `host/`, `koinii/` and `browser/` — rather than listed here.  `public_api_test`'s
  `no-public-namespace-is-spelled-impl` pins that the derivation equals the six, so the
  two disagree only when one of them is wrong.  `koinii/` is out for the reason it is out
  of the SPI and refusal rosters: it is an application shipped in this tree, a *consumer*
  of the six rather than one of them (`docs/koinii.md`), and freezing its arglists here
  would put koinii's own development in the engine's compatibility contract.  `browser/` is
  out for the same reason: the browser is the second application (`docs/web.md`)."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]])
  (:import [java.io File]
           [java.util.regex Pattern]))

(def ^:private golden-file "test/golden/api-surface.edn")

(defn public-namespaces
  "The public namespaces, read off the tree: every `.clj` under `src/vaelii` that is not
  under `impl/`, `host/`, `koinii/` or `browser/`.  Sorted, so the golden's order is the
  tree's and not a hash's.  `host/` is private like `impl/` — the tooling above core,
  fronted by four of the five thin entry points (docs/namespaces.md) — and `koinii/` and
  `browser/` are the two apps, so none of them is a public promise."
  []
  (->> (file-seq (io/file "src/vaelii"))
       (filter #(.isFile ^File %))
       (map #(.getPath ^File %))
       (filter #(str/ends-with? % ".clj"))
       (remove #(str/includes? % "/impl/"))
       (remove #(str/includes? % "/host/"))
       (remove #(str/includes? % "/koinii/"))
       (remove #(str/includes? % "/browser/"))
       (map #(-> % (subs (count "src/")) (str/replace #"\.clj$" "")
                 (str/replace "/" ".") (str/replace "_" "-") symbol))
       sort))

(defn- surface-of
  "`{var-name arglists-or-:var}` for one namespace.  A bare `(def x …)` carries no
  `:arglists` and pins by name alone — `serve/ops` and `core/assert-opt-keys` are
  values, and a value has no shape to freeze beyond being there."
  [ns-sym]
  (require ns-sym)
  (into (sorted-map)
        (keep (fn [[sym v]]
                (when-not (:no-doc (meta v))
                  [sym (if-let [a (:arglists (meta v))] (pr-str (vec a)) :var)])))
        (ns-publics ns-sym)))

(defn current-surface
  "`{ns {var arglists}}` as the tree publishes it today."
  []
  (into (sorted-map) (map (juxt identity surface-of)) (public-namespaces)))

(defn regenerate-golden!
  "Rewrite `test/golden/api-surface.edn` from the live namespaces.  Run `lein
  regen-goldens` after a **deliberate** surface change — read this namespace's
  docstring first, because a removed var or a changed arglist is breaking — and commit
  the golden in that same commit."
  []
  ;; Realized before `with-out-str`, not inside it: `current-surface` requires every
  ;; public namespace, and a first-load `println` from a transitive dependency would
  ;; otherwise be captured into the golden and break the next read of it.
  (let [surface (current-surface)]
    (spit golden-file
          (str ";; Frozen public API surface — every public var of the six public\n"
               ";; namespaces, with its arglists.\n"
               ";; Regenerate: `lein regen-goldens`, and read vaelii.api-surface-test's\n"
               ";; docstring first — a removed var or a changed arglist is breaking.\n"
               (with-out-str (pprint/pprint surface))))))

(defn- golden [] (edn/read-string (slurp golden-file)))

;; ---- the pin, both ways -------------------------------------------------

(deftest every-namespace-in-the-published-surface-is-still-published
  (let [current (current-surface)
        frozen  (golden)
        removed (set/difference (set (keys frozen)) (set (keys current)))
        added   (set/difference (set (keys current)) (set (keys frozen)))]
    (is (empty? removed)
        (str "BREAKING: public namespace(s) gone: " (sort removed)
             ". Every consumer requires these by name. Restore them, or take the"
             " CONTRIBUTING §3.8 Breaking entry and regenerate the golden in that"
             " commit."))
    (is (empty? added)
        (str "New public namespace(s): " (sort added)
             " — a namespace outside impl/ is a new public promise. Run"
             " `lein regen-goldens`, and say so in docs/namespaces.md."))))

(deftest no-published-var-has-been-removed-or-had-its-arglists-changed
  (let [current (current-surface)
        frozen  (golden)]
    (doseq [ns-sym (sort (set/intersection (set (keys current)) (set (keys frozen))))]
      (let [cur (get current ns-sym)
            gld (get frozen ns-sym)
            removed (set/difference (set (keys gld)) (set (keys cur)))]
        (is (empty? removed)
            (str "BREAKING: " ns-sym " no longer publishes " (sort removed)
                 ". Restore them, or take the CONTRIBUTING §3.8 Breaking entry with the"
                 " migration line, and regenerate the golden in that commit."))
        (doseq [v (sort (set/intersection (set (keys cur)) (set (keys gld))))]
          (is (= (get gld v) (get cur v))
              (str "BREAKING: " ns-sym "/" v " arglists changed\n"
                   "  was: " (get gld v) "\n"
                   "  now: " (get cur v) "\n"
                   "Callers compiled against the old shape. Restore it, or take the"
                   " CONTRIBUTING §3.8 Breaking entry — and note that ADDING an arity"
                   " is compatible, so the entry may be a Change rather than a Break;"
                   " regenerate the golden either way.")))))))

(deftest a-new-published-var-is-recorded-in-the-golden
  ;; The half that gets waived, and the half that makes this a record rather than a
  ;; ratchet: adding a var breaks nobody, so nothing here fails on compatibility
  ;; grounds. It fails so the addition is read once, by someone, on purpose.
  (let [current (current-surface)
        frozen  (golden)]
    (doseq [ns-sym (sort (set/intersection (set (keys current)) (set (keys frozen))))]
      (let [added (set/difference (set (keys (get current ns-sym)))
                                  (set (keys (get frozen ns-sym))))]
        (is (empty? added)
            (str ns-sym " publishes new var(s): " (sort added)
                 " — compatible, but this extends the published surface. Run"
                 " `lein regen-goldens`, give each one a docstring and a place in"
                 " docs/api.md, and commit the golden in this same commit."))))))

;; ---- the two promises the golden's own failure message makes ------------

(def ^:private published-docs
  "Every published page, as `{filename text}` — `docs/**.md` plus the README.  Held
  once: two tests read the lot, and 57 files is a re-read worth not doing twice."
  (delay
    (into {"README.md" (slurp "README.md")}
          (comp (filter #(.isFile ^File %))
                (filter #(str/ends-with? (.getName ^File %) ".md"))
                (map (juxt #(.getName ^File %) slurp)))
          (file-seq (io/file "docs")))))

;; Clojure symbol constituents, which are NOT java's `\w` — and NOT `/` or `.`.
;;
;; Two ways to get this wrong, and the first draft managed both. `\b` is the
;; obvious spelling and cannot work: a boundary needs a word character on one
;; side, so `\b\*query-engine\*` matches nowhere — `*` is not one and neither is
;; the space before it — and every earmuffed var reads as undocumented while five
;; pages plainly name it. Then `/` and `.` in the class rejected every
;; **qualified** mention, which is how the docs usually write one: `serve/feed-ops`
;; on operations.md:140 is a mention of `feed-ops`, and reading it as one word is
;; the same false negative in a new place.
;;
;; What is left asks the real question — is this name flanked by more symbol — so
;; `edit-batch-keys` does not match inside `edit-batch-keys-extra`.
(def ^:private symbol-char "[\\w*+!?<>='-]")

(defn- mentions-pattern [v]
  (re-pattern (str "(?<!" symbol-char ")" (Pattern/quote (str v))
                   "(?!" symbol-char ")")))

(defn- code-spans
  "Every backticked span and fenced block in `text`, joined — the places a page names an
  **identifier** rather than uses a word.

  Searching the prose too is what makes the check weakest exactly where the surface is
  most ordinary: `handle`, `count`, `store`, `terms` and `types` are English, and a
  bare-word search over 57 pages reads forty-odd sentences apiece as documentation of the
  var.  Five of the published names were \"documented\" that way and would have gone on
  passing with no page mentioning them at all.  Every doc here writes identifiers in
  backticks — `lein lint`'s own doc checks assume it — so that is where to look."
  [^String text]
  (str/join "\n" (concat (map second (re-seq #"`([^`\n]+)`" text))
                         (map second (re-seq #"(?s)```(.*?)```" text)))))

(deftest every-published-var-is-named-in-some-doc
  ;; `a-new-published-var-is-recorded-in-the-golden` tells you to give the new var
  ;; "a place in docs/api.md", and until now nothing checked that you did — an
  ;; instruction in a failure message is worth what enforces it. **Some** doc and
  ;; not api.md specifically: `handler` belongs to web.md, the daemon's ops to
  ;; operations.md, and a check that insisted on one page would push six correct
  ;; entries onto the wrong one.
  (let [text (map code-spans (vals @published-docs))]
    (doseq [[ns-sym vars] (current-surface)]
      (let [absent (remove (fn [v]
                             (let [pat (mentions-pattern v)]
                               (some #(re-find pat %) text)))
                           (keys vars))]
        (is (empty? absent)
            (str ns-sym " publishes " (sort absent) ", named in no doc under docs/"
                 " and not in the README. A published var a reader cannot find is one"
                 " they have to read the source for — give each a place on the page"
                 " that owns its subsystem (docs/api.md for most of vaelii.core), or"
                 " tag it ^:no-doc if it is public for wiring and not a promise."))))))

(deftest every-published-var-carries-a-docstring
  ;; The other half of the same instruction. `doc` is the first thing a caller
  ;; reaches for and the only documentation that travels with the artifact — a
  ;; published var without one is documented only for whoever has this repo open.
  (doseq [[ns-sym vars] (current-surface)]
    (let [bare (remove #(seq (:doc (meta (ns-resolve ns-sym %)))) (keys vars))]
      (is (empty? bare)
          (str ns-sym " publishes " (sort bare) " with no docstring. `(doc "
               (first (sort bare)) ")` is what a caller at a REPL reads, and it is"
               " the only documentation that ships inside the jar.")))))

;; ---- and the thing a golden cannot say on its own -----------------------

(deftest the-golden-covers-the-namespaces-the-boundary-rule-names
  ;; A golden is only a contract about what it contains. If the derivation that feeds it
  ;; silently returned nothing — a moved source root, a changed layout — every test
  ;; above would compare {} to {} and pass. So the count is asserted against the rule
  ;; `boundaries.md` states, which is the one number that does not move on its own.
  (testing "six public namespaces, and the golden holds all six"
    (is (= 6 (count (public-namespaces)))
        (str "the public-namespace derivation found " (count (public-namespaces))
             ": " (public-namespaces)
             " — boundaries.md says six. Either a namespace moved, or the rule did."))
    (is (= (set (public-namespaces)) (set (keys (golden))))
        "the golden and the tree disagree about which namespaces are public"))
  (testing "and every one of them publishes something"
    (doseq [[ns-sym vars] (golden)]
      (is (seq vars) (str ns-sym " publishes nothing — the scan found no vars")))))
