;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.spi-surface-test
  "The extension points, pinned: the method set and arglists of every protocol a doc
  names as the thing an out-of-tree implementer implements, frozen against
  `test/golden/spi-protocols.edn`.

  **Why these protocols and not the others.**  `boundaries.md` says `vaelii.impl.*` is
  free to change, and it is — that rule is about the *require* surface, and it stands.
  But fourteen of the twenty protocols in the tree are named in a doc as an extension point somebody
  else fills: `docs/storage.md` says a new backend *is* a new `KvBackend`,
  `docs/asp.md` calls `Solver` an extension point, `docs/llm.md` calls `Provider` one,
  `docs/qcn.md` says `add-prover` takes any `Prover`, and `docs/inference.md` invites a
  prover that reads stored facts to implement `SupportingProver` beside it.  A doc that invites an
  implementation makes a promise about the structure of it, whatever the namespace is
  called.  This test is that promise written down.

  The other six are one backend's internal shape — `PTrie` is how the columnar index
  spells its trie, `IPostings` how the dense one packs a set — and nothing outside this
  repo has a reason to implement them.  They are listed in `not-an-extension-point` with the reason
  apiece, and `every-protocol-in-the-tree-is-classified` is what keeps that list honest:
  a new protocol has to be put in one bucket or the other before the suite goes green,
  so the pinned set cannot quietly fall behind the tree.

  **What a signature golden adds over `kv_backend_test`.**  That test says every adapter
  *behaves* — it runs the spec against each one, which is the stronger claim and the
  reason it exists.  It runs against the adapters **in this tree**.  An out-of-tree
  adapter is not there to be run, so the only thing it can be broken by is a change to
  the shape it compiled against, and the only place that shows up is a diff.

  ## On failure

  - **A REMOVED or CHANGED method breaks every implementer at once**, and silently:
    an out-of-tree `deftype` that no longer satisfies a protocol throws at the call
    site, not at compile time.  Restore it, or take the CONTRIBUTING §3.8 Breaking
    entry naming the method, and regenerate the golden in that commit.
  - **An ADDED method is breaking too**, which is the one people miss: an existing
    implementer does not have it, so the protocol it satisfied yesterday it half
    satisfies today.  Prefer a **new** protocol advertised separately — that grows the
    surface without moving what anyone already wrote — and if the method genuinely
    belongs on the protocol, say so in the entry and update the in-tree implementers in the
    same change.

  Names and arglists only, and no docstrings: these protocols carry long explanatory
  comments that are edited often, and a golden that moved on a reworded docstring is
  one that gets regenerated without being read.

  Run `lein regen-goldens` for a deliberate change."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.host.llm.protocol :as llm-protocol]
            [vaelii.impl.protocols :as protocols]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.snapshot :as snapshot-types]
            [vaelii.impl.types.solve :as solve-types])
  (:import [java.io File]))

(def ^:private golden-file "test/golden/spi-protocols.edn")
(def ^:private self-file "test/vaelii/spi_surface_test.clj")

(def extension-points
  "The protocols a doc names as an extension point, each with the doc that names it.  The pairing is
  the argument: a protocol is here because a page tells somebody to implement it, so the
  entry carries the page and the entry is checkable against it."
  [[#'protocols/RecordStore     "docs/storage.md"]
   [#'protocols/Prefetching     "docs/storage.md"]
   [#'protocols/Tallying        "docs/storage.md"]
   [#'protocols/BulkLoading     "docs/storage.md"]
   [#'protocols/RecordSink      "docs/storage.md"]
   [#'protocols/BulkAnnotating  "docs/storage.md"]
   [#'protocols/IndexStore      "docs/storage.md"]
   [#'protocols/KvBackend              "docs/storage.md"]
   [#'snapshot-types/SnapshotSink     "docs/storage.md"]
   [#'snapshot-types/SnapshotSource   "docs/storage.md"]
   [#'solve-types/Solver              "docs/asp.md"]
   [#'prover-types/Prover            "docs/qcn.md"]
   [#'prover-types/SupportingProver  "docs/inference.md"]
   [#'llm-protocol/Provider     "docs/llm.md"]])

(def ^:private not-an-extension-point
  "The protocols deliberately NOT pinned, each with why.  Every one is a single
  backend's internal shape: it exists so two namespaces in this repo can agree, and
  nothing outside the repo has an implementation of it to break."
  {'vaelii.impl.types.trie/PTrie
   "the columnar index's own trie shape; ColumnarIndexStore is its only implementer."
   'vaelii.impl.tokens/ITokens
   "the int-token table behind the columnar trie — an encoding detail of that backend."
   'vaelii.impl.types.dense-roots/PMappedRoots
   "how the dense roots are memory-mapped; read by the dense index and nothing else."
   'vaelii.impl.types.postings/IPostings
   "how the dense KvBackend packs a handle set. A new backend supplies a KvBackend
    (which IS pinned) and never this."
   'vaelii.impl.jtms-protocol/Tms
   "the sparse/dense JTMS swap (docs/density.md); the protocol has its own file so the
    rest of jtms.clj stays instrumentable (scripts/coverage.sh). Both implementations
    ship here and `VAELII_TEST_TMS` picks between them; an internal axis, not an invitation."
   'vaelii.impl.protocols/ArgColumns
   "the argument-root family's read shape — the counted pos→term trie behind
    `sentexes-with-arg`/`count-with-arg`. MemoryKvBackend implements it and DenseRoots
    delegates to that one; both are in this repo and nothing outside supplies it."})

;; ---- the pin ------------------------------------------------------------

(defn- protocol-key [v]
  (symbol (str (:ns (meta v))) (str (:name (meta v)))))

(defn current-spi
  "`{ns/Protocol {method arglists}}` as the tree declares it today."
  []
  (into (sorted-map)
        (map (fn [[v _doc]]
               [(protocol-key v)
                (into (sorted-map)
                      (map (fn [[_ {:keys [name arglists]}]] [name (pr-str (vec arglists))]))
                      (:sigs @v))]))
        extension-points))

(defn regenerate-golden!
  "Rewrite `test/golden/spi-protocols.edn` from the live protocols.  Run `lein
  regen-goldens` after a **deliberate** protocol change, update every in-tree implementer in
  the same change, and commit the golden with it."
  []
  (spit golden-file
        (str ";; Frozen extension points — the method sets an out-of-tree implementer\n"
             ";; compiles against. One entry per protocol a doc names as an extension point.\n"
             ";; Regenerate: `lein regen-goldens`, and read vaelii.spi-surface-test's\n"
             ";; docstring first — adding a method here is breaking too.\n"
             (with-out-str (pprint/pprint (current-spi))))))

(defn- golden [] (edn/read-string (slurp golden-file)))

(deftest no-extension-point-has-appeared-or-disappeared
  (let [current (current-spi)
        frozen  (golden)]
    (is (empty? (set/difference (set (keys frozen)) (set (keys current))))
        (str "BREAKING: pinned protocol(s) gone: "
             (sort (set/difference (set (keys frozen)) (set (keys current))))
             ". An out-of-tree implementer names the protocol var directly."))
    (is (empty? (set/difference (set (keys current)) (set (keys frozen))))
        (str "New protocol(s) in `extension-points`: "
             (sort (set/difference (set (keys current)) (set (keys frozen))))
             " — run `lein regen-goldens` to freeze the method set."))))

(deftest no-protocol-method-has-been-removed-added-or-reshaped
  (let [current (current-spi)
        frozen  (golden)]
    (doseq [proto (sort (set/intersection (set (keys current)) (set (keys frozen))))]
      (let [cur (get current proto)
            gld (get frozen proto)]
        (is (empty? (set/difference (set (keys gld)) (set (keys cur))))
            (str "BREAKING: " proto " lost method(s): "
                 (sort (set/difference (set (keys gld)) (set (keys cur))))
                 ". Every implementer calls them. Restore, or take the CONTRIBUTING"
                 " §3.8 Breaking entry and regenerate the golden in that commit."))
        (is (empty? (set/difference (set (keys cur)) (set (keys gld))))
            (str "BREAKING: " proto " grew method(s): "
                 (sort (set/difference (set (keys cur)) (set (keys gld))))
                 ". An existing implementer does not have them, so it satisfies the"
                 " protocol only in part. Prefer a NEW protocol advertised separately;"
                 " if it belongs here, say so in the Breaking entry, update every"
                 " in-tree implementer, and regenerate the golden."))
        (doseq [m (sort (set/intersection (set (keys cur)) (set (keys gld))))]
          (is (= (get gld m) (get cur m))
              (str "BREAKING: " proto " method " m " arglists changed\n"
                   "  was: " (get gld m) "\n"
                   "  now: " (get cur m) "\n"
                   "Every implementer's method has the old shape.")))))))

;; ---- and the roster that keeps the pinned set complete ------------------

(def ^:private protocol-form
  "`(defprotocol Name` at the start of a line — the only way the tree declares one."
  #"(?m)^\(defprotocol\s+([A-Za-z][\w*+!?<>=-]*)")

(defn- ns-of
  "The `ns` form's name for a source file."
  [^File f]
  (some-> (re-find #"(?m)^\(ns\s+(?:\^\{[^}]*\}\s+)?([\w.-]+)" (slurp f)) second symbol))

(defn declared-protocols
  "`#{ns/Protocol …}` — every protocol declared under `src/`.  Read from the sources
  rather than from loaded namespaces, so a protocol in a namespace nothing has required
  still counts.

  The `koinii/` subtree is excluded: koinii is an **application layered on the public
  API** (`docs/koinii.md`) — it sits beside `impl/` rather than inside it and requires
  nothing under `vaelii.impl` — not part of the engine, so its extension points
  (`CursorStore`, `Medium`) are koinii's own surface documented in koinii's own page and
  this roster pins the *engine's* protocols.  koinii is free to grow protocols without
  reshaping the engine's pinned set; the directory it lives in is that boundary, and
  extracting it to its own repo would only move the same line."
  []
  (into #{}
        (mapcat (fn [^File f]
                  (let [nm (ns-of f)]
                    (map (fn [[_ p]] (symbol (str nm) p))
                         (re-seq protocol-form (slurp f))))))
        (->> (file-seq (io/file "src"))
             (filter #(.isFile ^File %))
             (filter #(str/ends-with? (.getPath ^File %) ".clj"))
             (remove #(str/includes? (.getPath ^File %) "/koinii/"))
             (remove #(= self-file (.getPath ^File %))))))

(deftest every-protocol-in-the-tree-is-classified
  ;; What makes the pinned set trustworthy. Without this, `extension-points` is a list somebody
  ;; wrote once, and a protocol added later is unpinned by default — which is the
  ;; failure mode a golden is supposed to retire, reintroduced one level up.
  (let [declared (declared-protocols)
        pinned   (set (map (comp protocol-key first) extension-points))
        excused  (set (keys not-an-extension-point))
        stray    (set/difference declared pinned excused)]
    (is (empty? stray)
        (str "unclassified protocol(s): " (sort stray)
             ". Every protocol is either one somebody outside this repo implements —"
             " add it to `extension-points` with the doc that says so, and run `lein regen-goldens`"
             " — or one backend's internal shape, in which case add it to `not-an-extension-point`"
             " with the sentence saying why nothing out of tree implements it."))
    (testing "and nothing is classified twice, or classified without existing"
      (is (empty? (set/intersection pinned excused))
          (str "protocol(s) both pinned and excused: "
               (sort (set/intersection pinned excused))))
      (is (empty? (set/difference (set/union pinned excused) declared))
          (str "classified protocol(s) that no longer exist: "
               (sort (set/difference (set/union pinned excused) declared))
               " — drop the entry, and check whether its removal wanted a Breaking"
               " entry.")))))

(deftest every-extension-point-names-a-doc-that-names-it-back
  ;; The entry's second half is a citation, so it is checked: a protocol is pinned *because*
  ;; a page invites an implementation, and a citation nothing verifies is how that
  ;; reason outlives the page it pointed at.
  (doseq [[v doc] extension-points]
    (let [proto (str (:name (meta v)))
          f     (io/file doc)]
      (is (.isFile f) (str proto ": " doc " does not exist"))
      (when (.isFile f)
        (is (str/includes? (slurp f) proto)
            (str proto ": " doc " no longer names it — either the protocol moved doc, or"
                 " the page stopped inviting an implementation, in which case ask"
                 " whether it is still an extension point."))))))
