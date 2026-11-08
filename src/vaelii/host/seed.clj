;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.seed
  "Ontology KB files: declarative content held as **plain text on the classpath**
  rather than as code.

  A KB file is a list of ordinary vaelii sentences — one s-expression each, with
  `;;` line comments and blank lines allowed — named for the context its sentences
  assert into, and grouped **term-centrically**: every sentence about a vocabulary
  term sits together, and the terms run in natural sort order.  A rule is just a
  sentence carrying an `implies` / `set/*Rule` / `exceptWhen` wrapper.

  **The format itself — reader and writer both — is `vaelii.impl.io.text`**, which is
  where its two non-sentence spellings live (`(set/monotonic S)` and `(set/inert S)`)
  and what `vaelii.core/export-text!` writes.  What is here is the *classpath* side: the
  shallow tree under `resources/kb/` and how a layer's files are discovered in it.

  The files live under `resources/kb/`, in two layers:

      kb/upper/<name>.txt       the upper ontology, every file loaded into CxUniverse
                                (see vaelii.host.core-context)
      kb/middle/<C>.txt         theory contexts, each seeing CxUniverse

  An upper file is named for its domain (`core.txt` is the vocabulary, `interface-rules.txt`
  the `args`→`argAndRest` twin rule); a middle file's *name* is its context.  Only the
  layer a caller names is discovered, so a sibling directory under `kb/` that names no
  layer here is not loaded: `kb/koinii/` is one, an application's own context files, which
  that application loads for itself.  What stays in **code** (vaelii.host.core-context,
  vaelii.host.starter) is the *order* the layers load in and the one computed batch.
  Sentences read with `clojure.edn`, so a KB file is data and can never run code."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.io.text :as text]))

(def anchor
  "The classpath path of the file every KB carries: resource discovery anchors on it when
  a jar records no directory entry for the directory it lists."
  "kb/upper/core.txt")

(defn resource-files
  "The names of the files ending `ext` directly under classpath directory `dir`, sorted,
  or nil when it holds none.  A filesystem tree (repl / lein / test) is listed as a
  directory, and a packaged jar by its own entries, anchored on `anchor` when the jar
  carries no directory entry for `dir`.  Any other protocol is refused rather than answered
  nil: nil here starts a KB with a layer silently absent, the failure `read-sentences`
  refuses one file at a time."
  [dir ext]
  (let [want  (str dir "/")
        res   (or (io/resource dir) (io/resource anchor))
        names (when res
                (case (.getProtocol res)
                  "file" (when-let [d (io/resource dir)]
                           (keep (fn [^java.io.File f]
                                   (let [n (.getName f)]
                                     (when (str/ends-with? n ext) n)))
                                 (.listFiles (io/file d))))
                  "jar"  (let [conn ^java.net.JarURLConnection (.openConnection res)]
                           (for [^java.util.jar.JarEntry e (enumeration-seq (.entries (.getJarFile conn)))
                                 :let [n (.getName e)]
                                 :when (and (str/starts-with? n want)
                                            (str/ends-with? n ext)
                                            (not (str/includes? (subs n (count want)) "/")))]
                             (subs n (count want))))
                  (throw (ex-info (str dir " sits behind classpath protocol "
                                       (.getProtocol res) ", which resource discovery cannot"
                                       " list — it reads the file and jar protocols")
                                  {:type :missing-resource :dir dir :url (str res)}))))]
    (some-> (seq names) sort)))

(defn layer-files
  "The `.txt` file names in layer sub-directory `dir` (`resource-files` of `kb/<dir>`)."
  [dir]
  (resource-files (str "kb/" dir) ".txt"))

(defn layer-contexts
  "The context symbols whose KB files live in the layer sub-directory `dir` (\"middle\"),
  sorted for determinism.  Discovered from the classpath, so dropping a new
  `Cx<Name>.txt` in `kb/<dir>/` loads it with no code change — every context is loaded
  on kb start by default, from a filesystem tree and from a packaged jar alike
  (`layer-files`)."
  [dir]
  (some->> (layer-files dir)
           (map #(symbol (subs % 0 (- (count %) 4))))
           (sort)                                    ; filename-derived symbols — bare sort, same order
           vec))

(defn- resource-path
  "The classpath path of KB file `file` (a context or a file stem, with or without
  `.txt`), optionally under layer `dir`."
  [file dir]
  (let [n (name file)]
    (str "kb/" (when dir (str dir "/")) n (when-not (str/ends-with? n ".txt") ".txt"))))

(defn read-sentences
  "Read every sentence from KB file `file` — the context a middle file is named for, or
  an upper file's name — in file order.  `dir` names the layer sub-directory (\"upper\"
  / \"middle\"), nil for a file at the `kb/` root.  Throws if the resource is missing: a
  silently empty ontology is worse than a failure to start."
  ([file] (read-sentences file nil))
  ([file dir]
   (let [path (resource-path file dir)]
     (if-let [res (io/resource path)]
       (text/read-forms res)
       (throw (ex-info (str "ontology KB file not found on the classpath: " path)
                       {:type :missing-resource :file file :dir dir :resource path}))))))

(defn load-sentences
  "Assert `sentences` into `context`, **order-insensitively** — `text/load-entries!`,
  which is the loader for this format wherever it is read from (`vaelii.core/load-text!`
  reads a file tree through the same one).  Returns kb.

  A KB file's order is its *terms'*, not its dependencies', so a sentence refused
  because content further down the list has not arrived yet is retried rather than
  fatal; `text/load-entries!` says why, and what a clean list pays."
  [kb sentences context]
  (text/load-entries! (fn [sentence ctx o] (v/assert kb sentence ctx (or o {})))
                      (fn [sentence ctx] (v/assert-inert kb sentence ctx))
                      (mapv #(vector % context) sentences))
  kb)

(defn load-context
  "Assert every sentence of the KB file for `context` into that context, through
  `load-sentences` — so the file's term order is not also asked to be a dependency
  order.  `dir` names the layer sub-directory, nil for the `kb/` root.  Returns kb."
  ([kb context] (load-context kb context nil))
  ([kb context dir]
   (load-sentences kb (read-sentences context dir) context)))

(defn- release-order
  "The order of a renames file's name: its version's numbers, `unreleased` after them all."
  [file]
  (let [n (str/replace file #"\.edn$" "")]
    (if (= "unreleased" n) [Long/MAX_VALUE 0 0] (mapv parse-long (str/split n #"\.")))))

(defn compose-renames
  "The renames files `maps`, oldest first, as one map of the four vocabulary keys: each
  `:renames` and `:context-merges` chain followed to its last spelling, the `:re-meanings`
  notes joined and the `:retired` sets unioned.  `:api`, which a caller's code takes, is
  left out."
  [maps]
  (let [chase (fn [m] (update-vals m (fn [t] (loop [t t seen #{}]
                                               (if-let [u (when-not (seen t) (m t))]
                                                 (recur u (conj seen t))
                                                 t)))))]
    {:renames        (chase (apply merge {} (map :renames maps)))
     :context-merges (chase (apply merge {} (map :context-merges maps)))
     :re-meanings    (apply merge-with #(str %1 "; " %2) {} (map :re-meanings maps))
     :retired        (into #{} (mapcat :retired) maps)}))

(defn release-renames
  "Every `renames/<version>.edn` on the classpath, composed (`compose-renames`).  Every
  file is read, since a store records no release: `lein lint`'s E22 keeps each renamed or
  retired symbol out of the shipped KB, so a rename finds a premise to rewrite only in a
  store written before it."
  []
  (compose-renames
   (map #(edn/read-string (slurp (io/resource (str "renames/" %))))
        (sort-by release-order (resource-files "renames" ".edn")))))
