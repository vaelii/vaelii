;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.shipped
  "The shipped ontology's files on the classpath: which files a layer under `kb/` holds,
  from a filesystem tree and from a packaged jar alike, and the terms their premises name.
  `vaelii.host.seed` reads and loads the files.  See docs/kbs.md."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.sentex :as sx]))

(def anchor
  "The classpath path of the file every KB carries: resource discovery anchors on it when
  a jar records no directory entry for the directory it lists."
  "kb/upper/core.txt")

(defn resource-files
  "The names of the files ending `ext` directly under classpath directory `dir`, sorted,
  or nil when it holds none.  A filesystem tree (repl / lein / test) is listed as a
  directory, and a packaged jar by its own entries, anchored on `anchor` when the jar
  carries no directory entry for `dir`.  Any other protocol is refused rather than answered
  nil: nil here starts a KB with a layer silently absent, the failure
  `seed/read-sentences` refuses one file at a time."
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

(def ^:private terms
  "Every symbol a form of an upper or middle file names, less variables, and every middle
  context; read once."
  (delay
    (into (set (layer-contexts "middle"))
          (comp (mapcat (fn [[dir f]] (text/read-forms (io/resource (str "kb/" dir "/" f)))))
                (mapcat #(tree-seq coll? seq %))
                (filter symbol?)
                (remove sx/variable?))
          (for [dir ["upper" "middle"] f (layer-files dir)] [dir f]))))

(defn shipped-term?
  "Does a form of the shipped upper or middle ontology name `term`, or is `term` a middle
  context?  The term operations refuse such a term as the one they change (docs/api.md,
  \"Contract notes: term operations\")."
  [term]
  (contains? @terms term))
