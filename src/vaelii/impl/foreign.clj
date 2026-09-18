;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.foreign
  "Formats vaelii **reads and does not write**, and the plugin extension point they arrive through.

  A foreign reader is a bridge, not a feature: an engine-dialect dump and a translated
  OpenCyc corpus are how knowledge that predates this build gets in, and each one is
  finished the day its corpus has been converted once into the format we do write
  (`vaelii.impl.io.export`).  Carried in-tree it would be code that must keep compiling,
  keep passing tests, and keep being read by whoever changes a record shape, in exchange
  for nothing.  So no reader ships here.  This engine reads its own dump format and
  nothing else, and the bridges are **separate artifacts** that teach it a format when
  they are on the classpath — `vaelii-foreign` is the one we publish.

  ## What a plugin does

  It ships a namespace holding a `reader` var and one resource, `vaelii/foreign.edn`,
  which is a map of `kind -> the var holding its reader map`:

      {:engine-dump vaelii.foreign.engine/reader
       :cyc-corpus  vaelii.foreign.cyc/reader}

  Every copy of that resource on the classpath is read and merged, so a build reads the
  union of the bridges it was given and several plugins compose without knowing about
  each other.  A manifest is **edn**, so it declares a name and can never run code, and
  the symbols in it are resolved with `requiring-resolve` **on use** — a plugin's
  namespaces are loaded when something actually asks for its format, and no reference to
  one exists in this build's compile-time graph.  `register` is the same registration
  done in code, for an embedding application that has the reader in hand.

  Nothing else in this repo names a reader namespace, and nothing here has to change to
  add or drop a format.  A build with no plugin refuses a foreign dump or corpus **by
  name** instead of half-reading it, which is this file's job.
  `foreign_contract_test` is what keeps all of that true.

  ## Asking for a reader

  A caller asks by kind and gets a map of functions, or nil:

      (when-let [r (foreign/reader :engine-dump)] ((:decode-frame r) frame))
      ((:load-dir! (foreign/reader! :cyc-corpus)) kb path opts)

  `reader` for a path that has a fallback (the importer reads its own dialect either
  way), `reader!` for one that does not (there is no other way to load a corpus).  What
  a reader map holds is the reader's own business — the extension point carries capability, not a
  protocol, because two foreign formats have nothing in common but being on the way
  out."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [taoensso.trove :as trove])
  (:import [java.io PushbackReader]))

(def manifest-resource
  "The classpath resource a plugin declares its formats in.  Every copy of it is read,
  so the name is fixed and the plugin's own coordinates are its business."
  "vaelii/foreign.edn")

(defn- manifest-entries
  "The `kind -> symbol` pairs one manifest declares, as `[kind sym url]` triples.
  Throws on a manifest that is not a map of keyword to qualified symbol: a malformed
  declaration is a plugin bug, and swallowing it reads exactly like a format nobody
  shipped."
  [^java.net.URL url]
  (let [m (try (with-open [r (io/reader url)]
                 (edn/read (PushbackReader. r)))
               (catch Exception e
                 (throw (ex-info (str "a foreign manifest at " url " does not read as"
                                      " EDN: " (.getMessage e))
                                 {:type :bad-foreign-manifest :url (str url)} e))))]
    (when-not (map? m)
      (throw (ex-info (str "a foreign manifest is a map of kind -> reader var — " url
                           " reads as " (pr-str (type m)))
                      {:type :bad-foreign-manifest :url (str url) :read m})))
    (doseq [[kind sym] m]
      (when-not (and (keyword? kind) (qualified-symbol? sym))
        (throw (ex-info (str "a foreign manifest entry is `:kind ns/reader`, not "
                             (pr-str kind) " " (pr-str sym) ": " url)
                        {:type :bad-foreign-manifest :url (str url)
                         :kind kind :reader sym}))))
    (for [[kind sym] m] [kind sym url])))

(defn- merge-manifests
  "Fold every discovered entry into one `kind -> symbol` map.  Two plugins claiming the
  same kind is a misconfiguration rather than an error — one of them still reads the
  format — so it warns and keeps the **lexicographically smaller symbol**, a tie-break on
  content so that which reader wins never depends on classpath order."
  [entries]
  (reduce (fn [acc [kind sym url]]
            (if-let [prior (get acc kind)]
              (let [winner (first (sort [prior sym]))]
                (trove/log! {:level :warn :id ::duplicate-format
                             :msg (str "two foreign plugins read " kind " (" prior " and "
                                       sym ", the latter from " url ") — using " winner)})
                (assoc acc kind winner))
              (assoc acc kind sym)))
          {}
          entries))

(defn- discover
  "Scan the classpath for manifests.  Announces what it found, once, because the failure
  it is worth pre-empting is a plugin that is present and silently not being seen."
  []
  (let [urls (enumeration-seq (.getResources (clojure.lang.RT/baseLoader)
                                             manifest-resource))
        found (merge-manifests (mapcat manifest-entries urls))]
    (when (seq found)
      (trove/log! {:level :info :id ::discovered
                   :msg (str "foreign formats on the classpath: "
                             (str/join ", " (sort (map name (keys found)))))}))
    found))

(defonce ^{:private true
           :doc "The scan, cached — the classpath does not change under a running JVM.  `rescan` drops
  it, for a repl that has just added one."}
  discovered
  (atom nil))

(defonce ^{:private true
           :doc "Formats registered in code, which take precedence over the discovered ones: a caller
  holding the reader is more specific than a manifest that happens to be on the path."}
  registered
  (atom {}))

(defn rescan
  "Forget the cached classpath scan, so the next lookup reads the manifests again."
  [] (reset! discovered nil) nil)

(defn formats
  "Every format this build can be asked for: `kind -> the var holding its reader map`.
  Resolved on use, so an entry naming a namespace that is not here is not an error — it
  is a plugin that has gone, or one whose jar is missing."
  []
  (merge (or @discovered (reset! discovered (discover))) @registered))

(defn register
  "Declare that `sym` — a qualified symbol naming a var that holds a reader map — reads
  `kind`, in code rather than through a manifest.  Wins over discovery, and returns the
  full registry."
  [kind sym]
  ;; `ex-info` rather than `{:pre}`, for the reason `vaelii.impl.rules` gives about its
  ;; own entry points: this is a documented public call (docs/foreign.md), and an
  ;; AssertionError names the predicate that failed rather than the value that failed
  ;; it — and is elided entirely under `*assert*` false, which would store the bad
  ;; registration silently.
  (when-not (keyword? kind)
    (throw (ex-info (str "foreign/register: kind must be a keyword, got " (pr-str kind))
                    {:type :bad-arg :arg :kind :value kind})))
  (when-not (qualified-symbol? sym)
    (throw (ex-info (str "foreign/register: sym must be a namespace-qualified symbol"
                         " naming a var that holds a reader map, got " (pr-str sym))
                    {:type :bad-arg :arg :sym :value sym})))
  (swap! registered assoc kind sym)
  (formats))

(defn unregister
  "Drop a registration `register` made.  A format a manifest also declares stays
  readable — this undoes the call, not the classpath."
  [kind]
  (swap! registered dissoc kind)
  (formats))

(defn reader
  "The reader map for `kind`, or **nil** when nothing on this classpath reads it.
  Resolved through `requiring-resolve`, which is what keeps the reference out of the
  compile-time dependency graph."
  [kind]
  (when-let [sym (get (formats) kind)]
    (try
      (some-> (requiring-resolve sym) deref)
      ;; a missing namespace is the expected outcome when the plugin is not installed;
      ;; a *broken* one is not — a plugin that is installed and fails to compile logged
      ;; at :debug sends the operator to reinstall what is already there
      (catch java.io.FileNotFoundException e
        (trove/log! {:level :debug :id ::unavailable
                     :msg  (str "no reader for " kind ": " (.getMessage e))})
        nil)
      (catch Exception e
        (trove/log! {:level :warn :id ::broken-reader
                     :msg  (str "the reader for " kind " is on the classpath and failed"
                                " to load: " (.getMessage e))
                     :error e})
        nil))))

(defn reader!
  "The reader map for `kind`, or throw — naming the kind, and what this build does read.
  For a path with no fallback."
  [kind]
  (or (reader kind)
      (throw (ex-info (str "this build does not read " (name kind) " — the formats it"
                           " reads are "
                           (pr-str (into (sorted-set) (filter reader) (keys (formats))))
                           "; install a plugin that declares it"
                           " (see vaelii.impl.foreign)")
                      {:type :no-foreign-reader :kind kind
                       :available (into #{} (filter reader) (keys (formats)))}))))

(defn directory-loader!
  "The `:load-dir!` fn of the reader for `kind`, or throw `:no-foreign-reader` — for a
  build with no plugin for `kind` (`reader!`'s refusal), and for a reader that loads no
  directory.  `vaelii.core/load-foreign!` calls it."
  [kind]
  (or (:load-dir! (reader! kind))
      (throw (ex-info (str "the " (name kind) " reader loads no directory")
                      {:type :no-foreign-reader :kind kind
                       :available (into #{} (filter reader) (keys (formats)))}))))

(defn available?
  "Can this build read `kind`?  For a caller deciding what to **attempt** — an embedding
  application choosing between a foreign source and a converted one, without paying
  `reader!`'s throw to find out.

  Nothing in the engine asks it, and that is a decision rather than an oversight: the
  catalog offers a found KB whether or not a reader is present, because the honest answer
  to *I cannot read this* is a load that fails saying so and not a KB that quietly stops
  being listed (docs/foreign.md, \"Who asks\").  So this is published for a caller outside
  the engine, and every call site in here takes `reader` or `reader!` instead."
  [kind]
  (some? (reader kind)))
