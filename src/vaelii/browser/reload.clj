;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.reload
  "The development browser's source reloader, which only `scripts/start-vaelii-dev.sh`
  turns on (`vaelii.browser.web/dev-repl`).  Before each request it reloads every watched
  source file that changed since the last request, together with every loaded namespace
  that requires one of them, transitively, in dependency order.

  **A protocol, record, type or interface is never redefined.**  Re-evaluating a
  `defprotocol` defines a new interface and empties the protocol's extension map, and
  re-evaluating a `defrecord`, `deftype` or `definterface` defines a new class, so a KB
  loaded before the reload would hold values the reloaded code no longer recognizes.  A
  reload therefore loads a file form by form and leaves out each of those forms whose
  protocol or class already exists; every other form is evaluated.  A record keeps its
  methods inline, where protocol dispatch is a direct interface call, and a method that
  calls a function reaches the reloaded function through its var.  An edit inside such a
  form is not loaded: `restart-owed` names it until the process restarts, and the page
  shows that list.  A form for a class that does not exist yet is evaluated.

  **A held namespace is never re-evaluated at all.**  A namespace whose ns symbol carries
  `:clojure.tools.namespace.repl/load false` holds protocols and method-less records
  (`vaelii.impl.types.*`, `vaelii.impl.protocols`, …).  An edit to one reloads nothing on
  its account, and `restart-owed` names it.

  **Form by form, not tools.namespace's `refresh`.**  `refresh` removes each namespace with
  `remove-ns` before it loads the file again, which re-evaluates every `defonce` in it and
  empties the state a loaded KB keeps there: the cache registry, the change feed's
  listeners, the thaw guard's installed readers.  Loading into the existing namespace
  keeps a `defonce`'s value, as `require :reload` does.

  **Only loaded namespaces reload.**  A dependent this process never loaded, such as an
  LLM provider the browser has not reached, stays unloaded: loading it would run code the
  running server does not use.

  tools.namespace ships in the `:dev` profile only, so its dependency graph and ns-form
  reader are resolved when `wrap-reload` builds the reloader, never at this namespace's
  load.  The standalone jar compiles this namespace and has no tools.namespace."
  (:require [clojure.java.io :as io]
            [clojure.string :as str])
  (:import (clojure.lang LineNumberingPushbackReader LispReader$Resolver Var)
           (java.io File)))

(defn- tn
  "The tools.namespace var `sym`, resolved on first use."
  [sym]
  (requiring-resolve sym))

(defonce ^{:private true
           :doc "What an edit on disk left unloaded since this process started, sorted: a
  held namespace's symbol, or `ns/Name` for a protocol, record, type or interface."}
  owed
  (atom (sorted-set)))

(defn restart-owed
  "The held namespaces, and the protocols, records, types and interfaces as `ns/Name`,
  edited on disk since this process started.  The running process still runs the
  definitions it loaded, so these edits take a restart."
  []
  @owed)

(defn held-decl?
  "Is the ns form `decl` a held namespace's?  The key is read off the ns symbol's
  metadata, the `(ns ^{…} name)` spelling every held namespace uses."
  [decl]
  (false? (:clojure.tools.namespace.repl/load (meta (second decl)))))

(def ^:private defining
  "The `clojure.core` macros whose form defines a protocol or a class."
  '#{defprotocol defrecord deftype definterface})

(def ^:private comparing-resolver
  "Reads a form for comparison only: a `::alias/kw` or a syntax-quoted symbol reads the
  same way on every reading, whatever namespace is loaded."
  (reify LispReader$Resolver
    (currentNS [_] 'user)
    (resolveClass [_ s] s)
    (resolveAlias [_ s] s)
    (resolveVar [_ s] s)))

(defn- class-forms
  "`{Name form}` for each top-level `defprotocol`, `defrecord`, `deftype` and
  `definterface` in `f`, read for comparison, or nil when `f` does not read."
  [^File f]
  (try
    (let [forms (binding [*read-eval* false *reader-resolver* comparing-resolver]
                  (read-string {:read-cond :allow} (str "[" (slurp f) "]")))]
      (into {} (keep (fn [form]
                       (when (and (seq? form) (defining (first form)) (symbol? (second form)))
                         [(second form) form])))
            forms))
    (catch Exception _ nil)))

(defn- source-files [dirs]
  (->> dirs
       (mapcat #(file-seq (io/file %)))
       (filter #(.isFile ^File %))
       (filter #(.endsWith (.getName ^File %) ".clj"))))

(defn- read-entry
  "The ns name, dependencies, held flag, class-defining forms and modification time of
  source file `f`, or nil for a file with no ns form."
  [^File f]
  (when-some [decl ((tn 'clojure.tools.namespace.file/read-file-ns-decl) f)]
    {:ns      (second decl)
     :deps    ((tn 'clojure.tools.namespace.parse/deps-from-ns-decl) decl)
     :held?   (held-decl? decl)
     :classes (class-forms f)
     :time    (.lastModified f)}))

(defn scan
  "The source files under `dirs` as `{file entry}`, each entry
  `{:ns :deps :held? :classes :time}`."
  [dirs]
  (into {} (keep (fn [f] (some->> (read-entry f) (vector f)))) (source-files dirs)))

(defn- graph [entries]
  (let [depend (tn 'clojure.tools.namespace.dependency/depend)]
    (reduce (fn [g {n :ns deps :deps}] (reduce #(depend %1 n %2) g deps))
            ((tn 'clojure.tools.namespace.dependency/graph))
            (vals entries))))

(defn affected
  "The namespaces an edit to the namespaces `changed` reloads, in the order to reload
  them: each changed namespace that is not held, and every namespace under `entries` that
  requires one of those, transitively, minus the held ones.  An edited held namespace
  contributes nothing.  Loaded or not is the caller's filter (`reload!`)."
  [entries changed]
  (let [g     (graph entries)
        held  (into #{} (comp (filter :held?) (map :ns)) (vals entries))
        known (into #{} (map :ns) (vals entries))
        live  (remove held changed)
        deps  ((tn 'clojure.tools.namespace.dependency/transitive-dependents-set) g live)]
    (->> (into (set live) deps)
         (remove held)
         (filter known)
         (sort ((tn 'clojure.tools.namespace.dependency/topo-comparator) g)))))

(defn- defines
  "The name `form` defines a protocol or class under, read in namespace `n`, or nil."
  [n form]
  (when (and (seq? form) (symbol? (first form)) (symbol? (second form)))
    (let [v (ns-resolve n (first form))]
      (when (and (var? v)
                 (= 'clojure.core (ns-name (.-ns ^Var v)))
                 (defining (.-sym ^Var v)))
        (second form)))))

(defn- defined?
  "Does the protocol or class `nm` that a form in namespace `n` defines already exist?"
  [n nm]
  (let [x (ns-resolve n nm)]
    (cond
      (class? x) (= (.getName ^Class x) (str (munge (ns-name n)) "." nm))
      (var? x)   (and (bound? x) (map? @x) (contains? @x :on-interface))
      :else      false)))

(defn- source-path [n]
  (str (-> (name n) (str/replace \- \_) (str/replace \. \/)) ".clj"))

(defn- load-skipping!
  "Load namespace `n`'s source into it form by form, leaving out each form that defines a
  protocol or class that already exists.  Returns the names left out.  The bindings are
  the ones `clojure.lang.Compiler/load` makes, so a file's `set!` of a compiler flag works."
  [n]
  (let [path (source-path n)]
    (with-open [r (LineNumberingPushbackReader. (io/reader (io/resource path)))]
      (binding [*ns*                 *ns*
                *file*               path
                *source-path*        (last (str/split path #"/"))
                *warn-on-reflection* *warn-on-reflection*
                *unchecked-math*     *unchecked-math*
                *data-readers*       *data-readers*
                *read-eval*          true]
        (loop [skipped #{}]
          (let [form (read {:eof ::eof :read-cond :allow} r)]
            (if (identical? ::eof form)
              skipped
              (let [nm (defines *ns* form)]
                (if (and nm (defined? *ns* nm))
                  (recur (conj skipped nm))
                  (do (eval form) (recur skipped)))))))))))

(defn reload!
  "Reload each of `nss` that this process has loaded, in order, leaving every existing
  protocol, record, type and interface as it was loaded.  Returns `{ns #{Name}}` for the
  definitions each reload left out."
  [nss]
  (into {} (for [n nss :when (find-ns n)] [n (load-skipping! n)])))

(defn- reload-changed!
  "Reload what changed under `dirs` since the tracker `st` last looked, and record in
  `owed` each edited held namespace and each left-out definition whose form changed.  A
  reload that throws leaves its namespace at the head of the queue, so the next request
  retries it after the fix."
  [st dirs]
  (locking st
    (let [{old :entries queue :queue} @st
          stamps  (into {} (map (fn [^File f] [f (.lastModified f)])) (source-files dirs))
          fresh   (into {} (keep (fn [f] (when (not= (stamps f) (get-in old [f :time]))
                                           (some->> (read-entry f) (vector f)))))
                        (keys stamps))
          entries (merge old fresh)
          queue   (vec (distinct (concat queue (affected entries (map :ns (vals fresh))))))
          edited  (into {} (keep (fn [[f e]]
                                   (let [was (get-in old [f :classes])]
                                     (when-some [ks (seq (filter #(not= (get was %) (get (:classes e) %))
                                                                 (keys (:classes e))))]
                                       [(:ns e) (set ks)]))))
                        fresh)]
      (swap! owed into (comp (filter :held?) (map :ns)) (vals fresh))
      (reset! st {:entries entries :queue queue})
      (doseq [n queue]
        (let [skipped (get (reload! [n]) n)]
          (swap! owed into (map #(symbol (name n) (name %)))
                 (filter (get edited n #{}) skipped)))
        (swap! st update :queue #(vec (rest %)))))))

(defn wrap-reload
  "Ring middleware that reloads the changed sources under `:dirs` before each request
  (see the namespace docstring).  Throws when tools.namespace is not on the classpath,
  which is what `vaelii.browser.web/hot-reloading` catches to serve without reloading."
  [handler {:keys [dirs]}]
  (tn 'clojure.tools.namespace.dependency/graph)
  (let [st (atom {:entries (scan dirs) :queue []})]
    (fn [req]
      (reload-changed! st dirs)
      (handler req))))
