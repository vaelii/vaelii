;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.source-identity
  "The **source identity**: a digest of the engine definitions that derive belief.  A
  reasoning image is stamped with it, and an open installs the image only when its own source
  identity is equal, so an image is never installed by code that would derive a different
  belief from the same records.

  ## Which namespaces

  The walk first collects a set of namespaces: the transitive closure of `namespace-roots`
  over three kinds of edge, each read from the source files themselves rather than from
  the loaded namespaces:

  - the `ns` form's `:require`, `:use` and `:import` clauses — an imported deftype or
    defrecord class names the namespace that defines it;
  - every fully-qualified symbol under a `quote` in code.  These are the edges no `ns`
    form states: the `requiring-resolve` targets and the fixed symbol tables that name
    them (`vaelii.core`'s calculi, reasoners and solvers, `vaelii.impl.imperative`'s `do/`
    handlers, `vaelii.impl.wiring`'s three entry points).

  The walk follows `vaelii.core` and `vaelii.impl.*` and nothing else.  Code from outside
  those prefixes — a registered prover or evaluatable, a foreign plugin — is not in the
  digest; `vaelii.impl.reasoning-image` refuses to write or install an image for a KB that
  runs any.

  ## Which definitions

  The digest covers the top-level forms reachable from `roots` inside that namespace set,
  not whole files.  A form reaches every form that defines a var one of its symbols
  resolves to.  A symbol resolves through its namespace's `ns` form: an alias, a `:refer`,
  a `:refer :all` or `:use`, the namespace's own definitions, and an `:import` for a class
  name.  A symbol that resolves to none of these, a `clojure.core` var among them, reaches
  nothing.  The walk reads no scope, so a local binding that shadows a var reaches the var
  anyway: the set of reached forms is a superset of the forms recover can run.

  The roots are the forms that build and recover a KB: `vaelii.core/open-kb`, which also
  installs the callbacks the taxonomy calls through a map rather than through a symbol,
  `vaelii.impl.recovery/recover` and `recover-with-image`, and the three targets of
  `vaelii.impl.wiring`.  The reasoning image's writer is reached from `recover`, so an edit to
  the code that writes an image discards the images it wrote.

  Some forms run without a symbol naming them.  Each of these is included by a rule of its
  own:

  - a `defmethod` of a reached `defmulti`, and every `defmethod` of a multimethod outside
    the namespace set (`print-method` among them);
  - a `deftype`, `extend-type`, `extend-protocol` or `extend` form that names a reached
    protocol, and every extension of a protocol
    outside the namespace set;
  - every `defrecord`, because nippy and the EDN reader construct a record from its class
    name alone;
  - every top-level form that defines no var, in every namespace of the set: a
    registration, an `alter-var-root` or a `set!` runs when its namespace loads, and a
    namespace in the set is loaded whether or not any of its definitions is reached;
  - an `s/fdef` of a reached var.

  A reached macro contributes its whole form, and the symbols its syntax-quote names resolve
  in the macro's namespace like any other.  A reached `def` or `defonce` contributes its
  value and its metadata, so a `^:dynamic` default and a `^:const` value are covered.

  ## Instrumentation

  `observe`, `profile`, `settle-phases` and `caches` are called on the settle path, so the
  walk reaches them and their reached definitions are in the digest.  No namespace is
  marked as belief-neutral: `caches/limit-of` returns the bound a cache applies, and the
  value flows into the code that calls it, so no namespace of the four is called in
  statement position only.

  ## What is hashed

  Each form is hashed with four things removed: comments, `(comment …)` blocks,
  docstrings, and the reader's position metadata.  An edit that changes only prose
  therefore leaves the digest unchanged.  An edit to code, or to metadata the compiler reads
  (`^:dynamic`, `^:const`, a type hint), changes the digest when the form is reached.  The
  digest takes each reached form under its namespace and the var it defines, so moving a
  definition to another namespace changes it too.

  The reader mints a fresh name on every read for two kinds of symbol: a syntax-quote
  auto-gensym (`x#`) and an anonymous-fn argument (`%`).  Both are renumbered in order of
  first appearance within their top-level form, so two reads of one file hash alike.
  Aliases, classes and vars are read through a `*reader-resolver*` that resolves each to
  itself, so a file reads the same way whether or not its namespace is loaded.

  ## A namespace with no source

  The Clojars jar, the uberjar and a source checkout all carry the `.clj` files, so every
  namespace is normally read as forms.  A namespace on the classpath only as compiled
  classes contributes the digest of the code it loads from instead, whole: the jar its
  `__init` class sits in, or every class file of the namespace in a class directory.  A
  namespace compiles to one class per fn, so no single class file covers its code.  The
  jar digest changes with any rebuild, which is conservative: an image is discarded more
  often, never installed under different code.

  ## Libraries

  Each third-party library the namespace set requires or imports contributes the file name
  of the jar its code loads from (`nippy-3.5.0.jar`), and the file name carries the
  version.  A library loaded from a directory rather than a jar contributes its namespace or
  class name.  JDK classes contribute nothing.

  ## The parse memo

  The parse of a file — its forms, each classified and hashed, and its edges — is memoized
  per file, in the `:source-parses` cache.  Every call takes each file's stat, its
  modification time and length.  A file whose stat is unchanged since its last read is not
  read again; any other file is read and its bytes hashed, and parsed only when the SHA-256
  of its bytes changed.  An edit that leaves both the modification time and the length
  unchanged can land only within the file system's timestamp resolution of the read before
  it, so a file modified within `stat-window-ms` before its read is read again at the next
  call.  The digest therefore describes the files as they stand at the call, and an edit
  made at a REPL between two calls reaches it.  The walk over the definitions reruns only
  when the SHA-256 of some file in the set differs from the previous call's."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [vaelii.impl.caches :as caches])
  (:import [java.io File PushbackReader StringReader]
           [java.net URL]
           [java.nio.file Files]
           [java.security MessageDigest]))

(def namespace-roots
  "The namespaces the namespace walk starts from: recovery, which derives belief on open,
  and the public API, whose write entry points derive it between opens."
  '[vaelii.core vaelii.impl.recovery])

(def roots
  "The definitions the walk over forms starts from: the KB constructor, the two recover
  entry points, and the three `vaelii.impl.wiring` targets."
  '[vaelii.core/open-kb
    vaelii.impl.recovery/recover
    vaelii.impl.recovery/recover-with-image
    vaelii.core/assert
    vaelii.core/retract!
    vaelii.impl.provers/solve-goal])

(defn- in-scope?
  "Is `ns-sym` a namespace the digest follows?"
  [ns-sym]
  (let [s (str ns-sym)]
    (or (= s "vaelii.core") (str/starts-with? s "vaelii.impl."))))

(defn- ns-path ^String [ns-sym]
  (-> (str ns-sym) (str/replace "-" "_") (str/replace "." "/")))

(defn- source-url
  "The classpath URL of `ns-sym`'s source file, or nil when none is on the classpath."
  ^URL [ns-sym]
  (let [p (ns-path ns-sym)]
    (or (io/resource (str p ".clj")) (io/resource (str p ".cljc")))))

(defn- locator
  "The fn from a namespace to the URL of its source file.  With no `source-dirs` this is
  `source-url`.  With `source-dirs`, an in-scope namespace is looked up under those
  directories only, and any other namespace on the classpath."
  [source-dirs]
  (if (empty? source-dirs)
    source-url
    (fn [ns-sym]
      (if-not (in-scope? ns-sym)
        (source-url ns-sym)
        (let [p (ns-path ns-sym)]
          (first (for [d source-dirs ext [".clj" ".cljc"]
                       :let [f (io/file d (str p ext))]
                       :when (.isFile f)]
                   (.toURL (.toURI f)))))))))

;; ---- reading ----------------------------------------------------------------

(def ^:private resolver
  (reify clojure.lang.LispReader$Resolver
    (currentNS [_] 'vaelii.source)
    (resolveClass [_ s] s)
    (resolveAlias [_ s] s)
    (resolveVar [_ s] s)))

(defn read-forms
  "The top-level forms of the source `text`, without `(comment …)` blocks.  Reads with
  `*read-eval*` off and the self-resolving `*reader-resolver*`."
  [^String text]
  (with-open [r (PushbackReader. (StringReader. text))]
    (binding [*read-eval* false
              *reader-resolver* resolver]
      (into []
            (comp (take-while #(not= ::eof %))
                  (remove #(and (seq? %) (= 'comment (first %)))))
            (repeatedly #(read {:eof ::eof :read-cond :allow} r))))))

;; ---- the forms digest -------------------------------------------------------

(def ^:private dropped-meta
  "The reader's position keys, plus `:doc`."
  #{:line :column :end-line :end-column :file :source :doc})

(def ^:private doc-heads
  "The forms whose third element is a docstring when more elements follow it."
  '#{ns defn defn- defmacro defmulti defprotocol definterface defonce})

(defn- strip-doc
  "`form` without its docstring, when `form` is a def-like form that carries one.  A
  `defprotocol` also loses the docstring trailing each method signature."
  [form]
  (if-not (and (seq? form) (symbol? (first form)))
    form
    (let [h (first form)
          v (vec form)
          v (cond
              (and (doc-heads h) (> (count v) 3) (string? (v 2))) (into (subvec v 0 2) (subvec v 3))
              (and (= 'def h) (= 4 (count v)) (string? (v 2)))    [(v 0) (v 1) (v 3)]
              :else                                             v)
          v (if (= 'defprotocol h)
              (mapv (fn [x] (if (and (seq? x) (vector? (second x)) (string? (last x)))
                              (apply list (butlast x))
                              x))
                    v)
              v)]
      (with-meta (apply list v) (meta form)))))

(def ^:private minted
  "A symbol the reader mints per read: a syntax-quote auto-gensym or an anonymous-fn
  argument."
  #"^(.*?)(__\d+__auto__|p\d+__\d+#|rest__\d+#)$")

(defn- renumber
  "`form` with each reader-minted symbol replaced by its order of first appearance.  The
  replacement keeps no part of the minted name: an anonymous-fn argument inside a
  syntax-quote is minted twice (`p1__1235__1236__auto__`), so any prefix of the name can
  still hold a counter."
  [form]
  (let [seen (volatile! {})]
    (walk/postwalk
     (fn [x]
       (if (and (symbol? x) (nil? (namespace x)) (re-matches minted (name x)))
         (or (get @seen x)
             (let [s (symbol (str "minted__" (count @seen)))]
               (vswap! seen assoc x s)
               s))
         x))
     form)))

(defn- canon
  "`form` as plain data: docstrings removed, and each object's metadata, less the keys in
  `dropped-meta`, written out as `[:meta m x]` so the printer includes it."
  [form]
  (walk/postwalk
   (fn [x]
     (let [x (strip-doc x)
           m (when (instance? clojure.lang.IObj x) (apply dissoc (meta x) dropped-meta))]
       (if (seq m) [:meta m (with-meta x nil)] x)))
   (renumber form)))

(defn- sha256 ^MessageDigest [] (MessageDigest/getInstance "SHA-256"))

(defn- hex ^String [^bytes b]
  (let [sb (StringBuilder.)]
    (doseq [x b] (.append sb (format "%02x" (bit-and 0xff (long x)))))
    (str sb)))

(defn- print-canon
  "The printed text of already-canonical `x`."
  ^String [x]
  (binding [*print-meta* false *print-length* nil *print-level* nil
            *print-namespace-maps* false *print-dup* false]
    (pr-str x)))

(defn- text-bytes ^bytes [^String s]
  (.digest (doto (sha256) (.update (.getBytes s "UTF-8")))))

(defn- forms-bytes
  "The digest of already-read `forms`, as bytes."
  ^bytes [forms]
  (text-bytes (print-canon (mapv canon forms))))

(defn forms-digest
  "The hex digest of the source `text` with its comments, docstrings and reader positions
  removed."
  ^String [^String text]
  (hex (forms-bytes (read-forms text))))

;; ---- the ns form ------------------------------------------------------------

(defn- libspecs
  "`[[ns opts] …]` for a `:require` / `:use` libspec: a bare symbol, `[a.b :as x]`, or a
  prefix list `[a b [c :as x]]`.  `opts` is the libspec's keyword options as a map."
  [spec]
  (let [opts (fn [kvs] (into {} (map vec) (partition 2 kvs)))]
    (cond
      (symbol? spec) [[spec {}]]
      (and (sequential? spec) (symbol? (first spec)))
      (let [[head & more] spec]
        (if (or (empty? more) (keyword? (first more)))
          [[head (opts more)]]
          (for [m more
                :let [[s & kvs] (if (sequential? m) m [m])]
                :when (symbol? s)]
            [(symbol (str head "." s)) (opts kvs)])))
      :else [])))

(defn- import-classes
  "The class names an `:import` spec names: `a.b.C`, or `[a.b C D]` / `(a.b C D)`."
  [spec]
  (cond
    (symbol? spec)     [(str spec)]
    (sequential? spec) (let [[pkg & cs] spec] (map #(str pkg "." %) cs))
    :else              []))

(defn- ns-form [forms]
  (first (filter #(and (seq? %) (= 'ns (first %))) forms)))

(defn- ns-clauses [forms]
  (when-let [nsf (ns-form forms)]
    (filter seq? nsf)))

(defn- ns-info
  "What `forms`' `ns` form says about resolving a symbol: `{:name ns :aliases {alias ns}
  :refers {sym ns} :refer-all [ns …] :imports {ShortName \"full.ClassName\"}}`."
  [forms]
  (let [clauses (ns-clauses forms)
        specs   (for [c clauses :when (#{:require :use} (first c))
                      spec (rest c) [n o] (libspecs spec)]
                  [(first c) n o])]
    {:name      (let [n (second (ns-form forms))] (when (symbol? n) n))
     :aliases   (into {} (for [[_ n o] specs a [(:as o) (:as-alias o)] :when (symbol? a)] [a n]))
     :refers    (into {} (for [[k n o] specs
                               s (cond (sequential? (:refer o)) (:refer o)
                                       (and (= :use k) (sequential? (:only o))) (:only o))]
                           [s n]))
     :refer-all (vec (for [[k n o] specs
                           :when (or (= :all (:refer o)) (and (= :use k) (nil? (:only o))))]
                       n))
     :imports   (into {} (for [c clauses :when (= :import (first c))
                               spec (rest c) cls (import-classes spec)]
                           [(symbol (subs cls (inc (.lastIndexOf ^String cls ".")))) cls]))}))

;; ---- the top-level forms ----------------------------------------------------

(def ^:private var-heads
  "The `clojure.core` heads whose form defines exactly the var its second element names."
  '#{def defn defn- defmacro defonce defmulti definline})

(def ^:private extension-heads
  "The heads whose form attaches protocol methods to a type defined elsewhere."
  '#{extend-type extend-protocol extend})

(defn- bare
  "`x` as a symbol without namespace or metadata, or nil when `x` is not a symbol."
  [x]
  (when (symbol? x) (symbol (name x))))

(defn- class-name
  "The JVM class name of the type `t` that namespace `ns-sym` defines."
  [ns-sym t]
  (str (str/replace (str ns-sym) "-" "_") "." t))

(defn- spec-symbols
  "The symbols at the top level of a type's or an extension's `specs`: the protocols and
  interfaces it names, skipping each keyword option's value."
  [specs]
  (loop [out [] [x & more :as xs] specs]
    (cond
      (empty? xs)  out
      (keyword? x) (recur out (rest more))
      (symbol? x)  (recur (conj out x) more)
      :else        (recur out more))))

(defn- classify
  "What the top-level `form` of namespace `ns-sym` defines, and when the walk includes it:

  - `:var`, `:protocol`, `:type` — `:names` the vars the form defines, reached through them;
    a `:type` also through its `:classes`, and it names the `:protocols` it implements;
  - `:interface` — reached through its `:classes`;
  - `:record` — included always, `:names` and `:classes` as a `:type`;
  - `:method`, `:fdef` — attached to the var its `:target` symbol resolves to;
  - `:extension` — attached to each protocol its `:protocols` symbols resolve to;
  - `:other` — included always; `:names` the var a `def…` macro's second element names;
  - `:skip` — an `ns` or `declare` form, which the digest leaves out."
  [ns-sym form]
  (let [h      (when (seq? form) (first form))
        core?  (and (symbol? h) (contains? #{nil "clojure.core"} (namespace h)))
        hn     (when core? (name h))
        hsym   (when hn (symbol hn))
        [_ n & more] (when (seq? form) form)]
    (cond
      (#{'ns 'declare} hsym)
      {:kind :skip}

      (and (var-heads hsym) (symbol? n))
      {:kind :var :names [(bare n)]}

      (and (= 'defprotocol hsym) (symbol? n))
      {:kind :protocol :names (into [(bare n)] (keep #(when (seq? %) (bare (first %)))) more)}

      (and (#{'deftype 'defrecord} hsym) (symbol? n))
      (let [t (bare n)]
        {:kind      (if (= 'defrecord hsym) :record :type)
         :names     (cond-> [(symbol (str "->" t))]
                      (= 'defrecord hsym) (conj (symbol (str "map->" t))))
         :classes   [(class-name ns-sym t)]
         :protocols (spec-symbols (rest more))})

      (and (= 'definterface hsym) (symbol? n))
      {:kind :interface :classes [(class-name ns-sym (bare n))]}

      (and (= 'defmethod hsym) (symbol? n))
      {:kind :method :target n :key (str "defmethod " n " " (print-canon (canon (first more))))}

      (and (symbol? h) (= "fdef" (name h)) (symbol? n))
      {:kind :fdef :target n :key (str "fdef " n)}

      (and (symbol? h) (extension-heads (bare h)))
      {:kind      :extension
       :key       (str (name h) " " (print-canon (canon n)))
       :protocols (case (name h)
                    "extend-protocol" [n]
                    "extend"          (vec (take-nth 2 (filter symbol? more)))
                    (spec-symbols more))}

      :else
      {:kind  :other
       :names (when (and (symbol? h) (str/starts-with? (name h) "def") (symbol? n)) [(bare n)])})))

(defn- form-symbols
  "Every symbol in the canonical `form`, its metadata included."
  [form]
  (into #{} (filter symbol?) (tree-seq coll? seq form)))

(defn- parse-forms
  "The parse the memo holds for a file's `forms`: `:info` (`ns-info`), `:edges`, the file's
  whole-file `:bytes`, and `:forms`, one entry per top-level form that `classify` keeps,
  each carrying its `:bytes` and `:symbols`."
  [forms]
  (let [info (ns-info forms)
        ns   (:name info)
        top  (volatile! -1)]
    {:info  info
     :bytes (forms-bytes forms)
     :forms (into []
                  (keep (fn [form]
                          (let [c (classify ns form)]
                            (when-not (= :skip (:kind c))
                              (let [cf (canon form)]
                                (cond-> (assoc c
                                               :bytes   (text-bytes (print-canon cf))
                                               :symbols (form-symbols cf))
                                  ;; A form defining no var is keyed by its place among
                                  ;; the file's others, so reordering two changes the digest.
                                  (and (= :other (:kind c)) (empty? (:names c)))
                                  (assoc :key (str "top-level " (vswap! top inc)))))))))
                  forms)}))

;; ---- the namespace walk -----------------------------------------------------

(defn- quoted-namespaces
  "The in-scope namespaces named by a fully-qualified symbol under a `quote` in `forms`."
  [forms]
  (let [acc (volatile! #{})]
    (walk/postwalk
     (fn [x]
       (when (and (seq? x) (= 'quote (first x)))
         (walk/postwalk
          (fn [y]
            (when (and (symbol? y) (namespace y) (in-scope? (symbol (namespace y))))
              (vswap! acc conj (symbol (namespace y))))
            y)
          (second x)))
       x)
     forms)
    @acc))

(defn- edges
  "`{:reqs [ns …] :classes [cls …] :quoted #{ns …}}` — the namespaces `forms` requires,
  the classes it imports, and the in-scope namespaces a quoted symbol in it names.  Read
  from the forms alone, with no classpath lookup, so the parse memo can hold it."
  [forms]
  (let [clauses (ns-clauses forms)]
    {:reqs    (vec (for [c clauses :when (#{:require :use} (first c))
                         spec (rest c) [n] (libspecs spec)] n))
     :classes (vec (for [c clauses :when (= :import (first c))
                         spec (rest c) cls (import-classes spec)] cls))
     :quoted  (quoted-namespaces forms)}))

(defn- class-namespace
  "The in-scope namespace that defines class `cls`, when one does: a deftype or defrecord
  class lives in the munged package of its namespace."
  [loc ^String cls]
  (let [i (.lastIndexOf cls ".")]
    (when (pos? i)
      (let [n (symbol (str/replace (subs cls 0 i) "_" "-"))]
        (when (and (in-scope? n) (loc n)) n)))))

(defn- references
  "`{:namespaces #{…} :libraries #{…}}` — the in-scope namespaces a file's `edges` reach
  and the external namespaces and classes it requires or imports.  Resolves each imported
  class through `loc` at the call."
  [loc {:keys [reqs classes quoted]}]
  (let [by-cls (map (fn [c] [c (class-namespace loc c)]) classes)]
    {:namespaces (into quoted
                       (concat (filter in-scope? reqs) (keep second by-cls)))
     :libraries  (into #{}
                       (concat (map (fn [n] [:ns n]) (remove in-scope? reqs))
                               (keep (fn [[c n]] (when-not n [:class c])) by-cls)))}))

(defn- container-bytes
  "The digest of the compiled code class `url` loads from.  A namespace compiles to one
  class per fn beside its `__init` class, so no single class file covers its code: for a
  jar URL this is the whole jar, and for a directory URL every class file of namespace
  `stem` (`stem__init.class`, `stem$….class`) in name order."
  ^bytes [^URL url ^String stem]
  (let [md (sha256)]
    (case (.getProtocol url)
      "jar"  (let [p (.getPath url)
                   f (io/file (.toURI (URL. (subs p 0 (.indexOf p "!")))))]
               (.update md (Files/readAllBytes (.toPath f))))
      "file" (let [d (.getParentFile (io/file (.toURI url)))]
               (doseq [^File f (sort-by #(.getName ^File %) (.listFiles d))
                       :let [nm (.getName f)]
                       :when (or (= nm (str stem "__init.class"))
                                 (str/starts-with? nm (str stem "$")))]
                 (.update md (.getBytes nm "UTF-8"))
                 (.update md (Files/readAllBytes (.toPath f))))))
    (.digest md)))

(defn- compiled-bytes
  "For a namespace with no source on the classpath, the digest of the compiled code it
  loads from, or nil when no compiled class names it either.  `cache` is a volatile map
  shared across one walk, so a closure of namespaces from one jar reads the jar once."
  [ns-sym cache]
  (let [p (ns-path ns-sym)]
    (when-let [^URL u (io/resource (str p "__init.class"))]
      (let [stem (subs p (inc (.lastIndexOf p "/")))
            k    (if (= "jar" (.getProtocol u))
                   (let [path (.getPath u)] (subs path 0 (.indexOf path "!")))
                   (str u))]
        (or (get @cache k)
            (let [b (container-bytes u stem)] (vswap! cache assoc k b) b))))))

;; ---- the parse memo ---------------------------------------------------------

(def ^:private parse-memo-limit
  "Parsed files the memo holds before it is cleared wholesale.  The namespace set is 123
  namespaces today, so the bound leaves room for the versions a REPL session's edits add."
  1024)

(def ^:private stat-window-ms
  "How long after a file's modification time a read must happen for the file's stat to
  stand in for its bytes at the next call.  A file system records a modification time at a
  resolution of up to 2 s, so an edit landing within 2 s of the read before it can leave
  both the time and the length unchanged."
  2000)

;; `{url-string {:stat [modified length] :read-at ms :sha hex :bytes forms-digest
;; :edges edges :info ns-info :forms [form …]}}`, one entry per source file.
(defonce ^{:private true}
  parsed
  (atom {}))

(defn- url-bytes ^bytes [^URL url]
  (with-open [in (.openStream url)] (.readAllBytes in)))

(defn- file-stat
  "`[modified-ms length]` of the file `url` loads from — the jar itself for a `jar:` URL —
  or nil for any other protocol."
  [^URL url]
  (when-let [^File f (case (.getProtocol url)
                       "file" (io/file (.toURI url))
                       "jar"  (let [p (.getPath url)]
                                (io/file (.toURI (URL. (subs p 0 (.indexOf p "!"))))))
                       nil)]
    [(.lastModified f) (.length f)]))

(defn- parse-source
  "The parse of the source file at `url`: `parse-forms`' map plus its `:edges` and `:sha`.

  The memo entry stands without a read when the file's stat equals the stat taken before
  the entry's read, and the file's modification time is more than `stat-window-ms` older
  than that read.  Otherwise this reads the bytes and hashes them, and parses the forms
  only when the SHA-256 differs from the entry's."
  [^URL url]
  (let [k  (str url)
        st (file-stat url)
        e  (get @parsed k)]
    (if (and e st (= st (:stat e))
             (< (long (first st)) (- (long (:read-at e)) (long stat-window-ms))))
      e
      (let [read-at (System/currentTimeMillis)
            raw     (url-bytes url)
            sha     (hex (.digest (doto (sha256) (.update raw))))
            e       (assoc (if (= sha (:sha e))
                             e
                             (let [forms (read-forms (String. raw "UTF-8"))]
                               (assoc (parse-forms forms) :sha sha :edges (edges forms))))
                           :stat st :read-at read-at)]
        (when (and (not (contains? @parsed k))
                   (>= (count @parsed) (long (caches/limit-of :source-parses parse-memo-limit))))
          (reset! parsed {}))
        (swap! parsed assoc k e)
        e))))

(caches/register-cache
 {:cache    :source-parses
  :label    "Source parses"
  :scope    :process
  :unit     "source files"
  :limit    (caches/limit-thunk :source-parses parse-memo-limit)
  :counters nil
  :note     (str "Each engine source file's classified and hashed top-level forms and its "
                 "edges, keyed on the SHA-256 of its bytes, so the source identity parses "
                 "only a file whose bytes it has not parsed before. Past the limit it is "
                 "cleared wholesale.")
  :read     (fn [_] {:entries (count @parsed)})
  :trim     (fn [_ target] (caches/trim-map! parsed target))})

;; ---- the walk over namespaces -----------------------------------------------

(defn- walk-closure
  "`{ns-sym {:parse p :libraries #{…}}}` for every namespace the namespace walk reaches.  A
  namespace with source carries its parse (`parse-source`); one with only compiled code
  carries `:compiled`, its `compiled-bytes`, and no edges, since the jar's digest already
  covers every namespace compiled into it."
  [loc namespace-roots]
  (let [cache (volatile! {})]
    (loop [out {} todo (vec namespace-roots)]
      (if-let [n (peek todo)]
        (let [todo (pop todo)]
          (cond
            (contains? out n)
            (recur out todo)

            (loc n)
            (let [p (parse-source (loc n))
                  {:keys [namespaces libraries]} (references loc (:edges p))]
              (recur (assoc out n {:parse p :libraries libraries})
                     (into todo (remove #(contains? out %)) namespaces)))

            :else
            (recur (if-let [b (compiled-bytes n cache)]
                     (assoc out n {:compiled b :libraries #{}})
                     out)
                   todo)))
        out))))

;; ---- the walk over definitions ----------------------------------------------

(defn- index-forms
  "Every top-level form of the namespaces in `c` (`walk-closure`'s map), as `:forms`, a
  vector of form entries each carrying its `:ns` and `:info`, plus the lookups the walk
  reads:

  - `:defs` `{ns {name [id …]}}` and `:classes` `{class-name [id …]}`, the forms a
    resolved symbol reaches;
  - `:attached` `{id [id …]}`, the forms included once form `id` is reached;
  - `:always`, the forms included whether or not anything reaches them."
  [c]
  (let [forms (vec (for [[n {:keys [parse]}] (sort-by key c)
                         :when parse
                         f (:forms parse)]
                     (assoc f :ns n :info (:info parse))))
        ids   (range (count forms))
        defs  (reduce (fn [m i] (let [{:keys [ns names]} (forms i)]
                                  (reduce #(update-in %1 [ns %2] (fnil conj []) i) m names)))
                      {} ids)
        clss  (reduce (fn [m i] (reduce #(update %1 %2 (fnil conj []) i) m (:classes (forms i))))
                      {} ids)]
    {:forms forms :defs defs :classes clss}))

(defn- resolve-symbol
  "The ids of the forms symbol `s`, read in the namespace `info` describes, reaches."
  [{:keys [defs classes]} info s]
  (let [nm      (name s)
        ;; a short class name is an import, or a type the namespace itself defines
        cls     (fn [c] (or (get classes (or (get (:imports info) (symbol c)) c))
                            (when-not (str/includes? c ".")
                              (get classes (class-name (:name info) c)))))
        nsp     (namespace s)]
    (if nsp
      (let [a (symbol nsp)
            t (or (get (:aliases info) a) (when (contains? defs a) a))]
        (concat (when t (get-in defs [t (symbol nm)])) (cls nsp)))
      (if (and (str/ends-with? nm ".") (< 1 (count nm)))
        (cls (subs nm 0 (dec (count nm))))
        (concat (get-in defs [(:name info) s])
                (when-let [r (get (:refers info) s)] (get-in defs [r s]))
                (mapcat #(get-in defs [% s]) (:refer-all info))
                (cls nm))))))

(defn- attachments
  "`[attached always]` for the indexed forms `ix`: `attached` maps a form's id to the forms
  it brings in when reached, and `always` holds the forms `classify` includes unconditionally
  plus each method, fdef or extension whose target is outside the namespace set."
  [{:keys [forms] :as ix}]
  (let [protocol? #(= :protocol (:kind (forms %)))]
    (reduce
     (fn [[att alw] i]
       (let [{:keys [kind info target protocols]} (forms i)
             attach (fn [targets]
                      (if (seq targets)
                        [(reduce #(update %1 %2 (fnil conj []) i) att targets) alw]
                        [att (conj alw i)]))]
         (case kind
           (:record :other)  [att (conj alw i)]
           (:method :fdef)   (attach (resolve-symbol ix info target))
           :extension        (let [ps (map #(filter protocol? (resolve-symbol ix info %)) protocols)]
                               (if (every? seq ps)
                                 (attach (distinct (apply concat ps)))
                                 [att (conj alw i)]))
           :type             [(reduce #(update %1 %2 (fnil conj []) i) att
                                      (distinct (mapcat #(filter protocol? (resolve-symbol ix info %))
                                                        protocols)))
                              alw]
           [att alw])))
     [{} []]
     (range (count forms)))))

(defn- reached
  "The ids of the forms of `ix` the walk reaches from `root-syms`.  Throws when a root
  names no form, since a digest walked from a missing root covers less than recover runs."
  [ix root-syms]
  (let [[att alw] (attachments ix)
        forms     (:forms ix)
        start     (for [r root-syms
                        :let [ids (get-in (:defs ix) [(symbol (namespace r)) (symbol (name r))])]]
                    (if (seq ids)
                      ids
                      (throw (IllegalStateException.
                              (str "source identity root " r " names no definition")))))]
    (loop [seen #{} todo (into (vec alw) cat start)]
      (if-let [i (peek todo)]
        (let [todo (pop todo)]
          (if (contains? seen i)
            (recur seen todo)
            (let [{:keys [info symbols]} (forms i)]
              (recur (conj seen i)
                     (-> todo
                         (into (comp (mapcat #(resolve-symbol ix info %)) (remove seen)) symbols)
                         (into (remove seen) (get att i)))))))
        seen))))

(defn- form-key
  "The name the digest takes form `f` under: its namespace and the var it defines, or for a
  form defining no var, its kind and target."
  [f]
  (str (:ns f) "/" (or (:key f) (first (:names f)) (first (:classes f)))))

;; ---- libraries --------------------------------------------------------------

(defn- library-url ^URL [[kind nm]]
  (case kind
    :ns    (let [p (ns-path nm)]
             (or (io/resource (str p ".clj")) (io/resource (str p "__init.class"))
                 (io/resource (str p ".cljc"))))
    :class (io/resource (str (str/replace nm "." "/") ".class"))))

(defn- library-name
  "The jar file name `lib` loads from, its own name when it loads from a directory, or nil
  for a JDK class and for a name nothing on the classpath provides."
  [[_ nm :as lib]]
  (when-let [u (library-url lib)]
    (case (.getProtocol u)
      "jar"  (let [p (.getPath u) bang (.indexOf p "!")]
               (subs p (inc (.lastIndexOf p "/" (int bang))) bang))
      "file" (str nm)
      nil)))

;; ---- the identity -----------------------------------------------------------

(defn- compute
  "The identity of the namespaces `c` (`walk-closure`'s map), walked from `root-syms`."
  [c root-syms]
  (let [ix      (index-forms c)
        entries (sort (for [i (reached ix root-syms)
                            :let [f ((:forms ix) i)]]
                        [(form-key f) (hex (:bytes f))]))
        libs    (into (sorted-set) (keep library-name) (mapcat :libraries (vals c)))
        md      (sha256)]
    (doseq [[k h] entries]
      (.update md (.getBytes (str k " " h "\n") "UTF-8")))
    (doseq [[n {:keys [compiled]}] (sort-by key c) :when compiled]
      (.update md (.getBytes (str n) "UTF-8"))
      (.update md ^bytes compiled))
    (doseq [l libs]
      (.update md (.getBytes (str l) "UTF-8")))
    {:digest      (hex (.digest md))
     :namespaces  (count c)
     :definitions (mapv first entries)
     :libraries   (vec libs)}))

;; The last identity computed, `{:key [opts shas] :value identity}`: the walk over the
;; definitions reruns only when a file's SHA-256 moved since.
(defonce ^{:private true}
  last-identity
  (atom nil))

(defn- identity-of
  [{:keys [source-dirs] :as opts}]
  (let [c   (walk-closure (locator source-dirs) (:namespace-roots opts namespace-roots))
        k   [(select-keys opts [:source-dirs :roots :namespace-roots])
             (into (sorted-map) (map (fn [[n e]] [n (or (:sha (:parse e)) (hex (:compiled e)))])) c)]
        hit @last-identity]
    (if (= k (:key hit))
      (:value hit)
      (let [v (compute c (:roots opts roots))]
        (reset! last-identity {:key k :value v})
        v))))

(defn closure
  "The sorted set of namespaces whose forms the walk over definitions reads.  `opts` as
  `source-identity` takes."
  ([] (closure {}))
  ([opts]
   (into (sorted-set) (keys (walk-closure (locator (:source-dirs opts))
                                          (:namespace-roots opts namespace-roots))))))

(defn definitions
  "The sorted set of the names the digest takes each reached form under: `ns/var` for a
  form defining a var, `ns/<kind> <target>` for one that defines none.  `opts` as
  `source-identity` takes."
  ([] (definitions {}))
  ([opts] (into (sorted-set) (:definitions (identity-of opts)))))

(defn source-identity
  "`{:digest hex :namespaces n :definitions [name …] :libraries [jar …]}` for the source on
  the classpath now.  `:digest` covers every form the walk reaches from `roots`, each under
  its name, the compiled code of any namespace in `closure` with no source, and the sorted
  library names.

  `opts`, for a test or a replay of another commit's source: `:source-dirs`, directories
  searched for an in-scope namespace's source in place of the classpath; `:roots` and
  `:namespace-roots`, in place of the two vars of those names."
  ([] (source-identity {}))
  ([opts]
   (let [v (identity-of opts)]
     (assoc v :definitions (count (:definitions v))))))
