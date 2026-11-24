;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.run
  "A **run file** (`.vae`): KB forms in the text KB format, plus directives written as EDN
  tags.  `#base` names the KB a run starts from, `#context` the context the forms after it
  assert into, `#solve` the options the solve reads after it run under, and `#include`
  another run file or a text KB.  The rest are the reads a run answers once every form is
  stored.  `read-run-file` reads one into the entries
  `text/load-entries!` takes and the reads in file order.  See docs/operations.md."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.starter :as starter]
            [vaelii.impl.asp.solve-context :as solve-context]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx])
  (:import [java.io File]))

(def directives
  "Every directive a run file may hold, with the argument it takes: `:base` one of
  `base-names`, `:context` a context name, `:path` a string, `:pattern` a list,
  `:sentence` a list holding no variable, and `:options` a map of `answer-sets` options."
  '{base :base, context :context, include :path, show :pattern, truth :sentence,
    models :pattern, model :pattern, brave :pattern, cautious :pattern, solve :options})

(def ^:private solve-readings
  '{models :all, model :one, brave :brave, cautious :cautious})

(def ^:private solve-keys
  "The options a `#solve` map may hold: every solve read's (`solve-context`)."
  (into solve-context/search-options cat (vals solve-context/answer-set-readings)))

(defn- options-problem
  "Why the `#solve` map `m` is refused, or nil: `answer-sets`' option check over
  `solve-keys`, with `:project` holding `true` (each read's own pattern) or a pattern."
  [m]
  (try (solve-context/check-options! (cond-> m (true? (:project m)) (dissoc :project)) solve-keys)
       nil
       (catch clojure.lang.ExceptionInfo e (ex-message e))))

(def base-names
  "The KBs `#base` may name: `core` holds `kb/upper/core.txt` and `interface-rules.txt`,
  `upper` every `kb/upper/` file, and `starter` the upper and middle layers."
  '#{core upper starter})

(def default-base
  "The base a run starts from when no file names one."
  'core)

(def default-context
  "The context a form asserts into before any `#context` names another."
  'CxMain)

(defn- check-arg!
  "Refuse a directive whose argument is not the kind `directives` gives it (`:bad-value`)."
  [directive arg {:keys [file line]}]
  (let [kind    (directives directive)
        problem (when (= :options kind) (options-problem arg))
        ok?  (case kind
               :options  (nil? problem)
               :base    (contains? base-names arg)
               :context (and (nm/context? arg) (not (nm/query-context? arg)))
               :path    (and (string? arg) (not (str/blank? arg)))
               :pattern  (and (seq? arg) (seq arg))
               :sentence (and (seq? arg) (seq arg) (sx/ground-term? arg)))]
    (when-not ok?
      (throw (ex-info (str file ", line " line ": #" directive " takes "
                           (case kind
                             :base    (str "one of " (str/join ", " (sort base-names)))
                             :context "a context name that is not a query context"
                             :path    "a path string"
                             :pattern  "a sentence or pattern"
                             :sentence "a sentence holding no variable"
                             :options  (str "a map of answer-sets options: " problem))
                           ", given " (pr-str arg))
                      {:type :bad-directive :mismatch :bad-value :directive directive :arg arg
                       :file file :line line})))))

(defn- included
  "The file an `#include` of `path` in `from` names: `path` itself when absolute, and
  otherwise `path` read against `from`'s directory."
  ^File [^File from path]
  (let [f (io/file path)]
    (if (.isAbsolute f) f (io/file (.getParentFile (.getAbsoluteFile from)) path))))

(defn- text-kb?
  "Does `f` name a text KB rather than a run file: a directory, or a `.txt` file?"
  [^File f]
  (or (.isDirectory f) (str/ends-with? (.getName f) ".txt")))

(defn- read-into
  "`acc` with the run file `f` read into it.  `scope` holds the `:context` its forms assert
  into and the `:solve` options its solve reads run under, until a `#context` or `#solve`
  names others.  `stack` holds the canonical paths of `f` and the files including it.  A
  directive's scope ends with its own file, so an included file leaves the scope of the
  file including it as it was."
  [acc ^File f scope stack]
  (when-not (.isFile f)
    (throw (ex-info (str "no run file at " (.getPath f))
                    {:type :missing-resource :path (.getPath f)})))
  (let [file (.getPath f)
        step (fn [{:keys [acc scope]} {:keys [form directive arg start]}]
               (let [at   {:file file :line start}
                     same (fn [acc] {:acc acc :scope scope})]
                 (when directive (check-arg! directive arg at))
                 (case directive
                   nil     (same (update acc :entries conj (with-meta [form (:context scope)] at)))
                   context {:acc acc :scope (assoc scope :context arg)}
                   solve   {:acc acc :scope (assoc scope :solve arg)}
                   base    (if (and (:base acc) (not= arg (:base acc)))
                             (throw (ex-info (str file ", line " start ": #base " arg " after #base "
                                                  (:base acc) " — a run starts from one base")
                                             {:type :bad-directive :mismatch :conflict :directive 'base
                                              :arg arg :base (:base acc) :file file :line start}))
                             (same (assoc acc :base arg)))
                   include (let [g  (included f arg)
                                 gp (.getCanonicalPath g)]
                             (when (some #{gp} stack)
                               (throw (ex-info (str file ", line " start ": #include " (pr-str arg)
                                                    " names a file already being read: "
                                                    (str/join " → " (conj stack gp)))
                                               {:type :bad-directive :mismatch :cycle :directive 'include
                                                :stack (conj stack gp) :file file :line start})))
                             (same (if (text-kb? g)
                                     (let [{:keys [files entries]} (text/entries g)]
                                       (-> acc (update :entries into entries) (update :files into files)))
                                     (read-into acc g scope (conj stack gp)))))
                   (same (update acc :reads conj
                                 (cond-> (assoc at :directive directive :arg arg :context (:context scope))
                                   (and (solve-readings directive) (seq (:solve scope)))
                                   (assoc :solve (:solve scope))))))))]
    (:acc (reduce step
                  {:acc (update acc :files conj file) :scope scope}
                  (text/form-spans f {:directives (set (keys directives))})))))

(defn read-run-file
  "Read the run file at `path` and every file it includes, as
  `{:base b :entries [[form context] …] :reads [{:directive d :arg p :context c :file f
  :line n} …] :files [path …]}`.  `:base` is nil when no file names one, and a solve read
  under a non-empty `#solve` map holds it as `:solve`.  An entry read
  from a run file carries `{:file :line}` as metadata.  Refusals: `:bad-directive`, its
  `:mismatch` one of `:unknown-key`, `:misplaced`, `:bad-value`, `:conflict` (two bases)
  and `:cycle` (an include of a file already being read); `:missing-resource`; `:unreadable`."
  [path]
  (let [f (io/file path)]
    (read-into {:base nil :entries [] :reads [] :files []} f {:context default-context}
               [(.getCanonicalPath f)])))

(defn- base-loader
  "The fn asserting `base` into a KB."
  [base]
  (case base
    core    #(core-context/load-into % ["core.txt" "interface-rules.txt"])
    upper   core-context/load-into
    starter starter/load-into))

(defn base-kb
  "A new in-RAM KB holding `base`, one of `base-names`: restored from the export dump under
  `<root>/<base>` when one matches this engine and its shipped files, and otherwise loaded
  and then dumped there (`starter/load-through-dump`).  `root` defaults to
  `<java.io.tmpdir>/vaelii-run-dump`."
  ([base] (base-kb base (io/file (System/getProperty "java.io.tmpdir") "vaelii-run-dump")))
  ([base root]
   (starter/load-through-dump #(v/open-kb {:backend :memory :space (mem/engine-space :run)})
                              (io/file root (name base))
                              (base-loader base))))

(def ^:private complete-statuses
  "The `:status`es of a read answered in full: `query-status`'s `:complete`, and a solve's
  `:optimum`, `:sat` and `:unsat`."
  #{:complete :optimum :sat :unsat})

(defn stopped-short?
  "Did `read`, answered by `run-in`, stop short of its whole answer?"
  [{:keys [status]}]
  (boolean (and status (not (complete-statuses status)))))

(defn- solve-options
  "The `answer-sets` options of solve read `read`: the reading its directive names, and
  the options of its `#solve` map that reading reads, a `:project` of `true` naming the
  read's own pattern."
  [{:keys [directive arg solve]}]
  (let [reading (solve-readings directive)
        ks      (into solve-context/search-options (solve-context/answer-set-readings reading))]
    (cond-> (assoc (select-keys solve ks) :reading reading)
      (true? (:project solve)) (assoc :project arg)
      (not (ks :project))      (dissoc :project))))

(defn- answer
  "`read` with its answer at rule depth `depth`, `solve` answering `[context opts]` as
  `v/answer-sets` does.  A `#show` read gains `:answers`, its pattern's instances, and
  `:status`, `query-status`'s; a `#truth` read gains `:verdict`, `argue`'s.  A `#models` or
  `#model` read gains `:answer-sets`, each the instances of its pattern in one answer set,
  and `:answer-set-costs`.  A `#brave` or `#cautious` read gains `:answers`.  Each gains the
  solve's `:status` and `:costs`, and lists instances and answer sets in content order."
  [kb depth solve {:keys [directive arg context] :as read}]
  (let [instances (fn [atoms] (nm/by-print-key (filter #(res/unify arg % {}) atoms)))]
    (case directive
      show     (let [{:keys [answers status]} (v/query-status kb arg context {:max-depth depth})]
                 (assoc read
                        :answers (nm/by-print-key (distinct (map #(res/substitute arg %) answers)))
                        :status status))
      truth    (assoc read :verdict (:verdict (v/argue kb arg context {:max-depth depth})))
      (models model)
      (let [r     (solve context (solve-options read))
            pairs (nm/by-print-key (map vector (map instances (:answer-sets r))
                                        (concat (:answer-set-costs r) (repeat nil))))]
        (assoc read :status (:status r) :costs (:costs r)
               :answer-sets (mapv first pairs) :answer-set-costs (mapv second pairs)))
      (brave cautious)
      (let [r (solve context (solve-options read))]
        (assoc read :status (:status r) :costs (:costs r)
               :answers (instances (:consequences r)))))))

(defn run-in
  "Assert the entries of `program` (`read-run-file`'s map) into `kb` as `load-text!` does,
  then answer its reads at rule depth `depth`, solving each context's program once per
  reading and option map.  Returns `{:answers [read …]}`, each read
  with its answer (`answer`), or, when an entry is refused, `{:refused [{:file :line :form
  :context :error} …]}` and no answers."
  [kb {:keys [entries reads]} depth]
  (let [refused (volatile! [])]
    (text/load-entries! (fn [sentence context o] (v/assert kb sentence context (or o {})))
                        (fn [sentence context] (v/assert-inert kb sentence context))
                        entries
                        (fn [[form context :as entry] e]
                          (vswap! refused conj
                                  (assoc (meta entry) :form form :context context :error e)))
                        (text/digest-check kb))
    (if (seq @refused)
      {:refused @refused}
      (let [solve (memoize #(v/answer-sets kb %1 %2))]
        {:answers (mapv #(answer kb depth solve %) reads)}))))
