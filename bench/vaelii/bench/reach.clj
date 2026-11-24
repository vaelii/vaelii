;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.reach
  "The engine code each `vaelii.bench.perf` check and `vaelii.bench.ab` probe executes,
  read off the JaCoCo agent `lein perf --reach` attaches (scripts/perf.sh), for
  `scripts/perf-owed.py` to select the checks and probes a change reaches.  A check runs at
  both its sizes and a probe once, the agent's probe arrays reset before each.  `<out>`
  maps each fn to its targets, and `<out>` with `-lines` before `.tsv` each line of src/.

  Run: `lein with-profile +bench,+reach run -m vaelii.bench.reach <out> <rev> <dirty> [a,b]`,
  the last argument naming the only targets to run."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.bench.ab :as ab]
            [vaelii.bench.perf :as perf]
            [vaelii.core :as v])
  (:import [java.io ByteArrayInputStream File]
           [java.lang.reflect Method]
           [java.nio.file Files]
           [java.util ArrayList BitSet List]
           [org.jacoco.core.analysis IClassCoverage]
           [org.jacoco.core.data ExecutionData ExecutionDataReader ExecutionDataStore
            SessionInfoStore]
           [org.jacoco.core.internal.analysis ClassAnalyzer ClassCoverageImpl StringPool]
           [org.jacoco.core.internal.flow ClassProbesAdapter IFrame MethodProbesVisitor]
           [org.objectweb.asm ClassReader Label MethodVisitor]
           [org.objectweb.asm.tree MethodNode]))

(def ^:private no-classes (make-array Class 0))

(def ^:private dump-dir
  "Where the agent writes each class it instruments, as loaded (project.clj's `:reach`)."
  "target/reach-classes")

(defn- agent-calls
  "`[clear drain]` over the attached agent's `IAgent`: `clear` zeroes every probe array,
  and `drain` returns the execution data since the last clear and zeroes it.  The agent's
  classes exist only in a JVM it is attached to, so they are reached by reflection."
  []
  (let [iagent  (Class/forName "org.jacoco.agent.rt.IAgent")
        rt      (Class/forName "org.jacoco.agent.rt.RT")
        agent   (.invoke (.getMethod rt "getAgent" ^"[Ljava.lang.Class;" no-classes)
                         nil (object-array 0))
        reset   (.getMethod iagent "reset" ^"[Ljava.lang.Class;" no-classes)
        drain   (.getMethod iagent "getExecutionData"
                            ^"[Ljava.lang.Class;" (into-array Class [Boolean/TYPE]))]
    [#(.invoke ^Method reset agent (object-array 0))
     #(.invoke ^Method drain agent (object-array [true]))]))

(defn- executed
  "The classes JaCoCo execution data `bs` holds a probe set in, each an `ExecutionData`."
  [^bytes bs]
  (let [store (ExecutionDataStore.)
        in    (ExecutionDataReader. (ByteArrayInputStream. bs))]
    (.setExecutionDataVisitor in store)
    (.setSessionInfoVisitor in (SessionInfoStore.))
    (.read in)
    (filter #(.hasHits ^ExecutionData %) (.getContents store))))

(defn- class-key
  "The key of class `cname`: `ns/var` for a top-level fn and every fn nested in it, and
  `ns/Type` for a record or type.  An anonymous top-level fn (a `defmethod`, a protocol
  extension) keys as `ns`, and a namespace's loader class as nil."
  [cname]
  (let [[outer inner] (str/split (str/replace cname \/ \.) #"\$" 3)
        ns-name       #(str/replace % \_ \-)]
    (cond
      (str/ends-with? outer "__init")             nil
      (nil? inner)                                (let [i (str/last-index-of outer \.)]
                                                    (str (ns-name (subs outer 0 i)) "/"
                                                         (subs outer (inc i))))
      (re-find #"__\d+$|^eval\d+$|^fn$" inner)    (ns-name outer)
      :else (str (ns-name outer) "/" (clojure.lang.Compiler/demunge inner)))))

(defn- marking
  "Wraps JaCoCo's method analyzer `inner` so that each label starts a numbered line of its
  own, and each line entry one numbered for its source line; `syn` collects the source line
  per number (0 at a label).  A JaCoCo line then holds one straight run of instructions,
  where a source line also holds the call target loaded ahead of its entry and the join
  after a branch."
  [^MethodProbesVisitor inner ^List syn]
  (let [mark (fn [line ^Label l] (.add syn (int line)) (.visitLineNumber inner (.size syn) l))]
    (proxy [MethodProbesVisitor] [inner]
      (visitProbe [id] (.visitProbe inner (int id)))
      (visitJumpInsnWithProbe [op l id frame]
        (.visitJumpInsnWithProbe inner (int op) ^Label l (int id) ^IFrame frame))
      (visitInsnWithProbe [op id] (.visitInsnWithProbe inner (int op) (int id)))
      (visitTableSwitchInsnWithProbes [lo hi dflt ls frame]
        (.visitTableSwitchInsnWithProbes inner (int lo) (int hi) ^Label dflt
                                         ^"[Lorg.objectweb.asm.Label;" ls ^IFrame frame))
      (visitLookupSwitchInsnWithProbes [dflt ks ls frame]
        (.visitLookupSwitchInsnWithProbes inner ^Label dflt ^ints ks
                                          ^"[Lorg.objectweb.asm.Label;" ls ^IFrame frame))
      (accept [node mv] (.accept inner ^MethodNode node ^MethodVisitor mv))
      (visitLabel [l] (.visitLabel inner ^Label l) (mark 0 l))
      (visitLineNumber [line l] (mark line l)))))

(defn- analyze
  "Analyzes class bytes `bs` under `probes` (nil: none set).  Returns `[cov lines reached]`:
  JaCoCo's class coverage, the source lines holding a line entry, and those whose entry
  the probes show executed."
  [^bytes bs probes]
  (let [rd  (ClassReader. bs)
        syn (ArrayList.)
        cov (ClassCoverageImpl. (.getClassName rd) 0 false)
        an  (proxy [ClassAnalyzer] [cov probes (StringPool.)]
              (visitMethod [access mname desc sig exs]
                (let [^ClassAnalyzer this this]
                  (some-> (proxy-super visitMethod (int access) ^String mname ^String desc
                                       ^String sig ^"[Ljava.lang.String;" exs)
                          (marking syn)))))]
    (.accept rd (ClassProbesAdapter. an false) 0)
    [cov
     (into #{} (filter pos?) syn)
     (into #{} (keep (fn [^long n]
                       (let [line (int (.get syn (dec n)))]
                         (when (and (pos? line)
                                    (pos? (.getCoveredCount
                                           (.getInstructionCounter (.getLine cov (int n))))))
                           line))))
           (range 1 (inc (.size syn))))]))

(defn- source-path
  "The file under src/ class coverage `cov` was compiled from, or nil."
  [^IClassCoverage cov]
  (let [pkg (.getPackageName cov)
        src (.getSourceFileName cov)
        up  (subs pkg 0 (max 0 (or (str/last-index-of pkg "/") 0)))]
    (when src
      (some #(when (.isFile (io/file %)) %)
            [(str "src/" pkg "/" src) (str "src/" up "/" src)]))))

(defn- class-lines
  "`{:path :per-probe}` for the dumped class `cname` of id `id` with `n` probes, :per-probe
  holding the lines each probe alone shows executed; nil for a class outside src/."
  [classes cname id n]
  (when-let [^bytes bs (or (get classes id)
                           (let [f (io/file dump-dir (format "%s.%016x.class" cname id))]
                             (when (.isFile f) (Files/readAllBytes (.toPath f)))))]
    (when-let [path (source-path (first (analyze bs nil)))]
      {:path      path
       :per-probe (mapv #(nth (analyze bs (doto (boolean-array n) (aset-boolean % true))) 2)
                        (range n))})))

(defn- dumped
  "Every class the agent dumped, as `{id bytes}` read now, before anything empties target/."
  []
  (into {} (for [^File f (file-seq (io/file dump-dir))
                 :let  [m (re-find #"\.([0-9a-f]{16})\.class$" (.getName f))]
                 :when m]
             [(Long/parseUnsignedLong (second m) 16) (Files/readAllBytes (.toPath f))])))

(defn- targets
  "`[label thunk]` per check (`:run` at its small size, then its large one) and per probe
  (`ab:<name>`, closing the KBs it opened), in table order."
  []
  (let [opened @#'ab/opened]
    (concat (for [{:keys [run sizes] :as c} perf/checks]
              [(name (:name c)) #(run! run sizes)])
            (for [p ab/probes]
              [(str "ab:" (:name (meta p)))
               #(try (p) (finally (run! v/close! (first (reset-vals! opened [])))))]))))

(defn- load-engine!
  "Requires every namespace under src/.  Loading a class sets a probe in its static
  initializer, so a namespace a target first loads would read as executed in full."
  []
  (doseq [^File f (file-seq (io/file "src"))
          :let  [path (.getPath f)]
          :when (str/ends-with? path ".clj")]
    (require (symbol (-> (subs path 4 (- (count path) 4))
                         (str/replace \/ \.)
                         (str/replace \_ \-))))))

(defn- macro-names
  "The name of every macro interned in a loaded namespace, sorted."
  []
  (sort (distinct (for [n (all-ns) [s v] (ns-interns n) :when (:macro (meta v))] (name s)))))

(defn- write-atomic!
  "Writes the lines `rows` to `out` through a sibling `.tmp` file and a rename."
  [^String out rows]
  (let [tmp (File. (str out ".tmp"))]
    (io/make-parents tmp)
    (with-open [w (io/writer tmp)]
      (doseq [^String r rows] (.write w r) (.write w "\n")))
    (.renameTo tmp (File. out))))

(defn- lines-rows
  "The `-lines` map's rows off `by-line` (`{path {line BitSet}}`): `s<i>` and the target
  indexes of each distinct set, then per file `line:s<i>` for each line holding an entry."
  [header by-line]
  (let [ids (volatile! {})
        id  #(or (@ids %) (let [i (count @ids)] (vswap! ids assoc % i) i))
        fs  (doall (for [[path ls] (sort-by key by-line)]
                     (str path "\t" (str/join " " (for [[l bs] (sort-by key ls)]
                                                    (str l ":s" (id bs)))))))]
    (concat header
            (for [[^BitSet bs i] (sort-by val @ids)]
              (str "s" i "\t" (str/join " " (.toArray (.stream bs)))))
            fs)))

(defn -main [out revision dirty & [only]]
  (let [[clear drain] (try (agent-calls)
                           (catch Exception _
                             (binding [*out* *err*]
                               (println "reach: no JaCoCo agent; run it as `lein perf --reach`"))
                             (System/exit 2)))
        _       (load-engine!)
        classes (dumped)
        info    (memoize #(class-lines classes %1 %2 %3))
        by-line (volatile! {})
        hit!    (fn [i ^ExecutionData d]
                  (let [ps ^booleans (.getProbes d)]
                    (when-let [{:keys [path per-probe]} (info (.getName d) (.getId d) (alength ps))]
                      (doseq [p (range (alength ps)) :when (aget ps p) l (per-probe p)]
                        (let [^BitSet bs (or (get-in @by-line [path l])
                                             (let [bs (BitSet.)] (vswap! by-line assoc-in [path l] bs) bs))]
                          (.set bs (int i)))))))
        only    (some-> only (str/split #",") set)
        ts      (cond->> (vec (targets)) only (filterv (comp only first)))
        rows    (vec (map-indexed
                      (fn [i [label thunk]]
                        (clear)
                        (let [ok (try (thunk) true
                                      (catch Throwable t
                                        (binding [*out* *err*]
                                          (println "reach:" label "threw:" (ex-message t)))
                                        false))
                              ds (executed (drain))]
                          (run! #(hit! i %) ds)
                          (binding [*out* *err*]
                            (println (format "reach-progress %d/%d %s" (inc i) (count ts) label))
                            (flush))
                          [label ok (into #{} (keep #(class-key (.getName ^ExecutionData %))) ds)]))
                      ts))
        _       (doseq [[_ ^bytes bs] classes
                        :let [[cov lines] (analyze bs nil)
                              path        (source-path cov)]
                        :when path
                        l lines
                        :when (not (get-in @by-line [path l]))]
                  (vswap! by-line assoc-in [path l] (BitSet.)))
        index   (zipmap (map first rows) (range))
        by-key  (reduce (fn [m [label _ ks]]
                          (reduce #(update %1 %2 (fnil conj []) (index label)) m ks))
                        (sorted-map) rows)
        failed  (keep (fn [[label ok]] (when-not ok label)) rows)
        header  [(str "# reach " revision " " dirty)
                 (str "# targets " (str/join " " (map first rows)))
                 (str "# failed " (str/join " " failed))]]
    (write-atomic! out (concat header (for [[k ix] by-key] (str k "\t" (str/join " " ix)))))
    (write-atomic! (str/replace out #"\.tsv$" "-lines.tsv")
                   (lines-rows [(first header) (str "# macros " (str/join " " (macro-names)))]
                               @by-line))
    (println (format "%d target(s), %d key(s) and %d line(s) reached%s"
                     (count rows) (count by-key)
                     (count (for [[_ ls] @by-line [_ ^BitSet bs] ls :when (not (.isEmpty bs))] 1))
                     (if (seq failed) (str ", census threw for " (vec failed)) "")))
    (shutdown-agents)
    (System/exit (if (seq failed) 1 0))))
