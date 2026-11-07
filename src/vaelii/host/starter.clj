;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.starter
  "A starter common-sense KB: a documented, **schema-only** upper + middle ontology.
  It loads the upper ontology into CxUniverse (vaelii.host.core-context), then the
  middle contexts, each a KB file on the classpath under resources/kb/:

    * upper (`kb/upper/`, every file in CxUniverse): what things *are*, always true, like
      `genl`.  Split by domain, one file each:
        - core.txt       — the vocabulary the engine interprets and the ontology's top.
        - abstract.txt   — the abstract type skeleton (physical/intangible and
                                their kinds) + the structural relations tangiblePartOf/locatedIn.
        - organism.txt   — the biological taxonomy + its disjointness.
        - life.txt       — the organism relations (parentOf, siblingOf, flies,
                                mortal, birthYearOf, olderThan, …) with arg + metadata.
        - society.txt    — the social relations (marriedTo, likes, owns).
        - measure.txt    — the theory of measurement: the two measure terms, the
                                dimensionOf/conversionFactor table with the units that
                                fill it, the comparisons, weightOf / heightOf, and the
                                sign vocabulary for the quantities nobody has a figure
                                for (signOf / trendOf / the qualitative* arithmetic).
        - reflection.txt — the expression lattice (atomic and non-atomic, open and
                                closed, well-formed and ill-formed expressions) and the
                                use/mention vocabulary (proposition, means, denotes,
                                expresses).
        - space.txt      — qualitative space, four independent calculi: RCC-8
                                topology (eight base + six derived), cardinal direction
                                (nine + four), relative direction over a frame's own axes
                                (nine + four, the frame being the context), and
                                qualitative distance (seven + three).
        - structure.txt  — the data structures (lists, multisets, finite sets, maps),
                                the relations that read one and the corresponding predicates.
        - time.txt       — qualitative time: Allen's interval relations (thirteen
                                base + seven derived), the point algebra over instants,
                                the three calendar constructors and the InstantFn moment
                                a calendar term's startOf and endOf are computed as, plus
                                the length / totalDuration / overlapDuration vocabulary
                                the arithmetic computes over.
    * middle (`kb/middle/`, one context per file, between CxUniverse and CxWell): how the
      definitional things *interrelate*, where several overlapping theories can coexist.
        - CxAnatomy.txt   — what kinds of thing have what kinds of part.
        - CxBiology.txt   — birds fly by default except penguins; organisms
                                 are mortal; flight enables travel; sleep is what the
                                 theory is willing to assume.
        - CxChange.txt    — a simple event calculus: a state persists until an
                                 event ends it, so holdsAt is inertia over what
                                 initiates and terminates say.
        - CxKinship.txt   — grandparentOf, ancestorOf, olderThan, and parenthood
                                 from maternity and paternity.
        - CxMereology.txt — a part is located where its whole is; owning a whole
                                 entails owning its parts.
        - CxNormalPhysicalConditions.txt — the states of matter at room temperature
                                 and pressure: stone, wood and glass are solid,
                                 mercury is liquid, metal_stuff is solid by default.
                                 Opt-in: it sees CxUniverse and CxWell does not
                                 see it.
        - CxSize.txt      — comparative size: stated between kinds, computed
                                 between objects from their measures.
        - CxSocial.txt    — what acquaintance follows from; employment as one way
                                 of belonging; the general relationship and
                                 dwelling vocabulary over two persons.
        - CxTra.txt       — vocabulary that is generally useful but specific to
                                 one domain: relations over software tools, their
                                 invocations and receipts and the abilities they
                                 confer, media resources and DNS names, the kinds
                                 the relations are typed over, computers and what
                                 runs on them, access to a resource and to the
                                 files a path names, pull requests on a forge
                                 and who may merge them, and
                                 the perception relations perceives, sees, seeImage
                                 and watchVideo, and relationship and plural-
                                 identity vocabulary narrower than CxSocial's.
                                 Opt-in: it sees CxUniverse and CxSocial, and
                                 CxWell does not see it.

  The topology, most general (top) to most specific (bottom): CxUniverse holds the upper
  ontology; each of the seven theories sees CxUniverse and not the other middle
  contexts, and an opt-in theory sees the middle context its vocabulary builds on (CxTra
  sees CxSocial); and CxWell sees every middle context but the opt-in ones.  Each middle file wires itself in
  with its own `genlCx` edges, so the topology is data.  **No cast and no contingent facts
  ship**: the starter is a schema, and contingent data (a cast, worked examples, the
  Aesop fables) belongs below CxWell and lives in the tests that need it.

  The unit table is the one place individuals ship, and it applies that rule rather
  than excepting itself from it: a minute is sixty seconds by stipulation, so the
  factor is vocabulary and not a measurement anybody took.  measure.txt states
  the test it holds a unit to.

  What stays in code here is the *order the layers* load in — loading order is logic,
  the definitional layer must precede the theories that reason over it — and the one
  computed batch (every type is also a unary_predicate).  Within a layer, every file
  present is loaded (discovered from the classpath), so adding a domain or a theory is
  dropping a file in kb/upper/ or kb/middle/, no code change."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.kb :as kbi]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.source-identity :as si]
            [vaelii.impl.strength :as strength])
  (:import [java.io File]
           [java.lang ProcessHandle]
           [java.lang.management ManagementFactory]
           [java.nio.charset StandardCharsets]
           [java.nio.file CopyOption Files StandardCopyOption]
           [java.security MessageDigest]))

(defn warn-retired
  "Log at `:warn` each symbol of `retired` that a stored sentex of `kb` names, with how
  many name it, and return those counts as a sorted map.  One term-index read per symbol
  (`v/find-sentexes`), so an empty `retired` reads nothing."
  [kb retired]
  (let [named (into (sorted-map)
                    (keep (fn [s] (let [n (count (v/find-sentexes kb s))]
                                    (when (pos? n) [s n]))))
                    retired)]
    (doseq [[s n] named]
      (trove/log! {:level :warn :id ::retired-symbol
                   :msg  (str n (if (= 1 n) " stored sentex names " " stored sentexes name ") s
                              ", which a release retired; `upgrade --sync` lists the premises")
                   :data {:symbol s :sentexes n}}))
    named))

(defn load-into
  "Populate `kb` with the starter schema — every file under resources/kb/upper/ and
  resources/kb/middle/, loaded on kb start by default, then `warn-retired` over every
  release's `:retired` set (`seed/release-renames`). Returns kb.

  `loaded`, when given, is called with each load's context right after it is asserted —
  `CxUniverse` after the upper ontology, then each middle context in load order — and
  with `:unary-predicates` after the closing batch, which no file states.
  `vaelii.host.sync` reads it to learn which load each premise came from."
  ([kb] (load-into kb nil))
  ([kb loaded]
   (let [loaded (or loaded (fn [_]))]
     ;; The whole starter is one batch: belief settles once at the end, not once per
     ;; sentence (`v/with-deferred-settle`).  The nested `core-context/load-into` defers
     ;; into this batch: its own wrapper is a no-op and this one's settle reconciles both.
     (v/with-deferred-settle kb
       (core-context/load-into kb)
       (loaded sx/root-context)
       (let [cs (seed/layer-contexts "middle")]
         (with-open [r (progress/start ::middle "starter: load the middle contexts" (count cs))]
           (doseq [c cs]
             (seed/load-context kb c "middle")
             (loaded c)
             (progress/tick! r)))))
     ;; The subtypes of thing are unary types. Other genl components may relate
     ;; predicates of any arity and do not imply unary membership.  `specs` is read after the
     ;; batch above settles, so its extent is the believed one; a second batch stores the
     ;; marks.  A type an argument declaration names already holds its mark (docs/argtypes.md)
     ;; and is skipped.
     (v/with-deferred-settle kb
       (let [ts (into [] (remove #(seq (v/sentexes-matching kb (list 'unary_predicate %)
                                                            sx/root-context)))
                      (nm/by-print-key (v/specs kb 'thing)))]
         (with-open [r (progress/start ::unary-predicates "starter: mark the unary types"
                                       (count ts))]
           (doseq [t ts]
             (v/assert kb (list 'unary_predicate t) sx/root-context)
             (progress/tick! r)))))
     (loaded :unary-predicates)
     (warn-retired kb (:retired (seed/release-renames)))
     kb)))

(defn- files-sha
  "The hex SHA-256 over `files`, `[name source]` pairs in load order: each name, its byte
  count and its bytes."
  [files]
  (let [md (MessageDigest/getInstance "SHA-256")]
    (doseq [[n src] files]
      (let [^bytes b (with-open [^java.io.InputStream in (io/input-stream src)] (.readAllBytes in))]
        (.update md (.getBytes (str n " " (alength b) "\n") StandardCharsets/UTF_8))
        (.update md b)))
    (apply str (map #(format "%02x" %) (.digest md)))))

(defn- source-sha
  "The hash of the files `source` loads: the starter's upper and middle files for
  `:starter`, else the `Cx….txt` files of a text KB directory and its digest manifest, or
  the one file the path names.  Nil for a path that does not exist."
  [source]
  (if (= :starter source)
    (files-sha (concat (for [f (core-context/upper-files)]
                         [(str "upper/" f) (io/resource (str "kb/upper/" f))])
                       (for [c (seed/layer-contexts "middle")]
                         [(str "middle/" c ".txt") (io/resource (str "kb/middle/" c ".txt"))])))
    (let [^File f (io/file (str source))
          ^File m (io/file f text/manifest-file)]
      (when (.exists f)
        (files-sha (map (fn [^File x] [(.getName x) x])
                        (if (.isDirectory f)
                          (cond-> (text/kb-files f) (.isFile m) (conj m))
                          [f])))))))

(def ^:private loader-sources
  "The classpath sources that shape `load-into`'s KB outside the source identity's walk."
  ["vaelii/host/starter.clj" "vaelii/host/core_context.clj" "vaelii/host/seed.clj"
   "vaelii/impl/io/text.clj"])

(defn- dump-name
  "The directory name of this engine's starter dump.  It joins everything that decides
  what `load-into` stores: the source identity's digest, `loader-sources`, the starter's
  files, and the two switches that change what a load stores."
  ^String []
  (str/join "-" [(:digest (si/source-identity))
                 (files-sha (map (juxt identity io/resource) loader-sources))
                 (source-sha :starter)
                 (if argument/*assertive-arg-types?* "assertive" "constraint")
                 (if checks/*prune-subsumed-mints?* "pruned" "unpruned")]))

(defn- edited-since-start?
  "Did a source file or a shipped KB file change after this JVM started?  The code this JVM
  compiled and a `dump-name` read from the files then describe different engines."
  []
  (let [started (.getStartTime (ManagementFactory/getRuntimeMXBean))]
    (boolean
     (some (fn [^File dir] (some #(> (.lastModified ^File %) started) (file-seq dir)))
           [(.getParentFile (io/file (io/resource "vaelii/core.clj")))
            (.getParentFile (io/file (io/resource "kb/upper")))]))))

(defn- write-dump!
  "Export `kb` to `dir`, through a temporary sibling and an atomic rename so a reader never
  sees a partial dump, and delete every other dump under `dir`'s parent.  Nothing is written
  under `edited-since-start?`.  A failed write is logged: the dump only shortens a later
  start, and the KB is already loaded."
  [kb ^File dir]
  (let [root (.getParentFile dir)
        tmp  (File. root (str "tmp-" (.pid (ProcessHandle/current))))]
    (try
      (when-not (edited-since-start?)
        (.mkdirs root)
        (v/export! kb (str tmp) {:variant :records+index :compression :none})
        (Files/move (.toPath tmp) (.toPath dir)
                    (into-array CopyOption [StandardCopyOption/ATOMIC_MOVE]))
        (doseq [^File f (.listFiles root)
                :when (and (not= f dir) (not (str/starts-with? (.getName f) "tmp-")))]
          (dfiles/delete-tree! f)))
      (catch Exception e
        (trove/log! {:level :warn :id ::dump-not-written :error e
                     :msg (str "the starter dump was not written: " (ex-message e))}))
      (finally (dfiles/delete-tree! tmp)))))

(defn load-through-dump
  "Answer a KB holding the starter, restored from the export dump `dump-name` names under
  the directory `root`.  `open` answers an empty KB.  With no such dump, or one the import
  refuses, `load-into` runs on a KB `open` answers, and that KB replaces every dump under
  `root`.  See docs/web.md, \"The starter dump\"."
  [open root]
  (let [dir (File. (str root) (dump-name))]
    (or (when (.isDirectory dir)
          (try
            (let [kb (doto (open) (v/import! (str dir) {:belief? true}))]
              (trove/log! {:level :info :id ::dump-restored
                           :msg (str "restored the starter from " dir)})
              kb)
            (catch Exception e
              (trove/log! {:level :warn :id ::dump-refused :error e
                           :msg (str "the starter dump " dir " did not import: " (ex-message e))})
              (dfiles/delete-tree! dir)
              nil)))
        (doto (open) load-into (write-dump! dir)))))

(defn- records-fingerprint
  "`p/belief-fingerprint` of `kb`'s record store, or nil for a store that keeps none."
  [kb]
  (let [r (oplog/inner-records (:records kb))]
    (when (satisfies? p/ImageFingerprinting r)
      (p/belief-fingerprint r))))

(defn- stated
  "What the text KB `source` states: `{context {sentence #{strength}}}`, a context its
  forms name mapped to the ground literals stated there, an `(ist Cx S)` read in `Cx`.  A
  rule and an inert form name their context and state no literal."
  [source]
  (reduce (fn [m [form context]]
            (let [[s o]  (text/peel-form form)
                  [s c]  (if (and (seq? s) (= 'ist (first s)) (symbol? (second s)))
                           [(nth s 2 nil) (second s)]
                           [s context])
                  m      (update m c #(or % {}))]
              (if (or (:inert o) (not (seq? s)) (not (sx/ground-term? s))
                      (rules/rule-sentence? (rules/inner-rule s)))
                m
                (update-in m [c s] (fnil conj #{}) (:strength o :default)))))
          {} (:entries (text/entries source))))

(defn- stated-handles
  "The handles `kb` stores the sentences of `said` under (`stated`'s map, nil for the
  starter)."
  [kb said]
  (when said
    (into #{} (for [[c ss] said, s (keys ss), :let [h (v/handle-of kb s c)], :when h] h))))

(defn- trim-stated!
  "Retract, in one `v/edit!`, each handle of `handles` storing a premise `kbi/replaceable-premise?`
  accepts outside CxUniverse and the middle contexts, unless `said` (`stated` of every
  current source, merged) states its sentence there at its stored strength.  Then
  re-assert, at the strongest strength stated, each retracted sentence `said` states, and
  return `{retracted-handle new-handle}` for those."
  [kb handles said]
  (let [fixed (into #{sx/root-context} (seed/layer-contexts "middle"))
        cands (into {} (keep (fn [h] (let [x (v/sentex kb h)]
                                       (when (and (not (fixed (:context x))) (kbi/replaceable-premise? kb h x))
                                         [h x]))))
                    handles)
        want  (into {} (for [c (distinct (map (comp :context val) cands))
                             [s strengths] (get said c)
                             :let [h (v/handle-of kb s c)]
                             :when (contains? cands h)]
                         [h [s c (reduce strength/max strengths)]]))
        gone  (into [] (comp (remove (fn [[h x]] (= (nth (want h) 2 nil) (:strength x :default))))
                             (map key))
                    cands)]
    (when (seq gone) (v/edit! kb {:remove gone}))
    (v/with-deferred-settle kb
      (into {} (keep (fn [h] (when-let [[s c st] (want h)] [h (v/assert kb s c {:strength st})])))
            gone))))

(defn load-sources
  "Load `sources` into `kb` in order, each `:starter` (`load-into`) or a text KB path
  (`v/load-text!`), and return kb.  Over a store with a directory whose records answer
  `p/belief-fingerprint`, it records the load key (`dfiles/write-load-key!`) and the
  handles each source states (`dfiles/write-load-stated!`).  Under an unchanged key, the
  sources before the first whose hash differs from the recorded one are skipped, and the
  premises the recorded sources from there stated are trimmed to what `sources` state
  (`trim-stated!`) before the rest load.  See docs/operations.md, \"Restarting over a
  built store\"."
  [kb sources]
  (let [dir    (:dir kb)
        fp     (when dir (records-fingerprint kb))
        shas   (mapv source-sha sources)
        engine (when fp (:digest (si/source-identity)))
        rec    (when fp (dfiles/recorded-load-key dir))
        valid? (and rec (= engine (:engine rec)) (= fp (:records rec)))
        same   (if valid? (count (take-while true? (map = shas (map :sha (:sources rec))))) 0)
        todo   (drop same sources)
        stale  (when valid? (drop same (:sources rec)))
        held   (when (and valid? (or (seq todo) (seq stale))) (dfiles/recorded-load-stated dir fp))
        said   (memoize #(when-not (= :starter %) (stated %)))
        trim   (into #{} cat (drop same held))
        moved  (if (seq trim)
                 (trim-stated! kb trim (apply merge-with (partial merge-with into) (keep said sources)))
                 {})]
    (doseq [s todo]
      (if (= :starter s) (load-into kb) (v/load-text! kb s)))
    (trove/log! {:level :info :id ::loaded
                 :msg   (format "loaded %d of %d sources; the store held the first %d"
                                (count todo) (count sources) same)
                 :data  {:skipped same :loaded (count todo)}})
    (when (and fp (or (seq todo) (seq stale)))
      (let [fp' (records-fingerprint kb)]
        (dfiles/write-load-stated! dir fp'
                                   (map-indexed (fn [i s]
                                                  (if-let [hs (when (< i same) (get held i))]
                                                    (into #{} (map #(get moved % %)) hs)
                                                    (stated-handles kb (said s))))
                                                sources))
        (dfiles/write-load-key! dir {:engine  engine
                                     :sources (mapv (fn [s h] {:source (if (keyword? s) s (str s)) :sha h})
                                                    sources shas)
                                     :records fp'})))
    kb))

(defn load-starter-and-layers
  "`load-sources` of the starter, then of each path in `opts`' `:layers`: the entry point
  `vaelii.starter/load-into` is.  A key other than `:layers` is refused
  (`:unknown-option`)."
  [kb opts]
  (opts/check! opts #{:layers} "load-into" nil)
  (load-sources kb (into [:starter] (:layers opts))))
