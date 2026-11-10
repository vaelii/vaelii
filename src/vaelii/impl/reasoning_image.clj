;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.reasoning-image
  "A **reasoning image**: the whole reasoning state of a KB
  (`vaelii.impl.types.reasoning`), written as three files and installed into an empty KB in
  place of a recover.  Two places hold one: a `:disk-snapshot` KB's own directory, under
  `<dir>/reasoning/`, and an export dump, under `<dump>/reasoning/` (`dir-name`).

  `:belief? true` is still what the export and import option is called, because that option
  decides whether the **labels** are carried, and a dump written with `:belief? false`
  holds records and no image at all.

  ## What is in it

  - `network.bin` — the dense network (`dense/write-image`): every node, justification
    column, label, defeat-class, block, forced set and supersession;
  - `state.nippy` — the taxonomy's relations and caches, less the slots the live KB
    owns (`taxonomy-side-slots`), and the KB atoms recovery fills or the closing settle
    leaves (`state-atoms`);
  - `manifest.edn` — what the image is valid against, written last, so a directory with
    no manifest holds no image.

  ## The manifest

  The two layout numbers, a records fingerprint, the source identity's digest, and the
  policies that move belief: `config/assertive-arg-types?`, the forced-monotonic set the
  stored declarations give and where each is stated (`declared-forced`), and the shipped
  reasoners the KB records (`kb/reasoners-of`).  The
  records fingerprint differs by place, because each place is checked against something
  different.  A store's own image carries the record store's `p/belief-fingerprint` — on
  the disk store its `reasoning-fingerprint`, read off the slots without decoding a record.
  A dump's image carries content fingerprints of the sentexes and the justifications the
  dump streams (`fingerprint/accumulator`), which an
  import recomputes while it lands them.

  ## When one is installed

  `install-from!` installs an image when every one of these holds, and otherwise leaves the
  KB untouched for the full recover:

  - the KB is on the dense network, and its network holds no node;
  - its provers are the defaults and the shipped reasoners it records, and its solver is
    the default (`refusal`): a registered prover or evaluatable runs code the source
    identity does not cover;
  - the manifest equals the one `manifest-for` gives the KB (`decision`).

  Both sections are read in full before anything moves into the KB, so a torn or
  truncated section costs the recover and never leaves a half-installed network.
  `install!` is the disk image's case: a `:disk-snapshot` KB (`applies?`) against its own
  directory.

  ## When one is written

  `save!` writes a `:disk-snapshot` KB's image after a full recover, and `register-close!`
  arranges a refresh when the directory closes if the records moved since the image was
  written.  The records fingerprint is read before and after the sections are written, and
  an image whose records moved during the write is abandoned.  A close-time write is also
  skipped when the source identity at close differs from the one belief was derived under
  at open: a REPL can reload engine code mid-session, and an image carries the digest of
  the source that derived its belief, never the digest of source loaded afterwards.
  `vaelii.impl.io.export` writes a dump's image through `write-sections!`.  Neither place
  takes an image of a KB whose network does not cover its records (`writable?`).

  ## What an installed image equals

  The records stay the only source of truth.  An image is installed whole, against the
  exact records, source and policies it was written under, or discarded whole; nothing
  reconciles an image against records that moved.  So a KB that installs an image is the
  KB that wrote it, field for field, less the journals and the discovery memo's journal
  position, which an image is written without, and the memo's `:mark`, which names a
  point in the writer's touched set and which the install drops.  The install
  restarts the candidate index's journal.  An image written after a
  recover is that recover.  An image written by a KB built assert by assert carries that
  KB's labels, which equal a recover's because belief is order independent, and that KB's
  derivation depths, which a recover rebuilds from the records
  instead of reading ([docs/defenses.md](docs/defenses.md), \"A reasoning image is
  installed whole or not at all\")."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [taoensso.nippy :as nippy]
            [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.config :as config]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.io.thaw :as safe]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rewrite-query :as rewrite-query]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.source-identity :as si]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.io BufferedInputStream BufferedOutputStream DataInputStream
            DataOutputStream File FileInputStream FileOutputStream FilterInputStream
            InputStream]
           [java.nio.file CopyOption Files StandardCopyOption]
           [java.util.concurrent.atomic AtomicLong]
           [vaelii.impl.dense_jtms DenseTms]
           [vaelii.impl.types.reasoning Reasoning]))

(def format-version
  "The image's own layout number, beside `dense/image-version` (the network section's).
  An image of any other number is discarded, and the open recovers from the records."
  16)

(def ^String dir-name
  "The directory an image is written to, under a `:disk-snapshot` KB's own directory and
  under an export dump.  One constant because five callers name it: `disk-dir` here,
  `vaelii.impl.seal`, `vaelii.impl.io.export`, `vaelii.impl.io.import` and
  `vaelii.host.cli`."
  "reasoning")

(defn state-atoms
  "The KB atoms an image carries: the fields of the register rows imaged as `:state`
  (`caches/image-fields`), each one recovery fills or the closing settle leaves holding
  something the next settle reads.  A fn because a row registers when its namespace loads,
  and this namespace requires few of them: a value read here at load depends on the order
  the namespaces loaded in."
  []
  (vec (caches/image-fields :state)))

(def added-atoms
  "The state atoms an image an earlier build wrote may lack, each left as the open made it
  when the image holds none: `:mint-queues`, which carries the owed mint releases."
  #{:mint-queues})

(defn unimaged-atoms
  "The KB atoms an image leaves as the open made them: every other `Reasoning` atom, and
  the KB's own `:provers`, `:solver`, `:unrecovered` and `:feed`.  `:taxonomy` has its own
  section, and the register says why each of the rest is not carried."
  []
  (-> (into #{} (map keyword) (Reasoning/getBasis))
      (disj :tms)
      (set/difference (set (state-atoms)))
      (into #{:provers :solver :unrecovered :feed})))

(def taxonomy-side-slots
  "The taxonomy keys an image leaves as the open made them: the six callbacks and the
  index store `kb/open-kb` installs with its `:raw?` flag, which belong to the KB, the
  three side caches, each keyed by a relation's own `:gen` or the change clock,
  the supporter cache, which fills from the index on a read, and the reach memo, which
  the KB installs beside its callbacks and fills on a read (`kb/held-forward-reach`)."
  [:supporter-filter-active? :supporter-visible? :network-filter-active? :network-visible?
   :supporter-reaches? :supporter-sentence :index :raw? :closure-memo :closure-lru :rewrite-order
   :supporters :supporter-reach])

;; ---- which KB ---------------------------------------------------------------

(defn- network
  "`kb`'s belief network, or nil when `kb` holds no `Reasoning` value.  A dump is written
  from a `{:records …}` map as well as from an open KB (`vaelii.impl.io.export/export!`),
  and that map has no `:reasoning` volatile for `reasoning/tms` to dereference.  A KB
  value holding no reasoning reads as holding no network, so the three callers below
  answer false or `:not-applicable` for one."
  [kb]
  (some-> (:reasoning kb) deref :tms))

(defn applies?
  "Does `kb` keep a reasoning image in its own directory — a KB on the `:snapshot` index
  (the one carrying a `:snapshot-dir`) over a record store that answers the image
  fingerprint (`p/ImageFingerprinting`), on the dense network?"
  [kb]
  (and (some? (:snapshot-dir kb))
       (satisfies? p/ImageFingerprinting (:records kb))
       (instance? DenseTms (network kb))))

(defn refusal
  "Why `kb` may neither write nor install an image, or nil.  A prover or evaluatable
  beyond the defaults and the shipped reasoners `kb` records, or a solver other than the
  local one, runs code the source identity does not cover.  A recorded reasoner whose
  prover an open has not registered yet is no reason: the open registers it after the
  install."
  [kb]
  (let [pv      @(:provers kb)
        n       (count provers/default-provers)
        shipped (into #{} (map provers/reasoner) (kb/reasoners-of kb))]
    (cond
      (not (and (= provers/default-provers (subvec (vec pv) 0 (min n (count pv))))
                (every? shipped (drop n pv))))   :provers-registered
      (not= solve/local-solver @(:solver kb))  :solver-set
      :else                                    nil)))

(defn- belief-built?
  "Does `kb` hold belief for every stored sentex?  Two conditions: no loader declared the
  belief unbuilt (`kb/note-hazards!`'s `:no-belief`), and every live sentex is a network
  node, which a recover makes and every assert makes, or a record carrying the `:inert`
  provenance mark `assert-inert` writes, which mints no node.  A KB holding a record that
  is neither takes no image, and never writes one of a network that does not cover its
  records."
  [kb]
  (and (not (:no-belief @(:unrecovered kb)))
       (let [tms   (reasoning/tms kb)
             recs  (:records kb)
             nodes (dense/node-count tms)
             total (cap/count-sentexes recs)]
         ;; the walk runs only when the counts differ, so a KB with no inert record reads two
         ;; counts
         (or (== nodes total)
             (== total (+ nodes (count (filter #(and (not (jtms/known-datum? tms %))
                                                     (true? (:inert (p/get-provenance recs %))))
                                               (p/sentex-ids recs)))))))))

(defn writable?
  "May `kb`'s belief be written as an image: the dense network, no `refusal`, and a
  network that covers the records?"
  [kb]
  (and (instance? DenseTms (network kb)) (nil? (refusal kb)) (belief-built? kb)))

(defn- disk-dir ^File [kb] (io/file (str (:snapshot-dir kb)) dir-name))

(defn kb-name
  "The name of `kb`'s directory, which a log line names the KB by."
  [kb]
  (.getName (io/file (str (:snapshot-dir kb)))))

(defn- section ^File [^File dir ^String nm] (io/file dir nm))

;; ---- the manifest -----------------------------------------------------------

(def ^:private forced-declarations
  '#{forced_monotonic_predicate forced_monotonic_between_predicates})

(defn declared-forced
  "The forced-monotonic set `kb`'s stored declarations give, as a sorted vector of
  `[declaration-functor predicate context]` triples: what the image's forced sets were
  computed under, the context deciding whether a declaration is global (docs/nmtms.md,
  \"The forced-monotonic set\").  Read off the index and the records, so an image is
  checked against it before any belief is installed."
  [kb]
  (into []
        (comp (mapcat #(reads/as-stored-with-term (:index kb) %))
              (keep #(p/get-sentex (:records kb) %))
              (filter #(let [s (:sentence %)]
                         (and (sequential? s) (= 2 (count s))
                              (contains? forced-declarations (first s)) (symbol? (second s)))))
              (map #(conj (vec (:sentence %)) (:context %)))
              (distinct))
        (sort forced-declarations)))

(defn manifest-for
  "What an image of `kb` whose records fingerprint is `records` is valid against.
  `:libraries` is carried for a reader of the manifest; the source digest already covers
  it.  `:recover`, the step timings of the last recover of `kb`'s belief (`{:ms total
  :steps {step ms}}`, filed by `vaelii.impl.recovery`), is carried when `kb` holds one,
  for a later rebuild to report its progress against; `decision` does not read it.
  `source`, when given, is the digest recorded in place of the running one: the source a
  trusted image's belief was last derived under in full (`:recover? :trust`)."
  ([kb records] (manifest-for kb records nil))
  ([kb records source]
   (let [sid (si/source-identity)
         lr  (some-> (:unrecovered kb) deref :last-recover)]
     (cond-> {:format    format-version
              :network   dense/image-version
              :records   records
              :source    (or source (:digest sid))
              :libraries (:libraries sid)
              :policy    {:assertive-arg-types (boolean (config/assertive-arg-types?))
                          :forced-monotonic    (vec (sort (declared-forced kb)))
                          :reasoners           (vec (sort (kb/reasoners-of kb)))}}
       lr (assoc :recover lr)))))

(defn decision
  "Why the image `manifest` describes cannot be installed into a KB whose manifest is
  `now`, or nil when it can.  One reason per mismatch class: `:absent`, `:format-changed`,
  `:records-differ`, `:source-differs`, `:policy-differs`."
  [manifest now]
  (cond
    (nil? manifest)                                          :absent
    (not= [(:format manifest) (:network manifest)]
          [(:format now) (:network now)])                    :format-changed
    (not= (:records manifest) (:records now))                :records-differ
    (not= (:source manifest) (:source now))                  :source-differs
    (not= (:policy manifest) (:policy now))                  :policy-differs
    :else                                                    nil))

(defn read-manifest
  "The committed manifest of the image in `dir`, or nil when there is none or it does not
  read under the manifest byte bound."
  [^File dir]
  (let [f (section dir "manifest.edn")]
    (when (.exists f)
      (try (dfiles/read-edn-manifest f) (catch Exception _ nil)))))

;; ---- writing ----------------------------------------------------------------

(defn- move-over!
  "Rename `from` over `to` in one step."
  [^File from ^File to]
  (Files/move (.toPath from) (.toPath to)
              (into-array CopyOption [StandardCopyOption/ATOMIC_MOVE
                                      StandardCopyOption/REPLACE_EXISTING])))

(defn- write-atomic!
  "Write `target` through `write-fn` of a sibling temp file, then rename it over `target`."
  [^File target write-fn]
  (let [tmp (File. (str target ".tmp"))]
    (try
      (write-fn tmp)
      (move-over! tmp target)
      (finally (.delete tmp)))))

(defn- data-out ^DataOutputStream [^File f]
  (DataOutputStream. (BufferedOutputStream. (FileOutputStream. f) 1048576)))

(def ^:private ^:const mb 1048576)

(defn- ticking
  "`in`, adding the bytes each read returns to `read` and counting the reporter `r` up to
  the MB read so far."
  ^InputStream [^InputStream in r ^AtomicLong read]
  (let [add! (fn [^long n] (when (pos? n) (progress/tick-to! r (quot (.addAndGet read n) mb))) n)]
    (proxy [FilterInputStream] [in]
      (read
        ([] (let [b (.read in)] (when-not (neg? b) (add! 1)) b))
        ([bs] (add! (.read in ^bytes bs)))
        ([bs off len] (add! (.read in ^bytes bs (int off) (int len))))))))

(defn- data-in
  "`f` read through a 1 MB buffer, counting the reporter `r` up to the MB read when one is
  given (`ticking`)."
  (^DataInputStream [^File f] (data-in f nil nil))
  (^DataInputStream [^File f r read]
   (let [in (FileInputStream. f)]
     (DataInputStream. (BufferedInputStream. (if r (ticking in r read) in) mb)))))

(defn- state-of
  "`kb`'s taxonomy and state atoms as an image holds them.  The candidate index and the
  taxonomy are held without their journals (`:cache-moves` is one), which name what this
  process's readers read since their last position and none of an installed KB's, and the
  candidate index without its candidates by context, which the first read rebuilds."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    {:taxonomy (apply dissoc @tax :cache-moves taxonomy-side-slots)
     :atoms    (into {} (map (fn [a] (let [v @(get (reasoning/of kb) a)]
                                       [a (cond-> v
                                            (= a :nogood-candidates) journal/without
                                            ;; the owed releases alone; the other queues empty at a settle
                                            (= a :mint-queues) (select-keys [:owed])
                                            ;; the discovery memo's position in `:cache-moves`
                                            (and (= a :preserved-clashes) (:flat v))
                                            (update :flat dissoc :pos))])))
                     (state-atoms))}))

(defn write-sections!
  "Write `kb`'s network and state into `dir`, then a manifest carrying `fields`, and
  return the manifest — or nil when `commit?`, asked after both sections are written,
  answers false.  Both sections are written to temp files beside the image first, so a
  write that throws or runs out of heap, or that `commit?` declines, leaves the image
  `dir` held installable.  Only then is the manifest deleted, the sections renamed over
  the old ones and the new manifest written last, so from the first rename until the
  commit `dir` holds no image rather than an old manifest over new sections.  The caller
  holds the KB still; nothing here stops a writer."
  ([kb dir fields] (write-sections! kb dir fields (constantly true)))
  ([kb ^File dir fields commit?]
   (let [mf  (section dir "manifest.edn")
         net (section dir "network.bin.tmp")
         st  (section dir "state.nippy.tmp")]
     (.mkdirs dir)
     (try
       (with-open [_ (progress/start ::write-sections (str (kb-name kb) ": write the reasoning image") nil)]
         (with-open [o (data-out net)] (dense/write-image (reasoning/tms kb) o))
         (with-open [o (data-out st)]
           (nippy/freeze-to-out! o (state-of kb))))
       (when (commit?)
         (let [manifest (assoc fields
                               :written-at (str (java.time.Instant/now))
                               :bytes {:network (.length net) :state (.length st)})]
           (.delete mf)
           (move-over! net (section dir "network.bin"))
           (move-over! st (section dir "state.nippy"))
           (write-atomic! mf (fn [^File f]
                               (binding [*print-length* nil *print-level* nil]
                                 (spit f (pr-str manifest)))))
           manifest))
       (finally (.delete net) (.delete st))))))

(defn save!
  "Write a `:disk-snapshot` KB's image into its own directory, and return the manifest —
  or nil when nothing was written: the KB does not keep one (`applies?`, `writable?`), a
  settle is deciding its belief on another thread, or its records or belief moved while
  the sections were written.  A failure, running out of heap included, is logged and
  returns nil, and leaves the image on disk as it was (`write-sections!`).

  The manifest covers the records alone, so an image of belief a settle had not finished
  deciding would pass the next open's check.  The write is therefore declined while a
  settle holds the network (`jtms/held`), and committed only when the change clock read
  before the sections equals the one read after them; the clock moves on every mutation
  in the process, so a write beside another KB's writer is declined as well.

  `source` is recorded in place of the running digest (`manifest-for`)."
  ([kb] (save! kb nil))
  ([kb source]
   (when (and (applies? kb) (writable? kb) (nil? (jtms/held (reasoning/tms kb))))
     (try
       (let [t0      (System/nanoTime)
             clock   (observe/change-clock)
             records (p/belief-fingerprint (:records kb))
             moved?  #(or (some? (jtms/held (reasoning/tms kb)))
                          (not= clock (observe/change-clock))
                          (not= records (p/belief-fingerprint (:records kb))))
             m       (write-sections! kb (disk-dir kb) (manifest-for kb records source)
                                      #(not (moved?)))]
         (if m
           (trove/log! {:level :info :id ::written
                        :msg (format "%s: wrote the reasoning image in %.1f s"
                                     (kb-name kb) (/ (- (System/nanoTime) t0) 1e9))})
           (trove/log! {:level :warn :id ::records-moved
                        :msg (str "reasoning image for " (:snapshot-dir kb) " abandoned: the"
                                  " records or the belief moved while it was written")}))
         m)
       (catch Throwable t
         (trove/log! {:level :warn :id ::write-failed :error t
                      :msg (str "reasoning image for " (:snapshot-dir kb) " not written ("
                                (.getMessage t) ") — the next open recovers")})
         nil)))))

(defn- save-at-close!
  "The close-time write: `save!` recording `derived` when the records moved since the
  image on disk, and only when the source identity still equals `running`, the digest of
  the code that has been moving belief.  The two differ for a trusted image: `derived` is
  the source its belief was last derived under in full, and `running` the build that
  installed it and settled every write since."
  [kb derived running]
  (when (applies? kb)
    (let [m (read-manifest (disk-dir kb))]
      (cond
        (not= running (:digest (si/source-identity)))
        (trove/log! {:level :info :id ::source-moved
                     :msg (str "close " (kb-name kb) ": reasoning image not refreshed, the"
                               " engine source changed since belief was derived")})

        (or (nil? m) (not= (:records m) (p/belief-fingerprint (:records kb))))
        (save! kb derived)

        :else nil))))

(defn register-close!
  "Arrange for `kb`'s image to be refreshed when its directory closes.  `source` is the
  source identity's digest belief was last derived under in full, and the digest now when
  the caller has none; the refreshed image records it.  The close writes only while
  the source on disk is still the one this call saw, which a trusted image's `source` is
  not.  A no-op for a KB that does not keep an image, or that `refusal` names a reason
  for."
  [kb source]
  (when (and (applies? kb) (nil? (refusal kb)))
    (let [running (:digest (si/source-identity))
          source  (or source running)]
      (disk/register-reasoning-image! (:snapshot-dir kb)
                                      #(save-at-close! kb source running)))))

(defn register-rebuild-close!
  "Arrange for `kb`'s directory close to stop a belief rebuild and then refresh the image,
  for a KB whose open installed an image written under other engine source.  `stop!`
  returns once the rebuild has stopped.  `source` is a thunk: the digest belief was
  derived under once the rebuilt belief is installed, and nil while the installed image
  is still the one the earlier build wrote, in which case nothing is written."
  [kb stop! source]
  (disk/register-reasoning-image! (:snapshot-dir kb)
                                  #(do (stop!)
                                       (when-let [s (source)] (save-at-close! kb s s)))
                                  stop!))

(defn source-digest
  "The source identity's digest for the source on the classpath now."
  []
  (:digest (si/source-identity)))

;; ---- installing -------------------------------------------------------------

(defn- read-state
  "`state.nippy`, thawed behind the class-name check (`vaelii.impl.io.thaw`), under
  `safe/sharing`, so a symbol or a handle the taxonomy and the atoms repeat is one object.
  Counts the reporter `r` up to the MB `read` holds (`data-in`)."
  [^File dir r read]
  (let [st    (with-open [i (data-in (section dir "state.nippy") r read)]
                (safe/thaw-from-in! i (safe/sharing)))
        atoms (set (state-atoms))]
    (when-not (and (map? (:taxonomy st))
                   (= (set/difference atoms added-atoms)
                      (set/difference (set (keys (:atoms st))) added-atoms))
                   (set/subset? (set (keys (:atoms st))) atoms))
      (throw (IllegalStateException. "state.nippy does not hold the atoms this build images")))
    st))

(defn install-from!
  "Install the image in `dir` into `kb` in place of a recover.  `records-fn` returns the
  KB's records fingerprint in the form the image's manifest carries; it runs only once the
  cheaper conditions hold.  Returns `{:reasoning :installed :source d :image m}`, or
  `{:reasoning :recover :reason r}` with the KB untouched — `r` one of `decision`'s reasons, a `refusal`,
  `:not-applicable`, `:network-populated` or `:unreadable`.  A `VirtualMachineError`
  anywhere in a failed install's cause chain is rethrown as itself, not answered
  `:unreadable`: the heap ran out, the image may be sound, and a recover from the records
  needs more heap than the install.  `:source` is the source
  identity's digest, which `register-close!` takes, and `:image` the installed manifest's
  `:source`, `:written-at` and `:recover`.

  `accept` is a set of `decision` reasons under which the image is installed anyway, and
  the result is then `{:reasoning :stale :reason r :source d :image-source d' :image m}`, `d'` the
  digest the image was written under.  `vaelii.impl.recovery` passes `#{:source-differs}`
  under `:recover? :background` and rebuilds belief behind the installed image."
  ([kb dir records-fn] (install-from! kb dir records-fn #{}))
  ([kb ^File dir records-fn accept]
   (cond
     (not (instance? DenseTms (network kb))) {:reasoning :recover :reason :not-applicable}
     (jtms/any-node? (network kb))           {:reasoning :recover :reason :network-populated}
     (refusal kb)                         {:reasoning :recover :reason (refusal kb)}
     :else
     (let [now      (manifest-for kb (records-fn))
           manifest (read-manifest dir)
           why      (decision manifest now)]
       (if (and why (not (contains? accept why)))
         {:reasoning :recover :reason why :source (:source now)}
         (try
           (let [[net st]
                 (with-open [r (progress/start ::read-image
                                               (str (kb-name kb) ": read the reasoning image, MB")
                                               (quot (+ (.length (section dir "network.bin"))
                                                        (.length (section dir "state.nippy")))
                                                     mb))]
                   (let [read (AtomicLong. 0)]
                     [(with-open [i (data-in (section dir "network.bin") r read)]
                        (dense/read-image! (dense/create-dense-tms) i))
                      (read-state dir r read)]))]
             (dense/copy-into! (reasoning/tms kb) net)
             (swap! (reasoning/taxonomy kb)
                    (fn [tax]
                      (let [installed (merge tax (:taxonomy st))]
                        (if (contains? (:taxonomy st) rewrite-query/consumer-key)
                          installed
                          (dissoc installed rewrite-query/consumer-key)))))
             (doseq [[a v] (:atoms st)] (reset! (get (reasoning/of kb) a) v))
             ;; the discovery memo's `:mark` names a point in the writer's touched set,
             ;; and the installed network opens touched sets of its own at generation 0, where
             ;; `jtms/touched-since` would take the writer's mark for one of its own
             (swap! (reasoning/preserved-clashes kb) dissoc :mark)
             ;; the candidate index is written without its journal
             (swap! (reasoning/nogood-candidates kb) journal/restart)
             ;; an image an earlier build wrote without the argument family
             (argument/installed! kb)
             (let [image (select-keys manifest [:source :written-at :recover])]
               (if why
                 {:reasoning :stale :reason why :source (:source now)
                  :image-source (:source manifest) :image image}
                 {:reasoning :installed :source (:source now) :image image})))
           (catch Throwable t
             (when-let [e (safe/vm-error t)] (throw e))
             (trove/log! {:level :warn :id ::unreadable :error t
                          :msg (str "reasoning image in " dir " unreadable ("
                                    (.getMessage t) ") — recovering from the records")})
             {:reasoning :recover :reason :unreadable :source (:source now)})))))))

(defn install!
  "Install a `:disk-snapshot` KB's own image in place of a recover — `install-from!` over
  its directory, against the record store's `p/belief-fingerprint`, under `accept`."
  ([kb] (install! kb #{}))
  ([kb accept]
   (if (applies? kb)
     (install-from! kb (disk-dir kb) #(p/belief-fingerprint (:records kb)) accept)
     {:reasoning :recover :reason :not-applicable})))

;; ---- trusting and verifying a source change -----------------------------------

(def ^:private sections
  "The image's files, manifest first: moving or deleting in this order leaves a directory
  without a manifest, and so without an image, from the first file on."
  ["manifest.edn" "network.bin" "state.nippy"])

(defn move-image!
  "Move the image in `from` into `to`, manifest first, and return the manifest now in `to`.
  Returns nil and moves nothing when `from` holds no manifest.  A section already in `to`
  is replaced."
  [^File from ^File to]
  (when (.exists (section from "manifest.edn"))
    (.mkdirs to)
    (doseq [nm sections
            :let [src (section from nm)]
            :when (.exists src)]
      (Files/move (.toPath src) (.toPath (section to nm))
                  (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING])))
    (read-manifest to)))

(defn delete-image!
  "Delete the image in `dir`, manifest first, and then `dir` itself when no other file is
  left in it."
  [^File dir]
  (doseq [nm sections] (.delete (section dir nm)))
  (when (empty? (.list dir)) (.delete dir)))

(defn- read-network ^DenseTms [^File dir]
  (with-open [i (data-in (section dir "network.bin"))]
    (dense/read-image! (dense/create-dense-tms) i)))

(defn- labels
  "The bitmaps that state what network `t` believes: its nodes, and the IN and blocked
  sets."
  [^DenseTms t]
  [(.-nodes t) (.-in t) (.-blocked t)])

(defn compare-images
  "Compare the images in `a` and `b`, as `{:labels :network :state}`, each `:same` or
  `:differs`.  `:labels` compares what the two networks believe: the node set and the IN
  and blocked sets.  `:network` and `:state` compare the two files byte for byte,
  so they also differ on derivation depths, justification order and map iteration order,
  and none of those is belief.  Both images must carry this build's layout numbers, which
  the caller checks against the manifests before calling."
  [^File a ^File b]
  (let [same  (fn [x] (if x :same :differs))
        file= (fn [nm] (== -1 (Files/mismatch (.toPath (section a nm)) (.toPath (section b nm)))))]
    {:labels  (same (= (labels (read-network a)) (labels (read-network b))))
     :network (same (file= "network.bin"))
     :state   (same (file= "state.nippy"))}))
