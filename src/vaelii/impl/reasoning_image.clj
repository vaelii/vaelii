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
    column, label, defeat-class, defeat, block and supersession;
  - `state.nippy` — the taxonomy's relations and caches, less the slots the live KB
    owns (`taxonomy-side-slots`), and the KB atoms recovery fills or the closing settle
    leaves (`state-atoms`);
  - `manifest.edn` — the stamp, written last, so a directory with no manifest holds no
    image.

  ## The stamp

  The two layout numbers, a records fingerprint, the source identity's digest, and the two
  policies that move belief (`checks/arbitrating?` and `config/assertive-arg-types?`).  The
  records fingerprint differs by place, because each place is checked against something
  different.  A disk image carries the record store's `reasoning-fingerprint`, read off the
  slots without decoding a record.  A dump's image carries content fingerprints of the
  sentexes and the justifications the dump streams (`fingerprint/accumulator`), which an
  import recomputes while it lands them.

  ## When one is installed

  `install-from!` installs an image when every one of these holds, and otherwise leaves the
  KB untouched for the full recover:

  - the KB is on the dense network, and its network holds no node;
  - its provers and its solver are the defaults (`refusal`): a registered prover or
    evaluatable runs code the source identity does not cover;
  - the manifest's stamp equals the KB's (`decision`).

  Both sections are read in full before anything moves into the KB, so a torn or
  truncated section costs the recover and never leaves a half-installed network.
  `install!` is the disk image's case: a `:disk-snapshot` KB (`applies?`) against its own
  directory.

  ## When one is written

  `save!` writes a `:disk-snapshot` KB's image after a full recover, and `register-close!`
  arranges a refresh when the directory closes if the records moved since the image was
  written.  The records stamp is read before and after the sections are written, and an
  image whose records moved during the write is abandoned.  A close-time write is also
  skipped when the source identity at close differs from the one belief was derived under
  at open: a REPL can reload engine code mid-session, and an image carries the digest of
  the source that derived its belief, never the digest of source loaded afterwards.
  `vaelii.impl.io.export` writes a dump's image through `write-sections!`.  Neither place
  takes an image of a KB whose network does not cover its records (`writable?`).

  ## What an installed image equals

  The records stay the only source of truth.  An image is installed whole, against the
  exact records, source and policies it was written under, or discarded whole; nothing
  reconciles an image against records that moved.  So a KB that installs an image is the
  KB that wrote it, field for field.  An image written after a recover is that recover.  An
  image written by a KB built assert by assert carries that KB's labels, which equal a
  recover's because belief is order independent, and that KB's derivation depths and
  settle readings, which a recover rebuilds from the records instead of reading
  ([docs/defenses.md](docs/defenses.md), \"A reasoning image is installed whole or not at
  all\")."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [taoensso.nippy :as nippy]
            [taoensso.trove :as trove]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.config :as config]
            [vaelii.impl.dense-jtms :as dense]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.source-identity :as si]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.io BufferedInputStream BufferedOutputStream DataInputStream
            DataOutputStream File FileInputStream FileOutputStream]
           [java.nio.file CopyOption Files StandardCopyOption]
           [vaelii.impl.dense_jtms DenseTms]
           [vaelii.impl.disk.record_store DiskRecordStore]))

(def format-version
  "The image's own layout number, beside `dense/image-version` (the network section's).
  An image of any other number is discarded."
  1)

(def ^String dir-name
  "The directory an image is written to, under a `:disk-snapshot` KB's own directory and
  under an export dump.  One constant because five callers name it: `disk-dir` here,
  `vaelii.impl.seal`, `vaelii.impl.io.export`, `vaelii.impl.io.import` and
  `vaelii.host.cli`."
  "reasoning")

(def state-atoms
  "The KB atoms an image carries: each one recovery fills, or the closing settle leaves
  holding something the next settle reads.  `reasoning_image_test` fails on a KB atom that is
  in neither this list nor `unimaged-atoms`."
  [:clash-readings :program :recheck :refused :opposed :preserving
   :preserved-clashes :excepted :meta-except-count :rule-antecedents :rule-contexts
   :negations :clashes :sib-exc-dirty :supersessions :scoped-defeats
   :vantage-disagreements])

(def unimaged-atoms
  "The KB atoms an image leaves as the open made them.  `:taxonomy` has its own section.
  `:provers` and `:solver` are configuration the caller sets, held to the defaults by
  `refusal`.  `:settle-stats` and `:chain-stats` count work this process did.  `:qcn`,
  `:qcn-joined`, `:matches` and `:closures` are bounded caches a missing read refills, and
  `:withdrawn` is the per-reader cache `res/withdrawal` refills from the imaged
  `:scoped-defeats`, `:vantage-disagreements` and `:excepted`.
  `:unrecovered` is the write-hazard record recovery clears after an install.  `:feed`
  holds the change feed's subscriptions, which a caller in this process registered.
  `:violations` is the log of what writes newly exposed; a restore exposes nothing
  (`settle/*rebuilding?*`), so an installed KB starts it empty, as a recovered one does."
  #{:taxonomy :provers :solver :settle-stats :chain-stats :qcn :qcn-joined :matches
    :closures :withdrawn :unrecovered :feed :violations})

(def taxonomy-side-slots
  "The taxonomy keys an image leaves as the open made them: the two callbacks
  `kb/open-kb` installs, which close over the KB, and the three side caches, which are
  atoms stamped by a relation's own `:gen`."
  [:supporter-filter-active? :supporter-visible? :closure-memo :vis-index :rewrite-order])

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
  "Does `kb` keep a reasoning image in its own directory — a `:disk-snapshot` KB (the one
  carrying a `:snapshot-dir`) over the durable record store, on the dense network?"
  [kb]
  (and (some? (:snapshot-dir kb))
       (instance? DiskRecordStore (:records kb))
       (instance? DenseTms (network kb))))

(defn refusal
  "Why `kb` may neither write nor install an image, or nil.  A prover or evaluatable
  beyond the defaults, or a solver other than the local one, runs code the source identity
  does not cover."
  [kb]
  (cond
    (not= provers/default-provers @(:provers kb)) :provers-registered
    (not= solve/local-solver @(:solver kb))       :solver-set
    :else                                         nil))

(defn- belief-built?
  "Does `kb` hold belief for every stored sentex?  Two conditions: no loader declared the
  belief unbuilt (`kb/note-hazards!`'s `:no-belief`), and the network holds a node per live
  sentex, which a recover makes and every assert makes.  A KB holding `assert-inert`
  sentexes has fewer nodes than records and fails the second; it takes no image, and
  never writes one of a network that does not cover its records."
  [kb]
  (and (not (:no-belief @(:unrecovered kb)))
       (== (dense/node-count (reasoning/tms kb)) (cap/count-sentexes (:records kb)))))

(defn writable?
  "May `kb`'s belief be written as an image: the dense network, no `refusal`, and a
  network that covers the records?"
  [kb]
  (and (instance? DenseTms (network kb)) (nil? (refusal kb)) (belief-built? kb)))

(defn- disk-dir ^File [kb] (io/file (str (:snapshot-dir kb)) dir-name))

(defn- section ^File [^File dir ^String nm] (io/file dir nm))

;; ---- the stamp --------------------------------------------------------------

(defn stamp
  "What an image of `kb` whose records fingerprint is `records` is valid against.
  `:libraries` is carried for a reader of the manifest; the source digest already covers
  it."
  [kb records]
  (let [sid (si/source-identity)]
    {:format    format-version
     :network   dense/image-version
     :records   records
     :source    (:digest sid)
     :libraries (:libraries sid)
     :policy    {:arbitrate           (boolean (checks/arbitrating? kb))
                 :assertive-arg-types (boolean (config/assertive-arg-types?))}}))

(defn decision
  "Why the image `manifest` describes cannot be installed into a KB whose stamp is `now`,
  or nil when it can.  One reason per mismatch class: `:absent`, `:format-changed`,
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
  read."
  [^File dir]
  (let [f (section dir "manifest.edn")]
    (when (.exists f)
      (try (edn/read-string (slurp f)) (catch Exception _ nil)))))

;; ---- writing ----------------------------------------------------------------

(defn- write-atomic!
  "Write `target` through `write-fn` of a sibling temp file, then rename it over `target`."
  [^File target write-fn]
  (let [tmp (File. (str target ".tmp"))]
    (try
      (write-fn tmp)
      (Files/move (.toPath tmp) (.toPath target)
                  (into-array CopyOption [StandardCopyOption/ATOMIC_MOVE
                                          StandardCopyOption/REPLACE_EXISTING]))
      (finally (.delete tmp)))))

(defn- data-out ^DataOutputStream [^File f]
  (DataOutputStream. (BufferedOutputStream. (FileOutputStream. f) 1048576)))

(defn- data-in ^DataInputStream [^File f]
  (DataInputStream. (BufferedInputStream. (FileInputStream. f) 1048576)))

(defn- state-of [kb]
  {:taxonomy (apply dissoc @(reasoning/taxonomy kb) taxonomy-side-slots)
   :atoms    (into {} (map (fn [a] [a @(get (reasoning/of kb) a)])) state-atoms)})

(defn write-sections!
  "Write `kb`'s network and state into `dir`, then a manifest carrying `stamp`, and return
  the manifest — or nil when `commit?`, asked after both sections are written, answers
  false.  The manifest is deleted first and written last, so from the first byte until the
  commit `dir` holds no image rather than an old manifest over new sections.  The caller
  holds the KB still; nothing here stops a writer."
  ([kb dir stamp] (write-sections! kb dir stamp (constantly true)))
  ([kb ^File dir stamp commit?]
   (let [mf (section dir "manifest.edn")]
     (.mkdirs dir)
     (.delete mf)
     (write-atomic! (section dir "network.bin")
                    (fn [f] (with-open [o (data-out f)] (dense/write-image (reasoning/tms kb) o))))
     (write-atomic! (section dir "state.nippy")
                    (fn [f] (with-open [o (data-out f)] (nippy/freeze-to-out! o (state-of kb)))))
     (when (commit?)
       (let [manifest (assoc stamp
                             :written-at (str (java.time.Instant/now))
                             :bytes {:network (.length (section dir "network.bin"))
                                     :state   (.length (section dir "state.nippy"))})]
         (write-atomic! mf (fn [^File f]
                             (binding [*print-length* nil *print-level* nil]
                               (spit f (pr-str manifest)))))
         manifest)))))

(defn save!
  "Write a `:disk-snapshot` KB's image into its own directory, and return the manifest —
  or nil when nothing was written: the KB does not keep one (`applies?`, `writable?`), or
  its records moved while the sections were written.  A failure is logged and returns nil:
  the image is a cache of a recover, and the next open recovers without it."
  [kb]
  (when (and (applies? kb) (writable? kb))
    (try
      (let [t0      (System/nanoTime)
            records (drs/reasoning-fingerprint (:records kb))
            moved?  #(not= records (drs/reasoning-fingerprint (:records kb)))
            m       (write-sections! kb (disk-dir kb) (stamp kb records) #(not (moved?)))]
        (if m
          (trove/log! {:level :info :id ::written
                       :msg (format "wrote the reasoning image for %s in %.0f ms"
                                    (:snapshot-dir kb) (/ (- (System/nanoTime) t0) 1e6))})
          (trove/log! {:level :warn :id ::records-moved
                       :msg (str "reasoning image for " (:snapshot-dir kb) " abandoned: the"
                                 " records moved while it was written")}))
        m)
      (catch Throwable t
        (trove/log! {:level :warn :id ::write-failed :error t
                     :msg (str "reasoning image for " (:snapshot-dir kb) " not written ("
                               (.getMessage t) ") — the next open recovers")})
        nil))))

(defn- save-at-close!
  "The close-time write: `save!` when the records moved since the image on disk, and only
  when the source identity still equals `source`, the digest belief was derived under."
  [kb source]
  (when (applies? kb)
    (let [m (read-manifest (disk-dir kb))]
      (cond
        (not= source (:digest (si/source-identity)))
        (trove/log! {:level :info :id ::source-moved
                     :msg (str "reasoning image for " (:snapshot-dir kb) " not refreshed at"
                               " close: the engine source changed since belief was derived")})

        (or (nil? m) (not= (:records m) (drs/reasoning-fingerprint (:records kb))))
        (save! kb)

        :else nil))))

(defn register-close!
  "Arrange for `kb`'s image to be refreshed when its directory closes.  `source` is the
  source identity's digest belief was derived under, and the digest now when the caller
  has none.  A no-op for a KB that does not keep an image, or that `refusal` names a
  reason for."
  [kb source]
  (when (and (applies? kb) (nil? (refusal kb)))
    (let [source (or source (:digest (si/source-identity)))]
      (disk/register-reasoning-image! (:snapshot-dir kb) #(save-at-close! kb source)))))

(defn register-rebuild-close!
  "Arrange for `kb`'s directory close to stop a belief rebuild and then refresh the image,
  for a KB whose open installed an image written under other engine source.  `stop!`
  returns once the rebuild has stopped.  `source` is a thunk: the digest belief was
  derived under once the rebuilt belief is installed, and nil while the installed image
  is still the one the earlier build wrote, in which case nothing is written."
  [kb stop! source]
  (disk/register-reasoning-image! (:snapshot-dir kb)
                                  #(do (stop!)
                                       (when-let [s (source)] (save-at-close! kb s)))))

(defn source-digest
  "The source identity's digest for the source on the classpath now."
  []
  (:digest (si/source-identity)))

;; ---- installing -------------------------------------------------------------

(defn- read-state [^File dir]
  (let [st (with-open [i (data-in (section dir "state.nippy"))] (nippy/thaw-from-in! i))]
    (when-not (and (map? (:taxonomy st)) (= (set state-atoms) (set (keys (:atoms st)))))
      (throw (IllegalStateException. "state.nippy does not hold the atoms this build images")))
    st))

(defn install-from!
  "Install the image in `dir` into `kb` in place of a recover.  `records-fn` returns the
  KB's records fingerprint in the form the image's manifest carries; it runs only once the
  cheaper conditions hold.  Returns `{:reasoning :installed :source d}`, or `{:reasoning :recover
  :reason r}` with the KB untouched — `r` one of `decision`'s reasons, a `refusal`,
  `:not-applicable`, `:network-populated` or `:unreadable`.  `:source` is the source
  identity's digest, which `register-close!` takes.

  `accept` is a set of `decision` reasons under which the image is installed anyway, and
  the result is then `{:reasoning :stale :reason r :source d :image-source d'}`, `d'` the
  digest the image was written under.  `vaelii.impl.recovery` passes `#{:source-differs}`
  under `:recover? :background` and rebuilds belief behind the installed image."
  ([kb dir records-fn] (install-from! kb dir records-fn #{}))
  ([kb ^File dir records-fn accept]
   (cond
     (not (instance? DenseTms (network kb))) {:reasoning :recover :reason :not-applicable}
     (jtms/any-node? (network kb))           {:reasoning :recover :reason :network-populated}
     (refusal kb)                         {:reasoning :recover :reason (refusal kb)}
     :else
     (let [now      (stamp kb (records-fn))
           manifest (read-manifest dir)
           why      (decision manifest now)]
       (if (and why (not (contains? accept why)))
         {:reasoning :recover :reason why :source (:source now)}
         (try
           (let [net (with-open [i (data-in (section dir "network.bin"))]
                       (dense/read-image! (dense/create-dense-tms) i))
                 st  (read-state dir)]
             (dense/copy-into! (reasoning/tms kb) net)
             (swap! (reasoning/taxonomy kb) merge (:taxonomy st))
             (doseq [[a v] (:atoms st)] (reset! (get (reasoning/of kb) a) v))
             (if why
               {:reasoning :stale :reason why :source (:source now)
                :image-source (:source manifest)}
               {:reasoning :installed :source (:source now)}))
           (catch Throwable t
             (trove/log! {:level :warn :id ::unreadable :error t
                          :msg (str "reasoning image in " dir " unreadable ("
                                    (.getMessage t) ") — recovering from the records")})
             {:reasoning :recover :reason :unreadable :source (:source now)})))))))

(defn install!
  "Install a `:disk-snapshot` KB's own image in place of a recover — `install-from!` over
  its directory, against the record store's `reasoning-fingerprint`, under `accept`."
  ([kb] (install! kb #{}))
  ([kb accept]
   (if (applies? kb)
     (install-from! kb (disk-dir kb) #(drs/reasoning-fingerprint (:records kb)) accept)
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
  "The bitmaps that state what network `t` believes: its nodes, and the IN, defeated and
  blocked sets."
  [^DenseTms t]
  [(.-nodes t) (.-in t) (.-defeated t) (.-blocked t)])

(defn compare-images
  "Compare the images in `a` and `b`, as `{:labels :network :state}`, each `:same` or
  `:differs`.  `:labels` compares what the two networks believe: the node set and the IN,
  defeated and blocked sets.  `:network` and `:state` compare the two files byte for byte,
  so they also differ on derivation depths, justification order and map iteration order,
  and none of those is belief.  Both images must carry this build's layout numbers, which
  the caller checks against the manifests before calling."
  [^File a ^File b]
  (let [same  (fn [x] (if x :same :differs))
        file= (fn [nm] (== -1 (Files/mismatch (.toPath (section a nm)) (.toPath (section b nm)))))]
    {:labels  (same (= (labels (read-network a)) (labels (read-network b))))
     :network (same (file= "network.bin"))
     :state   (same (file= "state.nippy"))}))
