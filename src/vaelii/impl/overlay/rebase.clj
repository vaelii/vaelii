;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.rebase
  "Replacing a fork's base with an export dump while the fork keeps what it wrote: the
  fork's own premises and its removals of base premises are read by content, its own half
  is emptied, the dump is imported into the base's stores, belief is rebuilt over the
  merged contents, and the premises are asserted again.  And a durable fork's reopen over
  a base that grew or changed (`follow-base!`, `fire-arrivals!`).  A namespace of its own
  because it sits above the dump importer, the index writers and the overlay stores, which
  `vaelii.impl.kb` requires.  See docs/overlay.md, \"Replacing the base\", \"A base that
  grew between mounts\" and \"A base changed below its end\"."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.argtype-pass :as argpass]
            [vaelii.impl.disk.codec :as codec]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.io.import :as io-import]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.overlay.store :as ostore]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn fork?
  "Is `kb` a fork, an overlay over a frozen base?"
  [kb]
  (ostore/overlay-record-store? (:records kb)))

;; ---- what the fork wrote, by content ---------------------------------------

(defn own-records
  "The fork's own premises and inert sentexes, ascending by handle: each record of the own
  half that is a premise of the merged KB or holds no TMS node, less a copy of a base record
  equal to it, strength included (an override that changed nothing).  The records a delta
  export writes."
  [kb]
  (let [rs   (:records kb)
        base (:base rs)
        prem (set (p/premise-ids rs))
        tms  (reasoning/tms kb)]
    (into [] (keep (fn [h]
                     (when-let [rec (p/get-sentex rs h)]
                       (when (and (or (contains? prem h) (not (jtms/known-datum? tms h)))
                                  (not= rec (p/get-sentex base h)))
                         rec))))
          (sort (p/sentex-ids (:overlay rs))))))

(defn removed-keys
  "The content keys of the base premises the merged KB holds as no premise: the ones the
  fork retracted."
  [kb]
  (let [rs   (:records kb)
        base (:base rs)]
    (into #{} (keep #(some-> (p/get-sentex base %) ostore/sentex-content))
          (set/difference (set (p/premise-ids base)) (set (p/premise-ids rs))))))

(defn- form-key
  "What a captured form is matched on: its sentence and context."
  [form context]
  [(first (text/peel-form form)) context])

(defn- capture
  "What the fork wrote against its base, read by content before anything moves:
  `:entries`, the text forms of its premises and inert sentexes with the provenance, the
  reference digests and the record of each (`text/premise-entries`), the record only for a
  form one record holds; `:removed`, the content keys of the base premises it retracted.
  `held`, what a stopped rebase's marker keeps (`read-pending`), adds its entries, under
  `:held` too, less each the fork's own forms hold, and its retractions, less each of a
  sentence the fork's own records hold."
  [kb held]
  (let [rs      (:records kb)
        own     (own-records kb)
        [es _]  (text/premise-entries kb own)
        entries (mapv (fn [{:keys [context form handles digests]}]
                        {:form form :context context :digests (or digests [])
                         :provenance (p/get-provenance rs (first handles))
                         :record (when-not (next handles) (p/get-sentex rs (first handles)))})
                      es)
        mine    (into #{} (map #(form-key (:form %) (:context %))) entries)
        kept    (into [] (remove #(mine (form-key (:form %) (:context %)))) (:entries held))
        owned   (into #{} (map ostore/sentex-content) own)]
    {:entries (into entries kept)
     :held    kept
     :removed (into (removed-keys kb) (remove owned) (:removed held))}))

;; ---- replay ------------------------------------------------------------------

(defn- assert-opts
  "The assert opts that carry a record's provenance: its creator, and the rest of the map
  less the store's own entries, the spellings record and the inert mark."
  [prov o]
  (let [extras (dissoc prov :creator :inert integrate/spellings-key)]
    (cond-> (or o {})
      (:creator prov) (assoc :creator (:creator prov))
      (seq extras)    (assoc :provenance extras))))

(defn- content-index
  "`{content handle}` over every sentex `kb` holds."
  [kb]
  (let [rs (:records kb)]
    (into {} (keep #(some-> (p/get-sentex rs %) ostore/sentex-content (vector %)))
          (p/sentex-ids rs))))

(defn- replay!
  "Assert `captured` into `kb`, now over its new base, and return what landed.  The text
  forms go through `text/load-entries!`'s retry rounds, each form's reference digests
  checked (`text/digest-check`); a form still refused is reported under `:refused`, or
  `:unresolved` when a reference names no stored record.  Then each base premise the fork
  retracted that the new base holds is retracted again, and `on-replayed`, when given, is
  called with the record each premise was captured from and its new handle.  `:left` is
  what did not land, in `capture`'s shape: the refused entries, and the retractions of a
  sentence `kb` holds no premise of."
  [kb {:keys [entries removed]} {:keys [assert! assert-inert! retract! on-replayed]}]
  (let [key-of  form-key
        prov-of (into {} (map (fn [{:keys [form context provenance]}]
                                [(key-of form context) provenance]))
                      entries)
        rec-of  (if on-replayed
                  (into {} (keep (fn [{:keys [form context record]}]
                                   (when record [(key-of form context) record])))
                        entries)
                  {})
        refused (volatile! [])
        landed  (volatile! {})]
    (text/load-entries!
     (fn [s c o]
       (let [h (assert! s c (assert-opts (prov-of [s c]) o))]
         (when-let [r (and (integer? h) (rec-of [s c]))] (vswap! landed assoc [s c] [r h]))
         h))
     (fn [s c] (assert-inert! s c))
     (mapv (juxt :form :context :digests) entries)
     (fn [[form context] e]
       (vswap! refused conj {:form form :context context :type (:type (ex-data e))}))
     (text/digest-check kb))
    (let [{unresolved true others false}
          (group-by #(= :unresolved-reference (:type %)) @refused)
          index     (if (seq removed) (content-index kb) {})
          premises  (set (p/premise-ids (:records kb)))
          retracted (into [] (comp (keep index) (filter premises)) (sort-by nm/print-key removed))
          missed    (into #{} (map (juxt :form :context)) @refused)]
      (run! retract! retracted)
      (doseq [[r h] (vals @landed)] (on-replayed r h))
      {:asserted   (- (count entries) (count @refused))
       :refused    (vec others)
       :unresolved (mapv #(dissoc % :type) unresolved)
       :retracted  (count retracted)
       :left       {:entries (filterv #(missed [(:form %) (:context %)]) entries)
                    :removed (into #{} (remove #(contains? premises (index %))) removed)}})))

;; ---- the pending delta -----------------------------------------------------------

(def ^:private pending-file
  "The marker a durable fork's directory holds while a rebase has emptied, or may have
  emptied, its own half and has not yet asserted its writes again."
  "rebase-pending.nippy")

(def ^:private delta-dir
  "The text KB beside the marker, holding the fork's writes as a delta export writes them."
  "rebase-delta")

(def ^:dynamic *phase-hook*
  "A `(fn [phase])` `rebase!` calls at `:emptied`, after the own half is emptied and before
  the base is refilled, and at `:refilled`, after the base is refilled and before the
  writes are asserted again; `finish-pending!` calls it at `:pending`, before it asserts a
  stopped rebase's writes again; or nil.  A test binds it to throw there, which leaves the
  directory as a crash at that point leaves it."
  nil)

(defn- write-marker!
  "Write the marker into `dir`, atomically: the content keys of the retracted base premises,
  each entry's provenance and captured record, and the `held` entries the delta does not
  hold."
  [dir {:keys [entries removed]} held]
  (dfiles/write-nippy-atomic!
   (str (io/file dir pending-file))
   {:removed    removed
    :held       (mapv (juxt :form :context :digests) held)
    :provenance (into {} (map (juxt (juxt :form :context) :provenance)) entries)
    :records    (into {} (keep #(when-let [r (:record %)]
                                  [[(:form %) (:context %)] (codec/encode-sentex r)]))
                      entries)}))

(defn- write-pending!
  "Write `captured` into the durable fork `kb`'s directory `dir`: the fork's own records as
  a delta text KB (`text/write-kb!` over `own-records`, what `export-text! {:delta? true}`
  writes) with each file fsynced, then the marker, holding `captured`'s `:held` entries
  beside them.  The marker is written last, so a directory holding it holds the whole
  delta."
  [kb dir captured]
  (let [d (io/file dir delta-dir)]
    (dfiles/delete-tree! d)
    (let [{:keys [files]} (text/write-kb! kb d {:delta? true} (own-records kb))]
      (run! #(dfiles/fsync-file! (str (io/file d ^String %))) (conj files text/manifest-file))
      (dfiles/fsync-dir! (str d)))
    (write-marker! dir captured (:held captured))))

(defn- read-pending
  "The capture the marker and delta in `dir` hold, in `capture`'s shape, or nil when `dir`
  holds no marker."
  [dir]
  (let [mf (io/file dir pending-file)]
    (when (.exists mf)
      (let [{:keys [removed held provenance records]} (dfiles/read-nippy-file (str mf) {})
            d     (io/file dir delta-dir)
            forms (if (seq (text/kb-files d)) (:entries (text/entries d)) [])]
        {:entries (mapv (fn [[form context digests]]
                          {:form form :context context :digests digests
                           :provenance (get provenance [form context])
                           :record (some-> (get records [form context]) codec/decode-sentex)})
                        (distinct (map (fn [[f c ds]] [f c (or ds [])]) (concat forms held))))
         :removed (set removed)}))))

(defn- keep-pending!
  "Rewrite the marker in `dir` to hold `left` alone, then delete the delta.  A crash between
  the two leaves forms in both, and `read-pending` reads each once."
  [dir left]
  (write-marker! dir left (:entries left))
  (dfiles/delete-tree! (io/file dir delta-dir)))

(defn- clear-pending!
  "Delete the marker in `dir`, then the delta beside it."
  [dir]
  (let [mf (io/file dir pending-file)]
    (when (.exists mf)
      (.delete mf)
      (dfiles/fsync-dir! (str mf)))
    (dfiles/delete-tree! (io/file dir delta-dir))))

(defn pending?
  "Does the durable fork `kb`'s directory hold the marker of a rebase that has not asserted
  the fork's writes again?"
  [kb]
  (boolean (when-let [dir (and (fork? kb) (:dir kb))]
             (.exists (io/file dir pending-file)))))

(defn finish-pending!
  "Assert again the writes a rebase of the durable fork `kb` left in its directory, and
  retract again the base premises it records.  The marker then keeps the forms refused and
  the retractions of a sentence `kb` holds no premise of, the delta is deleted, and the
  marker goes too when it keeps nothing.  Returns `replay!`'s summary with `:kept`, the
  retractions kept; nil when the directory holds no marker.  `fns` are `rebase!`'s."
  [kb fns]
  (when-let [captured (and (pending? kb) (read-pending (:dir kb)))]
    (when-let [hook *phase-hook*] (hook :pending))
    (let [{:keys [left] :as landed} (replay! kb captured fns)
          landed (-> landed (dissoc :left) (assoc :kept (vec (sort-by nm/print-key (:removed left)))))]
      (if (some seq (vals left))
        (keep-pending! (:dir kb) left)
        (clear-pending! (:dir kb)))
      (trove/log! {:level (if (some seq (vals left)) :warn :info)
                   :id    ::pending-replayed
                   :msg   (cond-> (format (str "rebase: %s held the writes of a rebase that did not"
                                               " finish; %,d asserted again, %d refused, %d naming a"
                                               " record no longer held, %d base premises retracted,"
                                               " %d retractions naming no premise")
                                          (:dir kb) (long (:asserted landed))
                                          (count (:refused landed)) (count (:unresolved landed))
                                          (long (:retracted landed)) (count (:kept landed)))
                            (some seq (vals left))
                            (str "; the marker keeps the refused forms and those retractions"
                                 " for the next rebase"))
                   :data  landed})
      landed)))

;; ---- the base ------------------------------------------------------------------

(defn- refill-base!
  "Import the dump at `dir` into the base's stores, as a second KB opened from the opts
  the base was mounted from, which reaches the stores the fork reads through the store
  registries.  The import stores the records, the justifications, the premise marks and
  the index, and recovers nothing (`:belief? :stored`): the fork's belief is rebuilt over
  the merged contents afterwards.  The base KB records the dump's reasoner set."
  [base-opts dir meta {:keys [drop-principal? report-every on-progress]} {:keys [recover reindex]}]
  (let [bkb (kb/open-kb (assoc base-opts :recover? false :reasoners :stored) recover reindex)]
    (p/clear-records! (:records bkb))
    (p/clear-index! (:index bkb))
    (some->> (:reasoners meta) set (kb/record-reasoners! bkb))
    (io-import/import-dump bkb dir (cond-> {:belief? :stored :drop-principal? (boolean drop-principal?)}
                                     report-every (assoc :report-every report-every)
                                     on-progress  (assoc :on-progress on-progress)))))

(defn- refuse-unowned!
  [kb]
  (when-not (:base-opts (:records kb))
    (throw (ex-info (str "this fork's base is the stores of the KB it was forked from, and"
                         " a base refresh writes its base.  Import into that KB, or open the"
                         " fork from opts ({:backend :overlay :base … :overlay …}) so the"
                         " base is the fork's own.")
                    {:type :frozen-base :op "import!"}))))

(defn rebase!
  "Install the export dump at `dir` as fork `kb`'s base, keeping what the fork wrote, and
  return the import's summary with `:rebase` added: `{:asserted n :refused [..]
  :unresolved [..] :retracted n :elapsed-ms n}`.

  The fork's premises, inert sentexes and retractions of base premises are read by content
  first, and a durable fork writes them to its directory as a delta with a marker
  (`write-pending!`).  Then the own half is emptied (`ostore/rebase!`), the dump is imported
  into the base's stores, belief is rebuilt over the merged contents (`recovery/rebuild!`),
  what the fork wrote is asserted again (`replay!`), and the marker is deleted.  A marker
  an earlier rebase left is finished first (`finish-pending!`), and what it keeps joins the
  capture.  `fns` is `{:assert! :assert-inert! :retract! :recover :reindex :on-replayed}`.

  Refused before the first write: a fork whose base arrived as another KB's stores
  (`:frozen-base`), a dump this build does not read, and a dump whose reasoner set `kb`
  does not register (`:reasoner-mismatch`, as `import!` refuses it)."
  [kb dir opts fns]
  (io-import/check-import-opts! opts)
  (when-not (true? (:belief? opts true))
    (throw (ex-info (str ":rebase? rebuilds the fork's belief over the new base, and :belief? "
                         (pr-str (:belief? opts)) " asks for an import that does not")
                    {:type :unknown-option :mismatch :conflict :option :belief?
                     :value (:belief? opts)})))
  (when-not (or (nil? (:on-replayed fns)) (ifn? (:on-replayed fns)))
    (throw (ex-info (str ":on-replayed is called with each replayed record and its handle,"
                         " and " (pr-str (:on-replayed fns)) " is no fn")
                    {:type :unknown-option :mismatch :bad-value :option :on-replayed
                     :value (:on-replayed fns)})))
  (refuse-unowned! kb)
  (let [t0   (System/nanoTime)
        meta (io-import/read-meta dir)
        _    (io-import/check-dump! meta)
        regs (io-import/dump-reasoners kb meta dir opts)
        rs   (:records kb)
        own  (:dir kb)
        hook (or *phase-hook* (fn [_]))]
    (ostore/excluding-readers
     rs
     (fn []
       (finish-pending! kb fns)
       (let [captured (capture kb (when own (read-pending own)))
             _        (when own (write-pending! kb own captured))
             summary  (ostore/rebase!
                       rs
                       (fn []
                         (some-> (mount/kv-backend-of (:index kb)) :overlay p/kv-clear!)
                         (argpass/clear-owed! kb)
                         (hook :emptied)
                         (refill-base! (:base-opts rs) dir meta opts fns)))]
         (hook :refilled)
         (observe/note-change (:clock kb))
         (recovery/rebuild! kb)
         (when regs (kb/add-reasoners! kb regs))
         (let [landed (dissoc (replay! kb captured fns) :left)
               _      (when own (clear-pending! own))
               ms     (long (/ (- (System/nanoTime) t0) 1000000))
               result (assoc landed :elapsed-ms ms)]
           (trove/log! {:level (if (some seq [(:refused landed) (:unresolved landed)]) :warn :info)
                        :id    ::rebased
                        :msg   (format (str "rebase: the base holds %,d sentexes from %s; the fork's"
                                            " %,d writes were asserted again, %d refused, %d naming a"
                                            " record no longer held, %d base premises retracted, in %d ms")
                                       (long (:sentexes summary)) dir (long (:asserted landed))
                                       (count (:refused landed)) (count (:unresolved landed))
                                       (long (:retracted landed)) ms)
                        :data  result})
           (assoc summary :rebase result)))))))

(defn- mint-concluded
  "The handles the justifications among `arrivals` conclude under a mint rule
  (`kb/records-mint-kind`), read off `records`."
  [records arrivals]
  (let [kind (memoize #(kb/records-mint-kind records %))]
    (into #{} (keep #(when-let [j (p/get-justification records %)]
                       (when (kind (:informant j)) (:consequence j))))
          arrivals)))

(defn- follow-ops
  "The `kv-batch` ops that take the fork `kb`'s index from the base it describes to that
  base plus `arrivals`, the handles the base gained.  One scratch layer takes the arrivals'
  sentexes out of the base's index, which then holds what it held before them; the fork's
  own index half goes over that; a second scratch layer indexes the arrivals over the
  result.  The ops are the difference between that and the fork's index at each key a
  scratch layer wrote (`okv/align-ops`).  The re-check index keeps the base's postings."
  [kb arrivals]
  (let [fork   (mount/kv-backend-of (:index kb))
        brs    (:base (:records kb))
        s1     (mem/->MemoryKvBackend (atom {}))
        s2     (mem/->MemoryKvBackend (atom {}))
        before (okv/overlay-kv s1 (:base fork))
        after  (okv/overlay-kv s2 (frozen/frozen-kv (okv/overlay-kv (:overlay fork)
                                                                    (frozen/frozen-kv before))))
        [i1 i2 bidx] (map kv/->KvIndexStore [before after (:base fork)])
        sxs    (into [] (keep #(when-let [sx (p/get-sentex brs %)] [% sx])) arrivals)
        minted (mint-concluded brs arrivals)]
    (doseq [[h sx] (rseq sxs)]
      (p/unindex-sentex! i1 sx h)
      (when (rules/rule? sx)
        (rules/unindex-rule! i1 h (rules/antecedent-keys (:antecedent sx))
                             (rules/consequent-index-pred sx) (rules/consequent-heads sx)
                             (:context sx)))
      (special/unpost-mint! i1 (sx/sentence-of sx) (:context sx) h)
      (tax/retire-stored-supporter! i1 h))
    (doseq [[h sx] sxs]
      (reindex/index-one! i2 sx h)
      (when (contains? minted h) (special/post-mint! i2 (sx/sentence-of sx) (:context sx) h))
      (tax/copy-stored-supporter! bidx i2 h (:context sx)))
    (okv/align-ops fork after [s1 s2])))

(defn- base-handle-of
  "The handle at which the base holds sentex content `[sentence context]`, or nil: the
  candidates at its trie leaf, each checked against the record."
  [brs bidx [s c :as content]]
  (some #(when (= content (some-> (p/get-sentex brs %) ostore/sentex-content)) %)
        (reads/as-stored-leaf bidx (sx/path (sx/sentex s c)))))

(defn- resolve-justifications
  "`{named handle  base handle}` for the named justification handles `hs`: each part of a
  recorded content resolved to its handle (`resolve-content`), then one pass over the base's
  justifications for the one holding them.  A handle absent from the answer departed."
  [rs brs hs resolve-content]
  (let [want (into {} (keep (fn [h]
                              (let [[_ i as c] (ostore/named-content rs h)
                                    r   #(if (vector? %) (resolve-content %) %)
                                    k   [(r i) (mapv r as) (r c)]]
                                (when (and (some? (k 0)) (every? some? (k 1)) (some? (k 2)))
                                  [k h]))))
                   hs)]
    (if (empty? want)
      {}
      (into {} (keep #(when-let [j (p/get-justification brs %)]
                        (when-let [h (want [(:informant j) (vec (:antecedents j)) (:consequence j)])]
                          [h %])))
            (p/justification-ids brs)))))

(defn- resolve-moved
  "`{named handle  base handle or nil}` for each handle the fork `kb` names whose content
  the base no longer holds there (`ostore/moved-handles`): the base handle now holding that
  content, nil when the base holds it nowhere."
  [kb]
  (let [rs    (:records kb)
        brs   (:base rs)
        bidx  (kv/->KvIndexStore (:base (mount/kv-backend-of (:index kb))))
        moved (ostore/moved-handles rs)
        kind  #(first (ostore/named-content rs %))
        r     #(base-handle-of brs bidx %)
        sxs   (into {} (map (fn [h] [h (r (subvec (ostore/named-content rs h) 1))]))
                    (filter #(= :sentex (kind %)) moved))
        jds   (filterv #(= :justification (kind %)) moved)]
    (merge sxs (zipmap jds (repeat nil)) (resolve-justifications rs brs jds r))))

(defn- rewrite-handles
  "`sentence` with each handle `m` maps replaced by its image, canonical (`sx/canon`); nil
  when `m` maps one it names to nil.  A handle is a `(sentexHandle n)` term, or the bare
  integer of an `(except n)`."
  [sentence m]
  (let [gone? (volatile! false)
        image (fn [h] (if (contains? m h) (or (m h) (do (vreset! gone? true) h)) h))
        walk  (fn walk [x] (cond (sx/sentex-handle? x) (sx/sentex-handle (image (sx/handle-id x)))
                                 (sequential? x)       (map walk x)
                                 :else                 x))
        out   (sx/canon (if (and (= sx/except-functor (first sentence)) (integer? (second sentence)))
                          (list (first sentence) (image (second sentence)))
                          (walk sentence)))]
    (when-not @gone? out)))

(defn- rewrite-sentex
  "`sx` naming the images `m` gives its handles, or nil when one departed."
  [sx m]
  (let [s (sx/sentence-of sx)]
    (if-not (sx/names-a-handle? s)
      sx
      (when-let [s' (rewrite-handles s m)]
        (if (rules/rule? sx)
          (merge sx (select-keys (sx/sentex s' (:context sx)) [:antecedent :consequent :varmap]))
          (assoc sx :sentence s'))))))

(defn- remap-plan
  "The target state of the fork `kb`'s record half under `m` (`resolve-moved`), as
  `ostore/apply-remap!` takes it.  Each reference to a moved handle follows it.  What
  names a departed handle is dropped, with each fork justification resting on a dropped
  sentence.  docs/overlay.md, \"A base changed below its end\"."
  [kb m]
  (let [rs      (:records kb)
        own     (:overlay rs)
        img     #(if (contains? m %) (m %) %)
        premise (set (p/premise-ids own))
        sxs     (for [h (sort (p/sentex-ids own)) :let [sx (p/get-sentex own h)] :when sx]
                  (let [to (img h) sx' (when to (rewrite-sentex sx m))]
                    {:from h :to (when sx' to) :sx (some-> sx' (assoc :id to))
                     :changed? (or (not= to h) (not (identical? sx sx')))}))
        dropped (into #{} (comp (remove :to) (map :from)) sxs)
        jds     (for [h (sort (p/justification-ids own)) :let [j (p/get-justification own h)] :when j]
                  (let [refs (cons (:consequence j) (:antecedents j))
                        j'   (when (and (not-any? dropped refs) (some? (img h))
                                        (every? some? (map img refs))
                                        (or (not (integer? (:informant j))) (some? (img (:informant j)))))
                               (cond-> (assoc j :id (img h)
                                              :antecedents (mapv img (:antecedents j))
                                              :consequence (img (:consequence j)))
                                 (integer? (:informant j)) (update :informant img)))]
                    {:from h :to (:id j') :rec j' :changed? (not= j j')}))
        writes  (fn [rows rec]
                  (let [rows (filter :changed? rows)]
                    (merge (into {} (map (fn [r] [(:from r) nil])) rows)
                           (into {} (keep (fn [r] (when (:to r) [(:to r) (rec r)]))) rows))))
        moved   (keys m)
        named   (merge (into {} (map (fn [h] [h nil])) moved)
                       (into {} (keep (fn [h] (when-let [to (m h)] [to (ostore/named-content rs h)])))
                             moved))]
    {:sentexes       (writes sxs :sx)
     :justifications (writes jds :rec)
     :premises       (into {} (keep (fn [{:keys [from to changed?]}]
                                      (when (and changed? to (contains? premise from))
                                        [to (p/premise-strength own from)])))
                           sxs)
     :provenance     (merge (into {} (map (fn [h] [h nil])) (concat dropped moved))
                            (into {} (keep (fn [h] (when-let [v (and (m h) (p/get-provenance own h))]
                                                     [(m h) v])))
                                  moved))
     :sets           (into {} (map (fn [[k hs]] [k (into #{} (keep img) hs)]))
                           (ostore/bookkeeping-sets rs))
     :named          named}))

(defn- replay-ops
  "The `kv-batch` ops that take the fork `kb`'s index to the one its rewritten records give
  over its base.  A scratch layer over the base's index takes out each base record the fork
  tombstoned.  It takes in each record the fork minted, as `reindex` posts them, and the
  fork's `:exception-index` postings under `m`.  The ops make the fork's index equal the
  scratch layer's at each key either one wrote (`okv/align-ops`)."
  [kb m]
  (let [fork  (mount/kv-backend-of (:index kb))
        rs    (:records kb)
        brs   (:base rs)
        s     (mem/->MemoryKvBackend (atom {}))
        src   (okv/overlay-kv s (:base fork))
        [i old] (map kv/->KvIndexStore [src fork])
        img   #(if (contains? m %) (m %) %)
        own   (sort (remove #(p/get-sentex brs %) (p/sentex-ids (:overlay rs))))
        minted (into #{} (keep #(when-let [j (p/get-justification rs %)]
                                  (when (kb/records-mint-kind rs (:informant j)) (:consequence j))))
                     (p/justification-ids (:overlay rs)))]
    (doseq [h (sort (:sx-tombstoned (ostore/bookkeeping-sets rs)))
            :let [sx (p/get-sentex brs h)] :when sx]
      (reindex/unindex-one! i sx h))
    (doseq [h own :let [sx (p/get-sentex rs h)] :when sx]
      (reindex/index-one! i sx h)
      (when (contains? minted h) (special/post-mint! i (sx/sentence-of sx) (:context sx) h))
      (tax/copy-stored-supporter! old i h (:context sx)))
    (doseq [[k {:keys [added removed tombstoned?]}] (okv/own-deltas (:overlay fork) :exception-index)]
      (when tombstoned? (p/kv-delete src k))
      (doseq [h added :let [h (img h)] :when h] (p/kv-add-to-set src k h))
      (doseq [h removed :let [h (img h)] :when h] (p/kv-remove-from-set src k h)))
    (okv/align-ops fork src [(:overlay fork) s])))

(defn- remap!
  "Follow a base changed below the fork `kb`'s recorded end (`ostore/remap-owed`).  Resolve
  each moved named handle by content, then record and apply the record half's rewrite.  The
  index ops and the firings of every record the fork holds become a pending catch-up, which
  `follow-base!` applies.  Each step is recorded before it applies."
  [kb]
  (let [rs   (:records kb)
        m    (or (:m (:plan (ostore/remap-owed rs))) (resolve-moved kb))
        plan (or (:plan (ostore/remap-owed rs))
                 (let [p (assoc (remap-plan kb m) :m m)] (ostore/begin-remap! rs p) p))]
    (ostore/apply-remap! rs plan)
    (ostore/owe-follow! rs (vec (sort (p/sentex-ids (:overlay rs)))))
    (ostore/begin-follow! rs (replay-ops kb (:m plan)))
    (ostore/end-remap! rs)))

(defn- record-all-named!
  "Name every base handle the fork `kb` refers to (`ostore/record-all-named!`).  Those are
  the handles its own records hold or name, the members of its bookkeeping sets, and the
  handles its index half posts or removes (`okv/own-handles`).  An index half `reindex`
  rebuilt names none.  One pass over the fork's own half."
  [kb]
  (let [rs  (:records kb)
        own (:overlay rs)]
    (ostore/record-all-named!
     rs (concat (p/sentex-ids own)
                (mapcat #(some-> (p/get-sentex own %) ostore/named-in-sentex) (p/sentex-ids own))
                (p/justification-ids own)
                (mapcat #(some-> (p/get-justification own %) ostore/named-in-justification)
                        (p/justification-ids own))
                (apply concat (vals (ostore/bookkeeping-sets rs)))
                (let [ix (:overlay (mount/kv-backend-of (:index kb)))]
                  (when-not (okv/index-cleared? ix) (okv/own-handles ix)))))))

(defn follow-base!
  "Bring the index of `kb`, a durable fork, to the base its mount accepted.  Apply the ops
  a catch-up left pending (`ostore/pending-follow`).  Then follow a base changed below its
  end (`remap!`), or record and apply the ops for the records the base gained
  (`ostore/follow-owed`, `follow-ops`).  A fork whose bookkeeping does not name every base
  handle it refers to names them (`record-all-named!`).  `kb/open-kb` calls it first."
  [kb]
  (let [rs   (:records kb)
        fork (mount/kv-backend-of (:index kb))]
    (when (and (ostore/overlay-record-store? rs) (okv/overlay-kv? fork))
      (let [apply! #(do (p/kv-batch fork (:ops (ostore/pending-follow rs)))
                        (ostore/end-follow! rs))]
        (when (ostore/pending-follow rs) (apply!))
        (if (ostore/remap-owed rs)
          (do (remap! kb) (apply!))
          (when-let [{:keys [arrivals]} (ostore/follow-owed rs)]
            (ostore/begin-follow! rs (follow-ops kb arrivals))
            (apply!)))
        (when (and (:durable? rs) (not (ostore/names-complete? rs)))
          (record-all-named! kb))))))

(defn firings-owed
  "The base handles whose rule firings the fork `kb` owes (`fire-arrivals!`), or nil."
  [kb]
  (when (fork? kb) (seq (ostore/firings-owed (:records kb)))))

(defn fire-arrivals!
  "Run in the fork `kb` what an assert of each base record `hs` names would run past its
  store and index: a rule's and an `exceptWhen`'s re-check postings, each sentence's
  re-check triggers, then a chaining run from the believed ones and a settle.  Drops the
  owed firings."
  [kb hs]
  (let [rs (:records kb)]
    (doseq [h hs :let [sx (p/get-sentex rs h)] :when sx]
      (cond (rules/rule? sx)                     (special/index-rule-sentex kb h sx)
            (sx/exceptWhen-meta? (:sentence sx)) (special/index-exceptWhen-meta kb sx))
      (special/recheck-on-sentence kb (sx/sentence-of sx)))
    (settle/rechain-seeds kb hs)
    (settle/settle kb)
    (ostore/firings-done! rs)))
