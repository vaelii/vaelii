;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.rebase
  "Replacing a fork's base with an export dump while the fork keeps what it wrote: the
  fork's own premises and its removals of base premises are read by content, its own half
  is emptied, the dump is imported into the base's stores, belief is rebuilt over the
  merged contents, and the premises are asserted again.  A namespace of its own because it
  sits above both the dump importer and the overlay stores, which `vaelii.impl.kb`
  requires.  See docs/overlay.md, \"Replacing the base\"."
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
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.overlay.store :as ostore]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.io File]))

(defn fork?
  "Is `kb` a fork, an overlay over a frozen base?"
  [kb]
  (ostore/overlay-record-store? (:records kb)))

(defn- content-key
  "What a record is matched on across the two bases: its canonical sentence and context."
  [sx]
  [(sx/sentence-of sx) (:context sx)])

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
    (into #{} (keep #(some-> (p/get-sentex base %) content-key))
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
        owned   (into #{} (map content-key) own)]
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
  "`{content-key handle}` over every sentex `kb` holds."
  [kb]
  (let [rs (:records kb)]
    (into {} (keep #(some-> (p/get-sentex rs %) content-key (vector %)))
          (p/sentex-ids rs))))

(defn- replay!
  "Assert `captured` into `kb`, now over its new base, and return what landed.  The text
  forms go through `text/load-entries!`'s retry rounds, each form's reference digests
  checked (`text/digest-check`); a form still refused is reported under `:refused`, or
  `:unresolved` when a reference names no stored record.  Then each base premise the fork
  retracted that the new base holds is retracted again, and `on-replayed`, when given, is
  called with the record each premise was captured from and its new handle.  `:left` is
  what did not land, in `capture`'s shape: the refused entries, and the retractions of a
  sentence `kb` holds no record of."
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
                    :removed (into #{} (remove index) removed)}})))

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

(defn- delete-tree! [^File f]
  (when (.isDirectory f) (run! delete-tree! (.listFiles f)))
  (.delete f))

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
    (delete-tree! d)
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
  (delete-tree! (io/file dir delta-dir)))

(defn- clear-pending!
  "Delete the marker in `dir`, then the delta beside it."
  [dir]
  (let [mf (io/file dir pending-file)]
    (when (.exists mf)
      (.delete mf)
      (dfiles/fsync-dir! (str mf)))
    (delete-tree! (io/file dir delta-dir))))

(defn pending?
  "Does the durable fork `kb`'s directory hold the marker of a rebase that has not asserted
  the fork's writes again?"
  [kb]
  (boolean (when-let [dir (and (fork? kb) (:dir kb))]
             (.exists (io/file dir pending-file)))))

(defn finish-pending!
  "Assert again the writes a rebase of the durable fork `kb` left in its directory, and
  retract again the base premises it records.  The marker then keeps the forms refused and
  the retractions of a sentence `kb` holds no record of, the delta is deleted, and the
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
                                               " %d retractions naming no record")
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
         (observe/note-change)
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
