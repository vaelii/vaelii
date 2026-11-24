;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.reindex
  "Rebuild the index store wholesale from the record store.

  Everything the index holds — the trie, the secondary roots, the rule index, the
  exception re-check index, the inverted term index — is *derived* from the
  stored sentexes, and the mint family from the stored justifications, so the repair
  for a damaged or stale index is mechanical: clear it and re-derive every entry.  Three situations need it:

  * a crash between the record write and the index pipeline (`assert` spans both
    stores; each side is a single pipeline, but the boundary between them remains)
    — the orphaned record is unfindable, and re-asserting its sentence
    would mint a *second* handle for the same canonical form;
  * an index whose key shapes are not this build's (`kv/index-layout-version`): a
    lookup finds no key and answers nothing, which is fail-safe and undiagnosable, so
    a persistent KB needs this rebuild;
  * any suspicion that counts and extents have drifted: a rebuild is cheaper
    than an audit.

  Run `core/recover` afterwards: it rebuilds the TMS and taxonomy from the
  stores, and parts of that rebuild (`rebuild-taxonomy` reads the predicate extents)
  read the very index this restores.

  Named bare, like `recover`: the `!` convention marks destruction of stored
  *knowledge*, and this destroys only derived state and recreates it from the
  records, which stay untouched."
  (:require [vaelii.impl.capabilities :as cap]
            [vaelii.impl.except :as exc]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]))

(defn index-one!
  "Index one stored sentex `sx` at handle `h` into `index`: its positional / term / root
  entry (`index-sentex`), plus, when `sx` is a rule, the rule-predicate entry
  `special/index-rule-sentex` posts.  The re-check index is posted once every record is
  in (`special/post-taxonomy-supporters!`), since a rule's keys read the taxonomy.  This
  is the per-sentex core `reindex` folds over every live handle, and the core the
  importer's inline bulk load calls with the record already in hand.  Returns true iff
  `sx` is a rule (the caller's rule tally)."
  [index sx h]
  (p/index-sentex index sx h)
  (let [rule? (rules/rule? sx)]
    (when rule?
      (rules/index-rule index h
                        (rules/antecedent-keys (:antecedent sx))
                        (rules/consequent-index-pred sx)
                        (rules/consequent-heads sx)
                        (:context sx)))
    rule?))

(defn unindex-one!
  "Take stored sentex `sx` at handle `h` out of `index`: the mirror of `index-one!` for a
  record or a rule, plus its mint family entry and the taxonomy supporters it posted.
  Reads no belief, so a KB whose network is not built can take a record out
  (`vaelii.impl.record-edit`).  An `exceptWhen` meta-sentex is not handled: its departure
  re-posts the predicates its rule's other exceptions still watch."
  [index sx h]
  (p/unindex-sentex! index sx h)
  (when (rules/rule? sx)
    (rules/unindex-rule! index h
                         (rules/antecedent-keys (:antecedent sx))
                         (rules/consequent-index-pred sx)
                         (rules/consequent-heads sx)
                         (:context sx))
    (when-let [ks (seq (concat (when (rules/rechecked? sx) (rules/recheck-predicates sx))
                               (rules/nonempty-recheck-predicates sx)))]
      (rules/unindex-exception! index h ks)))
  (special/unpost-mint! index (sx/sentence-of sx) (:context sx) h)
  (tax/retire-stored-supporter! index h)
  nil)

(defn- mint-conclusions
  "The handles the stored justifications of a mint (`kb/records-mint-kind`) conclude: one
  fetch per stored justification and per distinct rule-handle informant, chunk-hinted as `recover`'s walk is."
  [records]
  (with-open [r (progress/start ::read-justifications
                                "reindex: read the justifications"
                                (cap/count-justifications records))]
    (into #{}
          (comp (keep #(do (progress/tick! r) (p/get-justification records %)))
                (filter (let [kind (memoize #(kb/records-mint-kind records %))]
                          #(some? (kind (:informant %)))))
                (map :consequence))
          (cap/hinting (cap/justification-prefetcher records) cap/recovery-hint-chunk
                       (p/justification-ids records)))))

(defn reindex
  "Flush the index store and rebuild every entry from the stored sentexes: each record's
  own entries (`index-one!`) and its mint family entry, then the taxonomy's supporter
  families and the re-check index (`special/post-taxonomy-supporters!`).  The mint
  family is read from the stored justifications, walked first, so each mint is posted
  from the record the sentex walk holds.  Returns {:sentexes n :rules n}."
  [kb]
  (let [records (:records kb)
        index   (:index kb)
        minted  (mint-conclusions records)]
    (p/clear-index! index)
    (kb/forget-mint-rules! kb)
    (kb/forget-engine-rules! kb)
    ;; the index moves wholesale here rather than through the per-sentex choke point, so
    ;; the clock a resident derived structure is keyed by is bumped by hand — as
    ;; `core/clear!` does, and for the same reason
    (observe/note-change (:clock kb))
    (let [counts
          (with-open [r (progress/start ::index-sentexes
                                        "reindex: index the sentexes"
                                        (cap/count-sentexes records))]
            (reduce
             (fn [acc h]
               (progress/tick! r)
               (if-let [sx (p/get-sentex records h)]
                 (do (when (contains? minted h)
                       (special/post-mint! index (sx/sentence-of sx) (:context sx) h))
                     (cond-> (update acc :sentexes inc)
                       (index-one! index sx h) (update :rules inc)))
                 acc))
             {:sentexes 0 :rules 0}
             ;; A walk that fetches every live record, so a store that can warm many at one cost
             ;; is told a chunk ahead (`protocols/Prefetching`).  Unconditional, unlike the query path's
             ;; hint: this walk consumes every handle it is given, so a hint here can save round
             ;; trips and cannot waste one.  Nil for every store that does not prefetch, which is
             ;; every store the engine ships, and then this is `(p/sentex-ids records)`.
             (cap/hinting (cap/prefetcher records) cap/recovery-hint-chunk (p/sentex-ids records))))]
      (exc/note-rewritten kb)
      (special/post-taxonomy-supporters! kb)
      counts)))
