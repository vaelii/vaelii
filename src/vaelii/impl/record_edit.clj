;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.record-edit
  "Premise additions, premise removals and rule direction changes applied to the records
  of a KB whose belief is not built (`apply!`), and the sweep that follows the rebuild
  (`sweep!`): `vaelii.core/edit-records!` and `vaelii.core/settle-record-edits!` are the
  entry points.  See docs/storage.md, \"Editing the records of a KB without belief\"."
  (:require [clojure.string :as str]
            [vaelii.impl.argtype-pass :as argpass]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat-maintenance :as nat-maint]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

;; ---- the batch --------------------------------------------------------------------

(defn- check-kb!
  "Refuse a KB that has belief: the batch skips the checks, the dependency sweep and the
  settle that belief owes, so it runs only where there is none."
  [kb]
  (let [hz (kb/write-hazards kb)]
    (when (or (not (:no-belief hz)) (:stale-belief hz))
      (throw (ex-info (str "edit-records! writes records with no checks, no dependency sweep and no"
                           " settle, so it runs only on a KB whose belief is not built: open the"
                           " store with {:recover? false}.  This KB "
                           (if (:stale-belief hz)
                             "answers from an installed reasoning image"
                             "has belief")
                           "; edit! is the write for it.")
                      {:type :belief-built :operation "edit-records!"
                       :hazards (vec (sort (keys hz)))})))))

(defn- removable-problem
  "Why the record `sx` at handle `h` cannot be removed at record level, or nil.  The
  departure of an `except`, a `defeat` or an `exceptWhen` meta-sentex re-posts what the
  remaining ones still name, which `reindex/unindex-one!` does not do."
  [h sx]
  (let [s (sx/sentence-of sx)
        f (nm/functor s)]
    (when (or (sx/exceptWhen-meta? s) (= sx/except-functor f) (= sx/defeat-functor f))
      {:type :record-edit-unsupported :handle h :functor f :operation "edit-records!"
       :message (str "handle " h " is " (pr-str f) " record; its departure re-posts the index"
                     " entries the remaining ones need, which edit-records! does not compute."
                     "  Remove it with edit! on a KB with belief.")})))

(defn- direction-problem
  "Why rule handle `h`, stored as `sx`, cannot take `direction`, or nil."
  [h sx direction]
  (cond
    (not (contains? sx/direction-engines direction))
    {:type :unknown-option :mismatch :bad-value :handle h :direction direction
     :options (vec (sort (disj (set (keys sx/direction-engines)) :lazy-forward)))
     :operation "edit-records!"
     :message (str "unknown direction " (pr-str direction) " for handle " h)}

    (nil? sx)
    {:type :unknown-handle :handle h :operation "edit-records!"
     :message (str "handle " h " names no stored record, so it has no direction to change")}

    (not (rules/rule? sx))
    {:type :unknown-option :mismatch :conflict :handle h :direction direction
     :operation "edit-records!"
     :message (str "handle " h " is not a rule, so it has no direction")}

    (contains? (:engines sx) :solve)
    {:type :unknown-option :mismatch :conflict :handle h :direction direction
     :operation "edit-records!"
     :message (str "handle " h " is a choice or constraint rule; a solve decides its head,"
                   " so it takes no direction")}

    (or (= :lazy-forward direction) (contains? (:engines sx) :lazy))
    {:type :unknown-option :mismatch :conflict :handle h :direction direction
     :operation "edit-records!"
     :message (str "handle " h " is or would be a lazy-forward rule; the firings reading it"
                   " rest on it as an antecedent, and edit-records! re-joins and deletes"
                   " firings by rule.  Retract it and assert the new spelling")}))

(defn- throw-problem! [problem]
  (when problem (throw (ex-info (:message problem) (dissoc problem :message)))))

(defn- scan-justifications
  "One pass over every stored justification, keeping the ones a batch can kill: those
  resting on a handle of `removals` or fired by a rule of `narrowed`, and those concluding
  a handle of `removals`.  Returns `{jid justification}`."
  [records removals narrowed]
  (with-open [r (progress/start ::scan "edit-records!: read the justifications"
                                (cap/count-justifications records))]
    (persistent!
     (reduce (fn [acc id]
               (progress/tick! r)
               (if-let [j (p/get-justification records id)]
                 (if (or (contains? removals (:consequence j))
                         (contains? narrowed (:informant j))
                         (some removals (jtms/rests-on j)))
                   (assoc! acc id j)
                   acc)
                 acc))
             (transient {})
             (cap/hinting (cap/justification-prefetcher records) cap/recovery-hint-chunk
                          (p/justification-ids records))))))

(defn- plan
  "Which removals are deleted and which only lose their premise mark, and which
  justifications go.  A removal is deleted unless a justification that survives the batch
  concludes it.  Keeping one revives the justifications resting on it, so the split is
  iterated to a fixpoint; the deleted set only shrinks.  Returns `{:delete #{h} :keep #{h}
  :dead {jid justification}}`."
  [removals narrowed js]
  (loop [deleted removals]
    (let [dead?  (fn [j] (or (contains? narrowed (:informant j))
                             (some deleted (jtms/rests-on j))))
          kept   (into #{} (comp (remove dead?) (map :consequence) (filter deleted)) (vals js))]
      (if (seq kept)
        (recur (reduce disj deleted kept))
        {:delete deleted
         :keep   (into #{} (remove deleted) removals)
         :dead   (into {} (filter (comp dead? val)) js)}))))

(def addable
  "The functors `apply!` adds a fact of.  Each stores where `assert` stores it, as written:
  the shipped vocabulary marks none of them symmetric, commutative or forced
  decontextualized, and `add-problem` refuses a store that does.  Of their index entries
  only a `genl` edge's taxonomy supporters go beyond the record's own."
  '#{genl sense comment})

(def ^:private relocating-marks
  "The marks about a predicate under which `assert` stores a fact other than as written: a
  permuting mark sorts its arguments (`res/kb-sentex`), and a forced decontextualization
  moves it to the root context (`assert-entry/storage-context`)."
  (conj inherit/permuting-marks 'forced_decontextualized_predicate))

(defn- add-refusal
  "The `:record-edit-unsupported` refusal of the `:add` entry `s` in `ctx`, `why` ending
  its message."
  [s ctx why]
  {:type :record-edit-unsupported :functor (nm/functor s) :operation "edit-records!"
   :sentence s :context ctx
   :message (str (pr-str s) " in " ctx " " why)})

(defn- entry-shape-problem
  "The `:shape` problem of one `:add` entry, or nil: a `[sentence context]` pair whose
  sentence is a list and whose context is a symbol naming a place."
  [entry]
  (cond
    (not (and (sequential? entry) (= 2 (count entry))))
    {:type :shape :message (str "each edit-records! :add entry is [sentence context], got "
                                (pr-str entry))}
    (not (seq? (first entry)))
    {:type :shape :message (str "an :add sentence is a list, got " (pr-str (first entry)))}
    (not (symbol? (second entry)))
    {:type :shape :message (str "an :add context is a symbol, got " (pr-str (second entry)))}
    (nm/query-context? (second entry))
    {:type :shape :message (str (second entry) " is a query context, which nothing is"
                                " asserted into")}))

(defn- known-context?
  "Does the index name `ctx` as a context: the root, a context holding a stored record, or
  one a stored `genlCx` edge names?  Set-size and posting reads; no belief."
  [idx ctx]
  (boolean (or (= sx/root-context ctx)
               (pos? (reads/stored-count-in-context idx ctx))
               (seq (reads/as-stored-with-args idx 'genlCx {1 ctx}))
               (seq (reads/as-stored-with-args idx 'genlCx {2 ctx})))))

(defn- add-problem
  "Why the `:add` sentence `s` in `ctx` cannot be written at record level, or nil, read
  off the sentence and the index alone."
  [idx s ctx]
  (let [f (nm/functor s)]
    (cond
      (not (contains? addable f))
      (add-refusal s ctx (str "is not a fact of " (str/join ", " (sort addable))
                              ", the functors edit-records! adds"))

      (not= 3 (count s))
      (add-refusal s ctx "does not take two arguments")

      (not-every? #(or (symbol? %) (string? %)) (rest s))
      (add-refusal s ctx (str "has an argument that is neither a symbol nor a string; a"
                              " compound reifies or resolves against belief, which edit!"
                              " reads"))

      (and (= 'genl f) (nm/between-predicates? s))
      (add-refusal s ctx (str "relates predicates, a forced-monotonic edge that carries"
                              " declarations down; edit! adds it"))

      (some #(seq (reads/as-stored-with-args idx % {1 f})) relocating-marks)
      (add-refusal s ctx (str "names a predicate the store marks "
                              (str/join " or " (filter #(seq (reads/as-stored-with-args idx % {1 f}))
                                                       relocating-marks))
                              ", which moves where assert stores it; edit! adds it"))

      (not (known-context? idx ctx))
      (add-refusal s ctx (str "names a context the store holds nothing in and no genlCx"
                              " edge names")))))

(defn- check-add!
  "Throw the first refusal of the `:add` entry `entry`: its shape, a free variable
  (`:not-ground`), the naming checks under `kb`'s `:naming` policy, a length binding
  against its shape, the well-formedness that reads no stored content
  (`:not-well-formed`), then `add-problem`, then a stored record of the sentence that
  `assert-inert` marked."
  [kb entry]
  (throw-problem! (entry-shape-problem entry))
  (let [[s ctx] entry
        idx     (:index kb)
        built   (sx/sentex s ctx)]
    (checks/check-sentex-ground built s ctx)
    (nm/check! (:naming kb) s ctx)
    (checks/check-length-binding (:naming kb) s ctx)
    (when-let [ps (seq (special/wff-problems nil s ctx))]
      (throw (ex-info (str "not well-formed: " (str/join "; " ps))
                      {:type :not-well-formed :sentence s})))
    (throw-problem! (add-problem idx s ctx))
    (when-let [h (first (reads/as-stored-leaf idx (sx/path built)))]
      (when (and (p/get-sentex (:records kb) h) (recovery/inert-marked? kb h))
        (throw-problem! (add-refusal s ctx (str "is stored at handle " h " as an inert"
                                                " record, which is no premise")))))))

(defn- add-one!
  "Write the `:add` entry `[s ctx]` into `kb`'s records: `[:added h]` for a new premise,
  `[:marked h]` for a stored record that gains the premise mark, `[:present h]` for a
  stored premise, left as it is.  A new record goes in index first: its postings, a
  `genl` edge's taxonomy supporters (`special/post-declaration-supporters!`), then the
  record with its mark.  A posting naming no record is taken out, as
  `kb/find-or-create-sentex` takes it out, and the sentence stored anew, so the same entry
  run again repairs a crash before the record.  A stored record gains its supporters,
  then the mark."
  [kb [s ctx]]
  (let [records (:records kb)
        idx     (:index kb)
        built   (sx/sentex s ctx)
        h       (first (reads/as-stored-leaf idx (sx/path built)))
        stored  (when h (p/get-sentex records h))]
    (cond
      (and stored (some? (:strength stored)))
      [:present h]

      stored
      (do (special/post-declaration-supporters! kb [(assoc stored :id h)])
          (p/mark-premise records h :default)
          [:marked h])

      :else
      (let [_   (when h (reindex/unindex-one! idx (assoc built :id h) h))
            h   (p/next-id records)
            new (assoc built :id h :strength :default)]
        (reindex/index-one! idx new h)
        (special/post-declaration-supporters! kb [new])
        (p/put-sentex records new)
        (p/mark-premise records h :default)
        [:added h]))))

(defn apply!
  "Apply `batch` to the records of `kb`, which must have no belief: `:add`, a seq of
  `[sentence context]` of an `addable` functor; `:remove`, a seq of handles; `:direction`,
  `{handle direction}` over `sx/direction-engines`.  No belief read, sweep or settle runs.

  The additions are written first (`add-one!`).  A removed record is deleted with its
  index postings unless a justification that survives the batch concludes it; such a
  record only loses its premise mark.  A rule's direction is written into its record.
  Every stored justification resting on a deleted record, and every firing of a rule the
  batch takes off `:forward`, is deleted, except a firing that rests on a deleted `genl`
  or `genlCx` edge: `sweep!` reads its antecedents as the facts to re-chain, then deletes
  it.  An addition stored already counts under `:present` and a removal naming no stored
  record under `:absent`, so the same batch run again after a crash completes it.

  Returns `{:added n :present n :removed n :unpremised n :absent n :redirected n
  :justifications-removed n :seeds [h …]}`, `:seeds` naming where the settle starts.  A
  batch adding a `genl` edge or removing or redirecting a stored record owes the
  argument-type pass (`argpass/owe-all!`) before its first write.  Refuses before writing
  what `vaelii.core/edit-records!` lists."
  [kb batch]
  (opts/check! batch #{:add :remove :direction} "edit-records!"
               "A key nothing reads would leave its edits unapplied.")
  (check-kb! kb)
  (when-not (sequential? (get batch :add []))
    (throw-problem! {:type :shape :message (str "edit-records! :add is a sequence of [sentence"
                                                " context], got " (pr-str (:add batch)))}))
  (let [records    (:records kb)
        index      (:index kb)
        adds       (into [] (:add batch))
        directions (into {} (:direction batch))
        removes    (into [] (distinct) (:remove batch))
        ;; a nil removal, `handle-of`'s answer for a sentence the KB does not hold, names
        ;; no stored record and counts under `:absent`
        stored     (into {} (keep #(when-let [sx (and (integer? %) (p/get-sentex records %))]
                                     [% (assoc sx :id %)]))
                         (concat removes (keys directions)))
        removals   (into #{} (filter stored) removes)]
    ;; every refusal before the first write
    (when (and (seq adds) (:no-index (kb/write-hazards kb)))
      (let [msg (str "edit-records! deduplicates an addition against the index, and this KB's"
                     " index was never built from its records: call (reindex kb) first.")]
        (throw-problem! {:type :unrecovered-kb :hazards (vec (sort (keys (kb/write-hazards kb))))
                         :operation "edit-records!" :repair 'reindex :message msg})))
    (run! #(check-add! kb %) adds)
    (doseq [h removals]
      (throw-problem! (removable-problem h (stored h)))
      (throw-problem! (kb/mint-rule-refusal (kv/mint-rule-kind (stored h)) h "edit-records!"
                                            "is not removed")))
    (doseq [[h d] directions]
      (throw-problem! (direction-problem h (stored h) d))
      (when (not= (:engines (stored h)) (sx/direction-engines d))
        (throw-problem! (kb/mint-rule-refusal (kv/mint-rule-kind (stored h)) h "edit-records!"
                                              "keeps its direction")))
      (when (contains? removals h)
        (throw-problem! {:type :unknown-option :mismatch :conflict :handle h
                         :operation "edit-records!"
                         :message (str "handle " h " is both removed and redirected")})))
    (let [engines  (into {} (map (fn [[h d]] [h (sx/direction-engines d)])) directions)
          narrowed (into #{} (comp (remove (fn [[_ e]] (contains? e :forward))) (map key)) engines)
          js       (if (or (seq removals) (seq narrowed))
                     (scan-justifications records removals narrowed)
                     {})
          {:keys [delete keep dead]} (plan removals narrowed js)
          ;; a firing that named a deleted closure edge as its witness may still be
          ;; licensed by a second route; `recover` leaves it out as `:unrooted`, and
          ;; `sweep!` reads the facts to re-chain off it before deleting it
          edges    (into #{} (filter #(special/closure-edge-relation (sx/sentence-of (stored %)))) delete)
          left     (into #{} (comp (filter (fn [[_ j]] (and (special/firing-informant? kb (:informant j))
                                                            (not (contains? narrowed (:informant j)))
                                                            (some edges (:antecedents j)))))
                                   (map key))
                         dead)
          ;; a rule the batch puts on `:forward` is a seed too, every run, so a run after a
          ;; crash names it again although its record already holds the direction
          seeds    (-> (into (sorted-set) keep)
                       (into (comp (map :consequence) (remove delete) (filter integer?)) (vals dead))
                       (into (comp (filter (fn [[_ e]] (contains? e :forward))) (map key)) engines))]
      (when (or (seq removals) (seq engines) (some #(= 'genl (nm/functor (first %))) adds))
        (argpass/owe-all! kb))
      ;; Written in this order so that a crash at any point leaves a store the same batch
      ;; run again completes: the additions, the directions and premise marks, each deleted
      ;; record with its postings, and last the dead justifications, which `recover` leaves
      ;; out of the network while their records are gone (`:unrooted`).
      (let [added (mapv #(add-one! kb %) adds)
            gained (into [] (comp (remove #(= :present (first %))) (map second)) added)
            tally  (fn [tags] (count (filter #(contains? tags (first %)) added)))
            seeds  (into seeds gained)]
        (doseq [[h e] engines
                :let [old (stored h)]
                :when (not= e (:engines old))
                :let [new (assoc old :engines e)]]
          (p/unindex-sentex! index old h)
          (p/put-sentex records new)
          (p/index-sentex index new h))
        (run! #(p/unmark-premise! records %) keep)
        (doseq [h (sort delete)]
          (reindex/unindex-one! index (stored h) h)
          (p/delete-sentex! records h))
        (run! #(p/delete-justification! records %) (sort (remove left (keys dead))))
        (kb/refresh-index-image! kb)
        {:added                  (tally #{:added})
         :present                (tally #{:present :marked})
         :removed                (count delete)
         :unpremised             (count keep)
         :absent                 (- (count removes) (count removals))
         :redirected             (count engines)
         :justifications-removed (- (count dead) (count left))
         :seeds                  (into [] (filter #(p/get-sentex records %)) seeds)}))))

;; ---- the sweep after the rebuild ----------------------------------------------------

(def ^:private sweep-steps
  "The steps of `sweep!`, in order."
  [:unrooted :sweep :settle :chain :rechain :settle-chain :arrive :settle-arrive])

(defn- arrive
  "Run, for the stored premise fact at `h`, what `assert-entry/assert-one` runs after it
  stores a fact and `recover` does not: the equality migrations and merges, the nogood
  offers, the argument-order migration, the supersessions a merge moved, the lift, the
  argument-type mints at its placements (`special/draw-fact`, as `assert` draws them
  beside `deduce-below`), the mints' arrival orders, the companion rules and the arity
  class memberships.  Returns `{:seeds [h …] :violations [v …]}`, the chaining seeds and
  the violations `assert` computes, the batch's subsumption seeds aside.  Run under
  `special/call-with-pass-caches`."
  [kb h]
  (let [sx   (assoc (p/get-sentex (:records kb) h) :id h)
        s    (:sentence sx)
        ctx  (:context sx)
        own  (when (kb/rewritable-sentex? kb sx) (special/migrate-sentex kb sx))
        _    (special/migrate-meta-onto-twins kb sx)
        fnl  (special/derive-functional-equalities kb s ctx h)
        fex  (special/equate-existing kb s)
        fdn  (special/equate-under-edge kb s)
        asym (special/derive-antisymmetric-equalities kb s ctx h)
        axe  (special/antisym-equate-existing kb s)
        axd  (special/antisym-equate-under-edge kb s)
        _    (special/offer-marked-existing kb s)
        _    (special/offer-marked-under-edge kb s)
        sym  (integrate/commute-existing kb s h)
        mig  (merge-with into {:new [] :superseded [] :violations []}
                         own fnl fex fdn asym axe axd sym)
        _    (when (seq (:superseded mig)) (special/refresh-supersessions kb (:superseded mig)))
        lift (special/deduce-lifts kb s h ctx)
        args (special/draw-fact kb h nil)
        back (special/entail-existing kb s h)
        down (special/entail-under-edge kb s)
        dfn  (special/materialize-defn-rules kb s h ctx)
        cls  (chain/arity-classes-moved! kb [sx] false)]
    {:seeds      (-> [h]
                     (into (special/minted-seeds kb (:new mig)))
                     (into (:new lift))
                     (into (special/minted-seeds kb (:new down)))
                     (into (:new dfn))
                     (into (:new cls))
                     (into (special/minted-seeds kb (:new args)))
                     (into (special/minted-seeds kb (:new back)))
                     (into (special/transitive-seeds kb s)))
     :violations (into [] cat [(:violations mig) (:violations lift) (:violations args)
                               (:violations back) (:violations down) (:violations dfn)
                               (:violations cls)])}))

(defn- arrive-all!
  "Bring the stored premise facts `hs` in as `assert` brings each in after its store
  (`arrive`), chain from every seed they name and from the facts their `genl` edges make
  newly matchable (`special/batch-subsumption-seeds`, as `edit!` batches them), report
  the violations, settle, and run the reified-term maintenance `assert` runs last
  (`nat-maint/reconcile-assert`).  `chain-opts` are `chain/chain-all`'s."
  [kb hs chain-opts]
  (let [records (:records kb)
        sxs     (mapv #(p/get-sentex records %) hs)
        drawn   (special/call-with-pass-caches
                 kb #(reduce (fn [acc h] (merge-with into acc (arrive kb h)))
                             {:seeds [] :violations []}
                             hs))
        seeds   (into [] (distinct)
                      (concat (:seeds drawn)
                              (special/batch-subsumption-seeds kb (map :sentence sxs))))]
    (chain/chain-all kb seeds chain-opts)
    (violations/report kb (:violations drawn))
    (settle/settle kb)
    (doseq [sx sxs]
      (nat-maint/reconcile-assert kb (:sentence sx) (:context sx) {}))
    (count seeds)))

(defn sweep!
  "Delete the unrooted justifications the last `recover` left out (`:unrooted`), sweep
  the consequence closure of their stored conclusions and of `seeds` as a retraction
  sweeps it — every record there that is not a premise and is OUT goes, with the
  justifications touching it (`jtms/sweep!`), through the removal choke point — and settle;
  chain each forward rule among `seeds` over the stored facts, re-chain the antecedents of
  the unrooted rule firings (`special/firing-seeds`) and settle; then bring each seed that
  is a stored premise fact in as `assert` brings a stored fact in (`arrive-all!`), and
  settle.  Runs over a KB with belief.  Returns `{:unrooted n :removed-sentexes n
  :removed-justifications n :rules-chained n :rechained n :arrived n}`.

  `report`, when given, is called with `{:phase :sweep :step k :done i :total 8}` as each
  step begins (`sweep-steps`), and with the chain's `:derived` and `:pending` beside while
  it runs."
  ([kb seeds] (sweep! kb seeds nil))
  ([kb seeds report]
   (let [step!   (fn [k & [extra]]
                   (when report
                     (report (merge {:phase :sweep :step k
                                     :done (.indexOf ^java.util.List sweep-steps k)
                                     :total (count sweep-steps)}
                                    extra))))
         _       (step! :unrooted)
         records (:records kb)
         tms     (reasoning/tms kb)
         unrooted (:unrooted @(:unrecovered kb))
         js      (into [] (keep #(p/get-justification records %)) unrooted)
         concl   (into [] (keep :consequence) js)
         gone?   (fn [h] (and (integer? h) (nil? (p/get-sentex records h))))
         ;; read off the records before they go, as `edit!` reads its seeds off the
         ;; justifications its sweep removed (`special/resubsumption-seeds`)
         refire  (special/firing-seeds kb js gone? gone?)
         _       (run! #(p/delete-justification! records %) unrooted)
         _       (swap! (:unrecovered kb) dissoc :unrooted)
         _       (step! :sweep)
         seeds   (into #{} (filter #(and (integer? %)
                                         (jtms/known-datum? tms %)
                                         (not (recovery/inert-marked? kb %))))
                       (concat seeds concl))
         rm      (if (seq seeds) (jtms/sweep! tms seeds) {})
         _       (integrate/apply-removals! kb rm)
         _       (step! :settle)
         _       (settle/settle kb)
         ;; the rules a batch put on `:forward`, joined over the facts as `assert` joins a
         ;; rule that newly runs forward
         rules   (into [] (filter #(some-> (p/get-sentex records %) rules/forward-sentex?))
                       (sort seeds))]
     (step! :chain {:rules (count rules)})
     (when (seq rules)
       (chain/chain-all kb rules (if report
                                   {:on-progress #(step! :chain (assoc % :rules (count rules)))}
                                   {})))
     (step! :rechain {:firings (count refire)})
     ;; re-asking firings the removal swept, so one that places nothing is not reported
     ;; (`chain/*report-no-placement?*`)
     (when (seq refire)
       (binding [chain/*report-no-placement?* false] (settle/rechain-seeds kb refire)))
     (when (or (seq rules) (seq refire))
       (step! :settle-chain)
       (settle/settle kb))
     (let [arrivals (into [] (filter #(when-let [sx (p/get-sentex records %)]
                                        (and (sx/positive-fact? sx) (jtms/premise? tms %))))
                          (sort seeds))]
       (step! :arrive {:facts (count arrivals)})
       (when (seq arrivals)
         (binding [special/*producer-moves* (or special/*producer-moves* (special/producer-moves))]
           (arrive-all! kb arrivals (if report
                                      {:on-progress #(step! :arrive (assoc % :facts (count arrivals)))}
                                      {})))
         (step! :settle-arrive)
         (settle/settle kb))
       {:unrooted               (count unrooted)
        :removed-sentexes       (count (:removed-sentexes rm))
        :removed-justifications (count (:removed-justifications rm))
        :rules-chained          (count rules)
        :rechained              (count refire)
        :arrived                (count arrivals)}))))
