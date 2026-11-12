;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.settle
  "Belief settling: the pass that relabels the TMS and runs the `exceptWhen` re-check
  queue to a joint fixpoint with belief (`pass-work`, `block-work`, `apply-pass!`), the
  seed readers a pass gathers, `settle-finish` and `settle`.  A pass calls `recheck`;
  what a reader reads of the clashes is `vaelii.impl.clashes`.  The top engine layer,
  below `vaelii.core`.  See docs/nmtms.md."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.except :as exc]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.recheck :as recheck]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]
            [vaelii.impl.wiring :as wiring]))

;; ---- the facet contract -------------------------------------------------
;; `predicates/check-facets` runs at this namespace's load (docs/predicates.md says why).

(def facet-check-inputs
  "The cross-layer facts `predicates/check-facets` cannot read for itself.  A var so
  that this call site and `predicates_test` check the same arguments.

  * `:recheck-subjects` — the functors posting exception re-checks through the shared
    path (`special/declaration-subjects`) rather than from an arm of their own.
  * `:family-lists` — `family -> {list-name functors}`, every list that reads a
    mark family as a family (`predicates_test/a-list-that-enumerates-a-family-is-named-here`).
  * `:clash-checks` — the violations `checks/fact-clash-checks` and
    `checks/declaration-clash-checks` answer, by direction."
  {:recheck-subjects special/recheck-subjects
   :clash-checks     {:fact        (into #{} (map first) checks/fact-clash-checks)
                      :declaration (into #{} (map first) checks/declaration-clash-checks)}
   :family-lists     {:argument-constraint
                      {'checks/constraint-declaration-functors
                       checks/constraint-declaration-functors
                       'provers/meta-constraint-functors
                       provers/meta-constraint-functors}}})

(def checked-entries
  "`predicates/entries`, having passed the facet contract at this namespace's load, which
  throws on a violation.  A var rather than a bare call so `predicates_test` can prove
  the check runs here on the live inputs."
  (pr/check-facets pr/entries facet-check-inputs))

;; ---- the exception fixpoint ---------------------------------------------
;; Belief and blocking depend on each other, so `settle` iterates: relabel, re-evaluate
;; the exceptions the triggers queued, relabel again if the blocked set moved.

(def ^:private max-settle-passes
  "Bound on the exception fixpoint's passes.  Termination rests on the stratification
  checks at assert time; a run that reaches this bound logs `::exception-fixpoint`
  instead of looping (docs/exceptions.md)."
  16)

(defn- drain-recheck!
  "Take the queued `{rule-handle -> triggers}` map and clear the queue in one `swap-vals!`,
  so a `swap!` landing during the take is kept for the next pass."
  [kb]
  (first (swap-vals! (reasoning/recheck kb) (constantly {}))))

(def ^:dynamic *touched-sink*
  "An atom holding a set, or nil.  When bound, every settle adds the handles of its
  relabelled region before clearing them.  `core/preview` and
  `core/edit-with-consequences!` bind it (docs/preview.md)."
  nil)

(def ^:dynamic *touched-in-sink*
  "An atom holding a set, or nil: the companion of `*touched-sink*`, collecting which
  handles of that region were believed before the settle (`jtms/touched-in`).
  `core/edit-with-consequences!` binds both."
  nil)

(def ^:dynamic *sweep?*
  "Does a settle delete what a newly-blocked justification solely supported?  False only
  inside `core/preview`, which must hand the KB back at the same handles
  (docs/preview.md)."
  true)

(def ^:dynamic *relabelled-before?*
  "True when labels flipped before the settle by a path that is neither a defeat, a
  block nor a write: `core/preview`'s `jtms/suspend-premise` and its rollback's
  `add-premise`, and `settle`'s drop of a firing over a retired spelling
  (`withdraw-retired-firings!`).  It sets the `belief-moved?` condition (docs/nmtms.md,
  \"What `settle-finish` reconciles\").  The caller binds this flag instead of a check that
  tests the region for a taxonomy sentex, because that test would cost a record read per
  region member on every settle for a path only `preview` takes."
  false)

(def ^:dynamic *rebuilding?*
  "True while `recover`'s settles restore a KB rather than react to a change.  The passes
  that report or re-derive what a change moved read it and stand aside, among them the
  cut notices, the revival and un-merge re-seeds, the refusal re-asks
  and the second-route re-derivations.  A rebuild relabels the whole graph, so its region
  is every stored sentex, and the replayed justifications already carry every
  derivation.  The definitional nogood sweep does not read it (docs/taxonomy.md, \"What a
  declaration reaches back over\")."
  false)

(def ^:dynamic ^:private *unmerged-sink*
  "A volatile collecting the spellings an un-merge gave back, and each equality supporter
  believed again with its twins, or nil.  `settle` binds it, `settle-finish` fills it
  from the supersession moves since the last settle (`special/take-supersession-moves!`)
  and from `special/believed-again-sweeps`, and `settle` re-seeds
  what it holds and settles again (docs/nmtms.md, \"The other half: a spelling an
  un-merge gives back\")."
  nil)

(defn- sweep-excepted!
  "Delete what the newly-blocked justifications were solely supporting, through the JTMS
  sweep (`integrate/apply-removals!`), and record each newly-blocked forward rule firing
  the sweep deletes as a refusal (`chain/record-swept-firing!`), so the trigger that lifts
  its block releases it from its bindings.  Deletes nothing while `*sweep?*` is false."
  [kb newly-blocked]
  (let [tms   (reasoning/tms kb)
        seeds (when *sweep?*
                (into #{} (keep #(:consequence (jtms/justification tms %))) newly-blocked))]
    (when (seq seeds)
      (let [rm   (jtms/sweep! tms seeds)
            gone (set (:removed-justifications rm))]
        (doseq [jid newly-blocked
                :when (contains? gone jid)
                :let [j (p/get-justification (:records kb) jid)]
                :when j]
          (chain/record-swept-firing! kb j))
        (integrate/apply-removals! kb rm)))))

(defn- released-rules
  "The informants of the justifications in `was` and not in `new`: the rules whose
  exception this pass lifted.  Called before the sweep, while those justifications are
  still in the TMS."
  [kb was new]
  (let [tms (reasoning/tms kb)]
    (into #{}
          (keep (fn [jid]
                  (let [inf (:informant (jtms/justification tms jid))]
                    (when (special/firing-informant? kb inf) inf))))
          (remove new was))))

(defn- arity-class-seeds
  "The class memberships a metatype route derives that the records stored since the last
  pass with no sync on their store path (`arity/take-classes!`), the relabelled handles
  of `region` (a delay) and the `genl` edges moved since the last pass
  (`arity/take-class-ends!`) move, as new handles to chain from
  (`chain/arity-classes-moved!`, `chain/arity-class-ends-moved!`), the violations
  reported.  A relabelled handle whose node this settle created was queued at its store,
  and a removed one holds no class, so neither is read.  Empty during a rebuild, whose replayed justifications carry every
  class membership."
  [kb region]
  (if *rebuilding?*
    []
    (let [tms   (reasoning/tms kb)
          recs  (:records kb)
          new   (jtms/touched-new tms)
          moved (into [] (comp (remove new) (filter #(jtms/known-datum? tms %))
                               (keep #(p/get-sentex recs %)))
                      (set @region))]
      (if (and (empty? moved)
               (not (arity/classes-queued? (reasoning/taxonomy kb) @(reasoning/nogood-candidates kb))))
        []
        (let [fresh (into [] (keep #(p/get-sentex recs %)) (sort (arity/take-classes! kb)))
              r     (merge-with into (chain/arity-classes-moved! kb fresh false)
                                (chain/arity-classes-moved! kb moved true)
                                (chain/arity-class-ends-moved! kb (arity/take-class-ends! kb)))]
          (violations/report kb (:violations r))
          (:new r))))))

(defn- revived-mark-seeds
  "The merges and lifts a mark, or a `genl` edge under one, in `revived` owes the facts
  stored while it was OUT, as new handles to chain from
  (`special/revived-declaration-sweeps`).  Reconciles the retired spellings and reports
  the violations, as `assert-one` does for the same sweeps on an arrival.  `revived` is
  `revived-seeds`' answer, so a rebuild asks nothing.  The taxonomy is reconciled over
  `revived` first: a datum a relabel inside this settle revived, such as a `genl` edge
  whose void firing a forced-monotonic declaration released, is in no cache until `settle-finish`,
  and the sweeps read the marks and edges the caches hold."
  [kb revived]
  (when (seq revived)
    (special/reconcile-belief-change kb revived)
    (tax/restore-depths (reasoning/taxonomy kb)))
  (if-let [mig (special/revived-declaration-sweeps kb revived)]
    (do (when (seq (:superseded mig))
          (special/refresh-supersessions kb (:superseded mig)))
        (violations/report kb (:violations mig))
        (special/minted-seeds kb (:new mig)))
    []))

(defn- revived-edge-seeds
  "The facts a `genl` edge in `revived` makes matchable, as new handles to chain from: the
  `special/batch-subsumption-seeds` the edge's arrival chains, owed again when a relabel
  brings it back IN."
  [kb revived]
  (when (seq revived)
    (special/batch-subsumption-seeds kb (keep #(:sentence (p/get-sentex (:records kb) %)) revived))))

(defn- class-moved-merge-seeds
  "The merges and un-merges a collision member's class moving owes
  (`special/class-moved-merges` over `region`, the pass's `touched` as a delay), as handles
  to chain from: the new twins and the members of each dropped merge.  Applies the
  removals, reconciles the retired spellings and reports the violations, as
  `revived-mark-seeds` does.  `asked` is the settle's record of what it asked.  Empty
  during a rebuild, whose replayed justifications carry every merge."
  [kb region asked]
  (if-let [mig (when-not *rebuilding?* (special/class-moved-merges kb region asked *sweep?*))]
    (let [seeds (into (special/minted-seeds kb (:new mig)) (:members mig))]
      (some->> (:removed mig) (integrate/apply-removals! kb))
      (when (seq (:superseded mig))
        (special/refresh-supersessions kb (:superseded mig)))
      (violations/report kb (:violations mig))
      seeds)
    []))

(defn- except-move-seeds
  "The twins owed to the facts an `except` moved an equality's or a merge mark's
  visibility over, and the argument-type derivations it moved, as new handles to chain
  from (`special/drain-except-moves!`), then its `:rejoin` facts, chained alone.  The
  derivations it hides are removed here.  The supersessions the sweep found wait on
  `:except-moves` for `settle-finish`; the violations are reported here.  A rebuild clears
  the queue, since it reconciles every supersession from the stored twins."
  [kb]
  (if *rebuilding?*
    (do (special/clear-except-moves! kb) [])
    (if-let [mig (special/drain-except-moves! kb *sweep?*)]
      (do (some->> (:removed mig) (integrate/apply-removals! kb))
          (violations/report kb (:violations mig))
          (into (special/minted-seeds kb (:new mig)) (:rejoin mig)))
      [])))

(defn- context-move-seeds
  "The chaining seeds the pass's `genlCx` moves owe (`special/drain-context-moves!`): the
  facts they make matchable and the twins and mints their sweeps wrote.  The supersessions
  the sweeps found are reconciled and the violations reported here."
  [kb {:keys [seeds mig]}]
  (when (seq (:superseded mig))
    (special/refresh-supersessions kb (:superseded mig)))
  (violations/report kb (:violations mig))
  (into (vec seeds) (special/minted-seeds kb (:new mig))))

(defn- released-subsumed
  "The mints a record leaving belief or the store no longer lets the KB withhold, as new
  handles to chain from (`special/withheld-releases`).  `withdrawn` is the mints this
  settle withdrew, whose own departure releases nothing.  Empty during a rebuild, which
  drops the queued departures: a restore changes nothing.  `was-in` and `believed?` are
  belief before the settle and now (`pass-belief`)."
  [kb moved was-in believed? asked withdrawn]
  (if *rebuilding?*
    (do (special/drain-departures! kb) [])
    (:new (special/withheld-releases kb moved was-in asked withdrawn believed?))))

(defn- triggered-seeds
  "The entailments a membership or a `genl` edge that came IN this settle triggers over
  the stored facts naming the terms it types, as new handles to chain from
  (`special/triggered-mints`).  `asked` holds the records already asked this settle.
  Empty during a rebuild, which draws no entailment."
  [kb moved was-in believed? asked]
  (if *rebuilding?*
    []
    (let [r (special/triggered-mints kb moved was-in asked believed?)]
      (violations/report kb (:violations r))
      (special/minted-seeds kb (:new r)))))

(defn- drop-surplus-placements!
  "Drop the mint justifications `jids` (`special/surplus-placements`, read by
  `subsumed-blocks`) and the merge justifications (`special/covered-merges`), and delete
  what the drop sweeps.  Returns `jids` as a vector."
  [kb jids]
  (when (seq jids)
    (let [tms (reasoning/tms kb)]
      (integrate/apply-removals! kb (reduce (fn [acc jid]
                                              (let [r (jtms/drop-justification! tms jid)]
                                                (p/delete-justification! (:records kb) jid)
                                                (merge-with into acc r)))
                                            nil jids))))
  (vec jids))

(defn- subsumed-blocks
  "The mint justifications this settle withdraws, and the records they held up:
  `special/subsumed-mint-blocks` over `moved`, the delay of the region's sentexes
  `released-subsumed` reads too.  A `recover`'s region, the whole store, is passed as its
  size, so the mints are read instead of the region where fewer are stored."
  [kb region moved was-in believed? asked]
  (let [whole (when (and *rebuilding?* discovery/*whole-store-region?*) (count @region))]
    (or (special/subsumed-mint-blocks kb moved was-in asked believed? (not *rebuilding?*) whole)
        {:blocked #{} :withdrawn #{}})))

(defn- removed-moves
  "`[target context]` for each handle moved by a sentex the removal record holds
  (`integrate/*removed-sink*`) that was IN when the settle began (`was`,
  `jtms/touched-in`), read off its sentence (`kb/placed-targets`) since its record is gone."
  [kb was]
  (if-let [sink integrate/*removed-sink*]
    (into #{} (mapcat (fn [sx] (when (contains? was (:id sx))
                                 (map #(vector % (:context sx))
                                      (kb/placed-targets kb (:sentence sx))))))
          @sink)
    #{}))

(defn- defeat-moves
  "`[stored removed]` over the placed handles of `region` (the touched set) that move a
  handle with no relabel (`kb/placed-targets`): `stored` holds those IN now and not when
  the settle began, and `removed` holds `[target context]` for each handle moved by one
  IN when the settle began and OUT now or gone from the store, the gone ones read off the
  removal record (`removed-moves`)."
  [kb region]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        was  (jtms/touched-in tms)
        ;; only the engine derives a defeat, under one of two informants, so a handle
        ;; with no such justification is no defeat and its record is not read
        placed? (fn [h] (some #(contains? #{exc/nogood-informant exc/guard-informant}
                                          (:informant (jtms/justification tms %)))
                              (jtms/supports tms h)))
        gone (removed-moves kb was)]
    ;; with no defeat stored and no except beside a placed contradicts, the touched set holds
    ;; nothing that moves a handle with no relabel
    (if-not (exc/placed-reads? kb)
      [#{} gone]
      (reduce (fn [[st rm :as acc] h]
                (let [sx (when (placed? h) (p/get-sentex recs h))
                      ts (some->> sx :sentence (kb/placed-targets kb))]
                  (cond (empty? ts)                                    acc
                        (and (jtms/in? tms h) (not (contains? was h))) [(conj st h) rm]
                        (and (not (jtms/in? tms h)) (contains? was h)) [st (into rm (map #(vector % (:context sx))) ts)]
                        :else                                          acc)))
              [#{} gone]
              region))))

(def ^:dynamic *batch-seeds-moves*
  "A volatile a `with-deferred-settle` batch binds to false before its first write, or nil.
  A write the batch defers sets it true when its own settle would have seeded chaining
  from the `genlCx` moves it settles (`settle-write`), and the batch's closing
  settle seeds them only then (`special/*seed-moves?*`)."
  nil)

(defn- report-wanted?
  "Does a settle owe a report: a sink is bound or a listener is registered?"
  [kb]
  (boolean (or *touched-sink* *touched-in-sink*
               (and (not *rebuilding?*) (feed/wants-region? kb)))))

(defn write-record
  "What a write entry point binds `observe/*write-record*` to before it writes: the record
  open, or a new one when the write owes a report (`report-wanted?`), else nil.  The
  report reads the KB as it stood when the record opened (`kb/prior-kb`), and
  `settle-finish` empties the record once it has reported (docs/nmtms.md, \"The published
  set\")."
  [kb]
  (or observe/*write-record* (when (report-wanted? kb) (java.util.IdentityHashMap.))))

(defmacro ^:private reading-prior
  "Run `body`, a read of `kb/prior-kb`'s copy, with no write record and no pass memo bound,
  so the read records nothing and answers from the copy alone.  `body` realizes what it
  answers."
  [& body]
  `(binding [observe/*write-record*        nil
             observe/*handle-cache*        nil
             observe/*reach-memo*          nil
             observe/*held-values*         nil
             tax/*visible-neighbours-cache* nil
             res/*membership-memo*         nil
             inherit/*memo*                nil
             exc/*routes*                  nil]
     ~@body))

(defn- edge-write-seeds
  "The handles the `genlCx` edge moves `ms` (`special/context-move`) can move the belief of
  at their own contexts: each move names the contexts whose ancestor sets it changes (`:under`)
  and the contexts it shows or hides (`:moved`, `:raw`).  The seeds are the targets of
  the defeats and the members of the `contradicts` stored in those contexts, and the
  nogood candidates stated under the edge, where a placement it gives or takes hides one
  at its own context."
  [kb ms]
  (let [recs  (:records kb)
        idx   (:index kb)
        under (into #{} (mapcat #(deref (:under %))) ms)
        ctxs  (into under (mapcat #(concat (:moved %) (:raw %))) ms)
        named (fn [f] (into [] (comp (keep #(p/get-sentex recs %))
                                     (mapcat #(rest (:sentence %)))
                                     (keep sx/handle-id))
                            (reads/as-stored-with-functor-in idx f ctxs)))]
    (-> #{}
        (into (named sx/defeat-functor))
        (into (named 'contradicts))
        (into (decide/handles-at (decide/synced kb) under)))))

(defn- edge-declaration-seeds
  "The handles the `genlCx` edge moves `ms` (`special/context-move`) can move the forced-monotonic
  reading of: for each predicate a believed declaration stated in a context a move shows
  or hides makes forced-monotonic (`decide/declared`), its stored facts and their stored denials
  stated under that move's edge.  A reader under the edge gains or loses the declaration,
  and the read walk alone hides a void firing and re-decides a denial's defeat there."
  [kb ms]
  (let [declared (decide/declared (reasoning/taxonomy kb))]
    (when (seq declared)
      (let [idx  (:index kb)
            recs (:records kb)]
        (into #{} (mapcat (fn [m]
                            (let [shown (into (set (:moved m)) (:raw m))
                                  preds (into #{} (keep (fn [[[_ pred] decls]]
                                                          (when (some shown (vals decls)) pred)))
                                              declared)]
                              (when (seq preds)
                                (let [under @(:under m)]
                                  (concat (mapcat #(reads/as-stored-with-functor-in idx % under) preds)
                                          (filter #(let [d (:sentence (p/get-sentex recs %))]
                                                     (and (sx/negation? d) (contains? preds (nm/functor (second d)))))
                                                  (when (reads/stores-opposed? idx)
                                                    (reads/as-stored-opposed-in idx under)))))))))
              ms)))))

(defn- sentence-seeds
  "The handles a sentex `sx` of `k` (the KB, or `kb/prior-kb`'s copy) that the write stored,
  removed or relabelled moves the own-context reading of with no relabel of its own: the
  handles it names (an `except`'s, a `defeat`'s, a `(contradicts …)`'s), the facts a
  forced-monotonic declaration reaches (`chain/declaration-reach`), and, while a placement
  can be exempt (`exempt?`) and its functor is interpreted or a disjoint metatype, the
  memberships of every type under a symbol it names and the handles naming a term of
  each symbol's equality class (`decide/exempt-at?`'s inputs).  The types are read over
  every context's `genl` edges, a superset of what any reader sees, and each handle's
  reading is then decided at its own context."
  [k sx exempt?]
  (let [s   (sx/sentence-of sx)
        tax (reasoning/taxonomy k)
        idx (:index k)
        f   (when (seq? s) (first s))]
    (concat (keep sx/handle-id (when (seq? s) (rest s)))
            (chain/declaration-reach k s (:context sx))
            (when (and exempt? (symbol? f)
                       (or (and (pr/entry f) (not (contains? pr/belief-free f)))
                           (tax/stored-disjoint-metatype? tax f)))
              (let [syms (filter #(and (symbol? %) (not (sx/variable? %))) (rest s))]
                (concat (mapcat #(reads/as-stored-with-functor idx %)
                                (into #{} (mapcat #(tax/specs-global tax %)) syms))
                        (mapcat #(reads/as-stored-with-term idx %)
                                (into #{} (mapcat #(tax/equiv-class tax %)) syms))))))))

(defn- report-reach
  "The handles a settle's report reads beside the moved region (`moved`): every handle walked
  forward (`kb/moved-reach`), in `kb` and in its copy before the write `pk` when there is
  one, from the handles the write can move the own-context belief of with no relabel.
  Those are `moved`, the sentexes the write stored, deleted or respelled, the handles
  whose support the network moved (`jtms/moved-supports`), what each of those sentexes
  moves (`sentence-seeds`), and what the `genlCx` moves the settle drained reach
  (`edge-write-seeds`, `edge-declaration-seeds`).  Empty when neither KB owes the read
  walk (`exc/walk-reads?`): no handle is then hidden on either side."
  [kb pk moved]
  (let [both (fn [f] (cond-> (f kb) pk (into (reading-prior (f pk)))))]
    (if-not (seq (both #(when (exc/walk-reads? %) [true])))
      #{}
      (let [exempt? (boolean (seq (both #(when (exc/exemption-reads? %) [true]))))
            changed (into (set moved) (kb/recorded-sentexes kb))
            moves   (some-> ^java.util.List (observe/recorded ::special/context-moves) seq vec)
            seeds   (-> changed
                        (into (jtms/moved-supports (reasoning/tms kb)))
                        (into (both (fn [k] (into #{} (mapcat #(when-let [sx (p/get-sentex (:records k) %)]
                                                                 (sentence-seeds k sx exempt?)))
                                                  changed))))
                        (cond-> moves (-> (into (edge-write-seeds kb moves))
                                          (into (edge-declaration-seeds kb moves)))))]
        (both #(kb/moved-reach % seeds))))))

(defn- defeat-belief-moves
  "`{:gone :back}`: the targets of the defeats `stored` that their own context no longer
  believes, and the targets of `removed` it believes again (`exc/believed-own?`) — the
  handles a defeat moved with no relabel, which a pass reads as it reads a relabelled
  one.  One progress line covers both."
  [kb [stored removed]]
  (if (and (empty? stored) (empty? removed))
    {:gone #{} :back #{}}
    (let [recs (:records kb)]
      (with-open [r (progress/start ::defeat-belief-moves "settle: read the defeats' own-context belief"
                                    (+ (count stored) (count removed)))]
        {:gone (into #{} (comp (keep #(some-> (p/get-sentex recs %) :sentence kb/defeat-target))
                               (remove #(exc/believed-own? kb %)))
                     (progress/each r stored))
         :back (into #{} (comp (map first) (filter #(exc/believed-own? kb %)))
                     (progress/each r removed))}))))

(defn- pass-belief
  "`[was-in believed?]` for a pass: the relabelled handles believed before the settle
  (`jtms/touched-in`) with the targets a defeat moved (`moves`, `defeat-belief-moves`)
  folded in, and belief now: the network's, and for a moved target its own context's."
  [kb {:keys [gone back]}]
  (let [tms   (reasoning/tms kb)
        moved (into (set gone) back)]
    [(as-> (jtms/touched-in tms) w
       (into w gone)
       (reduce disj w back))
     (if (empty? moved)
       #(jtms/in? tms %)
       #(and (jtms/in? tms %) (or (not (contains? moved %)) (exc/believed-own? kb %))))]))

(defn- post-defeat-moves!
  "Post the re-check each `defeat` relabelled in `region` (the pass's `touched`, as a
  delay) or among `placed`, the handles this pass placed, and not in `read` (a volatile
  set, which this adds them to, so each is posted once a settle), owes its target's watchers
  (`special/recheck-defeat-target`): a defeat moves the belief of its target, and of what
  rests on the target, with no relabel of either.  While a watched rule is stored, each
  handle of `kb/defeat-reach` over those defeats posts its sentence
  (`special/recheck-on-sentence`): a defeat in a target's closure moves in force with the
  target, so its own target and that target's closure are posted too.  The pass drains
  what this queues, and releases a firing the move unblocks from the refusal record
  (`recheck/released-refusals`).  Reads `region` only while a defeat is stored.  It
  fetches a record per handle read, or per stored `defeat` where fewer are stored."
  [kb region placed read]
  (let [idx (:index kb)
        nd  (reads/stored-count-at idx [sx/defeat-functor])]
    (when (pos? nd)
      (let [recs  (:records kb)
            fresh (into [] (remove @read) (concat @region placed))
            _     (vswap! read into fresh)
            ;; a `recover`'s region is the whole store, and the defeat extent the smaller read
            cands (if (< nd (count fresh))
                    (filter (set (reads/as-stored-with-functor idx sx/defeat-functor)) fresh)
                    fresh)
            ds    (into [] (keep #(let [sx (p/get-sentex recs %)]
                                    (when (kb/defeat-target (:sentence sx)) sx)))
                        cands)]
        (doseq [sx ds] (special/recheck-defeat-target kb sx))
        (when (and (seq ds) (pos? (reads/watched-rule-count idx)))
          (doseq [h (kb/defeat-reach kb (map :id ds) #{})
                  :let [s (p/get-sentex recs h)]
                  :when s]
            (special/recheck-on-sentence kb (sx/sentence-of s))))))))

(defn- revived-seeds
  "The datums `jtms/revived` finds in `region` (the pass's `touched`, as a delay) and
  `released` (`chain/place-nogoods!`'s, relabelled after `region` was read), minus `done`,
  the ones an earlier pass of this settle already re-seeded.  Nil during a rebuild
  (docs/nmtms.md, \"A revived datum is a datum the agenda has not seen\")."
  [kb done region released]
  (when-not *rebuilding?*
    (into [] (remove done) (jtms/revived (reasoning/tms kb) (cond-> @region (seq released) (into released))))))

(defn- departed-handles
  "The handles in `region` (the pass's `touched`, as a delay) that went IN ⇒ OUT this
  settle, by a relabel: the set `departed-seeds` and `defeated-derivation-seeds` both
  read.  Empty during a rebuild."
  [kb region]
  (if *rebuilding?*
    []
    (let [tms (reasoning/tms kb)
          was (jtms/touched-in tms)]
      (into [] (filter #(and (contains? was %) (not (jtms/in? tms %)))) @region))))

(defn- departed-seeds
  "The facts owed a re-join because a `genl` or `genlCx` edge in `out` (`departed-handles`)
  went IN ⇒ OUT or was withdrawn at its own context, minus `done`
  (`special/departed-edge-seeds`).  A verdict sweeps nothing, so this is the re-join a
  retraction gets from `special/resubsumption-seeds`
  (docs/nmtms.md, \"Where the layer stops\")."
  [kb done out]
  (when (seq out)
    (into [] (remove done) (special/departed-edge-seeds kb out))))

(defn- lost-derivation-seeds
  "Draw `justs` (`special/lost-descended-derivations`) again over a route that survives,
  and return the handles that created and each conclusion the new justification brought
  back IN, as seeds.  The second is what makes the pass that drew it productive, so the
  next pass reads the region the new support moved."
  [kb justs]
  (if (seq justs)
    (let [tms (reasoning/tms kb)]
      (into (special/rederive-descended kb justs)
            (comp (map :consequence) (distinct) (filter #(jtms/in? tms %)))
            justs))
    []))

(defn- defeated-derivation-seeds
  "The argument-type entailments and descended equalities a `genl` edge took OUT or
  withdrew at their own context when this settle withdrew it, drawn again over a route
  that survives — `departed-seeds`' twin for the derivations that name the edge rather
  than for the firings.  An equality whose facts a withdrawn merge still supersedes is
  drawn by `settle`'s un-merge round instead, once the spellings are back.

  `out` is `departed-handles`' answer for the pass."
  [kb out]
  (if (seq out)
    (lost-derivation-seeds kb (special/lost-descended-derivations kb out true))
    []))

(defn- narrow-marker?
  "Is `t` a withdrawal marker whose re-derivations a settle chains narrowly rather than
  over the rule's extent: an `except`'s move, chained from the moved target's consequence
  closure (`special/drain-except-moves!`), a separation or `nonempty` move, re-joined over
  the types it moved (`typed-rejoins`), or a merge's class queued for a rule whose only
  re-check condition is `different`, which the merge can withdraw and never release
  (`special/recheck-equality-edge`)?"
  [t]
  (boolean (and (map? t) (or (::special/except-closure t) (::special/separation t)
                             (::special/nonempty t) (::special/merged t)))))

(defn- typed-rejoins
  "`{rule-handle types}` for the rules of the re-check queue `queued` queued with a
  `{::separation types}` or `{::nonempty types}` marker, the types of every such marker on
  one rule merged."
  [queued]
  (into {} (keep (fn [[rh ts]]
                   (when (set? ts)
                     (when-let [ms (seq (keep #(or (::special/separation %) (::special/nonempty %)) ts))]
                       [rh (into #{} cat ms)]))))
        queued))

(defn- blanket-recheck-rules
  "The queued rules with no triggering sentence (`:all` or `:all-rejoin`: a taxonomy edge
  moved, or the rule was just indexed) or with a withdrawal marker other than a
  `narrow-marker?`.  They take the coarse re-chain, since nothing says
  whether the move blocked or released."
  [queued]
  (keep (fn [[rh triggers]]
          (when (or (#{:all :all-rejoin} triggers)
                    (some #(and (recheck/withdrawal-marker? %) (not (narrow-marker? %)))
                          triggers))
            rh))
        queued))

(defn- forced-recheck-rules
  "The unconditional rechecks that also owe a fresh join when blocking stayed still."
  [queued]
  (keep (fn [[rh triggers]] (when (= :all-rejoin triggers) rh)) queued))

(defn- rejoin-on-arrival-rules
  "The queued rules an arriving fact can release rather than only block
  (`special/arrival-releasable-rule?`: an aggregate or a nested NAF, in an antecedent or
  an exception), which are re-joined whatever the blocked set did (docs/exceptions.md,
  \"Re-chaining what was released, not what was touched\")."
  [kb queued]
  (keep (fn [[rh _]] (when (special/arrival-releasable-rule? kb rh) rh)) queued))

(defn- released-narrowly?
  "Does a settle release every firing of the rule at `rh` that a queued sentence unblocks,
  from the blocked set and the refusal record alone?  True for a stored rule whose only
  re-check conditions are `exceptWhen` exceptions and `unknown` antecedents, the block
  literals `recheck/exception-candidates` and `recheck/released-refusals` narrow by."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (and (not (rules/has-different? rsx))
         (not (rules/has-aggregate? rsx))
         (empty? (chain/closed-extent-antecedents kb (:antecedent rsx))))))

(defn rechain-owed
  "The rules of the re-check queue `queued` a teardown re-chains over their extent
  (`rechain-exception-rules`): every one but a rule queued only for `narrow-marker?`
  moves, and a rule queued only for sentences and those moves
  that the settle releases narrowly (`released-narrowly?`): a firing its block refused or
  swept is in the refusal record (`chain/record-swept-firing!`)."
  [kb queued]
  (into [] (keep (fn [[rh ts]]
                   (when-not (and (set? ts) (seq ts)
                                  (or (every? narrow-marker? ts)
                                      (and (not-any? #(and (recheck/withdrawal-marker? %)
                                                           (not (narrow-marker? %)))
                                                     ts)
                                           (released-narrowly? kb rh))))
                     rh)))
        queued))

(defn rechain-exception-rules
  "Re-chain the stored, believed forward rules among `rule-handles` over their whole
  extent, to re-derive what a released exception suppressed, and re-join the readers of
  each lazy-forward rule among them (`chain/lazy-readers`).  A firing whose conclusion
  stands or whose exception still holds places nothing.  Each rule costs one join over its
  extent, so callers pass the released rules rather than the queued ones
  (docs/exceptions.md).  Uses `chain`, not `chain-all`: the violations ledger is scoped to
  the caller's run."
  [kb rule-handles]
  (let [live (filter (fn [rh]
                       (let [rsx (p/get-sentex (:records kb) rh)]
                         (and rsx (rules/rule? rsx)
                              (or (rules/forward-sentex? rsx) (rules/lazy-sentex? rsx))
                              (jtms/in? (reasoning/tms kb) rh))))
                     rule-handles)]
    (when (seq live)
      (with-open [r (progress/start ::rechain-exception-rules "settle: re-chain the released rules (derivations)" nil)]
        (chain/chain kb live {:on-progress (progress/on-progress r)})))))

(defn rechain-seeds
  "Re-chain from `seeds`, the datum handles something put back on the agenda, filtered to
  what is still stored and believed.  One join per rule keyed by each datum's predicate,
  as an assert pays (docs/nmtms.md, \"A revived datum is a datum the agenda has not
  seen\").  Uses `chain`, not `chain-all`, as `rechain-exception-rules` does."
  [kb seeds]
  ;; `distinct`: each genlCx move of a pass seeds the facts its readers see, and on a
  ;; loaded ontology those are the same facts for every move
  (let [live (into [] (comp (distinct)
                            (filter (fn [h] (and (p/get-sentex (:records kb) h)
                                                 (jtms/in? (reasoning/tms kb) h)))))
                   seeds)]
    (when (seq live)
      (with-open [r (progress/start ::rechain-seeds "settle: re-chain the revived data (derivations)" nil)]
        (chain/chain kb live {:on-progress (progress/on-progress r)})))))

(defn- settle-finish
  "Reconcile the derived caches with settled belief, publish the moved region to the
  sinks and the feed, file a calculus network the region made unsatisfiable
  (`qkb/report-moved!`), and clear the touched set.  `belief-moved?` decides whether
  the first `refresh-beliefs` reconcile runs.  Returns the spellings superseded since the
  last settle, for `settle` to withdraw the firings over (`withdraw-retired-firings!`),
  and on a rebuild's first settle every superseded spelling; empty with `*sweep?*` off.
  `dmoves` is the last pass's `defeat-belief-moves`, nil when a pass applied after it.
  The order and each condition: docs/nmtms.md, \"What `settle-finish` reconciles\"."
  [kb region passes moved belief-moved? dmoves]
  ;; a potential the passes left loose; free when none is
  (tax/restore-depths (reasoning/taxonomy kb))
  (let [extra    (volatile! #{})     ; region members no relabel recorded
        opened   (volatile! {})      ; the superseded map when the settle began
        retired  (volatile! [])]     ; the spellings superseded since the last settle
    ;; forces the region only on a timing run (`settle_region_cost_test` counts reads)
    (when (phases/profiling?) (phases/note-region! (count @region)))
    (when belief-moved?
      (special/reconcile-belief-change kb @region)
      ;; the reconcile can open or close a cycle (docs/taxonomy.md)
      (tax/restore-depths (reasoning/taxonomy kb)))
    ;; an equality supporter a reconcile found believed again restates its class, as its
    ;; arrival does; `settle` re-seeds the supporter and its twins
    (when-let [hs (tax/take-believed-again! (reasoning/taxonomy kb))]
      (when-not *rebuilding?*
        (let [mig (special/believed-again-sweeps kb hs)]
          (when (seq (:superseded mig))
            (special/refresh-supersessions kb (:superseded mig)))
          (violations/report kb (:violations mig))
          (vswap! extra into (:new mig))
          (some-> *unmerged-sink* (vswap! into (concat hs (special/minted-seeds kb (:new mig))))))))
    (let [ex (special/take-except-moves! kb)]
      ;; the write path reconciles every supersession a stored or removed sentence moves;
      ;; the settle owes it only for an `except` that moved and an equality edge that
      ;; moved in belief
      (when (or (seq (:extra ex)) (seq (:region ex)) (:full? ex)
                (tax/equality-moves? (reasoning/taxonomy kb) :supersessions))
        (special/refresh-supersessions kb (:extra ex) (when-not (:full? ex) (set (:region ex)))))
      ;; a corresponding fact that moved in belief or class moves the values it names: a
      ;; relabelled one, and a defeat's or an `except`'s target, whose belief or
      ;; visibility the defeat or the `except` moves with no relabel.  An `except`'s
      ;; target also moves the constants it names, as a write of it does: a use the
      ;; `except` hid or showed is a copy's source
      (when-not *rebuilding?*
        (let [{:keys [gone back]} (or dmoves (defeat-belief-moves kb (defeat-moves kb (set @region))))
              hs (cond-> (-> #{} (into gone) (into back))
                   belief-moved? (into @region))
              sentences #(keep (fn [h] (:sentence (p/get-sentex (:records kb) h))) %)]
          (when (and (or (seq hs) (seq (:moved ex))) (nat-read/values-reachable? kb))
            (nat-read/note-values kb (sentences hs) false)
            (nat-read/note-values kb (sentences (:moved ex)) true)))))
    ;; `moved` is every datum whose supersession entry changed since the last settle
    ;; finished, and `was` its entry before the first change, so `before` and `after` are
    ;; the superseded maps of the last settle and this one
    (let [after  (jtms/superseded (reasoning/tms kb))
          {:keys [moved was]} (or (special/take-supersession-moves! kb) {:moved #{} :was {}})
          before (vreset! opened (reduce (fn [m d] (if-let [e (get was d)] (assoc m d e) (dissoc m d)))
                                         after moved))]
      (vswap! extra into moved)
      ;; a merge supersedes a declaration with no label moving, after the reconcile above
      (when (seq moved)
        (special/reconcile-belief-change kb (into @region moved)))
      ;; the spellings an un-merge gave back, for `settle` to re-seed
      (when-let [sink (and (not *rebuilding?*) *unmerged-sink*)]
        (vswap! sink into
                (filter #(and (contains? before %) (not (contains? after %))
                              (jtms/in? (reasoning/tms kb) %)))
                moved))
      ;; ...and the spellings a merge retired, for `settle` to withdraw the firings over;
      ;; a rebuild's first settle reads every superseded spelling, since a store written
      ;; before the withdrawal holds firings over them
      (when *sweep?*
        (vreset! retired (if (and *rebuilding?* discovery/*whole-store-region?*)
                           (vec (keys after))
                           (filterv #(and (contains? after %) (not (contains? before %))) moved)))))
    ;; a network the settle made unsatisfiable files its ledger entry here, whether or
    ;; not a rule or a read asks it, before the feed event that carries it (docs/qcn.md,
    ;; "The settle asks every write")
    (cond
      *rebuilding?*        (qkb/forget-settled kb)
      (qkb/settles? kb)    (qkb/report-moved! kb @region @extra))
    ;; the published set is built only when a sink is bound or a listener registered
    (let [sink    *touched-sink*
          in-sink *touched-in-sink*
          fed?    (and (not *rebuilding?*) (feed/wants-region? kb))]
      (when (or sink in-sink fed?)
        (let [tms    (reasoning/tms kb)
              ;; the KB as it stood when the write record opened; with none open, a
              ;; handle reads as hidden before the write as it reads now
              pk     (when observe/*write-record* (kb/prior-kb kb))
              moved  (-> @extra (into @region))
              moved  (into moved (report-reach kb pk moved))
              ;; the label when the settle began: `touched-in` for a relabelled handle,
              ;; and the label it holds now, less the `:held` set, for any other.  A
              ;; spelling superseded when the settle began was not believed, whatever its
              ;; label.
              tin    (jtms/touched-in tms)
              label? #(if (contains? @region %)
                        (contains? tin %)
                        (and (jtms/network-in? tms %) (not (jtms/forced? tms :held %))))
              open?  #(not (contains? @opened %))
              cands  (filterv #(and (label? %) (open? %)) moved)
              hidden (if pk
                       (reading-prior (if-let [hid (exc/own-hidden-fn pk)] (into #{} (filter hid) cands) #{}))
                       (if-let [hid (exc/own-hidden-fn kb)] (into #{} (filter hid) cands) #{}))
              was-in (into #{} (remove hidden) cands)]
          (when sink    (swap! sink into moved))
          (when in-sink (swap! in-sink into was-in))
          (when fed?    (feed/note-region! kb moved was-in)))))
    (discovery/note-touched! kb @extra)
    (kb/note-reach-touched! kb)
    (jtms/reset-touched! (reasoning/tms kb))
    ;; the next report diffs against the belief this one published
    (some-> ^java.util.Map observe/*write-record* .clear)
    (swap! (reasoning/settle-stats kb)
           (fn [s] (-> s
                       (assoc :iterations moved :passes passes)
                       (update-in [:histogram moved] (fnil inc 0)))))
    ;; the pass count says whether the KB's exceptions have started to interact
    (trove/log! {:level :debug :id ::settled
                 :data {:passes     passes
                        :iterations moved
                        :moved?     belief-moved?}})
    @retired))

(defn- finish-settle
  "Close one settle: note the pass count for `settle-phases`, run `settle-finish` inside
  the `:finish` span, and file this settle's record.  Every `settle*` return runs
  through here."
  [kb passes moved belief-moved? dmoves]
  (phases/note-passes! passes)
  ;; one materialized region for the finish's reads
  (let [region (delay (jtms/touched (reasoning/tms kb)))
        r      (phases/with-phase :finish
                 (settle-finish kb region passes moved belief-moved? dmoves))]
    (phases/end-settle!)
    r))

;; ---- one pass -------------------------------------------------------------------
;; A pass reads what it owes (`pass-work`), what the queued exceptions block
;; (`block-work`), and applies both (`apply-pass!`).  It has converged when it queues,
;; blocks and owes nothing.

(def ^:private owed
  "The keys of `pass-work` a pass applies whatever the blocked set does: the datums whose
  belief came back, the facts a departed edge owes a re-join, the mints, lifts and merges
  owed, and the mint placements a
  `genlCx` edge displaced (`:dropped`, applied by `pass-work` itself), so the pass after
  a drop drains what the drop queued."
  [:revived :departed :mnew :dropped])

(defn- owes-nothing?
  "Is every key of `ks` empty in the pass work `w`?"
  [w ks]
  (every? #(empty? (get w %)) ks))

(defn- pass-work
  "One pass's reads, before anything is blocked or re-chained, as a map: the inherited
  clashes found and placed first (`chain/place-inherited!`); the drained re-check queue
  (`:queued`); every key of `owed`; the targets a removed defeat gave back (`:back`); and
  the mints this pass withdraws (`:wdrawn`, `subsumed-blocks`).  `:region` is the relabelled touched set, read
  again when a merge this pass owed moved it.  The second argument is the settle's
  state: `:region`, `:reseeded` (what earlier passes seeded), the sets `:checked` of the
  handles the placement and the defeat re-checks read, and the volatiles of `:asked`."
  [kb {:keys [region reseeded checked asked]}]
  ;; a rebuild decides the argument holds `recover` emptied before a family reads a
  ;; label, as a live KB decides them at the write; otherwise `place-nogoods!` does
  (when *rebuilding?* (checks/refresh-argument-holds! kb (special/conviction-generations kb)))
  ;; the merges a collision member's class moving owes, before the discovery reads the
  ;; pairs they reconcile
  (let [remerge (class-moved-merge-seeds kb region (:merge asked))
        region  (if (seq remerge) (delay (jtms/touched (reasoning/tms kb))) region)
        ;; the `genlCx` moves since the last pass, each handed to every family it moves
        ;; (`special/drain-context-moves!`): their re-checks are queued before the drain
        ;; below, and the placement families read their reach
        moves   (special/drain-context-moves! kb (:genlcx checked) *rebuilding?*)
        ;; the inherited clashes found and placed, before the other families place
        inh     (phases/with-phase :discovery (chain/place-inherited! kb region moves))
        ;; the nogoods whose placement can have moved, placed again; a defeat stored
        ;; there posts its target's re-check before the drain.  The types a declaration
        ;; could not mint until its type lost another length mint there too (`:minted`)
        placed  (when-not *rebuilding?* (chain/place-nogoods! kb region (:negations checked) moves))
        negs    (into inh (:made placed))
        ;; a defeat stored or relabelled moves its target's belief with no relabel of the
        ;; target, and queues the rules watching it for the drain below
        _       (post-defeat-moves! kb region negs (:defeats checked))
        _       (when-not *rebuilding?* (special/recheck-route-gains! kb))
        queued  (drain-recheck! kb)
        ;; the targets whose own-context belief a defeat moved with no relabel
        dmoves  (if *rebuilding?* {} (defeat-belief-moves kb (defeat-moves kb (set @region))))
        ;; the datums whose belief came back, and the targets a removed defeat gave back;
        ;; `reseeded` seeds each once per settle, since the touched set spans the settle.  A
        ;; given-back target is re-chained only when the taxonomy derives from it
        ;; (`tax/derives-from?`): the network kept it IN, so a rule's firings over it stand
        rs      (vec (revived-seeds kb reseeded region (:released placed)))
        back    (into [] (remove reseeded) (:back dmoves))
        revived (into rs (filter #(tax/derives-from? (reasoning/taxonomy kb) %)) back)
        _       (special/note-producer-moves! :arrived (into rs back))
        ;; the facts under an edge a firing named that this settle defeated, whose second
        ;; route nothing else re-joins (`departed-seeds`)
        out      (departed-handles kb region)
        departed (departed-seeds kb reseeded out)
        ;; the merges and lifts a revived mark owes the facts that arrived while it was
        ;; OUT, the twins an `except` that began or stopped hiding an equality or a merge
        ;; mark owes, and the entailments and equalities a defeated genl edge took OUT
        ;; while a second route still licenses them
        mnew    (-> (into [] (:minted placed))
                    (into (revived-mark-seeds kb (into rs back)))
                    (into (revived-edge-seeds kb revived))
                    (into (except-move-seeds kb))
                    (into (context-move-seeds kb moves))
                    (into (defeated-derivation-seeds kb out))
                    (into remerge)
                    (into negs))
        ;; the relabelled records and the targets a defeat moved, read once for both
        ;; halves of the subsumption question
        rsx     (delay (into [] (keep #(p/get-sentex (:records kb) %))
                             (-> (set @region) (into (:gone dmoves)) (into (:back dmoves)))))
        [was-in believed?] (pass-belief kb dmoves)
        mnew    (-> mnew
                    (into (released-subsumed kb rsx was-in believed? (:release asked)
                                             @(:withdrawn asked)))
                    ;; the interArg and homogeneity entailments a trigger arriving
                    ;; after its facts owes them
                    (into (triggered-seeds kb rsx was-in believed? (:trigger asked)))
                    ;; the class memberships a relabelled `genl` edge or class membership
                    ;; moves (`chain/arity-classes-moved!`)
                    (into (arity-class-seeds kb region)))
        ;; the other direction of the subsumption question: the mints a membership
        ;; arriving this settle has made redundant, whose justifications this pass blocks
        ;; so the sweep collects the records
        wdrawn  (subsumed-blocks kb region rsx was-in believed? (:subsumption asked))
        ;; the mint placements a `genlCx` edge arriving this settle left below a more
        ;; general one, and the merge copies a more general merge covers
        dropped (drop-surplus-placements!
                 kb (into (or (:surplus wdrawn) (sorted-set))
                          (special/covered-merges kb (:covered moves))))]
    {:region region :queued queued :revived revived :back back :departed departed
     :mnew mnew :wdrawn wdrawn :dropped dropped :dmoves dmoves}))

(defn- guarded-records
  "The records of the rule firings among `cands`: the firings a guard, or a contrary
  claim of an inherited antecedent, can block."
  [kb cands]
  (let [tms (reasoning/tms kb)]
    (into [] (comp (filter #(special/firing-informant? kb (:informant (jtms/justification tms %))))
                   (keep #(p/get-justification (:records kb) %)))
          cands)))

(defn- block-work
  "`w` with what its queued exceptions block: the blocked set as it is (`:was`) and as the
  queue and the withdrawn mints leave it (`:new`), the visibility transitions that owe the
  blanket re-join whether or not anything blocked (`:forced`), the rules an arrival can
  release (`:aggs`), and the refusals the queue released (`:free`, and `:over` for an
  overflowed rule), the targets whose guard defeats moved (`:gmoved`), and the rules a
  separation move re-joins over the types it moved (`:sep`)."
  [kb {:keys [queued wdrawn] :as w}]
  (let [was  (jtms/blocked (reasoning/tms kb))
        cands (recheck/exception-candidates kb queued)
        new  (into (recheck/exception-blocked-set kb queued cands) (:blocked wdrawn))
        ;; the re-decided guarded firings place their guard defeats, before the sweep
        ;; deletes the blocked ones
        gmoved (chain/place-guard-defeats!
                kb (map (fn [j] [j (not (contains? new (:id j)))]) (guarded-records kb cands))
                *sweep?*)
        aggs (rejoin-on-arrival-rules kb queued)
        {free :free over :overflow} (recheck/released-refusals kb queued)]
    (assoc w :was was :new new :gmoved gmoved :forced (vec (forced-recheck-rules queued))
           :aggs aggs :free free :over over :sep (typed-rejoins queued))))

(defn- apply-pass!
  "Block what `w` blocks, sweep what that excepts, and re-chain what the pass owes: the
  released refusals, the revived datums and the mints on one agenda; the departed facts
  silently, as the retraction path's re-join is; and the rules the pass released.
  `asked` takes the mints withdrawn."
  [kb {:keys [was new wdrawn queued free revived mnew departed aggs over sep]}
   asked]
  ;; read before the sweep, which deletes justifications — and so are the re-joins the
  ;; withdrawn mints' firings owe (`special/withdrawn-edge-seeds`)
  (let [released (released-rules kb was new)
        wseeds   (when-not *rebuilding?*
                   (not-empty (special/withdrawn-edge-seeds kb (:withdrawn wdrawn))))]
    (vswap! (:withdrawn asked) into (:withdrawn wdrawn))
    (jtms/set-blocked (reasoning/tms kb) new)
    (sweep-excepted! kb (into #{} (remove was) new))
    ;; the rules the sweep queued; what the re-chains below queue the next pass drains
    ;; and re-decides narrowly
    (let [swept (keys @(reasoning/recheck kb))
          seeds (-> (into [] (mapcat (fn [[rh e]] (chain/release-refusal! kb rh e))) free)
                    (into revived)
                    (into mnew))]
      (when (seq seeds) (rechain-seeds kb seeds))
      ;; the re-join a defeated witness owes, silent where it places nothing
      ;; (`chain/*report-no-placement?*`)
      (when (seq departed)
        (binding [chain/*report-no-placement?* false] (rechain-seeds kb departed)))
      ;; ...and the one a withdrawn mint's firings owe, as silent for the same reason
      (when wseeds
        (binding [chain/*report-no-placement?* false] (rechain-seeds kb wseeds)))
      ;; only the rules this pass released, never every rule it touched: a rule seed
      ;; joins over the whole extent, except a rule a separation move alone queued, which
      ;; joins over the types it moved
      (let [full (into (set released) (concat (blanket-recheck-rules queued) aggs over swept))]
        (binding [chain/*moved-types* (apply dissoc sep full)]
          (rechain-exception-rules kb (into full (keys sep))))))))

;; ---- a settle that owes nothing -------------------------------------------------
;; docs/nmtms.md, "A settle that owes nothing"

(defn- empty-entry?
  "Is the value of the map entry `e` nil, false or an empty collection?"
  [[_ v]]
  (or (nil? v) (false? v) (and (coll? v) (empty? v))))

(def ^:private pass-queues
  "The KB's atoms a pass takes work from or fills, by name, each read by `queue-state`.
  `:drained-by` names the arms of `pass-work` that empty it, so a skip needs it empty
  (`idle-conditions`); `:sparse` marks one whose entries can sit empty, read with those
  dropped.  The nogood candidates hold the families' cursors, which the families answer
  for, and `settle` drains the respell queue after the passes."
  {:recheck   {:atom reasoning/recheck :drained-by #{#'drain-recheck!}}
   :except    {:atom reasoning/except-moves :sparse true
               :drained-by #{#'except-move-seeds #'special/recheck-route-gains!
                             #'special/drain-context-moves!}}
   :mints     {:atom reasoning/mint-queues :sparse true
               :drained-by #{#'released-subsumed #'subsumed-blocks #'special/drain-context-moves!}}
   :preserved {:atom reasoning/preserved-clashes :drained-by #{#'chain/place-inherited!}}
   :cands     {:atom reasoning/nogood-candidates :sparse true}
   :respell   {:atom reasoning/respell}})

(defn- queued
  "The queue `k` of `pass-queues` as `kb` holds it, its empty entries dropped where it is
  `:sparse`."
  [kb k]
  (let [{a :atom sparse? :sparse} (pass-queues k)
        v @(a kb)]
    (if sparse? (into {} (remove empty-entry?) v) v)))

(def ^:private cost-order
  "What a row of `idle-conditions` reads, cheapest first: the bindings, the KB's atoms, the
  taxonomy's sets, the labels of the touched set, the index's counts."
  [:binding :atom :taxonomy :region :index])

(def ^:private idle-conditions
  "The questions a skip asks, a row each: `:idle?` of the KB and the touched set (a delay)
  holds when the arms of `pass-work` the row names (`:arms`) owe nothing, and an arm answers
  empty when every row naming it holds.  Rows are asked in `cost-order` (`:cost`), so a
  write a queue rules out reads no index.  `:no-mint` reads every context's mint count, as
  the mint withdrawal it stands in for does (`special/subsumed-mint-blocks`).  Each call
  of `pass-work` is an arm of a row or one of `pass-reads`, and `vaelii.settle-skip-test`
  holds both lists to its body."
  (vec
   (sort-by
    (comp (zipmap cost-order (range)) :cost)
    (concat
     [{:id :plain-write :cost :binding :arms #{#'checks/refresh-argument-holds!}
       :idle? (fn [_ _] (and (not *rebuilding?*) *sweep?* (not *relabelled-before?*)))}]
     (for [[k {:keys [drained-by]}] pass-queues :when drained-by]
       {:id k :cost :atom :arms drained-by :idle? (fn [kb _] (empty? (queued kb k)))})
     [{:id :no-inherited-queued :cost :atom :arms #{#'chain/place-inherited!}
       :idle? (fn [kb _] (nil? (:inherited @(reasoning/nogood-candidates kb))))}
      {:id :no-context-move :cost :atom
       :arms #{#'special/drain-context-moves! #'context-move-seeds}
       :idle? (fn [kb _] (not (decide/edge-moved? kb)))}
      {:id :no-placement-queued :cost :atom :arms #{#'chain/place-nogoods! #'arity-class-seeds}
       :idle? (fn [kb _] (not (chain/placement-queued? kb)))}
      {:id :no-covered-merge :cost :taxonomy
       :arms #{#'special/covered-merges #'drop-surplus-placements!}
       :idle? (fn [kb _] (not (tax/equality-moves? (reasoning/taxonomy kb) :covers)))}
      {:id :no-merge-mark :cost :taxonomy :arms #{#'class-moved-merge-seeds}
       :idle? (fn [kb _] (let [tax (reasoning/taxonomy kb)]
                           (not (or (tax/functional-family-declared? tax)
                                    (seq (tax/props tax :anti-symmetric))))))}
      {:id :no-forced-declaration :cost :taxonomy :arms #{#'chain/place-inherited!}
       :idle? (fn [kb _] (empty? (decide/declared (reasoning/taxonomy kb))))}
      {:id :no-entailing-declaration :cost :taxonomy :arms #{#'triggered-seeds #'released-subsumed}
       :idle? (fn [kb _] (not (special/any-declaring? kb)))}
      {:id :no-standing-relabel :cost :region
       :arms #{#'revived-seeds #'revived-mark-seeds #'revived-edge-seeds #'arity-class-seeds}
       :idle? (fn [kb r] (let [tms (reasoning/tms kb) new (jtms/touched-new tms)]
                           (not-any? #(and (not (contains? new %)) (jtms/known-datum? tms %)) @r)))}
      {:id :no-departure-with-dependents :cost :region
       :arms #{#'departed-handles #'departed-seeds #'defeated-derivation-seeds}
       :idle? (fn [kb r] (let [tms (reasoning/tms kb) was (jtms/touched-in tms)]
                           (not-any? #(and (contains? was %) (not (jtms/in? tms %))
                                           (seq (jtms/dependents tms %)))
                                     @r)))}
      {:id :no-preserving-declaration :cost :index :arms #{#'chain/place-inherited!}
       :idle? (fn [kb _] (empty? (inherit/preserved-pairs kb)))}
      {:id :no-defeat-read :cost :index
       :arms #{#'post-defeat-moves! #'defeat-moves #'defeat-belief-moves}
       :idle? (fn [kb _] (not (exc/placed-reads? kb)))}
      {:id :no-removed-defeat :cost :index
       :arms #{#'defeat-moves #'defeat-belief-moves #'revived-mark-seeds #'revived-edge-seeds}
       :idle? (fn [kb _] (empty? (removed-moves kb (jtms/touched-in (reasoning/tms kb)))))}
      {:id :no-mint :cost :index :arms #{#'subsumed-blocks #'drop-surplus-placements!}
       :idle? (fn [kb _] (zero? (reads/stored-mint-count-global (:index kb))))}
      {:id :no-nogood-held :cost :index :arms #{#'chain/place-nogoods! #'chain/place-inherited!}
       :idle? (fn [kb _] (not (chain/nogoods-held? kb)))}
      {:id :no-arity-read :cost :index :arms #{#'chain/place-nogoods!}
       :idle? (fn [kb r] (not (arity/relabel-owed? kb @r)))}]))))

#_{:clj-kondo/ignore [:unused-private-var]}
(def ^:private pass-reads
  "The calls of `pass-work` that read the KB or note a move and owe nothing, so no row of
  `idle-conditions` names them.  Read by `vaelii.settle-skip-test` alone."
  #{#'reasoning/tms #'reasoning/taxonomy #'jtms/touched #'p/get-sentex #'tax/derives-from?
    #'special/conviction-generations #'special/note-producer-moves! #'pass-belief})

(defn- owes-nothing-up-front?
  "Does every row of `idle-conditions` hold over `region`, the touched set as a delay?
  Then every arm of `pass-work` answers nothing, and `settle*` closes the settle at pass 1."
  [kb region]
  (every? (fn [{:keys [idle?]}] (idle? kb region)) idle-conditions))

(def ^:dynamic *check-skip?*
  "When true, a settle that skips its pass (`owes-nothing-up-front?`) runs the pass anyway
  and throws `::skip-owed` if the pass owed or moved anything (`check-skip!`).  Off in the
  engine; the test suite turns it on (`vaelii.test-util`), so a row of `idle-conditions`
  that answers idle too often fails the suite (docs/nmtms.md)."
  false)

(defn- pass-state
  "The settle's state across its passes, fresh: the records `:asked` each question in
  each direction (`subsumed-blocks`, `released-subsumed`), the merges asked, the mints
  withdrawn and the records asked what they trigger (`triggered-seeds`); and the handles
  `:checked` by `chain/place-nogoods!`, by the defeat posts and by the context-move drain."
  []
  {:asked   {:subsumption (volatile! #{}) :release (volatile! #{})
             :merge (volatile! #{}) :withdrawn (volatile! #{}) :trigger (volatile! #{})}
   :checked {:negations (volatile! #{}) :defeats (volatile! #{}) :genlcx (volatile! #{})}})

(defn- queue-state
  "Every queue of `pass-queues` (`queued`), the blocked set and the touched set, for
  `check-skip!` to compare."
  [kb]
  (let [tms (reasoning/tms kb)]
    (-> (into {} (map (fn [k] [k (queued kb k)])) (keys pass-queues))
        (assoc :blocked (jtms/blocked tms) :touched (set (jtms/touched tms))))))

(defn- check-skip!
  "Run the first pass a skip left out, and throw `::skip-owed` when it would not have
  closed the settle at pass 1 with nothing applied: it queued, withdrew, revived, gave
  back or owed anything, a defeat moved a target, the arity family owes a refresh, or a
  queue moved (`queue-state`)."
  [kb region]
  (let [before (queue-state kb)
        w      (pass-work kb (assoc (pass-state) :region region :reseeded #{}))
        arity? (arity/moved? (reasoning/taxonomy kb) @(reasoning/nogood-candidates kb))
        after  (queue-state kb)
        found  (into {} (remove empty-entry?)
                     (-> (select-keys w (into owed [:queued :back]))
                         (assoc :wdrawn (into {} (remove empty-entry?) (:wdrawn w))
                                :dmoves (into {} (remove empty-entry?) (:dmoves w))
                                :arity? arity?)))
        moved  (into {} (keep (fn [k] (when (not= (k before) (k after)) [k [(k before) (k after)]])))
                     (keys before))]
    (when (or (seq found) (seq moved))
      (throw (ex-info "a settle skipped a pass that owed work"
                      {:type ::skip-owed :found found :moved moved})))))

(defn- settle*
  "Relabel, find the inherited clashes, and re-evaluate the `exceptWhen` exceptions the
  triggers queued, to a joint fixpoint of at most `max-settle-passes` passes.  A pass
  that leaves the blocked set as it was (`set-blocked` replaces), queues, revives and
  releases nothing, and leaves the arity family no refresh owed (`arity/moved?`) ends the
  loop; every other pass counts in `settle-stats`' `:iterations`.  A settle that owes
  nothing up front (`owes-nothing-up-front?`) runs no pass.  Returns the spellings
  superseded since the last settle (`settle-finish`)."
  [kb]
  ;; one `settle-phases` record per settle, filed by `finish-settle` at each return
  (phases/begin-settle!)
  ;; belief moves by a block change or a caller's relabel before the settle, and
  ;; `moved?` is the `belief-moved?` condition over them
  (let [moved? (fn [moved] (or *relabelled-before?* (pos? moved)))]
    ;; reconcile the caches with what a caller relabelled before discovery reads them: a
    ;; revived `genl` or `genlCx` edge can make a pair jointly visible.  The region is
    ;; read once per pass into a delay (docs/nmtms.md, "The runtime state").
    (let [region (delay (jtms/touched (reasoning/tms kb)))
          _      (phases/with-phase :belief
                   (when *relabelled-before?*
                     (special/reconcile-belief-change kb @region))
                   ;; the depth repair a `with-deferred-settle` batch owes, before the
                   ;; passes read `genl?`, which walks a loose relation unpruned
                   (tax/restore-depths (reasoning/taxonomy kb)))
          {:keys [asked checked]} (pass-state)]
      (if (owes-nothing-up-front? kb region)
        (do (when *check-skip?* (check-skip! kb region))
            (dur/check-abort!)
            (finish-settle kb 1 0 false {:gone #{} :back #{}}))
        (loop [pass 1, moved 0, reseeded #{}, region region]
          ;; a pass boundary is a point a shutdown can stop a write at
          (dur/check-abort!)
          (let [w (pass-work kb {:region region :reseeded reseeded :checked checked :asked asked})
                ;; a length the pass moved after its arity refresh (the removal of a
                ;; `(unary_predicate T)` the refresh withdrew) owes the next pass's refresh,
                ;; which holds the tuples it breaks inert
                arity? (and (not *rebuilding?*)
                            (arity/moved? (reasoning/taxonomy kb) @(reasoning/nogood-candidates kb)))]
            (if (and (not arity?) (empty? (:queued w)) (empty? (:blocked (:wdrawn w))) (owes-nothing? w owed))
              (finish-settle kb pass moved (moved? moved) (:dmoves w))
              (let [w (block-work kb w)]
                (if (and (not arity?) (= (:new w) (:was w))
                         (owes-nothing? w (into owed [:forced :aggs :free :over :gmoved :sep])))
                  (finish-settle kb pass moved (moved? moved) (:dmoves w))   ; unproductive pass: converged
                  (do (apply-pass! kb w asked)
                      (if (< pass max-settle-passes)
                        (recur (inc pass) (inc moved)
                               (-> reseeded (into (:revived w)) (into (:back w)) (into (:departed w)))
                               (delay (jtms/touched (reasoning/tms kb))))
                        (do (trove/log! {:level :warn :id ::exception-fixpoint
                                         :msg  (str "exception re-check did not converge in "
                                                    max-settle-passes " passes; giving up")
                                         :data {:passes pass :blocked (count (:new w))}})
                            (finish-settle kb pass (inc moved) (moved? (inc moved)) nil)))))))))))))

(def ^:private max-unmerge-rounds
  "How many times `settle` re-seeds an un-merge and settles again before it logs
  `::unmerge-fixpoint` and stops (docs/nmtms.md, \"The other half: a spelling an un-merge
  gives back\")."
  8)

(defn- merge-support
  "The handles the merges superseding `retired` rest on: each restatement of a spelling in
  `retired` (a `rewriteOf` or `except` justification whose first antecedent it is) names
  its merges as the other antecedents, and this is those merges with their justification
  ancestors."
  [tms retired]
  (loop [todo (into []
                    (comp (mapcat (fn [d] (keep #(jtms/justification tms %) (jtms/dependents tms d))))
                          (filter #(#{'rewriteOf 'except} (:informant %)))
                          (mapcat #(rest (:antecedents %))))
                    retired)
         seen #{}]
    (if-let [h (peek todo)]
      (if (contains? seen h)
        (recur (pop todo) seen)
        (recur (into (pop todo)
                     (mapcat #(some-> (jtms/justification tms %) jtms/rests-on))
                     (jtms/supports tms h))
               (conj seen h)))
      seen)))

(defn- withdraw-retired-firings!
  "Drop each rule firing that names a spelling in `retired` as an antecedent or as its
  rule, and delete what the drop sweeps (`integrate/apply-removals!`).  A superseded
  spelling fires nothing (`chain/process-datum`), so the KB then holds the firings it
  holds when the merge arrived first.  A firing the superseding merge rests on (`merge-support`)
  stays, since no order makes that merge without it.  A dropped firing that climbed a
  retired `genl` edge is drawn again over the edge's twin (`special/withdrawn-edge-seeds`,
  read before the drop).  Returns true when a firing was dropped."
  [kb retired]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        held (delay (merge-support tms retired))
        jids (into (sorted-set)
                   (comp (mapcat #(jtms/dependents tms %))
                         (filter #(let [j (jtms/justification tms %)]
                                    (and (special/firing-informant? kb (:informant j))
                                         (not (contains? @held (:consequence j)))))))
                   retired)
        wseeds (when (seq jids) (not-empty (special/withdrawn-edge-seeds kb retired)))]
    (with-open [r (progress/start ::withdraw-retired "settle: withdraw the retired firings" (count jids))]
      (doseq [jid (progress/each r jids)
              ;; an earlier drop can have swept this one with its antecedent
              :when (jtms/justification tms jid)]
        (let [rm (jtms/drop-justification! tms jid)]
          (p/delete-justification! recs jid)
          (integrate/apply-removals! kb rm))))
    (when wseeds
      (binding [chain/*report-no-placement?* false] (rechain-seeds kb wseeds)))
    (boolean (seq jids))))

(defn- respelled-seeds
  "Drain the `:respell` queue, the predicates whose permuting marks moved in the settle just
  run, the `[:row h]` rows a write stored while their readers disagree on a mark, the
  `[:mention p]` predicates whose mention mark moved, the `[:reifiable f]` functions whose
  reifiable or permuting mark moved, the `[:reifiable-use f]` functions used while their
  readers disagree, the `[:corresponded f]` functions a `genlCx` move can re-spell rules
  through, and the `[:valued k]`, `[:valued-fn f]` and `[:valued-facts f]` constants whose
  correspondence derivations moved (`nat-read/note-values`), through the reconciles of
  `vaelii.impl.chain` and `chain/sync-values!`, and return `[respelled valued]`, the handles
  each made.  A rebuild clears the queue and respells nothing, since a recovered store was
  spelled when written.  With `*sweep?*` off the queue is kept, so `core/preview`'s rollback
  settle drains it against the restored KB and the handles stay the same."
  [kb]
  (let [q (reasoning/respell kb)]
    (when (seq @q)
      (cond
        *rebuilding?*    (do (reset! q #{}) nil)
        (not *sweep?*)   nil
        :else            (let [[moved] (swap-vals! q (constantly #{}))
                               tagged (fn [k] (into [] (comp (filter #(and (vector? %) (= k (first %))))
                                                             (map second))
                                                    moved))
                               fns    (tagged :reifiable)
                               ufns   (remove (set fns) (tagged :reifiable-use))
                               cfs    (remove (set fns) (tagged :corresponded))]
                           [(-> (chain/reconcile-spellings!
                                 kb (remove vector? moved)
                                 (distinct (into (tagged :row)
                                                 (mapcat #(integrate/rows-a-mention-spells kb %))
                                                 (tagged :mention))))
                                (into (when (seq fns) (chain/reconcile-reified! kb fns)))
                                (into (when (seq ufns) (chain/reconcile-reified! kb ufns nil false)))
                                (into (when (seq cfs) (chain/reconcile-corresponded! kb cfs))))
                            (chain/sync-values! kb (tagged :valued) (tagged :valued-fn)
                                                (tagged :valued-facts))])))))

(defn- hold-belief!
  "Hold the belief `kb` holds now for every other thread until `publish-belief!`, and
  return the hold, or nil when nothing is held: on a rebuild, and when a hold is open on
  the network already.  The network (`jtms/hold!`) and the candidate index, whose
  inherited clashes the settle re-finds (`observe/hold-atom!`), are held before
  `observe/open-hold!` registers the hold, so a reader switches to both at once (docs/nmtms.md, \"Two representations of the same
  network\")."
  [kb]
  (when-not *rebuilding?*
    (let [tms (reasoning/tms kb)
          sd  (reasoning/nogood-candidates kb)
          h   (observe/new-hold)]
      (when (jtms/hold! tms h)
        (observe/hold-atom! sd h)
        (observe/open-hold! h)
        [tms h sd]))))

(defn- publish-belief!
  "Publish what the settle decided under `held` (`hold-belief!`'s answer): close the hold,
  so every reader reads the belief the settle reached in one step, then drop what the
  network and the candidate index kept for it."
  [held]
  (when-let [[tms h sd] held]
    (observe/close-hold! h)
    (jtms/release! tms h)
    (observe/release-atom! sd)))

(defn settle
  "Settle belief (`settle*`) under a belief hold, re-settle while an un-merge gives
  spellings back or a merge retires spellings that fired (at most `max-unmerge-rounds`
  rounds), then deliver the moved region to the feed listeners, outside the relabel so a
  listener's write starts a fresh settle.  Returns nil.  The rounds: docs/nmtms.md,
  \"The other half: a spelling an un-merge gives back\"."
  [kb]
  (binding [special/*release-withheld?* (and special/*release-withheld?*
                                             (not (special/take-first-deferral! kb)))
            rules/*stratification-memo* (or rules/*stratification-memo* (volatile! nil))
            rules/*negated-keys-memo*   (or rules/*negated-keys-memo* (volatile! nil))
            exc/*reader-states*         (or exc/*reader-states* (volatile! nil))]
    (let [held (hold-belief! kb)]
      ;; the removals a settle makes, whose defeats moved their targets' belief with no
      ;; label to read it off (`defeat-moves`), and the write record a report reads
      (binding [integrate/*removed-sink* (or integrate/*removed-sink*
                                             (integrate/removal-sink
                                              (exc/placed-reads? kb)))
                observe/*write-record*   (write-record kb)
                observe/*route-gain-sink* (special/route-gain-sink kb)]
        (try
          (loop [round 1, dropped? false]
            (let [seeds   (volatile! #{})
                  ;; a dropped firing relabelled its region outside a settle, so the next
                  ;; settle reconciles the caches with it before discovery reads them
                  ;; a later round's region is what the drop moved, not the whole store
                  retired (binding [*unmerged-sink*       seeds
                                    *relabelled-before?* (or *relabelled-before?* dropped?)
                                    discovery/*whole-store-region?* (and discovery/*whole-store-region?*
                                                                         (= 1 round))]
                            (settle* kb))
                  [respelled valued] (respelled-seeds kb)
                  back    (into (vec @seeds) respelled)
                  dropped (withdraw-retired-firings! kb retired)]
              (cond
                (and (empty? back) (empty? valued) (not dropped)) nil
                (>= round max-unmerge-rounds)
                (trove/log! {:level :warn :id ::unmerge-fixpoint
                             :msg  (str "un-merge re-seeding did not converge in "
                                        max-unmerge-rounds " rounds; giving up")
                             :data {:rounds round :seeds (count back)}})
                ;; a given-back spelling is also a fact a descended equality is drawn
                ;; from, and the merge it rests on may have lost its route while the
                ;; spelling was superseded (`lost-derivation-seeds`)
                ;; a `{:chain? false}` write places the value derivations and chains
                ;; nothing from them, as it chains nothing from its own sentence
                :else (let [back (into back (when special/*seed-moves?* valued))]
                        (when (seq back)
                          (rechain-seeds
                           kb (into back (lost-derivation-seeds
                                          kb (special/lost-descended-derivations kb back false)))))
                        (recur (inc round) dropped)))))
          (finally
            (publish-belief! held))))
      (feed/deliver! kb)
      nil)))

(defn settle-write
  "Settle after a write, seeding chaining from the `genlCx` moves it settles when `seed?`
  (`special/*seed-moves?*`).  Under `wiring/*defer-settle?*` it settles nothing and
  records `seed?` for the batch in force (`*batch-seeds-moves*`)."
  [kb seed?]
  (if wiring/*defer-settle?*
    (when (and seed? *batch-seeds-moves*) (vreset! *batch-seeds-moves* true))
    (binding [special/*seed-moves?* seed?] (settle kb))))

