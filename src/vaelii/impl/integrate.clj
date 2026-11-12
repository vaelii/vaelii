;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrate
  "Store mutation is the boundary: the choke points everything that stores or removes a
  sentex passes through, so exceptWhen's re-check queue is never skipped. The table of what
  each special predicate means is in `vaelii.impl.special`.

    sentex-added     integrate through the table and queue the re-check: the assert
                     path's reflection of a sentex that just landed
    sentex-removed!  disintegrate, unindex, delete the record and queue the re-check: the
                     one teardown, shared by `retract!` and the excepted-conclusion sweep
    symmetrize-      re-spell the rows stored before a late `(symmetric P)` mark, folding
      existing       a mirrored pair into one; moves a record without moving a handle

  `special/derived-sentex-added` is the derivation path's twin. Triggers that are not store
  mutations (a taxonomy edge change, rule indexing, `recover`) post their re-checks at their
  own sites. See docs/exceptions.md and docs/canonicalization.md."
  (:require [vaelii.impl.decide :as decide]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:dynamic *removed-sink*
  "A volatile holding a vector of the sentexes that have left the store, or nil (the default:
  the removal choke point records nothing). Callers that act on the region a teardown
  touched read it, such as `core`'s reified-NAT orphan sweep. Every removal passes the
  choke point, so the narrowed question equals the whole-KB one (docs/nat.md). A volatile
  because the engine is single-writer."
  nil)

(defn removal-sink
  "The sink to record a teardown's removals into: the bound one when there is one, a fresh
  volatile otherwise, so a nested teardown appends to the record its caller is reading.
  `want?` false answers nil, which records nothing. The record retains every removed sentex
  for the teardown's length, so the caller passes the presence check its readers consult
  (`nat/any-reified-constants?`, a stored `defeat`)."
  ([] (removal-sink true))
  ([want?] (when want? (or *removed-sink* (volatile! [])))))

(defn sentex-added
  "Reflect a sentex that just landed as a premise into the caches through the
  special-predicate table, and queue the exception re-check its arrival may flip. Returns
  the table walk's result: the `{:new :superseded :violations}` migration map for an
  equality sentex, nil otherwise. Runs whether or not the sentex is new, since
  re-asserting adds premise support."
  [kb sentex handle]
  (let [result (special/integrate-sentex kb sentex handle)]
    (special/recheck-on-sentence kb (sx/sentence-of sentex))
    result))

(defn sentex-removed!
  "Everything that must happen because a sentex is leaving the store: reverse its
  cache effects through the table, drop it from every index, delete the record, and
  queue the exception re-check — a fact *leaving* is as much a re-check trigger as
  one arriving, since its departure may be exactly what releases some rule's
  exception.

  Records the sentex into `*removed-sink*` when one is bound, which is how a caller
  learns the region a teardown removed without every removal path having to report it."
  [kb sentex]
  ;; Capture the except target *before* any mutation — the sentex record is about to be
  ;; deleted, so extracting it afterward would depend on the local binding outliving
  ;; storage.  Binding here makes the before/after contract structural.
  (let [except-target (kb/except-target (sx/sentence-of sentex))]
    ;; the removal record, for a caller scoping its own follow-up work to what left
    (when-let [sink *removed-sink*] (vswap! sink conj sentex))
    ;; the sentence the inherited-clash discovery reads for a handle with no record
    (discovery/note-removed! kb sentex)
    (special/disintegrate-sentex! kb sentex)
    (p/unindex-sentex! (:index kb) sentex (:id sentex))
    (p/delete-sentex! (:records kb) (:id sentex))
    ;; the remove-side boundary for an incremental matcher's alpha memories, mirroring the
    ;; add in `kb/create-sentex` — a no-op unless one is engaged
    (observe/notify-remove kb sentex)
    ;; and the change clock, mirroring the same line there
    (observe/note-change)
    (exc/note-stored! kb sentex false)
    ;; the handle cache holds "this sentence is stored at this handle", and this is the
    ;; one event that falsifies it — so the invalidation belongs beside the removal
    ;; itself, not in the caller that happens to have a cache bound
    (observe/forget-handle! (sx/sentence-of sentex) (:context sentex))
    ;; a defeat leaving moves its target's belief, which its watchers re-check
    (special/recheck-defeat-target kb sentex)
    ;; ...and the candidates of the nogood families the settle places
    (decide/note-candidate! kb sentex false)
    (kb/note-mint-rule-moved! kb sentex)
    (kb/note-lazy-rule-moved! kb sentex)
    ;; ...and the mint family, the remove half of `special/entail-arg-type`'s add, and
    ;; the departure the settle re-derives withheld mints from
    (special/retire-mint! kb sentex)
    (special/note-departure! kb sentex)
    ;; ...and the supersessions the departure moves: a superseded spelling leaving, or an
    ;; equality, a rewrite rule or a `genlCx` edge whose leaving gives spellings back.
    ;; After the record is deleted, which is what drops a departing spelling's entry
    (special/reconcile-removed-supersession! kb sentex)
    ;; An except's departure changes the effective belief of the declaration it hid.
    ;; Run after the except leaves the index so the common reconcile reads the new
    ;; visibility state.
    (when except-target
      (special/reconcile-belief-change kb #{except-target}))
    (special/recheck-on-sentence kb (sx/sentence-of sentex))))

;; ## The spellings a permuting mark folded
;;
;; A permuting mark sorts a literal's arguments on the way in, so the row a fact is stored
;; at need not be spelled as written. The row records the written spellings in the
;; provenance entry `spellings-key`, `{:premise {written strength} :derived {jid written}}`,
;; which `chain/reconcile-spellings!` reads when the mark leaves. Only a piece spelled
;; otherwise than its row is recorded, except that an existing premise map lists every
;; premise assertion. A `:derived` entry naming a gone justification is ignored; a
;; `:premise` map on a row that is no longer a premise is replaced by the next assertion.
;; `core/provenance` leaves the entry out.

(def spellings-key
  "The provenance key a row's written spellings are recorded under."
  :vaelii/spellings)

(defn spellings
  "Row `h`'s written-spelling record — `{:premise {written strength} :derived {jid
  written}}` — or nil when every piece of it is spelled as the row is."
  [kb h]
  (get (p/get-provenance (:records kb) h) spellings-key))

(defn put-spellings!
  "Record `rec` as row `h`'s written spellings, dropping empty parts; an empty record
  removes the entry (and the provenance map with it, when nothing else is in it)."
  [kb h rec]
  (let [recs (:records kb)
        prov (p/get-provenance recs h)
        rec  (not-empty (into {} (remove (comp empty? val)) rec))]
    (cond
      rec                           (when-not (= rec (get prov spellings-key))
                                      (p/put-provenance recs h (assoc prov spellings-key rec)))
      (contains? prov spellings-key) (let [prov' (dissoc prov spellings-key)]
                                       (if (seq prov')
                                         (p/put-provenance recs h prov')
                                         (p/delete-provenance! recs h))))))

(defn permuting?
  "Does a stored mark permute `pred`'s arguments — `symmetric`, or a commuting group — or
  reshape its applications below the literal — `associative`, `idempotent`, a
  `meetFunctionOf` order, or a `distinctInArgAndRest` position?

  Read unscoped: the fold decides the stored key, which every reader shares."
  [kb pred]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (and pred (or (tax/has-prop? tax :symmetric pred)
                           (seq (tax/commuting-groups tax pred))
                           (tax/has-prop? tax :associative pred)
                           (tax/has-prop? tax :idempotent pred)
                           (seq (tax/meet-orders tax pred))
                           (seq (tax/distinct-positions tax pred)))))))

(defn permuting-sentence?
  "Does a stored mark permute the arguments of `sentence`'s literal, or of a compound
  below it (`sx/compound-functors`)?  Read unscoped, as `permuting?` is."
  [kb sentence]
  (let [s (if (and (seq? sentence) (= 'not (first sentence))) (second sentence) sentence)]
    (boolean (some #(permuting? kb %)
                   (sx/compound-functors s (res/opaque-fn (reasoning/taxonomy kb)))))))

(defn premise-spellings
  "`{written strength}` for row `h`'s premise assertions: the record's, or `stored` at
  `h`'s premise class when the record lists none, or `{}` when `h` is no premise."
  [kb h stored]
  (let [tms (reasoning/tms kb)]
    (if (jtms/premise? tms h)
      (or (not-empty (:premise (spellings kb h))) {stored (jtms/premise-strength tms h)})
      {})))

(defn- queue-respelling!
  "Queue row `h` on `:respell` when a reader of `written`, stored as `stored`, may read
  another spelling (`res/split-functors`: some reader does not believe a mark of its
  predicate or of a functor below it): the settle that drains the queue puts the row's
  pieces at the spellings their readers read (`chain/reconcile-spellings!`)."
  [kb h stored written]
  (when (and (not= written stored) (seq (res/split-functors kb written)))
    (swap! (reasoning/respell kb) conj [:row h])))

(defn note-premise-spelling!
  "Record that `written` was asserted at `strength` onto row `h`, stored as `stored`.
  `prior` is `h`'s premise class before this assertion, nil when it was none — the
  record's premise map is then stale and starts again.  Writes nothing while every
  premise assertion is spelled as the row is."
  [kb h stored written strength prior]
  (queue-respelling! kb h stored written)
  (let [rec  (spellings kb h)
        live (when prior (not-empty (:premise rec)))]
    (cond
      (or live (not= written stored))
      (let [pm (or live (if prior {stored prior} {}))]
        (put-spellings! kb h (assoc rec :premise (update pm written #(strength/max % strength)))))
      (and (nil? prior) (seq (:premise rec)))
      (put-spellings! kb h (dissoc rec :premise)))))

(defn note-derived-spelling!
  "Record that justification `jid`, a rule firing, concluded `written` onto row `h`."
  [kb h jid written]
  (queue-respelling! kb h (:sentence (p/get-sentex (:records kb) h)) written)
  (put-spellings! kb h (assoc-in (spellings kb h) [:derived jid] written)))

(defn normalized-spellings
  "`rec` for a row stored as `stored`, without what the row's own spelling already says:
  a premise map whose one assertion is `stored`, and every firing written as `stored`."
  [stored {:keys [premise derived]}]
  {:premise (when-not (every? #(= stored %) (keys premise)) premise)
   :derived (into {} (remove (comp #{stored} val)) derived)})

(defn witness-among
  "The believed handle among `supporters` chosen by content — the handle a fold carries a
  folded row's metas on when no declaration arrived to be it.  Nil when none is believed."
  [kb supporters]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> supporters
         (filter #(jtms/in? tms %))
         (keep #(when-let [sx (p/get-sentex recs %)] [(nm/print-key [(:sentence sx) (:context sx)]) %]))
         sort
         first
         second)))

(defn mark-witness
  "A believed statement of a permuting mark on `pred` (`witness-among`), for
  `commute-predicate`.

  The marks are read unscoped, a superset that `witness-among` narrows to a believed
  statement."
  [kb pred]
  (let [tax (reasoning/taxonomy kb)]
    (witness-among kb (concat (tax/prop-supporters tax :symmetric pred)
                              (mapcat #(tax/commuting-supporters tax pred %)
                                      (tax/commuting-groups tax pred))
                              (tax/prop-supporters tax :associative pred)
                              (tax/prop-supporters tax :idempotent pred)
                              (mapcat #(tax/meet-supporters tax pred %)
                                      (tax/meet-orders tax pred))
                              (mapcat #(tax/distinct-supporters tax pred %)
                                      (tax/distinct-positions tax pred))))))

(defn- rule-justification?
  "Is `jid` a rule firing — a justification whose informant is a rule handle other than
  an argument-type mint's inert rule (`special/firing-informant?`)?  Only a firing's
  written spelling is recorded; every other justification restates a row it rests on,
  and follows that row wherever its spelling puts it."
  [kb jid]
  (special/firing-informant? kb (:informant (jtms/justification (reasoning/tms kb) jid))))

(defn- written-out
  "Row `h`'s record with every piece that is spelled `stored` only implicitly written
  out — its premise assertions and its rule firings — for a caller about to move the
  row off that spelling."
  [kb h stored]
  (let [tms (reasoning/tms kb)
        rec (spellings kb h)]
    (assoc rec
           :premise (premise-spellings kb h stored)
           :derived (reduce (fn [m jid]
                              (if (or (contains? m jid) (not (rule-justification? kb jid)))
                                m
                                (assoc m jid stored)))
                            (:derived rec {})
                            (jtms/supports tms h)))))

;; ## A `symmetric` mark arriving after the facts
;;
;; The third store mutation, and the only one that moves a record without moving a handle.
;; The retroactive half of `(symmetric P)` is a storage migration: the rows stored before
;; the mark end up spelled as the rows stored after it are (docs/canonicalization.md). It
;; lives here because it removes and re-stores records. `assert-entry/assert-one` and
;; `chain/place-fact-conclusion` call it, as they call `special/equate-existing`.

(defn- rewritten
  "Written-spelling record `rec` for a row about to be spelled `stored`, each written
  spelling put through `rewrite` and the pieces `stored` already says dropped — or `rec`
  unchanged when `rewrite` is nil.  A permuting mark keeps the spellings as written; a
  reifiable mark moving re-spells them as it re-spells the row, but for the applications
  whose constants their expressions sorted name (`chain/reconcile-row-spelling!`)."
  [rewrite stored {:keys [premise derived] :as rec}]
  (if-not rewrite
    rec
    (normalized-spellings
     stored
     {:premise (reduce-kv (fn [m w st] (update m (rewrite w) #(strength/max % st))) {} premise)
      :derived (update-vals derived rewrite)})))

(defn- respell!
  "Bring one stored sentex into `sentence`, its cache effects walked off the old spelling
  and back on under the new one.  The handle, the TMS node, the premise mark and every
  justification naming it are untouched: for a re-canonicalization, nothing that rests on
  the row is about its spelling except the argument-type mints it triggers, which
  `move-row!` draws again.  `rewrite` is `move-row!`'s."
  [kb sx sentence rewrite]
  ;; the pieces spelled as the row was stop being spelled as the row is
  (put-spellings! kb (:id sx) (rewritten rewrite sentence (written-out kb (:id sx) (sx/sentence-of sx))))
  (special/disintegrate-sentex! kb sx)
  (let [sx' (kb/respell-sentex! kb sx sentence)]
    (special/refile-mint! kb sx (:id sx'))
    (special/integrate-sentex kb sx' (:id sx'))
    (special/recheck-on-sentence kb sentence)
    sx'))

(defn- fold-premise!
  "Give `survivor` the premise mark `doomed` carries, at the **stronger** of the two
  classes — `assert-entry/mark-premise`'s rule, and for its reason: the pair is one proposition
  asserted twice, and which of the two assertions the KB keeps must not decide how
  strongly it holds it.  A `doomed` that is not a premise leaves the survivor alone."
  [kb doomed survivor]
  (let [tms (reasoning/tms kb)]
    (when (jtms/premise? tms doomed)
      (let [s (strength/max (jtms/premise-strength tms survivor)
                            (jtms/premise-strength tms doomed))]
        (jtms/add-premise tms survivor s)
        (p/mark-premise (:records kb) survivor s)))))

(defn- fold-dependents!
  "Re-hang every justification that uses `doomed` as an antecedent on `survivor`: same
  informant, bindings and strength, only the antecedent moves. A justification whose
  consequence is already `survivor` is skipped, since rewritten it would name `survivor`
  among its own antecedents and a datum that grounds itself stays believed after its real
  support goes. Idempotent through `has-justification?`.
  Copied from the record, not the network, because the network drops a firing's `:bindings`,
  which an `exceptWhen` query and a NAF antecedent re-evaluate."
  [kb doomed survivor]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (doseq [jid  (vec (jtms/dependents tms doomed))
            :let [j     (or (p/get-justification recs jid) (jtms/justification tms jid))
                  antes (mapv #(if (= % doomed) survivor %) (:antecedents j))]
            :when (and j (not= (:consequence j) survivor)
                       (not (jtms/has-justification?
                             tms (:informant j) antes (:consequence j)
                             (jtms/justification-key (:informant j) antes (:subsumptions j)))))]
      (let [nid  (p/next-id recs)
            just (jtms/->just nid (:informant j) antes (:consequence j)
                              (:bindings j) (:strength j) (:subsumptions j))]
        (p/put-justification recs just)
        (jtms/add-justification tms just)
        ;; the copy concludes what the original did, spelled as the original was
        (when-let [w (get-in (spellings kb (:consequence j)) [:derived jid])]
          (note-derived-spelling! kb (:consequence j) nid w))))))

(defn- fold-supports!
  "Re-hang every justification that concludes `doomed` on `survivor`: same informant,
  antecedents, bindings and strength, only the consequence moves. The twin of
  `fold-dependents!`, so `symmetrize-row!` can fold a pair a rule concluded. Copies; the
  originals go with `doomed` in `fold-row!`'s `take-out!`. Skips a justification naming
  `survivor` among its antecedents: retargeted, it would conclude `survivor` from itself,
  and skipping loses no belief because the row it concluded is leaving. Idempotent; read
  from the record. Returns `{jid copy}`."
  [kb doomed survivor]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (reduce (fn [copied jid]
              (let [j (or (p/get-justification recs jid) (jtms/justification tms jid))]
                (if (and j (not (some #{survivor} (:antecedents j)))
                         (not (jtms/has-justification?
                               tms (:informant j) (:antecedents j) survivor
                               (jtms/justification-key (:informant j) (:antecedents j)
                                                       (:subsumptions j)))))
                  (let [nid  (p/next-id recs)
                        just (jtms/->just nid (:informant j) (vec (:antecedents j)) survivor
                                          (:bindings j) (:strength j) (:subsumptions j))]
                    (p/put-justification recs just)
                    (jtms/add-justification tms just)
                    (assoc copied jid nid))
                  copied)))
            {}
            (vec (jtms/supports tms doomed)))))

(defn swept-records
  "The stored records of a network removal's `removed-sentexes`, in the removal's order and
  read before any is deleted, less each record carrying the `:inert` provenance mark
  `assert-inert` writes.  A derivation concluding an inert record's sentence gives the
  record a node and a justification, and the sweep that drops them leaves the record as
  `assert-inert` stored it.  `retracted`, the handle a `retract!` names, is kept in the
  result even when it carries the mark."
  ([kb removed-sentexes] (swept-records kb removed-sentexes nil))
  ([kb removed-sentexes retracted]
   (let [recs (:records kb)]
     (into [] (keep #(when (or (= % retracted) (not (true? (:inert (p/get-provenance recs %)))))
                       (p/get-sentex recs %)))
           removed-sentexes))))

(defn apply-removals!
  "Delete from the stores what a network removal `r` swept (`swept-records`), and tear
  each deleted record down through `sentex-removed!`: `r` is a `jtms/retract!`,
  `jtms/sweep!` or `jtms/drop-justification!` result."
  [kb {:keys [removed-sentexes removed-justifications] :as r}]
  (let [recs (:records kb)
        gone (swept-records kb removed-sentexes)]
    (doseq [sx gone] (sentex-removed! kb sx))
    (doseq [jid removed-justifications] (p/delete-justification! recs jid))
    (special/retire-unjustified-mints! kb r)))

(defn take-out!
  "Take stored row `h` out of the network and the store: drop its premise mark and every
  justification concluding it, retract it, remove what that swept, then the row itself when
  still stored (an inert sentex is no network datum). `core/retract!`'s storage half. The
  justifications go first, so no node or justification names a handle with no record."
  [kb h]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (p/unmark-premise! recs h)
    (doseq [jid (vec (jtms/supports tms h))]
      (let [r (jtms/drop-justification! tms jid)]
        (p/delete-justification! recs jid)
        (apply-removals! kb r)))
    (apply-removals! kb (jtms/retract! tms h))
    (when-let [sx (p/get-sentex recs h)] (sentex-removed! kb sx))))

(defn- fold-row!
  "Fold the mirrored row `doomed` into `survivor` and take it out of the store: the
  justifications concluding it, its premise mark, the conclusions drawn through it and the
  handle-naming metas. `fold-supports!` runs first, so the survivor holds a copy of each
  justification concluding the row before `take-out!` drops the originals. Swept records go
  to the removal choke point. `want` is the spelling the survivor ends at."
  [kb doomed survivor want witness rewrite]
  ;; read before anything moves: the doomed row's pieces, spelled as it wrote them, go to
  ;; the survivor with everything else it hands over
  (let [dsx     (p/get-sentex (:records kb) doomed)
        ssent   (sx/sentence-of (p/get-sentex (:records kb) survivor))
        dpieces (written-out kb doomed (sx/sentence-of dsx))
        spieces (written-out kb survivor ssent)
        copied  (fold-supports! kb doomed survivor)]
    (when (seq copied) (special/refile-mint! kb nil survivor))
    (put-spellings! kb survivor
                    (rewritten rewrite (when rewrite want)
                               (assoc spieces
                                      :premise (merge-with strength/max (:premise spieces) (:premise dpieces))
                                      :derived (into (:derived spieces)
                                                     (keep (fn [[jid w]] (when-let [n (copied jid)] [n w])))
                                                     (:derived dpieces))))))
  (fold-dependents! kb doomed survivor)
  (fold-premise! kb doomed survivor)
  ;; with no witness the carried meta rests on the original meta alone
  (special/migrate-handle-metas kb doomed survivor 'rewriteOf [(if witness [witness] [])]
                                (:context (p/get-sentex (:records kb) doomed)))
  (take-out! kb doomed))

(defn- redraw-mints!
  "Bring the argument-type mints row `h` triggers to the spelling it holds now: draw what
  that spelling entails, then drop each mint justification it does not draw
  (`special/redraw-mints`).  `{:new [handle …] :violations [v …]}`, the mints drawn."
  [kb h]
  (let [tms         (reasoning/tms kb)
        [drawn stale] (special/redraw-mints kb h)]
    (doseq [jid stale]
      (let [r (jtms/drop-justification! tms jid)]
        (p/delete-justification! (:records kb) jid)
        (apply-removals! kb r)))
    drawn))

(defn move-row!
  "Bring one stored row `sx` to the spelling `want`: `{:at handle :new [handle …]
  :violations [v …]}`, the handle the row ends up at, followed in `:new` by the mints its
  new spelling drew (`redraw-mints!`), or nil when it is spelled `want` already.
  `symmetrize-row!` below states the shape and the choice of survivor.  `witness` is the
  mark handle a folded row's metas are carried on, or nil.  `rewrite` re-spells the row's
  written spellings (`rewritten`), nil to keep them as written."
  [kb sx want witness rewrite]
  (when (not= want (sx/sentence-of sx))
    (let [tms    (reasoning/tms kb)
          ctx    (:context sx)
          self   (:id sx)
          mirror (kb/find-sentex-handle kb want ctx)
          ;; the row that can leave: the one standing on nothing but its own premise
          ;; where only one of the two does, and otherwise the later handle — which
          ;; covers a pair a rule concluded on both sides, `fold-supports!` being what
          ;; makes that one foldable
          bare?  (fn [h] (empty? (jtms/supports tms h)))
          doomed (cond (nil? mirror)                          nil
                       (and (bare? self)   (not (bare? mirror))) self
                       (and (bare? mirror) (not (bare? self)))   mirror
                       :else                                    (max self mirror))]
      (let [at (cond
                 ;; nothing to fold: the row is alone under this proposition and only
                 ;; spelled the way the entry point used to spell it
                 (nil? mirror)   (:id (respell! kb sx want rewrite))
                 ;; this row is the one that leaves; the mirror is already the wanted
                 ;; spelling
                 (= doomed self) (do (fold-row! kb self mirror want witness rewrite) mirror)
                 ;; the mirror leaves, and this row takes the spelling it vacated
                 :else           (do (fold-row! kb mirror self want witness rewrite)
                                     (:id (respell! kb (p/get-sentex (:records kb) self) want rewrite))))
            {:keys [new violations]} (redraw-mints! kb at)]
        {:at at :new (into [at] new) :violations violations}))))

(defn spelling-plan
  "`[home entries respelled]` for a piece of a fact written `w` in `ctx`, read through
  `planner` (`res/spelling-planner`): `home`, the spelling the piece is stored at, with
  `entries`, the marks that spell it (nil: the store's own marks); and `respelled`,
  `{spelling entries}` for every other spelling a reader of the fact reads, each stored
  justified `respell` by the home row (`chain/respell-rows!`).  One spelling read: the
  piece sits at it.  Several: the piece sits at `w` as written."
  [kb planner w ctx]
  (if-let [sp (planner w ctx)]
    (if (= 1 (count sp))
      (let [[sw e] (first sp)] [sw e {}])
      [w #{} (dissoc sp w)])
    [(kb/canonical-sentence kb w ctx) nil {}]))

(defn spelled
  "Call `f` with `res/*spelled-by*` naming the functors of `sentence` some reader spells
  per reader (`res/split-functors`) in `ctx` with `entries`, or plainly when `entries` is
  nil, so the store spells `sentence`'s literal in `ctx` by those marks.  `f`'s value is
  realized inside the binding."
  [kb sentence ctx entries f]
  (if (some? entries)
    (binding [res/*spelled-by* [(res/split-functors kb sentence) ctx entries]]
      (let [v (f)] (if (seq? v) (doall v) v)))
    (f)))

(defn- symmetrize-row!
  "Bring one stored row of a newly symmetric predicate into the argument order its readers
  read: `move-row!`'s result, or nil when it is spelled so already. With no mirror stored the
  row is re-spelled where it lies. With one stored, the pair folds into one row, re-spelled
  if needed. A row that is only a premise is preferred as the one to go; a row a rule
  concluded leaves through `fold-supports!`; between two rows the fold cannot separate, the
  lower handle survives. A pair both rule-concluded folds too. See docs/canonicalization.md,
  \"A mark arriving after the facts migrates them\"."
  [kb planner sx witness]
  (let [ctx          (:context sx)
        [want ents]  (spelling-plan kb planner (:sentence sx) ctx)]
    (spelled kb (:sentence sx) ctx ents #(move-row! kb sx want witness nil))))

(defn fold-row-home!
  "`symmetrize-row!` for one row a caller walks itself (`chain/respell-rows!`)."
  [kb planner sx witness]
  (symmetrize-row! kb planner sx witness))

(defn- recanonicalizing-subject
  "The predicate whose stored facts a declaration re-spells, or nil when `sentence` moves no
  spelling. Eight spellings reach one sweep: `(symmetric P)`; `(commutativeInArgAndRest P
  f)`, `(commutativeInArgs P p …)` and `(commutative P)`, which sort the arguments of the
  named component; and `(associative F)`, `(idempotent F)`, `(meetFunctionOf F R)` and
  `(distinctInArgAndRest F n)`, which reshape a ground application of `F` below the literal
  (`sx/canonical-term`). The mark must
  be installed, and is read unscoped because the fold decides the stored key every reader
  shares."
  [kb sentence]
  (when (and (sequential? sentence) (symbol? (nm/functor sentence)))
    (let [tax (reasoning/taxonomy kb)
          f   (nm/functor sentence)
          p   (first (nm/args sentence))]
      (when (and (symbol? p) (not (sx/variable? p)))
        (case f
          symmetric                (when (and (= 1 (nm/arity sentence))
                                              (tax/has-prop? tax :symmetric p))
                                     p)
          (commutativeInArgAndRest
           commutativeInArgs
           commutative)            (when (seq (tax/commuting-groups tax p)) p)
          associative              (when (tax/has-prop? tax :associative p) p)
          idempotent               (when (tax/has-prop? tax :idempotent p) p)
          meetFunctionOf           (when (seq (tax/meet-orders tax p)) p)
          distinctInArgAndRest     (when (seq (tax/distinct-positions tax p)) p)
          nil)))))

(defn rows-spelled-by
  "The stored rows whose spelling `pred`'s permuting marks decide, sorted: `pred`'s own
  rows, and the rows the term index keys by `pred`, a candidate set holding every row with
  an application of `pred` below its literal.  A candidate whose spelling the marks do not
  move is left where it lies by the caller's re-spell."
  [idx pred]
  (vec (into (sorted-set)
             (concat (when (pos? (reads/stored-count-with-functor idx pred))
                       (reads/as-stored-with-functor idx pred))
                     (reads/as-stored-with-term idx pred)))))

(defn rows-a-mention-spells
  "The stored rows a mention of `pred` arriving or leaving can respell, sorted: those the
  term index keys by `pred` and by a functor a permuting or term mark sorts, a candidate
  set holding every row with such a compound beside `pred`.  One posting intersection per
  marked functor, so a row of `pred` holding no marked functor is not read.  The marks are
  read KB-wide, as the store spells a row under a mark any context holds."
  [kb pred]
  (let [tax (reasoning/taxonomy kb)
        t   @tax
        idx (:index kb)]
    (vec (into (sorted-set)
               (mapcat #(reads/as-stored-with-terms idx [pred %]))
               (distinct (concat (tax/props tax :symmetric) (keys (:commuting t))
                                 (tax/props tax :associative) (tax/props tax :idempotent)
                                 (keys (:meet t)) (keys (:distinct t))))))))

(defn commute-predicate
  "Bring `pred`'s stored rows into the spelling its marks now give them, folding mirrored
  pairs — `commute-existing`'s walk, for a caller that knows the predicate rather than
  the declaration: a mark revived by a relabel, which no declaration arrives to announce
  (`chain/reconcile-spellings!`).  `witness` is the mark handle a folded row's metas are
  carried on.  `{:new [handles] :violations [v]}`, the moved rows and the mints their new
  spellings drew, or nil when `pred` has no stored rows."
  [kb pred witness]
  ;; snapshotted before the first write: the fold posts to the roots this walk reads,
  ;; and no index backend promises whether a posting read is a snapshot
  (when-let [hs (not-empty (rows-spelled-by (:index kb) pred))]
    (let [planner (res/spelling-planner kb)]
      (transduce (keep (fn [h]
                         (when-let [sx (p/get-sentex (:records kb) h)]
                           (when-not (:antecedent sx)
                             (symmetrize-row! kb planner sx witness)))))
                 (completing #(merge-with into %1 (select-keys %2 [:new :violations])))
                 {:new [] :violations []}
                 hs))))

(defn commute-existing
  "When a declaration that re-spells arrives (`symmetric`, or either commutativity relation),
  bring the named predicate's stored facts into the argument order it puts every later one
  in, and queue `[:reifiable P]` for a reifiable `P` (`chain/reconcile-reified!`, the mark
  read unscoped). Returns `commute-predicate`'s result (the moved rows, new content to every
  rule reading the canonical one, and the mints their spellings drew), or nil when
  `sentence` moves no spelling. The extent is `P`'s own rows and the rows applying `P` below
  the literal (`rows-spelled-by`), read from storage. Linear in the facts it reaches. See
  docs/canonicalization.md."
  [kb sentence witness]
  (when-let [p (recanonicalizing-subject kb sentence)]
    (when (and (contains? '#{symmetric commutative commutativeInArgs commutativeInArgAndRest}
                          (nm/functor sentence))
               (tax/has-prop? (reasoning/taxonomy kb) :reifiable p))
      (swap! (reasoning/respell kb) conj [:reifiable p]))
    (commute-predicate kb p witness)))
