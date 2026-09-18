;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.jtms
  "A non-monotonic truth-maintenance system.

  Each TMS *node* corresponds to a datum (a sentex handle) and records: its label
  (IN/OUT), whether it is a premise (and at what assumption *strength*), its
  derivation depth, the justifications that conclude it (:supports), and the
  justifications that use it as an antecedent or name it as their rule (:consequences).

  A node holds **no reference to the sentex it labels** — only its handle.  The record
  store is where a sentex lives, so a copy here would be a second one to keep in step;
  and because this graph is always resident, a strong reference from it would hold every
  record in RAM, which on a paging backend defeats the paging entirely (measured: the
  nodes reached 50% of the record store).  A caller that needs the sentence fetches it
  by handle.

  Belief is a least fixpoint: a node is IN when it is a premise or has a valid
  justification (all antecedents IN) — EXCEPT that a node in the *defeated* set is
  forced OUT.  Because labels are computed from the current justification set and
  the current defeated set rather than accumulated as events arrive, belief is
  order-independent: asserting a defeater later withdraws a previously-drawn
  conclusion, and removing the defeater revives it.  That is the non-monotonic
  behaviour a plain monotone JTMS lacked.

  ## Two invariants

  **Order independence.** The same knowledge, given in any order, yields the same
  beliefs.  Every operation here recomputes labels from current state, so nothing
  depends on arrival order.  (The one place this can leak is a *tie-break* between
  two equally-strong beliefs: keying it on handle id would smuggle assertion order
  back in, so the contradiction layer keys it on content — see
  `vaelii.impl.solve/content-key`.)

  **Locality.** No operation recomputes the whole graph.  A change can only affect
  nodes downstream of it, so every relabel is scoped to the *affected region* — the
  forward consequence closure of whatever changed — with the rest of the graph held
  fixed as the boundary.  Cost is proportional to the region, not to the size of the
  KB, which is what lets belief maintenance scale.

  These two pull against each other, and the reconciliation is the whole design:
  a local fixpoint over the region, with boundary labels fixed, has a *unique*
  solution, and it is the same one a global fixpoint would produce.  See
  `relabel-region*`.

    * strength — every premise carries a strength (:monotonic / :default); every
      justification carries a *strength* too (:monotonic for a bare rule, :default for
      a defeasible one), capping the class it confers.  From these, `relabel` derives
      each IN node's *defeat-class* (monotonic > default, see
      vaelii.impl.strength).  Strength **propagates**: a justification confers no more
      than the weakest of its antecedents' classes, so a conclusion is never stronger
      than what it rests on.  That makes the class equation recursive, and
      `region-classes` solves it as a least fixpoint inside the region relabel.
      The class decides who loses a soft contradiction; the caller
      (core) owns the contradiction layer and pushes the losers into the defeated set
      with `defeat`.

    * defeated — a set of datums forced OUT by contradiction resolution.  It is
      *derived* (recomputed each settle by core), so `clear-defeats!` resets it and
      revival is automatic.

    * superseded — a *map* `datum -> reason` of datums displaced by an equality
      merge: the stale spelling of a fact whose terms have been rewritten to their
      class representative (docs/equality.md).  Three things make it its own state
      rather than a reuse of `defeated` or `blocked`:

      - `blocked` names *justifications*, and a directly asserted `(bornIn Dep
        Chicago)` is a **premise with no justification at all** — `region-fixpoint`
        seeds every premise IN unconditionally, so there is nothing for a block to
        invalidate.  Superseding has to act on the datum.
      - `defeated` would be the wrong reason.  A superseded spelling lost no
        argument; it was restated, and `why-not` must be able to say so — hence the
        map carries the displacing representative rather than being a bare set.
      - It is **not** a forced OUT inside the fixpoint.  A superseded datum stays in
        `:in` for the purposes of `valid?`, because its rewritten twin is justified
        *by it*: forcing it OUT structurally would invalidate the twin's own
        justification and the merge would believe neither spelling.  What
        supersession removes is *reported* belief — `in?` and `in-datums` subtract
        it — so the stale spelling stops matching, stops answering queries and stops
        entering nogoods, while everything derived from it stands.

      Retention is the point: the spelling is the **caller's premise**, so unlike an
      excepted conclusion it is never swept, and dropping the equality gives it back.
      Like `defeated` and `blocked` the map is *derived* — core recomputes it each
      settle from the equality closure — so belief stays order independent.

    * blocked — a set of *justification* ids whose rule's exception currently holds
      (`exceptWhen`, see docs/exceptions.md).  A blocked justification is not a
      defeated conclusion: it is simply **invalid**, so it supports nothing, confers
      no defeat-class, and does not make its consequence groundable — which is what
      lets the ordinary dependency-directed sweep garbage-collect an excepted
      conclusion instead of retaining it for revival.  This module is pure and has no
      KB, so it cannot run the exception query itself: the caller evaluates the
      exception and hands the answer in with `set-blocked`, which relabels only the
      region the change reaches.  Like `defeated`, the set is *derived* — computed
      from current state each settle, never accumulated — so belief stays order
      independent.

  Retraction is dependency-directed: drop the premise, relabel, then SWEEP the
  affected closure — datums that end up OUT with no valid support and are not
  defeated are solely supported by the retraction, so they (and their non-premise
  justifications) are returned for the caller to delete from the stores.  A datum that
  is merely *defeated* keeps its support and is retained for later revival.

  This module owns the in-memory graph; the caller owns physical deletion, since
  only it holds the stores."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.jtms-protocol :refer [Tms
                                               -believed? -believed -node? -datums
                                               -any-node? -any-belief? -depth -premise?
                                               -premise-strength -defeat-class -defeated
                                               -blocked -superseded -touched -touched-in
                                               -touched-new -reset-touched -supports
                                               -dependents -justification -justifications
                                               -ensure-node -add-premise -suspend-premise
                                               -add-justification -restrength-informant
                                               -relabel -defeat -clear-defeats -set-blocked
                                               -update-blocked -supersede -retract -sweep
                                               -snapshot]]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.types.tms :as tms-types]))

(defn- without-informant
  "`antecedents` as a vector, with a rule-handle `informant` taken out of it.  A firing
  hands over its handle list with the rule in it (`chain/derive-conclusion`), and so does
  a seven-field frame on disk (`codec/decode-justification`); both store the rule once."
  [informant antecedents]
  (if (integer? informant)
    (into [] (remove #(= informant %)) antecedents)
    (vec antecedents)))

(defn rests-on
  "Every handle justification `j` needs believed to be valid: its antecedents, plus its
  informant when that is a rule handle.  The sweep preview, `why-not`'s missing list, the
  visibility check and recovery's storedness check read this."
  [j]
  (let [inf (:informant j)]
    (cond-> (vec (:antecedents j)) (integer? inf) (conj inf))))

(defn- reduce-rests-on
  "`(reduce f init (rests-on j))` without the vector: the adjacency writes run once per
  justification added or swept, and the add is the hottest write path there is."
  [f init j]
  (let [acc (reduce f init (:antecedents j))
        inf (:informant j)]
    (if (integer? inf) (f acc inf) acc)))

(defn ->just
  "Construct a Justification, defaulting `strength` to :monotonic — a bare monotone
  justification adds no defeasibility of its own, so `conferred-class` caps it at its
  weakest antecedent.  A rule-handle informant is taken out of `antecedents`
  (`without-informant`)."
  ([id informant antecedents consequence bindings]
   (->just id informant antecedents consequence bindings :monotonic))
  ([id informant antecedents consequence bindings strength]
   (tms-types/->Justification id informant (without-informant informant antecedents) consequence
                              bindings (or strength :monotonic))))

(defn graph-just
  "The part of a justification the **network** is made of — everything except the
  firing's `:bindings`.

  Belief never reads the bindings: `valid?` needs the antecedents, `conferred-class`
  the strength and the informant, and the region walks the consequence.  The bindings
  are the variable map of the firing that produced it, and only two readers want them
  — re-evaluating an `exceptWhen` query and a NAF antecedent per firing — both of
  which hold the KB and take the **record** from the store, where it is durable.  So
  the network keeps the graph and the store keeps the record, and the JTMS stops
  holding a second copy of every justification.  Measured (`lein bench-jtms`, a
  rules-heavy corpus at 3.6 justifications per node): 80 of 277 B each.

  It also **normalizes** — antecedents to a vector without the informant, strength
  defaulted — so that however a caller spells a justification, the two
  representations store a value equal to each other's.  `:bindings` is nil rather
  than dropped, keeping the record shape fixed for every reader."
  [j]
  (tms-types/->Justification (:id j) (:informant j) (without-informant (:informant j) (:antecedents j))
                             (:consequence j) nil (or (:strength j) :monotonic)))

;; ---- labelling ----------------------------------------------------------

(defn- ensure* [state datum depth]
  (if-let [n (get-in state [:nodes datum])]
    (assoc-in state [:nodes datum] (update n :depth min depth))
    ;; A node the window **created** is noted as it is created, and that is the only
    ;; place the distinction exists: by the time the relabel that follows reads the
    ;; graph, a brand-new node and a stored one that has been OUT for a hundred settles
    ;; look identical — neither is believed, and both are about to be.  `touched-new` is
    ;; what separates them (see `revived`).
    (-> state
        (assoc-in [:nodes datum] {:datum datum :premise? false
                                  :depth depth :supports #{} :consequences #{}})
        (update :touched-new (fnil conj #{}) datum))))

(defn- valid?
  "Is justification `j` currently satisfied under the IN set `in` and the blocked set
  `blocked`?

  Three independent conditions: every antecedent believed, the rule believed when the
  informant is a rule handle, and the justification not blocked by its rule's exception."
  [j in blocked]
  (let [inf (:informant j)]
    (and (every? #(contains? in %) (:antecedents j))
         (or (not (integer? inf)) (contains? in inf))
         (not (contains? blocked (:id j))))))

(defn- conferred-class
  "The defeat-class a valid justification confers on its consequence: its own
  strength, capped by the *weakest* of its antecedents' classes.

  A conclusion can be no stronger than the weakest thing it rests on — a bare rule
  over a merely-default premise concludes a default, and the same rule over
  known-true facts concludes a monotonic, which is correct: it *is* monotonically
  entailed.

  The **informant is not in the cap**.  A rule-handle informant is a condition of
  `valid?`, which is what makes retracting or defeating the rule withdraw everything it
  licensed — a *validity* role, not a ground, and `antecedents` never lists it.
  Capping on it as well would fold the rule's assumption strength into every
  conclusion — and a rule takes `:default` unless its own assertion says otherwise,
  exactly as a fact does, so that alone would put every datum an ordinary rule
  licensed at `:default`.  The strength a rule contributes
  is already carried by `:strength` on the justification (`:monotonic` for a bare
  rule, `:default` for a `set/defaultRule`)."
  [j classes]
  (reduce (fn [c a] (strength/min c (get classes a :default)))
          (or (:strength j) :monotonic)
          (:antecedents j)))

(defn- node-class
  "The defeat-class of an IN datum: the strongest support it has — its premise
  strength, and the class each currently-valid justification *confers* on it.

  A blocked justification is not valid, so it confers nothing: its strength is never
  read, exactly as if it were missing an antecedent."
  [state d in classes]
  (let [n       (get-in state [:nodes d])
        blocked (:blocked state #{})
        prem  (when (and (:premise? n) (not (contains? (:defeated state) d)))
                (:premise-strength n :default))
        strs  (for [jid (:supports n)
                    :let [j (get-in state [:justs jid])]
                    :when (and j (valid? j in blocked))]
                (conferred-class j classes))]
    (reduce strength/max :default (remove nil? (cons prem strs)))))

;; ---- region-local relabelling -------------------------------------------

(defn- affected-region
  "Every node whose label could change when `seeds` change: the forward closure over
  consequence justifications, seeds included.

  This is the claim locality rests on — a node's label is a function of its
  justifications' antecedents, so a node whose label can move is, by construction,
  reachable from whatever moved.  Everything outside the region is boundary: fixed,
  and never even looked at."
  [state seeds]
  (loop [seen #{}, stack (vec seeds)]
    (if (empty? stack)
      seen
      (let [d (peek stack), stack (pop stack)]
        (if (seen d)
          (recur seen stack)
          (recur (conj seen d)
                 (into stack (->> (get-in state [:nodes d :consequences])
                                  (map #(get-in state [:justs % :consequence]))
                                  (remove nil?)))))))))

(defn- region-fixpoint
  "Least fixpoint of IN over `region`, with `base` — the boundary's believed nodes —
  held fixed.  `forced-out?` forces a node OUT whatever its support (the defeated set
  when labelling; nothing when computing groundability).

  Blocking is *not* a forced-OUT: it invalidates a justification rather than a datum,
  so it is read through `valid?` and therefore applies to the groundability pass as
  well.  That is deliberate — an excepted conclusion has lost a derivation, not merely
  a belief, so the retraction sweep should collect it (docs/exceptions.md, \"Garbage
  collection, not defeat\").

  Starting from *nothing believed inside the region* and only ever adding is what
  keeps support well-founded: a cycle within the region that has no ground outside
  it never enters, exactly as in a global least fixpoint.  And a least fixpoint is
  unique, so the result cannot depend on the order nodes are visited — which is why
  going local costs no order independence."
  [state region cands base forced-out?]
  (let [blocked (:blocked state #{})
        justs   (:justs state)
        nodes   (:nodes state)
        seeded  (into base
                      (filter #(and (get-in state [:nodes % :premise?]) (not (forced-out? %))))
                      region)]
    ;; Semi-naive worklist.  `valid?` is monotone in `in` (blocked is fixed and the
    ;; reserved `:out` slot is empty), so a justification only needs re-testing when one
    ;; of its antecedents newly enters `in` — reached through `:consequences`, the stored
    ;; inverse of the antecedent edge.  Each justification is retried once per antecedent
    ;; that fires, not once per round: O(region edges), not O(region depth × cands).  The
    ;; result is the same unique least fixpoint, so locality and order independence hold.
    (loop [in    seeded
           stack (vec cands)]
      (if (empty? stack)
        in
        (let [j (peek stack), stack (pop stack), c (:consequence j)]
          (if (and (contains? region c)
                   (not (contains? in c))
                   (not (forced-out? c))
                   (valid? j in blocked))
            (recur (conj in c)
                   (into stack (keep justs) (get-in nodes [c :consequences])))
            (recur in stack)))))))

(defn- region-classes
  "Defeat-classes for `region` under the IN set `in`, as a **least fixpoint**.

  The class equation is recursive: a justification confers no more than the weakest
  of its antecedents' classes, so a node's class depends on its antecedents'.  A
  single pass over the region would therefore be wrong, and wrong in a way that looks
  fine — visited in one order it reads a not-yet-computed antecedent as bottom and
  under-rates the conclusion; visited in another it reads a stale, too-high value and
  over-rates it.  Either way the answer would depend on the traversal order, which is
  exactly what order independence forbids.

  So: every in-region IN node starts at `:default`, the bottom of the lattice, and
  the equation is iterated to stability.  The operator is monotone in the class
  lattice (`strength/max` and `strength/min` both are, and raising an antecedent's
  class can only raise what a justification confers), and the iteration starts at
  bottom, so it converges to the *least* fixpoint.  A least fixpoint is unique —
  hence independent of visit order, and of the order the knowledge arrived in.

  Nodes outside the region are boundary: their stored class is read and held fixed,
  just as their labels are.  A boundary node whose class could move would have an
  antecedent in the region and would therefore be in the region itself, so holding
  them fixed loses nothing."
  [state region in]
  (let [nodes   (:nodes state)
        justs   (:justs state)
        base    (reduce (fn [m d] (if (contains? in d) m (dissoc m d)))
                        (:classes state {}) region)
        members (filterv #(contains? in %) region)
        init    (reduce (fn [m d] (assoc m d :default)) base members)]
    ;; Worklist over the same monotone operator.  A node's class rises only when an
    ;; antecedent's rises, so a member is recomputed only when a node it derives from
    ;; moves — reached through `:consequences`.  Starting every member at :default
    ;; (bottom), this converges to the same unique least fixpoint a round-robin sweep
    ;; would, in O(region edges) rather than O(region depth × members); the class lattice
    ;; has height one, so each member's class changes at most once.  Uniqueness of the
    ;; least fixpoint is what keeps the answer independent of the order nodes are visited.
    (loop [classes init
           stack   (vec members)]
      (if (empty? stack)
        ;; drop the :default entries **of this region**.  Every read of this map already
        ;; defaults an absent datum to :default (it is the lattice's bottom), so storing
        ;; them says nothing — and on a KB whose content is mostly :default, which a
        ;; common-sense KB's is, they are nearly the whole map.  `defeat-class` is the one
        ;; reader that did not default, and it decides OUT-vs-absent from `:in` instead,
        ;; which is what it was really using the entry's presence to mean.
        ;;
        ;; Only the members are filtered, because only they were seeded at :default here:
        ;; every entry outside the region came from an earlier relabel that applied this
        ;; same filter, so the map already holds no :default anywhere else.  Rebuilding
        ;; the whole map instead would make a region relabel O(classes) — proportional to
        ;; the KB rather than to the region, which is the one thing locality forbids, and
        ;; it is invisible until a KB carries enough non-:default content for the map to
        ;; be large (an import of Cyc's monotonic assertions is exactly that).
        (reduce (fn [m d] (if (= :default (get m d)) (dissoc m d) m)) classes members)
        (let [d   (peek stack)
              stk (pop stack)
              cls (node-class state d in classes)]
          (if (= cls (get classes d))
            (recur classes stk)
            (recur (assoc classes d cls)
                   (into stk (comp (keep justs)
                                   (map :consequence)
                                   (filter #(contains? in %)))
                         (get-in nodes [d :consequences])))))))))

(defn- relabel-region*
  "Recompute `:in`, `:groundable` and the defeat-classes for `region`, holding every
  node outside it fixed.  Equivalent to a global relabel whenever the region is the
  affected closure of what changed, and proportional to the region rather than to
  the graph.

  Boundary classes need no recomputation either: a node's class depends on which of
  its justifications are valid and on those justifications' antecedents' classes, so
  a boundary node whose class could move would have an antecedent in the region — and
  would therefore be in the region itself."
  [state region]
  (let [defeated (:defeated state #{})
        old-in   (:in state #{})
        ;; the region members this window has not relabelled yet — their label right now
        ;; is their label before anything in the window moved, and that is the reading
        ;; `touched-in` wants.  A member relabelled earlier already contributed its own,
        ;; and the earlier one is the one that predates the window.
        fresh    (into #{} (remove (:touched state #{})) region)
        ;; only the justifications that can conclude something in the region matter
        cands    (into [] (comp (mapcat #(get-in state [:nodes % :supports] #{}))
                                (distinct)
                                (keep #(get-in state [:justs %])))
                       region)
        in       (region-fixpoint state region cands
                                  (set/difference old-in region)
                                  defeated)
        ground   (region-fixpoint state region cands
                                  (set/difference (:groundable state #{}) region)
                                  (constantly false))
        state    (assoc state :in in :groundable ground)]
    ;; Record the region as *touched*: a supporter's belief can flip only inside a
    ;; relabelled region, so the accumulated touched set is a superset of every handle
    ;; whose belief moved this settle — what `tax/refresh-beliefs` uses to skip a cache
    ;; no moved supporter touches.  Alongside
    ;; it, `touched-in` records which of them were **believed before** — so the two
    ;; together say which way each one moved, which the superset alone cannot.
    (-> state
        (assoc :classes (region-classes state region in))
        (update :touched (fnil into #{}) region)
        (update :touched-in (fnil into #{}) (filter old-in fresh)))))

(defn- resettle
  "Relabel the region affected by `seeds`."
  [state seeds]
  (relabel-region* state (affected-region state seeds)))

(defn- relabel-all*
  "Relabel every node.  No engine path calls it — the assert / retract / settle path
  relabels regions and a rebuild composes the region relabels its own adds run
  (`recovery/rebuild-tms`) — so this is the differential oracle's whole-graph operation, which
  is why both representations carry it (`relabel`).

  The blocked set is **reset to empty first**, and the supersession map with it.  Neither
  is stored — blocking is derived from the exception queries and supersession from the
  equality closure — so a whole-graph relabel can read neither back, and one that merged
  into whatever was there could only ever *add*: a block standing for a justification
  whose exception no longer holds, or a spelling held OUT for an equality nothing
  asserts.  That is the bug docs/taxonomy.md records for the transitive closures.  So
  this lands unblocked and unsuperseded, and a caller that wants either states the whole
  answer again (`set-blocked` and `supersede` both replace)."
  [state]
  (let [state (assoc state :blocked #{} :superseded {})]
    (relabel-region* state (set (keys (:nodes state))))))

(defn- premise* [state datum strength-kw]
  (-> (ensure* state datum 0)
      (assoc-in [:nodes datum :premise?] true)
      (assoc-in [:nodes datum :premise-strength] (or strength-kw :default))
      (resettle [datum])))

(defn- add-just* [state j]
  (let [{:keys [id consequence] :as just} (graph-just j)
        state (-> state
                  (assoc-in [:justs id] just)
                  (update-in [:nodes consequence :supports] conj id)
                  (as-> s (reduce-rests-on (fn [st a] (update-in st [:nodes a :consequences] conj id))
                                           s just)))
        in    (:in state #{})]
    ;; Fast path — a *redundant* justification changes nothing, so skip the region relabel.
    ;; If `consequence` is already believed and this justification confers no stronger a
    ;; defeat-class than it already holds (or is not even valid), then belief, groundability
    ;; and every downstream class are unmoved: an already-IN node feeds its consequences
    ;; identically whether it rests on one witness or two.  This is what collapses a
    ;; recursive/cyclic forward load from O(derived²) to O(derived).  The `affected-region`
    ;; walk that dominated it happened *per re-derivation* — every alternate path to an
    ;; existing fact relabelled the fact's whole growing forward closure.  Now the closure is
    ;; walked once, when the fact is *first* derived (a brand-new node has no consequences
    ;; yet, so its region is a singleton and the relabel is O(log n)); every later
    ;; re-derivation via another path is a no-op.  Any *real* change still takes the full
    ;; resettle — a newly-IN consequence, a class that actually rises, a defeated/blocked one
    ;; (all of which move belief or class and so must reconcile the region) — so belief is
    ;; identical to the per-conclusion relabel, only cheaper.
    ;;
    ;; The consequence still enters `touched`, and that is not a hedge against the fast
    ;; path being wrong about belief.  A caller reading the window asks a slightly larger
    ;; question — *is what I published about this datum still current* — and a second
    ;; witness moves the answer to that while moving no label: `settle/record-clashes!`
    ;; republishes a standing clash's supporting justifications each settle and carries
    ;; the report forward for a pair the window does not hold, so a silent arrival is a
    ;; report naming fewer reasons than the KB holds.  Noting one handle is O(1) where
    ;; polling every standing pair for its support count is O(standing) per settle — which
    ;; `lein perf`'s `negation-arbitration` is indistinguishable from a 19% worse growth ratio at 800
    ;; standing dilemmas, against no measurable change for this.  `touched-in` takes it too,
    ;; or the window would read as "newly believed" — but only when this window has not
    ;; relabelled it already, since an earlier relabel's answer is the one that predates
    ;; the window (`relabel-region*`'s `fresh`).
    (if (and (contains? in consequence)
             (or (not (valid? just in (:blocked state #{})))
                 (let [cls (get (:classes state) consequence :default)]
                   (= cls (strength/max cls (conferred-class just (:classes state)))))))
      (cond-> (update state :touched (fnil conj #{}) consequence)
        (not (contains? (:touched state #{}) consequence))
        (update :touched-in (fnil conj #{}) consequence))
      (resettle state [consequence]))))

(defn- restrength-informant* [state informant strength]
  ;; The adjacency lists every justification a rule informs under the rule's node
  ;; (`reduce-rests-on` in `add-just*` — the link that makes retracting the rule withdraw
  ;; its conclusions), so the node's `:consequences` is the candidate set and nothing
  ;; scans the whole `:justs` map.  The informant filter keeps out a justification that
  ;; merely *uses* the rule's handle as an ordinary antecedent.
  (let [jids  (into []
                    (filter #(= informant (get-in state [:justs % :informant])))
                    (get-in state [:nodes informant :consequences] #{}))
        stale (into [] (remove #(= strength (get-in state [:justs % :strength]))) jids)]
    (if (empty? stale)
      state
      (-> (reduce (fn [s jid] (assoc-in s [:justs jid :strength] strength)) state stale)
          (resettle (mapv #(get-in state [:justs % :consequence]) stale))))))

;; ---- retraction ---------------------------------------------------------

(defn dissoc-all
  "`(apply dissoc m ks)` in one transient pass.  `apply dissoc` walks the map once per
  key with a full HAMT path copy each time, and `ks` here is the whole swept region of
  a retraction — which is a routine path rather than a rare one, since an `exceptWhen`
  block runs the sweep on ordinary fact arrival.

  Public because the dense network sweeps the same region out of the same shape: its
  `superseded` is the one persistent map it keeps (docs/density.md), so
  `vaelii.impl.dense-jtms` drops a swept region from it through this rather than
  through a second copy of the reasoning."
  [m ks]
  (if (seq ks) (persistent! (reduce dissoc! (transient (or m {})) ks)) (or m {})))

(defn- disj-all
  "`(apply disj s ks)` in one transient pass, for the same reason as `dissoc-all`."
  [st ks]
  (if (seq ks) (persistent! (reduce disj! (transient (or st #{})) ks)) (or st #{})))

(defn- sweep*
  "SWEEP: collect the datums in `suspects` that are no longer *structurally*
  derivable (not groundable) and are not premises, delete them and every
  justification touching them, and return
  [new-state {:removed-sentexes [datum...] :removed-justifications [jid...]}].

  Groundability ignores defeats, so a defeated node with a surviving derivation is
  kept for revival, while a defeated node whose only support was just torn down is
  swept (no orphan leak).  Blocking, by contrast, *does* suppress groundability
  (see `region-fixpoint`), which is what makes this the garbage collector for an
  excepted conclusion as well as for a retracted one — docs/exceptions.md,
  \"Garbage collection, not defeat\".

  The caller must have relabelled `suspects` already: this reads `:groundable`, it
  does not compute it.

  Like every other operation here it is **region-local**: the justifications to tear
  down are read off the dead nodes' own `:supports` / `:consequences`, never found by
  scanning `:justs`.  That matters because `exceptWhen` blocks a justification on
  ordinary fact arrival, so sweeping is routine rather than a retraction-only path,
  and a sweep that scanned the whole graph would make a run of them quadratic."
  [state suspects]
  (let [groundable (:groundable state #{})
        dead     (filter (fn [d]
                           (and (not (get-in state [:nodes d :premise?]))
                                (not (contains? groundable d))))
                         suspects)
        ;; The justifications that touch a dead datum are exactly the ones its node
        ;; already names: `:supports` (it is their consequence) and `:consequences`
        ;; (it is one of their antecedents, or their rule).  Reading the two
        ;; adjacency sets keeps this proportional to the swept region — scanning
        ;; `:justs` instead would make every sweep cost the whole graph, which is the
        ;; locality invariant this module is built on (docs/nmtms.md).
        dead-jids (into #{}
                        (comp (mapcat (fn [d] (concat (get-in state [:nodes d :supports] #{})
                                                      (get-in state [:nodes d :consequences] #{}))))
                              ;; an adjacency set names a justification; only a live one
                              ;; is ours to remove or to report
                              (filter #(contains? (:justs state) %)))
                        dead)
        removed-justifications (remove #(= :premise (get-in state [:justs % :informant])) dead-jids)
        ;; the swept datums, as handles.  The caller fetches each one's record from the
        ;; store before deleting it — the store is where a sentex lives, and a copy kept
        ;; here would be a second one to keep in step (and, on a paging backend, would
        ;; hold every record resident).
        removed-sentexes   (vec dead)
        ;; 5. apply removals to the graph
        state (reduce (fn [st jid]
                        (let [{:keys [consequence] :as j} (get-in st [:justs jid])]
                          (-> st
                              (update :justs dissoc jid)
                              (update-in [:nodes consequence :supports] #(disj (or % #{}) jid))
                              (as-> s (reduce-rests-on (fn [s2 a]
                                                         (update-in s2 [:nodes a :consequences]
                                                                    #(disj (or % #{}) jid)))
                                                       s j)))))
                      state dead-jids)
        state (update state :nodes dissoc-all dead)
        state (update state :classes dissoc-all dead)
        ;; a block names a justification, so a swept justification must lose its
        ;; block too — an id left behind would be a stale block waiting to be
        ;; reapplied to whatever reuses it
        state (update state :blocked disj-all dead-jids)
        ;; a supersession names a datum, so a swept datum must lose it too — an entry
        ;; left behind would hold a future handle OUT for a merge that is long gone
        state (update state :superseded dissoc-all dead)
        ;; the swept nodes were OUT and ungroundable, so dropping them cannot move
        ;; any survivor's label — only these bookkeeping sets need the removal
        state (update state :in         disj-all dead)
        state (update state :groundable disj-all dead)]
    [state {:removed-sentexes removed-sentexes
            :removed-justifications removed-justifications}]))

(defn- retract-known*
  [state datum]
  (let [;; 1. drop premise support for datum
        state    (-> state
                     (assoc-in [:nodes datum :premise?] false)
                     (update-in [:nodes datum] dissoc :premise-strength))
        ;; 2. MARK: the affected closure — also exactly the region to relabel, so
        ;;    marking and relabelling walk the graph once between them
        suspects (affected-region state [datum])
        ;; 3. relabel that region with datum no longer a premise (SAVE happens
        ;;    implicitly: a suspect with a surviving valid justification stays IN)
        state    (relabel-region* state suspects)]
    ;; 4-5. sweep what the retraction solely supported, and apply the removals
    (sweep* state suspects)))

(defn- suspend-premise*
  [state datum]
  (if-not (get-in state [:nodes datum])
    state
    (let [state (-> state
                    (assoc-in [:nodes datum :premise?] false)
                    (update-in [:nodes datum] dissoc :premise-strength))]
      (relabel-region* state (affected-region state [datum])))))

(defn- retract*
  "Return [new-state {:removed-sentexes [datum...] :removed-justifications [jid...]}].

  An unknown datum is a no-op: retraction is idempotent, and the test is what keeps it
  so.  Reaching `retract-known*` regardless would have `assoc-in` *create* the node it
  was asked to retract; the sweep then collects the phantom (not a premise, not
  groundable) and the result claims a removal that never happened."
  [state datum]
  (if-not (get-in state [:nodes datum])
    [state {:removed-sentexes [] :removed-justifications []}]
    (retract-known* state datum)))

(defn- set-blocked*
  [state jids]
  (let [jids    (set jids)
        was     (:blocked state #{})
        ;; only the justifications whose blocked status actually MOVED can change a
        ;; label, so they alone seed the region — the ones blocked in both sets are
        ;; already accounted for in the current labels
        changed (set/union (set/difference jids was) (set/difference was jids))]
    (if (empty? changed)
      state
      (-> state
          (assoc :blocked jids)
          (resettle (keep #(get-in state [:justs % :consequence]) changed))))))

(defn- swap-with-result!
  "Atomically apply `f` — a pure `state -> [state' result]` fn — to atom `a`,
  retrying on contention exactly as `swap!` does, and return the result.

  Do not reach for deref-then-`reset!` here.  It silently *discards* any concurrent
  `swap!` landing between the two, and under incidental concurrency (a REPL thread
  beside the web handler) what that loses is premises and justifications, not
  staleness.  Atomicity here makes concurrent operations compose; it does not make
  interleaved KB operations semantically serializable — the engine's contract is still
  one writer (docs/storage.md)."
  [a f]
  (loop []
    (let [old @a
          [new result] (f old)]
      (if (compare-and-set! a old new)
        result
        (recur)))))

;; ---- the representation protocol --------------------------------------------
;; The `Tms` protocol lives in `vaelii.impl.jtms-protocol` — both this reference
;; network and `vaelii.impl.dense-jtms` sit behind it, and it is too large to
;; instrument (scripts/coverage.sh).  Its methods are `:refer`red above; the
;; public façade over them is at the foot of this file.

;; ---- the reference implementation: one atom, one persistent map ---------

(deftype RefTms [^clojure.lang.Atom state]
  ;; `@tms` yields the state map, which is what the JTMS tests and the RAM benches
  ;; read.  It is the live map, not a copy — this implementation *is* the canonical
  ;; shape, so there is nothing to materialize.
  clojure.lang.IDeref
  (deref [_] @state)
  Tms
  (-believed? [_ datum]
    (let [s @state]
      (and (contains? (:in s #{}) datum)
           (not (contains? (:superseded s {}) datum)))))
  (-believed [_] (let [s @state] (seq (remove (:superseded s {}) (:in s #{})))))
  (-any-node?   [_] (boolean (seq (:nodes @state))))
  (-any-belief? [_] (let [s @state]
                      (boolean (first (remove (:superseded s {}) (:in s #{}))))))
  (-node? [_ datum] (contains? (:nodes @state) datum))
  (-datums [_] (keys (:nodes @state)))
  (-depth [_ datum] (get-in @state [:nodes datum :depth] 0))
  (-premise? [_ datum] (boolean (get-in @state [:nodes datum :premise?])))
  (-premise-strength [_ datum] (get-in @state [:nodes datum :premise-strength]))
  (-defeat-class [_ datum]
    (let [s @state]
      (when (contains? (:in s) datum) (get (:classes s) datum :default))))
  (-defeated [_] (:defeated @state #{}))
  (-blocked [_] (:blocked @state #{}))
  (-superseded [_] (:superseded @state {}))
  (-touched [_] (:touched @state #{}))
  (-touched-in [_] (:touched-in @state #{}))
  (-touched-new [_] (:touched-new @state #{}))
  (-reset-touched [_] (swap! state assoc :touched #{} :touched-in #{} :touched-new #{}) nil)
  (-supports [_ datum] (get-in @state [:nodes datum :supports] #{}))
  (-dependents [_ datum] (get-in @state [:nodes datum :consequences] #{}))
  (-justification [_ jid] (get-in @state [:justs jid]))
  (-justifications [_] (vals (:justs @state)))
  (-ensure-node [_ datum depth]
    ;; skip the swap when it would write back a value-identical map — a node already
    ;; present at a depth no higher than `depth` is exactly what `ensure*` leaves
    ;; (`min` keeps the stored depth); this runs once per placement, so most calls
    ;; are that no-op.  Sound under the single-writer contract: nothing moves the
    ;; node between the read and the skipped write.
    (let [n (when observe/*chain-fast-paths* (get (:nodes @state) datum))]
      (when (or (nil? n) (< (long depth) (long (:depth n 0))))
        (swap! state ensure* datum depth)))
    nil)
  (-add-premise [_ datum strength] (swap! state premise* datum strength) nil)
  (-suspend-premise [_ datum] (swap! state suspend-premise* datum) nil)
  (-add-justification [_ just] (swap! state add-just* just) nil)
  (-restrength-informant [_ informant strength]
    (swap! state restrength-informant* informant strength) nil)
  (-relabel [_] (swap! state relabel-all*) nil)
  (-defeat [_ datums]
    (swap! state (fn [s] (-> s (update :defeated (fnil into #{}) datums) (resettle datums))))
    nil)
  (-clear-defeats [_]
    (swap! state (fn [s] (let [was (:defeated s #{})]
                           (-> s (assoc :defeated #{}) (resettle was)))))
    nil)
  (-set-blocked [_ jids] (swap! state set-blocked* jids) nil)
  (-update-blocked [_ f] (swap! state (fn [s] (set-blocked* s (f (:blocked s #{}))))) nil)
  (-supersede [_ m] (swap! state assoc :superseded (into {} m)) nil)
  (-retract [_ datum] (swap-with-result! state #(retract* % datum)))
  (-sweep [_ seeds] (swap-with-result! state (fn [s] (sweep* s (affected-region s seeds)))))
  (-snapshot [_] @state))

(defn create-tms
  "A fresh, empty truth-maintenance network — the reference implementation.

  `:in` is the believed set and the authority on belief — nodes carry no label of
  their own, so there is no second copy to drift.  `:groundable` is the set that is
  *structurally* derivable from the premises ignoring defeats: a defeated node that
  is still groundable can revive, one that is not has lost its last derivation and
  is swept.  Both are maintained region-locally.

  `:blocked` is the set of justification ids currently blocked by their rule's
  exception; it starts empty and only a caller that has evaluated the exceptions can
  fill it.

  (Rules live in the stores as sentexes, not here.)"
  []
  (->RefTms (atom {:nodes {} :justs {} :defeated #{} :blocked #{} :superseded {}
                   :classes {} :in #{} :groundable #{}
                   :touched #{} :touched-in #{} :touched-new #{}})))

;; ---- public API ---------------------------------------------------------
;;
;; Thin dispatch onto the protocol.  Every engine path calls these, never a protocol
;; method directly, so the representation a KB was opened with is invisible above
;; this line.

(defn in?
  "Is `datum` believed?  Structural support minus supersession: a datum the equality
  layer has displaced keeps its place in the fixpoint (its twin is justified by it)
  but is not believed, so it stops matching and stops answering queries."
  [tms datum] (-believed? tms datum))

(defn depth  [tms datum] (-depth tms datum))
(defn known-datum?
  "Does the TMS hold a node for `datum`?  False for an **inert** sentex
  (`core/assert-inert`) — stored and indexed but never a TMS datum — which is how
  `retract!` tells a belief-bearing retraction from a direct teardown."
  [tms datum] (-node? tms datum))
(defn in-datums [tms] (-believed tms))
(defn any-node?   [tms] (-any-node? tms))
(defn any-belief? [tms] (-any-belief? tms))
(defn premise? [tms datum] (-premise? tms datum))
(defn premise-strength [tms datum] (-premise-strength tms datum))
(defn datums [tms] (-datums tms))

(defn defeat-class
  "The current defeat-class of an IN datum (monotonic / default), or nil
  when the datum is OUT.  Valid after `relabel`.

  `:classes` holds only the datums *above* the lattice's bottom, so IN-ness is what
  separates \"OUT, hence no class\" from \"IN at the default class\".  An entry's mere
  presence cannot carry both, since only one of them is information."
  [tms datum] (-defeat-class tms datum))

(defn defeated?  [tms datum] (contains? (-defeated tms) datum))
(defn defeated   [tms] (-defeated tms))

(defn touched
  "The datums whose region has been relabelled since the last `reset-touched!` — a
  superset of every datum whose belief could have flipped in that window.  `settle`
  reads it to tell `tax/refresh-beliefs` which handles moved, so a cache no moved
  supporter touches is skipped.

  Plus the datums a **redundant** justification landed on, which is the one entry here
  whose belief provably did *not* move: the window is read as \"what I published about
  this datum may be out of date\", and a second witness for an already-believed
  conclusion moves that without moving a label (`add-just*` says why the alternative is
  worse).  Every consumer reads a superset, so an extra handle costs a re-derivation and
  never an answer."
  [tms] (-touched tms))

(defn touched-in
  "The subset of `touched` that was **already believed** when this window first
  relabelled it.  With `touched` and current belief that is the whole belief delta:
  a datum in `touched` and IN now but not here came *in*, and one here that is OUT now
  went *out*.  The superset alone cannot say which — most of a relabelled region does
  not move — so this is what a caller reporting consequences reads.

  \"When first relabelled\" is what makes it a reading from before the window rather
  than from part-way through it: a datum relabelled twice keeps the earlier answer."
  [tms] (-touched-in tms))

(defn touched-new
  "The datums whose **node this window created** — the ones that had no label to move
  because they had no node.  `touched-in` cannot say this: a brand-new datum and a
  stored one that has been OUT since the settle before both read as \"not believed when
  the window opened\", and they are the two halves `revived` has to keep apart."
  [tms] (-touched-new tms))

(defn revived
  "The datums this window brought **back**: relabelled, believed now, not believed when
  the window opened, and already in the graph before it opened.

  A revival is the one belief move nothing downstream of it has seen.  A datum arriving
  is chained from as it arrives; a datum losing belief withdraws its conclusions through
  the justifications that name it.  A datum that goes OUT and comes back has neither —
  no arrival to chain from, no justification to withdraw — and while it was OUT the
  belief-filtered matcher hid it, so a partner that arrived meanwhile joined against
  nothing.  `settle` re-seeds these onto the agenda for exactly that reason.

  The three window sets between them are the whole belief delta, and this is the corner
  of it that costs work rather than a report: `touched` minus `touched-in` is what
  gained belief, and minus `touched-new` is the part of *that* which is not a datum the
  writer has already chained from.

  The two-arity takes `touched` as the caller already read it — `settle` reads the
  region once per pass and hands the value to everything in the pass that wants it,
  since the dense network materializes a fresh set on every read."
  ([tms] (revived tms (touched tms)))
  ([tms t]
   (if (empty? t)
     #{}
     (let [was-in (touched-in tms)
           born   (touched-new tms)]
       (into #{}
             (comp (remove was-in) (remove born) (filter #(in? tms %)))
             t)))))

(defn reset-touched!
  "Clear the accumulated touched sets (see `touched` / `touched-in` / `touched-new`).
  `settle` clears them once it has read them, at the *end* — so the window a caller sees
  spans everything since the last settle finished, which for `edit` is the whole
  deferred batch and its one settle rather than the settle alone."
  [tms] (-reset-touched tms) tms)

(defn superseded
  "The `datum -> reason` map of spellings an equality merge has displaced."
  [tms] (-superseded tms))

(defn superseded? [tms datum] (contains? (-superseded tms) datum))

(defn supersession
  "Why `datum` is superseded — the representative that displaced it — or nil."
  [tms datum] (get (-superseded tms) datum))

(defn supersede
  "**Replace** the superseded map with `m` (`{datum reason}`).

  Replace, not accumulate, for the same reason `set-blocked` replaces: the caller
  recomputes the whole answer from the current equality closure each settle, so a
  supersession cannot outlive the merge that caused it and belief cannot depend on
  the order the merges arrived in.

  No relabel: supersession does not enter the fixpoint (see the namespace docstring),
  it only subtracts from what `in?` reports, so there is no region to recompute."
  [tms m] (observe/note-change) (-supersede tms m) tms)

(defn supports
  "Justification ids that conclude `datum` (its supporting justifications)."
  [tms datum] (-supports tms datum))

(defn dependents
  "Justification ids that use `datum` as an antecedent (or a defeater)."
  [tms datum] (-dependents tms datum))

(defn justification [tms jid] (-justification tms jid))
(defn justifications [tms] (-justifications tms))

(defn- indexed
  "`coll` as something `nth` reaches in constant time — itself when it already is one
  (an antecedent list is stored as a vector), a vector otherwise."
  ^clojure.lang.Indexed [coll]
  (if (instance? clojure.lang.Indexed coll) coll (vec coll)))

(defn- covered?
  "Is every one of `a`'s `na` elements among `b`'s `nb`? — the subset half, by index
  rather than by seq, so nothing is allocated to answer it."
  [^clojure.lang.Indexed a ^long na ^clojure.lang.Indexed b ^long nb]
  (loop [i 0]
    (if (>= i na)
      true
      (let [x (.nth a i)]
        (if (loop [j 0]
              (cond (>= j nb)          false
                    (= x (.nth b j))   true
                    :else              (recur (inc j))))
          (recur (inc i))
          false)))))

(defn- same-antecedents?
  "Do `a` and `b` name the same antecedents *as sets* — same members, order and
  duplicates immaterial?  Mutual containment, which is that definition read directly,
  and it allocates nothing where `(= (set a) (set b))` allocated two hash sets.

  The allocation matters because of **where this is asked**.  A conclusion re-derived
  by k witnesses is checked once per witness against every justification it holds so
  far, so the comparison runs Θ(k²) times per conclusion across a run.  Measured on the
  W4 join pyramid (10k, 65k derived facts): 7.7M comparisons for 429k justifications
  stored, and building those sets was the single largest line in the profile.

  An antecedent list is two to five handles, so a scan beats hashing one of them, and
  a mismatch — the common case, since a fresh witness is a fresh justification — ends
  at the first member `b` does not hold."
  [a b]
  (let [av (indexed a) na (count a)
        bv (indexed b) nb (count b)]
    (and (covered? av na bv nb)
         (covered? bv nb av na))))

(def ^:dynamic *dedup-cache*
  "`{:tms tms :m mutable-HashMap-of-consequence→HashSet-of-just-keys}`, or nil — the
  default, and `has-justification?` scans `-supports` as always.

  A **run-scoped index over the dedup question**.  A conclusion re-derived by k
  witnesses is asked about once per witness, and each ask scans every justification it
  already holds — Θ(k²) `same-antecedents?` comparisons per conclusion across a forward
  run, with a `-justification` fetch apiece (the W4 join pyramid at 1k: ~430k firings
  over ~66k conclusions, and the scan is the largest line in the profile).  Bound by
  `chain/chain` for the length of a run, the first ask per conclusion builds its key
  set from `-supports` once and every later ask is one hash probe.

  The binding carries the TMS it was built beside, and `dedup-cache-for` hands the
  map out only to that TMS: a nested run over a *second* KB (legal from a
  `:on-progress` callback) reaches these fns with the first KB's binding still in
  force, and handle spaces overlap, so an unscoped reuse would answer one KB's dedup
  question from the other's supports.  Anything but the owning TMS bypasses to the
  reference scan.

  Justification *existence* is structural, not belief: a label flip adds and removes
  nothing here, so no entry goes stale by belief moving — only by a justification
  being **removed**, which reaches the graph on exactly two paths (`retract!`,
  `sweep!`), and both clear the cache wholesale.  `add-justification` extends the
  entry it passes through, so a bound cache never disagrees with the graph it mirrors.
  The keys are handle-content — no canonicalization — so there is no canon stamp to
  carry (`observe/*handle-cache*`, which has one, says what that kind of stamp is
  for; the `:tms` slot here is identity, not currency)."
  nil)

(defn- dedup-cache-for
  "The bound dedup index's map when it mirrors `tms`, else nil (see `*dedup-cache*`)."
  ^java.util.HashMap [tms]
  (let [c *dedup-cache*]
    (when (and c (identical? (:tms c) tms)) (:m c))))

(defmacro with-dedup-cache
  "Run `body` with the justification dedup index engaged for `tms`; an outer cache
  over the *same* TMS is reused rather than shadowed — the composition
  `observe/with-handle-cache` makes — and one over another TMS is shadowed by a
  fresh map.  A no-op when `observe/*chain-fast-paths*` is bound false — the
  reference lever `chain_fast_paths_test` pulls."
  [tms & body]
  `(let [tms# ~tms]
     (binding [*dedup-cache* (or (let [c# *dedup-cache*]
                                   (when (and c# (identical? (:tms c#) tms#)) c#))
                                 (when observe/*chain-fast-paths*
                                   {:tms tms# :m (java.util.HashMap.)}))]
       ~@body)))

;; Both key shapes normalize fixnum boxing to Long: the HashMap/HashSet compare with
;; Java equals, where Integer 7 ≠ Long 7, and the reference scan compares with `=`,
;; where they are equal — every handle producer allocates Longs today, but the cache
;; is where a future Integer would silently split a key, so the coercion lives here
;; rather than as a convention.
(defn- unbox ^Object [x] (if (int? x) (long x) x))

(defn- just-key
  "The content `has-justification?` deduplicates on — the informant plus the
  antecedents **as a set**, `same-antecedents?`'s judgement (order and duplicates
  immaterial) frozen into one hashable value.  A rule-handle informant is dropped from
  the set: a stored record never lists it there, and a firing's handle list does."
  [informant antecedents]
  (let [inf (unbox informant)
        s   (set antecedents)]
    [inf (if (integer? inf) (disj s inf) s)]))

(defn- dedup-keys
  "The cached key set for `consequence`, built from its supports on the first ask."
  ^java.util.HashSet [tms ^java.util.Map cache consequence]
  (let [ck (unbox consequence)]
    (or (.get cache ck)
        (let [s (java.util.HashSet.)]
          (doseq [jid (-supports tms consequence)]
            (when-let [j (-justification tms jid)]
              (.add s (just-key (:informant j) (:antecedents j)))))
          (.put cache ck s)
          s))))

(defn has-justification?
  "Is there already a support for `consequence` from `informant` over exactly these
  antecedents (as a set)?  Guards against duplicate justifications.  Answered from
  the dedup index when one is bound for this TMS — the same judgement, one hash
  probe — and by the supports scan otherwise."
  [tms informant antecedents consequence]
  (if-let [^java.util.Map cache (dedup-cache-for tms)]
    (.contains (dedup-keys tms cache consequence) (just-key informant antecedents))
    (let [antes (without-informant informant antecedents)]
      (boolean
       (some (fn [jid]
               (let [j (-justification tms jid)]
                 (and (= informant (:informant j))
                      (same-antecedents? antes (:antecedents j)))))
             (-supports tms consequence))))))

;; Every mutating entry point below bumps `observe/note-change` — the coarse clock a
;; cache derived from *belief* stamps itself with (the qualitative constraint networks
;; are the caller today).  It goes here, on the wrappers, rather than in the two `Tms`
;; implementations: the wrappers are the whole of how the engine reaches the network, so
;; one bump apiece is exhaustive by construction and neither representation can forget
;; one.  A call that turns out to move no label bumps anyway, which costs a re-derivation
;; and never a wrong answer.

(defn ensure-node [tms datum depth] (observe/note-change) (-ensure-node tms datum depth) datum)

(defn add-premise
  "Add `datum` as a premise at `strength` (default :default)."
  ([tms datum] (add-premise tms datum :default))
  ([tms datum strength-kw]
   (observe/note-change)
   (-add-premise tms datum (or strength-kw :default))
   datum))

(defn suspend-premise
  "Drop `datum`'s premise mark and relabel its region — a retraction's effect on
  **belief**, and nothing else.  Unknown datums no-op.

  `retract!` is this plus the sweep, and the sweep is exactly the part that cannot be
  put back: it deletes, so restoring the datum afterwards means re-deriving it at fresh
  handles.  Belief does not need it — a swept datum is OUT and ungroundable, so
  dropping it moves no label — which is what makes the pair (`suspend-premise`, then
  `add-premise` at the same strength) a reversible retraction.  `core/preview` is the
  caller: it answers what a removal would do to belief and then puts the premise back.

  Bare, not `!`, because nothing is lost: the node, its justifications and its record
  all stay exactly where they were."
  [tms datum] (observe/note-change) (-suspend-premise tms datum) datum)

(defn add-justification [tms just]
  (observe/note-change)
  (-add-justification tms just)
  ;; keep a bound dedup index in step: extend the one entry this justification lands
  ;; in, when that entry has been built (an absent entry rebuilds from `-supports`,
  ;; which now includes this justification, so absence needs nothing)
  (when-let [^java.util.Map cache (dedup-cache-for tms)]
    (when-let [^java.util.HashSet ks (.get cache (unbox (:consequence just)))]
      (.add ks (just-key (:informant just) (:antecedents just)))))
  just)

(defn restrength-informant
  "Set `strength` as the rule-contribution slot of every justification whose informant
  is `informant`, and relabel the region their consequences span.

  A justification's `:strength` is the *rule's* contribution, read off the record at
  fire time (`chain/rule-view-of`) — a cache of one slot of one sentex.  When that slot
  moves (a re-asserted rule's defeasibility resolves strict, `core/reconcile-rule-slots!`),
  the cache must move with it, or belief keeps the arrival order the slot resolution
  exists to remove: the same rule stated defeasible-then-strict and strict-then-defeasible
  would confer two different classes on conclusions already derived.  The antecedent half
  of `conferred-class` is already read live at labelling time, so this one scalar is the
  only stored copy — updated here, then relabelled through the full affected region,
  since a class that rises can flip defeat decisions anywhere in the consumer ancestor set."
  [tms informant strength]
  (observe/note-change)
  (-restrength-informant tms informant strength)
  tms)

(defn relabel
  "Recompute *every* node's label and defeat-class, and clear the blocked and superseded
  sets — the whole-graph counterpart to the region relabels the assert / retract / settle
  path runs, for a caller that holds no smaller region.  Nothing on the live paths calls it:
  the assert / retract / settle path relabels regions, and `recover` composes the region
  relabels its own rebuild runs (`recovery/rebuild-tms`), its settle re-deriving blocking
  wholesale.  It is the
  differential oracle's whole-graph operation (`strength_test`, `jtms_dense_oracle_test`,
  `jtms_blocked_test`), which is why both representations implement it.

  It **clears blocked and superseded** because both are derived from queries that are never
  stored — a whole-graph relabel cannot recover either and must not inherit a stale one."
  [tms] (observe/note-change) (-relabel tms) tms)

(defn defeat
  "Force `datums` OUT (contradiction resolution) and relabel the region they affect."
  [tms datums] (observe/note-change) (-defeat tms datums) tms)

(defn blocked
  "The justification ids currently blocked by their rule's exception."
  [tms] (-blocked tms))

(defn blocked?
  "Is justification `jid` currently blocked?"
  [tms jid] (contains? (-blocked tms) jid))

(defn set-blocked
  "Replace the blocked set with `jids` — the justifications whose exception the caller
  has just found to hold — and relabel the region the change reaches.

  The set is *replaced*, not accumulated: the caller re-evaluates every exception it
  cares about and states the whole answer, exactly as core recomputes the defeated set
  each settle.  Nothing here remembers that a justification was blocked a round ago,
  so belief cannot depend on the order the exceptions were discovered in.

  The region is seeded from the **consequences of the justifications whose blocked
  status changed** — blocking or unblocking j can only move j's conclusion and what
  follows from it — so cost is proportional to that region, not to the graph, and a
  call that changes nothing does no work at all.  `#{}` unblocks everything."
  [tms jids] (observe/note-change) (-set-blocked tms jids) tms)

(defn block
  "Add `jids` to the blocked set (a delta on `set-blocked`, for a caller that knows
  only what it just found rather than the whole answer).  Reads and writes in one
  step, so a delta cannot be computed against a set that has already moved."
  [tms jids] (observe/note-change) (-update-blocked tms #(into % jids)) tms)

(defn unblock
  "Remove `jids` from the blocked set."
  [tms jids] (observe/note-change) (-update-blocked tms #(reduce disj % jids)) tms)

(defn clear-defeats!
  "Reset the derived defeated set and relabel — the basis for revival.

  The region is the *previously* defeated nodes: lifting a forced OUT can only
  affect them and what follows from them, so a settle that defeated nothing last
  round does no work at all here."
  [tms] (observe/note-change) (-clear-defeats tms) tms)

(defn grounded-in-region
  "For `extra` — datums to force OUT — the forward consequence closure of `extra`
  (`:region`) and, within it, the datums that stay believed once `extra` is disbelieved
  (`:in`), the rest of the graph held at its current label.

  Read **region-local**: belief for a datum outside the region is taken per-datum from
  `in?`, never materialized, so cost is proportional to the region and not to the KB — the
  property that keeps `classify-local` linear in the number of dilemmas rather than
  quadratic (`grounded_forcing_out_test`).  The walk mirrors `affected-region` over the
  closure and the fixpoint mirrors `region-fixpoint` over it, both restricted to the
  region.  Built on the protocol reads (`in?`, `dependents`, `supports`, `justification`,
  `premise?`, `defeated`, `blocked`, `superseded?`), so both network representations answer
  it identically without either implementing a method — the derived-read footing `revived`
  has.

  The read behind the solve-free skeptical/credulous bracket
  (`vaelii.impl.asp.label/classify-local`, docs/labeling.md) and behind
  `grounded-forcing-out`."
  [tms extra]
  (let [extra       (set extra)
        forced?     (let [f (into (set (defeated tms)) extra)] #(contains? f %))
        blocked-set (blocked tms)
        just-of     #(justification tms %)
        ;; raw belief for a boundary datum: reported belief plus the superseded spellings
        ;; the fixpoint keeps IN (their twin is justified by them).
        raw-in?     (fn [d] (or (in? tms d) (superseded? tms d)))
        ;; forward consequence closure of `extra`, seeds included — the only datums a
        ;; forced-out member can move.
        region      (loop [seen #{}, stack (vec extra)]
                      (if (empty? stack)
                        seen
                        (let [d (peek stack), stack (pop stack)]
                          (if (contains? seen d)
                            (recur seen stack)
                            (recur (conj seen d)
                                   (into stack (comp (keep just-of) (map :consequence))
                                         (dependents tms d)))))))
        ;; an antecedent in the region reads the recomputed set; outside it, live belief
        believed?*  (fn [in d] (if (contains? region d) (contains? in d) (raw-in? d)))
        valid-here? (fn [in j] (and (every? #(believed?* in %) (:antecedents j))
                                    (let [inf (:informant j)]
                                      (or (not (integer? inf)) (believed?* in inf)))
                                    (not (contains? blocked-set (:id j)))))
        ;; region premises seed the fixpoint unless forced out
        seed        (into #{} (filter #(and (premise? tms %) (not (forced? %)))) region)
        ;; the justifications that can conclude something in the region
        cands       (into [] (comp (mapcat #(supports tms %)) (distinct) (keep just-of)) region)
        in          (loop [in seed, stack (vec cands)]
                      (if (empty? stack)
                        in
                        (let [j (peek stack), stack (pop stack), c (:consequence j)]
                          (if (and (contains? region c)
                                   (not (contains? in c))
                                   (not (forced? c))
                                   (valid-here? in j))
                            (recur (conj in c)
                                   (into stack (keep just-of) (dependents tms c)))
                            (recur in stack)))))]
    {:region region :in in}))

(defn grounded-forcing-out
  "The believed datums recomputed with every datum in `extra` **forced OUT**, the rest of
  the graph held at its current label — a non-mutating read of what belief would be if
  `extra` were disbelieved.  Equal to the believed set after `(defeat tms extra)` on a
  network with nothing else defeated, computed without touching the network
  (`grounded-forcing-out-equals-defeat` pins it).

  The recompute is region-local (`grounded-in-region`); splicing its region-in-set into
  belief outside the region is the one ordinary belief read, the cost `in-datums` has.  A
  caller that needs only the region — `classify-local` — reads `grounded-in-region`
  directly and pays neither."
  [tms extra]
  (if (empty? (seq extra))
    (set (in-datums tms))
    (let [{:keys [region in]} (grounded-in-region tms extra)
          supersede (set (keys (superseded tms)))]
      ;; boundary belief (outside the region) is unchanged — take it from `in-datums`; the
      ;; region's own belief is `in`.  Both drop the superseded spellings, as `in?` does.
      (into (into #{} (remove #(or (contains? region %) (contains? supersede %))) (in-datums tms))
            (remove supersede)
            in))))

(defn classes-in-region
  "The defeat-classes of the datums `in` holds inside `region`, where `region` and `in`
  are a `grounded-in-region` answer: the classes belief carries with that answer's `extra`
  forced OUT, the rest of the graph held at its current classes.

  The least fixpoint `region-classes` computes during a relabel, over the same equation —
  a datum's class is the strongest of its premise strength and what each valid
  justification confers, and a justification confers the weakest of its own strength and
  its antecedents' classes.  Every member starts at `:default`, the bottom, and the
  operator is monotone, so iterating to stability reaches the least fixpoint whatever the
  visit order.  Built on the protocol reads, like `grounded-in-region`, so both network
  representations answer it without implementing a method.

  The settle's reader of it is a nogood weighed at a vantage that withdraws part of what
  supports a member (docs/nmtms.md, \"A defeat is scoped to its vantage\")."
  [tms region in]
  (let [blocked-set (blocked tms)
        members     (filterv #(contains? in %) region)
        believed?*  (fn [d] (if (contains? region d)
                              (contains? in d)
                              (or (in? tms d) (superseded? tms d))))
        class-of    (fn [classes d] (if (contains? region d)
                                      (get classes d :default)
                                      (or (defeat-class tms d) :default)))
        node-class  (fn [classes d]
                      (let [prem (when (premise? tms d) (or (premise-strength tms d) :default))
                            strs (for [jid  (supports tms d)
                                       :let [j (justification tms jid)]
                                       :when (and j
                                                  (every? believed?* (:antecedents j))
                                                  (let [inf (:informant j)]
                                                    (or (not (integer? inf)) (believed?* inf)))
                                                  (not (contains? blocked-set (:id j))))]
                                   (reduce (fn [c a] (strength/min c (class-of classes a)))
                                           (or (:strength j) :monotonic)
                                           (:antecedents j)))]
                        (reduce strength/max :default (remove nil? (cons prem strs)))))]
    (loop [classes (zipmap members (repeat :default))]
      (let [next (reduce (fn [m d] (assoc m d (node-class classes d))) classes members)]
        (if (= next classes) classes (recur next))))))

(defn retract!
  "Dependency-directed retraction (drop premise / relabel / sweep).  Returns
  {:removed-sentexes [datum...] :removed-justifications [jid...]}.
  Unknown datums no-op (empty result): retraction is idempotent."
  [tms datum]
  (observe/note-change)
  ;; the one path besides `sweep!` that removes justifications — a bound dedup index
  ;; over this TMS is cleared wholesale rather than edited (see `*dedup-cache*`)
  (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
  (-retract tms datum))

(defn sweep!
  "Garbage-collect the consequence closure of `seeds`: every datum in it that is not
  a premise and is no longer *groundable* is deleted, along with the justifications
  touching it.  Returns the same shape as `retract!`, for the caller to apply to its
  own stores.

  This is `retract!`'s sweep without the retraction.  It exists because `exceptWhen`
  removes a conclusion by invalidating its justification rather than by withdrawing a
  premise: blocking suppresses groundability (`region-fixpoint`), so the conclusion is
  ungroundable and this collects it exactly as a retraction would — the trade
  docs/exceptions.md records under \"Garbage collection, not defeat\".

  Labels must already be current — `set-blocked` relabels the same region — so this
  only reads `:groundable`."
  [tms seeds]
  (observe/note-change)
  ;; removes justifications, so a bound dedup index over this TMS is cleared (see
  ;; `*dedup-cache*`)
  (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
  (-sweep tms seeds))

(defn snapshot
  "The network as one canonical persistent map (see `-snapshot`).  A testing and
  debugging surface — the differential oracle compares two implementations with it."
  [tms] (-snapshot tms))

;; ---- what the network holds beside itself, declared ---------------------

(caches/register-cache
 {:cache    :justification-dedup
  :label    "Justification dedup"
  :scope    :process
  :unit     "conclusions"
  :limit    nil
  :counters nil
  :note     (str "Which justifications a conclusion already holds, so a conclusion "
                 "reached by k witnesses is not scanned k times. Bound for the length "
                 "of one chaining run and dropped when it returns, so there is nothing "
                 "to count between runs.")
  :read     (fn [_] {:entries (some-> ^java.util.HashMap (:m *dedup-cache*) .size)})})
