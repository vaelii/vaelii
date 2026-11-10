;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.jtms
  "The reference non-monotonic truth-maintenance network: nodes keyed by sentex handle
  (no sentex reference, so the resident graph holds no records), justifications, premise
  strengths, defeat-classes, and the `superseded`, forced, and `blocked` sets.  Belief is
  a least fixpoint over current state, so it is order-independent, and every relabel is
  scoped to the affected region (locality).  The caller owns physical deletion after a
  sweep.  See docs/nmtms.md."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.jtms-protocol :refer [Tms
                                               -believed? -believed -node? -datums
                                               -any-node? -any-belief? -depth -premise?
                                               -premise-strength -defeat-class
                                               -blocked -superseded -touched -touched-in
                                               -touched-new -touched-out -reset-touched
                                               -touch-mark -touched-since
                                               -supports
                                               -dependents -justification -justifications
                                               -ensure-node -add-premise -suspend-premise
                                               -add-justification -restrength-informant
                                               -forced? -forced-members -set-forced
                                               -relabel -set-blocked
                                               -supersede -retract -sweep
                                               -drop-justification -snapshot
                                               -hold -release -held]]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.types.tms :as tms-types])
  (:import [java.util PriorityQueue]
           [java.util.concurrent.atomic AtomicReference]))

(defmacro ^:private moving
  "Run `body`, a mutation of the network, between two moves of the change clock
  (`observe/note-change`), and answer what `body` answers.  Every mutating entry point wraps
  its mutation in this, so neither `Tms` representation can forget a bump.  The clock moves
  on both sides: a cache installs an entry only when the clock still reads the value it read
  before computing (`literal-cache/lookup`, `provers/cached-reach`), the first move keeps a
  read inside the mutation from an older entry, and the second retires entries a reader
  thread computed mid-mutation (`kb_concurrency_test`)."
  [& body]
  `(do (observe/note-change)
       (let [r# (do ~@body)]
         (observe/note-change)
         r#)))

(defn- without-informant
  "`antecedents` as a vector, with a rule-handle `informant` taken out of it.  A firing
  hands over its handle list with the rule in it (`chain/derive-conclusion`), and so does
  a seven-field frame on disk (`codec/decode-justification`); both store the rule once."
  [informant antecedents]
  (if (and (integer? informant)
           (reduce (fn [_ h] (if (= informant h) (reduced true) false)) false antecedents))
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

(def respell-informant
  "The informant of a justification storing a spelling a reader reads of a fact, from the
  row holding the fact as written and the marks that sort it (`chain/respell-rows!`).  Its
  first antecedent is the row and the rest are the marks: every one must be IN for the
  justification to be valid, and only the row caps the class it confers
  (`class-antecedents`), so a spelling holds at the class of the fact it spells."
  'respell)

(defn class-antecedents
  "The antecedents of justification `j` whose classes cap the class it confers: all of
  them, except under `respell-informant`, where only the first does."
  [j]
  (let [as (:antecedents j)]
    (if (and (= respell-informant (:informant j)) (next as))
      [(first as)]
      as)))

(defn ->just
  "Construct a Justification, defaulting `strength` to :monotonic — a bare monotone
  justification adds no defeasibility of its own, so `conferred-class` caps it at its
  weakest antecedent.  A rule-handle informant is taken out of `antecedents`
  (`without-informant`). `subsumptions` is a firing's `[sub super]` set. Optional
  `reading` records a producer's source interpretation, outside logical bindings;
  both are retained only when nonempty and participate in proof identity."
  ([id informant antecedents consequence bindings]
   (->just id informant antecedents consequence bindings :monotonic nil))
  ([id informant antecedents consequence bindings strength]
   (->just id informant antecedents consequence bindings strength nil))
  ([id informant antecedents consequence bindings strength subsumptions]
   (->just id informant antecedents consequence bindings strength subsumptions nil))
  ([id informant antecedents consequence bindings strength subsumptions reading]
   (cond-> (tms-types/->Justification id informant (without-informant informant antecedents)
                                      consequence bindings (or strength :monotonic))
     (seq subsumptions) (assoc :subsumptions subsumptions)
     (seq reading) (assoc :reading reading))))

(defn graph-just
  "The part of a justification the network is made of: everything except the firing's
  `:bindings`.  Belief never reads the bindings (`valid?` needs the antecedents,
  `conferred-class` the strength and informant); only the `exceptWhen` and NAF re-evaluations
  want them, and those take the record from the store.  Measured (`lein bench-jtms`): 80 of
  277 B per justification at 3.6 justifications per node.  It also normalizes (antecedents to a
  vector without the informant, strength defaulted) so both representations store equal
  values. `:bindings` is nil, not dropped. `:subsumptions` and optional `:reading`
  stay for `just-key`; a reader policy must explicitly interpret the latter."
  [j]
  (->just (:id j) (:informant j) (:antecedents j) (:consequence j) nil (:strength j)
          (:subsumptions j) (:reading j)))

;; Owner-key remapping shares the dedup key defined after the network accessors.
(declare justification-key)

(defn remap-reading
  "Remap a source reading's antecedent ids during import or a row fold. If several
  old sources become the SAME handle, an ordinary strict source wins on each axis.
  Reader contexts and other non-handle evidence are preserved. Nil remains nil."
  ([reading antecedents remap] (remap-reading reading antecedents remap false))
  ([reading antecedents remap informant?]
   (when (seq reading)
     (let [changed (reduce (fn [r axis]
                             (if-let [relaxed (get reading axis)]
                               (let [strict (into #{} (comp (remove relaxed) (keep remap)) antecedents)
                                     kept (into #{} (comp (keep remap) (remove strict)) relaxed)]
                                 (if (seq kept) (assoc r axis kept) (dissoc r axis)))
                               r))
                           reading [:nonplacing :label-only])
           changed (cond-> changed
                     (seq (:rewrite-reads reading))
                     (assoc :rewrite-reads
                            (into #{} (keep (fn [{:keys [handle] :as read}]
                                               (when-let [h (remap handle)]
                                                 (assoc read :handle h))))
                                  (:rewrite-reads reading))))]
       (if-let [[inf owner-antes subs owner-reading] (:owner-key reading)]
         ;; Import remaps the owning informant; folding retains it.
         (assoc changed :owner-key
                (justification-key (if informant? (remap inf) inf)
                                   (mapv remap owner-antes) subs
                                   (remap-reading owner-reading owner-antes remap informant?)))
         changed)))))

;; ---- derivation depth ---------------------------------------------------
;;
;; The two walks keep every stored depth at the least solution of the depth equation
;; (docs/nmtms.md, "Derivation depth"), reading the network through accessor fns so the dense
;; network runs the same code.

(defn- depth-queue
  "An empty min-queue of `[depth datum]` entries."
  ^PriorityQueue []
  (PriorityQueue. 16 (fn [a b] (Long/compare (long (nth a 0)) (long (nth b 0))))))

(defn- one-deeper
  "One more than the deepest of `antes`, each read through `depth-of`."
  ^long [antes depth-of]
  (inc (long (reduce (fn [^long m a] (max m (long (depth-of a)))) 0 antes))))

(defn- cites?
  "Does `antes` name `d`?  A justification lists its rule under the rule's node too, and
  the rule is no antecedent of it."
  [antes d]
  (boolean (some #(= d %) antes)))

(defn lowered-depths
  "`{node depth}` for `datum` at `depth` and for every node downstream of it whose
  shallowest justification reads shallower once it is, walked shallowest first.  Writes
  nothing.  `dependents` names the justification ids citing a node, `antecedents` and
  `consequence` read one justification (nil for an id no longer stored), and `depth-of`
  is the stored depth."
  [datum depth dependents antecedents consequence depth-of]
  (let [q (depth-queue)]
    (.add q [depth datum])
    (loop [low {datum depth}]
      (if-let [[v d] (.poll q)]
        (if (> (long v) (long (get low d)))
          (recur low)
          (recur (reduce (fn [low jid]
                           (let [antes (antecedents jid)
                                 c     (consequence jid)]
                             (if (or (nil? c) (not (cites? antes d)))
                               low
                               (let [cur  #(get low % (depth-of %))
                                     cand (one-deeper antes cur)]
                                 (if (< cand (long (cur c)))
                                   (do (.add q [cand c]) (assoc low c cand))
                                   low)))))
                         low (dependents d))))
        low))))

(defn region-depths
  "`{node depth}` for each node of `region` whose depth moves when the region is solved
  afresh, every node outside it held at its stored depth.  `region` is closed under
  consequence (an affected region).  Writes nothing.  Knuth's generalization of Dijkstra: a
  justification is queued once its last antecedent inside the region is final; the queue pops
  shallowest first."
  [region premise? supports dependents antecedents consequence depth-of]
  (let [inside (set region)
        q      (depth-queue)
        ;; jid -> [its antecedents inside the region not yet final, the deepest final one]
        wait   (volatile! {})]
    (doseq [d inside]
      (if (premise? d)
        (.add q [0 d])
        (doseq [jid (supports d)]
          (let [antes (antecedents jid)
                n     (count (into #{} (filter inside) antes))
                hi    (reduce (fn [^long m a] (if (contains? inside a) m (max m (long (depth-of a)))))
                              0 antes)]
            (if (zero? n) (.add q [(inc hi) d]) (vswap! wait assoc jid [n hi]))))))
    (loop [final {}]
      (if-let [[v d] (.poll q)]
        (if (contains? final d)
          (recur final)
          (do (doseq [jid (dependents d)
                      :let [[n hi] (get @wait jid)]
                      :when (and n (cites? (antecedents jid) d))]
                (let [hi (max (long hi) (long v))]
                  (if (== 1 (long n))
                    (do (vswap! wait dissoc jid) (.add q [(inc hi) (consequence jid)]))
                    (vswap! wait assoc jid [(dec (long n)) hi]))))
              (recur (assoc final d v))))
        (into {} (remove (fn [[d v]] (== (long v) (long (depth-of d))))) final)))))

;; ---- labelling ----------------------------------------------------------

(defn- lower-depth*
  "`state` with `datum` lowered to `depth` and the fall pushed down its consequences."
  [state datum depth]
  (let [nodes (:nodes state)
        justs (:justs state)]
    (reduce-kv (fn [s d v] (assoc-in s [:nodes d :depth] v))
               state
               (lowered-depths datum depth
                               #(get-in nodes [% :consequences])
                               #(get-in justs [% :antecedents])
                               #(get-in justs [% :consequence])
                               #(get-in nodes [% :depth] 0)))))

(defn- ensure* [state datum depth]
  (if-let [n (get-in state [:nodes datum])]
    (if (< (long depth) (long (:depth n 0)))
      (lower-depth* state datum depth)
      state)
    ;; A node created since the last reset is noted as it is created: by the time the relabel reads
    ;; the graph, a new node and one that has been OUT for a hundred settles look identical.
    ;; `touched-new` separates them (see `revived`).
    (-> state
        (assoc-in [:nodes datum] {:datum datum :premise? false
                                  :depth depth :supports #{} :consequences #{}})
        (update :touched-new (fnil conj #{}) datum))))

(defn- valid?
  "Is justification `j` currently satisfied under the IN set `in`, the blocked set
  `blocked` and the `:void` forced set `void`?

  Four independent conditions: every antecedent believed, the rule believed when the
  informant is a rule handle, the justification not blocked by its rule's exception, and
  not void."
  [j in blocked void]
  (let [inf (:informant j)]
    (and (every? #(contains? in %) (:antecedents j))
         (or (not (integer? inf)) (contains? in inf))
         (not (contains? blocked (:id j)))
         (not (contains? void (:id j))))))

(defn- forced-set
  "`state`'s forced set `kind`."
  [state kind]
  (get-in state [:forced kind] #{}))

(defn- conferred-class
  "The defeat-class a valid justification confers on its consequence: its own strength,
  capped by the weakest of its antecedents' classes, and by its rule's class when the informant
  is a rule handle that is not a premise (a generator's mint, a derived rule).  A premise rule
  informant is not in the cap, since a rule takes `:default` unless its assertion says
  otherwise.  The rule's contribution is `:strength` on the justification
  (`provers/firing-strength`).  See docs/nmtms.md, \"Strength propagates from the antecedents\"."
  [state j classes]
  (let [inf (:informant j)
        c   (reduce (fn [c a] (strength/min c (get classes a :default)))
                    (or (:strength j) :monotonic)
                    (class-antecedents j))]
    (if (and (integer? inf) (not (get-in state [:nodes inf :premise?])))
      (strength/min c (get classes inf :default))
      c)))

(defn- node-class
  "The defeat-class of an IN datum: the strongest support it has — its premise
  strength, and the class each currently-valid justification *confers* on it.

  A blocked justification is not valid, so it confers nothing: its strength is never
  read, exactly as if it were missing an antecedent."
  [state d in classes]
  (let [n       (get-in state [:nodes d])
        blocked (:blocked state #{})
        void    (forced-set state :void)
        prem  (when (:premise? n)
                (if (contains? (forced-set state :mono) d)
                  :monotonic
                  (:premise-strength n :default)))
        strs  (for [jid (:supports n)
                    :let [j (get-in state [:justs jid])]
                    :when (and j (valid? j in blocked void))]
                (conferred-class state j classes))]
    (reduce strength/max :default (remove nil? (cons prem strs)))))

;; ---- region-local relabelling -------------------------------------------

(defn- affected-region
  "Every node whose label could change when `seeds` change: the forward closure over
  consequence justifications, seeds included.  Everything outside it is boundary, held
  fixed and not read (docs/nmtms.md, \"Locality\")."
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
  "Least fixpoint of IN over `region`, with `base` (the boundary's believed nodes) held fixed.
  Blocking invalidates a justification and is read through `valid?`, so the retraction sweep
  collects an excepted conclusion (docs/exceptions.md, \"Garbage collection, not defeat\").
  See docs/nmtms.md, \"Locality\"."
  [state region cands base]
  (let [blocked (:blocked state #{})
        void    (forced-set state :void)
        out     (forced-set state :out)
        justs   (:justs state)
        nodes   (:nodes state)
        seeded  (into base (filter #(and (get-in state [:nodes % :premise?])
                                         (not (contains? out %))))
                      region)]
    ;; Semi-naive worklist: `valid?` is monotone in `in`, so a justification is re-tested only when an
    ;; antecedent newly enters `in`, reached through `:consequences`.  O(region edges), the same unique
    ;; least fixpoint.
    (loop [in    seeded
           stack (vec cands)]
      (if (empty? stack)
        in
        (let [j (peek stack), stack (pop stack), c (:consequence j)]
          (if (and (contains? region c)
                   (not (contains? in c))
                   (not (contains? out c))
                   (valid? j in blocked void))
            (recur (conj in c)
                   (into stack (keep justs) (get-in nodes [c :consequences])))
            (recur in stack)))))))

(defn- region-classes
  "Defeat-classes for `region` under the IN set `in`, as a least fixpoint: every in-region IN
  node starts at `:default` and the monotone operator (`strength/max`, `strength/min`) is
  iterated to stability.  Nodes outside the region are boundary."
  [state region in]
  (let [nodes   (:nodes state)
        justs   (:justs state)
        base    (reduce (fn [m d] (if (contains? in d) m (dissoc m d)))
                        (:classes state {}) region)
        members (filterv #(contains? in %) region)
        init    (reduce (fn [m d] (assoc m d :default)) base members)]
    ;; Worklist over the same monotone operator: a member is recomputed only when a node it derives
    ;; from moves.  Starting every member at :default, it converges to the unique least fixpoint in
    ;; O(region edges); the lattice has height one.
    (loop [classes init
           stack   (vec members)]
      (if (empty? stack)
        ;; drop the :default entries of this region: every read already defaults an absent datum to
        ;; `:default`, and on a mostly-default KB they are nearly the whole map.  `defeat-class` decides
        ;; OUT-vs-absent from `:in`.  Only the members are filtered, since every entry outside the region
        ;; came from an earlier relabel that applied this filter; rebuilding the whole map would make a
        ;; region relabel O(classes), which locality forbids.
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

(defn- note-epoch
  "`state` with `hs` recorded in the open epoch, the one the last `-touch-mark`
  opened: what `-touched-since` reads.  No epoch is open before the first mark since the
  last reset, so touched sets nobody marks record nothing twice."
  [state hs]
  (let [es (:epochs (:marks state))]
    (if (seq es)
      (update-in state [:marks :epochs (dec (count es))] into hs)
      state)))

(defn- relabel-region*
  "Recompute `:in` and the defeat-classes for `region`, holding every node outside it fixed.
  Equivalent to a global relabel whenever the region is the affected closure of what changed,
  and proportional to the region."
  [state region]
  (let [old-in   (:in state #{})
        ;; the region members not relabelled since the last reset: their label now is their label before
        ;; anything since the reset moved, the reading `touched-in` wants.
        fresh    (into #{} (remove (:touched state #{})) region)
        ;; only the justifications that can conclude something in the region matter
        cands    (into [] (comp (mapcat #(get-in state [:nodes % :supports] #{}))
                                (distinct)
                                (keep #(get-in state [:justs %])))
                       region)
        in       (region-fixpoint state region cands (set/difference old-in region))
        state    (assoc state :in in)]
    ;; Record the region as touched: a supporter's belief can flip only inside a relabelled region, so
    ;; the accumulated set is a superset of every handle whose belief moved this settle
    ;; (`tax/refresh-beliefs`).  `touched-in` records which were believed before, which gives the
    ;; direction of each move.
    (-> state
        (assoc :classes (region-classes state region in))
        (update :touched (fnil into #{}) region)
        (note-epoch region)
        (update :touched-in (fnil into #{})
                (let [held (forced-set state :held)]
                  ;; a `:held` member is IN and was not believed
                  (if (empty? held)
                    (filter old-in fresh)
                    (filter #(and (contains? old-in %) (not (contains? held %))) fresh)))))))

(defn- resettle
  "Relabel the region affected by `seeds`."
  [state seeds]
  (relabel-region* state (affected-region state seeds)))

(defn- relabel-all*
  "Relabel every node.  No engine path calls it: it is the differential oracle's whole-graph
  operation, so both representations carry it (`relabel`).  The blocked set and the
  supersession map are reset to empty first, since neither is stored (blocking derives from
  the exception queries, supersession from the equality closure) and a relabel merging into
  them could only add stale entries.  A caller wanting either states the whole answer again
  (`set-blocked`, `supersede`)."
  [state]
  (let [state (assoc state :blocked #{} :superseded {})]
    (relabel-region* state (set (keys (:nodes state))))))

(defn- premise*
  "Mark `datum` a premise at `strength-kw` and relabel its region.

  A mark the node already holds at the same strength, on a node that is IN, relabels
  nothing: every input of the region's fixpoint is unchanged, so the relabel would write
  back the labels and classes it read.  `datum` alone is noted touched, as `add-just*`'s
  fast path notes its consequence.  Without this, re-marking a premise relabels its whole
  forward closure, and `recovery/rebuild-tms` over a network that already holds a chain n
  deep re-marks n premises, which costs O(n²)."
  [state datum strength-kw]
  (let [state (ensure* state datum 0)
        s     (or strength-kw :default)
        node  (get-in state [:nodes datum])]
    (if (and (:premise? node) (= s (:premise-strength node)) (contains? (:in state #{}) datum))
      (cond-> (-> state
                  (update :touched (fnil conj #{}) datum)
                  (note-epoch [datum]))
        (not (or (contains? (:touched state #{}) datum)
                 (contains? (forced-set state :held) datum)))
        (update :touched-in (fnil conj #{}) datum))
      (-> state
          (assoc-in [:nodes datum :premise?] true)
          (assoc-in [:nodes datum :premise-strength] s)
          (resettle [datum])))))

(defn- add-just* [state j]
  (let [{:keys [id consequence] :as just} (graph-just j)
        state (-> state
                  (assoc-in [:justs id] just)
                  (update-in [:nodes consequence :supports] conj id)
                  (as-> s (reduce-rests-on (fn [st a] (update-in st [:nodes a :consequences] conj id))
                                           s just)))
        in    (:in state #{})]
    ;; Fast path: a redundant justification changes nothing, so skip the region relabel.  If
    ;; `consequence` is already believed and this justification confers no stronger defeat-class than
    ;; it holds (or is not valid), belief, groundability and downstream classes are unmoved.  This
    ;; collapses a recursive forward load from O(derived^2) to O(derived): the closure is walked once,
    ;; when the fact is first derived.  Any real change takes the full resettle.
    ;;
    ;; The consequence still enters `touched`, since a second witness moves what a reader published
    ;; about the datum without moving a label.  Noting one handle is O(1); polling every standing pair
    ;; is O(standing) per settle (`lein perf`'s `negation-arbitration`: a 19% worse growth ratio at 800
    ;; standing dilemmas).  `touched-in` takes it only when no earlier relabel since the reset has
    ;; (`relabel-region*`'s `fresh`).
    (if (and (contains? in consequence)
             (or (not (valid? just in (:blocked state #{}) (forced-set state :void)))
                 (let [cls (get (:classes state) consequence :default)]
                   (= cls (strength/max cls (conferred-class state just (:classes state)))))))
      (cond-> (-> state
                  (update :touched (fnil conj #{}) consequence)
                  (note-epoch [consequence]))
        (not (contains? (:touched state #{}) consequence))
        (update :touched-in (fnil conj #{}) consequence))
      (resettle state [consequence]))))

(defn- restrength-informant* [state informant strength]
  ;; The adjacency lists every justification a rule informs under the rule's node (`reduce-rests-on`
  ;; in `add-just*`), so `:consequences` is the candidate set and nothing scans `:justs`.  The informant
  ;; filter drops a justification that uses the rule's handle as an ordinary antecedent.
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
  "`(apply dissoc m ks)` in one transient pass, since `apply dissoc` copies a full HAMT path
  per key and `ks` is the whole swept region of a retraction.  Public because
  `vaelii.impl.dense-jtms` drops a swept region from its `superseded` map through it
  (docs/density.md)."
  [m ks]
  (if (seq ks) (persistent! (reduce dissoc! (transient (or m {})) ks)) (or m {})))

(defn- disj-all
  "`(apply disj s ks)` in one transient pass, for the same reason as `dissoc-all`."
  [st ks]
  (if (seq ks) (persistent! (reduce disj! (transient (or st #{})) ks)) (or st #{})))

(defn- unlink-just
  "`state` without justification `jid`: out of `:justs`, off its consequence's
  `:supports` and off every `:consequences` it was listed under.  No relabel."
  [state jid]
  (let [{:keys [consequence] :as j} (get-in state [:justs jid])]
    (-> state
        (update :justs dissoc jid)
        (update-in [:nodes consequence :supports] #(disj (or % #{}) jid))
        (as-> s (reduce-rests-on (fn [s2 a]
                                   (update-in s2 [:nodes a :consequences]
                                              #(disj (or % #{}) jid)))
                                 s j)))))

(defn- redepth*
  "`state` with the depths re-solved over the consequence closure of those `seeds` still
  in the graph: the nodes that lost a premise mark or a justification, whose depth can
  rise.  No seed left, no walk."
  [state seeds]
  (let [nodes (:nodes state)
        live  (filterv #(contains? nodes %) seeds)]
    (if (empty? live)
      state
      (let [justs (:justs state)]
        (reduce-kv (fn [s d v] (assoc-in s [:nodes d :depth] v))
                   state
                   (region-depths (affected-region state live)
                                  #(get-in nodes [% :premise?])
                                  #(get-in nodes [% :supports])
                                  #(get-in nodes [% :consequences])
                                  #(get-in justs [% :antecedents])
                                  #(get-in justs [% :consequence])
                                  #(get-in nodes [% :depth] 0)))))))

(defn- sweep*
  "Collect the datums in `suspects` that are no longer derivable (OUT) and not premises,
  delete them and every justification touching them, and return `[new-state {:removed-sentexes
  [datum...] :removed-justifications [jid...] :removed-supports [[consequence informant]...]}]`;
  the map is absent when nothing was removed.  A survivor that lost a justification, and each
  of `raised`, has its depth re-solved (`redepth*`).  The caller must have relabelled
  `suspects`: this reads `:in`.  Region-local: justifications are read off the dead nodes'
  `:supports` / `:consequences`.  This is also the collector for an excepted conclusion
  (docs/exceptions.md, \"Garbage collection, not defeat\")."
  [state suspects raised]
  (let [in       (:in state #{})
        dead     (filter (fn [d]
                           (and (not (get-in state [:nodes d :premise?]))
                                (not (contains? in d))))
                         suspects)
        ;; The justifications touching a dead datum are the ones its node names: `:supports` and
        ;; `:consequences`.  Reading them keeps the sweep proportional to the region (docs/nmtms.md).
        dead-jids (into #{}
                        (comp (mapcat (fn [d] (concat (get-in state [:nodes d :supports] #{})
                                                      (get-in state [:nodes d :consequences] #{}))))
                              ;; an adjacency set names a justification; only a live one
                              ;; is ours to remove or to report
                              (filter #(contains? (:justs state) %)))
                        dead)
        removed-justifications (remove #(= :premise (get-in state [:justs % :informant])) dead-jids)
        removed-supports (mapv #(let [j (get-in state [:justs %])] [(:consequence j) (:informant j)])
                               removed-justifications)
        ;; the swept datums, as handles; the caller fetches each record from the store before deleting it,
        ;; so the network holds no second copy.
        removed-sentexes   (vec dead)
        ;; the survivors among these lost a justification
        lost  (keep #(get-in state [:justs % :consequence]) dead-jids)
        ;; 5. apply removals to the graph
        state (reduce unlink-just state dead-jids)
        state (update state :nodes dissoc-all dead)
        state (update state :classes dissoc-all dead)
        ;; a block names a justification, so a swept justification must lose its
        ;; block too — an id left behind would be a stale block waiting to be
        ;; reapplied to whatever reuses it
        state (update state :blocked disj-all dead-jids)
        ;; ...and a forced membership names a justification or a datum, for the same reason
        state (-> state
                  (update-in [:forced :void] disj-all dead-jids)
                  (update-in [:forced :mono] disj-all dead)
                  (update-in [:forced :out] disj-all dead)
                  (update-in [:forced :held] disj-all dead))
        ;; a supersession names a datum, so a swept datum must lose it too — an entry
        ;; left behind would hold a future handle OUT for a merge that is long gone
        state (update state :superseded dissoc-all dead)
        ;; the swept nodes were OUT, so dropping them cannot move any survivor's label —
        ;; only the bookkeeping set needs the removal
        state (update state :in disj-all dead)
        state (redepth* state (into (vec raised) lost))]
    [state (cond-> {:removed-sentexes removed-sentexes
                    :removed-justifications removed-justifications}
             (seq removed-supports) (assoc :removed-supports removed-supports))]))

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
    (sweep* state suspects [datum])))

(defn- drop-just*
  "Return [new-state removals] with justification `jid` gone: unlinked, unblocked, its
  consequence's region relabelled and then swept, so a conclusion it alone grounded
  leaves with it.  `jid` itself is not among the reported removals — the caller asked
  for it by name, and is listed only in `:removed-supports`.  An unknown `jid` is a no-op."
  [state jid]
  (if-let [c (get-in state [:justs jid :consequence])]
    (let [inf      (get-in state [:justs jid :informant])
          state    (-> state
                       (unlink-just jid)
                       (update :blocked disj-all [jid])
                       (update-in [:forced :void] disj-all [jid]))
          suspects (affected-region state [c])
          [state r] (sweep* (relabel-region* state suspects) suspects [c])]
      [state (update r :removed-supports (fnil conj []) [c inf])])
    [state {:removed-sentexes [] :removed-justifications []}]))

(defn- suspend-premise*
  [state datum]
  (if-not (get-in state [:nodes datum])
    state
    (let [state (-> state
                    (assoc-in [:nodes datum :premise?] false)
                    (update-in [:nodes datum] dissoc :premise-strength))]
      (-> (relabel-region* state (affected-region state [datum]))
          (redepth* [datum])))))

(defn- retract*
  "Return [new-state {:removed-sentexes [datum...] :removed-justifications [jid...]}].

  An unknown datum is a no-op: retraction is idempotent, and the test is what keeps it
  so.  Reaching `retract-known*` regardless would have `assoc-in` *create* the node it
  was asked to retract; the sweep then collects the phantom (not a premise, not
  IN) and the result claims a removal that never happened."
  [state datum]
  (if-not (get-in state [:nodes datum])
    [state {:removed-sentexes [] :removed-justifications []}]
    (retract-known* state datum)))

(defn- set-blocked*
  [state jids]
  (let [jids    (into #{} (filter #(contains? (:justs state) %)) jids)
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

(defn- set-forced*
  "`state` with each of `xs` added to forced set `kind` (`on?`) or taken out of it, and
  the region of the members that moved relabelled: the datums with a node for `:mono`
  and `:out`, the consequences of the stored justifications for `:void`.  A `:held` move
  relabels nothing: the members that are IN are recorded in the touched sets as a relabel
  records them, in `touched-in` when one was believed before, and in `touched-out` when
  one leaves belief."
  [state kind xs on?]
  (let [cur   (forced-set state kind)
        moved (into [] (comp (distinct) (filter #(not= (boolean on?) (contains? cur %)))) xs)]
    (cond
      (empty? moved)
      state

      (= :held kind)
      (let [live (filterv #(contains? (:in state #{}) %) moved)
            t    (:touched state #{})]
        (-> state
            (assoc-in [:forced kind] (if on? (into cur moved) (disj-all cur moved)))
            (update :touched (fnil into #{}) live)
            (note-epoch live)
            (update :touched-in (fnil into #{}) (when on? (remove #(contains? t %) live)))
            (update :touched-out (fnil into #{}) (when on? live))))

      :else
      (let [region (affected-region state (if (= :void kind)
                                            (keep #(get-in state [:justs % :consequence]) moved)
                                            (filter #(get-in state [:nodes %]) moved)))
            was    (filterv #(contains? (:in state #{}) %) region)
            state  (-> state
                       (assoc-in [:forced kind] (if on? (into cur moved) (disj-all cur moved)))
                       (relabel-region* region))]
        ;; what the change took OUT, for `revived` to re-seed if it comes back before the reset
        (update state :touched-out (fnil into #{}) (remove #(contains? (:in state) %)) was)))))

(defn- unbelieved-fn
  "`(fn [datum])`: is an IN datum of `state` kept from belief, superseded or `:held`?
  The supersession map itself when nothing is held."
  [state]
  (let [sup  (:superseded state {})
        held (forced-set state :held)]
    (if (empty? held) sup #(or (contains? sup %) (contains? held %)))))

(defn- swap-with-result!
  "Atomically apply `f`, a pure `state -> [state' result]` fn, to atom `a`, retrying as
  `swap!` does, and return the result.  Not deref-then-`reset!`, which discards a concurrent
  `swap!`.  This makes concurrent operations compose and does not make them serializable: the
  engine's contract is one writer (docs/storage.md)."
  [a f]
  (loop []
    (let [old @a
          [new result] (f old)]
      (if (compare-and-set! a old new)
        result
        (recur)))))

;; ---- the representation protocol --------------------------------------------
;; The `Tms` protocol lives in `vaelii.impl.jtms-protocol`; this reference network and
;; `vaelii.impl.dense-jtms` sit behind it.  Its methods are `:refer`red above, and the public facade
;; is at the foot of this file.

;; ---- the reference implementation: one atom, one persistent map ---------

(defn- ref-state
  "The state map a `RefTms` read answers from, given its `hold` and `state` fields: the map
  the open hold took when it opened, for a thread other than its owner that
  `observe/reads-held-in?` says reads it, and otherwise the live map.

  A live read takes the registry before and after the map, and reads again when a hold
  opened or closed in between: a settle mutates the network only while its hold is open,
  so a map read with no hold open on either side is one no settle was deciding."
  [^AtomicReference hold ^clojure.lang.Atom state]
  (let [st (.get hold)]
    (if (and st (identical? (:owner (:hold st)) (Thread/currentThread)))
      @state
      (loop []
        (let [m  (observe/registry)
              st (.get hold)]
          (if (and st (observe/reads-held-in? m (:hold st)))
            (:state st)
            (let [s @state]
              (if (identical? m (observe/registry)) s (recur)))))))))

(deftype RefTms [^clojure.lang.Atom state ^AtomicReference hold]
  ;; `@tms` yields the live state map, which the JTMS tests and RAM benches read.  `hold` is nil or
  ;; `{:hold h :state s}` while hold `h` is open: every read answers from `s`, the state map at open,
  ;; to a thread that reads `h`'s belief.
  clojure.lang.IDeref
  (deref [_] @state)
  Tms
  (-believed? [_ datum]
    (let [s (ref-state hold state)]
      (and (contains? (:in s #{}) datum)
           (not (contains? (:superseded s {}) datum))
           (let [held (forced-set s :held)] (or (empty? held) (not (contains? held datum)))))))
  (-believed [_] (let [s (ref-state hold state)] (seq (remove (unbelieved-fn s) (:in s #{})))))
  (-any-node?   [_] (boolean (seq (:nodes (ref-state hold state)))))
  (-any-belief? [_] (let [s (ref-state hold state)]
                      (boolean (first (remove (unbelieved-fn s) (:in s #{}))))))
  (-node? [_ datum] (contains? (:nodes (ref-state hold state)) datum))
  (-datums [_] (keys (:nodes (ref-state hold state))))
  (-depth [_ datum] (get-in (ref-state hold state) [:nodes datum :depth] 0))
  (-premise? [_ datum] (boolean (get-in (ref-state hold state) [:nodes datum :premise?])))
  (-premise-strength [_ datum] (get-in (ref-state hold state) [:nodes datum :premise-strength]))
  (-defeat-class [_ datum]
    (let [s (ref-state hold state)]
      (when (contains? (:in s) datum) (get (:classes s) datum :default))))
  (-blocked [_] (:blocked (ref-state hold state) #{}))
  (-superseded [_] (:superseded (ref-state hold state) {}))
  (-touched [_] (:touched @state #{}))
  (-touched-in [_] (:touched-in @state #{}))
  (-touched-new [_] (:touched-new @state #{}))
  (-touched-out [_] (:touched-out @state #{}))
  (-reset-touched [_]
    (swap! state #(-> %
                      (assoc :touched #{} :touched-in #{} :touched-new #{} :touched-out #{})
                      (update :marks (fn [m] {:gen (inc (:gen m 0)) :epochs []}))))
    nil)
  (-touch-mark [_]
    ;; an empty open epoch is shared, as the dense network shares it
    (let [m (:marks (swap! state update :marks
                           (fn [m] (let [m (or m {:gen 0 :epochs []})
                                         e (peek (:epochs m))]
                                     (if (and e (empty? e)) m (update m :epochs conj #{}))))))]
      [(:gen m) (dec (count (:epochs m)))]))
  (-touched-since [_ mark]
    (let [st @state
          {:keys [gen epochs]} (:marks st)
          [g i] mark]
      (if (and mark (= g gen) (< i (count epochs)))
        (into #{} cat (subvec epochs i))
        (:touched st #{}))))
  (-supports [_ datum] (get-in (ref-state hold state) [:nodes datum :supports] #{}))
  (-dependents [_ datum] (get-in (ref-state hold state) [:nodes datum :consequences] #{}))
  (-justification [_ jid] (get-in (ref-state hold state) [:justs jid]))
  (-justifications [_] (vals (:justs (ref-state hold state))))
  (-ensure-node [_ datum depth]
    ;; skip the swap when it would write back a value-identical map (a node already present at a depth
    ;; no higher than `depth`); most calls are that no-op.  Sound under the single-writer contract.
    (let [n (when observe/*chain-fast-paths* (get (:nodes @state) datum))]
      (when (or (nil? n) (< (long depth) (long (:depth n 0))))
        (swap! state ensure* datum depth)))
    nil)
  (-add-premise [_ datum strength] (swap! state premise* datum strength) nil)
  (-suspend-premise [_ datum] (swap! state suspend-premise* datum) nil)
  (-add-justification [_ just] (swap! state add-just* just) nil)
  (-restrength-informant [_ informant strength]
    (swap! state restrength-informant* informant strength) nil)
  (-forced? [_ kind x] (contains? (forced-set (ref-state hold state) kind) x))
  (-forced-members [_ kind] (forced-set (ref-state hold state) kind))
  (-set-forced [_ kind xs on?] (swap! state set-forced* kind xs on?) nil)
  (-relabel [_] (swap! state relabel-all*) nil)
  (-set-blocked [_ jids] (swap! state set-blocked* jids) nil)
  (-supersede [_ m] (swap! state assoc :superseded (if (map? m) m (into {} m))) nil)
  (-retract [_ datum] (swap-with-result! state #(retract* % datum)))
  (-sweep [_ seeds] (swap-with-result! state (fn [s] (sweep* s (affected-region s seeds) nil))))
  (-drop-justification [_ jid] (swap-with-result! state #(drop-just* % jid)))
  (-snapshot [_] (dissoc @state :marks))
  (-hold [_ h]
    ;; the writer is the one thread that swaps `state`, so the map read here is the one
    ;; every relabel after this call starts from
    (.compareAndSet hold nil {:hold h :state @state}))
  (-release [_ h]
    (let [st (.get hold)]
      (when (identical? h (:hold st)) (.compareAndSet hold st nil)))
    nil)
  (-held [_] (:hold (.get hold))))

(defn create-tms
  "A fresh, empty truth-maintenance network, the reference implementation.  `:in` is the
  believed set and the authority on belief, maintained region-locally; nodes carry no label of
  their own.  `:blocked` is the set of justification ids blocked by their rule's exception; it
  starts empty.  Rules live in the stores as sentexes, not here."
  []
  (let [state (atom {:nodes {} :justs {} :blocked #{} :superseded {}
                     :forced {:mono #{} :out #{} :void #{} :held #{}}
                     :classes {} :in #{}
                     :touched #{} :touched-in #{} :touched-new #{} :touched-out #{}})
        tms   (->RefTms state (AtomicReference. nil))]
    ;; the state map a swap replaces is the open write record's value for this network,
    ;; the first time a swap since the record opened replaces one (`before-network`)
    (add-watch state ::write-record
               (fn [_ _ old _] (when observe/*write-record* (observe/record-of tms (constantly old)))))
    tms))

(defn before-network
  "A reference network `tms` as it stood when the open write record first recorded it,
  as a network over that state map, or `tms` itself when the record holds none or `tms`
  is not a reference network."
  [tms]
  (if-let [s (and (instance? RefTms tms) (observe/recorded tms))]
    (->RefTms (atom s) (AtomicReference. nil))
    tms))

;; ---- public API ---------------------------------------------------------
;;
;; Thin dispatch onto the protocol.  Every engine path calls these, never a protocol method, so the
;; representation a KB was opened with is invisible above this line.

(defn in?
  "Is `datum` believed?  Structural support minus supersession and the `:held` forced
  set: a datum the equality layer has displaced, or a rule a correspondence holds
  (docs/nat.md), keeps its place in the fixpoint (a twin or a respelled row is justified
  by it) but is not believed, so it stops matching and stops answering queries."
  [tms datum] (-believed? tms datum))

(defn raw-in?
  "Is `datum` believed, or kept from belief with its label IN: superseded, or a member of
  the `:held` forced set?  The label a boundary datum of a region read takes, since the
  fixpoint keeps both kinds IN."
  [tms datum]
  (or (-believed? tms datum)
      (contains? (-superseded tms) datum)
      (-forced? tms :held datum)))

(defn network-in?
  "Is `datum` IN in the network, a superseded spelling included?  The families
  `chain/place-nogoods!` places detect their nogoods over this label, so a nogood with a
  superseded member keeps its placement (docs/nmtms.md)."
  [tms datum] (some? (-defeat-class tms datum)))

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

(defn unsupported?
  "Does the network hold a node for `datum` that is no premise and that no justification
  concludes?"
  [tms datum]
  (and (-node? tms datum) (not (-premise? tms datum)) (empty? (-supports tms datum))))

(defn defeat-class
  "The current defeat-class of an IN datum (monotonic / default), or nil
  when the datum is OUT.  Valid after `relabel`.

  `:classes` holds only the datums *above* the lattice's bottom, so IN-ness is what
  separates \"OUT, hence no class\" from \"IN at the default class\".  An entry's mere
  presence cannot carry both, since only one of them is information."
  [tms datum] (-defeat-class tms datum))

(defn touched
  "The datums whose region has been relabelled since the last `reset-touched!`: a superset of
  every datum whose belief could have flipped.  `settle` reads it to tell `tax/refresh-beliefs`
  which handles moved.  It also holds the datums a redundant justification landed on, whose
  belief did not move but whose published answer may be stale (`add-just*`).  Consumers read a
  superset, so an extra handle costs a re-derivation and never an answer."
  [tms] (-touched tms))

(defn touched-in
  "The subset of `touched` whose label was IN when a relabel since the reset first reached it.
  With `touched` and current belief it gives the label delta: IN now but not here came in; here
  and OUT now went out.  A superseded spelling keeps an IN label and is not believed (`in?`),
  so `settle-finish` drops the spellings superseded when the settle began.  A datum relabelled
  twice keeps the earlier answer."
  [tms] (-touched-in tms))

(defn touched-new
  "The datums whose **node was created since the last reset** — the ones that had no label to move
  because they had no node.  `touched-in` cannot say this: a brand-new datum and a
  stored one that has been OUT since the settle before both read as \"not believed at
  the last reset\", and they are the two halves `revived` has to keep apart."
  [tms] (-touched-new tms))

(defn revived
  "The datums brought back since the last reset: relabelled, believed now, not believed at the
  reset, and already in the graph at the reset.  A revival is the one belief move nothing
  downstream has seen (no arrival to chain from, no justification to withdraw), so `settle`
  re-seeds these onto the agenda.  It is `touched` minus `touched-in` and `touched-new`, plus
  the `-touched-out` datums believed again.  The two-arity takes `touched` as the caller
  already read it, since the dense network materializes a fresh set per read.
  See docs/nmtms.md."
  ([tms] (revived tms (touched tms)))
  ([tms t]
   (if (empty? t)
     #{}
     (let [was-in (touched-in tms)
           born   (touched-new tms)]
       (-> #{}
           (into (comp (remove was-in) (remove born) (filter #(in? tms %))) t)
           (into (filter #(in? tms %)) (-touched-out tms)))))))

(defn reset-touched!
  "Clear the accumulated touched sets (see `touched` / `touched-in` / `touched-new`).
  `settle` clears them once it has read them, at the *end* — so the touched set a caller sees
  spans everything since the last settle finished, which for `edit` is the whole
  deferred batch and its one settle rather than the settle alone."
  [tms] (-reset-touched tms) tms)

(defn touch-mark
  "A mark of this point in the touched set, for a reader that asks the touched set more
  than once between resets: `touched-since` answers what was recorded after it.  Each reader keeps
  its own mark."
  [tms] (-touch-mark tms))

(defn touch-mark-if-kept
  "`touch-mark` of `tms`, or nil for a network that keeps no marks (`kb/prior-kb`'s, whose
  frames are kept by reading every watched label)."
  [tms]
  (try (touch-mark tms) (catch UnsupportedOperationException _ nil)))

(defn touched-since
  "The datums `touched` recorded after `mark` (`touch-mark`): a datum relabelled again
  since the mark is in it although `touched` held it already, which a set difference over
  `touched` would drop.  A superset of what moved since the mark, as `touched` is of what
  moved since the reset.  The whole of `touched` for a mark the reset outdated
  (`reset-touched!`) or a nil one."
  [tms mark] (-touched-since tms mark))

(defn superseded
  "The `datum -> reason` map of spellings an equality merge has displaced."
  [tms] (-superseded tms))

(defn superseded? [tms datum] (contains? (-superseded tms) datum))

(defn supersession
  "Why `datum` is superseded — the representative that displaced it — or nil."
  [tms datum] (get (-superseded tms) datum))

(defn supersede
  "**Replace** the superseded map with `m` (`{datum reason}`), as `set-blocked` replaces:
  the caller reconciles the whole answer (`special/refresh-supersessions`).  No relabel:
  supersession only subtracts from what `in?` reports."
  [tms m] (moving (-supersede tms m)) tms)

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
  "Do `a` and `b` name the same antecedents as sets (members the same, order and duplicates
  immaterial)?  Mutual containment, which allocates nothing where `(= (set a) (set b))` builds
  two hash sets.  It runs Θ(k^2) times per conclusion re-derived by k witnesses (7.7M
  comparisons on the W4 join pyramid).  An antecedent list is two to five handles, and a
  mismatch ends at the first member `b` lacks."
  [a b]
  (let [av (indexed a) na (count a)
        bv (indexed b) nb (count b)]
    (and (covered? av na bv nb)
         (covered? bv nb av na))))

(def ^:dynamic *dedup-cache*
  "`{:tms tms :m HashMap-of-consequence->HashSet-of-just-keys}`, or nil (default): then
  `has-justification?` scans `-supports`.  A run-scoped index bound by `chain/chain` and
  `chain/place-nogoods!`; the first ask per conclusion builds its key set, later asks probe
  it.  The binding carries its TMS and `dedup-cache-for` hands the map only to that TMS,
  since a nested run over a second KB has overlapping handle spaces.  Existence is
  structural, so only a removal (`retract!`, `sweep!`) invalidates, and both clear the
  cache; `add-justification` extends the entry.  See docs/inference.md, Justification dedup."
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

;; Both key shapes normalize fixnum boxing to Long: the HashMap/HashSet compare with Java equals
;; (Integer 7 is not Long 7) and the reference scan compares with `=`.
(defn- unbox ^Object [x] (if (int? x) (long x) x))

(defn- just-key
  "The content `has-justification?` deduplicates on — the informant, the antecedents
  **as a set**, `same-antecedents?`'s judgement (order and duplicates immaterial) frozen
  into one hashable value, and the subsumptions.  A rule-handle informant is dropped
  from the set: a stored record never lists it there, and a firing's handle list does.
  Two firings that pair the same facts with different literals can rest on one
  antecedent set, and the subsumptions keep them two (`late_route_test`). Optional
  source readings remain correlated alternatives, never a union of exemptions. The
  ordinary nil-reading key retains its three-element shape."
  ([informant antecedents subsumptions]
   (just-key informant antecedents subsumptions nil))
  ([informant antecedents subsumptions reading]
   (let [inf (unbox informant)
         s   (set antecedents)]
     (cond-> [inf (if (integer? inf) (disj s inf) s) (not-empty subsumptions)]
       (seq reading) (conj reading)))))

(defn- dedup-keys
  "The cached key set for `consequence`, built from its supports on the first ask."
  ^java.util.HashSet [tms ^java.util.Map cache consequence]
  (let [ck (unbox consequence)]
    (or (.get cache ck)
        (let [s (java.util.HashSet.)]
          (doseq [jid (-supports tms consequence)]
            (when-let [j (-justification tms jid)]
              (.add s (just-key (:informant j) (:antecedents j) (:subsumptions j) (:reading j)))))
          (.put cache ck s)
          s))))

(defn justification-key
  "The dedup key of a justification from `informant` over `antecedents` with
  `subsumptions`, a set or nil — `just-key`, for a caller that asks
  `has-justification?` and then adds the justification, and so would otherwise build the
  same set twice."
  ([informant antecedents] (just-key informant antecedents nil))
  ([informant antecedents subsumptions] (just-key informant antecedents subsumptions))
  ([informant antecedents subsumptions reading] (just-key informant antecedents subsumptions reading)))

(defn has-justification?
  "Is there already a support for `consequence` from `informant` over exactly these
  antecedents (as a set), with the same subsumptions?  Guards against duplicate
  justifications.  Answered from the dedup index when one is bound for this TMS — the
  same judgement, one hash probe — and by the supports scan otherwise.  `k`, when given,
  is `justification-key` of the same informant and antecedents, and carries the
  subsumptions; without it the question is about a justification with none."
  ([tms informant antecedents consequence]
   (has-justification? tms informant antecedents consequence nil))
  ([tms informant antecedents consequence k]
   (if-let [^java.util.Map cache (dedup-cache-for tms)]
     (.contains (dedup-keys tms cache consequence) (or k (just-key informant antecedents nil)))
     (let [antes (without-informant informant antecedents)
           subs  (when k (nth k 2))
           reading (when k (nth k 3 nil))]
       (boolean
        (some (fn [jid]
                (let [j (-justification tms jid)]
                  (and (= informant (:informant j))
                       (= subs (:subsumptions j))
                       (= reading (:reading j))
                       (same-antecedents? antes (:antecedents j)))))
              (-supports tms consequence)))))))

;; Every mutating entry point below wraps its mutation in `moving`, and notes the handles whose
;; support it moved while a write record is open (`moved-supports`).

(def ^:dynamic *support-observer*
  "Optional queue-only support listener frames: :tms, :active?, :note, :previous.
  The first identical network owns an event; nested writes on another network cannot
  observe a hypothetical network or deliver the same event twice. No write report is opened."
  nil)

(defn- support-observer
  "The active listener belonging to this exact network, never a read-copy network."
  [tms]
  (loop [frame *support-observer*]
    (when frame
      (if (identical? tms (:tms frame))
        (when ((:active? frame)) frame)
        (recur (:previous frame))))))

(defn- note-moved!
  "Record touched `hs` for an optional write report, and notify the listener of
  `changed` (default `hs`). Listener no-op filtering leaves report touches unchanged;
  a listener-only event can pass no report handles."
  ([tms hs] (note-moved! tms hs false hs))
  ([tms hs departing?] (note-moved! tms hs departing? hs))
  ([tms hs departing? changed]
   (when (seq changed)
     (when-let [frame (support-observer tms)] ((:note frame) changed departing?)))
   (when (and observe/*write-record* (seq hs))
     (let [^java.util.Map m (observe/record-of ::moved #(java.util.IdentityHashMap.))
           ^java.util.Set s (or (.get m tms) (let [s (java.util.HashSet.)] (.put m tms s) s))]
       (run! #(.add s %) hs)))))

(defn moved-supports
  "The handles whose premise mark, justifications, or forced or blocked membership `tms`
  moved since the open write record opened, as a set, or nil."
  [tms]
  (some-> ^java.util.Map (observe/recorded ::moved) (.get tms) set))

(defn- note-removed!
  "Note the consequences of the supports a removal (`retract!`'s shape) took, and return
  the result."
  [tms result]
  (note-moved! tms (concat (map first (:removed-supports result)) (:removed-sentexes result)) true)
  result)

(defn ensure-node
  "Create `datum`'s node if absent, at `depth` or lower (`-ensure-node`).  A node already
  present at a depth no higher than `depth` is what the write would leave, so under
  `observe/*chain-fast-paths*` it moves neither the network nor the change clock."
  [tms datum depth]
  (when-not (and observe/*chain-fast-paths* (integer? datum) (-node? tms datum)
                 (<= (long (-depth tms datum)) (long depth)))
    (moving (-ensure-node tms datum depth)))
  datum)

(defn- note-route-gain
  "Hand `datum` to the bound `observe/*route-gain-sink*` when the sink mirrors `tms` and
  `datum` is believed and not a premise.  An `except` hides a premise only by naming it, so
  a route a premise gains shows it to no further reader."
  [tms datum]
  (when-let [{mirrors? :mirrors? note :note} observe/*route-gain-sink*]
    (when (and (mirrors? tms) (not (-premise? tms datum)) (in? tms datum))
      (note datum))))

(defn add-premise
  "Add `datum` as a premise at `strength` (default :default)."
  ([tms datum] (add-premise tms datum :default))
  ([tms datum strength-kw]
   (note-route-gain tms datum)
   (let [strength (or strength-kw :default)
         old (when (support-observer tms) (-premise-strength tms datum))]
     (moving (-add-premise tms datum strength))
     (note-moved! tms [datum] false (when (not= old strength) [datum])))
   datum))

(defn suspend-premise
  "Drop `datum`'s premise mark and relabel its region without sweeping: a retraction's
  effect on belief, undone by `add-premise` at the same strength.  Unknown datums no-op.
  Bare, not `!`: the node and its justifications stay.  `core/preview` is the caller
  (docs/nmtms.md)."
  [tms datum]
  (let [old (when (support-observer tms) (-premise-strength tms datum))]
    (moving (-suspend-premise tms datum))
    (note-moved! tms [datum] false (when old [datum])))
  datum)

(defn add-justification
  "Add `just` to the network.  `k`, when given, is its `justification-key`, already built
  for the `has-justification?` that guarded the add."
  ([tms just] (add-justification tms just nil))
  ([tms just k]
   (note-route-gain tms (:consequence just))
   (let [old (when (support-observer tms) (-justification tms (:id just)))]
     (moving (-add-justification tms just))
     (note-moved! tms [(:consequence just)] false
                  (when (not= old (graph-just just)) [(:consequence just)])))
   (when-let [^java.util.Set s observe/*fired-sink*]
     (when (integer? (:informant just)) (.add s (:consequence just))))
   ;; keep a bound dedup index in step: extend the one entry this justification lands
   ;; in, when that entry has been built (an absent entry rebuilds from `-supports`,
   ;; which now includes this justification, so absence needs nothing)
   (when-let [^java.util.Map cache (dedup-cache-for tms)]
     (when-let [^java.util.HashSet ks (.get cache (unbox (:consequence just)))]
       (.add ks (or k (just-key (:informant just) (:antecedents just) (:subsumptions just)
                               (:reading just))))))
   just))

(defn restrength-informant
  "Set `strength` as the rule-contribution slot of every justification whose informant is
  `informant`, and relabel the region their consequences span.  The slot caches
  `provers/firing-strength`, which moves when a re-asserted rule's defeasibility resolves or an
  `exceptWhen` arrives or leaves (`special/restrength-firings!`); without the move belief would
  keep the arrival order.  The antecedent half of `conferred-class` is read live, so this is the
  only stored copy.  The relabel spans the full affected region, since a class that rises can
  flip defeat decisions anywhere in the consumer ancestor set."
  [tms informant strength]
  (moving (-restrength-informant tms informant strength))
  tms)

(defn forced?
  "Is `x` a member of forced set `kind`?"
  [tms kind x] (-forced? tms kind x))

(defn forced-members
  "Every member of forced set `kind`, as a set."
  [tms kind] (-forced-members tms kind))

(defn set-forced
  "Add each of `xs` to forced set `kind` (`on?` true) or take it out, and relabel the
  region the members that moved reach.  `:mono` names premises whose class is
  `:monotonic` whatever strength they carry, `:out` datums never IN, `:void`
  justifications that support nothing, and `:held` datums the fixpoint labels as usual
  and `in?` never answers believed, so a `:held` move relabels nothing.  A member may be written before its node or its
  justification exists, so the element never holds a label the set rules out."
  [tms kind xs on?]
  (when (seq xs)
    (let [changed (when (support-observer tms)
                    (filterv #(not= (boolean on?) (boolean (-forced? tms kind %))) xs))
          datums (fn [xs] (if (= :void kind) (keep #(:consequence (-justification tms %)) xs) xs))]
      (moving (-set-forced tms kind xs on?))
      (note-moved! tms (datums xs) false (datums changed))))
  tms)

(defn premise-class
  "The class `datum`'s premise mark confers: `:monotonic` for a `:mono` member, its
  premise strength otherwise, nil for a datum that is no premise."
  [tms datum]
  (when-let [s (premise-strength tms datum)]
    (if (forced? tms :mono datum) :monotonic s)))

(defn relabel
  "Recompute every node's label and defeat-class, and clear the blocked and superseded sets
  (both derive from queries that are never stored): the whole-graph counterpart to the region
  relabels.  Nothing on the live paths calls it; it is the differential oracle's operation
  (`strength_test`, `jtms_dense_oracle_test`, `jtms_blocked_test`), so both representations
  implement it."
  [tms] (moving (-relabel tms)) tms)

(defn blocked
  "The justification ids currently blocked by their rule's exception."
  [tms] (-blocked tms))

(defn set-blocked
  "Replace the blocked set with `jids`, the justifications whose exception the caller found to
  hold, less any id the network holds no justification for, and relabel the region the change
  reaches.  The set is replaced and not accumulated, so belief cannot depend on the order the
  exceptions were discovered in.  The region is seeded from the consequences of the
  justifications whose blocked status changed; a call that changes nothing does no work."
  [tms jids]
  (let [old (when (or observe/*write-record* (support-observer tms)) (-blocked tms))]
    (moving (-set-blocked tms jids))
    (when old
      (let [new (set jids)]
        (note-moved! tms (keep #(:consequence (-justification tms %))
                               (concat (remove new old) (remove (set old) new)))))))
  tms)

(defn hold!
  "Open hold `h` (`observe/new-hold`) on `tms`, and answer whether it opened: false when a
  hold is open on it already.  Until `release!`, every relabel records the labels it moves
  as they were before the hold's first move, and once `observe/open-hold!` registers `h`, a
  thread other than its owner reads belief, the blocked and superseded sets, and
  on the reference every read, from those.  A settle holds its network this way, so a
  reader beside it reads the belief the settle began from until the settle publishes what
  it decided (`vaelii.impl.settle/settle`)."
  [tms h] (-hold tms h))

(defn release!
  "Close hold `h` on `tms`.  A no-op for a hold that is not the one open."
  [tms h] (-release tms h) nil)

(defn held
  "The hold open on `tms`, or nil."
  [tms] (-held tms))

(defn consequence-closure
  "The forward consequence closure of `seeds`, seeds included: every datum a justification
  resting on one of them concludes, transitively.  The region `grounded-in-region` labels,
  for a caller that needs the datums a forced-OUT set can move and not their labels."
  [tms seeds]
  (loop [seen #{}, stack (vec seeds)]
    (if (empty? stack)
      seen
      (let [d (peek stack), stack (pop stack)]
        (if (contains? seen d)
          (recur seen stack)
          (recur (conj seen d)
                 (into stack (comp (keep #(justification tms %)) (map :consequence))
                       (dependents tms d))))))))

(defn region-valid-fn
  "`(fn [in j])`: is the justification `j` valid with `in` the believed datums of
  `region`, the read `region-in` makes of each justification.  An antecedent or rule
  handle in `region` is believed when `in` holds it, one outside at its live label, and
  one `belief-only` names for `j` (a handle or a set) at its label wherever it lies.  `j`
  is invalid when blocked, `:void` or named by `invalid`."
  [tms region belief-only invalid]
  (let [blocked-set (blocked tms)
        ;; raw belief for a boundary datum: reported belief plus the superseded spellings
        ;; and held rules the fixpoint keeps IN (a twin or a respelled row rests on them)
        raw-in?     #(raw-in? tms %)
        ;; an antecedent in the region reads the recomputed set; outside it, live belief
        believed?*  (fn [in d] (if (contains? region d) (contains? in d) (raw-in? d)))]
    (fn [in j] (and (if-let [b (and belief-only (belief-only j))]
                      (let [label? (if (set? b) b #{b})]
                        (every? #(if (label? %) (raw-in? %) (believed?* in %))
                                (:antecedents j)))
                      (every? #(believed?* in %) (:antecedents j)))
                    (let [inf (:informant j)]
                      (or (not (integer? inf)) (believed?* in inf)))
                    (not (contains? blocked-set (:id j)))
                    (not (contains? invalid (:id j)))
                    (not (forced? tms :void (:id j)))))))

(defn region-in
  "The datums of `scope`, a part of `region` closed forward within it, that stay believed
  with `extra` forced OUT and `invalid` (justification ids) read as invalid, every datum of
  `region` outside `scope` read at its label in `base` and every datum outside `region`
  at its live one, added to `base`: `grounded-in-region*`'s fixpoint over `scope`, each
  justification read by `region-valid-fn`."
  [tms region scope base extra belief-only invalid]
  (let [out?        #(or (contains? extra %) (forced? tms :out %))
        just-of     #(justification tms %)
        valid-here? (region-valid-fn tms region belief-only invalid)
        ;; scope premises seed the fixpoint unless forced out
        seed        (into base (filter #(and (premise? tms %) (not (out? %)))) scope)
        ;; the justifications that can conclude something in the scope: a premise is
        ;; seeded or forced OUT, so none of its own is read
        cands       (into [] (comp (remove #(premise? tms %)) (mapcat #(supports tms %)) (distinct)
                                   (keep just-of))
                          scope)
        ;; those resting on each handle, which a handle concluded IN queues again: its
        ;; other dependents conclude outside the scope, and a handle of a support read
        ;; at a reader can have far more of them than the support has handles
        waiting     (persistent! (reduce (fn [m j] (reduce-rests-on #(assoc! %1 %2 (conj (get %1 %2 []) j)) m j))
                                         (transient {}) cands))]
    (loop [in seed, stack cands]
      (if (empty? stack)
        in
        (let [j (peek stack), stack (pop stack), c (:consequence j)]
          (if (and (contains? scope c)
                   (not (contains? in c))
                   (not (out? c))
                   (valid-here? in j))
            (recur (conj in c) (into stack (get waiting c)))
            (recur in stack)))))))

(defn- invalid-seeds
  "The conclusions of the justifications `invalid` names."
  [tms invalid]
  (into #{} (keep #(:consequence (justification tms %))) invalid))

(defn- grounded-in-region*
  [tms extra belief-only invalid]
  (let [extra   (set extra)
        invalid (set invalid)
        ;; the only datums a forced-out member or an invalid justification can move
        region  (consequence-closure tms (into extra (invalid-seeds tms invalid)))]
    {:region region :in (region-in tms region region #{} extra belief-only invalid)}))

(defn grounded-in-region
  "For `extra` (datums to force OUT): the forward consequence closure of `extra` (`:region`)
  and, within it, the datums that stay believed once `extra` is disbelieved (`:in`), the rest of
  the graph held at its current label.  Region-local: belief outside the region is read per
  datum from `in?`, which keeps `classify-local` linear in the number of dilemmas
  (`grounded_in_region_test`).  Built on the protocol reads, so both representations answer it
  without a method.  `belief-only` maps a justification to the antecedent(s) read at the current
  label (`exc/belief-only-antecedent`); `invalid` is a set of justification ids read as invalid.
  See docs/labeling.md."
  ([tms extra] (grounded-in-region* tms extra nil nil))
  ([tms extra belief-only] (grounded-in-region* tms extra belief-only nil))
  ([tms extra belief-only invalid] (grounded-in-region* tms extra belief-only invalid)))

(defn classes-in-region
  "The defeat-classes of the datums `in` holds inside `region`, where `region` and `in` are a
  `grounded-in-region` answer: the classes belief carries with that answer's `extra` forced
  OUT, the rest of the graph held at its current classes.  The same least fixpoint
  `region-classes` computes during a relabel, built on the protocol reads.  The settle reads it
  for a nogood weighed at a vantage (docs/nmtms.md, \"A defeat is scoped to its vantage\")."
  [tms region in]
  (let [blocked-set (blocked tms)
        members     (filterv #(contains? in %) region)
        believed?*  (fn [d] (if (contains? region d)
                              (contains? in d)
                              (raw-in? tms d)))
        class-of    (fn [classes d] (if (contains? region d)
                                      (get classes d :default)
                                      (or (defeat-class tms d) :default)))
        node-class  (fn [classes d]
                      (let [prem (when (premise? tms d) (or (premise-class tms d) :default))
                            strs (for [jid  (supports tms d)
                                       :let [j (justification tms jid)]
                                       :when (and j
                                                  (every? believed?* (:antecedents j))
                                                  (let [inf (:informant j)]
                                                    (or (not (integer? inf)) (believed?* inf)))
                                                  (not (contains? blocked-set (:id j)))
                                                  (not (forced? tms :void (:id j))))]
                                   (cond-> (reduce (fn [c a] (strength/min c (class-of classes a)))
                                                   (or (:strength j) :monotonic)
                                                   (class-antecedents j))
                                     (let [inf (:informant j)] (and (integer? inf) (not (premise? tms inf))))
                                     (strength/min (class-of classes (:informant j)))))]
                        (reduce strength/max :default (remove nil? (cons prem strs)))))]
    (loop [classes (zipmap members (repeat :default))]
      (let [next (reduce (fn [m d] (assoc m d (node-class classes d))) classes members)]
        (if (= next classes) classes (recur next))))))

(defn retract!
  "Dependency-directed retraction (drop premise / relabel / sweep).  Returns
  {:removed-sentexes [datum...] :removed-justifications [jid...]
  :removed-supports [[consequence informant]...]}, the last absent when no justification
  went; a caller deletes the records and the justifications, and reads the supports
  without a justification fetch.  Unknown datums no-op (empty result): retraction is
  idempotent."
  [tms datum]
  ;; the one path besides `sweep!` that removes justifications — a bound dedup index
  ;; over this TMS is cleared wholesale rather than edited (see `*dedup-cache*`)
  (let [old (when (support-observer tms) (-premise-strength tms datum))
        result (note-removed! tms (moving (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
                                          (-retract tms datum)))]
    ;; A premise can leave while another support keeps the datum IN and no sweep
    ;; removes anything. Its independent-demand authority still changed.
    (note-moved! tms nil true (when old [datum]))
    result))

(defn sweep!
  "Garbage-collect the consequence closure of `seeds`: every datum in it that is not a premise
  and is OUT is deleted with the justifications touching it.  Returns `retract!`'s shape, for
  the caller to apply to its own stores.  `retract!`'s sweep without the retraction, for
  `exceptWhen` (docs/exceptions.md, \"Garbage collection, not defeat\").  Labels must already be
  current (`set-blocked` relabels the same region)."
  [tms seeds]
  ;; removes justifications, so a bound dedup index over this TMS is cleared (see
  ;; `*dedup-cache*`)
  (note-removed! tms (moving (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
                             (-sweep tms seeds))))

(defn drop-justification!
  "Remove the one justification `jid` from the network, relabel the region it supported, and
  sweep what that leaves OUT.  Returns `retract!`'s shape; `jid`'s own record is the caller's
  to delete, and is listed only in `:removed-supports`.  The one removal that names a
  justification, for a permuting mark leaving: the firing still holds, at a spelling the store
  stopped folding into its row (`chain/reconcile-spellings!`)."
  [tms jid]
  ;; removes a justification, so a bound dedup index over this TMS is cleared (see
  ;; `*dedup-cache*`)
  (note-removed! tms (moving (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
                             (-drop-justification tms jid))))

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

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(defn- tms-of [kb] (:tms @(:reasoning kb)))

(caches/register-derived
 {:id :M1 :label "Labels" :kind :index :keyed-by :handle :reads [:justifications]
  :holds-content? false
  :retired-by {:relabelled :K :forced-monotonic :K :recover :R :image-install :R}
  :computed :write :imaged? :network :at [[:tms]]
  :value (fn [kb] (let [s (snapshot (tms-of kb))]
                    (assoc (select-keys s [:in :blocked :classes :forced :superseded])
                           :premises (into #{} (keep (fn [[d n]] (when (:premise? n) d)))
                                           (:nodes s)))))
  :note "IN, blocked, monotonic class, forced and superseded per handle; a mutation relabels its region inside `moving`"})

(caches/register-derived
 {:id :M2 :label "Touched set" :kind :journal :keyed-by :handle :reads [:M1]
  :holds-content? false
  :retired-by {:relabelled :K :forced-monotonic :K :settle-exit :W :recover :W}
  :computed :write :imaged? false :at [[:tms]]
  :value (fn [kb] (select-keys (snapshot (tms-of kb))
                               [:touched :touched-in :touched-new :touched-out]))
  :note "the handles relabelled since the last settle exit, with the reader marks into it; `reset-touched!` at the settle exit empties it and moves the mark generation"})

(caches/register-derived
 {:id :M3 :label "Belief hold" :kind :index :keyed-by :global :reads [:M1]
  :holds-content? false
  :retired-by {:held :K}
  :computed :settle :imaged? false :at [[:tms]]
  :value (fn [kb] (held (tms-of kb)))
  :note "the labels as they stood before a settle's first relabel, which other threads read until the settle publishes"})

(caches/register-derived
 {:id :M4 :label "Justification dedup" :cache :justification-dedup :kind :pass
  :holds-content? false
  :keyed-by :handle :reads [:justifications]
  :retired-by {:relabelled :W} :computed :pass :imaged? false :var #'*dedup-cache*
  :note "the justification keys each conclusion holds, bound for one chaining run; `retract!`, `sweep!` and `drop-justification!` clear it"})
