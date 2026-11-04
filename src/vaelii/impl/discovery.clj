;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.discovery
  "The detector of the one nogood family a settle finds: the clashes argument preservation
  infers between a stored claim and a known-true claim no one stored, each with the most
  general contexts that read it whole, where `chain/place-inherited!` places it.  The
  memo `:preserved-clashes` carries a clash whose inputs did not move.  See docs/nmtms.md,
  \"The inherited-clash memo\"."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:dynamic *whole-store-region?*
  "True while `recover` runs the settle that follows `rebuild-tms`, over the memo
  `recover` emptied.  Under it, the `preserving-entries` call whose memo holds no `:mark`
  asks the whole store's questions off the index and reads no region handle
  (docs/nmtms.md, \"The inherited-clash memo\")."
  false)

(def ^:dynamic *incremental-preserving*
  "True (the default): `preserving-nogoods` carries each standing inherited clash whose
  inputs did not move, and re-asks only the stored facts a moved claim reaches.  False:
  every call re-asks every standing clash and the whole stored extent of every predicate
  a claim moved, the reference `inherited_clash_oracle_test` compares the memo against."
  true)

(defn- flat-reading
  "`[reading moved]`: the flat caches as `kb` reads them, `{:pos :map}`, and the
  flat-cache keys whose supporting contexts moved since `prev`, an earlier reading.  `:pos`
  is the taxonomy's position in the journal `tax/flat-moves` reads, and `:map` the
  contexts map the discovery reads (`tax/flat-contexts`).  The moves are the journal's
  since `prev`'s position.  Where the journal does not reach back that far (an
  image install, a rebuild, a journal restarted past its bound) they are the keys the
  two maps differ on, and nil when `prev` holds no map."
  [kb prev]
  (let [tax         (reasoning/taxonomy kb)
        [pos moved] (tax/flat-moves tax (:pos prev))
        now         (tax/flat-contexts tax)
        was         (:map prev)]
    [{:pos pos :map now}
     (cond moved                       moved
           (identical? was now)        #{}
           (some? was)                 (-> #{}
                                           (into (keep (fn [[k cs]] (when-not (= cs (get was k)) k)))
                                                 now)
                                           (into (remove #(contains? now %)) (keys was))))]))

(defn- member-priority
  "The rebuttal-range priority of an inherited nogood: the highest defeat-class rank among
  `members`."
  [tms members]
  (reduce max (map #(strength/rank-of (jtms/defeat-class tms %)) members)))

(defn- inherited-nogoods
  "The nogood maps `{:nogood :priority :vantages :kind :sentence :inherited}` for stored
  claim `h`, stating `sen`, against the `inherit/clashing-claim` answers `cs`: one per
  member set, its `:vantages` the most general of the contexts that found it."
  [kb h sen cs]
  (let [tms (reasoning/tms kb)
        tax (reasoning/taxonomy kb)]
    (mapv (fn [[members hits]]
            (let [c     (first hits)
                  [a b] (sort nm/compare-form [(:sentence c) sen])
                  vs    (into #{} (map :context) hits)]
              {:nogood   members
               :priority (member-priority tms members)
               :vantages (if (next vs) (tax/max-cxs tax vs) vs)
               :kind     :inherited
               :sentence (list 'contradicts a b)
               ;; the claim nobody stored, where it was read, the general `:claim` it was
               ;; read from and the handles `:via` which it was carried
               :inherited {:sentence (:sentence c) :context (:context c)
                           :claim (:claim c) :via (vec (:handles c))}}))
          (group-by #(into #{h} (cons (:claim %) (:handles %))) cs))))

(defn- separated-membership?
  "Is `sen` a positive unary membership whose type the unscoped taxonomy separates from a
  preserved predicate (`inherit/separated-preserved`)?"
  [kb sen]
  (boolean (and (seq? sen) (= 2 (count sen)) (not= 'not (first sen))
                (seq (inherit/separated-preserved kb (first sen) '?ctx)))))

(defn- preserving-entry
  "`s`'s inherited clash, or nil: `{:pred :askers :reads :contexts :classes :class
  :nogoods}`.  The clashing claims are `inherit/clashing-claim`'s answers from `s`'s own
  context and from the vantages of each reading `inherit/denial-readings` names: the
  maximal common descendants of `s`'s context and the reading's where `s` and every
  handle of the reading are seen with no except hiding one
  (`res/exception-aware-placements`, the placement a firing takes).  `:askers` is every
  context asked, `:reads` `s` and every handle of the readings, `:contexts` the contexts
  they are stated in, `:classes` the defeat-class of every member but `s`, `:class` `s`'s
  own, `:nogoods` `inherited-nogoods`, and `:sep?` whether `s` is a membership of a type
  separated from a preserved predicate (`inherit/separated-claims`).  An answer of no clash
  is an entry with no nogoods while some claim would deny `s` in a reader that saw both,
  so an except or a `genlCx` edge that makes that reader asks it again
  (`preserving-entries`)."
  [kb s]
  (let [sen    (:sentence s)
        tms    (reasoning/tms kb)
        c      (:context s)
        sep?   (separated-membership? kb sen)
        denial (inherit/denial-readings kb sen)
        askers (cons c (sort (disj (into #{}
                                         (mapcat (fn [{:keys [handles contexts]}]
                                                   (res/exception-aware-placements
                                                    kb (conj handles (:id s))
                                                    (into [c] (sort (disj contexts c))))))
                                         denial)
                                   c)))
        cs     (into [] (mapcat #(concat (keep (fn [f] (f kb sen %))
                                               [inherit/clashing-claim inherit/converse-claim])
                                         (when sep? (inherit/separated-claims kb sen %))))
                     askers)]
    (when (or (seq cs) (seq denial))
      {:pred     (nm/functor (kb/body-under-not sen))
       :sep?     sep?
       :askers   (set askers)
       :reads    (into #{(:id s)} (mapcat :handles) denial)
       :contexts (into #{c} (mapcat :contexts) denial)
       :classes  (into {} (map (juxt identity #(jtms/defeat-class tms %)))
                       (mapcat #(cons (:claim %) (:handles %)) cs))
       :class    (jtms/defeat-class tms (:id s))
       :nogoods  (inherited-nogoods kb (:id s) sen cs)})))

(defn note-removed!
  "Record `sentex`, leaving the store, as `{handle sentence}` under `:left` in
  `:preserved-clashes` while the memo holds an entry, so the next `preserving-entries`
  reads what a handle without a record moved.  `preserving-nogoods` empties `:left` with
  the rest of the memo.  Called from `integrate/sentex-removed!`."
  [kb sentex]
  (let [memo (reasoning/preserved-clashes kb)]
    (when (seq (:entries @memo))
      (swap! memo assoc-in [:left (:id sentex)] (sx/sentence-of sentex)))))

(defn note-touched!
  "Add to `:moved` in `:preserved-clashes`, while the memo holds an entry, the handles the
  touched set recorded since the memo's mark and `extra`, the region members no
  relabel recorded (supersessions among them), so the next `preserving-entries` reads the
  belief moves after this settle's last question, which the emptied touched set and the taken
  supersession moves no longer name.  Called from `settle/settle-finish` before it
  empties the touched set."
  [kb extra]
  (let [memo (reasoning/preserved-clashes kb)
        {:keys [entries mark]} @memo]
    (when (seq entries)
      (let [hs (into (jtms/touched-since (reasoning/tms kb) mark) extra)]
        (when (seq hs)
          (swap! memo update :moved (fnil into #{}) hs))))))

(defn- entry-keys
  "The `[slot key]` paths entry `e` is filed under in the memo's inverted index `:by`:
  each handle it reads, each member whose class it recorded, its predicate, each context
  it reads and each it asked, and `[:sep]` and `[:clash]` for a separated membership and
  an entry holding a nogood."
  [e]
  (concat (map #(vector :read %) (:reads e))
          (map #(vector :member %) (keys (:classes e)))
          [[:pred (:pred e)]]
          (map #(vector :context %) (:contexts e))
          (map #(vector :asker %) (:askers e))
          (when (:sep? e) [[:sep]])
          (when (seq (:nogoods e)) [[:clash]])))

(defn- file-entries
  "`by` with each of `es` (`[handle entry]`) filed under its `entry-keys` (`on?`), or
  taken out of them."
  [by es on?]
  (reduce (fn [by [h e]]
            (reduce (fn [by k]
                      (if on?
                        (update-in by k (fnil conj #{}) h)
                        (let [s (disj (get-in by k) h)]
                          (cond (seq s) (assoc-in by k s)
                                (next k) (update by (first k) dissoc (peek k))
                                :else    (dissoc by (first k))))))
                    by (entry-keys e)))
          by es))

(defn- separation-ends
  "The types at or below which the stored `sen` (handle `h`, nil for one with no record)
  can move separations, as a set, or nil for none: the lower end of a `genl` edge whose
  upper end a separation reaches (`tax/sentence-separation-ends`), both ends of one between
  symbols when `narrow?` is false, and the ends of each separation key `h` supports
  (`tax/separation-ends`).  A `genl` edge supports no separation key, and its keys are not
  read."
  [tax h sen narrow?]
  (let [body (kb/body-under-not sen)]
    (not-empty
     (cond (not= 'genl (nm/functor body))
           (into #{} (comp (keep #(tax/separation-ends tax %)) cat)
                 (when h (tax/supported-keys tax [h])))
           narrow?                          (tax/sentence-separation-ends tax body)
           (every? symbol? (nm/args body))  (set (nm/args body))))))

(defn- preserved-below
  "The predicates of the set `preds` at or below the type `t`, read over whichever of
  `t`'s unscoped spec closure and `preds` is smaller.  The unscoped closure is a superset
  over every reader, since each asker re-reads its own."
  [tax preds t]
  (if-some [below (tax/specs-global-within tax t (count preds))]
    (filter preds below)
    (filter #(contains? (tax/genls-global tax %) t) preds)))

(defn- separated-under
  "The handles of `sep`, the separated memberships' entries of `entries`, whose type is at
  or below one of the types `lows`, or all of `sep` when one of the preserved `preds` is:
  a `genl` edge moves the separations of the types at or below its lower end alone."
  [tax preds entries sep lows]
  (if (some #(seq (preserved-below tax preds %)) lows)
    sep
    (let [lows   (set lows)
          missed (volatile! #{})
          under? (memoize #(tax/genls-global-meets? tax % lows missed))]
      (filter #(under? (:pred (get entries %))) sep))))

(defn- separated-reach
  "The stored memberships the stored claims of the preserved `preds` can deny, read from the
  claims (`inherit/claim-reach-separated`, every class and polarity): the whole store's
  membership questions.  A predicate no stored claim states (`inherit/claims-stored?`)
  reaches nothing, and one stops reading its claims once they reach every stored
  membership of its separated types.  The claims are read over the unscoped closure of
  each predicate, a superset over every reader, since each asker re-reads its own."
  [kb preds]
  (let [idx  (:index kb)
        recs (:records kb)
        tax  (reasoning/taxonomy kb)]
    (into #{}
          (mapcat (fn [pred]
                    (when (inherit/claims-stored? kb pred)
                      (let [all (reduce + (map #(reads/stored-count-with-functor idx %)
                                               (inherit/separated-types kb pred)))]
                        (when (pos? all)
                          (reduce (fn [acc h]
                                    (let [acc (into acc (when-let [s (p/get-sentex recs h)]
                                                          (inherit/claim-reach-separated
                                                           kb (sx/sentence-of s) pred)))]
                                      (if (>= (count acc) all) (reduced acc) acc)))
                                  #{}
                                  (mapcat #(reads/as-stored-with-functor idx %) (tax/specs-global tax pred))))))))
          preds)))

(defn- preserving-moves
  "What the moved handles `moves` (`[handle region?]`, `region?` false for a withdrawal
  alone) re-open, as `[whole reached sep]`: the predicates whose extent is re-asked, the
  stored facts a moved claim reaches, and the separated memberships re-asked: `:all` when
  a separation or a recordless non-`genl` handle moved, else the moved `genl` edges' lower
  ends (`separated-under`) or nil.  `vantaged` (a delay) holds the predicates with an
  entry; `left` is `note-removed!`'s sentences; `narrow?` false re-opens the whole extent
  of every predicate a claim or an edge moves (docs/nmtms.md, \"The inherited-clash
  memo\", the vocabulary, claim and separation inputs)."
  [kb pairs left moves vantaged narrow?]
  (let [recs   (:records kb)
        tms    (reasoning/tms kb)
        tax    (reasoning/taxonomy kb)
        extent (memoize #(reads/as-stored-with-functor (:index kb) %))
        preds  (into #{} (map first) pairs)
        ;; a functor whose channels read no argument answers once per call
        by-f   (memoize #(inherit/moved-channels kb (list %) pairs any?))
        ;; preserved along a relation above `genl`, which `inherit/edge-reach` does not read
        wide   (let [rs (disj (tax/genls-global tax 'genl) 'genl)]
                 (into #{} (keep (fn [[p r]] (when (contains? rs r) p))) pairs))]
    (inherit/with-memo
      (let [[whole reached sep]
            (reduce
             (fn [[whole reached sep] [h region?]]
               (let [s   (p/get-sentex recs h)
                     sen (if s (sx/sentence-of s) (get left h))]
                 (if-not sen
                   [whole reached sep]
                   (let [body  (kb/body-under-not sen)
                         f     (nm/functor body)
                         [claimed other]
                         (if (inherit/channels-read-arguments? f)
                           (inherit/moved-channels
                            kb sen pairs #(and (not (contains? whole %)) (seq (extent %))))
                           (by-f f))
                         edge? (and (= 'genl f) (every? symbol? (nm/args body)))
                         ;; an edge moves a predicate preserved along `genl` at the facts
                         ;; holding a term of its closure alone
                         cross (when (and edge? narrow?)
                                 (let [[a b] (nm/args body)]
                                   (into {} (keep #(when-not (contains? wide %)
                                                     (some->> (inherit/edge-reach kb a b %) (vector %))))
                                         other)))
                         ends  (separation-ends tax (when s h) sen narrow?)
                         ;; a `genl` edge between predicates makes one's claims the other's, and
                         ;; carries a mark over to a sub-predicate (`tax/props-over`)
                         whole (cond-> (into whole (remove #(contains? cross %)) other)
                                 edge?
                                 (into (filter preds) (mapcat #(tax/genls-global tax %) (nm/args body)))
                                 ends
                                 (-> (into (comp (filter #(seq (inherit/separated-preserved kb % '?ctx)))
                                                 (mapcat #(tax/specs-global tax %)))
                                           ends)
                                     ;; a preserved predicate at or below an end is separated
                                     ;; from types no end is above
                                     (into (mapcat #(preserved-below tax preds %)) ends)))
                         kt?   (delay (and (jtms/in? tms h)
                                           (strength/known-true? (jtms/defeat-class tms h))))]
                     [whole
                      (into (into reached cat (vals cross))
                            (comp (remove whole)
                                  (filter #(or (not narrow?) (and region? (contains? @vantaged %)) @kt?))
                                  (mapcat #(concat
                                            (or (when narrow? (inherit/claim-reach-extent kb sen %))
                                                (extent %))
                                            (if narrow?
                                              (inherit/claim-reach-separated kb sen %)
                                              (mapcat extent (inherit/separated-types kb %))))))
                            claimed)
                      (cond (= :all sep)             :all
                            (and edge? narrow?)      (conj (or sep #{}) (first (nm/args body)))
                            (or edge? (nil? s) ends) :all
                            :else                    sep)]))))
             [#{} #{} nil]
             moves)]
        [(into whole (comp (filter #(inherit/claims-stored? kb %)) (mapcat #(inherit/separated-types kb %)))
               (filter preds whole))
         reached
         sep]))))

(defn- entry-live?
  "Does every member of entry `e` but its candidate hold the defeat-class `e` recorded?"
  [tms e]
  (every? (fn [[h c]] (and (jtms/in? tms h) (= c (jtms/defeat-class tms h)))) (:classes e)))

(defn- except-reach
  "The handles an `except` that moved can hide or show, as a set: what `special/except-moved`
  queued, the target of each `except` among the region `handles` (read from `left` for one
  with no record), each of those followed down its except cascade, and their consequence
  closure.  nil when no except moved."
  [kb handles left]
  (let [recs   (:records kb)
        target #(some-> (if-let [s (p/get-sentex recs %)] (sx/sentence-of s) (get left %))
                        kb/except-target)
        roots  (into (set (special/except-moved kb)) (keep target) handles)]
    (when (seq roots)
      (jtms/consequence-closure
       (reasoning/tms kb)
       (into #{} (mapcat #(take-while some? (iterate target %))) roots)))))

(defn- preserving-entries
  "The standing inherited clashes after this call, `{:entries {handle entry} :by by :asked
  hs :moved hs}` (`preserving-entry`), `by` their inverted index (`file-entries`),
  `:asked` the handles whose entries were dropped or found, and `:moved` the handles whose
  belief moved since the last call; both nil when nothing was carried.  An entry is
  carried unless an input it reads moved (docs/nmtms.md, \"The inherited-clash memo\"),
  and each input looks up in `by` the entries it names.  Nothing is carried when
  `*incremental-preserving*` is false, the `genlCx` relation was rebuilt, `first?` is true, `moved` is nil, or a region handle has
  neither a record nor a `:left` sentence.  Under `*whole-store-region?*` with no `:mark`
  in `prev`, the questions are the preserved predicates' stored extents and the
  memberships their stored claims reach (`separated-reach`).  `declared` is the facts a
  forced-monotonic declaration that moved reaches, whose entries are asked again."
  [kb pairs region prev reach first? moved declared]
  (let [recs    (:records kb)
        tms     (reasoning/tms kb)
        tax     (reasoning/taxonomy kb)
        handles (if-some [m (when *incremental-preserving* (:mark prev))]
                  (jtms/touched-since tms m)
                  @region)
        entries (:entries prev {})
        left    (:left prev {})
        ;; built from the entries when an image written without it installed them
        by      (delay (or (:by prev) (file-entries {} entries true)))
        ;; not a count of `handles`: a stored sentex with no premise and no justification
        ;; is never relabelled, so the region can miss a handle the store holds
        whole?  (and *whole-store-region?* (nil? (:mark prev)))
        why     (cond whole?                          :whole-store
                      (not *incremental-preserving*)  :exhaustive
                      (or (:all? reach) (nil? moved)) :rebuilt
                      ;; entries no pass has read the cursor beside since the index was emptied
                      (and (seq entries) first?)      :rebuilt
                      ;; nothing reads what a handle with no record and no `left` sentence moved
                      (some #(and (not (contains? left %)) (nil? (p/get-sentex recs %))) handles)
                      :retraction)
        fresh?  (some? why)
        moved-belief (when-not fresh?
                       (-> (set handles)
                           (into (:moved prev))
                           (into (special/pending-supersession-moves kb))))
        [whole reached sep]
        (if whole?
          [#{} #{} nil]
          (preserving-moves kb pairs left
                            ;; a moved flat-cache entry is read through what its supporters state
                            (concat (map #(vector % true) handles)
                                    (when-not fresh?
                                      (map #(vector % false)
                                           (into #{}
                                                 (mapcat #(tax/visible-supporters tax % nil))
                                                 moved))))
                            (delay (into #{} (keys (:pred @by))))
                            *incremental-preserving*))
        hidden  (when-not fresh? (except-reach kb handles left))
        dropped (if fresh?
                  (keys entries)
                  (let [b     @by
                        named (fn [slot ks] (mapcat #(get (slot b) %) ks))
                        held  #(contains? entries %)
                        moves (-> #{}
                                  (into (named :pred whole))
                                  (into (filter held) reached)
                                  (into (filter held) (keys left))
                                  (into (named :read hidden))
                                  ;; a moved declaration moves which claims a vantage believes
                                  (into (filter held) declared)
                                  (into (named :read declared))
                                  (into (when reach
                                          (concat (named :context (:below reach))
                                                  (named :asker (:under reach)))))
                                  ;; a separation leaving moves no extent
                                  (into (if (= :all sep)
                                          (:sep b)
                                          (concat (filter #(contains? (:sep b) %) (named :read handles))
                                                  (when (seq sep)
                                                    (separated-under tax (into #{} (map first) pairs)
                                                                     entries (:sep b) sep))))))]
                    (into moves
                          (comp (remove moves) (remove #(entry-live? tms (get entries %))))
                          (set (named :member moved-belief)))))
        kept    (if fresh? {} (persistent! (reduce dissoc! (transient entries) dropped)))
        idx     (:index kb)
        preds   (into #{} (map first) pairs)
        ;; the whole store's claims are the preserved predicates' stored extents and the
        ;; memberships those can deny, read off the index rather than off a record per
        ;; region handle
        ask     (-> (set dropped)
                    (into (if whole?
                            (concat (mapcat #(reads/as-stored-with-functor idx %) preds)
                                    (separated-reach kb preds))
                            handles))
                    (into reached)
                    (into (mapcat #(reads/as-stored-with-functor idx %)) whole)
                    (->> (remove kept)))
        _       (trove/log! {:level :debug :id ::asked
                             :data  {:region (count handles) :carried (count kept) :asked (count ask)
                                     :fresh why}})
        ;; one memo over every question: belief does not move while they are asked
        found   (inherit/with-memo
                  (with-open [r (progress/start ::preserving-entries "settle: ask the preserved predicates' questions"
                                                (count ask))]
                    (into []
                          (keep (fn [h]
                                  (when (jtms/in? tms h)
                                    (when-let [s (p/get-sentex recs h)]
                                      (when (or (contains? preds (nm/functor (kb/body-under-not (:sentence s))))
                                                (separated-membership? kb (:sentence s)))
                                        (when-let [e (preserving-entry kb s)] [h e]))))))
                          ;; sorted so the queries run in a reproducible order
                          (progress/each r (sort ask)))))]
    {:entries (into kept found)
     :by      (if fresh?
                (file-entries {} found true)
                (-> @by
                    (file-entries (map #(vector % (get entries %)) dropped) false)
                    (file-entries found true)))
     :asked   (when-not fresh? (into (set dropped) (map first) found))
     :moved   moved-belief}))

(defn- entry-nogoods
  "The nogood maps the entry of `h` in `entries` publishes: none while `h` is OUT, and
  each with its `:priority` read again when `h`'s class moved since the entry recorded it
  (the other members hold the classes it recorded)."
  [tms entries h]
  (when (jtms/in? tms h)
    (let [e (get entries h)]
      (if (= (:class e) (jtms/defeat-class tms h))
        (:nogoods e)
        (map #(assoc % :priority (member-priority tms (:nogood %))) (:nogoods e))))))

(defn- member-sets
  "Every member set holding `h` among the nogoods of the entries of `entries` that can
  hold it: `h`'s own and those `by` files `h` under as a member."
  [entries by h]
  (into #{} (comp (mapcat #(:nogoods (get entries %)))
                  (map :nogood)
                  (filter #(contains? % h)))
        (cons h (get-in by [:member h]))))

(defn preserving-nogoods
  "The clashes between a stored claim and a known-true claim argument preservation reads
  at its own tuple, as nogood maps (`inherited-nogoods`).  Resets `:preserved-clashes`,
  the memo `preserving-entries` carries.

  The members are the stored claim and the reading's reasons (`inherit/clashing-claim`'s
  `:claim` and `:handles`).  `:priority` is the rebuttal range, 1–2.  A candidate is asked
  from its own context and from every vantage (`preserving-entry`).  A body stored in both
  polarities is a negation pair (`chain/place-negations!`), excluded by
  `clashing-claim`.  Behind `inherit/preserved-pairs`, two predicate-extent counts on a KB
  that declares none (docs/nmtms.md, \"What qualifies as a nogood\";
  docs/inherit.md).  The memo keeps a mark of the touched set taken before the
  questions (`jtms/touch-mark`), where the next call's region starts.  `reach` (a delay,
  forced only when a pair is preserved) and `first?` are the pass's `genlCx` moves
  (`special/drain-context-moves!`).  `declared` is the facts a forced-monotonic declaration that
  moved reaches (`preserving-entries`).

  Answers `{:nogoods #{ngmap}}`, every entry's clashes, when no entry was carried.
  Otherwise `:nogoods` holds the clashes of the entries this call dropped or found and of
  those holding one of their handles as a member, and `:sets` every member set whose
  clashes can differ from the last call's: those of the changed entries before and after,
  and those holding a handle whose belief moved."
  [kb region reach first? declared]
  (let [pairs (inherit/preserved-pairs kb)]
    (if (empty? pairs)
      (do (reset! (reasoning/preserved-clashes kb) {}) {:nogoods #{}})
      (let [tms          (reasoning/tms kb)
            mark         (jtms/touch-mark tms)
            prev         @(reasoning/preserved-clashes kb)
            old          (:entries prev {})
            [flat moved] (flat-reading kb (:flat prev))
            {:keys [entries by asked] moved-belief :moved}
            (preserving-entries kb pairs region prev @reach first? moved (set declared))
            named        (fn [hs] (into (set hs) (mapcat #(get-in by [:member %])) hs))
            sets-of      (fn [es hs] (into #{} (comp (mapcat #(:nogoods (get es %))) (map :nogood)) hs))]
        (reset! (reasoning/preserved-clashes kb)
                {:flat    flat
                 :mark    mark
                 :entries entries
                 :by      by})
        (if (nil? asked)
          {:nogoods (into #{} (mapcat #(entry-nogoods tms entries %)) (:clash by))}
          (let [changed (into #{} (remove #(identical? (get entries %) (get old %))) asked)
                reread  (named changed)]
            {:nogoods (into #{} (mapcat #(entry-nogoods tms entries %)) reread)
             :sets    (-> (sets-of old changed)
                          (into (sets-of entries reread))
                          (into (sets-of entries (named moved-belief))))}))))))

(defn discover-inherited!
  "Find the inherited clashes (`preserving-nogoods`) over the network and record them in
  the candidate index: each member set it read again (`inherited/update-inherited!`), or
  every clash when it carried no entry (`inherited/install-inherited!`).  Answers
  `{:found [ngmap] :left [members]}`: each clash, whose members the network believes, of
  a candidate asked again this call (one whose memo entry was not carried), and the member
  sets the index held and no longer holds.  `chain/place-inherited!` places the first at
  their vantages and removes the placements of the second.  `reach` and `first?` are the
  pass's `genlCx` moves (`special/drain-context-moves!`).  `moved` is the facts a
  forced-monotonic declaration that moved reaches, whose entries are asked again
  (`preserving-entries`)."
  ([kb region reach first?] (discover-inherited! kb region reach first? nil))
  ([kb region reach first? moved]
   (let [tms   (reasoning/tms kb)
         in?   #(jtms/in? tms %)
         prev  (:entries @(reasoning/preserved-clashes kb) {})
         held  (comp (filter #(every? in? (:nogood %)))
                     (filter #(seq (:vantages %)))
                     (distinct))
         {:keys [nogoods sets]} (preserving-nogoods kb region reach first? moved)
         {now :entries by :by} @(reasoning/preserved-clashes kb)
         ngs   (into [] held nogoods)
         left  (if sets
                 (inherited/update-inherited!
                  kb
                  (into {} (map (fn [ms]
                                  [ms (into [] (comp (mapcat #(entry-nogoods tms now %))
                                                     (filter #(= ms (:nogood %)))
                                                     held)
                                            ms)]))
                        sets)
                  #(member-sets now by %))
                 (inherited/install-inherited! kb ngs))]
     ;; a carried entry is the identical value, so its clashes and their placements stand
     {:found (into [] (filter (fn [ng] (some #(not (identical? (get now %) (get prev %))) (:nogood ng))))
                   ngs)
      :left  left})))

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :D3 :label "Preserved clashes" :kind :cache :keyed-by :handle
  :holds-content? false
  :reads [:index :T1 :Q2 :Q3 :J4 :J6 :M2]
  :retired-by {:removed :K :inherited :K :settle-exit :K :settle-pass :K :recover :R
               :image-install :R}
  :computed :settle :imaged? :state :at [[:preserved-clashes]]
  :note "the inherited clashes found per stored claim with what each was read under; read again by region, moves, the excepts that moved and the genlCx moves of the pass (J6), whole when J4 lost its position, genlCx was rebuilt or the cursor restarted, and `:left` notes a removal; `:by` files each entry under what it reads, and `:moved` holds the belief moves after the last question"})
