;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.membership
  "The membership families: two memberships of one term whose types a separation holds
  apart (`disjoint`), a membership beside a denial of a supertype of its type
  (`supertype`), and a membership under a cover's whole beside a denial of each part
  (`covering`), placed as nogoods (`chain/place-memberships!`).  See docs/nmtms.md, \"A
  nogood placed as a conclusion\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the membership families ---------------------------------------------
;;
;; A `disjoint` nogood is two memberships of one term whose types a separation a reader
;; sees holds apart, a `supertype` nogood is a membership beside a denial of a strict
;; supertype of its type, and a `covering` nogood is a membership under a cover's whole
;; with one denial of each part or of a supertype of it.  All three are keyed by the term, so the
;; candidate index keeps each term holding two memberships, or a membership and a denial,
;; under `::mem` as `{x {h [type context positive?]}}`, read off the term's unary roster
;; once and kept in step after, its memberships by type under `::types`, `{x {t
;; #{h}}}`, and its denials by type under `::denials`.  The kept terms under a type are
;; read off the index (`reads/as-stored-unary-kept-terms`, `reads/as-stored-unary-denied-terms`,
;; `listed-under`).  `::sep` holds, per kept term, the pairs of its types the unscoped taxonomy separates with no exception read,
;; `{x {[ta tb] how}}`, `how` `:spared` when a stored `siblingDisjointException` exempts the pair and
;; `:sep` otherwise.  A pair is tested when its second type arrives at the term, and again
;; when `tax/separation-stamp` or a `genl` edge moves over one of its types
;; (`sync-memberships`), which reads no membership.  A term holding a separated pair, or a
;; membership beside a denial its nogoods convict, is live under `::live-mem`, and its
;; memberships and denials there are the family's candidates under `:membership`.
;; `::moved` holds the terms whose nogoods the settle places again (`take-moved!`).  Recover keeps the terms of two unary
;; predicates (`reads/as-stored-unary-multi-terms`) and of a unary body stored in both
;; polarities that hold two memberships or a membership and a denial, read off their
;; unary rosters (`recovered-terms`).

(defn- membership-of
  "`[x t positive?]` for a stored fact `sx` whose sentence is `(t x)` or `(not (t x))`
  with `t` and `x` plain symbols, else nil."
  [sx]
  (when (nil? (:antecedent sx))
    (let [s   (:sentence sx)
          neg (sx/negation? s)
          b   (if neg (second s) s)]
      (when (and (seq? b) (= 2 (count b)))
        (let [[t x] b]
          (when (and (sx/plain-symbol? t) (not= 'not t) (sx/plain-symbol? x))
            [x t (not neg)]))))))

(defn- term-entries
  "`{h [t context positive?]}` of the stored memberships and denials of `x`, read off its
  unary roster (`reads/as-stored-unary-with-arg-global`, a superset filtered here), so the facts
  holding `x` at argument 1 of a longer tuple are not fetched."
  [kb x]
  (let [recs (:records kb)]
    (into {}
          (keep (fn [h]
                  (when-let [sx (p/get-sentex recs h)]
                    (when-let [[x' t pos] (membership-of sx)]
                      (when (= x x') [h [t (:context sx) pos]])))))
          (reads/as-stored-unary-with-arg-global (:index kb) x))))

(defn- held?
  "Can the entries `m` of one term form a nogood: two memberships, or a membership and a
  denial?  Reads entries until they answer it."
  [m]
  (true? (reduce (fn [[p n] [_ _ pos]]
                   (let [p (cond-> p pos inc)
                         n (cond-> n (not pos) inc)]
                     (if (or (< 1 p) (and (pos? p) (pos? n))) (reduced true) [p n])))
                 [0 0] (vals m))))

(defn- separation-tests
  "`(fn [a])` → nil when no separation reaches the type `a` over the unscoped taxonomy
  (`tax/separation-test`), else `(fn [b])` → how it separates `a` and `b`: nil when it
  does not with no exception read, `:spared` when it does and a stored
  `siblingDisjointException` exempts the pair, `:sep` otherwise.  An exception exempts the pair only at a reader
  that sees it, so a reader may read a `:spared` pair separated.  The unscoped test is
  symmetric, so `a`'s test alone decides each pair."
  [tax]
  (let [exc? (tax/sib-exceptions? tax)]
    (fn [a]
      (when-let [strict (tax/separation-test tax a nil (constantly false))]
        (let [exempt (when exc? (tax/disjointness-test tax a nil))]
          (fn [b]
            (when (strict b)
              (if (and exempt (not (exempt b))) :spared :sep))))))))

(defn- pair-of [a b] (if (neg? (compare a b)) [a b] [b a]))

(defn- untest
  "`c` with the separated pairs of term `x` holding type `t` dropped."
  [c x t]
  (let [left (into {} (remove #(some #{t} (key %))) (get-in c [::sep x]))]
    (if (seq left) (assoc-in c [::sep x] left) (update c ::sep dissoc x))))

(defn- test-type
  "`c` with the pair of type `t` and each other type term `x` holds tested (`test`,
  `separation-tests`), and the separated ones under `::sep`.  Tests no partner when no
  separation reaches `t`."
  [test c x t]
  (if-let [f (test t)]
    (reduce (fn [c b]
              (if-let [how (and (not= b t) (f b))]
                (assoc-in c [::sep x (pair-of t b)] how)
                c))
            c (keys (get-in c [::types x])))
    c))

(defn- add-entry
  "`c` with the entry `e` of handle `h` added to term `x`: a membership under `::types`,
  its type tested against the term's others when it is new to the term (`test-type`), or
  a denial under `::denials`."
  [test c x h [t _ pos :as e]]
  (let [c (assoc-in c [::mem x h] e)]
    (if-not pos
      (update-in c [::denials x t] (fnil conj #{}) h)
      (let [fresh? (empty? (get-in c [::types x t]))
            c      (update-in c [::types x t] (fnil conj #{}) h)]
        (if fresh? (test-type test c x t) c)))))

(defn- remove-entry
  "`c` with handle `h`'s entry removed from term `x`: a membership's type leaves the term,
  with the separated pairs holding it (`untest`), when no other membership of `x` holds
  it, and a denial's type when no other denial of `x` holds it."
  [c x h]
  (if-let [[t _ pos] (get-in c [::mem x h])]
    (let [c   (update-in c [::mem x] dissoc h)
          k   (if pos ::types ::denials)
          hs  (disj (get-in c [k x t]) h)]
      (cond
        (seq hs) (assoc-in c [k x t] hs)
        pos      (untest (update-in c [::types x] dissoc t) x t)
        :else    (update-in c [::denials x] dissoc t)))
    c))

(defn- denied?
  "Does the candidate index `c` keep a denial of term `x`?"
  [c x]
  (boolean (seq (get-in c [::denials x]))))

(defn- cover-candidate?
  "Can a cover over one of term `x`'s types be refuted from what the candidate index `c`
  keeps of it: the taxonomy stores a cover, and `x` holds a denial or a second type, a
  membership a separation can deny a part through (`term-nogoods`)."
  [tax c x]
  (boolean (and (seq (tax/coverings tax))
                (or (denied? c x) (< 1 (count (get-in c [::types x])))))))

(defn- drop-term
  "`c` with term `x` and every row naming it dropped."
  [c x]
  (-> c (update ::mem dissoc x) (update ::types dissoc x) (update ::denials dissoc x)
      (update ::sep dissoc x)))

(defn- combinations
  "The cartesian product of the collections `colls`, each product a vector."
  [colls]
  (reduce (fn [acc c] (for [xs acc x c] (conj xs x))) [[]] colls))

(defn- term-nogoods
  "The membership nogoods of term `x` (`::mem`), each `{:members #{h} :kind k}`: two
  memberships of a pair of types a separation holds apart (`::sep`, a superset over every
  reader), `:disjoint`, marked `:spared? true` for a pair a stored exception exempts;
  a membership beside a denial of a strict supertype of its type, `:supertype`; and a
  membership under a cover's whole with, for each part, a denier of it, `:cover`, one
  nogood per choice of deniers, less a member set the `:disjoint` or `:supertype` arm
  already holds.  A denier of a part is a denial of the part or of a supertype of it, or a
  membership of another type a declaration separates from the part
  (`tax/pair-separated?`, unscoped and with no exception read): the separation's denial
  (`res/separation-denials`), whose soundness rule and exemptions the placement reads
  (`routes`, `chain/route-placements`).  Read through the write view `w`
  (`decide/write-view`)."
  [tax w c x]
  (let [above (:genls-global w)
        types (get-in c [::types x])
        ;; a denied type's specializations where they number no more than the term's
        ;; types, else each type's closure up, so a write reads the smaller of the two
        sups  (for [[q ds] (get-in c [::denials x])
                    :let [below (tax/specs-global-within tax q (count types))]
                    s (if below
                        (filter #(contains? types %) below)
                        (filter #(contains? (above %) q) (keys types)))
                    :when (not= s q)
                    h (get types s), d ds]
                {:members #{h d} :kind :supertype})
        dis   (for [[[a b] how] (get-in c [::sep x])
                    h1 (get-in c [::types x a])
                    h2 (get-in c [::types x b])]
                (cond-> {:members #{h1 h2} :kind :disjoint}
                  (= :spared how) (assoc :spared? true)))
        held  (into #{} (map :members) (concat dis sups))]
    (concat
     dis
     sups
     (when (cover-candidate? tax c x)
       (let [m   (get-in c [::mem x])
             pos (filterv #(nth (val %) 2) m)
             neg (filterv #(not (nth (val %) 2)) m)]
         (distinct
          (for [[h [s]]   pos
                [_ parts] (distinct (tax/covers-over tax s nil))
                :let [per (for [p (distinct parts)
                                :let [ups (above p)]]
                            (concat (for [[d [q]] neg :when (contains? ups q)] d)
                                    (for [[d [s']] pos
                                          :when (and (not= s' s) (tax/pair-separated? tax s' p))]
                                      d)))]
                :when (every? seq per)
                combo (combinations per)
                :let [ms (into #{h} combo)]
                :when (not (held ms))]
            {:members ms :kind :cover})))))))

(defn- place-term
  "`c` with term `x`'s nogoods read again through the unscoped taxonomy (`term-nogoods`),
  kept under `::ngs` while it has one; their members are under `::live-mem` and in step
  in `:membership`.  A term with no separated pair (`::sep`) and no denial has none, and
  is read no further.  A term whose nogoods moved, or every term
  holding one when `force?`, is queued under `::moved` with the members of its nogoods
  before and after, for the settle to place (`take-moved!`)."
  [w c x force?]
  (let [tax (:tax w)
        old (get-in c [::live-mem x])
        was (get-in c [::ngs x])
        ngs (when (or (seq (get-in c [::sep x])) (denied? c x) (cover-candidate? tax c x))
              (not-empty (vec (term-nogoods tax w c x))))
        new (not-empty (into #{} (mapcat :members) ngs))]
    (as-> c c
      (if (and (or was ngs) (or force? (not= (set was) (set ngs))))
        (update-in c [::moved x] (fnil into #{}) (concat old new))
        c)
      (if (seq ngs) (assoc-in c [::ngs x] ngs) (update c ::ngs #(some-> % (dissoc x))))
      (if (= old new)
        c
        (-> c
            (update :membership #(into (reduce disj (or % #{}) old) new))
            (journal/note (concat old new))
            (update ::live-mem #(if new (assoc (or % {}) x new) (dissoc % x))))))))

(def ^:private listings
  "The index's lists of terms by unary predicate, each `[count types terms]` over the
  index: the terms of two unary predicates under each (`:kept`), and the terms a stored
  denial names under its predicate (`:denied`)."
  {:kept   [reads/stored-count-unary-kept-types reads/as-stored-unary-kept-types
            reads/as-stored-unary-kept-terms]
   :denied [reads/stored-count-unary-denied-types reads/as-stored-unary-denied-types
            reads/as-stored-unary-denied-terms]})

(defn- listed-under
  "`[t xs]` for each type `t` at or below one of the types `ends` over the unscoped `genl`
  closure (`w`, `decide/write-view`) under which one of the index's lists `ks`
  (`listings`) holds terms, `xs` those terms.  The terms of two unary predicates are a
  superset of the kept terms holding an entry of `t` beside an entry of another type, and
  the terms denied `t` hold the kept terms whose every entry is of `t`.  Reads the types
  the lists hold, each by one walk up to the first of `ends` over one memo
  (`tax/genls-global-meets?`), or the specializations of `ends`, whichever is fewer, then
  one set per type and list."
  [kb w ends ks]
  (when (seq ends)
    (let [idx  (:index kb)
          ends (set ends)
          ls   (map listings ks)
          ts   (if (< (transduce (map #((first %) idx)) + ls) (* 4 (count ends)))
                 (let [missed (volatile! #{})]
                   (into #{} (comp (mapcat #((second %) idx))
                                   (filter #((:genls-global-meets? w) % ends missed)))
                         ls))
                 (distinct (mapcat (:specs-global w) ends)))]
      (into [] (keep (fn [t] (let [xs (into #{} (mapcat #((nth % 2) idx t)) ls)]
                               (when (seq xs) [t xs]))))
            ts))))

(defn- holding
  "The pairs `[x t]` of the listed `[t xs]` whose term `x` the candidate index `c` keeps
  with a membership of `t`."
  [c listed]
  (for [[t xs] listed, x xs :when (seq (get-in c [::types x t]))] [x t]))

(defn- cover-wholes-under
  "The wholes of the stored covers with a part at or below one of the types `ends` over
  the unscoped `genl` closure (`w`, `decide/write-view`): a `genl` edge moving at such a
  part moves which denials cover it.  Each part is read by one walk up to the first of
  `ends` over one memo (`tax/genls-global-meets?`)."
  [w ends]
  (let [ends   (set ends)
        missed (volatile! #{})
        under? #((:genls-global-meets? w) % ends missed)]
    (into #{} (keep (fn [[whole pks]] (when (some #(some under? (first %)) pks) whole)))
          (tax/coverings (:tax w)))))

(defn- membership-synced?
  "Is `c`'s membership index read under the taxonomy as it stands: the declarations
  (`tax/separation-stamp`), each roster the identical value, and the `genl` generation?
  A roster equal and not identical answers false, and `sync-memberships` takes the
  taxonomy's (docs/nmtms.md, \"How a settle finds the clashes\")."
  [tax c]
  (let [seen (::sep-stamp c)]
    (and (some? seen)
         (let [st (tax/separation-stamp tax)]
           (and (= (count st) (count seen)) (every? true? (map identical? st seen))))
         (= (tax/relation-gen tax :genl) (::genl-seen c)))))

(defn- sync-memberships
  "`c` with `::sep` and the kept nogoods read again under the taxonomy as it stands.  The
  pairs holding a type at or below a type whose separations the declarations moved
  (`tax/separation-moves`), or at or below the lower end of a moved `genl` edge
  (`tax/moves-since`), are tested again (`listed-under`), since no other pair's
  separation moved.  With no stamp to compare, or the `genl` relation rebuilt from nothing,
  every kept term's pairs are.  The terms tested are placed again, and so are the terms
  with a membership at or below a type whose cover nogoods the move can move, beside a
  denial or a second type (`cover-candidate?`):
  the lower end of a moved edge, the whole of a cover with a part at or below one
  (`cover-wholes-under`), and the whole of a moved cover (`tax/cover-moves`).  Every term
  placed is queued when an edge moved.  On a full test every term holding nogoods is
  placed again too.  Reads no membership."
  [kb w c]
  (let [tax    (:tax w)
        st     (tax/separation-stamp tax)
        old    (::sep-stamp c)
        g      (tax/relation-gen tax :genl)
        seen   (::genl-seen c)
        test   (separation-tests tax)
        full   (or (nil? old) (nil? seen) (< g seen))
        ;; an edge moving can move a nogood's routes with its members unmoved
        edge?  (or (nil? seen) (not= g seen))
        decl?  (not= st old)
        retest (fn [c x ts] (reduce #(test-type test (untest %1 x %2) x %2) c ts))
        [c xs] (if full
                 [(reduce-kv (fn [c x ts] (retest c x (keys ts)))
                             (assoc c ::sep {}) (::types c))
                  (keys (::mem c))]
                 (let [lows   (when edge? (tax/moves-since tax :genl seen))
                       ends   (cond-> (set lows) decl? (into (tax/separation-moves old st)))
                       hits   (holding c (listed-under kb w ends [:kept]))
                       covers (cond-> (set lows)
                                (seq lows) (into (cover-wholes-under w lows))
                                decl?      (into (tax/cover-moves old st)))]
                   [(reduce (fn [c [x t]] (retest c x [t])) c hits)
                    (concat (map first hits)
                            (keep (fn [[x _]] (when (cover-candidate? tax c x) x))
                                  (holding c (listed-under kb w covers [:kept :denied]))))]))
        xs     (cond-> (set xs)
                 full (into (keys (::ngs c))))
        c      (assoc c ::sep-stamp st ::genl-seen g)]
    (reduce #(place-term w %1 %2 edge?) c xs)))

(defn- add-held
  "`c` with the kept term `x`'s entries `m` recorded, and no separation read:
  `rebuild-candidates!`' step, which leaves the separations to `sync-memberships`."
  [c x m]
  (reduce-kv (fn [c h e] (add-entry (constantly nil) c x h e)) c m))

(defn- recovered-terms
  "The terms recover reads the entries of: those the unary roster lists two or more
  predicates of, and the arguments of the unary bodies stored in both polarities.  Every
  term holding two memberships of distinct types, or a membership and a denial, is one."
  [kb]
  (let [idx (:index kb)]
    (into (into #{} (filter sx/plain-symbol?) (reads/as-stored-unary-multi-terms idx))
          (keep (fn [b] (when (and (= 2 (count b)) (sx/plain-symbol? (first b))
                                   (sx/plain-symbol? (second b)))
                          (second b))))
          (reads/as-stored-opposed-bodies idx))))

(defn- note-membership!
  "Keep the membership candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving.  A membership or a denial of a kept term joins it with no roster read, and a
  membership's type new to the term is tested against the term's other types
  (`add-entry`).  One of a term not kept reads the term's unary roster once
  (`term-entries`), and keeps the term when it holds two memberships or a membership and
  a denial.  A term that read holds denials and no membership is noted under `::no-pos`,
  so a further denial of it reads nothing, and its first membership reads the roster once
  and keeps it.  A declaration arriving reads nothing here: `sync-memberships` reads its
  separations over the kept terms under its types (`listed-under`)."
  [kb w sx stored?]
  (when-let [[x t pos] (membership-of sx)]
    (let [h     (:id sx)
          e     [t (:context sx) pos]
          cands (reasoning/nogood-candidates kb)
          sync  #(if (membership-synced? (:tax w) %) % (sync-memberships kb w %))
          place (fn [c] (place-term w (if (held? (get-in c [::mem x])) c (drop-term c x)) x false))]
      (cond
        (contains? (::mem @cands) x)
        (swap! cands (fn [c]
                       (let [c (sync c)]
                         (place (if stored?
                                  (add-entry (separation-tests (:tax w)) c x h e)
                                  (remove-entry c x h))))))

        (and stored? (not pos) (contains? (::no-pos @cands) x))
        nil

        stored?
        (let [m (assoc (term-entries kb x) h e)]
          (cond
            (held? m)
            (swap! cands (fn [c]
                           (let [c    (-> (sync c) (update ::no-pos #(some-> % (disj x))))
                                 test (separation-tests (:tax w))]
                             (place (reduce-kv (fn [c h e]
                                                 (if (get-in c [::mem x h]) c (add-entry test c x h e)))
                                               c m)))))

            (not-any? #(nth % 2) (vals m))
            (swap! cands update ::no-pos (fnil conj #{}) x)))))))

(defn- note-placement-left!
  "Queue the term of the membership nogood a `(contradicts …)` sentex `sx` leaving the
  store placed, with its members, so the settle places the nogood where it stands
  (`take-moved!`): a `genlCx` edge under the placement can have left with it."
  [kb sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'contradicts (first s)))
      (let [cands (reasoning/nogood-candidates kb)
            hs    (into #{} (keep sx/handle-id) (rest s))
            xs    (into #{} (comp (keep #(p/get-sentex (:records kb) %)) (keep membership-of)
                                  (map first))
                        hs)]
        (when (and (= 1 (count xs)) (contains? (::mem @cands) (first xs)))
          (swap! cands update-in [::moved (first xs)] (fnil into #{}) hs))))))

(defn moved?
  "Has the index queued a term whose nogoods the settle places again (`take-moved!`)?"
  [c]
  (boolean (seq (::moved c))))

(defn take-moved!
  "`{x #{h}}`, the terms whose nogoods moved since the last call, each with the members of
  its nogoods before and after the move, and the queue emptied (`place-term`)."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::moved)]
    (::moved old {})))

(defn terms-of
  "The terms of the memberships and denials among the handles `hs` that the candidate
  index `c` keeps."
  [kb c hs]
  (let [recs (:records kb)]
    (into #{} (comp (keep #(p/get-sentex recs %)) (keep membership-of) (map first)
                    (filter #(contains? (::mem c) %)))
          hs)))

(defn terms-under
  "The kept terms with a nogood (`::ngs`) holding a type at or below one of the types
  `ends` over the unscoped `genl` closure (`w`, `decide/write-view`), in a membership or a
  denial (`listed-under`): those whose nogoods a separation over `ends` arriving can give
  a route."
  [kb w c ends]
  (when (seq (::ngs c))
    (let [ngs (::ngs c)]
      (into #{} (mapcat (fn [[t xs]]
                          (filter #(and (contains? ngs %)
                                        (or (get-in c [::types % t]) (get-in c [::denials % t])))
                                  xs)))
            (listed-under kb w ends [:kept :denied])))))

(defn terms-under-edges
  "The kept terms with a nogood whose routes climb a `genl` edge with its lower end at one
  of the types `lows`: those holding a type at or below one of them, and those holding a
  type at or below the whole of a cover with a part at or below one
  (`cover-wholes-under`).  An edge's defeat class moving moves which placements a cover
  refuted through a separation's denial reads (`chain/route-placements`), with no
  membership and no declaration moving."
  [kb w c lows]
  (when (seq lows)
    (terms-under kb w c (into (set lows) (cover-wholes-under w lows)))))

(defn nogoods-terms
  "The kept terms holding a nogood under the candidate index `c`."
  [c]
  (keys (::ngs c)))

(defn nogoods-of
  "Term `x`'s nogoods under the candidate index `c`, each `{:members #{h} :kind k}`."
  [c x]
  (get-in c [::ngs x]))

(defn- member-types
  "`[x positive negative]` for the member handles `ms` of one term's nogood: the term, the
  types it is held in and the types it is denied, or nil when some member is not a stored
  membership or denial of one term."
  [recs ms]
  (let [es (map #(some-> (p/get-sentex recs %) membership-of) ms)]
    (when (and (seq es) (every? some? es) (apply = (map first es)))
      [(ffirst es)
       (into (sorted-set) (keep (fn [[_ t pos]] (when pos t))) es)
       (into (sorted-set) (keep (fn [[_ t pos]] (when-not pos t))) es)])))

(defn kind-of
  "The kind of the membership nogood over the member handles `ms`, read off their
  sentences and the unscoped `genl` closure of the write view `w` (`decide/write-view`):
  `:disjoint` for two memberships of one term in distinct types a declaration separates
  (`tax/pair-separated?`), `:supertype` for one membership of a term beside one denial of
  a strict supertype of its type, `:cover` for any other membership of a term beside
  denials of it and for two or more memberships of a term in distinct types (a cover
  refuted through a separation's denial), else nil."
  [w recs ms]
  (when-let [[_ pos neg] (member-types recs ms)]
    (cond
      (and (empty? neg) (= 2 (count pos) (count ms))
           (tax/pair-separated? (:tax w) (first pos) (second pos)))
      :disjoint
      (and (= 1 (count pos) (count neg)) (= 2 (count ms))
           (not= (first pos) (first neg))
           ((:genl?-global w) (first pos) (first neg)))
      :supertype
      (and (= 1 (count pos)) (seq neg))               :cover
      (< 1 (count pos))                               :cover)))

(defn- cover-routes
  "The routes of a cover nogood over the held types `pos` and the denied types `neg`
  (`routes`), read off every stored cover: for each held type `s` and each cover over a
  whole above it, one route per choice of a denier for each part.  A part a denial of
  the part or of a supertype of it covers takes the first such denial, its subsumption a
  link.  Any other part takes each route a declaration separates another held type from
  it through (`tax/separation-routes`): the route's keys and links join the cover's, its
  links are `:strict-links`, its `[:member m y]` keys are `:strict-keys`, and a mark
  route's separated pair is in `:pairs`.  The placement reads the soundness rule of a
  separation's denial off those three (`chain/route-placements`).  A route is a superset
  over every reader, and the placement decides which contexts see it."
  [w pos neg]
  (let [tax (:tax w)]
    (distinct
     (for [s         pos
           [whole parts] (distinct (tax/covers-over tax s nil))
           [ps kind] (tax/covers-of tax whole)
           :when (= ps parts)
           :let [per (for [p parts]
                       (if-let [q (first (filter #(contains? ((:genls-global w) p) %) neg))]
                         [{:links [[p q]]}]
                         (for [d pos
                               :when (not= d s)
                               r (tax/separation-routes-held tax d p)]
                           {:keys   (:keys r) :links (:links r)
                            :strict (filterv #(= :member (first %)) (:keys r))
                            :pair   (when (:mark? r) (:pair r))})))]
           :when (every? seq per)
           combo (combinations per)]
       (let [strict (into [] (mapcat :links) (filter :keys combo))]
         (cond-> {:keys  (into #{[:cover [whole parts] kind]} (mapcat :keys) combo)
                  :links (into [] (remove (fn [[a b]] (= a b)))
                               (cons [s whole] (mapcat :links combo)))}
           (seq strict)                  (assoc :strict-links strict)
           (some (comp seq :strict) combo) (assoc :strict-keys (into #{} (mapcat :strict) combo))
           (some :pair combo)            (assoc :pairs (into [] (keep :pair) combo))))))))

(defn routes
  "Each way the declarations convict the membership nogood `ng` over the unscoped
  taxonomy, as `tax/separation-routes` answers for a `:disjoint` one: `{:keys #{k} :links
  [[sub super]] :pair [x y]}`, the flat-cache keys read, the `genl` subsumptions climbed
  and the separated pair.  For a `:cover` one, a cover over a whole above the held type
  with a member denial at or above each part: the cover's key, the subsumption from the
  held type to the whole and from each part to the first such denial's type, and no
  pair, and for a part a held type's separation denies, the separation's keys and links
  with the soundness rule's `:strict-links`, `:strict-keys` and `:pairs` (`cover-routes`).
  A `:disjoint` one takes each cover route of its two memberships besides, since
  `term-nogoods` keeps a cover refuted by the same two memberships as the one nogood.
  For a `:supertype` one, the subsumption from the held type to the denied type with no
  key, and each cover route besides.  Empty when the members are not one term's.
  Read over the write view `w` (`decide/write-view`): a route is a superset over every
  reader, and the placement decides which contexts see it."
  [w recs {:keys [members kind]}]
  (when-let [[_ pos neg] (member-types recs members)]
    (case kind
      :disjoint
      (when (= 2 (count pos))
        (let [[a b] (seq pos)]
          (concat (tax/separation-routes (:tax w) a b) (cover-routes w pos neg))))
      :supertype
      (when (= 1 (count pos) (count neg))
        (let [s (first pos) q (first neg)]
          (cond->> (cover-routes w pos neg)
            ((:genl?-global w) s q) (cons {:keys #{} :links [[s q]]}))))
      :cover
      (when (seq pos)
        (cover-routes w pos neg))
      nil)))

(defn- cover-convicted-at?
  "Does a reader with ancestor set `up` read a cover refuted by the held types `pos` and
  the denied types `neg` of one term: a held type `s` under a cover's whole each of whose
  parts a denial of it or of a supertype of it covers, or another held type `tax/disjoint?`
  over `up` separates from it, the exceptions the reader sees applied."
  [tax pos neg up]
  (boolean
   (some (fn [s]
           (some (fn [[_ parts]]
                   (every? (fn [p]
                             (or (some #(or (= p %) (tax/genl?-global tax p %)) neg)
                                 (some #(and (not= % s) (tax/disjoint? tax % p up)) pos)))
                           parts))
                 (distinct (tax/covers-over tax s nil))))
         pos)))

(defn exempt-at?
  "Does a reader with ancestor set `up` read no separation of the membership nogood
  `members` while the KB stores a `siblingDisjointException`: two memberships of one term
  whose types `tax/disjoint?` over `up` does not separate, or two or more memberships of
  one term refuting a cover through a separation the reader reads no cover refutation of
  (`cover-convicted-at?`).  An exception the reader sees removes a separation its
  placement reads, the one read below a placement that seeing more takes away
  (docs/taxonomy.md).  False for any other nogood."
  [tax recs members up]
  (boolean
   (and (tax/sib-exceptions? tax)
        (when-let [[_ pos neg] (member-types recs members)]
          (cond
            (and (empty? neg) (= 2 (count pos) (count members))
                 (tax/pair-separated? tax (first pos) (second pos)))
            (let [[a b] (seq pos)]
              (not (or (tax/disjoint? tax a b up) (tax/disjoint? tax b a up))))

            (< 1 (count pos))
            (not (cover-convicted-at? tax pos neg up))

            :else false)))))

(def family
  "The membership family's entry in `decide/registry`.  Recover keeps the entries of the
  terms `recovered-terms` names that `held?` holds, with no separation read: the first
  read after it tests every pair once (`sync-memberships`)."
  {:grounds   {:forced-monotonic '#{disjoint covering partition sibling_disjoint siblingDisjointException}}
   :note!     (fn [kb w sx stored?]
                (note-membership! kb w sx stored?)
                (when-not stored? (note-placement-left! kb sx)))
   :recovered (fn [kb _]
                (let [held (into {} (comp (map (fn [x] [x (term-entries kb x)]))
                                          (filter #(held? (second %))))
                                 (sort (recovered-terms kb)))]
                  (when (seq held)
                    (swap! (reasoning/nogood-candidates kb)
                           #(dissoc (reduce-kv add-held % held) ::sep-stamp ::genl-seen)))))
   :synced?   (fn [tax c] (or (empty? (::mem c)) (membership-synced? tax c)))
   :sync      (fn [kb w c] (sync-memberships kb w c))
   :handles   (fn [_ c] (:membership c))
   :holds?    (fn [_ c h] (contains? (:membership c) h))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N5 :label "Membership candidates" :kind :cache :keyed-by :term
  :holds-content? false
  :reads [:index :records :T1 :T2 :J5]
  :retired-by {:stored :K :removed :K :respelled :K :edge :K :declared :S :edge-belief :K
               :settle-pass :K :recover :R :image-install :R}
  :computed :read :imaged? :state
  :at [[:nogood-candidates :membership] [:nogood-candidates ::mem]
       [:nogood-candidates ::sep] [:nogood-candidates ::sep-stamp]
       [:nogood-candidates ::live-mem] [:nogood-candidates ::denials]
       [:nogood-candidates ::ngs] [:nogood-candidates ::types]
       [:nogood-candidates ::genl-seen] [:nogood-candidates ::no-pos]
       [:nogood-candidates ::moved]]
  :bound "the stored memberships and denials of each term holding two memberships, or a membership and a denial"
  :note "the unary members, each kept term's memberships and denials by type and its separated type pairs, read off a term's unary roster at its first write and at recover, and the kept terms under a type off the index; synced at a read by `tax/separation-stamp` and the relation moves (J5)"})
