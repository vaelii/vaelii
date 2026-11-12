;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.related
  "The declarations over related types: a `disjoint` over two types one reaches the other
  of through `genl`, a cover naming a part a `disjoint` separates from its whole, and an
  `orthogonal` over two types a `genl` edge or a separation contradicts.  See
  docs/reference.md, decision 8."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- declarations over related types -------------------------------------------
;;
;; A `disjoint` over related types forms one nogood per route of `genl` edges relating its
;; arguments, whose members are the declaration and the route's supporters, and the cover
;; and its `disjoint` a two-member one; every member is weighed (docs/reference.md, decision
;; 8).  Both are found from the declarations' own arguments, read off the argument trie: the
;; `disjoint`s naming a type at argument 1 or 2, and the covers naming a whole at argument
;; 1.  `:related-dj` keeps the `disjoint`s whose arguments are related over the unscoped
;; `genl` closure, read again for the declarations naming a type at or below the lower end
;; of an edge moved since the generation `::genl-seen` (`tax/moves-since`).
;; A cover pair, each `#{cover disjoint}` whose `disjoint` separates the whole from a part,
;; is read off the index for the side in hand (`pairs-of`, `pairs-holding`), and its
;; members are queued when either side arrives or leaves.
;;
;; An `(orthogonal a b)` says the two types are not disjoint and neither is a `genl` of the
;; other.  It exempts nothing, so what contradicts it is a `genl` edge between the two, one
;; type named twice, or a separation of the two or of two supertypes: a one-member clash of
;; the declaration, as a `disjoint` over related types is.  A fact whose functor the
;; unscoped `genl` closure places under `orthogonal` states one too
;; (`(genl siblingDisjointException orthogonal)`), and its own exemption from the
;; separation marks (`tax/exemption`) is the one a reader reads.  The stored ones are read
;; off the extents and the argument trie of those functors (`orthogonal-functors`), and
;; `:related-orth` keeps those whose pair some reader can read contradicted — related over
;; the unscoped `genl` closure, or separated by `disjointness-test` with no exemption
;; read.  One is read when it is stored, again with the `disjoint`s when an edge moves its
;; argument's ancestor set or its functor's place under `orthogonal`, and again when the
;; settle relabels a separation declaration over a type at or above an argument
;; (`reread-separated!`).

(def ^:private cover-functors
  "The functors of a whole-and-parts declaration (`tax/installed-edges`)."
  '[covering partition separating])

(defn- disjoint-args
  "`[a b]` for a stored fact `(disjoint a b)` over two distinct plain symbols, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 3 (count s)) (= 'disjoint (first s)))
      (let [[_ a b] s]
        (when (and (sx/plain-symbol? a) (sx/plain-symbol? b) (not= a b)) [a b])))))

(defn- cover-args
  "`[whole #{part}]` for a stored `covering`, `separating` or `partition` fact, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (some #{(first s)} cover-functors))
      (when-let [[w ps] (tax/cover-parts s)] [w (set ps)]))))

(defn- orthogonal-functors
  "`orthogonal` and every predicate the unscoped `genl` closure (in `w`) places
  under it, in content order."
  [w]
  (into (sorted-set) (filter symbol?) (conj ((:specs-global w) 'orthogonal) 'orthogonal)))

(defn- orthogonal-args
  "`[a b]` for a stored fact `(f a b)` over two plain symbols whose functor `f` states an
  `orthogonal` (`orthogonal-functors`), else nil.  `a` and `b` may be one symbol: a type
  subsumes itself, so that declaration is contradicted outright."
  [w sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 3 (count s)) (symbol? (first s))
               (or (= 'orthogonal (first s)) (contains? ((:specs-global w) 'orthogonal) (first s))))
      (let [[_ a b] s]
        (when (and (sx/plain-symbol? a) (sx/plain-symbol? b)) [a b])))))

;; ---- the stored declarations, read off the index ---------------------------------

(defn- read-args
  "`{h args}` for the stored records of the handles `hs` that `args-of` reads."
  [kb args-of hs]
  (let [recs (:records kb)]
    (into {} (keep (fn [h] (when-let [ab (some-> (p/get-sentex recs h) args-of)] [h ab]))) hs)))

(defn- naming
  "The handles of the stored facts of the functors `fs` naming a type of `ts` at one of
  the argument positions `ps` (`reads/as-stored-with-args`), or every stored fact of
  them (`reads/as-stored-with-functor`) when that set is the smaller."
  [kb fs ps ts]
  (let [idx (:index kb)
        all (transduce (map #(reads/stored-count-with-functor idx %)) + fs)]
    (if (<= all (* (count ps) (count ts)))
      (into #{} (mapcat #(reads/as-stored-with-functor idx %)) fs)
      (into #{} (for [f fs, pos ps, t ts, h (reads/as-stored-with-args idx f [[pos t]])] h)))))

(defn- disjoints
  "`{h [a b]}` of the stored `disjoint`s naming a type of `ts`, or every one when `ts` is
  nil."
  [kb ts]
  (read-args kb disjoint-args
             (if (nil? ts)
               (reads/as-stored-with-functor (:index kb) 'disjoint)
               (naming kb ['disjoint] [1 2] ts))))

(defn- orthogonals
  "`{h [a b]}` of the stored facts stating an `orthogonal` (`orthogonal-args`) that name a
  type of `ts`, or every one when `ts` is nil."
  [kb w ts]
  (let [fs (orthogonal-functors w)]
    (read-args kb #(orthogonal-args w %)
               (if (nil? ts)
                 (into #{} (mapcat #(reads/as-stored-with-functor (:index kb) %)) fs)
                 (naming kb fs [1 2] ts)))))

(defn- related?
  "Does one of the types `a`, `b` reach the other over the unscoped `genl` closure (in
  `w`, `decide/unscoped-closures`)?"
  [w [a b]]
  (let [genl? (:genl?-global w)] (or (genl? a b) (genl? b a))))

(defn- separates-part?
  "Does the `disjoint` over `[a b]` separate cover `[w ps]`'s whole from one of its parts?"
  [[w ps] [a b]]
  (or (and (= a w) (contains? ps b)) (and (= b w) (contains? ps a))))

(defn- pairs-of
  "The cover pairs, each `#{cover disjoint}`, the stored fact `sx` is a side of, the other
  side read off the index: a `disjoint`'s covers have one of its arguments as their
  whole, and a cover's `disjoint`s name its whole.  Empty for any other fact."
  [kb sx]
  (let [h (:id sx)]
    (if-let [ab (disjoint-args sx)]
      (into #{} (keep (fn [[cv wp]] (when (separates-part? wp ab) (hash-set cv h))))
            (read-args kb cover-args (naming kb cover-functors [1] ab)))
      (if-let [[whole _ :as wp] (cover-args sx)]
        (into #{} (keep (fn [[d ab]] (when (separates-part? wp ab) (hash-set h d))))
              (disjoints kb [whole]))
        #{}))))

(defn- pairs-possible?
  "Does the store hold a `disjoint` and a cover, which a cover pair needs?  Count reads."
  [kb]
  (let [idx (:index kb)]
    (and (pos? (reads/stored-count-with-functor idx 'disjoint))
         (boolean (some #(pos? (reads/stored-count-with-functor idx %)) cover-functors)))))

(defn- every-pair
  "Every cover pair the store holds: each stored cover's (`pairs-of`)."
  [kb]
  (if (pairs-possible? kb)
    (let [recs (:records kb)]
      (into #{} (comp (mapcat #(reads/as-stored-with-functor (:index kb) %))
                      (keep #(p/get-sentex recs %))
                      (mapcat #(pairs-of kb %)))
            cover-functors))
    #{}))

(defn- pairs-holding
  "The cover pairs the stored fact `h` is a side of (`pairs-of`)."
  [kb h]
  (if (pairs-possible? kb)
    (or (some->> (p/get-sentex (:records kb) h) (pairs-of kb)) #{})
    #{}))

(defn- noted
  "`c` with the handles `hs` journaled (`journal/note`) and queued under `::moved` for the
  settle to place their nogoods again (`take-moved!`)."
  [c hs]
  (-> (journal/note c hs) (update ::moved (fnil into #{}) hs)))

(defn- contradicted-somewhere?
  "Can some reader read the `orthogonal` over `[a b]` contradicted?  One type twice, a
  `genl` edge between the two over the unscoped closure, or a separation
  `disjointness-test` reads with no exception exempting it — the superset
  over every reader that the placements scope."
  [w [a b]]
  (or (= a b)
      (related? w [a b])
      (boolean ((tax/disjointness-test (:tax w) a nil (constantly false)) b))))

(defn- orthogonals-under
  "`{h [a b]}` of the stored `orthogonal`s with an argument at or below one of the types
  `ends` over the unscoped `genl` closure: those a separation over `ends` can contradict
  or exempt.  Reads the stored ones whole, each argument by one walk up to the first of
  `ends` over one memo (`tax/genls-global-meets?`), or those naming a specialization of
  `ends`, whichever is fewer."
  [kb w ends]
  (when (seq ends)
    (let [idx  (:index kb)
          ends (set ends)
          n    (transduce (map #(reads/stored-count-with-functor idx %)) + (orthogonal-functors w))]
      (if (< n (* 4 (count ends)))
        (let [missed (volatile! #{})]
          (into {} (filter (fn [[_ ab]] (some #((:genls-global-meets? w) % ends missed) ab)))
                (orthogonals kb w nil)))
        (orthogonals kb w (into #{} (mapcat (:specs-global w)) ends))))))

(defn- reread-orthogonals
  "`c` with each `orthogonal` of `orths` (`{h [a b]}`, `[a b]` nil for a fact no longer
  stating one) in `:related-orth` exactly when it is contradicted somewhere, every one
  journaled."
  [w c orths]
  (-> c
      (assoc :related-orth
             (reduce-kv (fn [r h ab] (if (and ab (contradicted-somewhere? w ab)) (conj r h) (disj r h)))
                        (or (:related-orth c) #{}) orths))
      (journal/note (keys orths))))

(defn- edge-fact?
  "Is the stored fact `sx` a `genl` edge between two plain symbols, or a cover, which
  installs its parts' edges (`tax/installed-edges`)?"
  [sx]
  (let [s (:sentence sx)]
    (boolean (and (nil? (:antecedent sx)) (seq? s)
                  (or (and (= 'genl (first s)) (= 3 (count s)) (sx/plain-symbol? (second s)))
                      (cover-args sx))))))

(defn- sxs-kind
  "The kind of the related-types nogood over the stored facts `sxs`: `:cover` for a cover
  beside a `disjoint`, `:disjoint` for one `disjoint` alone or beside the `genl` edges or
  covers of a route relating its arguments, else nil.  A `disjoint` whose route is one cover
  is the cover pair."
  [sxs]
  (let [[ds others] ((juxt filter remove) disjoint-args sxs)]
    (when (= 1 (count ds))
      (cond
        (and (= 1 (count others)) (cover-args (first others))) :cover
        (every? edge-fact? others)                             :disjoint))))

(defn kind-of
  "The kind of the related-types nogood over the member handles `ms`, read off their
  sentences through the unscoped closures `w`: `:orthogonal` for one fact stating an
  `orthogonal` (`orthogonal-args`), else `sxs-kind`'s, else nil."
  [w recs ms]
  (let [sxs (keep #(p/get-sentex recs %) ms)]
    (when (= (count sxs) (count ms))
      (or (when (= 1 (count sxs)) (when (orthogonal-args w (first sxs)) :orthogonal))
          (sxs-kind sxs)))))

(defn- edge-routes
  "Every acyclic route of `genl` edges from `lower` up to `upper` over the unscoped
  relation, each as the supporter handles of its edges, one route per believed supporter of
  each edge (`tax/genl-edge-supporters`): a `genl` fact and a cover installing one edge
  are two routes, and neither covers the other.  The walk takes only the steps that end
  at `upper` or below it, read over the unscoped closures `w` as `:related-dj` is kept;
  the settle places each nogood at the readers that see its members
  (`chain/place-related!`)."
  [w lower upper]
  (let [tax   (:tax w)
        genl? (:genl?-global w)]
    (letfn [(walk [u seen]
              (if (= u upper)
                [#{}]
                (for [v     (tax/direct-genls-global tax u)
                      :when (and (not (contains? seen v))
                                 (or (= v upper) (genl? v upper)))
                      h     (tax/genl-edge-supporters tax u v nil)
                      route (walk v (conj seen v))]
                  (conj route h))))]
      (walk lower #{lower}))))

(defn- edge-sets
  "The member sets of the `disjoint` `h` over `[a b]`: the declaration and the supporters of
  one route of `genl` edges from either argument up to the other (`edge-routes`), one set
  per route."
  [w h [a b]]
  (into #{} (for [[s t] [[a b] [b a]]
                  :when ((:genl?-global w) s t)
                  route (edge-routes w s t)
                  :when (seq route)]
              (conj route h))))

(defn- spanned
  "The `disjoint`s of `c`'s `:related-dj` that a route through one of the `genl` edges
  `es` can relate: one argument at or below the edge's lower end and the other at or above
  its upper end.  A supporter arriving at or leaving an edge that stays active moves no
  edge (`tax/moves-since`) and still adds or removes a route."
  [kb w c es]
  (let [genl? (:genl?-global w)
        sub?  (fn [x y] (or (= x y) (genl? x y)))
        hit?  (fn [[a b]] (some (fn [[s t]] (or (and (sub? a s) (sub? t b))
                                                (and (sub? b s) (sub? t a))))
                                es))]
    (into [] (keep (fn [[h ab]] (when (hit? ab) h)))
          (read-args kb disjoint-args (:related-dj c)))))

(defn- note-declaration!
  "Keep the related-types rows in step with the fact `sx` arriving (`stored?`) or leaving.
  A `disjoint` enters `:related-dj` when `::genl-seen` holds a generation it is read under
  (`sync-related` reads every one otherwise) and its arguments are related, and leaves it
  with its record; a `disjoint` or a cover arriving or leaving queues the members of the
  cover pairs it is a side of, read off the stored other side it names (`pairs-of`), and a
  `genl` edge or a cover arriving or leaving queues the `disjoint`s of `:related-dj` its
  edges can relate (`spanned`).  A fact stating an
  `orthogonal` enters `:related-orth` likewise when it is contradicted somewhere, and a
  `siblingDisjointException` either way queues the contradicted `orthogonal`s with an
  argument at or below one of its own: its exemption moves where they are placed.  A
  `(contradicts …)` leaving queues its members for the settle to place again
  (`take-moved!`): a `genlCx` edge under the placement can have left with it.  Reads
  nothing for any other fact."
  [kb w sx stored?]
  (let [cands (reasoning/nogood-candidates kb)
        h     (:id sx)
        f     (nm/functor (:sentence sx))]
    (cond
      (and (not stored?) (= 'contradicts f))
      (let [hs (into #{} (keep sx/handle-id) (rest (:sentence sx)))]
        (when (kind-of w (:records kb) hs)
          (swap! cands update ::moved (fnil into #{}) hs)))

      (disjoint-args sx)
      (let [ab  (disjoint-args sx)
            prs (into #{} cat (pairs-of kb sx))]
        (swap! cands (fn [c]
                       (cond-> (cond
                                 (not stored?)
                                 (-> c (update :related-dj #(some-> % (disj h))) (noted [h]))

                                 (and (::genl-seen c) (related? w ab))
                                 (-> c (update :related-dj (fnil conj #{}) h) (noted [h]))

                                 :else c)
                         (seq prs) (noted prs)))))

      (edge-fact? sx)
      (let [prs (into #{} cat (pairs-of kb sx))
            sps (when (seq (:related-dj @cands))
                  (spanned kb w @cands (tax/installed-edges (:sentence sx))))]
        (when (or (seq prs) (seq sps)) (swap! cands noted (into prs sps))))

      :else
      (let [ab (orthogonal-args w sx)]
        (when (or ab (and (not stored?) (contains? (:related-orth @cands) h)))
          (let [sib (when (= 'siblingDisjointException f)
                      (keys (orthogonals-under kb w ab)))]
            (swap! cands
                   (fn [c]
                     (let [c (if stored?
                               (if (and (::genl-seen c) (contradicted-somewhere? w ab))
                                 (-> c (update :related-orth (fnil conj #{}) h) (noted [h]))
                                 c)
                               (-> c (update :related-orth #(some-> % (disj h))) (noted [h])))]
                       (noted c (filter #(contains? (:related-orth c) %) sib)))))))))))

(defn- related-synced?
  "Is `c`'s `:related-dj` and `:related-orth` read under the `genl` generation as it
  stands?"
  [tax c]
  (= (tax/relation-gen tax :genl) (::genl-seen c)))

(defn- sync-related
  "`c` with `:related-dj` and `:related-orth` read again under the `genl` closure as it
  stands: every declaration when none was read or the relation was rebuilt from nothing,
  else those naming a type at or below the lower end of an edge that moved
  (`tax/moves-since`), since no other type's closure moved, the facts of a predicate at or
  below such a lower end, which the move can put under `orthogonal`, and the contradicted
  `orthogonal`s, whose functor it can take out.  The ones related or contradicted before
  or after are queued, since an edge moving moves their routes.  Reads the store only
  while it holds a `disjoint` or an `orthogonal`."
  [kb w c]
  (let [tax   (:tax w)
        idx   (:index kb)
        g     (tax/relation-gen tax :genl)
        seen  (::genl-seen c)
        full  (or (nil? seen) (< g seen))
        fs    (orthogonal-functors w)
        none? (and (zero? (reads/stored-count-with-functor idx 'disjoint))
                   (empty? (:related-orth c))
                   (not-any? #(pos? (reads/stored-count-with-functor idx %)) fs))]
    (if none?
      (assoc c :related-dj #{} ::genl-seen g)
      (let [types (when-not full
                    (into #{} (mapcat (:specs-global w)) (tax/moves-since tax :genl seen)))
            djs   (disjoints kb types)
            ;; the facts of a predicate the move can put under `orthogonal` or take out
            ;; from under it: those stored, and those `:related-orth` holds
            under (when-not full
                    (let [recs (:records kb)
                          fn-of #(some-> (p/get-sentex recs %) :sentence nm/functor)]
                      (-> (into #{} (comp (filter #(contains? types %))
                                          (mapcat #(reads/as-stored-with-functor idx %)))
                                fs)
                          (into (filter #(contains? types (fn-of %))) (:related-orth c)))))
            orths (if full
                    (orthogonals kb w nil)
                    (merge (zipmap under (repeat nil))
                           (read-args kb #(orthogonal-args w %) under)
                           (orthogonals kb w types)))
            rel   (reduce-kv (fn [r h ab] (if (related? w ab) (conj r h) (disj r h)))
                             (if full #{} (or (:related-dj c) #{}))
                             djs)
            old   c
            c     (as-> c c
                    (assoc c :related-dj rel ::genl-seen g)
                    (cond-> c full (assoc :related-orth #{}))
                    (reread-orthogonals w c orths)
                    (journal/note c (if full (concat (:related-dj old) (keys djs)) (keys djs))))
            held? (fn [c h] (or (contains? (:related-dj c) h) (contains? (:related-orth c) h)))]
        (update c ::moved (fnil into #{})
                (filter #(or (held? c %) (held? old %)))
                (concat (when full (concat (:related-dj old) (:related-orth old)))
                        (keys djs) (keys orths)))))))

(defn reread-separated!
  "Read again whether each stored `orthogonal` with an argument at or below one of the
  types `ends` is contradicted somewhere, and return those contradicted before or after:
  the ones whose routes a separation over `ends` moving can move.  The settle calls this
  for the separation declarations it relabels (`chain/place-related!`)."
  [kb w ends]
  (let [orths (orthogonals-under kb w ends)]
    (when (seq orths)
      (let [cands     (reasoning/nogood-candidates kb)
            [old new] (swap-vals! cands #(reread-orthogonals w % orths))]
        (filterv #(or (contains? (:related-orth old) %) (contains? (:related-orth new) %))
                 (sort (keys orths)))))))

(defn moved?
  "Has the index queued a declaration whose nogoods the settle places again
  (`take-moved!`)?"
  [c]
  (boolean (seq (::moved c))))

(defn orthogonals?
  "Does the store hold a fact of `orthogonal` or of a predicate under it, which a
  separation declaration the settle relabels can contradict (`reread-separated!`)?
  Count reads."
  [kb w]
  (let [stored? #(pos? (reads/stored-count-with-functor (:index kb) %))]
    (boolean (or (stored? 'orthogonal)
                 (some #(and (symbol? %) (not= 'orthogonal %) (stored? %))
                       ((:specs-global w) 'orthogonal))))))

(defn take-moved!
  "The declarations whose related-types nogoods moved since the last call, and the queue
  emptied (`noted`)."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::moved)]
    (::moved old #{})))

(defn held?
  "Can the related-types family hold a nogood: a `disjoint` of `:related-dj` or an
  `orthogonal` of `:related-orth` in the candidate index `c`, or a `disjoint` and a cover
  stored (`pairs-possible?`)?"
  [kb c]
  (boolean (or (seq (:related-dj c)) (seq (:related-orth c)) (pairs-possible? kb))))

(defn nogoods-holding
  "The related-types nogoods with the declaration `h` among their members, each
  `{:members ms :kind k}`: for a `disjoint` of `:related-dj` in the candidate index `c`,
  one per route relating its arguments (`edge-sets`), kind `sxs-kind`'s; each cover pair
  holding `h`, read off the index (`pairs-holding`), kind `:cover`; and an `orthogonal`
  of `:related-orth`, kind `:orthogonal`.  `w` is the unscoped closures map
  (`decide/unscoped-closures`)."
  [kb w c h]
  (let [recs (:records kb)]
    (cond-> (mapv (fn [pr] {:members pr :kind :cover}) (pairs-holding kb h))
      (contains? (:related-dj c) h)
      (into (keep (fn [ms] (when-let [k (sxs-kind (keep #(p/get-sentex recs %) ms))]
                             {:members ms :kind k})))
            (some->> (p/get-sentex recs h) disjoint-args (edge-sets w h)))
      (contains? (:related-orth c) h) (conj {:members #{h} :kind :orthogonal}))))

(defn routes
  "Each way the unscoped taxonomy convicts the related-types nogood `ng`, as
  `{:links [[sub super]] :keys #{k} :pair [x y]}` (`tax/separation-routes`' shape): a
  `disjoint` and the edges of a route, or a cover pair, none, since every fact it reads
  is a member; an `orthogonal` over one type twice, none, and
  otherwise the subsumption between the two in each direction the closure holds and
  each separation of the two (`tax/separation-routes`).  A fact whose functor `f` is a
  `genl` of `orthogonal` adds the subsumption `f` to `orthogonal` to each route.  `w` is
  `decide/unscoped-closures`'s."
  [w recs {:keys [members kind]}]
  (let [sx    (p/get-sentex recs (first members))
        genl? (:genl?-global w)
        links (fn [[a b]] (cond-> []
                            (genl? a b) (conj {:links [[a b]]})
                            (genl? b a) (conj {:links [[b a]]})))]
    (case kind
      (:disjoint :cover) [{:links []}]
      :orthogonal (when-let [[a b :as ab] (orthogonal-args w sx)]
                    (let [f  (nm/functor (:sentence sx))
                          rs (if (= a b)
                               [{:links []}]
                               (concat (links ab) (tax/separation-routes (:tax w) a b)))]
                      (if (= 'orthogonal f)
                        rs
                        (map #(update % :links (fnil conj []) [f 'orthogonal]) rs))))
      nil)))

(defn exempt-at?
  "Does a reader with ancestor set `up` read no conviction of the `orthogonal` nogood
  `members`: one declaration over two distinct types no `genl` edge relates over the
  unscoped closure (`w`, `decide/unscoped-closures`) and `tax/disjoint?` over `up` does not
  separate.  A `siblingDisjointException` the reader sees removes a mark separation its
  placement reads, as for a membership nogood (`membership/exempt-at?`).  False for any
  other nogood."
  [w recs members up]
  (boolean
   (when (= 1 (count members))
     (when-let [[a b :as ab] (some->> (p/get-sentex recs (first members)) (orthogonal-args w))]
       (let [tax (:tax w)]
         (and (not= a b) (not (related? w ab))
              (not (tax/disjoint? tax a b up)) (not (tax/disjoint? tax b a up))))))))

(def family
  "The related-types family's entry in `decide/registry`.  It keeps no stored declaration
  and no cover pair: a cover pair is read off the index (`pairs-holding`, `every-pair`),
  and recover leaves `::genl-seen` unread, so the first read reads every declaration
  (`sync-related`).  Each nogood of it is placed as a conclusion
  (`chain/place-related!`)."
  {:note!     (fn [kb w sx stored?] (note-declaration! kb w sx stored?))
   :synced?   related-synced?
   :sync      sync-related
   :handles   (fn [kb c] (concat (:related-dj c) (apply concat (every-pair kb)) (:related-orth c)))
   :holds?    (fn [kb c h] (or (contains? (:related-dj c) h) (contains? (:related-orth c) h)
                               (boolean (seq (pairs-holding kb h)))))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N6 :label "Related declaration candidates" :kind :cache :keyed-by :handle
  :holds-content? false
  :reads [:index :records :T1 :J5]
  :retired-by {:stored :K :removed :K :respelled :K :edge :K :declared :K :edge-belief :K
               :settle-pass :K :recover :R :image-install :R}
  :computed :read :imaged? :state
  :at [[:nogood-candidates :related-dj] [:nogood-candidates :related-orth]
       [:nogood-candidates ::genl-seen] [:nogood-candidates ::moved]]
  :bound "one handle per stored `disjoint` and per stored fact stating an `orthogonal`"
  :note "the `disjoint`s over related types and the contradicted `orthogonal`s, read off the argument trie and the extents; synced at a read by the relation moves (J5), and an orthogonal read again by the separation declarations a settle relabels"})
