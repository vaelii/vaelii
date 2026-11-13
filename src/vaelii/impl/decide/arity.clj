;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.arity
  "The arity family: a stored tuple whose length breaks its functor's length is held in
  the `:out` forced set, and two exact bindings of one predicate, or of two predicates a
  `genl` edge relates, whose lengths differ are a pair the settle places one
  `contradicts` of in CxUniverse (`chain/sync-arity-pairs!`).  A `negates` declaration
  whose sides' lengths rule out a shared argument list is a one-member clash
  (`negates-clash`, `chain/sync-negates-lengths!`).  See docs/nmtms.md, \"The forced
  sets\", and docs/taxonomy.md, \"Arity\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.graph :as graph]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.predicates :as predicates]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- arity ---------------------------------------------------------------
;;
;; The bindings are the forced-monotonic spellings, read as storage (`sx/arity-binding`) off the
;; index family `:arity-binding` (docs/indexing.md, "The arity bindings").  What binds a
;; relation's length is one function, read the same at every context (`relation-length`).
;;
;; The exact lengths stored at or above a type, and its own exact lengths and `arityMin`
;; floors, are its entries in a weighted LRU (`entry`, register row N8), computed off the
;; binding family and the unscoped `genl` closure when a write or a settle reads them, a
;; type's lengths from its parents' held answers.  A binding write evicts the entries at
;; or below its predicate, and the relation moves (J5) of a `genl` edge evict every entry
;; at or below its lower end (`lengths-lru`), so an eviction costs a recompute and changes
;; no answer.
;;
;; A `:monotonic` membership `(T P)` binds P's length when T reaches an exact-arity class
;; `C` through `:monotonic` `genl` edges: the settle stores `(C P)` in CxUniverse, justified
;; by the membership and the edges (`class-paths`, `chain/sync-arity-classes!`), and the
;; stored class membership is a binding like any other.

(defn- values-of
  "The values of the `kind` pairs among `kinds` (`[kind value]`, as the family lists
  them)."
  [kinds kind]
  (into #{} (keep (fn [[k v]] (when (= k kind) v))) kinds))

(defn- exact-at
  "The exact lengths `p` stores: one probe of the bound predicates, and `p`'s kinds where
  it holds one."
  [kb p]
  (let [idx (:index kb)]
    (when (reads/stored-arity-bound? idx p)
      (values-of (reads/as-stored-arity-binding-kinds idx p) :exact))))

(defn- exact-bound?
  "Does `p` store an exact length?"
  [kb p]
  (boolean (seq (exact-at kb p))))

(defn membership-of
  "`[T x]` for a stored fact `sx` whose sentence is the positive membership `(T x)` of a
  symbol in a symbol type, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and sx (nil? (:antecedent sx)) (seq? s) (= 2 (count s)))
      (let [[t x] s]
        (when (and (symbol? t) (symbol? x) (not= 'not t)
                   (not (sx/variable? t)) (not (sx/variable? x)))
          [t x])))))

(def exact-classes
  "The exact-arity classes, each a type (`sx/exact-arity-classes`)."
  (set (keys sx/exact-arity-classes)))

;; ---- the length entries ------------------------------------------------------

(def lengths-cache-limit
  "The most weight one KB's length entries hold before the least recently used are
  evicted, an entry weighing one plus the lengths and floors it holds (`entry`): the
  shipped default the cache profile scales and the memory guard shrinks."
  262144)

(defn- weigh
  "An entry's weight: one, plus each length or floor it holds."
  ^long [v]
  (if (set? v) (inc (count v)) (+ 1 (count (:own v)) (count (:mins v)))))

(defn- evict-below!
  "Drop the entries of `lru` at or below a term of `ends`, a type's lengths and whether
  it reaches an exact-arity class (`[::reaches t]`): an end's specializations read where
  they number no more than `lru`'s entries (`tax/specs-global-within`), else each entry
  asked whether it reaches the end.  Unscoped, since the entries are the unscoped
  closure's, a superset over every reader (`decide/unscoped-closures`)."
  [tax lru ends]
  (doseq [end ends
          :let [n (caches/lru-size lru)]
          :when (pos? n)]
    (if-let [ts (tax/specs-global-within tax end n)]
      (caches/lru-evict! lru (into (vec ts) (map #(vector ::reaches %)) ts))
      (caches/lru-evict-if! lru (constantly true)
                            #(let [k (if (and (vector? %) (= ::reaches (first %))) (second %) %)]
                               (or (= end k) (and (symbol? k) (tax/genl?-global tax k end))))))))

(defn- lengths-lru
  "`kb`'s length entries, brought current with the taxonomy `tax`: emptied when its
  relations were rebuilt (`tax/relation-epoch`) or the `genl` generation went back, else
  rid of every entry at or below the lower end of an edge moved since the generation they
  last read (`tax/moves-since`)."
  [kb tax]
  (let [a   (reasoning/arity-lengths kb)
        g   (tax/relation-gen tax :genl)
        e   (tax/relation-epoch tax)
        lru @a
        {:keys [gen epoch]} lru]
    (cond
      (nil? lru)
      (reset! a (assoc (caches/weighted-lru
                        (caches/limit-thunk :arity-lengths lengths-cache-limit) weigh)
                       :gen g :epoch e))

      (and (= g gen) (= e epoch)) lru

      (or (not= e epoch) (< g (long gen)))
      (do (caches/lru-clear! lru) (reset! a (assoc lru :gen g :epoch e)))

      :else
      (do (evict-below! tax lru (tax/moves-since tax :genl gen)) (reset! a (assoc lru :gen g))))))

(defn reaches-class?
  "Does the type `t` reach an exact-arity class (`sx/exact-arity-classes`) over the
  unscoped closure, or is it one?  Held in `kb`'s length entries under `[::reaches t]`,
  which an edge moving at or above `t` evicts (`evict-below!`).  A type with no `genl`
  parent reaches no class but itself, which one adjacency read answers before the cache:
  a fresh functor's entry is a miss and fifteen closure probes."
  [kb t]
  (let [tax (reasoning/taxonomy kb)]
    (cond
      (contains? exact-classes t)               true
      (empty? (tax/direct-genls-global tax t))  false
      :else
      (let [lru (lengths-lru kb tax)
            k   [::reaches t]
            v   (caches/lru-get lru k)]
        (if (some? v)
          v
          (caches/lru-put! lru k (boolean (some #(tax/genl?-global tax t %) exact-classes))))))))

(defn class-paths
  "`{C [h …]}`: each exact-arity class `C` strictly above the type `t` that no other such
  class above `t` is below, with the supporters of one shortest path of `genl` edges from
  `t` up to it, an edge entering the walk through its first supporter `[h ctx]` that
  `ok?` takes, in content order of the supporters' contexts.  The walk enters only the
  types that reach an exact-arity class (`reaches-class?`), and expands parents in name
  order, so the path is a function of the edges and their supporters.  Empty for an
  exact-arity class `t`, which binds its members itself.  Unscoped: a relation's length
  is read the same at every context."
  [kb t ok?]
  (if (or (contains? exact-classes t) (not (reaches-class? kb t)))
    {}
    (let [tax   (reasoning/taxonomy kb)
          found (loop [q (conj clojure.lang.PersistentQueue/EMPTY [t []]), seen #{t}, acc {}]
                  (if-let [[x path] (peek q)]
                    (let [acc (cond-> acc
                                (and (contains? exact-classes x) (not (contains? acc x)))
                                (assoc x path))
                          nxt (into []
                                    (keep (fn [y]
                                            (when-let [sup (->> (tax/supporters tax [:genl x y])
                                                                (filter ok?)
                                                                (nm/sort-by-content-key #(nm/print-key (second %)) compare)
                                                                first)]
                                              [y (conj path (first sup))])))
                                    (nm/sort-by-content-key
                                     nm/print-key compare
                                     (filter #(and (not (contains? seen %)) (reaches-class? kb %))
                                             (tax/direct-genls-global tax x))))]
                      (recur (into (pop q) nxt) (into seen (map first) nxt) acc))
                    acc))]
      (into {} (remove (fn [[c]] (some #(and (not= c %) (tax/genl?-global-held tax % c)) (keys found))))
            found))))

(defn- own-entry
  "`{:own :mins :var?}`: `f`'s own exact lengths, `arityMin` floors and whether it stores
  a `variable_arity` binding, one probe of the bound predicates and `f`'s kinds where it
  holds one."
  [kb f]
  (let [idx   (:index kb)
        kinds (when (reads/stored-arity-bound? idx f) (reads/as-stored-arity-binding-kinds idx f))]
    {:own (values-of kinds :exact) :mins (values-of kinds :min)
     :var? (boolean (some #(= :var (first %)) kinds))}))

(defn- exact-xf
  "Each term's stored exact lengths (`exact-at`)."
  [kb]
  (mapcat #(exact-at kb %)))

(defn- lengths-of
  "The exact lengths stored at or above `f`, `f`'s unscoped `genl` closure cut to them,
  built from its parents' answers, which `kb`'s length entries hold by component
  representative (`tax/genls-global-union-held`).  Unscoped, since a relation's length is
  read the same at every context."
  [kb tax f]
  (let [lru (lengths-lru kb tax)]
    (tax/genls-global-union-held tax f (exact-xf kb) #(caches/lru-get lru %) #(caches/lru-put! lru %1 %2))))

(defn- below-lengths
  "The exact lengths stored at or below `f`, `f`'s unscoped `genl` closure downward cut to
  them, built from its children's answers, which the volatile map `memo` holds under
  `[::below node]` for one still taxonomy (`tax/specs-global-union-held`).  The map
  holds every answer for the caller's pass: a bounded store that evicts an answer
  mid-pass builds it again from the subtree below it, once per type above it."
  [kb tax f memo]
  (tax/specs-global-union-held tax f (exact-xf kb)
                               #(get @memo [::below %])
                               #(vswap! memo assoc [::below %1] %2)))

(defn- own-held
  "`{:own :mins}` of `f` (`own-entry`), held in `kb`'s length entries under `[::own f]`
  (`lengths-lru`), with `tax` the taxonomy."
  [kb tax f]
  (let [lru (lengths-lru kb tax)]
    (or (caches/lru-get lru [::own f])
        (caches/lru-put! lru [::own f] (own-entry kb f)))))

(defn- entry
  "`{:lengths :own :mins}` of `f`: the exact lengths stored at or above `f` (`lengths-of`),
  and `f`'s own exact lengths and `arityMin` floors (`own-held`)."
  [kb tax f]
  (assoc (own-held kb tax f) :lengths (lengths-of kb tax f)))

(defn- binding-pred
  "The predicate the stored record at `h` binds the length of (`sx/fact-arity-binding`), or nil."
  [kb h]
  (some-> (p/get-sentex (:records kb) h) sx/fact-arity-binding first))

(defn- entry-may-break?
  "Can `f`'s length entry (`entry`) hold a length or a floor?  Yes when its own part is
  held.  On a miss the entry would read `f` and each type above it, and it holds stored
  bindings only, so a KB storing none answers no off one count read and holds `f`'s
  empty own part, as `own-entry` would build it: a write of a fresh functor pays that
  read, where a functor written again pays the cached entry as before."
  [kb tax f]
  (let [lru (lengths-lru kb tax)]
    (or (some? (caches/lru-get lru [::own f]))
        (pos? (reads/stored-count-arity-bound (:index kb)))
        (do (caches/lru-put! lru [::own f] {:own #{} :mins #{} :var? false})
            false))))

(defn- breaks-entry?
  "Does a tuple of `n` arguments break a length of the entry `e` (`entry`): one stored at
  or above its functor, or its `arityMin`?"
  [{:keys [lengths mins]} n]
  (boolean (or (some #(not= n %) lengths) (some #(> % n) mins))))

(defn- held-bindings
  "`{:exact {n #{h}} :min {m #{h}} :var #{h}}`: the stored bindings of `p` in every
  context, each IN.  Every context, since a relation's length is read the same at every
  context (`relation-length`); an `except` of a binding hides its sentence from reads and
  leaves the length bound."
  [kb p]
  (let [tms (reasoning/tms kb)
        idx (:index kb)]
    (if-not (reads/stored-arity-bound? idx p)
      {}
      (reduce (fn [m [h kind v _]]
                (if (jtms/in? tms h)
                  (if (= :var kind)
                    (update m :var (fnil conj #{}) h)
                    (update-in m [kind v] (fnil conj #{}) h))
                  m))
              {} (reads/as-stored-arity-bindings-global idx p)))))

(defn shape-length
  "The length an engine grammar term's `:shape` gives it (`predicates/shape-of`), with
  no grounds: `{:exact n}` for a fixed argument list, `{:min n}` for one with an
  `:optional` or `:variadic` tail; nil for a term with no shape."
  [q]
  (when-let [{:keys [args optional variadic]} (when (symbol? q) (predicates/shape-of q))]
    (assoc (if (or optional variadic) {:min (count args)} {:exact (count args)})
           :via q :grounds #{})))

(defn admits-length?
  "Does the length signature `outer` admit every length the signature `inner` admits?
  A signature is `{:exact n}`, admitting `n` alone, or `{:min m}`, admitting every length
  at or above `m`.  An exact `outer` admits an exact `inner` of its length and no floor;
  a floor `outer` admits an exact `inner` or a floor `inner` at or above it."
  [outer inner]
  (if-let [e (:exact outer)]
    (= e (:exact inner))
    (<= (long (:min outer)) (long (or (:exact inner) (:min inner))))))

(defn admits-shape?
  "Does a length binding of the engine term `q`, `kind` and `v` as `sx/arity-binding`
  answers them, admit every length `q`'s shape admits (`shape-length`, `admits-length?`)?
  An exact length agrees with an exact shape of that length, an `arityMin` floor with a
  shape whose shortest length is at or above it, and `variable_arity` with every shape.
  True for a term with no shape."
  [q kind v]
  (if-let [s (shape-length q)]
    (admits-length? (case kind :exact {:exact v} :min {:min v} :var {:min 0}) s)
    true))

(defn- reduce-own
  "The binding `q`'s own bindings `own` give it: under `variable_arity` its single
  `arityMin` floor, else its single exact length; nil for none, or for two."
  [q own]
  (cond
    (seq (:var own))   (when (= 1 (count (:min own)))
                         (let [[m hs] (first (:min own))] {:min m :via q :grounds hs}))
    (seq (:exact own)) (when (= 1 (count (:exact own)))
                         (let [[n hs] (first (:exact own))] {:exact n :via q :grounds hs}))))

(defn released?
  "Does a `variable_arity` binding of `q`, IN in any context, release it?  `relation-length`
  answers `{:min m}` or nil for such a `q` and does not report the release, which
  `admitsArgnum` and the integrity pass's undeclared-arity read beside it."
  [kb q]
  (boolean (seq (:var (held-bindings kb q)))))

(defn own-length
  "The length `q` itself is known to have, as `{:exact n}` or `{:min m}`, or nil, read the
  same at every context and with no `genl` closure read.  It comes from an engine term's
  `:shape` (`shape-length`), else `q`'s own IN bindings (`reduce-own`), else, for a
  `variable_arity` release with no single `arityMin`, the highest of its floors, zero
  without one.  An exact-arity class membership and a `:monotonic` membership reaching one
  are own bindings.  A length the bound predicates above `q` agree on is not `q`'s own
  (`relation-length` reads it), so the integrity pass's undeclared-arity and
  genl-arity-mismatch censuses read `own-length`."
  [kb q]
  (or (some-> (shape-length q) (dissoc :via :grounds))
      (let [own (held-bindings kb q)]
        (or (some-> (reduce-own q own) (dissoc :via :grounds))
            (when (seq (:var own))
              {:min (reduce max 0 (keys (:min own)))})))))

(defn unary-consistent?
  "Does `t`'s own arity admit one argument and no other: an engine term's `:shape` of
  exactly one, or, for any other term, no IN binding of a length other than one, no
  `variable_arity` release and no `arityMin` floor above one?  A type bound to one length
  and another admits neither, so a declaration naming it mints nothing.  The stored
  bindings, held in the length entries (`own-held`), answer when every one of them admits
  one, since then every IN subset of them does; otherwise the IN bindings answer
  (`held-bindings`), so no OUT binding decides.  No `genl` closure is read, so a length
  `t` inherits is not consulted (`mintable-type?`, docs/argtypes.md)."
  [kb t]
  (if-let [s (shape-length t)]
    (= 1 (:exact s))
    (let [ok? (fn [exacts var? mins]
                (and (every? #(= 1 %) exacts) (not var?) (every? #(<= (long %) 1) mins)))
          {:keys [own mins var?]} (own-held kb (reasoning/taxonomy kb) t)]
      (or (ok? own var? mins)
          (let [{:keys [exact var min]} (held-bindings kb t)]
            (ok? (keys exact) (seq var) (keys min)))))))

(defn mintable-type?
  "Is `t` a type a membership can be minted in: a symbol other than `thing` whose own
  arity admits one argument (`unary-consistent?`)?  A type is a unary predicate, so
  a declared type with no arity statement is one, and the declaration that mints in it
  entails its `unary_predicate` membership (`special/entail-existing`).  `thing` mints
  nothing: a membership in it says nothing about the term.  One read of `t`'s stored
  arity bindings, with no `genl` closure read (docs/argtypes.md, \"Where it does not
  mint\")."
  [kb t]
  (and (symbol? t) (not (sx/variable? t)) (not= 'thing t) (unary-consistent? kb t)))

(defn- bound-above
  "The predicates at or above `q` storing an exact or `variable_arity` binding, `q` left
  out unless `self?`, over the unscoped closure: a relation's length is read the same at
  every context (docs/taxonomy.md, \"Arity\"), so the cut reads every `genl` edge whoever
  can see it.  `tax/genls-global-union` probes the bound predicates once per type above
  `q`."
  ([kb q] (bound-above kb q false))
  ([kb q self?]
   (let [idx    (:index kb)
         bound? (fn [p] (and (reads/stored-arity-bound? idx p)
                             (some (fn [[kind]] (not= :min kind))
                                   (reads/as-stored-arity-binding-kinds idx p))))]
     (if (pos? (reads/stored-count-arity-bound idx))
       (cond-> (tax/genls-global-union (reasoning/taxonomy kb) q (filter bound?) (volatile! {}))
         (not self?) (disj q))
       #{}))))

(defn- with-write
  "The bindings `held` (`held-bindings`'s map) with the bindings `added` beside them, in
  the same shape."
  [held added]
  (merge-with (fn [a b] (if (set? a) (into a b) (merge-with into a b))) held added))

(defn- write-kinds
  "The `[kind value]` pairs of the bindings `added` (`held-bindings`'s map), as
  `reads/as-stored-arity-binding-kinds` lists them."
  [{:keys [exact min var]}]
  (cond-> (into #{} (concat (map #(vector :exact %) (keys exact)) (map #(vector :min %) (keys min))))
    (seq var) (conj [:var nil])))

(defn relation-length
  "What binds `q`'s length, as `{:exact n :via p}` or `{:min m :via q}`, or nil, read the
  same at every context: an engine term's `:shape` (`shape-length`), else `q`'s own
  bindings (`reduce-own`), else the one exact length the bound predicates above it agree
  on, none of them `variable_arity`, with `:via` the first of them by name.  With
  `grounds?`, the result also carries `:grounds #{h}`: the bindings stating the length,
  an engine term's own bindings stating its shape's length.  The rule is
  docs/taxonomy.md's \"Arity\"; `why-not` reads the grounds of an inert tuple's length
  (`inert-binding`).

  With `write`, the length a write not yet stored would give `q` (`write-breaks`):
  `:held` maps a predicate to the bindings the write adds to it, in `held-bindings`'
  shape, and `:above` holds the predicates the write puts above `q`."
  ([kb q] (relation-length kb q false nil))
  ([kb q grounds?] (relation-length kb q grounds? nil))
  ([kb q grounds? write]
   (or (when-let [s (shape-length q)]
         (if-not grounds?
           (dissoc s :grounds)
           ;; the shape decides; an own binding stating the shape's length is a ground, and
           ;; one stating another length binds nothing
           (let [own (held-bindings kb q)]
             (assoc s :grounds (or (if (:exact s)
                                     (get-in own [:exact (:exact s)])
                                     (get-in own [:min (:min s)]))
                                   #{})))))
       (let [held-of (if write
                       (fn [p] (with-write (held-bindings kb p) (get-in write [:held p])))
                       #(held-bindings kb %))
             own     (held-of q)]
         (if (or (seq (:var own)) (seq (:exact own)))
           (cond-> (reduce-own q own) (not grounds?) (dissoc :grounds))
           ;; the predicates above grouped by the exact lengths they store, each group in
           ;; name order, the smallest group first: a second length leaves `q` unbound, so
           ;; the rest go unread, and the first believed binding of a group names `:via`
           (let [idx    (:index kb)
                 cut    (cond-> (bound-above kb q)
                          write (into (filter #(and (not= q %)
                                                    (some (fn [[k]] (not= :min k))
                                                          (write-kinds (held-of %)))))
                                      (:above write)))
                 kinds  (into {} (map (fn [p] [p (cond-> (reads/as-stored-arity-binding-kinds idx p)
                                                   (get-in write [:held p])
                                                   (-> set (into (write-kinds (get-in write [:held p])))))]))
                              cut)
                 by-len (update-vals
                         (reduce (fn [m p] (reduce #(update %1 %2 (fnil conj []) p) m
                                                   (values-of (kinds p) :exact)))
                                 {} cut)
                         sort)
                 seen   (volatile! {})
                 held   (fn [p] (if-let [e (find @seen p)]
                                  (val e)
                                  (let [b (held-of p)]
                                    (vswap! seen assoc p b) b)))
                 holds? (fn [n p] (contains? (:exact (held p)) n))
                 vias   (reduce (fn [acc [n ps]]
                                  (if-let [p (first (filter #(holds? n %) ps))]
                                    (cond-> (assoc acc n p) (seq acc) reduced)
                                    acc))
                                {} (sort-by (comp count val) by-len))]
             (when (and (= 1 (count vias))
                        (not-any? #(and (contains? (kinds %) [:var nil]) (seq (:var (held %)))) cut))
               (let [[n via] (first vias)]
                 (cond-> {:exact n :via via}
                   grounds? (assoc :grounds (into #{} (mapcat #(get (:exact (held %)) n))
                                                  (filter #(holds? n %) (get by-len n)))))))))))))

(defn- breaks?
  "Does a tuple of `n` arguments break `binding`?"
  [binding n]
  (boolean (or (and (:exact binding) (not= n (:exact binding)))
               (and (:min binding) (< n (:min binding))))))

;; ---- the inert tuples ------------------------------------------------------
;;
;; A stored tuple of `q` whose length breaks `q`'s length (`relation-length`) is a member
;; of the `:out` forced set: never believed, it forms no nogood and fires no rule
;; (docs/nmtms.md, "The forced sets").  `checks/force-sentex!` decides a tuple as it is
;; stored (`inert-tuple?`).  A binding stored, removed or relabelled queues its predicate
;; under `::bound`, and the settle refreshes the shapes of every functor at or below a
;; queued predicate or the lower end of a `genl` edge moved since `::gen`
;; (`drain!`).  `::out` holds the lengths of each functor whose tuples are in `:out`, so a
;; refresh reads a shape's tuples only when the shape moves, or when a tuple stored since
;; the last refresh was decided inert on a shape `::out` does not hold (`::fresh`).

(defn- shape-breaks?
  "Does a tuple of `n` arguments of `q` break `q`'s length (`relation-length`)?  For a
  functor with no engine shape, the length entry (`entry`) answers no without a label read
  where no length stored at or above `q` and no floor of `q` differs from `n`
  (`entry-may-break?`)."
  [kb tax q n]
  (boolean (and (or (predicates/shape-of q)
                    (and (entry-may-break? kb tax q) (breaks-entry? (entry kb tax q) n)))
                (breaks? (relation-length kb q) n))))

(defn inert-tuple?
  "Does the stored fact `sx` break its functor's length (`shape-breaks?`), which holds it
  in the `:out` forced set?  A true answer for a shape `::out` does not record queues the
  shape under `::fresh`, and the next refresh reads each of its tuples
  (`refresh-shapes!`): the tuples stored before it can wait on a queued binding."
  [kb sx]
  (if-let [[q n] (sx/fact-shape sx)]
    (let [out?  (shape-breaks? kb (reasoning/taxonomy kb) q n)
          cands (reasoning/nogood-candidates kb)]
      (when (and out? (not (contains? (get-in @cands [::out q]) n)))
        (swap! cands update-in [::fresh q] (fnil conj #{}) n))
      out?)
    false))

(defn broken-binding
  "The binding a tuple of `n` arguments of `q` breaks, as `{:length n :via p :grounds [h …]
  :route [h …]}` with `:length` an exact length, or `{:min m …}` for a floor, or nil when
  it breaks none (`shape-breaks?`, then `relation-length` with its grounds).  `:route`
  holds the IN supporters of one path of `genl` edges from `q` up to `:via`
  (`tax/genl-path-edges`), empty for a length `q` binds itself."
  [kb q n]
  (let [tax (reasoning/taxonomy kb)
        b   (when (shape-breaks? kb tax q n) (relation-length kb q true))
        tms (reasoning/tms kb)]
    (when (breaks? b n)
      (cond-> {:via     (:via b)
               :grounds (vec (sort (:grounds b)))
               :route   (if (= q (:via b))
                          []
                          (into [] (comp (mapcat #(keys (tax/supporters tax (into [:genl] %))))
                                         (filter #(jtms/in? tms %))
                                         (distinct))
                                (tax/genl-path-edges tax q (:via b))))}
        (:exact b) (assoc :length (:exact b))
        (:min b)   (assoc :min (:min b))))))

(defn inert-binding
  "The binding a stored tuple `sx` in the `:out` forced set breaks (`broken-binding`), or
  nil when `sx` breaks none."
  [kb sx]
  (when-let [[q n] (sx/fact-shape sx)]
    (broken-binding kb q n)))

(defn- refresh-shapes!
  "Move the stored tuples of `q` into or out of the `:out` forced set for each length
  whose `shape-breaks?` answer differs from what `::out` records, or that `check` names,
  and record the answers.  Any other shape reads no tuple.  Answers the tuples taken out
  of `:out`.  A tuple of a `not_assertible` predicate stays in `:out`: the mark is forced
  decontextualized and forced monotonic, so its KB-wide reading is every reader's."
  [kb tax q check]
  (let [idx   (:index kb)
        tms   (reasoning/tms kb)
        cands (reasoning/nogood-candidates kb)
        was   (get-in @cands [::out q] #{})
        now   (into #{} (filter #(shape-breaks? kb tax q %)) (reads/as-stored-shape-lengths idx q))
        released (reduce (fn [acc n]
                           (let [on? (contains? now n)
                                 hs  (into [] (remove #(or (= on? (jtms/forced? tms :out %))
                                                           ;; the argument family or a mark holds it OUT
                                                           (and (not on?) (or (argument/held? kb %)
                                                                              (tax/has-prop? tax :not-assertible q)))))
                                           (reads/as-stored-shape-tuples-global idx q n))]
                             (when (seq hs) (jtms/set-forced tms :out hs on?))
                             (cond-> acc (not on?) (into hs))))
                         []
                         (sort (into check (remove #(= (contains? was %) (contains? now %))) (into was now))))]
    (when (not= was now)
      (swap! cands #(if (seq now) (assoc-in % [::out q] now) (update % ::out dissoc q))))
    released))

(defn- queue-bound!
  "Queue the bindings `bs` (`[p kind value]`, `sx/fact-arity-binding`) that moved under `::bound`,
  as `{p #{[kind value]}}` (`drain!`)."
  [kb bs]
  (when (seq bs)
    (swap! (reasoning/nogood-candidates kb) update ::bound
           #(reduce (fn [m [p k v]] (update m p (fnil conj #{}) [k v])) % bs))))

(defn relabelled-held
  "The handles among `hs` whose node this settle did not create, that the TMS still
  holds, and whose network label moved in this settle (`jtms/touched-in`): a created or
  removed binding is queued at the store and removal choke points (`note-arity!`), and a
  redundant justification moves no label, so only these are read."
  [kb hs]
  (let [tms (reasoning/tms kb)
        new (jtms/touched-new tms)
        was (jtms/touched-in tms)]
    (filter #(and (not (contains? new %)) (jtms/known-datum? tms %)
                  (not= (contains? was %) (jtms/network-in? tms %)))
            hs)))

(defn relabel-owed?
  "Does `note-relabelled!` read a record among the relabelled handles `hs`?"
  [kb hs]
  (boolean (seq (relabelled-held kb hs))))

(defn- negates-declaration?
  "Is the stored record `sx` a `(negates P Q)` declaration?"
  [sx]
  (let [s (:sentence sx)]
    (and (nil? (:antecedent sx)) (seq? s) (= 'negates (first s)) (= 3 (count s)))))

(defn- queue-negates!
  "Queue the handles `hs` of `negates` declarations under `::neg`
  (`chain/sync-negates-lengths!`)."
  [kb hs]
  (when (seq hs)
    (swap! (reasoning/nogood-candidates kb) update ::neg (fnil into #{}) hs)))

(defn note-relabelled!
  "Queue the predicates of the bindings among the relabelled handles `hs` (`drain!`): a
  binding a rule concludes goes OUT with its antecedents, and a binding OUT binds nothing
  (`held-bindings`).  A relabelled `negates` declaration is queued under `::neg`."
  [kb hs]
  (let [sxs (into [] (keep #(p/get-sentex (:records kb) %)) (relabelled-held kb hs))]
    (queue-bound! kb (into [] (keep sx/fact-arity-binding) sxs))
    (queue-negates! kb (into [] (comp (filter negates-declaration?) (map :id)) sxs))))

(defn- note-arity!
  "A binding of `p` stored or removed: evict the length entries at or below `p` and its
  own entry, and queue the binding (`drain!`)."
  [kb sx]
  (when-let [[p :as b] (sx/fact-arity-binding sx)]
    (let [tax (reasoning/taxonomy kb)
          lru (lengths-lru kb tax)]
      (evict-below! tax lru [p])
      (caches/lru-evict! lru [[::own p]]))
    (queue-bound! kb [b])))

(defn- class-shaped?
  "Can the stored record `sx` move a class membership a metatype route derives: a
  membership of a type reaching an exact-arity class or of the class itself
  (`reaches-class?`)?  A `genl` edge moves them through the taxonomy whatever supports it
  (`take-class-ends!`)."
  [kb sx]
  (let [s (:sentence sx)]
    (boolean
     (and (nil? (:antecedent sx)) (seq? s) (= 2 (count s)) (symbol? (first s))
          (not (sx/variable? (first s))) (symbol? (second s))
          (reaches-class? kb (first s))))))

(defn note-class!
  "Queue the handle of `sx` under `::classes` when it is stored and `class-shaped?`, and
  drop it when it leaves, for the settle to sync the class memberships it moves
  (`take-classes!`)."
  [kb sx stored?]
  (let [cands (reasoning/nogood-candidates kb)]
    (if stored?
      (when (class-shaped? kb sx)
        (swap! cands update ::classes (fnil conj #{}) (:id sx)))
      (when (contains? (::classes @cands) (:id sx))
        (swap! cands update ::classes disj (:id sx))))))

(defn take-classes!
  "The handles queued under `::classes` since the last call (`note-class!`), the queue
  emptied."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::classes)]
    (::classes old #{})))

(defn classes-synced!
  "Drop the handles `hs` from `::classes`: their store path synced the class memberships
  they move (`chain/arity-classes-moved!`)."
  [kb hs]
  (when (seq (::classes @(reasoning/nogood-candidates kb)))
    (swap! (reasoning/nogood-candidates kb) update ::classes #(reduce disj % hs))))

(defn take-class-ends!
  "The lower ends of the `genl` edges moved since the last call (`tax/moves-since`),
  whatever sentence supports each edge, the generation read recorded under `::class-gen`.
  Every logged end on the first call and after the relation was rebuilt."
  [kb]
  (let [tax     (reasoning/taxonomy kb)
        g       (tax/relation-gen tax :genl)
        e       (tax/relation-epoch tax)
        [old _] (swap-vals! (reasoning/nogood-candidates kb) assoc ::class-gen g ::class-epoch e)
        from    (::class-gen old)]
    (cond
      (or (nil? from) (not= e (::class-epoch old)) (< g (long from))) (tax/moves-since tax :genl -1)
      (= g from)                                                       #{}
      :else                                                            (tax/moves-since tax :genl from))))

(defn classes-queued?
  "Does the settle owe a class sync: a stored record queued one (`take-classes!`), or a
  `genl` edge moved since `::class-gen` (`take-class-ends!`)?"
  [tax c]
  (boolean (or (seq (::classes c))
               (not= (::class-gen c) (tax/relation-gen tax :genl))
               (not= (::class-epoch c) (tax/relation-epoch tax)))))

(defn- lengths-moved?
  "Does the settle owe a refresh (`drain!`): the shapes owed whole, a queued predicate, or
  a `genl` edge moved since the generation `::gen` of the candidate index `c`?"
  [tax c]
  (boolean (or (::owed c) (seq (::bound c)) (seq (::fresh c))
               (not= (::gen c) (tax/relation-gen tax :genl))
               (not= (::epoch c) (tax/relation-epoch tax)))))

(defn moved?
  "Does the settle owe the family work: a refresh (`lengths-moved?`), or a `negates`
  declaration queued under `::neg`?"
  [tax c]
  (boolean (or (seq (::neg c)) (lengths-moved? tax c))))

(defn take-negates!
  "The `negates` declarations queued under `::neg` since the last call, the queue
  emptied."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::neg)]
    (::neg old #{})))

(defn- at-or-below
  "`t` and the terms below it over the unscoped closure."
  [tax t]
  (conj (set (tax/specs-global tax t)) t))

(defn- gives-each?
  "Do `s`'s own bindings, IN, give each of the bindings `bs` (`[kind value]`): the exact
  length, or a `variable_arity` release?"
  [kb s bs]
  (let [own (held-bindings kb s)]
    (every? (fn [[k v]] (if (= :var k) (seq (:var own)) (contains? (:exact own) v))) bs)))

(defn- moved-below
  "`q` and the functors below it whose length the moved bindings `bs` of `q`
  (`[kind value]`) can move, over the unscoped closure.  An `arityMin` floor binds `q`
  alone.  The walk down enters no subtype whose own bindings give each of `bs`
  (`gives-each?`): every functor below it reads them through it, so they move none."
  [kb tax q bs]
  (let [bs (into #{} (remove (fn [[k]] (= :min k))) bs)]
    (if (empty? bs)
      #{q}
      (tax/specs-global-while tax q #(or (= q %) (not (gives-each? kb % bs)))))))

(defn drain!
  "Refresh the inert shapes (`refresh-shapes!`) of every functor whose length can have
  moved since the last call, and answer `{:pairs {p dirs} :moved ts :bound qs :released
  hs}`, `:released` the tuples the refresh took out of `:out`.  `:pairs`
  holds the predicates whose arity pairs the settle places again (`pair-sets`): `:both`
  for a queued predicate and those below it, whose own binding or whose lengths above
  moved, and `:up` for an exact-bound predicate at or below the lower end of a `genl`
  edge moved since `::gen`.  `:moved` is the set of terms whose length can have moved, or
  `:all`.  `:bound` maps each predicate whose own bindings were stored, removed or
  relabelled since the last call to those bindings' `#{[kind value]}`, on every call:
  what `unary-consistent?` reads.
  Everything is refreshed when the shapes are owed whole (a recover), on the first call,
  and when the `genl` relation was rebuilt: every functor of a stored fact, `:up` for
  every bound predicate, and `:moved` `:all`."
  [kb]
  (let [tax     (reasoning/taxonomy kb)
        idx     (:index kb)
        g       (tax/relation-gen tax :genl)
        e       (tax/relation-epoch tax)
        [old _] (swap-vals! (reasoning/nogood-candidates kb)
                            #(-> % (dissoc ::bound ::owed ::fresh) (assoc ::gen g ::epoch e)))
        whole?  (or (::owed old) (nil? (::gen old)) (not= e (::epoch old)) (< g (long (::gen old))))
        [fs ps] (if whole?
                  [(into #{} (filter #(and (symbol? %) (not (sx/variable? %))))
                         (reads/as-stored-children idx []))
                   (zipmap (reads/as-stored-arity-bound idx) (repeat :up))]
                  (let [qs   (::bound old {})
                        ends (if (= g (::gen old)) #{} (tax/moves-since tax :genl (::gen old)))
                        up   (into #{} (mapcat #(at-or-below tax %)) ends)]
                    [(-> up
                         (into (mapcat (fn [[q bs]] (moved-below kb tax q bs))) qs)
                         (into (keys (::fresh old))))
                     (merge (zipmap (filter #(reads/stored-arity-bound? idx %) up) (repeat :up))
                            (zipmap (keys qs) (repeat :both)))]))]
    (when whole?
      ;; the shapes recorded are those of the tuples the forced set holds, whatever the
      ;; rows held before, so a refresh moves exactly the tuples whose answer moved
      (let [recs (:records kb)]
        (swap! (reasoning/nogood-candidates kb) assoc ::out
               (reduce (fn [m h] (if-let [[q n] (some-> (p/get-sentex recs h) sx/fact-shape)]
                                   (update m q (fnil conj #{}) n)
                                   m))
                       {} (jtms/forced-members (reasoning/tms kb) :out)))))
    ;; a whole refresh reads every tuple of each recorded shape: a recorded shape can
    ;; hold a tuple stored before the answer it records
    {:pairs    ps :moved (if whole? :all fs) :bound (::bound old {})
     :released (into [] (mapcat #(refresh-shapes! kb tax % (if whole?
                                                             (get-in @(reasoning/nogood-candidates kb) [::out %] #{})
                                                             (get-in old [::fresh %] #{}))))
                     (sort-by nm/print-key fs))}))

;; ---- a write not yet stored -------------------------------------------------------
;;
;; `try-assert` refuses a declaration that would hold a stored tuple inert
;; (`checks/length-declaration-conflict`).  `write-breaks` reads, for each functor whose
;; length the write can move, the length `relation-length` gives it with the write beside
;; the stored bindings, against the lengths its tuples are stored at: one shape-length
;; read per functor, and a belief read of each tuple stored at a length the write breaks.

(defn class-route-ok?
  "Does the `genl` edge supporter `[h ctx]` carry a metatype route: IN at `:monotonic`?"
  [tms [h _]]
  (and (jtms/in? tms h) (= :monotonic (jtms/defeat-class tms h))))

(defn- route-types
  "`t` and the types below it through `genl` edges a supporter of which carries a
  metatype route (`class-route-ok?`), over the unscoped closure, as a class membership's
  route is read."
  [kb tax t]
  (let [tms (reasoning/tms kb)]
    (graph/reach-all [t]
                     (fn [x]
                       (filter (fn [s] (some #(class-route-ok? tms %) (tax/supporters tax [:genl s x])))
                               (tax/direct-specs-global tax x))))))

(defn- monotonic-members
  "The symbols `x` of the stored memberships `(t x)` held at `:monotonic`, for each type
  of `ts`."
  [kb ts]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (into #{} (comp (mapcat #(reads/as-stored-with-functor (:index kb) %))
                    (filter #(= :monotonic (jtms/defeat-class tms %)))
                    (keep #(second (membership-of (p/get-sentex recs %)))))
          ts)))

(defn- class-writes
  "`{f write}` (`relation-length`'s `write`) for the functors at or below each member of
  `xs` whose length the exact lengths `ns` can move (`moved-below`), each member given
  `ns` and placed above the functors below it."
  [kb tax xs ns]
  (let [held (into {} (map (fn [x] [x {:exact (zipmap ns (repeat #{::write}))}])) xs)
        bs   (mapv #(vector :exact %) ns)]
    (reduce (fn [m x]
              (reduce (fn [m f] (update m f #(-> (or % {:held held :above #{}})
                                                 (update :above conj x))))
                      m (moved-below kb tax x bs)))
            {} xs)))

(defn- write-targets
  "`{f write}`: each functor whose length the sentence `s`, written and not stored, can
  move, with the `relation-length` write it gives the functor.  A length binding moves its
  predicate and the functors below it (`moved-below`).  A `genl` edge `(genl a b)` puts
  the bound predicates at or above `b` above `a` and every term below it; written
  `mono?` (`:monotonic`) where `b` is or reaches an exact-arity class, it binds each
  `:monotonic` member of `a`, or of a type below `a` through a metatype route, to the
  class's length (`class-paths`).  A `:monotonic` membership `(t x)` whose type reaches
  an exact-arity class binds `x` so."
  [kb tax s mono?]
  (let [tms (reasoning/tms kb)
        ok? #(class-route-ok? tms %)
        lengths (fn [t] (if (contains? exact-classes t)
                          [(sx/exact-arity-classes t)]
                          (mapv sx/exact-arity-classes (keys (class-paths kb t ok?)))))]
    (or
     (when-let [[p kind v] (sx/arity-binding s)]
       (let [w {:held  {p (case kind
                            :exact {:exact {v #{::write}}}
                            :min   {:min {v #{::write}}}
                            :var   {:var #{::write}})}
                :above #{p}}]
         (zipmap (moved-below kb tax p [[kind v]]) (repeat w))))
     (when-let [[a b] (when (and (seq? s) (= 'genl (first s)) (= 3 (count s))
                                 (every? #(and (symbol? %) (not (sx/variable? %))) (rest s)))
                        (rest s))]
       (let [above   (bound-above kb b true)
             inherit (when (seq above) (zipmap (at-or-below tax a) (repeat {:above above})))
             ns      (when (and mono? (reaches-class? kb b)) (lengths b))
             classes (when (seq ns)
                       (class-writes kb tax (monotonic-members kb (route-types kb tax a)) ns))]
         (merge-with (fn [x y] {:held (:held y) :above (into (:above x) (:above y))})
                     inherit classes)))
     (when-let [[t x] (when mono? (membership-of {:sentence s}))]
       (when (and (not (contains? exact-classes t)) (reaches-class? kb t))
         (when-let [ns (seq (lengths t))]
           (class-writes kb tax [x] (vec ns))))))))

(defn write-lengths
  "`[[f binding] …]` in name order: each functor `keep?` accepts whose length the
  sentence `s`, written at `:monotonic` when `mono?` and not yet stored, can move
  (`write-targets`), with the length `relation-length` gives it with the write, where one
  binds it.  A functor with an engine shape takes its length from the shape, which no
  write moves, so it is left out."
  [kb s mono? keep?]
  (let [tax (reasoning/taxonomy kb)]
    (for [[f write] (sort-by (comp nm/name-key key) (write-targets kb tax s mono?))
          :when (and (symbol? f) (not (predicates/shape-of f)) (keep? f))
          :let  [b (relation-length kb f false write)]
          :when b]
      [f b])))

(defn write-breaks
  "The stored shapes the sentence `s`, written at `:monotonic` when `mono?` and not yet
  stored, would hold inert: `[{:relation f :arguments n :count c} …]` for each functor
  whose length it moves (`write-lengths`) and each length `n` its positive facts are
  stored at that the length the write gives breaks and the stored length does not
  (`shape-breaks?`), `c` the count of those facts in every context that `believed?`
  accepts, in content order, a shape with none believed left out: a relation's length
  is read the same at every context, so a tuple in any context is held inert.  Empty
  when the write moves no length."
  [kb s mono? believed?]
  (let [tax (reasoning/taxonomy kb)
        idx (:index kb)]
    (vec (for [[f b] (write-lengths kb s mono? #(seq (reads/as-stored-shape-lengths idx %)))
               n     (sort (reads/as-stored-shape-lengths idx f))
               :when (and (breaks? b n) (not (shape-breaks? kb tax f n)))
               :let  [c (count (filter believed? (reads/as-stored-shape-tuples-global idx f n)))]
               :when (pos? c)]
           {:relation f :arguments n :count c}))))

;; ---- the pairs ---------------------------------------------------------------

(defn- root-exact
  "`{n #{h}}`: the exact bindings of `q` stored in CxUniverse, empty when a stored
  `variable_arity` binding releases `q`."
  [kb q]
  (let [idx (:index kb)]
    (if (and (reads/stored-arity-bound? idx q)
             (not-any? #(= :var (first %)) (reads/as-stored-arity-binding-kinds idx q)))
      (reduce (fn [m [h kind v]] (if (= :exact kind) (update m v (fnil conj #{}) h) m))
              {} (reads/as-stored-arity-bindings idx q #{sx/root-context}))
      {})))

(defn- bound-up
  "The exact-bound predicates at or above `q` over the unscoped closure
  (`tax/genls-global-union`): a relation's length is read the same at every context.
  `memo` is the volatile map the caller makes for one still taxonomy."
  [kb tax q memo]
  (tax/genls-global-union tax q (filter #(exact-bound? kb %)) memo))

(defn pair-sets
  "The member sets of the arity pairs at `q`, each two exact bindings stored in
  CxUniverse (`root-exact`) whose lengths differ: two of `q`, and one of `q` with one of a
  predicate above it, or with `dirs` `:both` below it too, over the unscoped closure.  A
  relation's length is read the same at every context, so the pair is too.  Reads no
  closure while the lengths stored at or above `q` (`lengths-of`), and under `:both` at
  or below it, are one, and reads the bindings of a predicate only where its own lengths
  (`own-held`) differ from `q`'s.  `memo` is `bound-up`'s, and holds `below-lengths`'
  answers beside its own."
  [kb q dirs memo]
  (let [tax   (reasoning/taxonomy kb)
        mine  (root-exact kb q)
        cross (fn [other] (for [[a has] mine, [b hbs] other :when (not= a b), x has, y hbs] #{x y}))
        ;; a subtype whose subtree stores no length but `q`'s holds no pair with `q`
        other (fn [t] (let [ls (below-lengths kb tax t memo)]
                        (some (fn [n] (some #(not= n %) (keys mine))) ls)))
        apart (comp (remove #{q})
                    (filter #(some (fn [n] (some (fn [a] (not= n a)) (keys mine)))
                                   (:own (own-held kb tax %))))
                    (mapcat #(cross (root-exact kb %))))]
    (if (or (empty? mine)
            (< (count (cond-> (lengths-of kb tax q) (= :both dirs) (into (below-lengths kb tax q memo)))) 2))
      #{}
      (-> (into #{} (cross mine))
          (into apart (bound-up kb tax q memo))
          (into apart (when (= :both dirs)
                        (tax/specs-global-while tax q #(or (= q %) (other %)))))))))

(defn root-bindings
  "The handles of `q`'s exact bindings stored in CxUniverse."
  [kb q]
  (into [] (keep (fn [[h kind]] (when (= :exact kind) h)))
        (reads/as-stored-arity-bindings (:index kb) q #{sx/root-context})))

(defn negates-clash
  "The clash of the declaration `(negates P Q)` that the lengths of `P` and `Q`
  (`relation-length`) give, as `{:kind k :grounds #{h}}` with `:grounds` the bindings
  stating the lengths, else nil.  `:negates-arity`: no argument list fits both, an exact
  length differing from the other side's exact length or below its floor.
  `:negates-unary`: both sides are bound to one argument, where `disjoint` is the
  declaration that says it (docs/taxonomy.md, \"Predicate metadata\")."
  [kb [_ p q]]
  (when (and (symbol? p) (symbol? q))
    (let [a (relation-length kb p true)
          b (relation-length kb q true)
          apart? (fn [x y] (and (:exact x)
                                (or (and (:exact y) (not= (:exact x) (:exact y)))
                                    (and (:min y) (< (:exact x) (:min y))))))
          grounds (into (set (:grounds a)) (:grounds b))]
      (cond
        (or (apart? a b) (apart? b a)) {:kind :negates-arity :grounds grounds}
        (= 1 (:exact a) (:exact b))    {:kind :negates-unary :grounds grounds}))))

(defn binding-handle?
  "Is the stored record at `h` a binding of a relation's length (`sx/fact-arity-binding`)?"
  [kb h]
  (boolean (binding-pred kb h)))

(defn kind-of
  "`:arity-descension` for the member handles `ms` of two exact bindings (`sx/fact-arity-binding`)
  of different lengths; the kind `negates-clash` gives a lone `negates` declaration;
  else nil."
  [kb ms]
  (case (count ms)
    2 (let [[a b] (map #(some-> (p/get-sentex (:records kb) %) sx/fact-arity-binding) ms)]
        (when (and a b (= :exact (second a) (second b)) (not= (nth a 2) (nth b 2)))
          :arity-descension))
    1 (let [sx (p/get-sentex (:records kb) (first ms))]
        (when (and sx (negates-declaration? sx))
          (:kind (negates-clash kb (:sentence sx)))))
    nil))

(defn below-pair?
  "Is the member of the pair `ms` other than a binding of `q` a binding of a predicate
  below `q` over the unscoped closure?  `q` stores an exact binding, so the predicates
  `bound-up` answers for one below it hold `q`; `memo` is `bound-up`'s."
  [kb q ms memo]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (some #(let [p (binding-pred kb %)]
                      (and p (not= p q) (contains? (bound-up kb tax p memo) q)))
                   ms))))

(def family
  "The arity family's entry in `decide/registry`: the forced-monotonic spellings it reads as
  bindings, and the write hook that queues a binding's predicate (`note-arity!`) and
  holds a stored tuple breaking its functor's length in the `:out` forced set.  A
  recover empties the length entries and owes the shapes whole (`::owed`), which the
  first `drain!` after it computes."
  {:grounds   {:forced-monotonic          sx/arity-binding-functors
               :forced-between-predicates '#{genl}}
   :note!     (fn [kb _w sx stored?]
                (note-arity! kb sx)
                (note-class! kb sx stored?)
                (when (and stored? (negates-declaration? sx)) (queue-negates! kb [(:id sx)]))
                ;; every creation path passes here, so a tuple a mint, lift or rewrite
                ;; stores is held OUT as an asserted one is (`checks/force-sentex!`)
                (when (and stored? (inert-tuple? kb sx))
                  (jtms/set-forced (reasoning/tms kb) :out [(:id sx)] true)))
   :recovered (fn [kb _]
                (reset! (reasoning/arity-lengths kb) nil)
                (swap! (reasoning/nogood-candidates kb) assoc ::owed true))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-cache
 {:cache    :arity-lengths
  :label    "Arity lengths"
  :scope    :kb
  :unit     "functors, and the lengths and floors their entries hold"
  :limit    (caches/limit-thunk :arity-lengths lengths-cache-limit)
  :counters :kb
  :note     (str "Per functor, the exact lengths stored at or above it, and its own "
                 "lengths and arityMin floors. A "
                 "binding write evicts the entries it moves, a genl edge's "
                 "relation move every entry at or below its lower end; past the bound, and "
                 "under memory pressure, the least recently used go first.")
  ;; the LRU's own tally answers the hits while it exists; before the family's first read
  ;; there is none, and nothing has been counted
  :read     (fn [kb] (if-let [lru @(reasoning/arity-lengths kb)]
                       {:entries (caches/lru-weight lru)}
                       {:entries 0 :hits 0 :misses 0}))
  :clear    (fn [kb] (or (some-> @(reasoning/arity-lengths kb) caches/lru-clear!) 0))
  :trim     (fn [kb target]
              (or (some-> @(reasoning/arity-lengths kb) (caches/lru-trim! target)) 0))})

(caches/register-derived
 {:id :N3 :label "Arity inert shapes" :kind :cache :keyed-by :functor
  :holds-content? false
  :reads [:index :records :M1 :T1 :J5 :N8]
  :retired-by {:stored :K :removed :K :relabelled :K :edge :G :edge-belief :G
               :settle-pass :Q :recover :R :image-install :R}
  :computed :write :imaged? :state
  :at [[:nogood-candidates ::out] [:nogood-candidates ::bound] [:nogood-candidates ::gen]
       [:nogood-candidates ::epoch] [:nogood-candidates ::owed] [:nogood-candidates ::fresh]
       [:nogood-candidates ::classes] [:nogood-candidates ::class-gen]
       [:nogood-candidates ::class-epoch] [:nogood-candidates ::neg]]
  :bound "one entry per functor with a tuple in the `:out` forced set, holding its inert lengths, one per predicate whose binding moved since the last settle pass, one per functor with a tuple decided inert since then on a shape not recorded, one per class-shaped record stored since then whose store path did not sync its class memberships, and the `genl` generation and epoch the last class sync read, and one per `negates` declaration stored or relabelled since the last pass"
  :note "the lengths of each functor whose tuples the `:out` forced set holds for breaking its length, recorded as a tuple is stored and at each refresh; the predicates a binding write or relabel queued, and the `genl` generation the last refresh read, which the settle drains (`drain!`), and the class-shaped records stored since the last pass (`take-classes!`) and the `genl` generation the last class sync read (`take-class-ends!`); a recover owes them whole (`::owed`), and the first drain rebuilds `::out` from the forced set and refreshes every functor"})

(caches/register-derived
 {:id :N8 :label "Arity lengths" :cache :arity-lengths :kind :cache :keyed-by :functor
  :holds-content? false
  :reads [:index :records :T1 :J5]
  :retired-by {:stored :K :removed :K :edge :K :edge-belief :K :settle-pass :K
               :recover :W :caches-cleared :W}
  :computed :write :imaged? false :at [[:arity-lengths]]
  :value (fn [kb] (when-let [^java.util.LinkedHashMap m (:map (caches/value-at kb [:arity-lengths]))]
                    (locking m (into {} m))))
  :note "per functor, the exact lengths stored at or above it, and its own lengths and floors, in a weighted LRU; a binding write evicts the entries it moves, and the relation moves (J5) evict every entry at or below a moved edge's lower end at the next read, the settle's sync and placement reads included"})
