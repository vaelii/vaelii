;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.tuple
  "The two tuple families.  The self and converse family: a ground binary self tuple under
  `irreflexive`, and a tuple and its stored converse under `anti_symmetric`.  The
  tuple-mark family: the determinants under `functional` and `functionalInArg`, the
  `anti_transitive` chains, the `asymmetric` converse pairs and the tuples a `negates`
  declaration sets against each other.  Both find their nogoods
  from a stored tuple's own arguments and share the converse pairs, and each nogood is
  placed as a conclusion (`chain/place-tuples!`).  See docs/nmtms.md, \"A nogood placed as
  a conclusion\"."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the self and converse family -------------------------------------------

(def ^:private converse-marks
  "The taxonomy props of the marks that read a tuple's converses: `:converse` holds the
  ground binary tuples under one of them with a stored converse."
  #{:anti-symmetric :asymmetric})

(defn binary-tuple
  "`[a b]` for a stored fact `sx` whose sentence is a ground positive binary tuple with a
  symbol functor, else nil.  `checks` asks it of a sentence about to be written, as
  `{:sentence s}`."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 3 (count s)))
      (let [f (nm/functor s)]
        (when (and (symbol? f) (not= 'not f) (not (sx/variable? f)) (sx/ground-term? s))
          (vec (nm/args s)))))))

(defn self-tuple?
  "Is the stored fact `sx` a ground positive binary tuple `(p a a)` (`binary-tuple`)?"
  [sx]
  (let [[a b :as ab] (binary-tuple sx)] (boolean (and ab (= a b)))))

(defn- symbol-pair?
  "Two plain symbols, which an all-`:monotonic` `anti_symmetric` converse or functional
  collision merges instead of convicting (`special/derive-antisymmetric-equalities`,
  `special/derive-functional-equalities`)."
  [a b]
  (and (symbol? a) (symbol? b) (not (sx/variable? a)) (not (sx/variable? b))))

(defn- converse-functors
  "The functors a converse of a tuple of `q` is read under: `q`, and every predicate
  below an `anti_symmetric` or `asymmetric` mark on `q` or above it, since the mark binds
  its whole spec subtree, read over `specs`, the unscoped spec closure: a missed one is a nogood
  no placement stores."
  [tax specs q]
  (into #{q}
        (comp (mapcat #(when (seq (tax/props tax %)) (tax/props-over tax % q)))
              (mapcat specs))
        converse-marks))

(defn- converse-handles
  "The handles of the stored converses `(q' b a)` of `(q a b)`: one trie read under each
  of `converse-functors`, since the argument roots index neither a number nor a string."
  [kb tax specs q a b]
  (into []
        (mapcat #(reads/as-stored-at-path (:index kb) (sx/path (sx/sentex (list % b a) '?c))))
        (sort (converse-functors tax specs q))))

(defn- stored-converses
  "The handles other than `h` of the stored converses of `h`, `(q a b)`, read off the
  index (`converse-handles`) and checked against their records."
  [kb w h q a b]
  (let [recs (:records kb)]
    (into [] (filter #(and (not= h %) (= [b a] (some-> (p/get-sentex recs %) binary-tuple))))
          (converse-handles kb (:tax w) (:specs-global w) q a b))))

(defn- marked-facts
  "The handles of the stored facts of every predicate at or below one of the marked
  predicates `ps` over the unscoped closures (`w`), read off the predicate
  extents, in content order of the predicates."
  [kb w ps]
  (into [] (mapcat #(reads/as-stored-with-functor (:index kb) %))
        (into (sorted-set) (mapcat (:specs-global w)) ps)))

(defn- self-tuples-under
  "The stored self tuples of the predicates `fs` that an `irreflexive` mark stands on or
  above, read off the self-tuple trie (`reads/as-stored-self-tuples`), stated in a
  context of `ctxs` alone when it is given, and in every context otherwise.  The marks
  over `fs` are read off one memo (`tax/props-over-among`), so the call costs the `genl`
  edges above `fs` once rather than a closure per predicate."
  ([kb w fs] (self-tuples-under kb w fs nil))
  ([kb w fs ctxs]
   (let [tax  (:tax w)
         idx  (:index kb)
         memo (volatile! {})]
     (when (seq (tax/props tax :irreflexive))
       (into #{} (comp (filter #(seq (tax/props-over-among tax :irreflexive % memo)))
                       (mapcat #(if ctxs
                                  (reads/as-stored-self-tuples idx % ctxs)
                                  (reads/as-stored-self-tuples-global idx %))))
             fs)))))

(defn- self-tuples
  "Every stored self tuple under an `irreflexive` mark (`self-tuples-under`).

  The marks are read unscoped: a candidate row is a superset over every reader
  (`decide/unscoped-closures`)."
  [kb w]
  (let [tax (:tax w)]
    (self-tuples-under kb w (into (sorted-set) (mapcat (:specs-global w)) (tax/props tax :irreflexive)))))

;; ---- the tuple marks -------------------------------------------------------
;;
;; A tuple under a `functional`, `functionalInArg` or `anti_transitive` mark on its functor
;; or above it forms its nogoods with the stored tuples its own arguments name: the tuples
;; agreeing with it on the determinant, every position but the marked one, and differing
;; at the marked one; and the steps of a chain through its two arguments.  The candidate
;; index keeps each determinant holding two fillers under `::det`, as `{[P k n det] {h
;; [filler context]}}` for the mark's predicate `P`, arity `k`, position `n` and the
;; arguments with position `n` nil, with its members by context under `::det-ctx`; each
;; chain's members under `::chains`; and each stored converse pair under `::conv`, which
;; the `asymmetric` marks read.  `::member-of` holds each member's keys, for its removal.
;; The index reads every mark over a tuple's functor anywhere, so it is a superset, and
;; the placement keeps the nogoods some context sees whole.
;;
;; A determinant member is live, under `::live`, when a member with another filler sits in
;; a context some context sees together with its own; only a live member is a candidate,
;; so a determinant whose fillers no context sees together places nothing.  Liveness reads
;; the unscoped `genlCx` closure, so `::ts-gen` holds the generation it was read at, and
;; `sync-tuples` reads it again when it moved.  `::moved` holds the members whose nogoods
;; the settle places again (`take-moved!`).

(defn- fact-tuple
  "`[f args]` for a stored fact `sx` whose sentence is a ground positive tuple with a
  symbol functor, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (<= 2 (count s)))
      (let [f (first s)]
        (when (and (sx/plain-symbol? f) (not= 'not f) (sx/ground-term? s))
          [f (vec (rest s))])))))

(defn- tuple-marks?
  "Does the taxonomy hold a `functional`, `functionalInArg`, `anti_transitive` or
  `negates` mark?  Four map reads."
  [tax]
  (boolean (or (seq (tax/props tax :functional))
               (seq (tax/functional-in-arg-predicates tax))
               (seq (tax/props tax :anti-transitive))
               (tax/negates? tax))))

(defn- tuple-members
  "The handles of the tuple-mark candidates `c`: the live determinant members and the
  members of every chain, converse pair and `negates` set."
  [c]
  (-> #{}
      (into cat (vals (::live c)))
      (into cat (::chains c))
      (into cat (::conv c))
      (into cat (::neg c))))

(defn- tuple-member?
  "Is `h` among `tuple-members` of `c`?  Read off `::member-of`."
  [c h]
  (boolean (some (fn [[kind key]] (or (not= ::det kind) (contains? (get-in c [::live key]) h)))
                 (get-in c [::member-of h]))))

(defn- stored-specs
  "The predicates at or below `p` holding a stored fact, in content order."
  [kb w p]
  (into (sorted-set)
        (filter #(pos? (reads/stored-count-with-functor (:index kb) %)))
        ((:specs-global w) p)))

(defn- tuples-at
  "`{h [args context]}` of the stored positive tuples of a functor in `fs` whose arguments
  are `args` at every position `args` does not hold nil, `(count args)` of them.  Per
  functor, one trie read under a variable context when the bound positions lead, else one
  intersection of the bound symbol positions' argument roots, since those index neither a
  number nor a string, else the trie read."
  [kb fs args]
  (let [idx   (:index kb)
        recs  (:records kb)
        k     (count args)
        lead? (every? nil? (drop-while some? args))
        roots (into [] (keep-indexed (fn [i a] (when (sx/plain-symbol? a) [(inc i) a]))) args)
        probe (fn [g]
                (if (or lead? (empty? roots))
                  (reads/as-stored-at-path
                   idx (sx/path (sx/sentex (apply list g (map-indexed
                                                          (fn [i a] (if (nil? a) (symbol (str "?t" i)) a))
                                                          args))
                                           '?c)))
                  (reads/as-stored-with-args idx g roots)))]
    (into {}
          (for [g fs
                h (probe g)
                :let [sx (p/get-sentex recs h)
                      [f as] (some-> sx fact-tuple)]
                :when (and (= g f) (= k (count as))
                           (every? true? (map #(or (nil? %1) (= %1 %2)) args as)))]
            [h [as (:context sx)]]))))

(def ^:dynamic ^:private *functor-marks*
  "A volatile map while recover offers the facts under a tuple mark, holding each functor's
  marks as `found-for` reads them (`det-marks`, the `anti_transitive` marks above it):
  both walk the functor's supertypes, recover offers every stored tuple under a mark, and
  the taxonomy holds still under it, so a functor's are read once rather than once per
  tuple, and each kind's `:props` cut is read off one memo (`prop-marks`) rather than a
  closure per functor.  nil otherwise."
  nil)

(defn- functor-marks
  "`(f)`, held in `*functor-marks*` under `k` while it is bound."
  [k f]
  (if-some [m *functor-marks*]
    (caches/get-or! m k f)
    (f)))

(defn- prop-marks
  "`tax/props-over` of `kind` on `q` with no context.  While `*functor-marks*` is bound,
  read off the `:props` set's cut with one memo per kind and `:props` value
  (`tax/props-over-among`).

  The read is unscoped: a candidate row is a superset over every reader
  (`decide/unscoped-closures`)."
  [tax kind q]
  (if (some? *functor-marks*)
    (tax/props-over-among tax kind q
                          (functor-marks [::memo kind (get-in @tax [:props kind])] #(volatile! {})))
    (tax/props-over tax kind q)))

(defn- det-marks
  "`[P n]` for every `functional` mark on `q` or above it, at position 2 of a binary
  tuple, and every `functionalInArg` mark there at a position a tuple of `k` arguments
  has.  Unscoped."
  [tax q k]
  (cond-> (into #{} (filter (fn [[_ n]] (<= n k))) (tax/functional-in-arg-over tax q))
    (= 2 k) (into (map #(vector % 2)) (prop-marks tax :functional q))))

(defn- co-visible
  "The keys of `by` (a map keyed by context) some context sees together with `c`, nil
  among them when `by` holds it: read from `c`'s descendants' ancestor sets, or by asking
  each key for a descendant it shares with `c`, whichever reads fewer contexts.  It reads
  the unscoped closures `w`, since a scoped read asks a reader's withdrawal, which reads
  this."
  [w c by]
  (if (or (nil? c) (= sx/root-context c))
    (set (keys by))
    (let [ups  (:context-up-global w)
          down ((:context-down-global w) c)
          up   (ups c)]
      (cond-> (if (< (* (count down) (count up)) (count by))
                (into #{} (comp (mapcat ups) (filter #(contains? by %)))
                      down)
                (into #{} (filter #(and (some? %)
                                        (or (= c %) (= sx/root-context %)
                                            (boolean (some down ((:context-down-global w) %))))))
                      (keys by)))
        (contains? by nil) (conj nil)))))

(defn- noted
  "`c` with the handles `hs` journaled (`journal/note`) and queued under `::moved` for the
  settle to place their nogoods again (`take-moved!`).  Given `queued`, only those of `hs`
  are queued: a member joining or leaving a determinant moves its partners' candidate
  entries and only its own nogoods."
  ([c hs] (noted c hs hs))
  ([c hs queued]
   (-> (journal/note c hs) (update ::moved (fnil into #{}) queued))))

(defn- link
  "`c` with the members of `ms` recorded under `k`."
  [c ms k]
  (reduce (fn [c h] (update-in c [::member-of h] (fnil conj #{}) k)) c ms))

(defn- unlink
  "`c` with `k` dropped from the records of the members `ms`."
  [c ms k]
  (reduce (fn [c h]
            (let [left (disj (get-in c [::member-of h] #{}) k)]
              (if (empty? left)
                (update c ::member-of dissoc h)
                (assoc-in c [::member-of h] left))))
          c ms))

(defn- det-partners
  "The members of determinant `key` with a filler other than `h`'s, in a context some
  context sees together with `h`'s."
  [w c key h]
  (let [g      (get-in c [::det key])
        [v cx] (get g h)
        by     (get-in c [::det-ctx key])]
    (for [c' (co-visible w cx by)
          h' (get by c')
          :when (and (not= h h') (not= v (first (get g h'))))]
      h')))

(defn- classify-det-member
  "`c` with the member `h` of determinant `key` live, with its partners, when it has one
  (`det-partners`)."
  [w c key h]
  (let [ps (det-partners w c key h)]
    (if (empty? ps)
      c
      (-> c
          (update-in [::live key] (fnil into #{}) (conj ps h))
          (noted (conj ps h) [h])))))

(defn- add-det-member
  "`c` with `h`, filling `v` in context `cx`, a member of determinant `key`."
  [w c key h v cx]
  (as-> c c
    (assoc-in c [::det key h] [v cx])
    (update-in c [::det-ctx key cx] (fnil conj #{}) h)
    (link c [h] [::det key])
    (classify-det-member w c key h)))

(defn- sync-tuples
  "`c` with `::live` read again when the `genlCx` generation moved since `::ts-gen`: one
  pass over the determinants.  Only the members whose liveness moved are queued
  (`::moved`)."
  [w c]
  (let [gen (tax/relation-gen (:tax w) :genlCx)]
    (if (= gen (::ts-gen c 0))
      c
      (let [live (fn [c] (into #{} cat (vals (::live c))))
            c'   (as-> c c'
                   (journal/note c' (into #{} (mapcat keys) (vals (::det c'))))
                   (dissoc c' ::live)
                   (reduce-kv (fn [c' key g] (reduce #(classify-det-member w %1 key %2) c' (keys g)))
                              c' (::det c'))
                   (assoc c' ::ts-gen gen))
            was  (live c)
            now  (live c')]
        (assoc c' ::moved (-> (or (::moved c) #{})
                              (into (remove now) was)
                              (into (remove was) now)))))))

(defn- negates-sets
  "The `negates` nogoods the stored tuple `h`, `(q args…)`, is a member of, read from
  storage: `#{h}` when `q` is at or below both sides of one declaration, and `#{h h'}` for
  each stored tuple `h'` of another functor on the same arguments at or below a predicate
  a declaration sets against one at or above `q` (`tax/negates-over`).  One trie read per
  functor holding a stored fact in those spec subtrees.  Unscoped."
  [kb w h q args]
  (let [pairs (tax/negates-over (:tax w) q)]
    (when (seq pairs)
      (let [up ((:genls-global w) q)
            fs (into (sorted-set) (comp (map second) (mapcat #(stored-specs kb w %)) (remove #{q})) pairs)]
        (cond-> (into #{} (map #(hash-set h %)) (keys (tuples-at kb fs args)))
          (some (fn [[_ r]] (contains? up r)) pairs) (conj #{h}))))))

(defn- found-for
  "The determinants, chains and `negates` sets the stored tuple `h`, `(q args…)` in
  context `cx`, is a member of, read from storage: `{:det {key {h [filler context]}}
  :chains #{members} :neg #{members}}`.  A new determinant is kept when it holds two
  fillers, and a chain when it has two members or three.  A determinant `dets` (`::det`)
  holds already takes the tuple with no read, so an empty or a wide determinant is read
  once, when its second filler arrives."
  [kb w dets h q args cx]
  (let [tax (:tax w)
        k   (count args)
        det (into {}
                  (keep (fn [[p n]]
                          (let [d   (assoc args (dec n) nil)
                                key [p k n d]
                                v   (nth args (dec n))]
                            (if (contains? dets key)
                              [key {h [v cx]}]
                              (let [g (into {h [v cx]}
                                            (map (fn [[h' [as c']]] [h' [(nth as (dec n)) c']]))
                                            (tuples-at kb (stored-specs kb w p) d))]
                                (when (< 1 (count (into #{} (map first) (vals g))))
                                  [key g]))))))
                  (functor-marks [:det q k] #(det-marks tax q k)))
        anti (when (= 2 k)
               (functor-marks [:anti q] #(prop-marks tax :anti-transitive q)))
        chains (into #{}
                     (comp (mapcat
                            (fn [p]
                              (let [fs    (stored-specs kb w p)
                                    [a b] args
                                    at    (fn [x y] (keys (tuples-at kb fs [x y])))]
                                (concat
                                 ;; the direct step: (a m) and (m b)
                                 (for [[s1 [[_ m]]] (tuples-at kb fs [a nil]), s2 (at m b)]
                                   (hash-set s1 s2 h))
                                 ;; the first step: (b c) and the direct (a c)
                                 (for [[s2 [[_ c]]] (tuples-at kb fs [b nil]), cl (at a c)]
                                   (hash-set h s2 cl))
                                 ;; the second step: (z a) and the direct (z b)
                                 (for [[s1 [[z _]]] (tuples-at kb fs [nil a]), cl (at z b)]
                                   (hash-set s1 h cl))))))
                           (filter #(< 1 (count %))))
                     anti)]
    {:det det :chains chains :neg (negates-sets kb w h q args)}))

(defn- add-found
  "`c` with `found-for`'s answer merged in."
  [w c {:keys [det chains neg]}]
  (as-> c c
    (reduce-kv (fn [c key g]
                 (reduce-kv (fn [c h [v cx]]
                              (if (contains? (get-in c [::det key]) h)
                                c
                                (add-det-member w c key h v cx)))
                            c g))
               c det)
    (reduce (fn [c ms]
              (if (contains? (::chains c) ms)
                c
                (-> c (update ::chains (fnil conj #{}) ms) (link ms [::chains ms])
                    (noted ms))))
            c chains)
    (reduce (fn [c ms]
              (if (contains? (::neg c) ms)
                c
                (-> c (update ::neg (fnil conj #{}) ms) (link ms [::neg ms]) (noted ms))))
            c neg)))

(defn- add-conv
  "`c` with the stored tuple `h` and each of its stored converses `others` recorded as a
  pair under `::conv`."
  [c h others]
  (reduce (fn [c o]
            (let [ms #{h o}]
              (if (contains? (::conv c) ms)
                c
                (-> c (update ::conv (fnil conj #{}) ms) (link ms [::conv ms])
                    (noted ms)))))
          c others))

(defn- drop-det-member
  "`c` with `h` gone from determinant `key`: the determinant goes when one filler is
  left, and a partner left with none is no longer live."
  [w c key h]
  (let [[_ cx] (get-in c [::det key h])
        ps     (det-partners w c key h)
        c      (-> c
                   (update-in [::det key] dissoc h)
                   (update-in [::det-ctx key cx] disj h)
                   (update-in [::live key] #(some-> % (disj h)))
                   (noted (conj ps h) [h]))
        g      (get-in c [::det key])]
    (if (< 1 (count (into #{} (map first) (vals g))))
      (reduce (fn [c h'] (if (seq (det-partners w c key h'))
                           c
                           (update-in c [::live key] disj h')))
              c ps)
      (-> c
          (update ::det dissoc key)
          (update ::det-ctx dissoc key)
          (update ::live dissoc key)
          (unlink (keys g) [::det key])
          (noted (keys g))))))

(defn- drop-tuple
  "`c` with the tuple `h` gone from every determinant, chain and converse pair it is a
  member of: a chain or a pair goes whole."
  [w c h]
  (reduce (fn [c [kind key :as k]]
            (case kind
              ::det (drop-det-member w c key h)
              (-> c (update kind disj key) (unlink (disj key h) k) (noted key))))
          (update c ::member-of dissoc h)
          (get-in c [::member-of h])))

(defn- note-tuple!
  "Keep the tuple-mark candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving.  An arriving tuple reads its determinants and chains (`found-for`) while the
  taxonomy holds a tuple mark; a leaving one reads nothing."
  [kb w sx stored?]
  (let [cands (reasoning/nogood-candidates kb)]
    (if stored?
      (when (tuple-marks? (:tax w))
        (when-let [[q args] (fact-tuple sx)]
          (let [found (found-for kb w (::det @cands) (:id sx) q args (:context sx))]
            (when (or (seq (:det found)) (seq (:chains found)) (seq (:neg found)))
              (swap! cands #(add-found w (sync-tuples w %) found))))))
      (when (contains? (::member-of @cands) (:id sx))
        (swap! cands #(drop-tuple w (sync-tuples w %) (:id sx)))))))

(defn- note-converse!
  "Keep the converse candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving (`note-candidate!`).  A self tuple keeps no row: it is queued for the settle to
  place (`take-moved!`) when it leaves, or arrives under an `irreflexive` mark, and read
  off the self-tuple trie otherwise (`self-tuples-under`)."
  [kb w sx stored?]
  (when-let [[a b] (binary-tuple sx)]
    (let [q     (nm/functor (:sentence sx))
          h     (:id sx)
          cands (reasoning/nogood-candidates kb)]
      (cond
        (= a b)
        (when (or (not stored?) (seq (tax/props-over (:tax w) :irreflexive q)))
          (swap! cands update ::moved (fnil conj #{}) h))

        (not stored?)
        (when (contains? (:converse @cands) h)
          (swap! cands (fn [m] (-> m (update :converse disj h) (noted [h])))))

        ;; no mark over `q` reads its converse pairs, and one arriving on `q` or above
        ;; it offers the stored tuples again (`special/offer-marked-existing`,
        ;; `antisym-equate-existing` and their edge twins)
        (not-any? #(and (seq (tax/props (:tax w) %)) (seq (tax/props-over (:tax w) % q)))
                  converse-marks)
        nil

        :else
        (let [others (stored-converses kb w h q a b)]
          (when (seq others)
            (swap! cands #(-> (sync-tuples w %)
                              (update :converse (fnil into #{}) (conj others h))
                              (add-conv h others)
                              (noted (conj others h))))))))))

(defn offer!
  "Offer the stored fact `sx` to the converse and tuple-mark candidates again, or with
  `only` `:converse` to the converse ones alone: a mark or a predicate `genl` edge
  arriving over stored tuples makes candidates their store did not read
  (`decide/offer!`)."
  [kb w sx only]
  (note-converse! kb w sx true)
  (when-not (= :converse only) (note-tuple! kb w sx true)))

;; ---- the nogoods placed as conclusions -------------------------------------
;;
;; No reader decides a tuple nogood: the settle places each one where its members, a mark
;; over every functor and the predicate `genl` edges that reach the mark are seen together
;; (`chain/place-tuples!`).  The index queues the members whose nogoods moved under
;; `::moved` (`noted`), and a nogood's routes are the marks that convict it over the
;; unscoped taxonomy (`routes`).

(defn monotonic-member?
  "Is `h` a `:monotonic` member of a collision, which a merge needs of every member
  (docs/reference.md, decision 6)?  Its class, or its premise strength while a network
  defeat decided before a restrengthening holds it OUT: a `:monotonic` member is never a
  loser, so the next settle releases it."
  [tms h]
  (or (= :monotonic (jtms/defeat-class tms h)) (= :monotonic (jtms/premise-strength tms h))))

(defn merges?
  "Does a converse pair over `a` and `b` merge the two terms instead of forming a nogood:
  two symbols, both members `:monotonic` (`h-mono?`, `o-mono?`, each `monotonic-member?`
  of a stored member)."
  [a b h-mono? o-mono?]
  (and (symbol-pair? a b) h-mono? o-mono?))

(defn- same-class-at?
  "Do the symbols `a` and `b` denote one thing through equality edges a reader with
  ancestor set `up` sees: each with a supporter IN, stated in `up` and not hidden
  (`hidden?`, or nil)?  The scoped election `res/same-class-in?` makes, over the reader's
  ancestor set and with no withdrawal read."
  [kb up hidden? a b]
  (let [tax (reasoning/taxonomy kb)]
    (boolean
     (and (tax/merged? tax a) (tax/merged? tax b)
          (let [tms  (reasoning/tms kb)
                recs (:records kb)
                vis? (memoize (fn [h] (and (jtms/in? tms h) (not (and hidden? (hidden? h)))
                                           (let [c (:context (p/get-sentex recs h))]
                                             (or (nil? c) (contains? up c))))))
                rep  (fn [t] (if (tax/class-fully-visible? tax t vis?)
                               (tax/representative tax t)
                               (second (tax/scoped-class tax t vis?))))]
            (= (rep a) (rep b)))))))

(defn member?
  "Is `h` a member of a tuple nogood: a stored self tuple (`self-tuple?`), or a member of a
  converse pair or a chain or a live determinant member the candidate index `c` keeps?"
  [kb c h]
  (or (tuple-member? c h) (boolean (some-> (p/get-sentex (:records kb) h) self-tuple?))))

(defn held?
  "Does the candidate index `c` keep a member of a determinant, a chain or a converse
  pair, or does the taxonomy `tax` hold an `irreflexive` mark, which a stored self tuple
  can stand under?"
  [tax c]
  (boolean (or (seq (::member-of c)) (seq (tax/props tax :irreflexive)))))

(defn members
  "Every member of a tuple nogood: the stored self tuples under an `irreflexive` mark
  (`self-tuples`), and every member the candidate index `c` keeps.  `w` is
  `decide/unscoped-closures`'s."
  [kb w c]
  (into (set (self-tuples kb w)) (tuple-members c)))

(defn self-tuples-in
  "The stored self tuples under an `irreflexive` mark stated in a context of `ctxs`, which
  a `genlCx` move exposing those contexts can give a placement (`special/drain-context-moves!`' `:reach`).

  The marks are read unscoped: a candidate row is a superset over every reader
  (`decide/unscoped-closures`)."
  [kb w ctxs]
  (when (seq ctxs)
    (let [tax (:tax w)]
      (self-tuples-under kb w (into (sorted-set) (mapcat (:specs-global w)) (tax/props tax :irreflexive))
                         ctxs))))

(defn moved?
  "Has the index queued a member whose nogoods the settle places again (`take-moved!`)?"
  [c]
  (boolean (seq (::moved c))))

(defn take-moved!
  "The members whose tuple nogoods moved since the last call, and the queue emptied
  (`noted`)."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::moved)]
    (::moved old #{})))

(defn- note-placement-left!
  "Queue the tuple members a `(contradicts …)` sentex `sx` leaving the store names, so the
  settle places their nogoods where they stand (`take-moved!`): a `genlCx` edge under the
  placement can have left with it.  A placement naming a handle that is no member left
  with its nogood, and queues nothing: the departed member queued itself (`drop-tuple`),
  and the others' nogoods keep their placements."
  [kb sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'contradicts (first s)))
      (let [cands (reasoning/nogood-candidates kb)
            c     @cands
            hs    (into #{} (keep sx/handle-id) (rest s))]
        (when (and (seq hs) (every? #(member? kb c %) hs))
          (swap! cands update ::moved (fnil into #{}) hs))))))

(defn members-under
  "The members of the tuple nogoods whose functor is at or below one of the predicates
  `ps` over the unscoped `genl` closure (`w`, `decide/unscoped-closures`): those a mark on one of
  `ps`, or a `genl` edge whose lower end is one of `ps`, can give or take a route.  The
  members `c` keeps are read off their records, or off the stored facts of each predicate
  at or below `ps`, whichever is fewer; the self tuples under an `irreflexive` mark off
  those facts (`self-tuples-under`)."
  [kb w c ps]
  (when (and (seq ps) (held? (:tax w) c))
    (let [idx  (:index kb)
          fs   (into (sorted-set) (mapcat (:specs-global w)) ps)
          ms   (tuple-members c)]
      (into (set (self-tuples-under kb w fs))
            (if (< (count ms) (transduce (map #(reads/stored-count-with-functor idx %)) + fs))
              (filter #(contains? fs (some-> (p/get-sentex (:records kb) %) :sentence nm/functor)) ms)
              (into [] (comp (mapcat #(reads/as-stored-with-functor idx %)) (filter #(tuple-member? c %)))
                    fs))))))

(defn nogoods-holding
  "The tuple nogoods `c` keeps with a member among the handles `hs`, each `{:members #{h}
  :specs #{spec}}`, one per member set: `[:self]` for a self tuple, `[:conv]` for a
  converse pair, `[:chain]` for a chain, `[:neg]` for a `negates` set, and `[:det key]`
  for two live members of determinant `key` with distinct fillers.  A spec names the shape; `routes` reads the
  marks that convict it."
  [kb c hs]
  (let [recs  (:records kb)
        specs (fn [h]
                (concat
                 (when (some-> (p/get-sentex recs h) self-tuple?) [[#{h} [:self]]])
                 (mapcat (fn [[kind key]]
                           (case kind
                             ::det    (let [g    (get-in c [::det key])
                                            live (get-in c [::live key])
                                            v    (first (get g h))]
                                        (when (contains? live h)
                                          (for [h' live :when (and (not= h h') (not= v (first (get g h'))))]
                                            [#{h h'} [:det key]])))
                             ::chains [[key [:chain]]]
                             ::conv   [[key [:conv]]]
                             ::neg    [[key [:neg]]]))
                         (get-in c [::member-of h]))))]
    (->> (mapcat specs hs)
         (reduce (fn [m [ms spec]] (update m ms (fnil conj #{}) spec)) {})
         (mapv (fn [[ms ss]] {:members ms :specs ss})))))

(defn convicting
  "The predicates carrying `prop` at or above every functor of `fs` over the unscoped
  closure, or with `context` over what a reader there sees (`tax/props-over`), in content
  order."
  ([tax prop fs] (sort (reduce set/intersection (map #(tax/props-over tax prop %) fs))))
  ([tax prop fs context]
   (sort (reduce set/intersection (map #(tax/props-over tax prop % context) fs)))))

(defn- negates-routes
  "Each `negates` declaration convicting a tuple of `f1` beside one of `f2` (one tuple
  when the two are one functor) over the unscoped taxonomy (`w`): a declaration between
  a predicate at or above `f1` and one at or above `f2`, its flat-cache key, and the
  subsumptions from the functors to the two, in content order."
  [w f1 f2]
  (let [up2  ((:genls-global w) f2)
        link (fn [sub super] (when (not= sub super) [sub super]))]
    (for [[p r] (sort-by nm/print-key (tax/negates-over (:tax w) f1))
          :when (contains? up2 r)]
      {:keys  #{(tax/negates-key p r)}
       :links (into [] (comp (keep identity) (distinct)) [(link f1 p) (link f2 r)])})))

(defn routes
  "Each way a mark convicts the tuple nogood `ng` (`nogoods-holding`) over the unscoped
  taxonomy, as `{:keys #{k} :links [[sub super]]}` (`tax/separation-routes`' shape): a
  mark on a predicate `P` at or above every member's functor, its flat-cache key, and the
  subsumption from each functor to `P`.  A self tuple reads the `irreflexive` marks, a
  chain the `anti_transitive` ones, and a converse pair the `asymmetric` ones and the
  `anti_symmetric` ones unless it merges (`merges?`,
  `special/derive-antisymmetric-equalities`), and a `negates` set the declarations over
  its functors (`negates-routes`).  A determinant pair reads the determinant's
  own `functional` and `functionalInArg` marks; two symbol fillers both `:monotonic` merge
  (`special/derive-functional-equalities`) and give no route.  Two symbol fillers one class
  at a reader form no nogood there, which the read reads (`exempt-at?`).  A determinant
  pair's routes carry `:excluded-at`, the contexts at which `agree?`, `(fn [v1 v2
  context])`, reads its two fillers as one value (`chain/route-placements`).  `w` is
  `decide/unscoped-closures`'s."
  [kb w c {:keys [members specs]} agree?]
  (let [tax   (:tax w)
        tms   (reasoning/tms kb)
        recs  (:records kb)
        sxs   (into {} (map (fn [h] [h (p/get-sentex recs h)])) members)
        fs    (into (sorted-set) (keep #(some-> (get sxs %) :sentence nm/functor)) members)
        links (fn [q] (into [] (comp (remove #(= q %)) (map #(vector % q))) fs))
        by    (fn [prop] (for [q (convicting tax prop fs)] {:keys #{[:prop prop q]} :links (links q)}))]
    (when (every? some? (vals sxs))
      (into []
            (mapcat
             (fn [[kind key]]
               (case kind
                 :self  (by :irreflexive)
                 :chain (by :anti-transitive)
                 :neg   (negates-routes w (first fs) (last fs))
                 :conv  (let [[h o] (sort members)
                              [a b] (binary-tuple (get sxs h))]
                          (concat (by :asymmetric)
                                  (when-not (merges? a b (monotonic-member? tms h) (monotonic-member? tms o))
                                    (by :anti-symmetric))))
                 :det   (let [[q k n] key
                              [v1 v2] (map #(first (get-in c [::det key %])) members)
                              sym?    (symbol-pair? v1 v2)]
                          (when-not (and sym? (every? #(monotonic-member? tms %) members))
                            (for [mk (cond-> [[:functional-in-arg q n]] (= 2 k n) (conj [:prop :functional q]))]
                              (cond-> {:keys #{mk} :links (links q)}
                                (not sym?) (assoc :excluded-at #(agree? v1 v2 %)))))))))
            (sort-by nm/print-key specs)))))

(defn kind-of
  "The kind the tuple nogood over the member handles `ms` reports under, read off the
  candidate index `c` and the marks over the members' functors in the unscoped taxonomy:
  `:irreflexive` for a self tuple under an `irreflexive` mark, `:anti-transitive` for a
  chain under an `anti_transitive` one, `:functional` for a determinant pair, `:negates`
  for a `negates` set, and for a
  converse pair `:anti-symmetric` under an `anti_symmetric` mark, else `:asymmetric` under
  an `asymmetric` one; the first in keyword order when the set has two.  nil when no mark
  convicts a tuple nogood `c` keeps over `ms`."
  [kb c ms]
  (when (seq ms)
    (when-let [specs (some #(when (= ms (:members %)) (:specs %)) (nogoods-holding kb c [(first ms)]))]
      (let [tax  (reasoning/taxonomy kb)
            fs   (into #{} (map #(nm/functor (:sentence (p/get-sentex (:records kb) %)))) ms)
            has? #(seq (convicting tax % fs))]
        (first (sort (keep (fn [[kind]]
                             (case kind
                               :self  (when (has? :irreflexive) :irreflexive)
                               :chain (when (has? :anti-transitive) :anti-transitive)
                               :det   :functional
                               :neg   :negates
                               :conv  (cond (has? :anti-symmetric) :anti-symmetric
                                            (has? :asymmetric)     :asymmetric)))
                           specs)))))))

(def ^:private mark-kinds
  "The taxonomy props a tuple nogood is convicted through."
  #{:irreflexive :anti-symmetric :asymmetric :functional :anti-transitive})

(defn under-marks
  "The predicates of `qs` on or below a predicate carrying a mark a tuple nogood is
  convicted through (a `mark-kinds` `:props` set, a `functionalInArg` or a `negates`
  declaration) over the
  unscoped closure: the subtypes of the marked predicates, or one walk up from each of
  `qs` that enters no type an earlier walk found below no mark
  (`tax/genls-global-meets?`), whichever reads fewer.  A `genl` edge below no mark gives
  no tuple nogood a route."
  [tax qs]
  (let [marked (-> (tax/functional-in-arg-predicates tax)
                   (into (tax/negating-predicates tax))
                   (into (mapcat #(tax/props tax %)) mark-kinds))
        qs     (set qs)]
    (cond
      (or (empty? marked) (empty? qs)) #{}
      (< (count qs) (* 4 (count marked)))
      (let [missed (volatile! #{})]
        (into #{} (filter #(tax/genls-global-meets? tax % marked missed)) qs))
      :else (into #{} (comp (mapcat #(tax/specs-global tax %)) (filter qs)) marked))))

(defn owned?
  "Is the placed nogood over `members` with antecedents but the `genlCx` edges `core` one
  this family places (`chain/place-tuples!`): a ground among `core` supports a tuple
  mark's flat-cache key?"
  [tax members core]
  (boolean (some (fn [h] (some (fn [[kind prop]] (or (= :functional-in-arg kind) (= :negates kind)
                                                     (and (= :prop kind) (contains? mark-kinds prop))))
                               (tax/supported-keys tax [h])))
                 (remove (set members) core))))

(defn exempt-at?
  "Does a reader with ancestor set `up` read no nogood over the handles `ms`: two live
  members of one determinant of `c` whose fillers are symbols one class at the reader
  (`same-class-at?`, `hidden?` naming the handles the reader does not believe or see, or
  nil).  False for any other set."
  [kb c ms up hidden?]
  (boolean
   (when (= 2 (count ms))
     (let [[h o] (seq ms)]
       (some (fn [[kind key :as k]]
               (when (and (= ::det kind) (contains? (get-in c [::member-of o]) k))
                 (let [v1 (first (get-in c [::det key h]))
                       v2 (first (get-in c [::det key o]))]
                   (and (not= v1 v2) (symbol-pair? v1 v2) (same-class-at? kb up hidden? v1 v2)))))
             (get-in c [::member-of h]))))))

(def converse-family
  "The self and converse family's entry in `decide/registry`.  Its self tuples are read
  off the self-tuple trie (`self-tuples-under`).  Recover offers the stored facts of the
  predicates under an `anti_symmetric` or `asymmetric` mark to `note-converse!`, and
  queues the self tuples under an `irreflexive` mark.  Each nogood of it is placed as a
  conclusion (`chain/place-tuples!`).

  The marks are read unscoped: a candidate row is a superset over every reader
  (`decide/unscoped-closures`)."
  {:grounds   {:forced-monotonic '#{irreflexive anti_symmetric} :forced-between-predicates '#{genl}}
   :note!     (fn [kb w sx stored?] (note-converse! kb w sx stored?))
   :recovered (fn [kb w]
                (let [recs (:records kb)
                      hs   (marked-facts kb w (mapcat #(tax/props (:tax w) %) converse-marks))]
                  (with-open [r (progress/start ::converse-recovered "recover: read the converse candidates"
                                                (count hs))]
                    (doseq [h (progress/each r hs)
                            :let [sx (p/get-sentex recs h)]
                            :when sx]
                      (note-converse! kb w sx true))))
                (let [self (self-tuples kb w)]
                  (when (seq self)
                    (swap! (reasoning/nogood-candidates kb) update ::moved (fnil into #{}) self))))
   :handles   (fn [_ c] (:converse c))
   :holds?    (fn [_ c h] (contains? (:converse c) h))})

(def marks-family
  "The tuple-mark family's entry in `decide/registry`.  Liveness reads the `genlCx`
  closure, so a moved generation syncs `::live` (`sync-tuples`).  Each nogood of it is
  placed as a conclusion (`chain/place-tuples!`).

  The marks are read unscoped: a candidate row is a superset over every reader
  (`decide/unscoped-closures`)."
  {:grounds   {:forced-monotonic          '#{functional functionalInArg anti_transitive asymmetric negates}
               :forced-between-predicates '#{genl}}
   :note!     (fn [kb w sx stored?]
                (note-tuple! kb w sx stored?)
                (when-not stored? (note-placement-left! kb sx)))
   :recovered (fn [kb w]
                (binding [*functor-marks* (volatile! {})]
                  (let [recs (:records kb)
                        hs   (marked-facts kb w (concat (tax/props (:tax w) :functional)
                                                        (tax/functional-in-arg-predicates (:tax w))
                                                        (tax/props (:tax w) :anti-transitive)
                                                        (tax/negating-predicates (:tax w))))]
                    (with-open [r (progress/start ::marks-recovered "recover: read the tuple-mark candidates"
                                                  (count hs))]
                      (doseq [h (progress/each r hs)
                              :let [sx (p/get-sentex recs h)]
                              :when sx]
                        (note-tuple! kb w sx true))))))
   :synced?   (fn [tax c] (= (tax/relation-gen tax :genlCx) (::ts-gen c 0)))
   :sync      (fn [_ w c] (sync-tuples w c))
   :handles   (fn [_ c] (tuple-members c))
   :holds?    (fn [_ c h] (tuple-member? c h))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N1 :label "Converse candidates" :kind :cache :keyed-by :handle
  :holds-content? false
  :reads [:index :records :T2]
  :retired-by {:stored :K :removed :K :respelled :K :declared :K :edge :K :recover :R
               :image-install :R}
  :computed :write :imaged? :state
  :at [[:nogood-candidates :converse]]
  :bound "one handle per stored binary tuple under an `anti_symmetric` or `asymmetric` mark"
  :note "the stored binary tuples under a converse mark with a stored converse, read off the trie at a write and off the marked extents at recover"})

(caches/register-derived
 {:id :N2 :label "Tuple mark candidates" :kind :cache :keyed-by :value
  :holds-content? false
  :reads [:index :records :T1 :T2]
  :retired-by {:stored :K :removed :K :respelled :K :declared :K :edge :G :edge-belief :G
               :settle-pass :G :recover :R :image-install :R}
  :computed :read :imaged? :state
  :at [[:nogood-candidates ::det] [:nogood-candidates ::det-ctx]
       [:nogood-candidates ::chains] [:nogood-candidates ::conv] [:nogood-candidates ::neg]
       [:nogood-candidates ::member-of] [:nogood-candidates ::live]
       [:nogood-candidates ::ts-gen] [:nogood-candidates ::moved]]
  :bound "one entry per stored tuple under a `functional`, `functionalInArg`, `anti_transitive`, `anti_symmetric` or `asymmetric` mark or a side of a `negates` declaration"
  :note "the determinants holding two fillers, their chains and converses, the `negates` sets, and the members queued for the settle to place again; synced again at a read when the genlCx generation moved from `::ts-gen`"})

(caches/register-derived
 {:id :N9 :label "Candidate recover memos" :kind :pass :keyed-by :functor :reads [:records]
  :holds-content? false
  :retired-by {} :computed :pass :imaged? false
  :note "`*functor-marks*`, bound while `decide/rebuild-candidates!` offers the facts under a tuple mark"})
