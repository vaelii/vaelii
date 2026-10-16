;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ref.nogoods
  "The definitional and inherited nogood families of the belief reference, as pure
  functions of a **view** at one context.

  A view is the map `vaelii.ref.believe` builds for a context C. A family reads three of
  its keys and nothing else:

  - `:believed`, the set of ground sentences believed at C, a denial spelled `(not S)`;
  - `:class`, a function from a sentence to `:monotonic` or `:default` (nil when the
    sentence is not believed);
  - `:genl`, a function from a term to the set holding the term and every believed
    supertype of it at C. Types and predicates share the one closure.

  A family returns a vector of nogoods `{:kind :members :ground}`. `:members` is the set
  of believed sentences that cannot all hold. `:ground` is the set of believed
  declarations and `genl` edges the conviction is read through. Members and `:ground` are
  disjoint for every definitional family (docs/nmtms.md, \"What qualifies as a nogood\":
  the separations and marks are read through and never members). The inherited family
  puts its reasons in `:members`, and its `:ground` holds only the separation a membership
  denies through (docs/inherit.md, \"A contrary claim against a known-true one is a
  contradiction, and is reported\").

  Each family collects its nogoods by member set, so one set of members convicted by two
  declarations is one nogood whose `:ground` holds both. The vector is sorted on a
  printed content key. No function here picks the first element of a set, so the output
  is a function of the view's content and not of the order a set iterates in.

  A `genl` edge in `:ground` or in `:members` is a believed `(genl u v)` sentence lying on
  a route between the two terms the conviction relates: `u` is in the lower term's
  closure and the upper term is in `v`'s. An edge the view's `:genl` answers but no
  believed `genl` sentence states, such as the part edges a believed `covering` installs
  (docs/taxonomy.md, \"A cover states the specialization it rests on\"), convicts through
  the closure and is absent from `:ground`.

  **The reach of a relation mark** (decision D7 of docs/reference.md). A mark on `P`
  (`functional`, `functionalInArg`, `asymmetric`, `irreflexive`, `anti_symmetric`,
  `anti_transitive`) constrains a tuple `(Q ...)` when `P` is in `((:genl view) Q)`. The
  view's `:genl` is the closure over the `genl` sentences believed at C, whatever their
  class. So an edge OUT at C does not carry the mark to C, and a `:default` edge carries
  it exactly as a `:monotonic` edge does. The route edges go in `:ground`, and the
  decision never weighs `:ground`, so an edge's class never changes a verdict. No family
  reads the class of a mark: the marks are forced `:monotonic`, and `vaelii.ref.believe`
  enforces that.

  A nogood may have one member: an `irreflexive` self tuple is convicted alone, and the
  decision weighs a one-member nogood like any other (a `:default` member is OUT, a
  `:monotonic` one is a hard clash). Each family states its own minimum member count;
  `collect` drops no set for its size.

  `families` is the vector `vaelii.ref.believe` decides. No clash is refused (decision
  D8): every conviction here is a nogood.

  Left out, and for the world extraction to refuse rather than for this namespace to
  read: `disjoint_metatype`, `sibling_disjoint`, `separating`, `partition`,
  `orthogonal`, `siblingDisjointException`, `transitiveInArg`, a `transitiveInArgInverse` over any
  relation but `genl`, and an `asymmetric`, `anti_symmetric` or `anti_transitive` step
  reached only by argument preservation.")

;; ---- sentence shapes --------------------------------------------------------

(def ^:private connectives
  "Functors that wrap sentences rather than state a tuple."
  '#{not implies and or unknown exceptWhen except ist})

(defn- variable? [x]
  (and (symbol? x) (.startsWith ^String (name x) "?")))

(defn- atomic-term?
  "A term that is neither a variable nor a compound."
  [x]
  (and (not (coll? x)) (not (variable? x))))

(defn- tuple?
  "A ground atomic sentence: a list whose functor is a symbol other than a connective and
  whose arguments are atomic terms."
  [s]
  (and (seq? s)
       (symbol? (first s))
       (not (contains? connectives (first s)))
       (boolean (seq (rest s)))
       (every? atomic-term? (rest s))))

(defn- membership?
  "A unary tuple `(t x)`: a membership of `x` in the type `t`."
  [s]
  (and (tuple? s) (= 2 (count s))))

(defn- denial-of
  "The tuple a believed `(not L)` denies, or nil when `s` is not a denial of a tuple."
  [s]
  (when (and (seq? s) (= 'not (first s)) (= 2 (count s)) (tuple? (second s)))
    (second s)))

(defn- declarations
  "The believed tuples with functor `f` and `n` arguments."
  [view f n]
  (filterv #(and (tuple? %) (= f (first %)) (= (inc n) (count %))) (:believed view)))

;; ---- the closure and the edges ---------------------------------------------

(defn- up
  "The reflexive `genl` closure of `t` at the view's context."
  [view t]
  (conj (set ((:genl view) t)) t))

(defn- genl-edges
  "Every believed `(genl u v)` sentence."
  [view]
  (declarations view 'genl 2))

(defn- route-edges
  "The believed `genl` edges on some route from `lower` up to `upper`: each `(genl u v)`
  with `u` in `lower`'s closure and `upper` in `v`'s. Empty when the two terms are one."
  [view edges lower upper]
  (if (= lower upper)
    #{}
    (let [below (up view lower)]
      (into #{} (filter (fn [[_ u v]] (and (contains? below u)
                                           (contains? (up view v) upper))))
            edges))))

(defn- simple-routes
  "Every acyclic route of believed `genl` edges from `lower` up to `upper`, each a set of
  edges. Enumerated whole: the reference has no budget."
  [edges lower upper]
  (let [out (group-by second edges)]
    (letfn [(walk [u seen]
              (if (= u upper)
                [#{}]
                (for [[_ _ v :as e] (get out u)
                      :when (not (contains? seen v))
                      route (walk v (conj seen v))]
                  (conj route e))))]
      (set (walk lower #{lower})))))

;; ---- collecting ------------------------------------------------------------

(defn- content-key [ng]
  [(str (:kind ng)) (vec (sort (map pr-str (:members ng))))])

(defn- collect
  "Nogoods grouped by member set, `:ground` unioned, sorted on the content key. A group
  whose convictions carry two kinds takes the least kind in keyword order, so
  `:functional` wins over `:functional-in-arg`. Every set is kept, one member or more."
  [nogoods]
  (->> nogoods
       (group-by :members)
       (map (fn [[members group]]
              {:kind    (first (sort (map :kind group)))
               :members members
               :ground  (into #{} (mapcat :ground) group)}))
       (sort-by content-key)
       vec))

;; ---- disjoint ---------------------------------------------------------------

(defn disjoint
  "The `:disjoint` nogoods at the view's context. docs/taxonomy.md, \"Disjointness\" and
  \"What each constraint does in each arrival order\"; docs/nmtms.md, \"What qualifies as
  a nogood\".

  A believed `(disjoint t1 t2)` with `t1` distinct from `t2` convicts two distinct
  believed memberships `(a X)` and `(b X)` of one term when `t1` is in `a`'s `genl`
  closure and `t2` in `b`'s, or the reverse. Members: the two memberships. `:ground`: the
  declaration and the `genl` edges on the routes from `a` and `b` up to the separated
  types. Any term is separated, not only an individual, so a predicate holding two
  separated types is convicted the same way.

  The explicit arm reads no genl-relatedness guard (docs/taxonomy.md): `(disjoint dog
  animal)` with `(genl dog animal)` convicts `(dog Fido)` beside `(animal Fido)`. The
  write entry point refuses such a declaration when the edge is visible first, and admits
  it when the edge arrives after it.

  `(disjoint a b)` and `(disjoint b a)` both believed make one nogood per pair of
  memberships, with both declarations in `:ground`.

  A declaration over two types one of which is in the other's closure is a one-member
  nogood of the declaration itself, `:ground` the edges of the routes between them
  (decision 8; the ruling on settle prompt 54, item 3). The declaration is forced
  `:monotonic`, so the nogood is a hard clash and moves no belief. One membership whose own
  closure holds both separated types convicts nothing: `(disjoint dog animal)`, `(genl dog
  animal)` and `(dog Fido)` leave `(dog Fido)` believed."
  [view]
  (let [decls  (filterv (fn [[_ t1 t2]] (not= t1 t2)) (declarations view 'disjoint 2))
        edges  (genl-edges view)
        byterm (group-by second (filter membership? (:believed view)))]
    (collect
     (concat
      (for [[_ ms] byterm
            m1     ms
            m2     ms
            :when  (not= m1 m2)
            :let   [a (first m1) b (first m2) ua (up view a) ub (up view b)]
            [_ t1 t2 :as d] decls
            :when  (and (contains? ua t1) (contains? ub t2))]
        {:kind    :disjoint
         :members #{m1 m2}
         :ground  (into #{d} (concat (route-edges view edges a t1)
                                     (route-edges view edges b t2)))})
      (for [[_ t1 t2 :as d] decls
            :let  [lower (cond (contains? (up view t1) t2) t1
                               (contains? (up view t2) t1) t2)]
            :when lower]
        {:kind    :disjoint
         :members #{d}
         :ground  (route-edges view edges lower (if (= lower t1) t2 t1))})))))

;; ---- functional and functionalInArg ------------------------------------------

(defn- functional-marks
  "`[pred position kind declaration]` for every believed `(functional P)` (position 2,
  arity 2 only) and `(functionalInArg P n)`."
  [view]
  (concat
   (for [[_ p :as d] (declarations view 'functional 1)]
     [p 2 :functional d])
   (for [[_ p n :as d] (declarations view 'functionalInArg 2)
         :when (and (integer? n) (pos? n))]
     [p n :functional-in-arg d])))

(defn functional
  "The `:functional` and `:functional-in-arg` nogoods at the view's context.
  docs/taxonomy.md, \"Predicate metadata\" (the `functional` and `functionalInArg`
  entries) and the constraint-marks table below it.

  `(functional P)` constrains position 2 of a binary tuple. `(functionalInArg P n)`
  constrains position `n` (one-based) of a tuple of any arity of at least `n`, and every
  other position together is the determinant; with arity 1 the determinant is empty and
  any two tuples are compared. A mark is read up the predicate hierarchy: a tuple `(Q
  ...)` is constrained by a mark on any `P` in `Q`'s `genl` closure. Two distinct
  believed tuples of equal arity, each under the marked `P`, agreeing on every position
  but `n` and differing at `n`, form a nogood. Members: the two tuples. `:ground`: the
  marks and the predicate `genl` edges from each tuple's functor up to `P`.

  The fillers may be of any kind, symbols included (decision D6 of docs/reference.md). A
  collision is an ordinary nogood: the unique `:default` tuple loses, and two tied
  `:default` tuples are a dilemma. Two symbol fillers with every member `:monotonic` are
  the one case the engine merges through a derived `(equals V1 V2)`. This family returns
  that pair as a nogood too, and `vaelii.ref.believe/decide` gives it the verdict
  `:merge`, which takes nobody OUT. No collision is refused (decision D8): two
  `:monotonic` non-symbol fillers are a hard clash.

  A pair convicted under both spellings is one nogood of kind `:functional`."
  [view]
  (let [marks  (functional-marks view)
        edges  (genl-edges view)
        tuples (filterv tuple? (:believed view))]
    (collect
     (for [t1 tuples
           t2 tuples
           :when (and (not= t1 t2) (= (count t1) (count t2)))
           :let  [k (dec (count t1)) u1 (up view (first t1)) u2 (up view (first t2))]
           [p n kind d] marks
           :when (and (<= n k)
                      (or (= kind :functional-in-arg) (= 2 k))
                      (contains? u1 p) (contains? u2 p))
           :let  [v1 (nth t1 n) v2 (nth t2 n)]
           :when (and (not= v1 v2)
                      (every? #(= (nth t1 %) (nth t2 %))
                              (remove #{n} (range 1 (inc k)))))]
       {:kind    kind
        :members #{t1 t2}
        :ground  (into #{d} (concat (route-edges view edges (first t1) p)
                                    (route-edges view edges (first t2) p)))}))))

;; ---- asymmetric --------------------------------------------------------------

(defn- binary-under
  "The believed binary tuples whose functor has `p` in its `genl` closure."
  [view p]
  (filterv #(and (tuple? %) (= 3 (count %)) (contains? (up view (first %)) p))
           (:believed view)))

(defn- mark-edges
  "The mark and the predicate `genl` edges from each tuple's functor up to `p`."
  [view edges mark p tuples]
  (into #{mark} (mapcat #(route-edges view edges (first %) p)) tuples))

(defn asymmetric
  "The `:asymmetric` nogoods at the view's context. docs/taxonomy.md, \"Predicate
  metadata\" (the `asymmetric` entry); docs/inherit.md, \"`(asymmetric P)`\".

  A believed `(asymmetric P)` convicts two believed binary tuples `(Q1 a b)` and `(Q2 b
  a)` with `a` distinct from `b` and `P` in both functors' `genl` closures. Members: the
  two tuples. `:ground`: the mark and the predicate edges up to `P`. A self tuple `(P a
  a)` is its own converse and convicts nothing. A converse reached only by argument
  preservation is left out."
  [view]
  (let [edges (genl-edges view)]
    (collect
     (for [[_ p :as d] (declarations view 'asymmetric 1)
           :let  [ts (binary-under view p)]
           [_ a b :as t1] ts
           [_ b' a' :as t2] ts
           :when (and (not= a b) (= a a') (= b b'))]
       {:kind :asymmetric :members #{t1 t2} :ground (mark-edges view edges d p [t1 t2])}))))

;; ---- anti_transitive ---------------------------------------------------------

(defn anti-transitive
  "The `:anti-transitive` nogoods at the view's context. docs/nmtms.md, \"A nogood is a
  set: `anti_transitive` has three members\"; docs/taxonomy.md, \"Predicate metadata\".

  A believed `(anti_transitive P)` convicts three believed binary tuples, a first step
  `(Q1 a b)`, a second step `(Q2 b c)` and a direct step `(Q3 a c)`, each with `P` in
  its functor's `genl` closure, so a chain may be spelled half at a sub-predicate.
  Members: the set of the three. The set holds two sentences when two roles coincide, as
  `(P a b)` beside `(P b b)` do. A self tuple `(P a a)` fills all three roles alone and
  convicts nothing, since `anti_transitive` does not imply `irreflexive`
  (docs/taxonomy.md, the `anti_transitive` entry). `:ground`: the mark and the predicate edges up to `P`. A
  step reached only by argument preservation is left out (docs/nmtms.md, \"Where
  conviction is one-sided\")."
  [view]
  (let [edges (genl-edges view)]
    (collect
     (for [[_ p :as d] (declarations view 'anti_transitive 1)
           :let  [ts (binary-under view p)]
           [_ a b :as t1] ts
           [_ b' c :as t2] ts
           :when (= b b')
           [_ a' c' :as t3] ts
           :when (and (= a a') (= c c') (not= t1 t2 t3))]
       {:kind    :anti-transitive
        :members (hash-set t1 t2 t3)
        :ground  (mark-edges view edges d p [t1 t2 t3])}))))

;; ---- covering ---------------------------------------------------------------

(defn- combinations
  "The cartesian product of a sequence of collections, as vectors."
  [colls]
  (reduce (fn [acc c] (for [xs acc x c] (conj xs x))) [[]] colls))

(defn- predicate-spelled?
  "Is `x` spelled as a predicate of arity 2 or more (docs/naming.md): it starts lowercase
  and holds an uppercase letter after its first character."
  [x]
  (and (symbol? x) (boolean (re-matches #"[a-z][a-zA-Z0-9]*[A-Z][a-zA-Z0-9]*" (name x)))))

(defn- holding-edges
  "The `[u v]` edges of the view's closure that hold for every term: each believed `(genl
  u v)` whose class at the view is `:monotonic` or that joins two terms spelled as
  predicates (on the forced-monotonic roster, docs/reference.md D10), and the part edges
  of each believed `covering`, a roster declaration (docs/taxonomy.md, \"A cover states
  the specialization it rests on\")."
  [view]
  (into []
        (mapcat (fn [s]
                  (cond
                    (and (tuple? s) (= 'genl (first s)) (= 3 (count s))
                         (or (= :monotonic ((:class view) s))
                             (every? predicate-spelled? (rest s))))
                    [[(nth s 1) (nth s 2)]]
                    (and (tuple? s) (= 'covering (first s)) (<= 4 (count s)))
                    (for [p (drop 2 s)] [p (second s)])
                    :else [])))
        (:believed view)))

(defn- holding-up
  "The reflexive closure of `t` over the `holding-edges` `edges`, given as `{u #{v}}`."
  [adj t]
  (loop [seen #{t} todo [t]]
    (if-let [u (peek todo)]
      (let [fresh (remove seen (get adj u))]
        (recur (into seen fresh) (into (pop todo) fresh)))
      seen)))

(defn- separation-deniers
  "The members that deny part `p` of a cover held by the membership of type `s` of term
  `x` through a separation (docs/taxonomy.md, \"A separation answers a denial\"), each
  `{:member m :ground g}`: a believed membership `(s' x)` of another type `s'` with a
  believed `(disjoint t1 t2)`, `t1` distinct from `t2`, one of the two in `p`'s closure and
  the other in `s'`'s, both closures read over the `holding-edges` alone. A `:default`
  `genl` edge on either side applies forward and does not contrapose, so it carries no
  denial. `:ground`: the declaration and the `genl` edges on the routes from `p` and `s'`
  up to the separated types."
  [view edges adj decls by-term s x p]
  (for [[s' :as m'] (get by-term x)
        :when (not= s' s)
        :let [up-p (holding-up adj p) up-s (holding-up adj s')]
        [_ t1 t2 :as d] decls
        :let [[tp ts] (cond (and (contains? up-p t1) (contains? up-s t2)) [t1 t2]
                            (and (contains? up-p t2) (contains? up-s t1)) [t2 t1])]
        :when tp]
    {:member m'
     :ground (into #{d} (concat (route-edges view edges p tp) (route-edges view edges s' ts)))}))

(defn covering
  "The `:covering` nogoods at the view's context. docs/taxonomy.md, \"Covering: a whole
  and the parts named against it\" and \"The coverage inference is gated on explicit
  negation\".

  A believed `(covering W P1 ... Pn)` is refuted for a term `X` by a believed membership
  `(S X)` with `W` in `S`'s `genl` closure together with, for every part `Pi`, a believed
  denial `(not (Qi X))` with `Qi` in `Pi`'s closure. A denial of a supertype of a part
  denies the part: `(not (q X))` with `(genl p1 q)` rules out `(p1 X)`. Members: the
  membership and one denial per part, as a set, so one denial ruling out two parts is one
  member. A part with two such denials gives one nogood per choice of denial. `:ground`:
  the declaration and the `genl` edges from `S` up to `W` and from each `Pi` up to its
  `Qi`. A believed membership `(S' X)` of another type a believed `disjoint` separates from
  `Pi` over `:monotonic` edges denies `Pi` as well (`separation-deniers`), and is the member
  for that part, its declaration and edges in `:ground`. A part with no such denier leaves
  the cover unrefuted: the cover is gated on explicit negation and never on absence.

  The declaration is not a member, for `disjoint`'s reason (docs/taxonomy.md): a nogood
  that defeated the cover would find no violation on the next pass and revive it.

  A cover naming a part that a believed `(disjoint P W)` or `(disjoint W P)` separates from
  its whole is a two-member nogood of the cover and the `disjoint`, with an empty `:ground`
  (the ruling on settle prompt 54, item 3). Both are forced `:monotonic`, so it is a hard
  clash and moves no belief."
  [view]
  (let [edges   (genl-edges view)
        covers  (filterv #(and (tuple? %) (= 'covering (first %)) (<= 4 (count %)))
                         (:believed view))
        denials (group-by #(second (denial-of %))
                          (filter #(some-> (denial-of %) membership?) (:believed view)))
        decls   (filterv (fn [[_ t1 t2]] (not= t1 t2)) (declarations view 'disjoint 2))
        adj     (reduce (fn [m [u v]] (update m u (fnil conj #{}) v)) {} (holding-edges view))
        by-term (group-by second (filter membership? (:believed view)))]
    (collect
     (concat
      (for [[_ w & parts :as d] covers
            [s x :as m] (filter membership? (:believed view))
            :when (contains? (up view s) w)
            :let  [per-part (for [p (distinct parts)]
                              (concat
                               (for [den  (get denials x)
                                     :let [q (first (denial-of den))]
                                     :when (contains? (up view p) q)]
                                 {:member den :ground (route-edges view edges p q)})
                               (separation-deniers view edges adj decls by-term s x p)))]
            :when (every? seq per-part)
            combo (combinations per-part)]
        {:kind    :covering
         :members (into #{m} (map :member) combo)
         :ground  (into (conj (route-edges view edges s w) d) (mapcat :ground) combo)})
      (for [[_ w & parts :as cv] covers
            [_ a b :as d] (declarations view 'disjoint 2)
            :when (and (not= a b)
                       (or (and (= a w) (some #{b} parts)) (and (= b w) (some #{a} parts))))]
        {:kind :covering :members #{cv d} :ground #{}})))))

;; ---- supertype --------------------------------------------------------------

(defn supertype
  "The `:supertype` nogoods at the view's context. docs/nmtms.md, \"The membership
  families\".

  A believed membership `(s X)` is refuted by a believed denial `(not (q X))` with `q` in
  `s`'s `genl` closure and distinct from `s`: `(dog Rex)`, `(genl dog animal)` and `(not
  (animal Rex))` cannot all hold. Members: the membership and the denial. `:ground`: the
  `genl` edges on the routes from `s` up to `q`. With `q` equal to `s` the pair is a
  negation nogood, which belongs to no family here."
  [view]
  (let [edges   (genl-edges view)
        denials (group-by #(second (denial-of %))
                          (filter #(some-> (denial-of %) membership?) (:believed view)))]
    (collect
     (for [[s x :as m] (filter membership? (:believed view))
           den (get denials x)
           :let [q (first (denial-of den))]
           :when (and (not= q s) (contains? (up view s) q))]
       {:kind    :supertype
        :members #{m den}
        :ground  (route-edges view edges s q)}))))

;; ---- inherited (transitiveInArgInverse) -------------------------------------

(defn- separated-inherited
  "The arm of `inherited` whose denying side is a membership of a separated type."
  [view]
  (let [edges    (genl-edges view)
        believed (:believed view)]
    (for [[_ p k r :as d] (declarations view 'transitiveInArgInverse 3)
          :when  (and (= 'genl r) (= 1 k))
          [s sub :as m] (filter membership? believed)
          :when  (not= s p)
          [_ t1 t2 :as sep] (declarations view 'disjoint 2)
          :let   [up-p (up view p) up-s (up view s)
                  [tp ts] (cond (and (contains? up-p t1) (contains? up-s t2)) [t1 t2]
                                (and (contains? up-p t2) (contains? up-s t1)) [t2 t1])]
          :when  (and tp (not= t1 t2))
          [_ sup :as claim] (filter membership? believed)
          :when  (and (= p (first claim)) (not= sup sub)
                      (= :monotonic ((:class view) claim)))
          route  (simple-routes edges sub sup)]
      {:kind    :inherited
       :members (into #{m claim d} route)
       :ground  (into #{sep} (concat (route-edges view edges p tp)
                                     (route-edges view edges s ts)))})))

(defn inherited
  "The `:inherited` nogoods at the view's context. docs/inherit.md, \"A contrary claim
  against a known-true one is a contradiction, and is reported\" and \"Strict versus
  typical, from the strength that was already there\"; docs/nmtms.md, \"What qualifies as
  a nogood\" (the `preserving-nogoods` row).

  The one-position downward form. A believed `(transitiveInArgInverse P k genl)` and a believed
  general claim `(P ... sup ...)`, `sup` at position `k`, reach `(P ... sub ...)` for
  every `sub` below `sup` through believed `genl` edges, the other positions unchanged. A
  believed denial `(not (P ... sub ...))` clashes with the reached claim. Members: the
  denial, the general claim, the declaration, and the edges of one route from `sub` up to
  `sup`. `:ground` is empty: the reasons are members, because a reached claim has no
  sentence of its own for a defeat to take out. The family forms one nogood per general
  claim and per acyclic route.

  A general claim whose class at the view's context is `:default` is undercut: it does
  not reach the denied tuple and forms no nogood. The diagonal is excluded: a claim at the
  denied tuple itself pairs with the denial as a negation nogood, which belongs to no
  family here.

  A believed membership `(S sub)` denies the reached `(P sub)` of a unary `P` when a
  believed `(disjoint t1 t2)` separates the two types, `t1` in `P`'s closure and `t2` in
  `S`'s. Members: the membership, the general claim, the declaration and the route edges.
  `:ground`: the `disjoint` declaration and the edges from `P` and `S` up to the separated
  types.

  Left out: `transitiveInArg`; a relation other than `genl` (a `(transitive R)`
  relation, `genlCx`); a claim reached by moving two positions at once, as two
  declarations on one predicate license; a general claim spelled at a sub-predicate of
  `P`; the symmetric mirror, and an `asymmetric` converse as the denying side.

  TODO(spec): the engine names one reading per denial, the reading of highest class and
  the first in content order among equal ones (docs/inherit.md, \"A claim read over
  several routes opposes at its strongest reading\"); this family forms one nogood per
  reading. Smallest view where the two differ, every sentence `:monotonic` except the
  three edges: `(transitiveInArgInverse P 1 genl)`, `(P sup X)`, `(not (P sub X))`, and `(genl
  sub mid)`, `(genl mid sup)`, `(genl sub sup)` each `:default`. The two-edge reading is
  a dilemma and the one-edge reading defeats `(genl sub sup)`. The engine defeats the edge
  only when the one-edge reading comes first in content order."
  [view]
  (let [edges    (genl-edges view)
        believed (:believed view)]
    (collect
     (concat
      (for [[_ p k r :as d] (declarations view 'transitiveInArgInverse 3)
            :when (and (= 'genl r) (integer? k) (pos? k))
            den    believed
            :let   [lit (denial-of den)]
            :when  (and lit (= p (first lit)) (< k (count lit)))
            :let   [sub (nth lit k)]
            claim  believed
            :when  (and (tuple? claim)
                        (= p (first claim))
                        (= (count claim) (count lit))
                        (not= sub (nth claim k))
                        (every? #(= (nth claim %) (nth lit %))
                                (remove #{k} (range 1 (count lit))))
                        (= :monotonic ((:class view) claim)))
            route  (simple-routes edges sub (nth claim k))]
        {:kind :inherited :members (into #{den claim d} route) :ground #{}})
      (separated-inherited view)))))

;; ---- irreflexive and anti_symmetric ------------------------------------------

(defn irreflexive
  "The `:irreflexive` nogoods at the view's context. docs/taxonomy.md, \"Predicate
  metadata\" (the `irreflexive` entry); decision D7 of docs/reference.md.

  A believed `(irreflexive P)` convicts each believed binary self tuple `(Q a a)` with `P`
  in `Q`'s `genl` closure. Members: the self tuple alone, a one-member nogood. `:ground`:
  the mark and the predicate edges from `Q` up to `P`. The decision takes a `:default`
  self tuple OUT and reads a `:monotonic` one as a hard clash, believed and reported."
  [view]
  (let [edges (genl-edges view)]
    (collect
     (for [[_ p :as d] (declarations view 'irreflexive 1)
           [_ a b :as t] (binary-under view p)
           :when (= a b)]
       {:kind :irreflexive :members #{t} :ground (mark-edges view edges d p [t])}))))

(defn anti-symmetric
  "The `:anti-symmetric` nogoods at the view's context. docs/taxonomy.md, \"Predicate
  metadata\" (the `anti_symmetric` entry); decisions D6 and D7 of docs/reference.md.

  A believed `(anti_symmetric P)` convicts two believed binary tuples `(Q1 a b)` and `(Q2
  b a)` with `a` distinct from `b` and `P` in both functors' `genl` closures, whatever the
  arguments are. Members: the two tuples. `:ground`: the mark and the predicate edges up
  to `P`. A self tuple `(P a a)` is its own converse and convicts nothing. A symbol pair
  is returned like any other pair. `vaelii.ref.believe/decide` gives the verdict `:merge`
  to a symbol pair whose two members are `:monotonic`, since the engine derives `(equals
  a b)` from such a pair."
  [view]
  (let [edges (genl-edges view)]
    (collect
     (for [[_ p :as d] (declarations view 'anti_symmetric 1)
           :let  [ts (binary-under view p)]
           [_ a b :as t1] ts
           [_ b' a' :as t2] ts
           :when (and (not= a b) (= a a') (= b b'))]
       {:kind :anti-symmetric :members #{t1 t2} :ground (mark-edges view edges d p [t1 t2])}))))

;; ---- the wiring --------------------------------------------------------------

(def families
  "The nogood families `vaelii.ref.believe` decides, each a function of a view, in the
  order of their names. `vaelii.ref.believe` sorts the nogoods it decides on content, so
  this order changes no answer."
  [anti-symmetric anti-transitive asymmetric covering disjoint functional inherited
   irreflexive supertype])
