;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ref.gen
  "Random worlds inside the reference's v1 fragment, the loader that asserts a world into
  a fresh KB in a given order, the reader of the engine's belief per context, the
  comparators (engine against reference, engine against engine across orders, and a
  report's `:grounds` against the reference's `:ground`), the divergence classifier, the
  shrinker and the failure report.

  A **world** is `{:contexts #{C ...} :writes [{:sentence S :context C :strength k} ...]}`
  (`vaelii.ref.world`).  An **order** is a vector holding each write of a
  world once, so an order stays meaningful after the shrinker drops a write: dropping it
  from every order is `filterv`.

  This namespace requires no reference namespace.  The caller passes the reference in
  `check-world`'s judges map as `:reference`, a function `world -> {C {:believed #{S}
  :out #{S} :inherited #{S} :nogoods [...]}}`.

  The reference judges every write offered (docs/reference.md, \"What the engine has to
  equal\"): a run's refusal is a divergence of kind `:engine-refused-other`
  (`refusal-kind`), and every belief disagreement of a run with no refusal is shrunk to a
  minimal world and given a `:kind` by `classify`.

  Every KB this namespace opens is an in-RAM KB on a space of its own
  (`[::ref n]`, `n` from a process counter).  `run-order` and every caller of it
  close the KB and drop both RAM stores in a `finally`; `load-world!` hands the open KB
  to its caller, who closes it with `close-kb!`."
  (:refer-clojure :exclude [compare])
  (:require [clojure.java.io :as io]
            [clojure.pprint :as pp]
            [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.except :as exc]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu])
  (:import [java.util ArrayList Collections Random]))

;; ---- small helpers -----------------------------------------------------

(defn- pick [^Random rng coll]
  (let [v (vec coll)] (nth v (.nextInt rng (count v)))))

(defn- between
  "A uniform integer in `[lo hi]`, both ends included."
  [^Random rng [lo hi]]
  (+ lo (.nextInt rng (inc (- hi lo)))))

(defn- chance [^Random rng p] (< (.nextDouble rng) p))

(defn- weighted
  "One key of `table`, a seq of `[weight key]`, drawn in proportion to the weights."
  [^Random rng table]
  (let [total (reduce + (map first table))
        r     (.nextInt rng total)]
    (loop [[[w k] & more] table acc 0]
      (if (< r (+ acc (long w))) k (recur more (+ acc (long w)))))))

(defn- shuffled
  "`coll` shuffled by a `Random` seeded with `seed`: the same seed gives the same order."
  [seed coll]
  (let [al (ArrayList. ^java.util.Collection (vec coll))]
    (Collections/shuffle al (Random. (long seed)))
    (vec al)))

(defn permutations
  "Every ordering of the vector `xs`, as vectors, the given order first."
  [xs]
  (let [xs (vec xs)]
    (if (empty? xs)
      [[]]
      (vec (for [i    (range (count xs))
                 more (permutations (into (subvec xs 0 i) (subvec xs (inc i))))]
             (into [(nth xs i)] more))))))

(defn- symbols-in [form]
  (filter symbol? (tree-seq coll? seq form)))

(defn- variable? [x]
  (and (symbol? x) (str/starts-with? (name x) "?")))

(defn rule-sentence?
  "Is `s` a rule write: an `implies`, a `set/forwardRule` or an `exceptWhen` wrapping one?"
  [s]
  (and (seq? s) (contains? #{'implies 'exceptWhen 'set/forwardRule} (first s))))

(defn forward
  "`s` with its `implies` wrapped `set/forwardRule`, inside its `exceptWhen` when it has
  one; a sentence already wrapped, or not a rule, is returned as it is.  A bare `implies`
  is backward-only (docs/inference.md), so a world carries the wrapper and the reference
  and the engine read one shape."
  [s]
  (cond
    (and (seq? s) (= 'implies (first s)))    (list 'set/forwardRule s)
    (and (seq? s) (= 'exceptWhen (first s))) (list 'exceptWhen (second s) (forward (nth s 2)))
    :else s))

(defn- comparable-sentence?
  "Is `s` a sentence the comparators judge: a list with no variable, not a rule and not a
  meta-sentence naming a handle.  Rules are left out on both sides, since the engine
  stores a rule under canonical variable names and the reference is not required to list
  rules among what it believes."
  [s]
  (and (seq? s)
       (not (rule-sentence? s))
       (not-any? #(or (variable? %) (= 'sentexHandle %)) (symbols-in s))))

(defn world-contexts
  "Every context a world's writes name: each write's own context, and both contexts of
  each `(genlCx a b)` sentence."
  [writes]
  (into #{}
        (mapcat (fn [{:keys [sentence context]}]
                  (cons context
                        (when (and (seq? sentence) (= 'genlCx (first sentence)))
                          (rest sentence)))))
        writes))

(defn- functor-of
  "The functor of `s`, or of the sentence a denial `(not S)` wraps; nil for a non-list."
  [s]
  (when (seq? s)
    (if (= 'not (first s)) (functor-of (second s)) (first s))))

;; ---- the generator -----------------------------------------------------

(def default-sizes
  "The v1 sizes, each an inclusive `[lo hi]` range.  `:writes` counts every write, rules
  included."
  {:contexts    [2 4]
   :types       [3 6]
   :individuals [2 4]
   :predicates  [2 3]
   :writes      [4 10]
   :rules       [0 2]})

(defn- letter [i] (char (+ (int \a) i)))

(defn- fresh-pools
  "The world's terms, each with a gensym tail from `tu/fresh-term`, so no two worlds and
  no two KBs share a term.  Types are bare lowercase (`tmptya17`), predicates bare
  lowercase used at arity 2, individuals CapitalCamel, contexts `CxTmp…`.  Each predicate
  carries a kind that fixes its argument shape:

  - `:plain` — two individuals; marks `irreflexive`, `anti_transitive`, `functional`,
    `functionalInArg`, `anti_symmetric`, and `negates` with a predicate of its kind.  Two symbol fillers colliding under a mark are
    a merge only when both are `:monotonic` (decision D6), which `merge-disagreements`
    reads through the engine's equality.
  - `:num` — two integers in 1..3; the same marks.  Two integers never merge.
  - `:type-arg` — a type then an individual; marks `(transitiveInArgInverse P 1 genl)`."
  [rng sizes]
  {:contexts    (vec (for [i (range (between rng (:contexts sizes)))]
                       (tu/fresh-term :context (str "Cx" (str/upper-case (str (letter i)))))))
   :types       (vec (for [i (range (between rng (:types sizes)))]
                       (tu/fresh-term :type (str "ty" (letter i)))))
   :individuals (vec (for [i (range (between rng (:individuals sizes)))]
                       (tu/fresh-term :individual (str "Ind" (str/upper-case (str (letter i)))))))
   :predicates  (vec (for [i (range (between rng (:predicates sizes)))]
                       {:pred (tu/fresh-term :predicate (str "rel" (letter i)))
                        :kind (pick rng [:plain :num :type-arg])}))})

(defn- strength [rng] (if (chance rng 0.35) :monotonic :default))

(defn- type-pair
  "Two distinct types `[sub super]` with `sub` later in the pool than `super`, so every
  `genl` edge and every cover points to an earlier type and the forest has no cycle."
  [rng types]
  (let [i (inc (.nextInt ^Random rng (dec (count types))))
        j (.nextInt ^Random rng i)]
    [(nth types i) (nth types j)]))

(defn- filler
  "One argument for a tuple of predicate kind `kind` (`:plain` or `:num`)."
  [rng kind individuals]
  (if (= :num kind) (inc (.nextInt ^Random rng 3)) (pick rng individuals)))

(defn- tuple [rng {:keys [pred kind]} {:keys [types individuals]}]
  (case kind
    :plain    (list pred (pick rng individuals)
                    (if (chance rng 0.2) ::same (pick rng individuals)))
    :num      (list pred (filler rng kind individuals) (filler rng kind individuals))
    :type-arg (list pred (pick rng types) (pick rng individuals))))

(defn- fix-self
  "Replace the `::same` placeholder a `:plain` self tuple carries with its first argument."
  [t]
  (if (= ::same (last t)) (list (first t) (second t) (second t)) t))

(defn- declaration [rng {:keys [types predicates]}]
  (let [{:keys [pred kind]} (pick rng predicates)
        options (cond-> [:disjoint]
                  (>= (count types) 3)      (conj :covering)
                  (#{:plain :num} kind)     (into [:functional :functional-in-arg
                                                   :anti-symmetric :irreflexive
                                                   :anti-transitive :negates])
                  (= :type-arg kind)        (conj :transitive-in-arg))
        ;; a `negates` partner of the same argument shape, `pred` itself among them
        partner #(pick rng (vec (for [q predicates :when (= kind (:kind q))] (:pred q))))]
    (case (pick rng options)
      :disjoint          (let [[a b] (type-pair rng types)]
                           (list* 'disjoint (sort [a b])))
      :covering          (let [whole-i (.nextInt ^Random rng (- (count types) 2))
                               parts   (->> (subvec types (inc whole-i)) (shuffled (.nextLong ^Random rng))
                                            (take 2) sort)]
                           (list* 'covering (nth types whole-i) parts))
      :irreflexive       (list 'irreflexive pred)
      :anti-transitive   (list 'anti_transitive pred)
      :functional        (list 'functional pred)
      :functional-in-arg (list 'functionalInArg pred (inc (.nextInt ^Random rng 2)))
      :anti-symmetric    (list 'anti_symmetric pred)
      :negates           (list* 'negates (sort [pred (partner)]))
      :transitive-in-arg (list 'transitiveInArgInverse pred 1 'genl))))

(defn- violation
  "A tuple a mark among the writes `acc` convicts, or nil when `acc` holds no
  `irreflexive` or `anti_symmetric` mark: a self tuple `(P a a)` under an `(irreflexive
  P)`, or under an `(anti_symmetric P)` the converse of a tuple of `P` in `acc` with two
  distinct arguments (a fresh pair of distinct arguments when `acc` holds none).  Both
  are nogoods under decision D7, so the generator writes them on purpose."
  [rng {:keys [individuals predicates]} acc]
  (let [kinds (into {} (map (juxt :pred :kind)) predicates)
        marks (vec (for [{s :sentence} acc
                         :when (and (seq? s) (#{'irreflexive 'anti_symmetric} (first s)))]
                     s))]
    (when (seq marks)
      (let [[m p] (pick rng marks)
            kind  (kinds p)
            arg   #(filler rng kind individuals)]
        (if (= 'irreflexive m)
          (let [a (arg)] (list p a a))
          (let [prior (vec (for [{s :sentence} acc
                                 :when (and (seq? s) (= p (first s)) (= 3 (count s))
                                            (not= (nth s 1) (nth s 2)))]
                             s))]
            (if (seq prior)
              (let [[_ a b] (pick rng prior)] (list p b a))
              (let [a (arg) b (first (remove #{a} (shuffled (.nextLong ^Random rng)
                                                            (repeatedly 6 arg))))]
                (when b (list p a b))))))))))

(def ^:private menu-forced-functors
  "The functors of the writes `fact-write` draws that are forced-monotonic:
  the `genlCx` edge and every `declaration` but the separations."
  '#{genlCx functional functionalInArg anti_symmetric irreflexive anti_transitive negates})

(def ^:private menu-denied-functors
  "The functors whose writes `fact-write`'s `:forced-denial` denies: the forced-monotonic
  ones and the separations, which a denial defeats like a type `genl` edge."
  (into menu-forced-functors '#{disjoint covering}))

(defn- fact-write
  "One non-rule write drawn from the menu: a `genlCx` edge, a `genl` edge or its denial, a
  membership or its denial, a tuple or its denial, a declaration, a denial of a forced-monotonic
  write or a separation (one among `acc`, the writes drawn before it, when there is one), or a
  `violation` of a mark among `acc`.  Every write takes a random strength."
  [rng {:keys [contexts types individuals predicates] :as pools} acc]
  (let [ctx   #(pick rng contexts)
        kind  (weighted rng (cond-> [[2 :genl] [1 :genl-denial] [5 :member] [2 :member-denial]
                                     [3 :tuple] [1 :tuple-denial] [3 :declaration]
                                     [1 :forced-denial]]
                              (>= (count contexts) 2) (conj [2 :genl-cx])
                              (some #(#{'irreflexive 'anti_symmetric} (functor-of (:sentence %)))
                                    acc)
                              (conj [2 :violation])))
        write (fn [s c] {:sentence s :context c :strength (strength rng)})]
    (case kind
      :genl-cx       (let [[sub super] (type-pair rng contexts)]
                       (write (list 'genlCx sub super) 'CxUniverse))
      :genl          (let [[sub super] (type-pair rng types)]
                       (write (list 'genl sub (if (chance rng 0.25) 'thing super)) (ctx)))
      :genl-denial   (let [[sub super] (type-pair rng types)]
                       (write (list 'not (list 'genl sub super)) (ctx)))
      :member        (write (list (pick rng types) (pick rng individuals)) (ctx))
      :member-denial (write (list 'not (list (pick rng types) (pick rng individuals))) (ctx))
      :tuple         (write (fix-self (tuple rng (pick rng predicates) pools)) (ctx))
      :tuple-denial  (write (list 'not (fix-self (tuple rng (pick rng predicates) pools))) (ctx))
      :declaration   (write (declaration rng pools) (ctx))
      :forced-denial (let [prior (filterv #(contains? menu-denied-functors (first (:sentence %)))
                                          acc)
                           s     (if (seq prior)
                                   (:sentence (pick rng prior))
                                   (declaration rng pools))]
                       (write (list 'not s) (if (= 'genlCx (first s)) 'CxUniverse (ctx))))
      :violation     (when-let [t (violation rng pools acc)] (write t (ctx))))))

(defn- up-closure
  "`start` plus every type reachable from it over `edges`, a map sub -> #{super}."
  [edges start]
  (loop [seen (set start) todo (vec start)]
    (if-let [t (peek todo)]
      (let [new (remove seen (get edges t))]
        (recur (into seen new) (into (pop todo) new)))
      seen)))

(defn- type-edges
  "sub -> #{super} over every `genl` write and every cover's part -> whole, whatever the
  context or strength: the widest graph a derivation of a membership can follow."
  [writes]
  (reduce (fn [m {s :sentence}]
            (cond
              (and (seq? s) (= 'genl (first s)))
              (update m (nth s 1) (fnil conj #{}) (nth s 2))
              (and (seq? s) (= 'covering (first s)))
              (reduce #(update %1 %2 (fnil conj #{}) (second s)) m (drop 2 s))
              :else m))
          {} writes))

(defn- rule-writes
  "`n` rules over the pools, stratified.  Each rule concludes a membership `(tb ?x)`; a
  body is `(ta ?x)`, or `(and (ta ?x) (P ?x ?y))` over a `:plain` predicate concluding
  `(tb ?y)`, or `(and (ta ?x) (unknown (tu ?x)))`, or the rule is wrapped
  `(exceptWhen (tu ?x) …)`.  `tu` is never a type a rule concludes, a supertype of one
  over `type-edges`, or a type a cover names, so no rule reads the absence of what a
  rule derives; with no such type left the rule takes the plain body."
  [rng {:keys [contexts types predicates]} facts n]
  (let [conclusions (vec (repeatedly n #(pick rng types)))
        edges       (type-edges facts)
        covered     (into #{} (comp (map :sentence)
                                    (filter #(and (seq? %) (= 'covering (first %))))
                                    (mapcat rest))
                          facts)
        blocked     (into (up-closure edges conclusions) covered)
        plain       (filterv #(= :plain (:kind %)) predicates)]
    (vec (for [tb conclusions
               :let [ta    (pick rng (remove #{tb} types))
                     free  (remove (conj blocked ta) types)
                     shape (weighted rng (cond-> [[2 :simple]]
                                           (seq plain) (conj [2 :join])
                                           (seq free)  (into [[3 :unknown] [2 :except]])))
                     tu    (when (seq free) (pick rng free))]]
           {:sentence (forward
                       (case shape
                         :simple  (list 'implies (list ta '?x) (list tb '?x))
                         :join    (list 'implies
                                        (list 'and (list ta '?x) (list (:pred (pick rng plain)) '?x '?y))
                                        (list tb '?y))
                         :unknown (list 'implies
                                        (list 'and (list ta '?x) (list 'unknown (list tu '?x)))
                                        (list tb '?x))
                         :except  (list 'exceptWhen (list tu '?x)
                                        (list 'implies (list ta '?x) (list tb '?x)))))
            :context  (pick rng contexts)
            :strength (strength rng)}))))

(defn- guarded-parts
  "`[ta tb tu]` of a guarded rule sentence of `rule-writes`' shapes: `(and (ta ?x)
  (unknown (tu ?x)))` or `(exceptWhen (tu ?x) …)` over `(ta ?x)`, concluding `(tb ?x)`.
  Nil for an unguarded rule."
  [s]
  (if (= 'exceptWhen (first s))
    (let [[_ [tu] [_ [_ [ta] [tb]]]] s] [ta tb tu])
    (let [[_ [_ ante [tb]]] s]
      (when (and (seq? ante) (= 'and (first ante)) (seq? (nth ante 2))
                 (= 'unknown (first (nth ante 2))))
        (let [[_ [ta] [_ [tu]]] ante] [ta tb tu])))))

(defn- guarded-clash
  "The writes that put a guarded rule's conclusion into a clash with a `:default` member
  (decision D14), or nil when `rules` holds no guarded rule.  For the first guarded rule
  `(ta ?x) ⇒ (tb ?x)`, placed in `k`, and an individual `I`: a `:monotonic` `(ta I)` in
  `k`, and either a `:default` `(not (tb I))` in `k` or a `:monotonic` `(disjoint tb tc)`
  and a `:default` `(tc I)` in `k`, `tc` a type that is neither `ta`, the guard's type,
  nor above or below `tb` over `type-edges`.  The conclusion is `:default`, so the clash
  is a dilemma."
  [rng {:keys [types individuals]} facts rules]
  (when-let [[k [ta tb tu]] (first (keep #(when-let [p (guarded-parts (:sentence %))]
                                            [(:context %) p])
                                         rules))]
    (let [ind    (pick rng individuals)
          edges  (type-edges facts)
          apart  (remove (fn [t] (or (contains? #{ta tb tu} t)
                                     (contains? (up-closure edges [tb]) t)
                                     (contains? (up-closure edges [t]) tb)))
                         types)
          member {:sentence (list ta ind) :context k :strength :monotonic}]
      (if (and (seq apart) (chance rng 0.5))
        (let [tc (pick rng apart)]
          [member
           {:sentence (list* 'disjoint (sort [tb tc])) :context k :strength :monotonic}
           {:sentence (list tc ind) :context k :strength :default}])
        [member {:sentence (list 'not (list tb ind)) :context k :strength :default}]))))

(defn- collision
  "The writes of a mark that merges and two tuples of symbols it convicts, all in one
  context: `(functional P)` over `(P a b)` and `(P a a)`, `(functionalInArg P 1)` over
  `(P b a)` and `(P a a)`, or `(anti_symmetric P)` over `(P a b)` and `(P b a)`, for a
  `:plain` predicate.  The two tuples take one of the four pairs of strengths, so a
  quarter of these worlds hold a merge (decision D6) and the rest a nogood.  In a third
  of the worlds with a `:default` tuple, that tuple also has a `:monotonic` route: a
  `:monotonic` forward rule `(Q ?x ?y) => (P ?x ?y)` over a `:monotonic` `(Q …)` of its
  arguments, for a fresh `Q`, so the merge waits on the route and the order permutations
  move the member's class under an unchanged label.  In a third of the worlds whose tuples
  merge, a `:monotonic` `(disjoint ta tc)` over two types related by no edge of `facts`,
  with `(ta x)` and `(tc y)` in the same context, `x` and `y` drawn from the two merged
  individuals and each at a random strength, so the orders reach a clash member restated
  second and one OUT when the merge arrives.  Nil without a `:plain` predicate or two
  individuals."
  [rng {:keys [contexts individuals predicates types]} facts]
  (let [plain (filterv #(= :plain (:kind %)) predicates)]
    (when (and (seq plain) (<= 2 (count individuals)))
      (let [p       (:pred (pick rng plain))
            c       (pick rng contexts)
            [a b]   (take 2 (shuffled (.nextLong ^Random rng) individuals))
            [s1 s2] (pick rng [[:monotonic :monotonic] [:monotonic :default]
                               [:default :monotonic] [:default :default]])
            [d t u] (pick rng [[(list 'functional p) (list p a b) (list p a a)]
                               [(list 'functionalInArg p 1) (list p b a) (list p a a)]
                               [(list 'anti_symmetric p) (list p a b) (list p b a)]])
            routed  (when (and (some #{:default} [s1 s2]) (chance rng 0.33))
                      (if (= :default s1) t u))
            q       (when routed (tu/fresh-term :predicate "route"))
            clash   (when (and (or routed (= [:monotonic :monotonic] [s1 s2]))
                               (<= 2 (count types)) (chance rng 0.33))
                      (let [edges (type-edges facts)
                            [ta tc] (type-pair rng types)]
                        (when-not (or (contains? (up-closure edges [ta]) tc)
                                      (contains? (up-closure edges [tc]) ta))
                          [{:sentence (list* 'disjoint (sort [ta tc])) :context c :strength :monotonic}
                           {:sentence (list ta (pick rng [a b])) :context c :strength (strength rng)}
                           {:sentence (list tc (pick rng [a b])) :context c :strength (strength rng)}])))]
        (cond-> [{:sentence d :context c :strength :monotonic}
                 {:sentence t :context c :strength s1}
                 {:sentence u :context c :strength s2}]
          routed (into [{:sentence (forward (list 'implies (list q '?x '?y) (list p '?x '?y)))
                         :context  c :strength :monotonic}
                        {:sentence (apply list q (rest routed)) :context c :strength :monotonic}])
          clash  (into clash))))))

(defn- release-below
  "The writes of a clash a context decides and a context below it reads released
  (decision D3), or nil when the world has one context or no third type apart from the
  pair.  For contexts `hi` above `lo`, types `ta` below `tb`, a type `tc` related to
  neither over `type-edges`, and an individual `I`: `(genlCx lo hi)`, and in `hi` a
  `:default` `(genl ta tb)`, a `:monotonic` `(disjoint tb tc)`, a `:default` `(ta I)` and a
  `:monotonic` `(tc I)`; in `lo` a `:monotonic` `(not (genl ta tb))`.  `hi` takes `(ta I)`
  OUT; `lo` takes the edge OUT, reads no clash, and believes `(ta I)`."
  [rng {:keys [contexts types individuals]} facts]
  (when (and (>= (count contexts) 2) (>= (count types) 3))
    (let [[lo hi] (type-pair rng contexts)
          [ta tb] (type-pair rng types)
          ind     (pick rng individuals)
          edges   (update (type-edges facts) ta (fnil conj #{}) tb)
          apart   (remove (fn [t] (or (contains? #{ta tb} t)
                                      (contains? (up-closure edges [ta]) t)
                                      (contains? (up-closure edges [t]) ta)
                                      (contains? (up-closure edges [t]) tb)))
                          types)]
      (when (seq apart)
        (let [tc (pick rng apart)
              w  (fn [s c st] {:sentence s :context c :strength st})]
          [(w (list 'genlCx lo hi) 'CxUniverse :monotonic)
           (w (list 'genl ta tb) hi :default)
           (w (list* 'disjoint (sort [tb tc])) hi :monotonic)
           (w (list ta ind) hi :default)
           (w (list tc ind) hi :monotonic)
           (w (list 'not (list 'genl ta tb)) lo :monotonic)])))))

(defn- blocker-below
  "The writes that make a guarded rule's guard hold at a context below its placement and
  not at the placement (decision D4), or nil when `rules` holds no guarded rule or no
  context follows the rule's in the pool.  For the first guarded rule `(ta ?x) ⇒ (tb ?x)`,
  guarded by `tu` and placed in `k`, a context `lo` after `k` in the pool, and an
  individual `I`: `(genlCx lo k)`, a `(ta I)` in `k` and a `(tu I)` in `lo`.  `k` believes
  `(tb I)` and `lo` does not."
  [rng {:keys [contexts individuals]} rules]
  (when-let [[k [ta _ tu]] (first (keep #(when-let [p (guarded-parts (:sentence %))]
                                           [(:context %) p])
                                        rules))]
    (let [later (drop (inc (.indexOf ^java.util.List contexts k)) contexts)]
      (when (seq later)
        (let [lo  (pick rng later)
              ind (pick rng individuals)]
          [{:sentence (list 'genlCx lo k) :context 'CxUniverse :strength :monotonic}
           {:sentence (list ta ind) :context k :strength (strength rng)}
           {:sentence (list tu ind) :context lo :strength (strength rng)}])))))

(defn- declared-below
  "The writes that make a type forced-monotonic by a declaration below the context its
  memberships are stated in (docs/reference.md D17), or nil when the pools hold fewer than
  two contexts or the two types drawn are related by a written edge.  For two contexts
  `hi` before `lo` in the pool, two types `ta` and `tb`, and an individual `I`: `(genlCx
  lo hi)`, `(disjoint ta tb)`, `(ta I)` and `(tb I)` in `hi`, and
  `(forced_monotonic_predicate ta)` in `lo`; with a second individual `J` no drawn write
  names under `ta`, a `:monotonic` `(not (ta J))` and a `(ta J)` in `hi`.  `lo` reads
  `(tb I)` and the denial defeated; `hi` reads a dilemma and `(ta J)` defeated.  Half
  the draws state the declaration in `CxUniverse` and add `(genlCx hi CxUniverse)`, so both
  contexts read the declaration (docs/reference.md D17).  A drawn rule may read or conclude
  `ta`."
  [rng {:keys [contexts types individuals]} facts]
  (when (>= (count contexts) 2)
    (let [[lo hi] (type-pair rng contexts)
          edges   (type-edges facts)
          [ta tb] (type-pair rng types)]
      (when-not (or (contains? (up-closure edges [ta]) tb) (contains? (up-closure edges [tb]) ta))
        (let [[i & more] (shuffled (.nextLong ^Random rng) individuals)
              ;; the denial pair names an individual no drawn write names under `ta`
              j          (first (remove (fn [x] (some #(#{(list ta x) (list 'not (list ta x))}
                                                        (:sentence %))
                                                      facts))
                                        more))
              core?      (chance rng 0.5)
              w          (fn [s c st] {:sentence s :context c :strength st})]
          (cond-> [(w (list 'genlCx lo hi) 'CxUniverse :monotonic)
                   (w (list* 'disjoint (sort [ta tb])) hi :monotonic)
                   (w (list ta i) hi :default)
                   (w (list tb i) hi :default)
                   (w (list 'forced_monotonic_predicate ta) (if core? 'CxUniverse lo) :default)]
            core? (conj (w (list 'genlCx hi 'CxUniverse) 'CxUniverse :monotonic))
            j (into [(w (list 'not (list ta j)) hi :monotonic)
                     (w (list ta j) hi :default)])))))))

(defn gen-world
  "A random world for `seed`, inside the v1 fragment.  The same seed gives the same
  structure; every term carries a fresh gensym tail, so two calls never share a term.
  `opts` may override any range of `default-sizes`.

  Contexts form a `genlCx` DAG (an edge always points to an earlier context, stored in
  `CxUniverse`); types form a `genl` forest under `thing` the same way; the writes are
  drawn from `fact-write`'s menu without repeating a `[sentence context]` pair; 0–2
  rules come from `rule-writes`; half the worlds holding a guarded rule add the writes of
  `guarded-clash`, a quarter of the worlds the writes of `release-below`, a third the
  writes of `collision`, and a third of the worlds holding a guarded rule the writes of
  `blocker-below`, and a quarter of the worlds the writes of `declared-below`, each less
  any `[sentence context]` pair already drawn.  `:contexts` holds every generated context plus `CxUniverse` when an edge names it."
  [seed opts]
  (let [rng    (Random. (long seed))
        sizes  (merge default-sizes opts)
        pools  (fresh-pools rng sizes)
        total  (between rng (:writes sizes))
        nrules (min (between rng (:rules sizes)) (max 0 (- total 2)))
        facts  (loop [acc [] seen #{} guard 0]
                 (if (or (= (count acc) (- total nrules)) (> guard 200))
                   acc
                   (let [w (fact-write rng pools acc)
                         k [(:sentence w) (:context w)]]
                     (if (or (nil? w) (seen k))
                       (recur acc seen (inc guard))
                       (recur (conj acc w) (conj seen k) (inc guard))))))
        rules  (rule-writes rng pools facts nrules)
        clash  (when (chance rng 0.5) (guarded-clash rng pools facts rules))
        ;; drawn last, so every draw before it reads the numbers it read without it
        below  (when (chance rng 0.25) (release-below rng pools facts))
        ;; drawn after it, for the same reason
        coll   (when (chance rng 0.33) (collision rng pools facts))
        ;; and this after that
        under  (when (chance rng 0.33) (blocker-below rng pools rules))
        ;; and this after that
        decl   (when (chance rng 0.25) (declared-below rng pools facts))
        seen   (into #{} (map (juxt :sentence :context)) facts)
        writes (-> facts
                   (into (remove #(seen [(:sentence %) (:context %)])) clash)
                   (into (remove #(seen [(:sentence %) (:context %)])) below)
                   (into (remove #(seen [(:sentence %) (:context %)])) coll)
                   (into (remove #(seen [(:sentence %) (:context %)])) under)
                   (into (remove #(seen [(:sentence %) (:context %)])) decl)
                   (into rules))]
    {:contexts (into (set (:contexts pools)) (world-contexts writes))
     :writes   writes}))

;; ---- orders ------------------------------------------------------------

(defn orders-for
  "The orders a check runs `world` in: every permutation of its writes when there are at
  most `:exhaustive-up-to` of them, else `:sample` orders — the writes as generated, their
  reverse, and seeded shuffles (`:seed`) of the rest, without repeats."
  [world {:keys [exhaustive-up-to sample seed] :or {exhaustive-up-to 6 sample 8 seed 0}}]
  (let [ws (vec (:writes world))]
    (if (<= (count ws) exhaustive-up-to)
      (permutations ws)
      (->> (concat [ws (vec (rseq ws))]
                   (map #(shuffled (+ (* 1000 seed) %) ws) (range (* 4 sample))))
           distinct
           (take sample)
           vec))))

;; ---- the engine side ---------------------------------------------------

(defonce ^:private space-counter (atom 0))

(defn engine-form
  "The sentence `assert` receives for the world write `s`: `s` under `forward`."
  [s]
  (forward s))

(defn close-kb!
  "Close the KB `load-world!` returned and drop the RAM stores its space held."
  [{:keys [kb space]}]
  (try (some-> kb v/close!)
       (finally
         (when space
           (mem/drop-record-space! space)
           (mem/drop-index-space! space)))))

(def ^:private forced-context
  "The context the forced-monotonic declarations of a world KB are stored in: one no world context
  sees, so no comparison reads them.  Each names a baseline member, which every reader
  reads as forced-monotonic wherever its declaration is stated (`decide/global?`)."
  'CxRefForced)

(defn load-world!
  "A fresh KB on a space of its own, opened with `opts`, holding the
  `forced_monotonic_predicate` declaration of `genlCx` and of every functor in
  `menu-forced-functors` and the `(forced_monotonic_between_predicates genl)` declaration
  (core.txt declares them, and a world KB loads no upper layer), then the
  writes of `order` (a vector of the world's writes) asserted in that order.  A write
  `assert` refuses with an `ex-info` is recorded as
  `{:refused write :type (:type ex-data) :message …}` and loading goes on; any other
  throwable closes the KB and propagates.

  Returns `{:kb kb :space space :refused [...]}`; the caller closes it with `close-kb!`."
  [_world order opts]
  (let [space [::ref (swap! space-counter inc)]
        kb    (v/open-kb (merge {:backend :memory :space space :recover? false} opts))]
    (try
      (doseq [f (sort (conj menu-forced-functors 'genlCx))]
        (v/assert kb (list 'forced_monotonic_predicate f) forced-context))
      (v/assert kb '(forced_monotonic_between_predicates genl) forced-context)
      {:kb      kb
       :space   space
       :refused (into []
                      (keep (fn [{:keys [sentence context strength] :as w}]
                              (try (v/assert kb (engine-form sentence) context
                                             {:strength (or strength :default)})
                                   nil
                                   (catch clojure.lang.ExceptionInfo e
                                     {:refused w
                                      :type    (:type (ex-data e) :untyped)
                                      :message (ex-message e)}))))
                      order)}
      (catch Throwable t
        (close-kb! {:kb kb :space space})
        (throw t)))))

(defn engine-beliefs
  "`{C #{sentence}}` for every context `C` of `world`: the sentences the engine believes
  at `C`, read one sentence at a time (decision D5).

  - A stored literal sentence is read by `believed?` at `C` on its handle, when the
    handle's context is seen from `C` (`believed?` does not test visibility,
    docs/api.md).  Rules, variables, handle-naming meta-sentences
    (`comparable-sentence?`) and edge readings (`exc/edge-read-only?`) are left out.
  - A sentence of `asks` `{C #{S}}` that no handle seen from `C` stores is read by
    `ask?` at `C`: an inherited claim, which the engine answers and never stores.

  A sentence neither stored nor asked is absent here, which reads as OUT."
  ([kb world] (engine-beliefs kb world {}))
  ([kb world asks]
   (let [tms    (reasoning/tms kb)
         stored (into []
                      (keep (fn [h]
                              (let [sx (v/sentex kb h)]
                                (when (and sx (nil? (:antecedent sx)) (not (exc/edge-read-only? tms h)))
                                  (let [s (v/sentence-of sx)]
                                    (when (comparable-sentence? s)
                                      [h s (:context sx)]))))))
                      (v/handles kb))]
     (into {}
           (for [c (:contexts world)
                 :let [seen (filterv (fn [[_ _ ctx]] (or (nil? ctx) (v/sees? kb c ctx))) stored)
                       held (into #{} (keep (fn [[h s _]] (when (v/believed? kb h c) s))) seen)
                       kept (into #{} (map second) seen)]]
             [c (into held
                      (filter #(and (not (kept %)) (v/ask? kb % c)))
                      (sort-by pr-str (get asks c)))])))))

(defn engine-reports
  "Every report of `conflicts` and `contradictions`, as `{:members #{S} :grounds #{S}
  :vantages #{C}}`, with `:canon`, each non-rule write sentence of `world` mapped to the
  sentence the engine stores it as, so a reference sentence is compared in the engine's
  spelling.  `:vantages` is empty for a report weighed at none."
  [kb world]
  {:reports (vec (for [r (concat (v/conflicts kb) (v/contradictions kb))]
                   {:members  (into #{} (map :sentence) (:sides r))
                    :grounds  (into #{} (map :sentence) (:grounds r))
                    :vantages (set (clashes/report-vantages r))}))
   :canon   (into {}
                  (keep (fn [{:keys [sentence context]}]
                          ;; a write the engine refuses has no stored spelling
                          (when (comparable-sentence? sentence)
                            (try [sentence (v/sentence-of
                                            (v/canonical-sentex kb sentence context))]
                                 (catch clojure.lang.ExceptionInfo _ nil)))))
                  (:writes world))})

(defn- individuals-of
  "The individuals `world`'s writes name: every CapitalCamel symbol that is not a context."
  [world]
  (into (sorted-set)
        (comp (mapcat (comp symbols-in :sentence))
              (filter #(Character/isUpperCase (.charAt ^String (name %) 0)))
              (remove #(str/starts-with? (name %) "Cx")))
        (:writes world)))

(defn engine-merges
  "`{C #{#{a b}}}`: the pairs of `world`'s individuals the engine holds equal at each
  context of `world`, read by `ask?` on `(equals a b)`."
  [kb world]
  (let [inds (vec (individuals-of world))]
    (into {}
          (for [c (:contexts world)]
            [c (into #{}
                     (for [i (range (count inds))
                           j (range (inc i) (count inds))
                           :let [a (inds i) b (inds j)]
                           :when (v/ask? kb (list 'equals a b) c)]
                       #{a b}))]))))

(defn- respell
  "`form` with every symbol that is a key of `m` replaced by its value, at any depth."
  [form m]
  (cond (symbol? form) (get m form form)
        (seq? form)    (apply list (map #(respell % m) form))
        :else          form))

(defn engine-displaced
  "`{C {S S'}}`: each stored sentence `S` believed at `C` (`believed?` on its handle, as
  `engine-beliefs` reads it) that names a term of a pair of `merges` (`engine-merges`)
  whose representative at the context `S` is stored in is another term, with `S'`, its
  spelling under those representatives.  A merge supersedes every spelling the fact's own
  context displaces but its own equalities', so each entry is a spelling the merge left
  believed.  A fact stored above the merge stays believed where it lives, and a reader
  below retires its spelling through the read filter (`res/without-retired`,
  docs/equality.md, \"The reader is not the fact's own context\"), which `believed?` does
  not read, so such a fact is no entry."
  [kb merges]
  (let [stored (into [] (keep (fn [h]
                                (let [sx (v/sentex kb h)]
                                  (when (and sx (nil? (:antecedent sx)))
                                    [h (v/sentence-of sx) (:context sx)]))))
                     (v/handles kb))]
    (into {}
          (for [[c pairs] merges
                :let [terms (into #{} cat pairs)
                      ss    (into {}
                                  (keep (fn [[h s cx]]
                                          (when (and (comparable-sentence? s)
                                                     (not (contains? '#{equals sameAs rewriteOf}
                                                                     (functor-of s)))
                                                     (some terms (symbols-in s))
                                                     (v/sees? kb c cx)
                                                     (v/believed? kb h c))
                                            (let [rep (into {} (keep (fn [t]
                                                                       (let [r (v/representative kb t cx)]
                                                                         (when (not= t r) [t r]))))
                                                            (filter terms (symbols-in s)))]
                                              (when (seq rep) [s (respell s rep)])))))
                                  stored)]
                :when (seq ss)]
            [c ss]))))

(defn- recovered-beliefs
  "`engine-beliefs` of the KB `loaded` holds after it is closed and opened again over the
  same RAM stores with `{:recover? true}`, which rebuilds belief from the records alone.
  Closes both KBs; `close-kb!` then drops the stores."
  [{:keys [kb space]} world opts asks]
  (v/close! kb)
  (let [kb' (v/open-kb (merge {:backend :memory :space space :recover? true} opts))]
    (try (engine-beliefs kb' world asks)
         (finally (v/close! kb')))))

(defn run-order
  "Load `world` in `order`, read `engine-beliefs` (asking the sentences of `asks`,
  `{C #{S}}`, through `ask?`), `engine-reports`, `engine-merges` and `engine-displaced`,
  and close the KB.  Returns `{:order order :refused [...] :beliefs {C #{S}} :reports {...}
  :merges {C #{#{a b}}} :displaced {C {S S'}}}`, and with `recover?` also `:recovered`,
  the beliefs the KB reads once closed and recovered (`recovered-beliefs`)."
  ([world order opts] (run-order world order opts {}))
  ([world order opts asks] (run-order world order opts asks false))
  ([world order opts asks recover?]
   (let [loaded (load-world! world order opts)]
     (try
       (let [kb      (:kb loaded)
             beliefs (engine-beliefs kb world asks)
             merges  (engine-merges kb world)]
         (cond-> {:order     order
                  :refused   (:refused loaded)
                  :beliefs   beliefs
                  :reports   (engine-reports kb world)
                  :merges    merges
                  :displaced (engine-displaced kb merges)}
           recover? (assoc :recovered (recovered-beliefs loaded world opts asks))))
       (finally (close-kb! loaded))))))

;; ---- reading the reference ---------------------------------------------

(defn- inherited-at
  "The inherited claims the reference result `ref-c` (one context's map) derives, which
  the engine answers through `ask?` (decision D5)."
  [ref-c]
  (set (:inherited ref-c)))

(defn- merge-at?
  "Does the reference hold a `:merge` verdict at this context (decision D6): an
  all-monotonic symbol-filler functional or anti-symmetric pair, whose belief comparison
  is skipped and counted."
  [ref-c]
  (boolean (some #(= :merge (:verdict %)) (:nogoods ref-c))))

(defn- ref-in? [ref-c s]
  (or (contains? (set (:believed ref-c)) s) (contains? (inherited-at ref-c) s)))

;; ---- comparison --------------------------------------------------------

(defn compare
  "Every disagreement between the reference and the engine, as
  `[{:context C :sentence S :engine bool :reference bool}]`, sorted by context and
  sentence.  For each context of `world` outside `skip` the sentences judged are the
  reference's believed, inherited and OUT sentences and the engine's believed ones
  (`comparable-sentence?` filters all four); a sentence is IN for the reference when it
  is believed or inherited."
  ([world ref-result engine-result] (compare world ref-result engine-result #{}))
  ([world ref-result engine-result skip]
   (vec (for [c (sort-by str (:contexts world))
              :when (not (contains? skip c))
              :let [ref-c    (get ref-result c)
                    eb       (get engine-result c #{})
                    universe (filter comparable-sentence?
                                     (set/union (set (:believed ref-c)) (set (:out ref-c))
                                                (inherited-at ref-c) (set eb)))]
              s (sort-by pr-str universe)
              :let [r (ref-in? ref-c s)
                    e (contains? eb s)]
              :when (not= r e)]
          {:context c :sentence s :engine e :reference r}))))

(defn- joined-pairs
  "The unordered pairs of symbols `pairs` (`[[a b] …]`) join, closed under
  transitivity, as `#{#{a b}}`."
  [pairs]
  (let [classes (reduce (fn [cs [a b]]
                          (let [in (filter #(or (contains? % a) (contains? % b)) cs)]
                            (conj (reduce disj cs in) (into #{a b} cat in))))
                        #{} pairs)]
    (into #{} (for [cls classes a cls b cls :when (neg? (clojure.core/compare a b))] #{a b}))))

(defn reference-merges
  "`{C #{#{a b}}}`: the pairs of symbols the reference's `:merge` verdicts at each
  context of `ref-result` join (decision D6): each argument position where the two
  members differ pairs its two symbols."
  [ref-result]
  (into {}
        (for [[c ref-c] ref-result]
          [c (joined-pairs
              (for [ng (:nogoods ref-c)
                    :when (= :merge (:verdict ng))
                    [x y] (apply map vector (map rest (:members ng)))
                    :when (not= x y)]
                [x y]))])))

(defn merge-disagreements
  "Each context of `world` where the engine's merges in `run` (`engine-merges`) differ
  from the reference's (`reference-merges`), as `{:context :engine :reference :order}`."
  [world ref-result run]
  (let [want (reference-merges ref-result)]
    (vec (for [c (sort-by str (:contexts world))
               :let [e (get (:merges run) c #{}) r (get want c #{})]
               :when (not= e r)]
           {:context c :engine e :reference r :order (:order run)}))))

(defn grounds-disagreements
  "Each engine report of `run` whose `:grounds` differ from the declarations in the
  reference's `:ground` (every sentence but a `genl` edge, which the engine does not
  name), unioned over the reference's nogoods with the same members at the report's
  vantages (every context of `ref-result` for a report weighed at none), as
  `{:members :engine :reference :vantages :order}`.  A report no such nogood matches is
  left to the belief comparison."
  [ref-result run]
  (let [{:keys [reports canon]} (:reports run)
        spell (fn [ss] (into #{} (map #(get canon % %)) ss))]
    (vec (for [{:keys [members grounds vantages]} reports
               :let [vs  (if (seq vantages) (filter #(contains? ref-result %) vantages)
                             (keys ref-result))
                     ngs (for [c vs, ng (:nogoods (get ref-result c))
                               :when (= members (spell (:members ng)))]
                           ng)
                     want (spell (remove #(and (seq? %) (= 'genl (first %)))
                                         (mapcat :ground ngs)))]
               :when (and (seq ngs) (not= want grounds))]
           {:members members :engine grounds :reference want :vantages vantages
            :order (:order run)}))))

(defn- refused-set [run] (into #{} (map :refused) (:refused run)))

(defn- run-disagreements
  "The belief disagreements between two runs of one world, each naming both orders."
  [world a b]
  (vec (for [c (sort-by str (:contexts world))
             :let [ba (get (:beliefs a) c #{}) bb (get (:beliefs b) c #{})]
             s (sort-by pr-str (set/union ba bb))
             :let [x (contains? ba s) y (contains? bb s)]
             :when (not= x y)]
         {:context c :sentence s :order-a (:order a) :order-b (:order b) :a x :b y})))

(defn order-disagreements
  "Engine-against-engine over `runs` of one world.  Runs are grouped by the set of writes
  the engine refused, since two runs that stored different content may believe
  differently; within a group each run is compared with the group's first."
  [world runs]
  (vec (for [[_ group] (sort-by (comp count key) (group-by refused-set runs))
             b         (rest group)
             d         (run-disagreements world (first group) b)]
         d)))

;; ---- refusals ----------------------------------------------------------

(defn refusal-kind
  "The divergence kind of an engine refusal `{:refused w :type t …}`:
  `:engine-refused-other`.  The reference judges every write offered (decision D8), so
  every refusal of a generated write is a divergence."
  [_refusal]
  :engine-refused-other)

;; ---- the check ---------------------------------------------------------

(defn check-world
  "Run `world` in every order of `orders` and judge it against the reference over the
  writes offered (decision D8).  Returns

    {:refusals    [{:kind k :refusal w :type t :message m :order o
                    :beliefs [disagreement …]} …]   ; one per refusal per run; :beliefs
                                                     ; holds that run's belief differences
     :reference   [disagreement …]  ; engine against reference in the runs that refused
                                    ; nothing, each with the :order it was read in
     :grounds     [disagreement …]  ; `grounds-disagreements` in the runs that refused
                                    ; nothing
     :merges      [disagreement …]  ; `merge-disagreements` in the runs that refused
                                    ; nothing
     :orders      [disagreement …]  ; `order-disagreements`
     :recovered   [disagreement …]  ; engine against reference after the first order's
                                    ; KB is closed and recovered, when it refused nothing
     :displaced   [{:context C :sentence S :respelled S' :order o} …]
                                    ; at a context of :merge-skips, a spelling the
                                    ; engine's own merge displaces there and it believes,
                                    ; with its spelling under the representatives
                                    ; (`engine-displaced`)
     :merge-skips #{C …}            ; contexts skipped for a :merge verdict (D6)
     :refused     [{:refused w :type t :message m} …]  ; every refusal, distinct
     :store-split bool              ; did two orders store different content
     :runs        n}

  `judges` is a map.  `:reference` is `world -> {C {:believed :out :inherited
  :nogoods}}`, called once on the whole world.  `:kb-opts` is merged into each KB's
  `open-kb` options.  An inherited claim of the reference at `C` is read from the engine
  through `ask?` at `C`.  The first order's KB is also closed, recovered and read again
  (`run-order`'s `recover?`), since belief is a function of the records."
  [world orders {:keys [reference kb-opts]}]
  (let [ref    (reference world)
        asks   (into {} (for [[c ref-c] ref :let [i (inherited-at ref-c)] :when (seq i)] [c i]))
        skip   (into #{} (keep (fn [[c ref-c]] (when (merge-at? ref-c) c))) ref)
        runs   (into [] (map-indexed #(run-order world %2 kb-opts asks (zero? %1))) orders)
        judged (mapv (fn [r] [r (compare world ref (:beliefs r) skip)]) runs)]
    {:refusals    (vec (for [[r ds] judged
                             rf     (:refused r)]
                         (assoc rf :kind (refusal-kind rf) :order (:order r) :beliefs ds)))
     :reference   (vec (for [[r ds] judged
                             :when (empty? (:refused r))
                             d ds]
                         (assoc d :order (:order r))))
     :grounds     (vec (for [r runs
                             :when (empty? (:refused r))
                             d (grounds-disagreements ref r)]
                         d))
     :merges      (vec (for [r runs
                             :when (empty? (:refused r))
                             d (merge-disagreements world ref r)]
                         d))
     :orders      (order-disagreements world runs)
     :recovered   (vec (for [r (take 1 runs)
                             :when (empty? (:refused r))
                             d (compare world ref (:recovered r) skip)]
                         (assoc d :order (:order r))))
     :displaced   (vec (for [r runs
                             c (sort-by str skip)
                             [s s'] (sort-by (comp pr-str key) (get (:displaced r) c))]
                         {:context c :sentence s :respelled s' :order (:order r)}))
     :merge-skips skip
     :refused     (vec (distinct (mapcat :refused runs)))
     :store-split (< 1 (count (distinct (map refused-set runs))))
     :runs        (count runs)}))

;; ---- shape readers for the classifier ------------------------------------

(defn- context-up
  "`c` plus every context it sees over the `genlCx` writes of `writes` (every such write
  counts: decision D1 makes each one monotonic, and a denial of one moves no edge)."
  [writes c]
  (let [adj (reduce (fn [m {[f a b] :sentence}]
                      (if (= 'genlCx f) (update m a (fnil conj #{}) b) m))
                    {} (filter #(seq? (:sentence %)) writes))]
    (up-closure adj [c])))

(defn- conjuncts
  "The literals of an antecedent or exception form: an `(and …)`'s arguments, a
  vector's elements, or the form alone."
  [form]
  (cond (vector? form)                            (vec form)
        (and (seq? form) (= 'and (first form)))  (vec (rest form))
        :else                                    [form]))

(defn- rule-shape
  "`{:consequent C :antecedents [literal …] :guards [[literal …] …]}` for a rule sentence
  of the generator's shapes: the join antecedents, and one guard per `(unknown X)`
  antecedent and per `exceptWhen` exception, a set of conjuncts whose holding blocks the
  firing.  Nil for a sentence that is not a rule."
  [s]
  (when (rule-sentence? s)
    (let [[exc body] (if (= 'exceptWhen (first s)) [(second s) (nth s 2)] [nil s])
          body       (if (= 'set/forwardRule (first body)) (second body) body)
          [_ ante c] body
          lits       (conjuncts ante)]
      {:consequent  c
       :antecedents (vec (remove #(and (seq? %) (= 'unknown (first %))) lits))
       :guards      (cond-> (vec (for [l lits :when (and (seq? l) (= 'unknown (first l)))]
                                   (conjuncts (second l))))
                      exc (conj (conjuncts exc)))})))

(defn- bind
  "The bindings under which the pattern `p` equals the ground sentence `s`, or nil."
  [p s]
  (when (and (seq? p) (seq? s) (= (count p) (count s)))
    (reduce (fn [b [x y]]
              (cond (and (variable? x) (contains? b x)) (if (= (b x) y) b (reduced nil))
                    (variable? x)                        (assoc b x y)
                    (and (seq? x) (seq? y))              (if-let [b' (bind x y)]
                                                           (merge b b')
                                                           (reduced nil))
                    (= x y)                              b
                    :else                                (reduced nil)))
            {} (map vector p s))))

(defn- substitute [form b]
  (cond (variable? form) (get b form form)
        (seq? form)      (apply list (map #(substitute % b) form))
        (vector? form)   (mapv #(substitute % b) form)
        :else            form))

(defn- guarded-firings
  "`[[rule-write guard-instances] …]`: for each guarded rule of `world` visible at `c`
  whose consequent matches `s`, each guard instantiated under that match."
  [world c s]
  (let [up (context-up (:writes world) c)]
    (for [{r :sentence k :context :as w} (:writes world)
          :let [{:keys [consequent guards]} (rule-shape r)]
          :when (and (seq guards) (contains? up k))
          :let [b (bind consequent s)]
          :when b
          g guards]
      [w (mapv #(substitute % b) g)])))

;; ---- classification ----------------------------------------------------

(defn- exception-not-reasked?
  "Decision D4: the engine believes `s` at `c` where the reference does not; `s` is the
  conclusion of a guarded rule visible at `c`, every conjunct of one guard instance is
  believed at `c` in the reference, and a strict ancestor of `c` believes `s` in the
  reference: the blocking fact is visible at the reader and not at the placement."
  [world ref {:keys [context sentence engine reference]}]
  (let [ref-c (get ref context)]
    (and engine (not reference)
         (boolean (some (fn [[_ g]] (every? #(contains? (set (:believed ref-c)) %) g))
                        (guarded-firings world context sentence)))
         (boolean (some #(and (not= context %) (ref-in? (get ref %) sentence))
                        (context-up (:writes world) context))))))

(def classifiers
  "The belief-disagreement shapes, as `[kind predicate]` in the order `classify` tries
  them.  Each predicate reads the minimal world, the reference's result on it and the
  disagreement `{:context :sentence :engine :reference :order}`."
  [[:exception-not-reasked-below-placement exception-not-reasked?]])

(defn classify
  "The `:kind` of the belief disagreement `d` read in the minimal world `world`, whose
  reference result is `ref`: the first kind of `classifiers` whose shape matches, else
  `:unclassified`.  Best-effort: a shape names the mechanism a known engine defect
  follows, read off the world's content, and cannot prove the engine followed it."
  [world ref d]
  (or (some (fn [[k pred]] (when (pred world ref d) k)) classifiers)
      :unclassified))

;; ---- shrinking ---------------------------------------------------------

(defn- drop-write [world w]
  (update world :writes #(filterv (partial not= w) %)))

(defn- drop-context
  "`world` without context `c`: the writes stored in `c` or naming it leave with it."
  [world c]
  (-> world
      (update :contexts disj c)
      (update :writes (fn [ws] (filterv #(and (not= c (:context %))
                                              (not (some #{c} (symbols-in (:sentence %)))))
                                        ws)))))

(defn shrink
  "The smallest world `failing?` still fails on, reached by dropping writes one at a time
  while the failure persists, then dropping contexts (with the writes that name them)
  the same way.  `failing?` is `world -> failure-or-nil` (`failing-under`).  Returns
  `{:world minimal :failure (failing? minimal)}`; when `world` itself passes, `:failure`
  is nil and `:world` is `world`."
  [world failing?]
  (if-let [f (failing? world)]
    (let [[w1 f1] (loop [w world f f]
                    (if-let [[w' f'] (first (keep (fn [x]
                                                    (let [c (drop-write w x)]
                                                      (when-let [f' (failing? c)] [c f'])))
                                                  (:writes w)))]
                      (recur w' f')
                      [w f]))
          [w2 f2] (loop [w w1 f f1]
                    (if-let [[w' f'] (first (keep (fn [c]
                                                    (let [cand (drop-context w c)]
                                                      (when-let [f' (failing? cand)] [cand f'])))
                                                  (sort-by str (:contexts w))))]
                      (recur w' f')
                      [w f]))]
      {:world w2 :failure f2})
    {:world world :failure nil}))

(defn failing-under
  "A `failing?` for `shrink` that holds one belief disagreement `target` (`{:context
  :sentence :engine}`) fixed: re-run a candidate world in `orders` projected onto its
  writes, judged by `judges` (`check-world`'s third argument), and answer the candidate's
  reference disagreement on the same context, sentence and engine answer, or nil.  A
  candidate the reference refuses as outside the fragment passes."
  [judges orders {:keys [context sentence engine]}]
  (fn [world]
    (let [keep?  (set (:writes world))
          orders (vec (distinct (map #(filterv keep? %) orders)))]
      (try
        (first (filter #(and (= context (:context %)) (= sentence (:sentence %))
                             (= engine (:engine %)))
                       (:reference (check-world world orders judges))))
        (catch clojure.lang.ExceptionInfo e
          (when-not (= :unsupported (:type (ex-data e))) (throw e)))))))

;; ---- divergences -------------------------------------------------------

(defn divergences
  "Every divergence `check` (`check-world`'s result on `world`) holds, each with a
  `:kind`, deduplicated:

  - one per refused write, `{:kind (refusal-kind …) :category :refusal :refusal w :type t
    :message m :runs n :belief-differences n}`, the belief differences summed over the
    runs that refused it;
  - one per `[context sentence engine-answer]` of the reference disagreements,
    `{:kind k :category :reference :context :sentence :engine :reference :orders [o …]
    :world minimal :minimal d}`: the world shrunk while that disagreement persists
    (`shrink`, `failing-under` over at most two of the orders it was read in), and `k`
    from `classify` on the minimal world;
  - one per member set whose report's `:grounds` differ from the reference's
    declarations (`grounds-disagreements`), `{:kind :grounds-differ :category :grounds
    :members :engine :reference :vantages :orders [o …]}`;
  - one per context and pair of merge sets that differ (`merge-disagreements`),
    `{:kind :merge-differs :category :merges :context :engine :reference :orders [o …]}`;
  - one per `[context sentence]` of `:displaced`, a spelling the engine's own merge
    displaces at a context the belief comparison skips and the engine believes there,
    `{:kind :displaced-spelling :category :displaced-spelling :context :sentence :orders
    [o …]}`;
  - one per recovered disagreement, `{:kind :recover-differs :category :recovered
    :context :sentence :engine :reference :order}`;
  - one per engine-against-engine disagreement no divergence above accounts for (none
    is expected: a disagreement between two runs that refused nothing is a reference
    disagreement of one of them, and one between two runs that refused the same writes
    is reported under those refusals), `{:kind :unclassified :category :orders …}`."
  [world check judges]
  (let [refusals (for [[[w k] rs] (group-by (juxt :refused :kind) (:refusals check))]
                   {:kind               k
                    :category           :refusal
                    :refusal            w
                    :type               (:type (first rs))
                    :message            (:message (first rs))
                    :runs               (count rs)
                    :belief-differences (reduce + (map (comp count :beliefs) rs))})
        refs     (for [[[c s e] ds] (group-by (juxt :context :sentence :engine) (:reference check))
                       :let [orders (vec (take 2 (distinct (map :order ds))))
                             {mw :world mf :failure}
                             (shrink world (failing-under judges orders
                                                          {:context c :sentence s :engine e}))
                             mf     (or mf (first ds))
                             kind   (classify mw ((:reference judges) mw) mf)]]
                   {:kind      kind
                    :category  :reference
                    :context   c
                    :sentence  s
                    :engine    e
                    :reference (:reference (first ds))
                    :orders    orders
                    :world     mw
                    :minimal   mf})
        grounds  (for [[[m e r] ds] (group-by (juxt :members :engine :reference) (:grounds check))]
                   {:kind      :grounds-differ
                    :category  :grounds
                    :members   m
                    :engine    e
                    :reference r
                    :vantages  (:vantages (first ds))
                    :orders    (vec (take 2 (distinct (map :order ds))))})
        merges   (for [[[c e r] ds] (group-by (juxt :context :engine :reference) (:merges check))]
                   {:kind      :merge-differs
                    :category  :merges
                    :context   c
                    :engine    e
                    :reference r
                    :orders    (vec (take 2 (distinct (map :order ds))))})
        displaced (for [[[c s] ds] (group-by (juxt :context :sentence) (:displaced check))]
                    {:kind     :displaced-spelling
                     :category :displaced-spelling
                     :context  c
                     :sentence s
                     :orders   (vec (take 2 (distinct (map :order ds))))})
        ;; a displaced spelling believed in one order is, in another, its restatement
        ;; believed: both halves of that orders disagreement are this divergence
        covered  (-> #{}
                     (into (map (juxt :context :sentence)) (:reference check))
                     (into (mapcat (juxt (juxt :context :sentence) (juxt :context :respelled)))
                           (:displaced check)))
        refusing (into #{} (comp (map :order)) (:refusals check))
        orphans  (for [d (:orders check)
                       :when (not (or (covered [(:context d) (:sentence d)])
                                      (refusing (:order-a d)) (refusing (:order-b d))))]
                   (assoc d :kind :unclassified :category :orders))
        recovered (for [d (:recovered check)]
                    (assoc d :kind :recover-differs :category :recovered))]
    (vec (concat (sort-by #(pr-str (:refusal %)) refusals)
                 (sort-by #(pr-str [(:context %) (:sentence %)]) refs)
                 (sort-by #(pr-str (sort-by pr-str (:members %))) grounds)
                 (sort-by #(pr-str [(:context %) (:engine %) (:reference %)]) merges)
                 (sort-by #(pr-str [(:context %) (:sentence %)]) displaced)
                 orphans
                 recovered))))

;; ---- reporting ---------------------------------------------------------

(defn default-report-dir
  "`vaelii-ref` under the platform temp directory (`java.io.tmpdir`)."
  []
  (io/file (System/getProperty "java.io.tmpdir") "vaelii-ref"))

(defn summary
  "One line naming a divergence `d` of `divergences` for `seed`: its kind and category,
  what disagreed, and the size of the minimal world when it was shrunk."
  [seed d]
  (str "seed " seed ": " (name (:kind d)) " (" (name (:category d)) ") "
       (case (:category d)
         :refusal   (let [w (or (:refused d) (:refusal d))]
                      (str "engine refused " (pr-str (:sentence w)) " in " (:context w)
                           " as " (:type d) " in " (:runs d) " run(s)"))
         :reference (str "at " (:context d) " on " (pr-str (:sentence d)) ", engine "
                         (:engine d) " reference " (:reference d) "; minimal world "
                         (count (:writes (:world d))) " writes, "
                         (count (:contexts (:world d))) " contexts; order "
                         (pr-str (mapv (juxt :sentence :context :strength)
                                       (:order (:minimal d) (first (:orders d))))))
         :grounds   (str "over " (pr-str (sort-by pr-str (:members d))) " at "
                         (pr-str (sort (:vantages d))) ", engine grounds "
                         (pr-str (sort-by pr-str (:engine d))) " reference declarations "
                         (pr-str (sort-by pr-str (:reference d))))
         :orders    (str "at " (:context d) " on " (pr-str (:sentence d)) ", order a "
                         (:a d) " order b " (:b d))
         :merges    (str "at " (:context d) ", engine merges " (pr-str (:engine d))
                         " reference merges " (pr-str (:reference d)))
         :recovered (str "after a recover, at " (:context d) " on " (pr-str (:sentence d))
                         ", engine " (:engine d) " reference " (:reference d))
         :displaced-spelling (str "at " (:context d) " the engine believes "
                                  (pr-str (:sentence d)) ", a spelling its merge displaces"))))

(defn report!
  "Write the divergence `d` of `seed` as EDN into `dir` (default `default-report-dir`),
  and return `summary` followed by the file's path."
  ([seed d] (report! seed d (default-report-dir)))
  ([seed d dir]
   (let [f (io/file dir (str "reference-divergence-seed" seed "-"
                             (System/currentTimeMillis) ".edn"))]
     (io/make-parents f)
     (spit f (with-out-str (pp/pprint (assoc d :seed seed))))
     (str (summary seed d) " — " (.getPath f)))))
