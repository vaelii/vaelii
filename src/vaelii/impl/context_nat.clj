;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.context-nat
  "The structural genlCx producer for reified-NAT contexts — docs/context-nat.md.

  A `(contextArgSubrelation F pos R)` declaration says two `F`-contexts are ordered by the
  sub-relation `R` at argument `pos`.  Two `F`-contexts are ordered when they differ only
  at declared positions and each differing argument of the sub is `R`-below the other's,
  the product order.  This namespace reads the declarations and the context NATs of `F`
  from the store and **materializes** each such `genlCx` edge as a **justified** sentex in
  CxUniverse, never a premise.  `R` is resolved by a bounded oracle: a registered pure
  comparator, else the `genlCx` closure for a sub-relation in `closure-orders` and each
  believed stored `(R a b)` fact."
  (:require [vaelii.impl.datetime :as datetime]
            [vaelii.impl.except :as exc]
            [vaelii.impl.graph :as graph]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:private universal-context sx/root-context)

;; ---- the bounded R oracle -------------------------------------------------

(defn- comparator-holds?
  "True iff a registered comparator for `r` (`datetime/order-comparators`) answers that
  `a` is `R`-below `b`.  A comparator reads the two terms' shape alone, so the producer may
  call it inside the relabel loop."
  [r a b]
  (boolean (when-let [f (get datetime/order-comparators r)] (f a b))))

(def ^:private closure-orders
  "The sub-relations the `genlCx` closure answers between two contexts, before a stored
  fact: `genlMonad`, since a monad's time is Forever, so a monad that sees another is
  genlMonad-below it."
  #{'genlMonad})

(def ^:private bound-heads
  "The functors of a stated bound: the facts `bounds-routes` reads."
  '#{startOf endOf})

(def ^:private order-heads
  "The functors of a stated strict order between two moments, `instantBefore` and its
  converse `instantAfter`: the facts `instant-path` reads."
  '#{instantBefore instantAfter})

(defn- named? [x] (and (symbol? x) (not (sx/variable? x))))

(defn- ordered-from
  "Each believed stated order placing a moment after the moment `n` (`later?`) or before it,
  as `[moment handle]` in content order: `(instantBefore n m)` and `(instantAfter m n)` for
  a later `m`, `(instantBefore m n)` and `(instantAfter n m)` for an earlier one."
  [kb later? n]
  (->> [['instantBefore (if later? [n '?x] ['?x n]) (if later? 2 1)]
        ['instantAfter  (if later? ['?x n] [n '?x]) (if later? 1 2)]]
       (mapcat (fn [[h args i]] (map #(vector (nth (:sentence %) i) %)
                                     (kb/sentexes-matching kb (cons h args) '?ctx))))
       (nm/sort-by-content-key (fn [[_ sx]] [(:context sx) (:sentence sx)]))
       (map (fn [[m sx]] [m (:id sx)]))))

(defn- instant-path
  "The handles of the believed stated orders along the path from the moment `a` to the
  moment `b` that a breadth-first walk from `a` reaches first, each moment's later moments
  read in content order (`ordered-from`, `graph/bfs-tree`); nil when none reaches `b`."
  [kb a b]
  (when (seq (ordered-from kb false b))
    (let [step (fn [n tree] (keep (fn [[m h]] (when-not (contains? tree m) [m [n h]]))
                                  (ordered-from kb true n)))
          {:keys [found tree]} (graph/bfs-tree [[a nil]] step #(= b %))]
      (when found
        (loop [n b hs ()]
          (if-let [[m h] (get tree n)] (recur m (conj hs h)) (vec hs)))))))

(def ^:private ^:dynamic *walked*
  "nil, or inside `reconcile-order` of the moment `a` before `b`, `[a lm b hm]`: `lm` a delay
  of the moments at or before `a`, `hm` of those at or after `b` (`moments-along`)."
  nil)

(defn- reaches?
  "Does a chain of believed stated orders lead from the moment `a` to the distinct moment
  `b`?  True without a walk when `*walked*` shows `a` at or before its `a` and `b` at or
  after its `b`, or one of the two equal to its moment; else `graph/reaches?`."
  [kb a b]
  (or (when-let [[x lm y hm] *walked*]
        (let [lo? (contains? @lm a)]
          (or (and lo? (= b x)) (and (= a y) (contains? @hm b)) (and lo? (contains? @hm b)))))
      (graph/reaches? #(map first (ordered-from kb true %)) #(map first (ordered-from kb false %)) a b)))

(defn- before
  "A delay of the facts showing the bound `a` falls before `b`, or at or before it unless
  `strict?`, each bound six fields or a named moment: `[]` when the fields order them, or
  one bound is both and `strict?` is false; else `instant-path`'s.  nil when neither shows
  it, which `reaches?` answers before any path is read."
  [kb strict? a b]
  (let [term #(if (vector? %) (apply list 'InstantFn %) %)]
    (cond
      (and (vector? a) (vector? b)) (when ((if strict? neg? (complement pos?)) (compare a b)) (delay []))
      (= a b)                       (when-not strict? (delay []))
      :else                         (let [ta (term a) tb (term b)]
                                      (when (reaches? kb ta tb) (delay (instant-path kb ta tb)))))))

(def ^:private bounds-orders
  "The sub-relations a time's stated bounds decide, `{R (fn [lower-extent upper-extent])}`
  answering the comparisons `[strict? x y]` (`before`) the order needs past the bounds, nil
  when the extents' shape refuses it, over the half-open extents `bounds-routes` reads:
  `subintervalOf` between two intervals, and `subtimeOf` from a moment, whose extent is
  `[t t]`, into an interval, or into an extent with no end at its start."
  {'subintervalOf (fn [[as ae] [bs be]]
                    (when (and ae be (not= as ae) (not= bs be))
                      [[false bs as] [false ae be]]))
   'subtimeOf     (fn [[t u] [bs be]]
                    (cond
                      (not= t u) nil
                      (nil? be)  (when (= t bs) [])
                      :else      [[false bs t] [true t be]]))})

(defn- stated-bounds
  "Each believed `(P x t)` fact, `P` `startOf` or `endOf`, as `[bound handle]` in content
  order: `t`'s six fields for an `InstantFn` moment, `t` itself for a named moment."
  [kb p x]
  (->> (kb/sentexes-matching kb (list p x '?i) '?ctx)
       (keep #(let [t (nth (:sentence %) 2)]
                (when-let [b (or (datetime/instant-fields t) (when (named? t) t))] [b (:id %) %])))
       (nm/sort-by-content-key (fn [[_ _ sx]] [(:context sx) (:sentence sx)]))
       (map pop)))

(defn- own-extent
  "The half-open extent the term `x` names by its spelling (`datetime/extent`, an
  `InstantFn` moment `[t t]`), or nil."
  [x]
  (or (datetime/extent x) (some-> (datetime/instant-fields x) (#(vector % %)))))

(defn- extents
  "Each half-open extent the time `x` can be read as, `[[start end] handles]`: a term's own
  (`own-extent`), resting on nothing stored; else one per pair of a believed stated
  `startOf` and `endOf` of `x` (`stated-bounds`), the start before the end when both are
  fields, resting on the two facts, and one per stated start with no end, `[s nil]`; else,
  for a symbol with no stated bound, the named moment `[x x]`, resting on nothing."
  [kb x]
  (if-let [e (own-extent x)]
    [[e []]]
    (when (symbol? x)
      (let [ss (stated-bounds kb 'startOf x)
            es (stated-bounds kb 'endOf x)]
        (if (and (empty? ss) (empty? es))
          [[[x x] []]]
          (concat
           (for [[s hs] ss
                 [e he] es
                 :when (if (and (vector? s) (vector? e)) (neg? (compare s e)) (not= s e))]
             [[s e] [hs he]])
           (for [[s hs] ss] [[s nil] [hs]])))))))

(defn- bounds-routes
  "The routes ordering `a` `R`-below `b` by the two times' extents (`extents`), one vector
  of the stated bounds and the `instantBefore` facts each rests on, for an `R` in
  `bounds-orders` and two times of which at least one has stated bounds: a pair of terms is
  the comparator's alone."
  [kb r a b]
  (when-let [holds? (get bounds-orders r)]
    (when (or (symbol? a) (symbol? b))
      (for [[ea ha] (extents kb a)
            [eb hb] (extents kb b)
            :when (seq (concat ha hb))
            :let  [ds (some->> (holds? ea eb) (map (fn [[s x y]] (before kb s x y))))]
            :when (and ds (every? some? ds))
            :let  [evs (mapv deref ds)]
            :when (every? some? evs)]
        (reduce into (-> ha (into hb)) evs)))))

(defn- r-evidence
  "The beliefs the relationship `a` `R`-below `b` rests on, one vector of handles per route
  that holds, empty when none does: `[[]]` when a comparator answers it (a pure function of
  the two expressions, already carried by the `natFormula` antecedents); else, for an `R`
  in `closure-orders`, one supporter per edge along a path from `a` up to `b` that `a` sees
  (`tax/reach-support`, a content-ordered walk), for an `R` in `bounds-orders`, the stated
  bounds of each reading of the two extents that holds (`bounds-routes`), and the handle
  of each believed `(R a b)` fact, in context order.  Every route holding is a
  justification, so which arrived first decides none of them."
  [kb r a b]
  (if (comparator-holds? r a b)
    [[]]
    (concat
     (when (contains? closure-orders r)
       (let [tx (reasoning/taxonomy kb)]
         (when (and (not= a b) (tax/sees? tx a b))
           (some->> (tax/reach-support tx :genlCx a b a) (mapv first) not-empty vector))))
     (bounds-routes kb r a b)
     (->> (kb/sentexes-matching kb (list r a b) '?ctx)
          (sort-by :context)
          (map #(vector (:id %)))))))

;; ---- reading the declarations and the context NATs ------------------------

(defn any-context-subrelations?
  "Presence check: does the KB declare any `contextArgSubrelation`?  The producer is a no-op
  otherwise — one O(1) functor count per assert, the shape `res/any-corresponding-predicates?`
  has."
  [kb]
  (pos? (reads/stored-count-with-functor (:index kb) 'contextArgSubrelation)))

(defn- subrelation-declarations
  "Believed `(contextArgSubrelation F pos R)` declarations as `[F pos R handle]`, kept
  where `(pred? F)` — all of them, or only those for one function.  A declaration is read
  as its own context believes it (`exc/believed-own?`): a computed edge is seen from every
  context, so a declaration a defeat hides where it is stated builds none."
  [kb pred?]
  (for [sx  (kb/sentexes-matching kb '(contextArgSubrelation ?f ?pos ?r) '?ctx)
        :let [[_ f pos r] (:sentence sx)]
        :when (and (pred? f) (exc/believed-own? kb (:id sx)))]
    [f pos r (:id sx)]))

(defn- context-nat-entry
  "`[k expr nat-formula-handle]` when `sx` is a believed `(natFormula K E)` map in
  CxUniverse with `K` a `cx/` constant and `E` an application of `f`, else nil."
  [kb f sx]
  (let [[_ k e] (:sentence sx)]
    (when (and (= universal-context (:context sx))
               (= 'natFormula (nm/functor (:sentence sx)))
               (jtms/in? (reasoning/tms kb) (:id sx))
               (nat-read/reified-context-symbol? k)
               (sequential? e) (= f (first e)))
      [k e (:id sx)])))

(defn- context-nats-of
  "Every believed context NAT whose expression head is `f`, as `context-nat-entry`'s
  triples, read through the inverted term index on `f`, which descends into a ground
  compound, so an expression's head is one of the sentex's posted terms.  A declaration's
  arrival reads this; a mint and an edge read `context-nats-naming`."
  [kb f]
  (->> (kb/find-sentexes kb f) (keep #(context-nat-entry kb f %)) distinct))

(defn- context-nats-naming
  "The believed context NATs of `f` whose expression names one of `terms`: one
  intersection of the term index on `f` and on each term (`kb/find-sentexes-all`)."
  [kb f terms]
  (->> terms
       (mapcat #(kb/find-sentexes-all kb [f %]))
       (keep #(context-nat-entry kb f %))
       distinct))

(defn- context-nat-of
  "The entry of the context NAT `k`'s own believed map, or nil: one argument-root read."
  [kb k]
  (some (fn [sx] (let [e (nth (:sentence sx) 2 nil)]
                   (when (sequential? e) (context-nat-entry kb (first e) sx))))
        (kb/sentexes-matching kb (list 'natFormula k '?e) universal-context)))

(defn- product-key
  "The identity of a context NAT's group under the declared positions `ps`: its expression
  with every argument at a position of `ps` masked, so two contexts share a key iff they
  agree on every undeclared argument.  `pos` is 1-based over the function's arguments,
  hence the expression index `pos` (index 0 is the functor).  A declared position past the
  expression's arity, which nothing at the assert entry point refuses, masks nothing."
  [expr ps]
  (reduce (fn [v pos] (if (and (integer? pos) (pos? (long pos)) (< (long pos) (count v)))
                        (assoc v pos '_)
                        v))
          (vec expr) ps))

(defn- declarations-by-position
  "`F`'s believed declarations as `{pos [[R declaration-handle] …]}`."
  [kb f]
  (reduce (fn [m [_ pos r declH]] (update m pos (fnil conj []) [r declH]))
          {} (subrelation-declarations kb #(= f %))))

;; ---- materialization ------------------------------------------------------

(defn- any-built?
  "Did one of the materializations `ms` add a justification?  Realizes every one."
  [ms]
  (reduce #(or %2 %1) false ms))

(defn- materialize-edge
  "Deduce `(genlCx sub super)` in CxUniverse, justified by `antes`, unless a violation
  refuses it (a genlCx edge over two `cx/` contexts is admissible except a self-edge, which
  the caller already excludes).  Idempotent: a second call with the same antecedents adds
  no justification, and a different route adds another supporter of the one edge.  What
  the edge shows the contexts under `sub` is the settle's (`special/drain-context-moves!`),
  as for an asserted or a concluded edge.  Returns true when it added a justification.

  Bare: it adds one derived sentex and one justification, and the JTMS withdraws the edge
  when an antecedent stops being believed — nothing here destroys stored knowledge, so
  nothing in this chain carries a `!`."
  [kb sub super antes]
  (let [edge (list 'genlCx sub super)
        tms  (reasoning/tms kb)]
    (when-not (special/inadmissible kb edge universal-context)
      (let [[h2 s2 new?] (kb/find-or-create-sentex kb edge universal-context)
            _            (when new? (special/derived-sentex-added kb s2 h2))
            depth        (inc (reduce max 0 (map #(jtms/depth tms %) antes)))
            antes        (vec antes)]
        (jtms/ensure-node tms h2 depth)
        (when-not (jtms/has-justification? tms 'contextArgSubrelation antes h2)
          (let [jid  (p/next-id (:records kb))
                just (jtms/->just jid 'contextArgSubrelation antes h2 {} :monotonic)]
            (p/put-justification (:records kb) just)
            (jtms/add-justification tms just)
            true))))))

(defn- pure-first
  "The positions `ps` with a comparator-resolved declaration first, so a pair fails on a
  shape read before a closure walk or a fact read."
  [decls ps]
  (sort-by (fn [pos] (if (some #(contains? datetime/order-comparators (first %)) (decls pos)) 0 1))
           ps))

(defn- pair-routes
  "The routes ordering the context of expression `esub` below that of `esup` under
  `decls` (`declarations-by-position`): one vector per choice, at each differing position,
  of a declaration and a route its `R` holds by there (`r-evidence`), holding each choice's
  declaration handle and evidence handles.  Empty when the two differ at a position `decls`
  names no declaration for, or at one where no declared `R` holds."
  [kb decls esub esup]
  (let [diff (filterv #(not= (nth esub %) (nth esup %)) (range 1 (count esub)))]
    (if (and (seq diff) (every? decls diff))
      (reduce (fn [routes pos]
                (let [a   (nth esub pos)
                      b   (nth esup pos)
                      evs (for [[r declH] (decls pos)
                                ev (r-evidence kb r a b)]
                            (into [declH] ev))]
                  (if (seq evs) (for [rt routes ev evs] (into rt ev)) (reduced ()))))
              [[]] (pure-first decls diff))
      ())))

(defn- reconcile-pairs
  "Materialize the structural genlCx edges of function `f` over the ordered pairs `pairs`
  gives, `(pairs decls)` → `[[k expr nat-formula-handle] …]` pairs, `decls` being
  `declarations-by-position`: each pair gets one justification per route
  (`pair-routes`), from both `natFormula` maps and the route.  Returns true when an edge
  gained a justification."
  [kb f pairs]
  (let [decls (declarations-by-position kb f)]
    (when (seq decls)
      (any-built?
       (for [[[ksub esub th-sub] [ksup esup th-sup]] (pairs decls)
             route (pair-routes kb decls esub esup)]
         (materialize-edge kb ksub ksup (into [th-sub th-sup] route)))))))

(defn- all-pairs
  "Every ordered pair of distinct contexts of `f` that agree on every undeclared argument
  (`product-key`): what a declaration arriving owes."
  [kb f]
  (fn [decls]
    (for [[_ nats] (group-by #(product-key (second %) (keys decls)) (context-nats-of kb f))
          x nats y nats :when (not= (first x) (first y))]
      [x y])))

(defn- comparable-terms
  "The terms the oracle can find `R`-below or `R`-above `a`, `a` among them, or nil when a
  comparator answers `R`, whose terms no index enumerates: for an `R` in
  `closure-orders`, the contexts `tax/context-routed-global` gives above and below `a`, a
  superset of the scoped closure `r-evidence` decides a pair under; and the other end of
  every believed stored `(R a x)` and `(R x a)`."
  [kb r a]
  (when-not (contains? datetime/order-comparators r)
    (let [tx (reasoning/taxonomy kb)]
      (cond-> (-> #{a}
                  (into (map #(nth (:sentence %) 2)) (kb/sentexes-matching kb (list r a '?x) '?ctx))
                  (into (map #(nth (:sentence %) 1)) (kb/sentexes-matching kb (list r '?x a) '?ctx)))
        (and (symbol? a) (contains? closure-orders r))
        (-> (into (tax/context-routed-global tx :fwd a))
            (into (tax/context-routed-global tx :rev a)))))))

(defn- declared-in
  "The positions of `decls` inside the expression `e`'s arity whose declarations pass
  `ok?`, least first."
  [e decls ok?]
  (sort (for [[pos ds] decls :when (and (integer? pos) (< 0 (long pos) (count e)) (ok? ds))] pos)))

(defn- comparator? [[r]] (contains? datetime/order-comparators r))

(defn- comparable-read
  "`[p ts]`: the least declared position of `e`'s arity whose sub-relations no comparator
  answers, and the terms `comparable-terms` gives there; nil with no such position."
  [kb e decls]
  (when-let [p (first (declared-in e decls #(not-any? comparator? %)))]
    [p (into #{} (mapcat #(comparable-terms kb (first %) (nth e p))) (decls p))]))

(defn- agreeing
  "The context NATs of `cands` other than one of `e` that agree with `e` on every
  argument `decls` declares no position for (`product-key`)."
  [e decls cands]
  (let [ks (keys decls) key (product-key e ks)]
    (filter #(and (not= e (second %)) (= key (product-key (second %) ks))) cands)))

(defn- candidates
  "Every context of `f` other than one of expression `e` that agrees with `e` on every
  undeclared argument and could be ordered against it: at `comparable-read`'s position, a
  context holding one of its terms, read by term (`context-nats-naming`); with no such
  position, every context of `f`."
  [kb f e decls]
  (agreeing e decls
            (if-let [[p ts] (comparable-read kb e decls)]
              (filter #(contains? ts (nth (second %) p nil)) (context-nats-naming kb f ts))
              (context-nats-of kb f))))

(defn- context-nats-keyed
  "The believed context NATs of `f` whose expression names one of `terms`, read by each
  term's own term-index key beside `f`'s (`reads/as-stored-with-terms`): for a ground
  compound in the expression, a key a store indexed at `sx/*min-indexed-depth*` 2 or
  less holds."
  [kb f terms]
  (->> terms
       (mapcat #(reads/as-stored-with-terms (:index kb) [f (sx/canon %)]))
       distinct
       (keep #(some->> (p/get-sentex (:records kb) %) (context-nat-entry kb f)))))

(defn- range-term? [x] (and (sequential? x) (= datetime/range-function (first x))))

(defn- containing-read
  "`[q ts]` for a read of `e`'s unwritten context, or nil: the least declared position `q`
  all of whose declarations a comparator answers and where `e` holds a time with
  `datetime/containing-terms`, and the terms a context ordered above `e`'s holds there
  unless it holds a range: those, each symbol with a stated bound (`bounds-routes`) and
  the other end of each believed stored `(R t x)`.  Nil also when the postings beside `f`
  at those terms and the range function, with the stated bounds, number `n` or more."
  [kb f e decls n]
  (let [ix (:index kb)]
    (when (<= (long sx/*min-indexed-depth*) 2)
      (when-let [[q cs] (some #(some->> (datetime/containing-terms (nth e %)) (vector %))
                              (declared-in e decls #(every? comparator? %)))]
        (when (< (+ (transduce (map #(count (reads/as-stored-with-terms ix [f (sx/canon %)]))) + 0
                               (conj cs datetime/range-function))
                    (transduce (map #(reads/stored-count-with-functor ix %)) + 0 bound-heads))
                 n)
          [q (-> cs
                 (into (for [h bound-heads, sx (kb/sentexes-matching kb (list h '?x '?t) '?ctx)
                             :let [x (nth (:sentence sx) 1)] :when (named? x)] x))
                 (into (for [[r] (decls q), sx (kb/sentexes-matching kb (list r (nth e q) '?x) '?ctx)]
                         (nth (:sentence sx) 2))))])))))

(defn- above-candidates
  "The `candidates` a read of `e`'s unwritten context needs, those its context could be
  ordered below: at `containing-read`'s position, a context holding one of its terms or a
  range (`context-nats-keyed`), when it reads fewer postings than `candidates`; else
  `candidates`."
  [kb f e decls]
  (let [ix (:index kb)
        n  (if-let [[_ ts] (comparable-read kb e decls)]
             (transduce (map #(count (reads/as-stored-with-terms ix [f %]))) + 0 ts)
             (count (reads/as-stored-with-term ix f)))]
    (if-let [[q ts] (containing-read kb f e decls n)]
      (agreeing e decls (filter #(let [x (nth (second %) q nil)] (or (contains? ts x) (range-term? x)))
                                (context-nats-keyed kb f (conj ts datetime/range-function))))
      (candidates kb f e decls))))

(defn- pairs-with
  "The pairs, each way, of the context NAT `k` with each of its `candidates`."
  [kb f k]
  (fn [decls]
    (when-let [[_ e _ :as m] (context-nat-of kb k)]
      (for [o (candidates kb f e decls)
            :when (not= k (first o))
            pr [[m o] [o m]]]
        pr))))

(defn- unminted-supers
  "The context NATs the producer would order the context of `expr` below, were it minted,
  as `[k natFormula-handle]` in `k` order: each of `expr`'s `above-candidates` with a
  route (`pair-routes`).  For a read of a context nobody has written into, which sees what
  these contexts see (docs/context-nat.md).  Reads the declarations and the oracle and
  writes nothing; nil on a KB declaring no `contextArgSubrelation`."
  [kb expr]
  (when (and (sequential? expr) (any-context-subrelations? kb))
    (let [f     (first expr)
          decls (declarations-by-position kb f)]
      (when (seq decls)
        (->> (above-candidates kb f expr decls)
             (filter (fn [[_ e _]] (seq (pair-routes kb decls expr e))))
             (map (fn [[k _ th]] [k th]))
             (sort-by (comp nm/name-key first)))))))

(defn unwritten-read
  "`[k read-kb]` for a read of the context of `expr` nobody has written into: `k` the
  `cx/` constant its content names, `read-kb` `kb` with a `genlCx` edge from `k` to each
  of `unminted-supers` (`kb/with-context-edges`); nil when there are none.  Held among the
  resident values under the change clock (`observe/cached`), so the reads between two
  writes share one read copy and its caches."
  [kb expr]
  (observe/cached (reasoning/qcn kb) [::unwritten-read expr tax/*search* tax/*network-belief*]
                  (fn [_]
                    (when-let [supers (seq (unminted-supers kb expr))]
                      (let [k (nat/constant-for nat-read/context-namespace expr)]
                        [k (kb/with-context-edges kb k supers)])))))

(defn- pairs-across
  "The pairs of `f`'s contexts that agree on every undeclared argument, whose sub holds, at a
  position `decls` orders by `r`, a term at or below `x`, and whose super holds one at or
  above `y` there: equal, or for an `r` in `closure-orders`, a context
  `tax/context-routed-global` gives, a superset of the scoped closure `r-evidence` decides
  a pair under.  Each side is read by term (`context-nats-naming`), the sub side first,
  and an empty sub side reads no super side."
  [kb f r x y]
  (fn [decls]
    (let [ps     (for [[pos ds] decls :when (some #(= r (first %)) ds)] pos)
          tx     (reasoning/taxonomy kb)
          closed (and (contains? closure-orders r) (symbol? x) (symbol? y))
          side   (fn [ts] (filter (fn [[_ e]] (some #(contains? ts (nth e % nil)) ps))
                                  (context-nats-naming kb f ts)))
          subs   (side (cond-> #{x} closed (into (tax/context-routed-global tx :rev x))))]
      (when (seq subs)
        (let [ks   (keys decls)
              sups (group-by #(product-key (second %) ks)
                             (side (cond-> #{y} closed (into (tax/context-routed-global tx :fwd y)))))]
          (for [s subs
                t (get sups (product-key (second s) ks))
                :when (not= (first s) (first t))]
            [s t]))))))

(defn- functions-ordered-by
  "The context functions some believed declaration orders by sub-relation `r`: the
  functions an `(R a b)` fact arriving after both contexts is new evidence in, since `R`
  is all the fact says about which function an edge belongs to."
  [kb r]
  (when (symbol? r)
    (distinct (for [[f _ r' _] (subrelation-declarations kb (constantly true))
                    :when (= r r')]
                f))))

(defn- reconcile-bounded
  "The pairs of each context naming one of the times `xs`, in the functions a `bounds-orders`
  relation orders (`pairs-with`).  Returns true when an edge gained a justification."
  [kb xs]
  (any-built?
   (for [f (distinct (mapcat #(functions-ordered-by kb %) (keys bounds-orders)))
         [k _ _] (context-nats-naming kb f xs)]
     (reconcile-pairs kb f (pairs-with kb f k)))))

(defn- moments-along
  "The moment `a` and each moment a believed chain of stated orders places after it
  (`later?`) or before it."
  [kb later? a]
  (graph/reach-all [a] #(map first (ordered-from kb later? %))))

(defn- bounded-along
  "The moments `ms` and each time with a stated bound among them, in content order: one side
  of every pair of times an order between two moments arriving can order."
  [kb ms]
  (nm/sort-by-content-key identity
                          (into ms (for [m ms h bound-heads
                                         sx (kb/sentexes-matching kb (list h '?x m) '?ctx)]
                                     (nth (:sentence sx) 1)))))

(defn- contexts-at
  "The contexts of `f` holding, at one of the positions `ps`, one of the times `ts`, or a
  term whose own extent (`own-extent`) starts or ends at the fields of an `InstantFn` moment
  among `ts`, which reads every context of `f`."
  [kb f ps ts]
  (let [ts  (set ts)
        fs  (into #{} (keep datetime/instant-fields) ts)
        at? (fn [[_ e]] (some #(let [t (nth e % nil)]
                                 (or (contains? ts t) (some fs (own-extent t))))
                              ps))]
    (filter at? (if (seq fs) (context-nats-of kb f) (context-nats-naming kb f ts)))))

(defn- reconcile-order
  "The pairs a stated order of the moment `a` before `b` arriving can order, in the
  functions a `bounds-orders` relation orders: each context holding a time at or before `a`
  (`bounded-along`) against each holding one at or after `b`, both ways, at a position such
  a relation orders, every comparison reading the two walks through `*walked*`.  An empty
  first side reads no second.  Returns true when an edge gained a justification."
  [kb a b]
  (let [lm    (delay (moments-along kb false a))
        hm    (delay (moments-along kb true b))
        lo    (delay (bounded-along kb @lm))
        hi    (delay (bounded-along kb @hm))
        pairs (fn [f decls]
                (let [ps  (for [[pos ds] decls :when (some #(contains? bounds-orders (first %)) ds)] pos)
                      ks  (keys decls)
                      los (contexts-at kb f ps @lo)]
                  (when (seq los)
                    (let [his (group-by #(product-key (second %) ks) (contexts-at kb f ps @hi))]
                      (for [l  los
                            h  (get his (product-key (second l) ks))
                            :when (not= (first l) (first h))
                            pr [[l h] [h l]]]
                        pr)))))]
    (binding [*walked* [a lm b hm]]
      (any-built?
       (for [f (distinct (mapcat #(functions-ordered-by kb %) (keys bounds-orders)))]
         (reconcile-pairs kb f (partial pairs f)))))))

(defn- reconcile-arrival
  "The pairs a believed `sentence` arriving can order: for a `(contextArgSubrelation F …)`
  declaration, every pair of `F`'s contexts; for a `(natFormula K E)` map with `K` a `cx/`
  constant, the pairs `K` is in (`pairs-with`); for a stated `(startOf x t)` or `(endOf x
  t)`, `reconcile-bounded` over `x`, and for a stated order between two moments,
  `reconcile-order`; for an `(R a b)` fact on a declared sub-relation, the pairs
  across `a` and `b` (`pairs-across`) in the functions declared to order by `R`, and for a
  `(genlCx a b)` edge, the same per sub-relation in `closure-orders`.  Any other sentence
  creates no pair and reconciles nothing.  Returns true when an edge gained a justification."
  [kb sentence]
  (when (and (sequential? sentence) (seq sentence))
    (let [[head x y] sentence]
      (cond
        (= 'contextArgSubrelation head)
        (reconcile-pairs kb x (all-pairs kb x))

        (and (= 'natFormula head) (nat-read/reified-context-symbol? x) (sequential? y) (seq y))
        (reconcile-pairs kb (first y) (pairs-with kb (first y) x))

        (contains? bound-heads head)
        (reconcile-bounded kb [x])

        (contains? order-heads head)
        (if (= 'instantBefore head) (reconcile-order kb x y) (reconcile-order kb y x))

        :else
        (any-built?
         (for [r (if (= 'genlCx head) closure-orders [head])
               f (functions-ordered-by kb r)]
           (reconcile-pairs kb f (pairs-across kb f r x y))))))))

(defn- reconcile-edge-move
  "What a `genlCx` edge `[a b]` a settle moved owes: an edge between two context NATs that
  is no longer believed, the pair `a`, `b` again, since a second route can hold it; any
  other edge `a` now sees `b` through, a computed one included, its arrival
  (`reconcile-arrival`).  An edge that left the closure owes nothing more, since each
  computed edge resting on it moves too."
  [kb [a b]]
  (if (and (nat-read/reified-context-symbol? a) (nat-read/reified-context-symbol? b)
           (not (some->> (kb/find-sentex-handle kb (list 'genlCx a b) universal-context)
                         (jtms/in? (reasoning/tms kb)))))
    (when-let [ea (context-nat-of kb a)]
      (when-let [eb (context-nat-of kb b)]
        (let [f (first (second ea))]
          (when (= f (first (second eb)))
            (reconcile-pairs kb f (constantly [[ea eb]]))))))
    (when (tax/sees? (reasoning/taxonomy kb) a b)
      (reconcile-arrival kb (list 'genlCx a b)))))

(defn- declared-heads
  "The functors whose sentences `reconcile-arrival` reads: `contextArgSubrelation`,
  `natFormula`, every sub-relation a believed declaration names, and the `bound-heads` and
  `order-heads` when one of those is in `bounds-orders`."
  [kb]
  (let [rs (into #{} (map #(nth % 2)) (subrelation-declarations kb (constantly true)))]
    (cond-> (into '#{contextArgSubrelation natFormula} rs)
      (some bounds-orders rs) (into (into bound-heads order-heads)))))

(defn- reconcile-moves*
  "`reconcile-moves` past its presence checks."
  [kb {:keys [edges arrived derived]}]
  (let [recs  (:records kb)
        tms   (reasoning/tms kb)
        heads (when (or (seq arrived) (seq derived)) (declared-heads kb))
        ss    (for [h (into (set arrived) (mapcat #(get derived %)) heads)
                    :let [s (some-> (p/get-sentex recs h) sx/sentence-of)]
                    :when (and (seq? s) (contains? heads (first s)) (jtms/in? tms h))]
                s)]
    (any-built?
     (concat (map #(reconcile-arrival kb %) (nm/sort-by-content-key identity (set ss)))
             (map #(reconcile-edge-move kb %) (sort-by (fn [e] (mapv nm/name-key e)) (set edges)))))))

(defn reconcile-moves
  "The structural genlCx maintenance the belief moves `moves` call for, once the write that
  moved them has settled.  `moves` is what `special/take-producer-moves!` answers:
  `:edges`, the `genlCx` edges the write's settles moved, each reconciled by
  `reconcile-edge-move`; `:arrived`, handles revived, and `:derived`, handles derived by
  functor, each read as an arrival when believed and of a functor `declared-heads` names.
  Edges and sentences are read in content order.  Local: the cost follows the moves and
  the contexts they name, never the context-NAT population.  Returns true when an edge
  gained a justification, which the caller settles."
  [kb {:keys [edges arrived derived] :as moves}]
  (when (and (or (seq edges) (seq arrived) (seq derived)) (any-context-subrelations? kb))
    (reconcile-moves* kb moves)))

(defn reconcile-genlCx
  "The structural-genlCx maintenance a just-asserted `sentence` and the belief moves of its
  write (`moves`, `reconcile-moves`) call for: the arrival of `sentence`
  (`reconcile-arrival`), a `genlCx` edge read with the moved edges once.  A no-op, one
  functor count, on a KB that declares no `contextArgSubrelation`.  Returns true when an
  edge gained a justification, which the caller settles."
  [kb sentence moves]
  (when (any-context-subrelations? kb)
    (let [edge? (and (sequential? sentence) (= 'genlCx (first sentence)) (= 3 (count sentence)))]
      (any-built?
       [(when-not edge? (reconcile-arrival kb sentence))
        (reconcile-moves* kb (cond-> moves edge? (update :edges (fnil conj #{}) (vec (rest sentence)))))]))))

(defn reconcile-revivals
  "The structural genlCx maintenance a teardown owes once its belief has settled: the
  belief moves of the teardown (`moves`, `reconcile-moves`), and the target of every
  `except` or `defeat` among the `removed` sentences, whose belief or visibility the removal
  gave back with no relabel.  Behind `nat/any-reified-constants?`.  Returns true when an edge
  gained a justification, which the caller settles."
  [kb moves removed]
  (when (nat/any-reified-constants? kb)
    (reconcile-moves kb (update moves :arrived (fnil into #{})
                                (keep #(or (kb/except-target %) (kb/defeat-target %)) removed)))))
