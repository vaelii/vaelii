;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.context-nat
  "The structural genlCx producer for reified-NAT contexts — docs/context-nat.md.

  `(contextArgSubrelation F pos R)` orders two `F`-contexts by the product of the declared
  sub-relations at the positions where they differ, and `(contextArgGenlCx F pos)` places
  every `F`-context under its argument at `pos`.  This namespace **materializes** each such
  `genlCx` edge as a **justified** sentex in CxUniverse, never a premise.  `R` is resolved
  by a bounded oracle: a registered pure comparator, else the `genlCx` closure for a
  sub-relation in `closure-orders` and each believed stored `(R a b)` fact."
  (:require [vaelii.impl.datetime :as datetime]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.point-order :as po]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.timepoint :as tp]
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

(defn- calendar-time?
  "Does the term `x` name a time by its spelling alone: an `InstantFn` moment, a calendar
  term or a range?"
  [x]
  (boolean (or (datetime/instant-term? x) (datetime/extent x) (datetime/utc-extent x))))

(def ^:private bounds-orders
  "The sub-relations the order over time points decides, `{R (fn [lower upper])}` over two
  `point-order/readings`, answering the comparisons `[strict? x y]` (`point-order/path`)
  that place the lower half-open time inside the upper, or nil when the readings' shape
  refuses it: `subintervalOf` between two intervals, and `subtimeOf` from a moment, `[t t]`."
  {'subintervalOf (fn [[as ae] [bs be]]
                    (when (and (not= as ae) (not= bs be))
                      [[false bs as] [false ae be]]))
   'subtimeOf     (fn [[t u] [bs be]]
                    (when (and (= t u) (not= bs be))
                      [[false bs t] [true t be]]))})

(defn- bounds-routes
  "The routes ordering `a` `R`-below `b` through the order over time points, for an `R` in
  `bounds-orders` and two times not both calendar ones, a pair the comparator answers
  alone: one vector of handles per pair of `point-order/readings` whose comparisons each
  have a `point-order/path`, the handles of the paths' facts."
  [kb r a b]
  (when-let [holds? (get bounds-orders r)]
    (when-not (and (calendar-time? a) (calendar-time? b))
      (distinct
       (for [ea (po/readings a)
             eb (po/readings b)
             :let [cs (holds? ea eb)]
             :when (and cs (every? (fn [[strict? x y]] (po/holds? kb strict? x y)) cs))
             :let [ps (mapv (fn [[strict? x y]] (po/path kb strict? x y)) cs)]
             :when (every? some? ps)]
         (into [] (comp cat (map :id) (distinct)) ps))))))

(defn- r-evidence
  "The beliefs the relationship `a` `R`-below `b` rests on, one vector of handles per route
  that holds, empty when none does: `[[]]` when a comparator answers it (a pure function of
  the two expressions, already carried by the `natFormula` antecedents); else, for an `R`
  in `closure-orders`, one supporter per edge along a path from `a` up to `b` that `a` sees
  (`tax/reach-support`, a content-ordered walk), for an `R` in `bounds-orders`, the facts
  behind each pair of readings the order over time points places (`bounds-routes`), and
  the handle of each believed `(R a b)` fact, in context order.  Every route holding is a
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

(defn any-context-declarations?
  "Presence check: does the KB declare any `contextArgSubrelation` or `contextArgGenlCx`?
  The producer is a no-op otherwise — two O(1) functor counts per assert, the shape
  `res/any-corresponding-predicates?` has."
  [kb]
  (let [ix (:index kb)]
    (or (pos? (reads/stored-count-with-functor ix 'contextArgSubrelation))
        (pos? (reads/stored-count-with-functor ix 'contextArgGenlCx)))))

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
  CxUniverse with `K` a `cx/` constant and `E` an application of `f`, else nil.  With
  `named?` true, `K` is any symbol: a context a hand-written map names, which takes its
  `contextArgGenlCx` edges (`reconcile-arg-edges`) and no `contextArgSubrelation` pair."
  ([kb f sx] (context-nat-entry kb f sx false))
  ([kb f sx named?]
   (let [[_ k e] (:sentence sx)]
     (when (and (= universal-context (:context sx))
                (= 'natFormula (nm/functor (:sentence sx)))
                (jtms/in? (reasoning/tms kb) (:id sx))
                (if named? (and (symbol? k) (not (sx/variable? k))) (nat-read/reified-context-symbol? k))
                (sequential? e) (= f (first e)))
       [k e (:id sx)]))))

(defn- context-nats-of
  "Every believed context NAT whose expression head is `f`, as `context-nat-entry`'s
  triples (`named?` passed on).  The read goes through the inverted term index on `f`,
  which descends into a ground compound, so an expression's head is one of the sentex's
  posted terms.  A declaration's arrival reads this; a mint and an edge read
  `context-nats-at`."
  ([kb f] (context-nats-of kb f false))
  ([kb f named?]
   (->> (kb/find-sentexes kb f) (keep #(context-nat-entry kb f % named?)) distinct)))

(defn- context-nats-naming
  "The believed context NATs of `f` whose expression names one of `terms`: one
  intersection of the term index on `f` and on each term (`kb/find-sentexes-all`)."
  [kb f terms]
  (->> terms
       (mapcat #(kb/find-sentexes-all kb [f %]))
       (keep #(context-nat-entry kb f %))
       distinct))

(defn- context-nats-at
  "The believed context NATs of `f` whose expression holds one of `terms` at one of the
  positions `ps`: one `:nat-argument` node read per position and term, in CxUniverse, the
  one context `context-nat-entry` keeps (`reads/as-stored-nat-formulas-at`)."
  [kb f ps terms]
  (->> (for [pos ps
             t terms
             h (reads/as-stored-nat-formulas-at (:index kb) f pos t #{universal-context})]
         h)
       distinct
       (keep #(some->> (p/get-sentex (:records kb) %) (context-nat-entry kb f)))))

(defn- context-nat-of
  "The entry of the context NAT `k`'s own believed map (`named?` passed on), or nil: one
  argument-root read."
  ([kb k] (context-nat-of kb k false))
  ([kb k named?]
   (some (fn [sx] (let [e (nth (:sentence sx) 2 nil)]
                    (when (sequential? e) (context-nat-entry kb (first e) sx named?))))
         (kb/sentexes-matching kb (list 'natFormula k '?e) universal-context))))

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

(defn- arg-genlcx-declarations
  "`f`'s believed `(contextArgGenlCx F pos)` declarations as `[pos handle]`, in position
  order, each read as its own context believes it, as `subrelation-declarations` reads
  its own."
  [kb f]
  (sort (for [sx (kb/sentexes-matching kb (list 'contextArgGenlCx f '?pos) '?ctx)
              :when (exc/believed-own? kb (:id sx))]
          [(nth (:sentence sx) 2) (:id sx)])))

(defn- arg-context
  "The context at argument `pos` of the expression `e` of the context NAT `k`, when it is
  a symbol other than `k` and other than the universal context, which every context sees;
  else nil."
  [k e pos]
  (let [c (when (and (integer? pos) (pos? (long pos))) (nth e pos nil))]
    (when (and (symbol? c) (not= c k) (not= c universal-context)) c)))

(defn arg-supers
  "The contexts the structural producer places `k` under for `(natFormula k e)` in
  CxUniverse: the `arg-context` at each of the `arg-genlcx-declarations` of `e`'s
  function, in position order."
  [kb k e]
  (when (and (sequential? e) (symbol? (first e)))
    (into [] (keep (fn [[pos _]] (arg-context k e pos))) (arg-genlcx-declarations kb (first e)))))

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

(defn- reconcile-arg-edges
  "Materialize `(genlCx k c)` for each context NAT of `f` among `entries`
  (`context-nat-entry`'s triples) and each of `f`'s `arg-genlcx-declarations`, `c` the
  `arg-context` at the declared position, justified by `k`'s `natFormula` map and the
  declaration.  Returns true when an edge gained a justification."
  [kb f entries]
  (when-let [decls (seq (arg-genlcx-declarations kb f))]
    (any-built?
     (for [[k e th] entries
           [pos declH] decls
           :let [c (arg-context k e pos)]
           :when c]
       (materialize-edge kb k c [th declH])))))

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
  context holding one of its terms there (`context-nats-at`); with no such position, every
  context of `f`."
  [kb f e decls]
  (agreeing e decls
            (if-let [[p ts] (comparable-read kb e decls)]
              (context-nats-at kb f [p] ts)
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
  unless it holds a range: those, each thing whose start or end a believed fact links
  (`point-order/sentence-links`) and the other end of each believed stored `(R t x)`.  Nil
  also when the maps holding those terms at `q`, the postings beside `f` at the range
  function and the link facts number `n` or more."
  [kb f e decls n]
  (let [ix (:index kb)]
    (when-let [[q cs] (some #(some->> (datetime/containing-terms (nth e %)) (vector %))
                            (declared-in e decls #(every? comparator? %)))]
      (when (< (+ (transduce (map #(reads/stored-count-nat-formulas-at ix f q % #{universal-context})) + 0 cs)
                  (count (reads/as-stored-with-terms ix [f datetime/range-function]))
                  (transduce (map #(reads/stored-count-with-functor ix %)) + 0 po/link-heads))
               n)
        [q (-> cs
               (into (for [h po/link-heads
                           :when (pos? (reads/stored-count-with-functor ix h))
                           sx (kb/sentexes-matching kb (list h '?x '?y) '?ctx)
                           [lo hi] (po/sentence-links (:sentence sx))
                           x (keep tp/thing-of [lo hi])]
                       x))
               (into (for [[r] (decls q), sx (kb/sentexes-matching kb (list r (nth e q) '?x) '?ctx)]
                       (nth (:sentence sx) 2))))]))))

(defn- above-candidates
  "The `candidates` a read of `e`'s unwritten context needs, those its context could be
  ordered below.  When `containing-read` reads fewer postings than `candidates`, they are
  the contexts holding at its position one of its terms (`context-nats-at`) or a range
  (`context-nats-keyed`); else `candidates`."
  [kb f e decls]
  (let [ix (:index kb)
        n  (if-let [[pos ts] (comparable-read kb e decls)]
             (transduce (map #(reads/stored-count-nat-formulas-at ix f pos % #{universal-context})) + 0 ts)
             (count (reads/as-stored-with-term ix f)))]
    (if-let [[q ts] (containing-read kb f e decls n)]
      (agreeing e decls (distinct (concat (context-nats-at kb f [q] ts)
                                          (filter #(range-term? (nth (second %) q nil))
                                                  (context-nats-keyed kb f [datetime/range-function])))))
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
  "The contexts the producer would order the context of `expr` below, were it minted, as
  `[k supporter]` in `k` order: each `above-candidates` context with a route, supported by
  its `natFormula` map, and each `contextArgGenlCx` `arg-context`, by the declaration.  For
  a read of a context nobody has written into (docs/context-nat.md).  Writes nothing."
  [kb expr]
  (when (and (sequential? expr) (any-context-declarations? kb))
    (po/with-memo
      (let [f     (first expr)
            decls (declarations-by-position kb f)]
        (->> (concat (when (seq decls)
                       (->> (above-candidates kb f expr decls)
                            (filter (fn [[_ e _]] (seq (pair-routes kb decls expr e))))
                            (map (fn [[k _ th]] [k th]))))
                     (for [[pos declH] (arg-genlcx-declarations kb f)
                           :let [c (arg-context nil expr pos)]
                           :when c]
                       [c declH]))
             (sort-by (juxt (comp nm/name-key first) second))
             seq)))))

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
  a pair under.  Each side is read at those positions (`context-nats-at`), the sub side
  first, and an empty sub side reads no super side."
  [kb f r x y]
  (fn [decls]
    (let [ps     (for [[pos ds] decls :when (some #(= r (first %)) ds)] pos)
          tx     (reasoning/taxonomy kb)
          closed (and (contains? closure-orders r) (symbol? x) (symbol? y))
          side   #(context-nats-at kb f ps %)
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

(defn- side
  "One side of the links arriving, from the walks `reached` (`point-order/reach`) from its
  ends: `[times calendar?]`, the thing of each point and each symbol (a moment it can name)
  reached, and whether a calendar moment is among them."
  [reached]
  (reduce (fn [[ts cal?] [[n]]]
            [(cond-> ts
               (tp/thing-of n) (conj (tp/thing-of n))
               (symbol? n)     (conj n))
             (or cal? (some? (po/calendar-moment n)))])
          [#{} false] reached))

(defn- contexts-at
  "The contexts of `f` holding, at one of the positions `ps`, one of the times `ts` or an
  application with one of them as an argument, such as a meet whose points link to its
  arguments' (`point-order/path`).  Read by term (`context-nats-naming`, and
  `context-nats-keyed` for a compound), and from every context of `f` when the term index
  keys no compound at an expression's argument (`sx/*min-indexed-depth*` above 2)."
  [kb f ps ts]
  (when (seq ts)
    (let [{syms true cmps false} (group-by symbol? ts)]
      (filter (fn [[_ e]] (some #(let [x (nth e % nil)]
                                   (or (contains? ts x) (and (seq? x) (some ts (rest x)))))
                                ps))
              (if (or (empty? cmps) (<= (long sx/*min-indexed-depth*) 2))
                (distinct (concat (when (seq syms) (context-nats-naming kb f syms))
                                  (context-nats-keyed kb f cmps)))
                (context-nats-of kb f))))))

(defn- calendar-extreme
  "Per frame, the latest calendar moment (`point-order/calendar-moment`) among the nodes
  the walk `reached` holds when `latest?`, else the earliest, as `{frame fields}`."
  [latest? reached]
  (reduce (fn [m [[n]]]
            (if-let [[fr fs] (po/calendar-moment n)]
              (update m fr #(if (or (nil? %) ((if latest? pos? neg?) (compare fs %))) fs %))
              m))
          {} reached))

(def ^:private calendar-functors
  "The functors of the facts `bridged-contexts` reads: a context NAT's map, and each fact
  giving point-order links."
  (conj po/link-heads 'natFormula))

(defn- calendar-months
  "Each `[f month]` the calendar index holds for a functor `f` of `calendar-functors`: one
  name-set read per functor."
  [kb]
  (for [f calendar-functors, b (reads/as-stored-calendar-buckets (:index kb) f)] [f b]))

(defn- calendar-handles
  "The handles the calendar index files under each `[f month]` of `months`
  (`calendar-months`) whose month, in frame `frame`, lies from `from`'s to `to`'s, each six
  fields or nil for no bound, in every context: a superset of the pairs `reconcile-pairs`
  decides per context."
  [kb months frame from to]
  (let [ix  (:index kb)
        ym  #(subvec (vec %) 0 2)
        in? (fn [[_ [fr y m]]] (and (= frame fr)
                                    (or (nil? from) (<= (compare (ym from) [y m]) 0))
                                    (or (nil? to) (<= (compare [y m] (ym to)) 0))))]
    (into #{} (comp (filter in?) (mapcat (fn [[f b]] (reads/as-stored-calendar-at-global ix f b))))
          months)))

(defn- bridged-contexts
  "The contexts of `f` holding, at one of the positions `ps`, a time one of the stored
  facts `hs` joins to the calendar: the time of a context NAT's own map, and each time a
  walk away from the calendar end of a stated link reaches (`side`)."
  [kb f ps hs]
  (let [sxs (keep #(p/get-sentex (:records kb) %) hs)
        far (for [sx sxs
                  [lo hi] (po/sentence-links (:sentence sx))
                  :let [cal-lo (some? (po/calendar-moment lo))]
                  :when (not= cal-lo (some? (po/calendar-moment hi)))]
              (if cal-lo (po/reach kb true hi) (po/reach kb false lo)))]
    (into (set (keep #(context-nat-entry kb f %) sxs))
          (contexts-at kb f ps (first (side (apply merge far)))))))

(defn- calendar-candidates
  "The contexts of `f` a comparison of calendar fields can order against one of `cs`
  (`context-nat-entry`'s triples), each read at the positions `ps`.  For each reading
  `[s e]` of each time there, the walks from `s` and `e` give the calendar bounds: a
  context inside has its points between the earliest moment `s` reaches forward and the
  latest `e` reaches back, read off the calendar index's months between them; a context
  around has its start at or before the latest moment `s` reaches back and its end at or
  after the earliest `e` reaches forward, read off the months on the side holding fewer.
  The contexts at a time the walks reach are among them."
  [kb f ps cs]
  (let [months (delay (calendar-months kb))
        fewer  (fn [fr before after]
                 (let [n (fn [pick] (count (filter (fn [[_ [fr' y m]]] (and (= fr fr') (pick [y m]))) @months)))]
                   (if (<= (n #(<= (compare % (subvec (vec before) 0 2)) 0))
                           (n #(<= (compare (subvec (vec after) 0 2) %) 0)))
                     (calendar-handles kb @months fr nil before)
                     (calendar-handles kb @months fr after nil))))]
    (set
     (for [[_ e] cs, pos ps
           :let [t (nth e pos nil)] :when (some? t)
           [s en] (po/readings t)
           :let [fs (po/reach kb true s)  bs (po/reach kb false s)
                 fe (po/reach kb true en) be (po/reach kb false en)
                 in-lo (calendar-extreme false fs) in-hi (calendar-extreme true be)
                 out-lo (calendar-extreme true bs) out-hi (calendar-extreme false fe)
                 hs (concat (for [[fr a] in-lo :let [b (in-hi fr)] :when b
                                  h (calendar-handles kb @months fr a b)]
                              h)
                            (for [[fr a] out-lo :let [b (out-hi fr)] :when b
                                  h (fewer fr a b)]
                              h))]
           c (concat (contexts-at kb f ps (first (side (merge fs bs fe be))))
                     (bridged-contexts kb f ps (set hs)))]
       c))))

(defn- reconcile-link
  "The pairs the links `ls` (`point-order/sentence-links`) arriving can order, in the
  functions a `bounds-orders` relation orders: each context holding a time a lower end
  reaches back to against each holding one an upper end reaches forward to, both ways.
  A side whose walk meets a calendar moment also takes the other side's
  `calendar-candidates`, paired only with the other side's own, since a time joined to the
  link through the calendar is not one the walk reaches.  A pair's comparison through an
  end of a link reads the walks from that end (`point-order/*through*`).  Returns true
  when an edge gained a justification."
  [kb ls]
  (let [walks (delay (mapv (fn [n] [(po/reach kb false n) (po/reach kb true n)])
                           (distinct (mapcat #(take 2 %) ls))))
        lo    (delay (side (apply merge (map #(po/reach kb false (first %)) ls))))
        hi    (delay (side (apply merge (map #(po/reach kb true (second %)) ls))))
        pairs (fn [f decls]
                (let [ps     (for [[pos ds] decls :when (some #(contains? bounds-orders (first %)) ds)] pos)
                      ks     (keys decls)
                      [lt lc] @lo
                      los    (set (contexts-at kb f ps lt))]
                  (when (or (seq los) lc)
                    (let [[ht hc] @hi
                          his   (set (contexts-at kb f ps ht))
                          group #(group-by (fn [c] (product-key (second c) ks)) %)
                          hs    (group (cond-> his hc (into (calendar-candidates kb f ps los))))]
                      (distinct
                       (for [l (cond-> los lc (into (calendar-candidates kb f ps his)))
                             h (get hs (product-key (second l) ks))
                             :when (and (not= (first l) (first h))
                                        (or (contains? los l) (contains? his h)))
                             pr [[l h] [h l]]]
                         pr))))))]
    (binding [po/*through* walks]
      (any-built?
       (for [f (distinct (mapcat #(functions-ordered-by kb %) (keys bounds-orders)))]
         (reconcile-pairs kb f (partial pairs f)))))))

(defn- reconcile-arrival
  "The pairs a believed `sentence` arriving can order: for a `(contextArgSubrelation F …)`
  declaration, every pair of `F`'s contexts; for a `contextArgGenlCx` one, the argument edges
  (`reconcile-arg-edges`) of every context a map names; for a `(natFormula K E)` map, `K`'s
  argument edges, and `K`'s pairs (`pairs-with`) when `K` is a `cx/` constant; for a fact
  giving point-order links, `reconcile-link`; for an `(R a b)` fact on a declared
  sub-relation, the pairs across `a` and `b` (`pairs-across`) in the functions declared to
  order by `R`; for a `(genlCx a b)` edge, the same per sub-relation in `closure-orders`.
  Other sentences reconcile nothing.  Returns true when an edge gained a justification."
  [kb sentence]
  (when (and (sequential? sentence) (seq sentence))
    (let [[head x y] sentence]
      (cond
        (= 'contextArgSubrelation head)
        (reconcile-pairs kb x (all-pairs kb x))

        (= 'contextArgGenlCx head)
        (reconcile-arg-edges kb x (context-nats-of kb x true))

        (and (= 'natFormula head) (symbol? x) (sequential? y) (seq y))
        (let [f (first y)]
          (any-built? [(when (nat-read/reified-context-symbol? x) (reconcile-pairs kb f (pairs-with kb f x)))
                       (reconcile-arg-edges kb f (some-> (context-nat-of kb x true) vector))]))

        :else
        (any-built?
         (concat
          (when-let [ls (seq (po/sentence-links sentence))] [(reconcile-link kb ls)])
          (for [r (if (= 'genlCx head) closure-orders [head])
                f (functions-ordered-by kb r)]
            (reconcile-pairs kb f (pairs-across kb f r x y)))))))))

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
  `contextArgGenlCx`, `natFormula`, every sub-relation a believed declaration names, and
  `point-order/link-heads` when one of those is in `bounds-orders`."
  [kb]
  (let [rs (into #{} (map #(nth % 2)) (subrelation-declarations kb (constantly true)))]
    (cond-> (into '#{contextArgSubrelation contextArgGenlCx natFormula} rs)
      (some bounds-orders rs) (into po/link-heads))))

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
    (po/with-memo
      (any-built?
       (concat (map #(reconcile-arrival kb %) (nm/sort-by-content-key identity (set ss)))
               (map #(reconcile-edge-move kb %) (sort-by (fn [e] (mapv nm/name-key e)) (set edges))))))))

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
  (when (and (or (seq edges) (seq arrived) (seq derived)) (any-context-declarations? kb))
    (reconcile-moves* kb moves)))

(defn reconcile-genlCx
  "The structural-genlCx maintenance a just-asserted `sentence` and the belief moves of its
  write (`moves`, `reconcile-moves`) call for: the arrival of `sentence`
  (`reconcile-arrival`), a `genlCx` edge read with the moved edges once.  A no-op, two
  functor counts, on a KB that declares no `contextArgSubrelation` and no
  `contextArgGenlCx`.  Returns true when an
  edge gained a justification, which the caller settles."
  [kb sentence moves]
  (when (any-context-declarations? kb)
    (let [edge? (and (sequential? sentence) (= 'genlCx (first sentence)) (= 3 (count sentence)))]
      (po/with-memo
        (any-built?
         [(when-not edge? (reconcile-arrival kb sentence))
          (reconcile-moves* kb (cond-> moves edge? (update :edges (fnil conj #{}) (vec (rest sentence)))))])))))

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
