;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.witness-reading
  "How many stored firings rest on a reachability witness that placed them lower than
  another route would have, and how many a reader loses while still reaching — the one
  implementation `lein bench-witness` prints and `witness_shortfall_test` holds at zero.

  A forward firing that climbed the taxonomy names **one** path per reachability in its
  justification: the `genl` edges a subsumed match travelled, the `genlCx` edges the
  placement is seen over, and the facts a `transitiveInArg` claim moved along
  (docs/contexts.md, \"The consumers, and what each of them may reach\").  A second route
  carries no second justification, so where the named path is the constraint that decided
  the placement, the firing lands below the contexts another route would have reached, and
  a reader that reads the named path as withdrawn reads the firing as withdrawn with it.

  The counts per corpus, taken after the settle, and each broken out by the kind of
  witness — `preserve` for a step a `transitiveInArg` claim moved along, `subsume` for a
  `genl` path a match climbed, `sight` for a `genlCx` path the placement is seen over:

    named     witness paths of that kind the justifications name
    binding   those whose witness placed the conclusion strictly below the contexts the
              rule and the other antecedents allow — the witness, not the facts, is what
              the placement rests on
    above     those of `binding` for which a strictly more general context reaches the
              same two terms over the same relation on its own believed edges: the
              firings a witness chosen to place highest would move up
    lost      firings some reader reads as withdrawn where that reader still reaches the
              witness's two terms — the same shortfall, actual rather than potential
    silent    those of `lost` whose sentence the reader then believes through no other
              sentex: the readings a caller sees change

  The two corpora here are the shape the counts are about: two routes between the same
  ends, a long one stated in the general context and a short one in a specific context,
  optionally with a long-route edge per chain scoped-defeated in the specific one.
  Each takes `term`, a `(fn [role base] symbol)`, so the bench can spell the literal names
  and a test can mint net-neutral temporaries."
  (:require [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- reading the network -------------------------------------------------

(defn- record-of [kb h] (p/get-sentex (:records kb) h))

(defn- binary-fact
  "`[functor a b]` for a positive two-argument sentence, or nil for anything else — a
  negation, a rule, or an arity the reach walk never travels."
  [sentence]
  (when (seq? sentence)
    (let [as (nm/args sentence)]
      (when (= 2 (count as))
        [(nm/functor sentence) (first as) (second as)]))))

(defn- preserved-relations
  "The `R` of each `(transitiveInArg P n R)` a justification names.  A preservation support
  names the declaration beside the path it travelled (`inherit/move-supports`), so the
  declaration is what separates a claim that moved along `R` from a match that climbed the
  `genl` closure — both of which name `(genl …)` sentexes."
  [sentences]
  (into #{}
        (keep (fn [s]
                (when (and (seq? s) (= 'transitiveInArg (nm/functor s)))
                  (last (nm/args s)))))
        sentences))

(defn- witnesses
  "The antecedents of `j` that witness a reachability, as `{handle [kind rel a b]}`.  The
  kind is `preserve` for a step a `transitiveInArg` claim moved along, `subsume` for a
  `genl` path a match climbed, and `sight` for a `genlCx` path the placement is seen over."
  [kb j]
  (let [sxs  (into {} (keep (fn [h] (when-let [r (record-of kb h)] [h (:sentence r)])))
                   (jtms/rests-on j))
        pres (preserved-relations (vals sxs))]
    (into {}
          (keep (fn [[h s]]
                  (when-let [[f a b] (binary-fact s)]
                    (cond
                      (contains? pres f)   [h [(symbol (str f "/preserve")) f a b]]
                      (= 'genl f)          [h ['genl/subsume f a b]]
                      (= 'genlCx f)        [h ['genlCx/sight f a b]]))))
          sxs)))

;; ---- what one context reaches on its own edges ---------------------------

(defn- adjacency
  "`{a {b #{handle}}}` over the believed `rel` facts stored in the KB, with each edge's
  supporters kept: an edge one context states twice is one entry, and a reader drops the
  edge only where it reads every supporter as withdrawn."
  [kb rel]
  (reduce (fn [m h]
            (if-let [[f a b] (some-> (record-of kb h) :sentence binary-fact)]
              (if (= f rel) (update-in m [a b] (fnil conj #{}) h) m)
              m))
          {}
          (reads/believed-with-functor kb rel)))

(defn- witness-paths
  "The witness edges of `j` joined into paths, one per reachability the firing rests on,
  as `{:kind :rel :a :b :edges}`: a `genl` path a match climbed runs from the matched
  term up to the rule's, and `:a`/`:b` are its two ends.  A path is what the firing
  depends on, so a route that bypasses one of its edges still answers for it."
  [kb j]
  (into []
        (mapcat (fn [[kind pairs]]
                  ;; each of `ws` is `[handle rel a b]`
                  (let [ws   (map second pairs)
                        rel  (nth (first ws) 1)
                        out  (group-by #(nth % 2) ws)
                        tgts (into #{} (map #(nth % 3)) ws)]
                    (for [a (distinct (remove tgts (map #(nth % 2) ws)))]
                      (loop [n a, edges #{}]
                        (if-let [[h _ _ b] (first (remove #(contains? edges (first %)) (out n)))]
                          (recur b (conj edges h))
                          {:kind kind :rel rel :a a :b n :edges edges}))))))
        (group-by first
                  (map (fn [[h [kind rel a b]]] [kind [h rel a b]]) (witnesses kb j)))))

(defn- reaches?
  "Does `reader` reach `b` from `a` over `adj`, using only the edges it sees and believes,
  and none of the handles in `skip`?  Breadth-first over the same adjacency `inherit/fact-reach`
  walks, so a true answer names a route the reader can state its own reasons for."
  [kb adj reader a b skip]
  (let [tx      (reasoning/taxonomy kb)
        usable? (fn [hs]
                  (boolean (some (fn [h]
                                   (and (not (contains? skip h))
                                        (when-let [r (record-of kb h)]
                                          (and (tax/sees? tx reader (:context r))
                                               (res/believed-at? kb h reader)))))
                                 hs)))]
    (loop [q (conj clojure.lang.PersistentQueue/EMPTY a), seen #{a}]
      (if-let [n (peek q)]
        (let [nxt (into [] (comp (filter (fn [[_ hs]] (usable? hs)))
                                 (map first)
                                 (remove seen))
                        (get adj n))]
          (if (some #(= b %) nxt)
            true
            (recur (into (pop q) nxt) (into seen nxt))))
        false))))

;; ---- the three counts ----------------------------------------------------

(defn- placement-cap
  "The contexts the rule and the non-witness antecedents of `j` allow the conclusion to
  live in — the maximal contexts that see all of them, which is the placement rule with
  the taxonomy witnesses left out (`chain/placement-ingredients`)."
  [kb j witness-handles]
  (let [tx    (reasoning/taxonomy kb)
        ctxs  (into [] (keep (fn [h]
                               (when-not (contains? witness-handles h)
                                 (:context (record-of kb h)))))
                    (jtms/rests-on j))]
    (when (seq ctxs)
      (tax/maximal-common-descendant-contexts tx ctxs))))

(defn- above?
  "Is `k` strictly more general than `c` — `c` sees `k` and the two differ?"
  [tx c k]
  (and (not= c k) (tax/sees? tx c k)))

(defn- tally-justification
  "One justification's contribution to the report: a `{kind {:named n :binding n :above n}}`
  map counting witness paths, empty for the firing that names no witness."
  [kb adj-of j]
  (let [tx  (reasoning/taxonomy kb)
        ps  (witness-paths kb j)]
    (if (empty? ps)
      {}
      (let [c    (:context (record-of kb (:consequence j)))
            cap  (placement-cap kb j (into #{} (mapcat :edges) ps))
            ups  (into [] (filter #(above? tx c %)) cap)]
        (reduce (fn [m {:keys [kind rel a b edges]}]
                  (let [binding? (seq ups)
                        higher?  (and binding?
                                      (boolean (some #(reaches? kb (adj-of rel) % a b edges) ups)))]
                    (-> m
                        (update-in [kind :named] (fnil inc 0))
                        (cond-> binding? (update-in [kind :binding] (fnil inc 0)))
                        (cond-> higher? (update-in [kind :above] (fnil inc 0))))))
                {}
                ps)))))

(defn- lost-at-readers
  "`{kind {:lost n :silent n}}` — firings a reader reads as withdrawn where that reader
  still reaches the two ends of each witness path it lost an edge of, and the subset whose
  sentence the reader believes nowhere else.  Asked per path and not per edge, since the
  route that survives commonly bypasses the lost edge's own two terms.  Every context is asked, since a reader below a vantage is
  where a scoped defeat lands."
  [kb adj-of]
  (let [tms (reasoning/tms kb)
        tx  (reasoning/taxonomy kb)]
    (reduce
     (fn [acc reader]
       (reduce
        (fn [acc h]
          (let [js (keep #(jtms/justification tms %) (jtms/supports tms h))]
            (reduce
             (fn [acc j]
               (let [ps   (witness-paths kb j)
                     wit  (into #{} (mapcat :edges) ps)
                     gone (into #{} (remove #(res/believed-at? kb % reader)) (jtms/rests-on j))
                     hit  (filter #(some gone (:edges %)) ps)]
                 (if (and (seq gone) (every? wit gone)
                          (every? (fn [{:keys [rel a b]}] (reaches? kb (adj-of rel) reader a b gone)) hit))
                   (reduce (fn [acc {:keys [kind]}]
                             (cond-> (update-in acc [kind :lost] (fnil inc 0))
                               (empty? (res/matches-visible
                                        kb (:sentence (record-of kb h)) reader))
                               (update-in [kind :silent] (fnil inc 0))))
                           acc hit)
                   acc)))
             acc js)))
        acc
        (or (res/defeat-withdrawn-set kb reader) #{})))
     {}
     (tax/contexts tx))))

(defn report
  "The counts over a settled `kb`, as `{kind {:named :binding :above :lost :silent}}`."
  [kb]
  (let [tms   (reasoning/tms kb)
        cache (atom {})
        adj-of (fn [rel]
                 (or (get @cache rel)
                     (let [a (adjacency kb rel)] (swap! cache assoc rel a) a)))
        base  (reduce (fn [m j] (merge-with #(merge-with + %1 %2) m (tally-justification kb adj-of j)))
                      {}
                      (jtms/justifications tms))]
    (merge-with #(merge-with + %1 %2) base (lost-at-readers kb adj-of))))

;; ---- a firing stored below the same firing -------------------------------

(defn- reasons-besides-witnesses
  "The antecedents of `j` that are not a reachability witness."
  [kb j]
  (let [ws (witnesses kb j)]
    (into #{} (remove #(contains? ws %)) (jtms/rests-on j))))

(defn shadowed
  "Stored firings whose sentence a strictly more general context also stores, as
  `{:shadowed n :redundant n}`.

    shadowed   derived sentexes with a same-sentence derived sentex in a context they
               see, other than their own
    redundant  those of `shadowed` every justification of which rests, its witnesses
               aside, only on reasons some justification of the higher one names — the
               same claim and rule fired over a different route, and so the lower firing
               a retirement would take

  A conclusion two rules derive is stored twice as a matter of course; `redundant` is the
  pair that differs only in the route its witness names."
  [kb]
  (let [tms  (reasoning/tms kb)
        tx   (reasoning/taxonomy kb)
        js-of (group-by :consequence (jtms/justifications tms))
        by-sentence (group-by #(:sentence (record-of kb %))
                              (filter #(record-of kb %) (keys js-of)))]
    (reduce
     (fn [acc [_ hs]]
       (reduce
        (fn [acc lo]
          (let [lc     (:context (record-of kb lo))
                highs  (filter #(let [hc (:context (record-of kb %))]
                                  (above? tx lc hc))
                               hs)]
            (if (empty? highs)
              acc
              (let [hi-reasons (into #{} (comp (mapcat js-of) (mapcat jtms/rests-on)) highs)
                    red?       (every? #(every? hi-reasons (reasons-besides-witnesses kb %))
                                       (js-of lo))]
                (cond-> (update acc :shadowed inc)
                  red? (update :redundant inc))))))
        acc hs))
     {:shadowed 0 :redundant 0}
     by-sentence)))

;; ---- the corpora ---------------------------------------------------------

(defn- two-routes
  "Assert `n` two-route chains from three parts per chain: `base` (what both routes hang
  from), `long-route` (the general context's route) and `short-route` (the short route, the
  declaration, the claim and the rule).  In the default order the long route precedes the
  rest and all of it settles together; with `:short-first?` the base and the short route settle
  first, so every firing is placed over the short route before the long one arrives."
  [kb n base long-route short-route {:keys [short-first?]}]
  (if short-first?
    (do (v/with-deferred-settle kb (doseq [i (range n)] (base i) (short-route i)))
        (v/with-deferred-settle kb (doseq [i (range n)] (long-route i))))
    (v/with-deferred-settle kb
      (doseq [i (range n)] (base i) (long-route i) (short-route i))))
  kb)

(defn- defeat-long-routes
  "With `:defeated?`, a scoped defeat of one long-route edge per chain — `(edge i)` — stated
  in the short route's context: that context still reaches every chain's ends over its own
  edge, so a firing it reads as withdrawn is `lost`."
  [kb n short edge {:keys [defeated?]}]
  (when defeated?
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'not (edge i)) short {:strength :monotonic}))))
  kb)

(defn generated
  "A `transitiveInArg`-heavy corpus with two routes between each pair of ends: a long one
  stated in the general context and a short one stated in a specific context, which is the
  shape a witness search can answer two ways.  `n` chains, each `depth` long.
  `tax/general-reach-supports` picks the witness here."
  ([kb term n depth] (generated kb term n depth {}))
  ([kb term n depth opts]
   (let [short (term :context "CxShort")
         noted (term :predicate "wNoted")
         ts    (vec (for [i (range n)] (mapv #(term :type (str "wt" i "_" %)) (range depth))))
         prs   (mapv #(term :predicate (str "wRel" %)) (range n))]
     (v/assert kb (list 'genlCx short 'CxUniverse) 'CxUniverse)
     (two-routes
      kb n
      (fn [i]
        (let [t (ts i)]
          (doseq [k (range depth)] (v/assert kb (list 'genl (t k) 'thing) 'CxUniverse))))
      ;; the long route, general: t(depth-1) → t(depth-2) → … → t(0)
      (fn [i]
        (let [t (ts i)]
          (doseq [k (range 1 depth)]
            (v/assert kb (list 'genl (t k) (t (dec k))) 'CxUniverse))))
      (fn [i]
        (let [t (ts i), pr (prs i)]
          ;; the short route, specific: t(depth-1) → t(0) in one edge
          (v/assert kb (list 'genl (t (dec depth)) (t 0)) short)
          (v/assert kb (list 'transitiveInArg pr 1 'genl) 'CxUniverse)
          (v/assert kb (list pr (t 0) 'thing) 'CxUniverse)
          (v/assert kb (list 'set/forwardRule
                             (list 'implies (list pr '?x '?y) (list noted '?x '?y)))
                    'CxUniverse)))
      opts)
     (defeat-long-routes kb n short (fn [i] (list 'genl ((ts i) 2) ((ts i) 1))) opts))))

(defn generated-fact
  "The same two routes over a **fact** relation instead of `genl`: a declared-transitive
  part chain stated in the general context, one short edge stated in the specific one,
  and a predicate preserved along it.  `inherit/fact-paths` picks the witness here, where
  `tax/general-reach-supports` picks it for `genl`."
  ([kb term n depth] (generated-fact kb term n depth {}))
  ([kb term n depth opts]
   (let [short (term :context "CxShort")
         noted (term :predicate "wFNoted")
         ts    (vec (for [i (range n)] (mapv #(term :individual (str "Wp" i "x" %)) (range depth))))
         pts   (mapv #(term :predicate (str "wPart" %)) (range n))
         prs   (mapv #(term :predicate (str "wFRel" %)) (range n))]
     (v/assert kb (list 'genlCx short 'CxUniverse) 'CxUniverse)
     (two-routes
      kb n
      (fn [i] (v/assert kb (list 'transitive (pts i)) 'CxUniverse))
      (fn [i]
        (let [t (ts i), pt (pts i)]
          (doseq [k (range 1 depth)]
            (v/assert kb (list pt (t k) (t (dec k))) 'CxUniverse))))
      (fn [i]
        (let [t (ts i), pt (pts i), pr (prs i)]
          (v/assert kb (list pt (t (dec depth)) (t 0)) short)
          (v/assert kb (list 'transitiveInArg pr 1 pt) 'CxUniverse)
          (v/assert kb (list pr (t 0) 'thing) 'CxUniverse)
          (v/assert kb (list 'set/forwardRule
                             (list 'implies (list pr '?x '?y) (list noted '?x '?y)))
                    'CxUniverse)))
      opts)
     (defeat-long-routes kb n short (fn [i] (list (pts i) ((ts i) 2) ((ts i) 1))) opts))))
