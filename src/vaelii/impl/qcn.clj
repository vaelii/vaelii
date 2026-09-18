;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.qcn
  "Generic qualitative-constraint-network path consistency — the shared substrate
  every relation algebra reasons through (`vaelii.impl.space` is RCC-8 topology,
  `vaelii.impl.orientation` cardinal direction, `vaelii.impl.interval` Allen's interval
  time).

  Pure data in, pure data out: nothing here knows about a KB, a context, or belief.
  Reading stored facts into a network and reading an answer back out is the algebra's
  job; this namespace only tightens.

  A relation **algebra** is a map:

    {:universe  the full set of base relations — an unknown constraint
     :identity  the singleton constraint on the diagonal (i,i)
     :compose   (fn [s1 s2] → s) — composition of two relation sets
     :converse  (fn [s] → s) — the converse of a relation set}

  A **network** is `{[i j] → #{base relations}}`, both directions stored; an
  unrecorded pair is the universe.  So a network is a *value*, which is what lets a
  caller memoize an expensive pass on its content.

  Sets are the public representation and **bitmasks are the arithmetic**: a network is encoded into
  a flat array of masks for the duration of a pass and decoded back on the way out, so
  every caller keeps reasoning in relation sets while the cubic loop reasons in
  `bit-and`.  See \"bitmask relation sets\" below.

  Path consistency is sound but not in general complete: it tightens every pair to
  what composition permits, and an emptied constraint proves unsatisfiability, but a
  path-consistent network can still be globally unsatisfiable outside an algebra's
  tractable subclass.  So a constraint that survives is *possible*, not *satisfiable*,
  and a non-entailment is \"not provable\", never \"provably false\"."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.types.qcn :as qcn-types])
  (:import [java.util ArrayDeque BitSet LinkedHashSet]
           [vaelii.impl.types.qcn IRelationOps]))

(defn constraint
  "The constraint on `[i j]` in `net` under `algebra`: the identity on the diagonal,
  the recorded set, else the universe (unknown)."
  [net {:keys [universe identity]} i j]
  (if (= i j) identity (get net [i j] universe)))

(defn- unsatisfiable-as-given?
  "Is one recorded constraint unsatisfiable *before* any tightening?  Two ways, and the
  loop can report neither of them.

  It is **empty** — the pair can stand in no relation at all.  Tightening never says so:
  the loop reports a constraint it *narrows* to nothing, and an empty one it cannot
  narrow further compares equal to itself.  A third node routing through the pair would
  expose it, so without this check the verdict on two contradictory facts about a single
  pair — the smallest network a reader can build — would depend on how many *other*
  nodes happen to be present.

  Or it is a **diagonal** constraint that excludes the identity: a claim that a node
  stands to itself in some relation other than the one it must.  Every triple has i ≠ k,
  so no triple ever visits a diagonal, and `constraint` answers the identity there
  whatever is recorded — an unsatisfiable self-assertion would otherwise be silently
  dropped rather than reported.  It survives the empty check exactly when the relation is
  its own converse, which is exactly when a reader intersecting an asserted `(P a a)`
  with its converse leaves something behind."
  [identity [[i j] rels]]
  (or (empty? rels)
      (and (= i j) (empty? (set/intersection rels identity)))))

(defn unsatisfiable-pairs
  "The pairs of `net` that `unsatisfiable-as-given?` refuses — what a reader wrote down
  that no model can satisfy, before any tightening.  Empty when the network is
  unsatisfiable only *derivably*, by composition, which is the case a report has no
  single pair to blame for."
  [net {:keys [identity]}]
  (into #{} (keep (fn [[pair :as entry]]
                    (when (unsatisfiable-as-given? identity entry) pair)))
        net))

;; ---- bitmask relation sets ----------------------------------------------
;; A constraint is a *set* of base relations, and a pass does exactly three things to
;; one: intersect it, compose it with another, take its converse.  An algebra has a
;; handful of base relations — eight for RCC-8, thirteen for Allen, the largest that
;; ships — so a constraint fits in the bits of a long.  Then intersection is `bit-and`,
;; emptiness is `zero?`, the containment an entailment asks about is one `bit-and`
;; compared against its argument, and composition and converse are array reads.  That
;; retires the per-triple set allocation, which is what a cubic loop over sets spends
;; itself on.
;;
;; Everything is derived from the algebra exactly as given, so no calculus knows this
;; layer exists.  The base relations are ordered **by name**, so the encoding depends on
;; the algebra's content rather than on set iteration order and two runs agree.
;;
;; The tables are built by dynamic programming over the *base* relations.  Composition
;; and converse both distribute over union — R∘S is by definition the union of the
;; pairwise compositions of their members, and that is how every algebra here writes it
;; — so for any mask `f(s) = f(s minus its lowest relation) | f(that relation)`, and a
;; whole-mask table costs k² calls into the algebra plus one OR per entry instead of
;; k·2^k calls.  `qcn_mask_test` holds the tables against the algebra's own set
;; functions, which is where that distributivity is checked rather than assumed.

(def ^:private max-base-relations
  "The most base relations a compiled algebra may have: a constraint is the bits of a
  long, so this is what one holds.  Every algebra here is far below it — thirteen is the
  largest — and one above it has a constraint lattice no engine could work in."
  62)

(def ^:private dense-table-limit
  "The largest whole-mask composition table built eagerly, in entries.  Under it a
  composition is one array read per relation on its left; over it the table covers base
  relations only and a composition reads one entry per pair, which is |s2|× the reads and
  allocates nothing either way.  Allen's thirteen relations — the widest algebra here —
  need 106,496 entries, so every shipped calculus takes the dense side."
  (bit-shift-left 1 18))

(def ^:private decode-cache-limit 8192)

(defn- compile-algebra
  "Compile a relation algebra into its bitmask form:

    {:universe :identity  the two constants, as masks
     :ops                 an `IRelationOps` — compose and converse over masks
     :encode :decode      #{base relations} ↔ mask
     :no-op?              does the universe compose to itself?}

  Built once per algebra and cached, since an algebra is a stable value and the tables
  are a pure function of it."
  [{:keys [universe identity compose converse]}]
  (let [rels (into [] (sort-by nm/name-key universe))
        k    (count rels)]
    (when (> k max-base-relations)
      (throw (ex-info (str "relation algebra has " k " base relations; "
                           max-base-relations " is the most a constraint mask holds")
                      {:type :unknown-option :mismatch :bad-value :base-relations k :limit max-base-relations})))
    (let [bit       (into {} (map-indexed (fn [i r] [r (bit-shift-left 1 i)])) rels)
          ;; a relation outside the universe contributes nothing: a network's constraints
          ;; are subsets of it by construction (a reader intersects into the universe),
          ;; and this is the encoding of that contract rather than a place to widen it.
          mask      (fn [s] (reduce (fn [^long m r] (bit-or m (long (get bit r 0)))) 0 s))
          conv-base (long-array (map (fn [r] (mask (converse #{r}))) rels))
          comp-base (long-array (for [a rels b rels] (mask (compose #{a} #{b}))))
          size      (bit-shift-left 1 k)
          dense?    (and (<= k 20) (<= (* k size) dense-table-limit))
          conv-tbl  (long-array (if dense? size 0))
          comp-tbl  (long-array (if dense? (* k size) 0))]
      (when dense?
        ;; ascending, so `s & (s-1)` — `s` without its lowest relation — is always the
        ;; entry just filled in.
        (dotimes [i (dec size)]
          (let [s    (inc i)
                low  (Long/numberOfTrailingZeros s)
                rest (bit-and s (dec s))]
            (aset conv-tbl s (bit-or (aget conv-tbl rest) (aget conv-base low)))
            (dotimes [r k]
              (aset comp-tbl (+ (* r size) s)
                    (bit-or (aget comp-tbl (+ (* r size) rest))
                            (aget comp-base (+ (* r k) low))))))))
      (let [^IRelationOps ops (if dense?
                                (qcn-types/->DenseOps comp-tbl conv-tbl size)
                                (qcn-types/->SparseOps comp-base conv-base k))
            cache (atom {})
            decode
            (fn [^long m]
              (caches/read-through
               cache (caches/limit-of :relation-decode decode-cache-limit) m
               #(into #{} (keep-indexed (fn [i r] (when (bit-test m i) r))) rels)))
            uni (mask universe)]
        {:universe uni
         :identity (mask identity)
         :ops      ops
         :encode   mask
         :decode   decode
         ;; the atom `decode` closes over, carried out so it can be counted.  A cache
         ;; reachable only through the closure that reads it is one nothing can report
         ;; on, and this one is the largest of the three here (8,192 against 64)
         :decode-cache cache
         :no-op?   (= uni (.compose ops uni uni))}))))

(defonce ^{:private true
           :doc "Compiled algebras, keyed on the algebra map itself.  Each calculus holds its algebra
  as one stable value, so this fills once per algebra and never turns over; the cap is
  the same cleared-wholesale bound the other caches here take, for a caller building
  algebras on the fly."}
  compiled-cache
  (atom {}))

(def ^:private compiled-cache-limit 64)

(defn- compiled
  "The bitmask form of `algebra`, built on first use."
  [algebra]
  (caches/read-through compiled-cache (caches/limit-of :compiled-algebras compiled-cache-limit) algebra
                       #(compile-algebra algebra)))

;; ---- the pass over masks -------------------------------------------------
;; A run encodes the network into `long[n*n]` — node pairs by index, universe where
;; nothing is recorded — tightens it in place, and decodes the pairs it touched back into
;; relation sets.  The array is local to the run and never escapes, so mutating it is a
;; private matter; what a caller sees is the same immutable network value as before.
;;
;; Every entry point below runs the *same* step over that array, so the plain and the
;; support-carrying pass — and the arc queue and the reference sweep — cannot drift in
;; what they compute.

(defn- encode
  "Nodes to indices, and the network to a flat array of masks.

  Two kinds of entry cannot live in the array and are carried through the run untouched
  in `:aside`: a **diagonal** pair, which no triple ever visits and which `constraint`
  answers the identity for anyway, and one naming a node outside `nodes`, which
  tightening was never going to reach.  Merging them back on the way out is what makes
  the encoding invisible — the decoded network holds exactly the pairs the set-valued
  network would."
  [net support nodes {:keys [^long universe encode no-op?]}]
  (let [node-vec (into [] (distinct) nodes)
        n        (count node-vec)
        index    (into {} (map-indexed (fn [i x] [x i])) node-vec)
        masks    (long-array (* n n) universe)
        recorded (BitSet. (* n n))
        sup      (when support (object-array (* n n)))]
    (loop [entries (seq net), aside (transient {}), aside-sup (transient {})]
      (if-let [[[a b :as pair] rels] (first entries)]
        (let [i (index a), j (index b)]
          (if (and i j (not= a b))
            (let [p (int (+ (* (long i) n) (long j)))]
              (aset masks p (long (encode rels)))
              (.set recorded p)
              (when sup (aset sup p (get support pair)))
              (recur (next entries) aside aside-sup))
            (recur (next entries)
                   (assoc! aside pair rels)
                   (if-let [s (get support pair)] (assoc! aside-sup pair s) aside-sup))))
        ;; `no-op?` rides along because a driver's choice of where to start depends on it:
        ;; only where the universe composes to itself is an unrecorded pair provably
        ;; incapable of narrowing anything on the first look.
        {:masks masks :recorded recorded :sup sup :n n :node-vec node-vec :index index
         :no-op? no-op? :aside (persistent! aside)
         :aside-support (persistent! aside-sup)}))))

(defn- decode-net
  "The tightened array back to a network: the pairs the array actually holds a constraint
  for, plus the entries `encode` set aside.  A pair nothing was recorded for stays absent,
  since an absent pair *is* the universe."
  [{:keys [^longs masks ^BitSet recorded ^long n node-vec aside]} decode]
  (loop [p (.nextSetBit recorded 0), acc (transient aside)]
    (if (neg? p)
      (persistent! acc)
      (recur (.nextSetBit recorded (inc p))
             (assoc! acc [(node-vec (quot p n)) (node-vec (rem p n))]
                     (decode (aget masks p)))))))

(defn- decode-support
  "The support array back to `{[i j] → #{handle}}`, over the same pairs."
  [{:keys [^objects sup ^BitSet recorded ^long n node-vec aside-support]}]
  (loop [p (.nextSetBit recorded 0), acc (transient aside-support)]
    (if (neg? p)
      (persistent! acc)
      (recur (.nextSetBit recorded (inc p))
             (if-let [s (aget sup p)]
               (assoc! acc [(node-vec (quot p n)) (node-vec (rem p n))] s)
               acc)))))

(defn- union3
  "The union of the support at three array positions: a narrowing constraint's own prior
  support and the supports of the two that composed to narrow it."
  [^objects sup ^long a ^long b ^long c]
  (-> (or (aget sup a) #{})
      (into (or (aget sup b) #{}))
      (into (or (aget sup c) #{}))))

(defn- stepper
  "The tightening step for one run: `(fn [i j k])` applying `R(i,k) ∩= R(i,j)∘R(j,k)` over
  node **indices**, with three outcomes —

    nil                                     nothing narrowed
    :narrowed                               the array now holds the tighter constraint
    {::inconsistent [i k] ::culprits …}     the constraint emptied

  A tightened constraint's support is the union of the supports of the two constraints
  that composed to narrow it and of its own prior support — the handles a caller would
  have to take away for the narrowing not to have happened.  Both directions of the pair
  are written, with the same support, exactly as both directions of the constraint are.

  A closure rather than a plain function so the compiled algebra and the run's arrays are
  destructured once for a whole pass instead of once per triple, and so `no-op?` — the one
  shortcut in the loop — is decided once.  A triple both of whose inputs are unknown can
  only narrow when the algebra composes the universe to something smaller than itself;
  where it does not (every algebra whose base relations are jointly exhaustive), such a
  triple is provably a no-op and is skipped without composing.  In a sparse network that
  is most of them.

  No triple ever reads a diagonal — its three indices are distinct — so the array holds
  constraints only, and the identity never has to be special-cased in the hot path."
  [{:keys [^longs masks ^objects sup ^BitSet recorded ^long n]}
   {:keys [^long universe no-op?] :as compiled}]
  (let [^IRelationOps ops (:ops compiled)]
    (fn [^long i ^long j ^long k]
      (let [pij (+ (* i n) j)
            pjk (+ (* j n) k)
            rij (aget masks pij)
            rjk (aget masks pjk)]
        (when-not (and no-op? (== universe rij) (== universe rjk))
          (let [pik (+ (* i n) k)
                rik (aget masks pik)
                new (bit-and rik (.compose ops rij rjk))]
            (cond
              (== new rik) nil

              (zero? new)
              {::inconsistent [i k] ::culprits (when sup (union3 sup pik pij pjk))}

              :else
              (let [pki (+ (* k n) i)]
                (aset masks (int pik) new)
                (aset masks (int pki) (.converse ops new))
                (.set recorded (int pik))
                (.set recorded (int pki))
                (when sup
                  (let [s (union3 sup pik pij pjk)]
                    (aset sup (int pik) s)
                    (aset sup (int pki) s)))
                :narrowed))))))))

(defn- walk-triples
  "Apply `f` to every ordered triple (i j k) of distinct indices below `n`, in index
  order, stopping at the first inconsistency report — a map — which it returns.

  Primitive loops rather than a sequence of triples: a sweep visits n(n-1)(n-2) of them,
  and one vector per triple would be the largest allocation in the pass."
  [^long n f]
  (loop [i 0, j 0, k 0]
    (cond
      (== i n)                       nil
      (== j n)                       (recur (inc i) 0 0)
      (== k n)                       (recur i (inc j) 0)
      (or (== i j) (== j k) (== i k)) (recur i j (inc k))
      :else                          (let [r (f i j k)]
                                       (if (map? r) r (recur i j (inc k)))))))

(defn- walk-reading
  "Apply `f` to the triples that **read** the constraint on `[a b]`: `(a b m)`, which
  tightens `(a m)`, and `(m a b)`, which tightens `(m b)`.  Every triple with `[a b]` as
  an input is one of those, so revisiting them is exactly the work a change to that pair
  creates — and nothing else has to be looked at again.  Stops at the first report."
  [^long n ^long a ^long b f]
  (loop [m 0]
    (cond
      (== m n)                nil
      (or (== m a) (== m b))  (recur (inc m))
      :else                   (let [r (f a b m)]
                                (if (map? r)
                                  r
                                  (let [r2 (f m a b)]
                                    (if (map? r2) r2 (recur (inc m)))))))))

(defn- sweep
  "Tighten over every triple, recording into `changed` the array positions that narrowed.
  Returns nil, or the inconsistency report."
  [step ^long n ^LinkedHashSet changed]
  (walk-triples n (fn [^long i ^long j ^long k]
                    (let [r (step i j k)]
                      (when (identical? :narrowed r)
                        (.add changed (Long/valueOf (+ (* i n) k)))
                        (.add changed (Long/valueOf (+ (* k n) i))))
                      r))))

(defn- drain
  "Revisit only what a narrowing can have affected: pop a pair, tighten the triples that
  read it, enqueue whatever that narrows, until the queue empties.  Returns nil, or the
  inconsistency report.

  Terminates because every entry on the queue was put there by a strict narrowing over a
  finite universe.  At the end every triple has been examined since its inputs last
  changed, which is the same closure a repeated sweep reaches — a pair *being* narrowed
  never invalidates a triple that reads it, since a subset of a set that was already
  contained is still contained.

  `budget` caps the **pops** a drain may make before it gives up and returns
  `::over-budget`.  A caller that reached for the queue on an estimate uses it to bound
  how wrong that estimate can be: the array is monotonically narrowed and the fixpoint
  below the network it started from is unique, so an abandoned drain has done real work
  and any other driver finishes from there.  Omit it and the drain runs to completion."
  ([step n seed] (drain step n seed Long/MAX_VALUE))
  ([step ^long n ^LinkedHashSet seed ^long budget]
   (let [queue  (ArrayDeque. seed)
         queued (LinkedHashSet. seed)
         push!  (fn [^long p]
                  (let [b (Long/valueOf p)]
                    (when (.add queued b) (.add queue b))))
         visit  (fn [^long i ^long j ^long k]
                  (let [r (step i j k)]
                    (when (identical? :narrowed r)
                      (push! (+ (* i n) k))
                      (push! (+ (* k n) i)))
                    r))]
     (loop [pops 0]
       (let [p (.poll queue)]
         (cond
           (nil? p)         nil
           (> pops budget)  ::over-budget
           :else            (let [pl (long p)]
                              (.remove queued p)
                              (if-let [bad (walk-reading n (quot pl n) (rem pl n) visit)]
                                bad
                                (recur (inc pops))))))))))

(defn- fixpoint-by-sweep
  "Sweep every triple, and sweep again while anything narrowed."
  [step ^long n _state]
  (loop []
    (let [changed (LinkedHashSet.)
          bad     (sweep step n changed)]
      (cond
        bad                bad
        (.isEmpty changed) nil
        :else              (recur)))))

(defn- recorded-seeds
  "The array positions a constraint was *read into*, both directions, as a queue seed.

  Under a jointly-exhaustive algebra a triple whose two inputs are both unknown can narrow
  nothing (`no-op?`), so on the very first pass these are the only pairs a triple can read
  and learn anything from — which makes them a legitimate seed for a run that has not
  swept yet.  Both directions, since either can be an input and only one of them need have
  been written by the reader."
  [^BitSet recorded ^long n]
  (let [seeds (LinkedHashSet.)]
    (loop [p (.nextSetBit recorded 0)]
      (when-not (neg? p)
        (.add seeds (Long/valueOf p))
        (.add seeds (Long/valueOf (+ (* (rem p n) n) (quot p n))))
        (recur (.nextSetBit recorded (inc p)))))
    seeds))

(defn- fixpoint-by-queue
  "Revisit by **whichever is cheaper** — the arc queue, or a sweep — decided twice.

  A full sweep is how every triple gets its first look: one visit each, where seeding a
  queue with all n(n-1) pairs would visit each triple twice.  After a sweep, a triple
  needs revisiting only if one of the two constraints it *reads* narrowed, and those are
  exactly the pairs the sweep reports — so the work left is `2 × changed × (n-2)` triple
  visits against a sweep's `n(n-1) × (n-2)`, and the two counts say directly which to do.
  A sparse network moves a handful of pairs and drains in a rounding error; one that pins
  nearly every pair would cost about two sweeps to drain, and sweeping again is less work.
  Each changed pair is queued in **both** directions, since both are written on every
  tightening and either can be an input to a triple.

  **The first look need not be a sweep either.**  A network read out of a KB records a
  constraint at a handful of pairs and leaves the rest unknown, and under a
  jointly-exhaustive algebra a triple reading two unknowns narrows nothing — so the
  recorded pairs are the only ones worth starting from, and there are `m` of them where a
  sweep visits `n(n-1)` pairs' worth of triples.  Where `m` is small that is the same
  saving the queue makes after a sweep, made *before* one.  What the estimate cannot see
  is how much the network will turn out to narrow: a sparse input can still close to a
  dense output, and then draining costs more than sweeping.  So the drain is **budgeted**
  at one sweep's worth of pops and gives up rather than run away — its work is kept (the
  array only ever narrows) and the sweep route finishes from there.

  Both routes run the same step to the same fixpoint (`path-consistent-naive` is the
  re-sweeping reference, and `qcn-queue-test` proves them equal), so which one a run takes
  is a cost decision and nothing more."
  [step ^long n state]
  (let [sweep-cost (* n (max 0 (dec n)))
        sweeping   (fn []
                     (loop []
                       (let [changed (LinkedHashSet.)
                             bad     (sweep step n changed)]
                         (cond
                           bad                                  bad
                           (.isEmpty changed)                   nil
                           (< (* 2 (.size changed)) sweep-cost) (drain step n changed)
                           :else                                (recur)))))
        seeds      (when (:no-op? state)
                     (let [^LinkedHashSet s (recorded-seeds (:recorded state) n)]
                       (when (< (* 2 (.size s)) sweep-cost) s)))]
    (if (nil? seeds)
      (sweeping)
      (let [r (drain step n seeds (quot sweep-cost 2))]
        (if (identical? ::over-budget r) (sweeping) r)))))

(defn- fixpoint-from
  "The **warm-started** driver: the array arrives already path-consistent except at
  `seed-pairs`, so only the triples reading one of those need visiting at all.

  That is the same claim `drain` rests on — a triple is closed until one of the two
  constraints it *reads* narrows — applied to a network that was closed by an earlier run
  rather than by this one's first sweep.  So no sweep is owed here, and the first pass is
  already the queue.

  It still makes `fixpoint-by-queue`'s cost comparison rather than assuming the queue is
  cheaper: a seed set covering most of the pairs costs about two sweeps to drain, and one
  sweep-to-fixpoint is less work.  The two reach the same answer either way — the fixpoint
  is unique below the network it starts from — so this is a cost decision and nothing
  more, exactly as it is there."
  [seed-pairs]
  (fn [step ^long n state]
    (let [index (:index state)
          seeds (LinkedHashSet.)]
      (doseq [[a b] seed-pairs
              :let  [i (index a), j (index b)]
              :when (and i j (not= a b))]
        (.add seeds (Long/valueOf (+ (* (long i) n) (long j))))
        (.add seeds (Long/valueOf (+ (* (long j) n) (long i)))))
      (cond
        (.isEmpty seeds)                              nil
        (< (* 2 (.size seeds)) (* n (max 0 (dec n)))) (drain step n seeds)
        :else                                         (fixpoint-by-queue step n state)))))

(defn- given-inconsistency
  "The inconsistency report for a network that is unsatisfiable *before* any tightening,
  or nil.  The blamed pair is the smallest of them under `nm/print-key`, so which one is
  named is a function of content rather than of iteration order."
  [net support algebra]
  (let [bad (unsatisfiable-pairs net algebra)]
    (when (seq bad)
      (let [pair (nm/min-by-content-key nm/print-key compare bad)]
        {::inconsistent pair ::culprits (get support pair #{})}))))

(defn- run
  "The driver every entry point below shares: refuse a network no tightening could report
  on (`unsatisfiable-as-given?`), encode, run `driver` to the fixpoint, decode.  Returns
  `{:net … :support …}` or the inconsistency report, its pair named in **nodes** rather
  than in the indices the loop works in."
  [net support nodes algebra driver]
  (or (given-inconsistency net support algebra)
      (let [c     (compiled algebra)
            state (encode net support nodes c)
            bad   (driver (stepper state c) (:n state) state)]
        (if bad
          (let [[i k] (::inconsistent bad)
                nv    (:node-vec state)]
            {::inconsistent [(nv i) (nv k)] ::culprits (::culprits bad)})
          {:net     (decode-net state (:decode c))
           :support (when support (decode-support state))}))))

(defn path-consistent-naive
  "Path consistency by **repeated full sweeps**: visit all n(n-1)(n-2) triples, and do it
  again while anything narrowed.

  Same arguments and same answer as `path-consistent`, more work — it is kept as the
  **reference the arc queue is proven against** (`qcn-queue-test` runs both over
  randomized networks across four algebras and asserts they agree, network for network
  and verdict for verdict).  Two implementations that share their tightening step and
  differ only in which triples they revisit can agree only by both being right."
  [net nodes algebra]
  (let [outcome (run net nil nodes algebra fixpoint-by-sweep)]
    (if (::inconsistent outcome) :inconsistent (:net outcome))))

(defn path-consistent
  "Enforce composition closure over `net` across `nodes`: for every triple (i j k),
  tighten R(i,k) ∩= R(i,j)∘R(j,k), to a fixpoint.  Returns the tightened network, or
  `:inconsistent` the moment any constraint empties — an empty constraint says two nodes
  can stand in no relation at all, which no model can satisfy.  A constraint that is
  unsatisfiable *as given* counts too, whatever the node count and whether or not its
  nodes were passed: see `unsatisfiable-as-given?`.

  Each constraint set is expected to be a **subset of the algebra's universe**, which is
  what a reader produces by construction — it intersects into the universe rather than
  writing relations of its own.

  `nodes` is what the triples are drawn from, so it is the **caller's** obligation to
  pass every node the network mentions — tightening reaches only the nodes it is given,
  and a node left out is a path composition left unmade.  Passing extra nodes is safe: an
  isolated one constrains nothing, since its every constraint is the universe and the
  universe composes to itself — which is exactly the condition a jointly-exhaustive
  algebra meets, and the one every calculus here is built on.

  The result does not depend on the order of `nodes`, nor on the order the triples are
  visited in.  Tightening only ever narrows, and composition is monotone in ⊆, so the
  loop computes the unique greatest fixpoint below the network it was handed — order
  decides only how many revisits that takes.  The universe is finite and every step
  strictly narrows something, so it terminates.  Both directions are written on every
  tightening, so `constraint` never has to consult the converse.

  It is that order-independence which lets the loop be an **arc queue** (PC-2) rather
  than a re-sweep: one full pass over the triples, then revisits of only those a
  narrowing could have affected (`fixpoint-by-queue`).  `path-consistent-naive` is the
  re-sweeping reference it is proven equal to."
  [net nodes algebra]
  (let [outcome (run net nil nodes algebra fixpoint-by-queue)]
    (if (::inconsistent outcome) :inconsistent (:net outcome))))

;; ---- warm-starting: semi-naive over the network --------------------------
;; A KB that is being loaded asks for the pass again after every arriving fact, and all
;; but a handful of the pairs are exactly where the last run left them.  Closing the whole
;; thing again is the cubic loop redoing work it has already done — so a run that can be
;; told what moved starts from the previous answer and revisits only that.
;;
;; The identity that licenses it: path consistency computes the **greatest fixpoint below
;; the network it is handed**, so for a narrowing `c`, `PC(N ∩ c) = PC(PC(N) ∩ c)`.  Both
;; sides are ≤ `N ∩ c`; `PC(N ∩ c)` is a fixpoint below `PC(N)` (monotonicity) so it is
;; below the right-hand side, and the right-hand side is a fixpoint below `N ∩ c` so it is
;; below the left.  Warm-starting is therefore not an approximation — it is the same
;; answer, reached without re-deriving what did not move.
;;
;; It applies to **narrowing only**.  Widening — a fact retracted, a belief withdrawn — has
;; no such identity: a fixpoint cannot be undone from its result, since the result does not
;; record which of its narrowings the departing constraint was behind.  So a caller that
;; cannot show its new network is a narrowing of the old one runs the whole pass, which is
;; `qcn-kb`'s answer to retraction.

(defn narrowing-of?
  "Is `net` a pointwise **narrowing** of `prior` — is every pair's constraint at most as
  wide?  A pair `prior` records and `net` does not is the universe in `net`, so it is a
  narrowing only where `prior` records the universe there too.

  This is the precondition of `path-consistent-from`, and it is the caller's to check
  because only the caller holds the network the previous answer was computed from."
  [net prior {:keys [universe]}]
  (every? (fn [[pair rels]] (set/subset? (get net pair universe) rels)) prior))

(defn path-consistent-from
  "`path-consistent`, **warm-started** from `prior` — an answer this function returned for
  some earlier network of which `net` is a pointwise narrowing (`narrowing-of?`).

  Returns exactly what `path-consistent` would for `net` alone: the closure starts from
  `prior ∩ net` and revisits only the triples reading a pair where `net` is stricter than
  `prior`, which is the whole of what a narrowing can have invalidated.  See the note
  above for the fixpoint identity that makes those two the same value.

  `nodes` need name only what neither network mentions — a goal's own terms — since the
  rest are read off the merged network here.  That is not merely a convenience: a warm
  start is taken exactly when facts have *arrived*, and an arriving fact routinely names a
  node neither the previous network nor the caller's list holds.  A node left out is a
  node no triple visits, so its every composition goes unmade and the answer comes back
  looking merely uninformative rather than wrong.

  Handing it a `prior` that is *not* an answer for a network `net` narrows — or one from a
  different algebra — is a caller error and yields a network tighter than the facts
  license.  `narrowing-of?` is the guard; there is no cheaper one, since the whole point
  is not to look at the pairs that did not move."
  [net prior nodes algebra]
  (let [{:keys [universe]} algebra
        merged (reduce-kv (fn [m pair rels]
                            (assoc m pair (set/intersection (get net pair universe) rels)))
                          net prior)
        seeds  (into [] (keep (fn [[pair rels]]
                                (when-not (= rels (get prior pair universe)) pair)))
                     merged)
        ;; off `merged`, which holds every pair of both networks — `prior`'s nodes and
        ;; `net`'s, including the ones an arriving fact has just introduced
        ns'    (into (set nodes) (mapcat identity) (keys merged))
        outcome (run merged nil ns' algebra (fixpoint-from seeds))]
    (if (::inconsistent outcome) :inconsistent (:net outcome))))

(defn path-consistent-with-support
  "`path-consistent`, carrying **support** alongside the constraints: which stored
  sentexes an entailed relation rests on.

  `support` is the asserted support, `{[i j] → #{handle}}` — the sentexes a reader
  intersected into that pair's constraint.  A tightened constraint's support is the union
  of the supports of the two constraints that composed to narrow it and of its own prior
  support, so support propagates exactly where a narrowing does.

  Returns `{:network … :support …}`, or, when a constraint empties,
  `{:inconsistent [i j] :culprits #{handle}}` — the pair that emptied and the sentexes
  behind it, which is what a caller wants to know about an impossible network.  Which
  pair is blamed for a *derived* inconsistency depends on which one the fixpoint empties
  first, so treat the culprits as a diagnosis rather than as a canonical explanation; the
  *verdict* does not depend on that, only the blame does.

  Two things the support is **not**, and both matter to a caller.

  It is not **minimal**.  Support accumulates on every narrowing, so a pair narrowed
  twice keeps the first narrowing's support even where the second subsumed it — an
  over-approximation of the derivation it names.

  It is not **every** derivation.  Support propagates only where a constraint *moves*, so
  a second route that re-derives the value a first route already reached contributes
  nothing: what comes back is *a* witness, the accumulated one that produced the current
  value, not the set of all of them.  That is deliberate — it is exactly what a
  justification is (one support list; a datum with two derivations gets two
  justifications), and unioning across re-derivations would mean iterating the support
  system to its own fixpoint over every triple, whether or not anybody asked.  So
  retracting the reported set destroys *that* derivation; where the network has an
  independent second route the relation survives, and asking again names the survivor.

  What is guaranteed: every handle named is a sentex really read into this network, and
  the reported set is enough to have produced the relation on its own."
  [net support nodes algebra]
  (let [outcome (run net (or support {}) nodes algebra fixpoint-by-queue)]
    (if-let [pair (::inconsistent outcome)]
      {:inconsistent pair :culprits (or (::culprits outcome) #{})}
      {:network (:net outcome) :support (:support outcome)})))

;; ---- what the algebras hold, declared -----------------------------------
;;
;; Both are process-wide and shared by every KB: a calculus holds its algebra as one
;; stable value, so the compiled form is keyed on that value and two KBs running Allen
;; share one compilation and one decode table.  Neither offers a clear — dropping either
;; costs a recompile and buys no measurement, since nothing counts a hit on them.

(caches/register-cache
 {:cache    :compiled-algebras
  :label    "Compiled algebras"
  :scope    :process
  :unit     "algebras"
  :limit    (caches/limit-thunk :compiled-algebras compiled-cache-limit)
  :counters nil
  :note     (str "Each relation algebra's composition and converse tables, in bitmask "
                 "form, keyed on the algebra itself. One entry per calculus in use, so "
                 "this fills once and never turns over; the bound is for a caller "
                 "building algebras on the fly.")
  :read     (fn [_] {:entries (count @compiled-cache)})})

(caches/register-cache
 {:cache    :relation-decode
  :label    "Relation decode tables"
  :scope    :process
  :unit     "masks"
  :limit    (caches/limit-thunk :relation-decode decode-cache-limit)
  :counters nil
  :note     (str "One decoded relation set per bitmask the tightening pass has handed "
                 "back, held per compiled algebra — so the limit is per algebra and the "
                 "count here is the total across all of them.")
  :read     (fn [_] {:entries (reduce + 0 (map #(count @(:decode-cache %))
                                               (vals @compiled-cache)))})})
