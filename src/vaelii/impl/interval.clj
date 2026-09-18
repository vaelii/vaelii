;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.interval
  "Allen's interval algebra — a relation algebra over the generic constraint network in
  `vaelii.impl.qcn`, and the third alongside the RCC-8 topology of `vaelii.impl.space`
  and the cardinal directions of `vaelii.impl.orientation`.  Those two say where things
  are; this one says *when* they are, and about intervals rather than instants: an
  interval has extent, so two of them can meet, overlap, or nest, and not merely precede
  one another.

  The thirteen base relations are jointly exhaustive and pairwise disjoint, so exactly
  one holds of any two intervals.  Each is a claim about the four ways their endpoints
  can compare — writing an interval as `[start end]` with `start < end`:

    :before        a-end   < b-start
    :meets         a-end   = b-start
    :overlaps      a-start < b-start < a-end < b-end
    :finished-by   a-start < b-start,  a-end = b-end
    :contains      a-start < b-start,  a-end > b-end
    :starts        a-start = b-start,  a-end < b-end
    :equal         a-start = b-start,  a-end = b-end
    :started-by    a-start = b-start,  a-end > b-end
    :during        a-start > b-start,  a-end < b-end
    :finishes      a-start > b-start,  a-end = b-end
    :overlapped-by b-start < a-start < b-end < a-end
    :met-by        a-start = b-end
    :after         a-start > b-end

  Six of them pair off with their converses (`:before`/`:after`, `:meets`/`:met-by`,
  `:overlaps`/`:overlapped-by`, `:starts`/`:started-by`, `:during`/`:contains`,
  `:finishes`/`:finished-by`); `:equal` is its own converse and the algebra's identity.

  Intervals are **stored as ordinary sentexes** — the thirteen named binary predicates
  (`before`, `meets`, `during`, …), plus seven derived predicates (`precedes`,
  `subintervalOf`, `sharesTimeWith`, …) that each name a *disjunction* of them.
  Intervals are ordinary individuals; nothing about them is special, and nothing here
  reasons about clocks, dates or durations — only about order and containment.

  The calculus reads every asserted interval relation visible from a context into a
  qualitative constraint network — `{[i j] → #{possible base relations}}`, an unrecorded
  pair meaning \"unknown\", i.e. all thirteen — and `qcn/path-consistent` tightens it to a
  fixpoint.  the prover then answers a goal `(P i j)` by **entailment**: it holds iff
  every relation still possible between i and j satisfies P, `possible ⊆ denotation(P)`.
  So `(before A B)` and `(before B C)` entail `(before A C)`, and `(during A B)` with
  `(during B C)` entails `(during A C)` and the weaker `(subintervalOf A C)` with it.

  **Stored facts are not the only reader.**  This is the one calculus with a
  `qcn-kb` **narrowing**: `stp/allen-narrowing-with-support` closes the metric constraints
  over the instants `(startOf I P)` / `(endOf I P)` name and reads back what they pin down
  about the interval relations, and that is intersected into the same network.  So a KB
  that states two meetings' start and end times, and the gap between them, answers
  `(before A B)` with no interval relation written anywhere — and the entailment names the
  metric facts, the endpoint facts and the unit rows behind it, so retracting any of them
  withdraws whatever was concluded from it.  It runs one way only: metric narrows
  qualitative, never the reverse (docs/stp.md).

  An emptied constraint anywhere means the asserted relations are unsatisfiable, and then
  *no* interval goal is answered — an inconsistent theory should not be mined for
  conclusions.

  **Soundness.** Path consistency is sound but not in general complete: it decides the
  maximal tractable subclass of the interval algebra and no more, so an entailment
  reported here is real while a *non*-entailment means \"not provable\", never \"provably
  false\" — the same open-world reading `arg` and `exceptWhen` take.

  The vocabulary ships as `kb/upper/CxTime.txt`, an *upper* context rather than the
  vocabulary head: these twenty predicates are *about* time, so CxCore keeps only the
  grammar they are declared in.  The prover is **opt-in** on top of it: register it with
  `vaelii.core/add-prover`, and until then a KB stores and retrieves interval relations as
  ordinary facts without paying for the network."
  (:require [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.stp :as stp]))

;; ---- the algebra --------------------------------------------------------

(def all-relations
  "The thirteen jointly-exhaustive, pairwise-disjoint interval relations — the universe
  of the algebra, and so the constraint on a pair nothing is known about."
  #{:before :after :meets :met-by :overlaps :overlapped-by
    :starts :started-by :during :contains :finishes :finished-by :equal})

(def allen-converse
  "Each base relation's converse — reading the claim backwards.  Six pairs and one
  self-converse, since `:equal` is the identity."
  {:before :after,     :after :before
   :meets :met-by,     :met-by :meets
   :overlaps :overlapped-by, :overlapped-by :overlaps
   :starts :started-by, :started-by :starts
   :during :contains,  :contains :during
   :finishes :finished-by, :finished-by :finishes
   :equal :equal})

(defn converse-set
  "The converse of a relation set — how an asserted `(P a b)` constraint is read
  backwards as the constraint on `(b a)`."
  [rels]
  (into #{} (map allen-converse) rels))

;; The composition table below is written out of thirteen recurring blocks rather than 169
;; loose sets, because that is what its entries actually are.  Composing two relations
;; pins some of the four endpoint comparisons between the outer intervals and leaves the
;; rest free, and each block is the set of relations agreeing on the comparisons it pins —
;; so an entry says *which comparison survived the composition*, and can be read back
;; against the endpoint definitions above rather than merely trusted.

(def ^:private starts-first  "a-start < c-start" #{:before :meets :overlaps :finished-by :contains})
(def ^:private starts-last   "a-start > c-start" #{:after :met-by :overlapped-by :finishes :during})
(def ^:private ends-first    "a-end   < c-end"   #{:before :meets :overlaps :starts :during})
(def ^:private ends-last     "a-end   > c-end"   #{:after :met-by :overlapped-by :started-by :contains})
(def ^:private same-start    "a-start = c-start" #{:starts :started-by :equal})
(def ^:private same-end      "a-end   = c-end"   #{:finishes :finished-by :equal})
(def ^:private leads         "a-start < c-start and a-end < c-end" #{:before :meets :overlaps})
(def ^:private trails        "a-start > c-start and a-end > c-end" #{:after :met-by :overlapped-by})
(def ^:private ends-inside   "c-start < a-end   < c-end"   #{:overlaps :starts :during})
(def ^:private starts-inside "c-start < a-start < c-end"   #{:overlapped-by :during :finishes})
(def ^:private holds-c-start "a-start < c-start < a-end"   #{:overlaps :contains :finished-by})
(def ^:private holds-c-end   "a-start < c-end   < a-end"   #{:overlapped-by :contains :started-by})
(def ^:private concurrent
  "The nine relations under which two intervals share some time — the complement of
  `:before`, `:after`, `:meets` and `:met-by`."
  #{:overlaps :overlapped-by :starts :started-by :during :contains :finishes :finished-by :equal})

(def allen-composition
  "The canonical Allen composition table: `(get-in allen-composition [r1 r2])` is the set
  of base relations possible between A and C given `r1`(A,B) and `r2`(B,C).  `:equal` is
  the identity element on both sides.

  Only three entries are the whole universe, and each is the same shape: two intervals
  positioned against a third that constrains neither against the other.  A before B and C
  after B says nothing (both sit on the far side of B, in either order); so does A during
  B with B containing C, where A and C are both loose inside B.

  `interval_test` derives all 169 entries independently, by enumerating every ordering of
  six endpoints and reading off which outer relation each admits, and asserts the derived
  table equals this one — so a mis-transcribed entry is a test failure, not a wrong
  answer."
  {:before        {:before #{:before}     :after all-relations :meets #{:before}
                   :met-by ends-first    :overlaps #{:before}   :overlapped-by ends-first
                   :starts #{:before}     :started-by #{:before} :during ends-first
                   :contains #{:before}   :finishes ends-first  :finished-by #{:before}
                   :equal #{:before}}
   :after         {:before all-relations :after #{:after}       :meets starts-last
                   :met-by #{:after}      :overlaps starts-last :overlapped-by #{:after}
                   :starts starts-last   :started-by #{:after}  :during starts-last
                   :contains #{:after}    :finishes #{:after}    :finished-by #{:after}
                   :equal #{:after}}
   :meets         {:before #{:before}     :after ends-last      :meets #{:before}
                   :met-by same-end      :overlaps #{:before}   :overlapped-by ends-inside
                   :starts #{:meets}      :started-by #{:meets}  :during ends-inside
                   :contains #{:before}   :finishes ends-inside :finished-by #{:before}
                   :equal #{:meets}}
   :met-by        {:before starts-first  :after #{:after}       :meets same-start
                   :met-by #{:after}      :overlaps starts-inside :overlapped-by #{:after}
                   :starts starts-inside :started-by #{:after}  :during starts-inside
                   :contains #{:after}    :finishes #{:met-by}   :finished-by #{:met-by}
                   :equal #{:met-by}}
   :overlaps      {:before #{:before}     :after ends-last      :meets #{:before}
                   :met-by holds-c-end   :overlaps leads       :overlapped-by concurrent
                   :starts #{:overlaps}   :started-by holds-c-start :during ends-inside
                   :contains starts-first :finishes ends-inside :finished-by leads
                   :equal #{:overlaps}}
   :overlapped-by {:before starts-first  :after #{:after}       :meets holds-c-start
                   :met-by #{:after}      :overlaps concurrent  :overlapped-by trails
                   :starts starts-inside :started-by trails    :during starts-inside
                   :contains ends-last   :finishes #{:overlapped-by} :finished-by holds-c-end
                   :equal #{:overlapped-by}}
   :starts        {:before #{:before}     :after #{:after}       :meets #{:before}
                   :met-by #{:met-by}     :overlaps leads       :overlapped-by starts-inside
                   :starts #{:starts}     :started-by same-start :during #{:during}
                   :contains starts-first :finishes #{:during}  :finished-by leads
                   :equal #{:starts}}
   :started-by    {:before starts-first  :after #{:after}       :meets holds-c-start
                   :met-by #{:met-by}     :overlaps holds-c-start :overlapped-by #{:overlapped-by}
                   :starts same-start    :started-by #{:started-by} :during starts-inside
                   :contains #{:contains} :finishes #{:overlapped-by} :finished-by #{:contains}
                   :equal #{:started-by}}
   :during        {:before #{:before}     :after #{:after}       :meets #{:before}
                   :met-by #{:after}      :overlaps ends-first  :overlapped-by starts-last
                   :starts #{:during}     :started-by starts-last :during #{:during}
                   :contains all-relations :finishes #{:during} :finished-by ends-first
                   :equal #{:during}}
   :contains      {:before starts-first  :after ends-last      :meets holds-c-start
                   :met-by holds-c-end   :overlaps holds-c-start :overlapped-by holds-c-end
                   :starts holds-c-start :started-by #{:contains} :during concurrent
                   :contains #{:contains} :finishes holds-c-end :finished-by #{:contains}
                   :equal #{:contains}}
   :finishes      {:before #{:before}     :after #{:after}       :meets #{:meets}
                   :met-by #{:after}      :overlaps ends-inside :overlapped-by trails
                   :starts #{:during}     :started-by trails    :during #{:during}
                   :contains ends-last   :finishes #{:finishes} :finished-by same-end
                   :equal #{:finishes}}
   :finished-by   {:before #{:before}     :after ends-last      :meets #{:meets}
                   :met-by holds-c-end   :overlaps #{:overlaps} :overlapped-by holds-c-end
                   :starts #{:overlaps}   :started-by #{:contains} :during ends-inside
                   :contains #{:contains} :finishes same-end    :finished-by #{:finished-by}
                   :equal #{:finished-by}}
   :equal         {:before #{:before} :after #{:after} :meets #{:meets} :met-by #{:met-by}
                   :overlaps #{:overlaps} :overlapped-by #{:overlapped-by}
                   :starts #{:starts} :started-by #{:started-by}
                   :during #{:during} :contains #{:contains}
                   :finishes #{:finishes} :finished-by #{:finished-by}
                   :equal #{:equal}}})

(defn compose
  "The composition of two relation SETS: every base relation possible between A and C
  when r(A,B) ∈ `s1` and r(B,C) ∈ `s2` — the union of the table entries, since a
  disjunction on either side admits every combination."
  [s1 s2]
  (into #{}
        (mapcat (fn [a] (mapcat (fn [b] (get-in allen-composition [a b])) s2)))
        s1))

(def allen-algebra
  "Allen's interval algebra as a `vaelii.impl.qcn` relation algebra."
  {:universe all-relations
   :identity #{:equal}
   :compose  compose
   :converse converse-set})

;; ---- the vocabulary -----------------------------------------------------

(def base-relation-predicate
  "Base relation keyword → the binary predicate a fact about it is stored under.
  `:equal` is spelled `intervalEqual`: it is a claim about extent in time, not about the
  identity of two terms, so it must not be confused with the equality closure's `equals`."
  '{:before        before
    :after         after
    :meets         meets
    :met-by        metBy
    :overlaps      overlaps
    :overlapped-by overlappedBy
    :starts        starts
    :started-by    startedBy
    :during        during
    :contains      contains
    :finishes      finishes
    :finished-by   finishedBy
    :equal         intervalEqual})

(def interval-denotation
  "Every interval predicate — the thirteen base ones and the seven derived ones — mapped
  to the set of base relations it denotes.  A goal `(P i j)` is entailed exactly when the
  relations still possible between i and j are a *subset* of P's denotation, so a derived
  predicate with a wide denotation is entailed by more networks than a base one, and the
  base predicates are the singletons.

  The derived seven are the disjunctions worth asking about: the two orderings that do
  not care whether the intervals touch, the three part-of relations, and the pair that
  says whether two intervals share any time at all."
  (merge
   (into {} (map (fn [[rel pred]] [pred #{rel}])) base-relation-predicate)
   {'precedes            #{:before :meets}
    'precededBy          #{:after :met-by}
    'subintervalOf       #{:during :starts :finishes :equal}
    'properSubintervalOf #{:during :starts :finishes}
    'hasSubinterval      #{:contains :started-by :finished-by :equal}
    'sharesTimeWith      concurrent
    'temporallyDisjoint  #{:before :after :meets :met-by}}))

;; ---- the calculus, and the glue it shares with every other algebra -------

(def allen
  "Allen's interval algebra as a `vaelii.impl.qcn-kb` calculus — the algebra, the
  vocabulary, the two caches, and the metric narrowing.  Everything below delegates to the
  shared glue, which is the same code RCC-8 and the cardinal directions run.

  The **narrowing** is what the other five calculi have no counterpart for, and it is why
  this namespace requires `stp` rather than the other way about: an interval is bounded by
  two instants a metric constraint can speak of, so the metric layer is a second reader of
  this network.  `:sources` is every predicate whose arrival moves what it answers —
  the constraints, the two endpoint predicates and the unit table their magnitudes convert
  through — and `:contexts` the ones that put an interval *into* a network, which is what
  makes a context worth reading one at.  A `conversionFactor` is in the first and not the
  second: it changes what a bound comes to, and a context holding one and no interval has
  nothing to narrow."
  (qkb/calculus :allen allen-algebra interval-denotation
                {:fn       stp/allen-narrowing-with-support
                 :sources  stp/allen-narrowing-sources
                 :contexts (into stp/stp-predicates stp/endpoint-predicates)}))

(defn possible-allen-relations
  "The Allen base relations still possible between intervals `i1` and `i2` given
  everything believed in `context` — `#{}` when the network is inconsistent.

  This is the algebra read directly rather than through a goal, so a caller that needs to
  know *how much* is pinned down — rather than whether one named relation is entailed —
  asks here.  `vaelii.impl.duration` is the one in tree."
  [kb context i1 i2]
  (qkb/possible allen kb context i1 i2))

(defn allen-support
  "The handles of the stored sentexes the relation set between `i1` and `i2` rests on —
  `possible-allen-relations`' support (`qcn-kb/support`).

  `#{}` when the pair is unconstrained, which is the honest answer: an unconstrained pair
  leaves all thirteen relations open, and nothing stored says so.  A caller drawing a
  conclusion from what the relations *narrow* rests on exactly this set."
  [kb context i1 i2]
  (qkb/support allen kb context i1 i2))

(defn allen-predicates
  "Every predicate the Allen calculus reads — the thirteen base relations and the seven
  derived ones.  What a caller whose answer depends on the interval network names as its
  sources (`prover-types/SupportingProver`)."
  []
  (:predicates allen))

(defn definite-allen-relation
  "The single base relation between `i1` and `i2` when path consistency pins it down;
  `:inconsistent` when the network contradicts itself, `:unknown` when two or more
  relations remain possible."
  [kb context i1 i2]
  (qkb/definite allen kb context i1 i2))

(defn allen-prover
  "The interval-algebra entailment prover, to register with `vaelii.core/add-prover`."
  []
  (qkb/prover allen))
