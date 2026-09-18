;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.calendar
  "The clock behind the calendar constructors — where `(YearFn 2000)` stops being a name
  the interval algebra relates and starts being a **stretch between two moments**.

  `vaelii.impl.datetime` reads a calendar term to its fields and to the half-open
  `[start end]` it lies between; this namespace is the KB-facing half, one prover
  answering three families of goal out of that reading and storing nothing:

    (startOf (YearFn 2000) ?i)              ?i = (InstantFn 2000 1 1 0 0 0)
    (endOf   (YearFn 2000) ?i)              ?i = (InstantFn 2001 1 1 0 0 0)
    (instantBefore (InstantFn 1999 6 1 0 0 0) (InstantFn 2000 1 1 0 0 0))
    (during (MonthFn 2000 3) (YearFn 2000))
    (meets  (MonthFn 2000 2) (MonthFn 2000 3))

  **Answered, never stored.**  Nothing here mints a term, asserts a sentex or posts a
  justification, so a computed endpoint is not a belief, needs no retraction, and leaves
  no orphan for the NAT sweep to ask about (docs/nat.md).  What it rests on is the
  calendar and the convention, both of which are in this code rather than in the store —
  which is why it implements `Prover` and not `SupportingProver`: there is no handle to
  name, and a prover that names none is one whose answer no retraction can invalidate
  (docs/inference.md, \"What a computed answer rests on\").

  **Half-open, `[start, end)`.**  A term's end is the first moment of the next term at the
  same precision, so the end of 1999 and the start of 2000 are the same term and
  consecutive calendar terms **meet**.  `(before (YearFn 1999) (YearFn 2000))` therefore
  does *not* hold and `(precedes …)` does — before is Allen's strict one, with a gap, and
  `precedes` is the ordering that does not care whether the two touch, which is what
  \"1999 comes before 2000\" means (docs/time.md).

  **Fields, not endpoints, answer an interval relation.**  The relation between two
  calendar terms is fixed by their bounds, so `relation` classifies it directly rather
  than routing through `startOf` / `endOf` and a constraint network — one comparison of
  two six-field vectors against a network build.  The endpoints stay answerable because
  they are what joins this to the metric layer, not because anything here needs them.

  **Both ends bound, always.**  An open variable on either side of an instant ordering or
  an interval relation would ask this to enumerate the calendar, which is not an answer
  but a process that does not come back — so `applicable?` refuses it, exactly as the
  point algebra's own prover answers nothing for a pair of open variables.  The one
  variable it binds is a `startOf` / `endOf` **result**, which is a function of the
  interval and so exactly one term."
  (:require [vaelii.impl.datetime :as dt]
            [vaelii.impl.interval :as interval]
            [vaelii.impl.point :as point]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the relation two calendar terms stand in ----------------------------

(defn relation
  "The Allen base relation between calendar terms `a` and `b`, read off their half-open
  bounds — or nil when either is not a calendar term the clock can place.

  The thirteen are jointly exhaustive and pairwise disjoint over any two intervals, so
  this is a classification and not a search: four comparisons of six-field vectors decide
  it.  Two of the thirteen never come out of it — the calendar's terms are **aligned**, so
  two of them nest, coincide, touch or are disjoint, and neither `:overlaps` nor
  `:overlapped-by` can hold between a year, a month and a day.  The arms are written
  anyway, because they are what makes the classification total rather than a case
  analysis that happens to cover its inputs."
  [a b]
  (when-let [[as ae] (dt/bounds a)]
    (when-let [[bs be] (dt/bounds b)]
      (let [ss (compare as bs)
            ee (compare ae be)]
        (cond
          (neg? (compare ae bs))  :before
          (zero? (compare ae bs)) :meets
          (pos? (compare as be))  :after
          (zero? (compare as be)) :met-by
          (zero? ss)              (cond (zero? ee) :equal
                                        (neg? ee)  :starts
                                        :else      :started-by)
          (zero? ee)              (if (neg? ss) :finished-by :finishes)
          (neg? ss)               (if (neg? ee) :overlaps :contains)
          :else                   (if (pos? ee) :overlapped-by :during))))))

(defn- instant-order
  "The point-algebra base relation between two `InstantFn` terms, or nil when either is
  not one.  Six integers against six integers, and nothing else can decide it — which is
  why a *stated* instant is never given an order here: `Breakfast`'s moment is whatever
  the KB says about it, and this prover has nothing to read."
  [a b]
  (when-let [fa (dt/instant-fields a)]
    (when-let [fb (dt/instant-fields b)]
      (let [c (compare fa fb)]
        (cond (neg? c) :before (pos? c) :after :else :equal)))))

;; ---- the three goal shapes ----------------------------------------------

(def ^:private endpoint-slot
  "`startOf` / `endOf` → which half of `datetime/bounds` answers it."
  '{startOf 0, endOf 1})

(defn- answer-slot?
  "Can `x` be the answered argument — a variable to bind, or a ground instant to check?"
  [x]
  (or (sx/variable? x) (dt/instant-term? x)))

(defn- shape
  "Which family `goal` belongs to — `:endpoint`, `:instant` or `:interval` — or nil when
  this prover cannot answer it.  One reader, so `applicable?` and `solve` cannot disagree
  about what is claimed."
  [goal]
  (when (and (sequential? goal) (= 3 (count goal)))
    (let [[pred a b] goal]
      (cond
        (and (endpoint-slot pred) (some? (dt/bounds a)) (answer-slot? b)) :endpoint
        (and (point/instant-denotation pred)
             (dt/instant-term? a) (dt/instant-term? b))                   :instant
        (and (interval/interval-denotation pred)
             (some? (dt/bounds a)) (some? (dt/bounds b)))                 :interval))))

(defn- solve-goal
  "`goal`'s solutions — at most one, since every shape is either a ground check or binds
  one variable to the one term the calendar gives it."
  [goal]
  (let [[pred a b] goal]
    (case (shape goal)
      :endpoint (let [i (dt/instant-term (nth (dt/bounds a) (endpoint-slot pred)))]
                  (if (sx/variable? b)
                    [{b i}]
                    (when (= i b) [{}])))
      :instant  (when (contains? (point/instant-denotation pred) (instant-order a b)) [{}])
      :interval (when (contains? (interval/interval-denotation pred) (relation a b)) [{}])
      nil)))

;; ---- the prover ---------------------------------------------------------

(defn- time-vocabulary-visible?
  "Is `CxTime` visible from `context`?  One cached, belief-following taxonomy read, and
  the goal's own structural test has already run when it is asked — so a KB that never
  writes a calendar term pays nothing for it.

  `(transitive instantBefore)` stands in for the file: it is `CxTime`'s declaration and
  nothing else states it, so it is believed exactly where the vocabulary these goals are
  written in can be seen.  A calendar is arithmetic and could be answered from anywhere;
  scoping it to the theory that names `startOf` is what keeps a computed answer a claim
  this KB's reader can actually see, like every other read (docs/contexts.md)."
  [kb context]
  (tax/has-prop? (reasoning/taxonomy kb) :transitive 'instantBefore context))

(defrecord CalendarProver []
  prover-types/Prover
  (applicable? [_ kb goal context]
    (and (some? (shape goal)) (time-vocabulary-visible? kb context)))
  ;; Exactly one, in every shape it claims: a check has the one empty solution or none,
  ;; and an endpoint is a function of its interval.
  (est-bindings [_ _ _ _] 1)
  ;; A bounded ground computation on at most six integers per term — no closure, no
  ;; network, no index read.
  (cost         [_ _ _ _] :lookup)
  ;; **50, and it augments rather than replaces.**  A KB may state `startOf` facts about a
  ;; calendar term, or interval relations between two of them, and the calculus provers
  ;; entail more from what it stated than the fields alone say — so the registry unions
  ;; this in cheapest-first rather than running it alone.  The converse guard is
  ;; `shadowing-channels`' `:calendar`: a term's field structure is a source no
  ;; fact-reading prover has, so nothing else runs alone on such a goal either.
  (completeness [_ _ _ _] 50)
  (solve [_ _ goal _] (solve-goal goal)))

(defn calendar-prover
  "The calendar-clock prover, to register with `vaelii.core/add-prover`."
  []
  (->CalendarProver))
