;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.calendar
  "The calendar clock: one prover answering `startOf` / `endOf` of a calendar term, an
  instant ordering between two `InstantFn` terms, and an Allen relation between two
  calendar terms or ranges from the terms' fields, or with a named interval from its stated
  `InstantFn` bounds, storing nothing.  The half-open bounds are
  `vaelii.impl.datetime/bounds`.  See docs/time.md, \"The calendar clock\"."
  (:require [vaelii.impl.datetime :as dt]
            [vaelii.impl.point :as point]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the relation two calendar terms stand in ----------------------------

(defn- relation-of
  "The Allen base relation between two half-open extents `[[as ae] [bs be]]` in one frame."
  [[[as ae] [bs be]]]
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
      :else                   (if (pos? ee) :overlapped-by :during))))

(defn relation
  "The Allen base relation between interval terms `a` and `b`, read off their half-open
  extents in one frame (`dt/paired-extents`), or nil when they have none.  Two aligned
  calendar terms never reach the `:overlaps` and `:overlapped-by` arms, and two ranges can."
  [a b]
  (some-> (dt/paired-extents a b) relation-of))

(defn- extent-in
  "`[extent handles]` of `x` in no zone: a term's own (`dt/extent`) with no handle, or for a
  named interval the believed `startOf` and `endOf` facts visible in `context` naming one
  `InstantFn` moment each (`stp/endpoints-with-support`), the start before the end, with
  their handles; else nil."
  [kb context x]
  (if-let [ext (dt/extent x)]
    [ext #{}]
    (when (sx/plain-symbol? x)
      (when-let [[[s e] hs] (stp/endpoints-with-support kb x context dt/instant-term?)]
        (let [ext [(dt/instant-fields s) (dt/instant-fields e)]]
          (when (neg? (compare (first ext) (second ext))) [ext hs]))))))

(defn- instant-order
  "The point-algebra base relation between two `InstantFn` terms, or nil when either is
  not one."
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

(def ^:private clock-predicates
  "Every predicate a goal this prover answers is on."
  (-> (set (keys endpoint-slot))
      (into (keys point/instant-denotation))
      (into (keys stp/interval-denotation))))

(defn- shape
  "Which family `goal` belongs to — `:endpoint`, `:instant`, `:interval`, `:stated` for an
  interval goal naming a named interval, `:negated` for the negation of an instant or
  interval goal, or `:open` for an instant or interval goal with a variable beside a term
  of its kind or, for an interval goal, beside a named interval, which it answers once the
  variable is bound — or nil when this prover cannot answer it.  `applicable?` and `solve`
  both read it."
  [goal]
  (if (sx/negation? goal)
    (when (#{:instant :interval} (shape (second goal))) :negated)
    (when (and (sequential? goal) (= 3 (count goal)))
      (let [[pred a b] goal]
        (cond
          (and (endpoint-slot pred) (some? (dt/bounds a)) (answer-slot? b)) :endpoint
          (and (point/instant-denotation pred)
               (dt/instant-term? a) (dt/instant-term? b))                   :instant
          (and (stp/interval-denotation pred)
               (some? (dt/paired-extents a b)))                             :interval
          (and (stp/interval-denotation pred) (or (sx/plain-symbol? a) (sx/plain-symbol? b))
               (or (sx/plain-symbol? a) (dt/extent a)) (or (sx/plain-symbol? b) (dt/extent b))) :stated
          (and (some sx/variable? [a b])
               (if (point/instant-denotation pred)
                 (some dt/instant-term? [a b])
                 (and (stp/interval-denotation pred)
                      (some #(or (sx/plain-symbol? %) (dt/extent %) (dt/utc-extent %)) [a b]))))
          :open)))))

(defn- solve-goal
  "`goal`'s solutions as `[bindings handles]`, at most one: a ground check, a negated ground
  check, which holds when the check fails, or one variable bound to the one term the
  calendar gives it.  The handles are the time vocabulary's declaration
  (`time-vocabulary-visible?`) and a named interval's stated bounds; an `:open` goal has
  none."
  [kb goal context]
  (let [[pred a b] goal
        vocab #(res/declared-by kb :transitive 'instantBefore context)]
    (case (shape goal)
      :endpoint (let [i (dt/instant-term (nth (dt/bounds a) (endpoint-slot pred)))]
                  (if (sx/variable? b)
                    [[{b i} (vocab)]]
                    (when (= i b) [[{} (vocab)]])))
      :instant  (when (contains? (point/instant-denotation pred) (instant-order a b)) [[{} (vocab)]])
      :interval (when (contains? (stp/interval-denotation pred) (relation a b)) [[{} (vocab)]])
      :stated   (when-let [[ea ha] (extent-in kb context a)]
                  (when-let [[eb hb] (extent-in kb context b)]
                    (when (contains? (stp/interval-denotation pred) (relation-of [ea eb]))
                      [[{} (-> (vocab) (into ha) (into hb))]])))
      :negated  (when (empty? (solve-goal kb (second goal) context)) [[{} (vocab)]])
      nil)))

;; ---- the prover ---------------------------------------------------------

(defn- time-vocabulary-visible?
  "Is `(transitive instantBefore)`, which only `time.txt` states, believed in `context`?
  That declaration stands in for the time vocabulary (docs/time.md, \"Scoping\")."
  [kb context]
  (tax/has-prop? (reasoning/taxonomy kb) :transitive 'instantBefore context))

(defrecord CalendarProver []
  prover-types/Prover
  (applicable? [_ kb goal context]
    (and (some? (shape goal)) (time-vocabulary-visible? kb context)))
  ;; the three figures: docs/time.md, "Cost, and what it claims"
  (est-bindings [_ _ goal _] (if (= :open (shape goal)) provers/deferred-est 1))
  (cost         [_ _ _ _] :lookup)
  (completeness [_ _ _ _] 50)
  (solve [_ kb goal context] (map first (solve-goal kb goal context)))
  prover-types/SupportingProver
  (support-functors [_] clock-predicates)
  (support-sources [_] (conj stp/endpoint-predicates 'transitive))
  (solve-with-support [_ kb goal context] (solve-goal kb goal context)))

(defn calendar-prover
  "The calendar-clock prover, to register with `vaelii.core/add-prover`."
  []
  (->CalendarProver))
