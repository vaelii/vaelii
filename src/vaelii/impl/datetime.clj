;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.datetime
  "Reads the time terms — a `DatetimeFn` reduced-precision ISO string, the calendar
  constructors `YearFn` / `MonthFn` / `DayFn`, a `DatetimeRangeFn` range and the
  `InstantFn` moment — to integer field vectors.  Field nesting is calendar containment
  (`subinterval?`, docs/context-nat.md); `bounds` is the half-open `[start end)` the
  calendar clock reads, `extent` adds a range's, and `utc-extent` reads a time with a UTC
  offset or a `ZonedDatetimeFn` zone (docs/time.md).  Every reader is pure and total,
  returning nil rather than throwing, because the structural genlCx producer calls it
  inside the settle/relabel loop."
  (:require [clojure.string :as str])
  (:import (java.time DateTimeException Instant LocalDateTime ZoneId ZoneOffset)
           (java.time.zone ZoneRules)))

(def datetime-function
  "The structural ISO constructor this namespace reads."
  'DatetimeFn)

(def calendar-functions
  "The structural calendar constructors, `functor → field count`, one integer per field,
  coarsest first: `(YearFn 2000)`, `(MonthFn 2000 1)`, `(DayFn 2000 1 15)`."
  '{YearFn 1, MonthFn 2, DayFn 3})

(def ^:private field-ranges
  "The inclusive bounds of each field after the year, in field order: month, day, hour,
  minute, second.  Day is bounded at 31 whatever the month; `at` checks the calendar."
  [[1 12] [1 31] [0 23] [0 59] [0 59]])

(def ^:private year-pattern
  "A year is one to four digits, zero-padding optional.  The width refuses the basic ISO
  format, which would read `\"20260821\"` as the year 20,260,821, and keeps the read
  inside a `Long`."
  #"\d{1,4}")

(def ^:private field-pattern
  "Every field after the year is one or two digits, so `\"2000-1\"` and `\"2000-01\"` are
  one month, `\"2000-001\"` is nothing, and the read stays inside a `Long`."
  #"\d{1,2}")

(defn- parse
  "The ISO string as a vector of integer fields `[year month day hour minute second]`,
  truncated at the string's own precision, or nil when it is not well formed: one to three
  `-`-separated date fields, then optionally `T` and one to three `:`-separated time
  fields behind a full date, each field of its own width and in range.  Each half is
  bounded on its own, so `\"2000T13:00\"` and `\"2000-01-15-12\"` are refused."
  [s]
  (when (string? s)
    (let [[date time] (str/split s #"T" 2)
          date-parts (str/split date #"-" -1)
          time-parts (when time (str/split time #":" -1))
          parts      (concat date-parts time-parts)]
      (when (and (<= 1 (count date-parts) 3)
                 (or (nil? time)
                     (and (= 3 (count date-parts)) (<= 1 (count time-parts) 3)))
                 (re-matches year-pattern (first parts))
                 (every? #(re-matches field-pattern %) (rest parts)))
        (let [fields (mapv #(Long/parseLong ^String %) parts)]
          (when (every? (fn [[v [lo hi]]] (<= lo v hi))
                        (map vector (rest fields) field-ranges))
            fields))))))

(def ^:private year-range
  "The inclusive bounds of a numeric year: the range `year-pattern`'s width denotes, so a
  calendar constructor and an ISO string admit the same years."
  [0 9999])

(defn- fields-in-range?
  "Are numeric `fields` well formed — every one an integer, the year inside `year-range`
  and every later field inside its own?  Both numeric readers run this test."
  [fields]
  (and (every? integer? fields)
       (<= (first year-range) (long (first fields)) (second year-range))
       (every? (fn [[v [lo hi]]] (<= lo (long v) hi))
               (map vector (rest fields) field-ranges))))

(defn- calendar-fields
  "The fields of a calendar term `(YearFn Y)` / `(MonthFn Y M)` / `(DayFn Y M D)` of its
  functor's arity with every field in range, or nil."
  [form]
  (when (sequential? form)
    (when-let [n (get calendar-functions (first form))]
      (let [args (vec (rest form))]
        (when (and (= n (count args)) (fields-in-range? args))
          (mapv long args))))))

(defn- term-fields
  "The fields of a time term — a `(DatetimeFn \"<iso>\")` or one of the calendar
  constructors — or nil for anything that is neither.  Both spellings read to one field
  vector."
  [form]
  (when (sequential? form)
    (if (= datetime-function (first form))
      (when (= 2 (count form)) (parse (second form)))
      (calendar-fields form))))

(defn datetime-term?
  "True iff `form` is a `(DatetimeFn \"<iso>\")` term with a parseable ISO string."
  [form]
  (and (sequential? form) (= datetime-function (first form)) (some? (term-fields form))))

(defn calendar-term?
  "True iff `form` is a well-formed calendar term — `(YearFn 2000)`, `(MonthFn 2000 1)` or
  `(DayFn 2000 1 15)`."
  [form]
  (some? (calendar-fields form)))

;; ---- the moments a calendar term lies between ----------------------------

(def instant-function
  "The structural constructor for a moment, six integer fields always:
  `(InstantFn 2000 1 1 0 0 0)` is midnight at the start of 2000."
  'InstantFn)

(def ^:private instant-field-count 6)

(def ^:private field-defaults
  "Each field after the year at the first moment of a coarser term: month and day 1, the
  clock fields 0."
  [1 1 0 0 0])

(defn- at
  "The `LocalDateTime` six fields name, or nil when the calendar has no such moment."
  ^LocalDateTime [[y mo d h mi s]]
  (try (LocalDateTime/of (int y) (int mo) (int d) (int h) (int mi) (int s))
       (catch DateTimeException _ nil)))

(defn- from
  "A `LocalDateTime` back as a six-field vector."
  [^LocalDateTime t]
  [(long (.getYear t)) (long (.getMonthValue t)) (long (.getDayOfMonth t))
   (long (.getHour t)) (long (.getMinute t)) (long (.getSecond t))])

(defn- one-later
  "The moment one unit of `n`-field precision after `t` — the next year, month, day, hour,
  minute or second — or nil when it falls outside `year-range`.  `java.time` supplies
  month lengths and leap years."
  [^LocalDateTime t n]
  (let [^LocalDateTime u (case (long n)
                           1 (.plusYears t 1)
                           2 (.plusMonths t 1)
                           3 (.plusDays t 1)
                           4 (.plusHours t 1)
                           5 (.plusMinutes t 1)
                           (.plusSeconds t 1))
        v (from u)]
    (when (<= (first year-range) (long (first v)) (second year-range)) v)))

(defn epoch-second
  "The seconds from 1970-01-01T00:00:00 to the moment six fields name, both read on one
  clock, or nil when the calendar has no such moment."
  [fields]
  (when-let [^LocalDateTime t (at fields)] (.toEpochSecond t ZoneOffset/UTC)))

(defn instant-fields
  "The six fields of an `(InstantFn Y M D h m s)` term, or nil for anything that is not
  one — a term of the wrong arity, a field out of range, or a date the calendar does not
  have."
  [form]
  (when (sequential? form)
    (when (= instant-function (first form))
      (let [args (vec (rest form))]
        (when (and (= instant-field-count (count args))
                   (fields-in-range? args)
                   (some? (at args)))
          (mapv long args))))))

(defn instant-term
  "The `(InstantFn …)` term six fields name, a `PersistentList` as `sentex/canon`
  normalizes a typed one to."
  [fields]
  (apply list instant-function fields))

(defn instant-term?
  "True iff `form` is a well-formed `(InstantFn …)` term."
  [form]
  (some? (instant-fields form)))

(defn- fields-bounds
  "The half-open `[start end)` of the wall-clock interval `fields` name, or nil."
  [fields]
  (let [n     (count fields)
        start (into fields (subvec field-defaults (dec n)))]
    (when-let [^LocalDateTime t (at start)]
      (when-let [end (one-later t n)]
        [start end]))))

(defn bounds
  "The half-open `[start end)` a calendar term lies between, each a six-field vector: the
  end is the first moment of the next term at the same precision.  Nil for a term that is
  not a calendar one or names no moment."
  [form]
  (some-> (term-fields form) fields-bounds))

;; ---- absolute time: a UTC offset or a named zone ---------------------------

(def zoned-function
  "The structural constructor of a wall-clock time in a named zone: `(ZonedDatetimeFn
  \"2000-03-26T00:30\" \"Europe/London\")`."
  'ZonedDatetimeFn)

(def ^:private offset-pattern
  "An ISO string with a time and a UTC offset: the local part, then `Z` or `±hh:mm`."
  #"(.+T.+?)(Z|([+-])(\d{2}):(\d{2}))")

(defn- offset-fields
  "`[fields offset-seconds]` of an ISO string carrying a UTC offset, the offset at most
  18 hours, or nil."
  [s]
  (when (string? s)
    (when-let [[_ local z sign hh mm] (re-matches offset-pattern s)]
      (when-let [fields (parse local)]
        (if (= "Z" z)
          [fields 0]
          (let [h (Long/parseLong hh) m (Long/parseLong mm)]
            (when (and (<= h 18) (< m 60))
              [fields (* (if (= "-" sign) -1 1) (+ (* 3600 h) (* 60 m)))])))))))

(defn- to-utc
  "The six fields `v`, a wall-clock moment at `offset-seconds`, as UTC fields, or nil."
  [v offset-seconds]
  (when-let [^LocalDateTime t (at v)]
    (let [u (from (.minusSeconds t (long offset-seconds)))]
      (when (<= (first year-range) (long (first u)) (second year-range)) u))))

(defn- utc-fields
  "The UTC six fields of `instant`, or nil outside `year-range`."
  [^Instant instant]
  (let [u (from (LocalDateTime/ofInstant instant ZoneOffset/UTC))]
    (when (<= (first year-range) (long (first u)) (second year-range)) u)))

(defn- zoned-bounds
  "The UTC half-open bounds of the wall-clock span `[s e)` in the zone named `zone`, from
  the first instant the zone's clock reads inside it to the end of the last: a start in a
  daylight-saving gap is the transition, a repeated start its first occurrence and a
  repeated last second its second.  Nil when the span lies inside one gap or one repeated
  hour, or the zone database holds no `zone`."
  [zone s e]
  (when-let [ls (at s)]
    (when-let [le (at e)]
      (try
        (let [^ZoneRules rules (.getRules (ZoneId/of ^String zone))
              ll   (.minusSeconds le 1)
              ts   (.getTransition rules ls)
              tl   (.getTransition rules ll)
              one  (fn [^LocalDateTime t] (.toInstant t (.getOffset rules t)))
              ^LocalDateTime upto (when ts (if (.isGap ts) (.getDateTimeAfter ts) (.getDateTimeBefore ts)))]
          (when-not (and upto (not (.isAfter le upto)))
            (when-let [s' (utc-fields (cond (nil? ts) (one ls)
                                            (.isGap ts) (.getInstant ts)
                                            :else (.toInstant ls (.getOffsetBefore ts))))]
              (when-let [e' (utc-fields (cond (nil? tl) (.plusSeconds ^Instant (one ll) 1)
                                              (.isGap tl) (.getInstant tl)
                                              :else (.plusSeconds (.toInstant ll (.getOffsetAfter tl)) 1)))]
                [s' e']))))
        (catch DateTimeException _ nil)))))

(defn- utc-bounds
  "The UTC half-open bounds of a `DatetimeFn` term with a UTC offset, or of a
  `ZonedDatetimeFn` term (`zoned-bounds`), or nil."
  [form]
  (when (sequential? form)
    (condp = (first form)
      datetime-function
      (when (= 2 (count form))
        (when-let [[fields off] (offset-fields (second form))]
          (when-let [[s e] (fields-bounds fields)]
            (when-let [s' (to-utc s off)] (when-let [e' (to-utc e off)] [s' e'])))))
      zoned-function
      (when (and (= 3 (count form)) (string? (nth form 2)))
        (when-let [[s e] (some-> (parse (second form)) fields-bounds)]
          (zoned-bounds (nth form 2) s e)))
      nil)))

(def range-function
  "The structural constructor of a range, two ISO strings: `(DatetimeRangeFn \"2000-01\"
  \"2000-06\")` begins when its first string's interval begins and ends when its second's
  ends."
  'DatetimeRangeFn)

(defn- extent-by
  "`read`'s bounds of `form`, or a `DatetimeRangeFn` range's from the start of its first
  string's to the end of its second's, nil for a range that ends at or before it begins."
  [read form]
  (if (and (sequential? form) (= range-function (first form)))
    (when (= 3 (count form))
      (let [[_ from to] form]
        (when-let [[start _] (read (list datetime-function from))]
          (when-let [[_ end] (read (list datetime-function to))]
            (when (neg? (compare start end)) [start end])))))
    (read form)))

(defn extent
  "The half-open wall-clock `[start end)` a time interval term in no zone lies between: a
  calendar term's `bounds`, or a `DatetimeRangeFn` range's.  Nil for any other term."
  [form]
  (extent-by bounds form))

(defn utc-extent
  "The half-open UTC `[start end)` of a term with a UTC offset or a named zone, a range of
  two such strings included; nil for a term in no zone."
  [form]
  (extent-by utc-bounds form))

(defn paired-extents
  "`[extent-a extent-b]` read in one frame, both in no zone or both absolute, or nil: a
  wall-clock time in no zone and an absolute one have no order."
  [a b]
  (or (when-let [ea (extent a)] (some->> (extent b) (vector ea)))
      (when-let [ea (utc-extent a)] (some->> (utc-extent b) (vector ea)))))

(defn within?
  "True iff the half-open extent `[as ae)` lies inside `[bs be)`, each bound a six-field
  vector."
  [[as ae] [bs be]]
  (and (<= (compare bs as) 0) (<= (compare ae be) 0)))

(defn at-or-inside?
  "True iff the moment `t`, six fields, lies in the half-open extent `[bs be)`."
  [t [bs be]]
  (and (<= (compare bs t) 0) (neg? (compare t be))))

(defn subinterval?
  "True iff time term `a` denotes an interval contained in `b`'s (reflexive): for two
  calendar or ISO terms in no zone, `b`'s fields are a prefix of `a`'s; else `a`'s extent
  lies inside `b`'s in one frame (`paired-extents`).  `false` for anything else."
  [a b]
  (boolean
   (let [pa (term-fields a) pb (term-fields b)]
     (if (and pa pb)
       (and (<= (count pb) (count pa))
            (= pb (subvec pa 0 (count pb))))
       (when-let [[ea eb] (paired-extents a b)] (within? ea eb))))))

(defn disjoint?
  "True iff the calendar shows the time terms `a` and `b` share no time: two moments with
  different fields, a moment outside an interval term's extent, or two extents in one
  frame (`paired-extents`) that do not overlap.  `false` for anything else, a named time
  included."
  [a b]
  (boolean
   (let [ta (instant-fields a)
         tb (instant-fields b)]
     (cond
       (and ta tb) (not= ta tb)
       ta          (some->> (extent b) (at-or-inside? ta) not)
       tb          (some->> (extent a) (at-or-inside? tb) not)
       :else       (when-let [[[as ae] [bs be]] (paired-extents a b)]
                     (or (<= (compare ae bs) 0) (<= (compare be as) 0)))))))

(defn instant-within?
  "True iff `a` is an `InstantFn` moment at or inside the interval term `b`'s extent, or
  the same moment as the `InstantFn` term `b`.  `false` otherwise, two intervals
  included: those are `subinterval?`'s."
  [a b]
  (boolean
   (when-let [t (instant-fields a)]
     (if-let [e (extent b)]
       (at-or-inside? t e)
       (= t (instant-fields b))))))

(defn- spellings
  "Every ISO string `parse` returns the fields `fs` for: each field zero-padded to every
  width its pattern admits."
  [fs]
  (let [pad (fn [v w] (let [s (str v)] (when (<= (count s) w) (str (str/join (repeat (- w (count s)) \0)) s))))
        iso (fn [ps] (let [[d t] (split-at 3 ps)] (cond-> (str/join "-" d) (seq t) (str "T" (str/join ":" t)))))]
    (map iso (reduce (fn [acc opts] (for [a acc o opts] (conj a o)))
                     [[]] (map-indexed (fn [i v] (keep #(pad v %) (if (zero? i) [1 2 3 4] [1 2]))) fs)))))

(defn containing-terms
  "The terms in no zone that `subinterval?` or `instant-within?` can answer contain the
  time `t` in no zone, `t` among them and a `DatetimeRangeFn` range excepted: for each
  prefix of a calendar term's own fields, or of the start of an `InstantFn` moment or a
  range, the `DatetimeFn` term in every spelling (`spellings`) and the calendar term of
  as many fields.  Nil for any other term."
  [t]
  (when-let [fs (or (term-fields t) (instant-fields t)
                    (when (and (sequential? t) (= range-function (first t))) (first (extent t))))]
    (into #{t}
          (mapcat (fn [k]
                    (let [p (subvec fs 0 k)]
                      (concat (map #(list datetime-function %) (spellings p))
                              (for [[f n] calendar-functions :when (= n k)] (apply list f p))))))
          (range 1 (inc (count fs))))))

;; ---- one spelling per time --------------------------------------------------

(def ^:private calendar-constructors
  "`field count → functor`, the inverse of `calendar-functions`."
  (into {} (map (fn [[f n]] [n f])) calendar-functions))

(def ^:private endpoint-functions
  "The moment functions `calendar-spelling` reads off an extent: which half of it each names."
  '{StartFn 0, EndFn 1})

(defn- iso
  "The ISO string of `fields`, the year four digits wide and every later field two."
  [fields]
  (let [[d t] (split-at 3 (map-indexed #(format (if (zero? %1) "%04d" "%02d") %2) fields))]
    (cond-> (str/join "-" d) (seq t) (str "T" (str/join ":" t)))))

(defn- coarsest-unit
  "The fields of the coarsest calendar unit holding the moment `t` whose bounds satisfy
  `ok?`, or nil."
  [t ok?]
  (some #(let [fs (subvec t 0 %)] (when (some-> (fields-bounds fs) ok?) fs))
        (range 1 (inc instant-field-count))))

(defn- extent-spelling
  "The one term of the extent `[s e)`: the calendar term or the zero-padded `DatetimeFn`
  term of the one unit with those bounds, else the `DatetimeRangeFn` range from the
  coarsest unit starting at `s` to the coarsest unit ending at `e`."
  [[s e :as ext]]
  (if-let [fs (coarsest-unit s #(= ext %))]
    (if-let [f (calendar-constructors (count fs))]
      (apply list f fs)
      (list datetime-function (iso fs)))
    (let [last-second (from (.minusSeconds ^LocalDateTime (at e) 1))]
      (list range-function
            (iso (coarsest-unit s (fn [[bs be]] (and (= s bs) (<= (compare be e) 0)))))
            (iso (coarsest-unit last-second (fn [[bs be]] (and (= e be) (<= (compare s bs) 0)))))))))

(defn calendar-spelling
  "`t` with each time term in no zone inside it, innermost first, in the one spelling read
  off its extent: an `InstantFn` moment, and `(StartFn T)` / `(EndFn T)` of a term `T` with
  an `extent`, as the `InstantFn` term; any other term with an `extent` as
  `extent-spelling` gives it.  A time with a UTC offset or a zone, a named time and any
  other term keep their spelling (docs/context-nat.md, \"Two spellings of one calendar time
  name one context\")."
  [t]
  (if-not (and (sequential? t) (seq t))
    t
    (let [t (apply list (map calendar-spelling t))]
      (if-let [fs (instant-fields t)]
        (instant-term fs)
        (or (when-let [half (and (= 2 (count t)) (endpoint-functions (first t)))]
              (some-> (extent (second t)) (nth half) instant-term))
            (some-> (extent t) extent-spelling)
            t)))))

(def order-comparators
  "The registered pure comparators of an order, `{relation → (fn [a b] a-below-b?)}`.
  Each reads two terms' shape with no store read and no proof, and is total, returning
  `false` for terms it does not apply to.  `subtimeOf`'s answers the pairs whose lower
  term is a moment and leaves two intervals to `subintervalOf`'s.  `context-nat` reads one
  to order two context NATs, and the canonicalizer reads one to absorb a meet's argument
  (`res/meet-order`)."
  {'subintervalOf subinterval?
   'subtimeOf     instant-within?})

(defn time-term?
  "True iff `form` is any term this namespace reads — a calendar constructor, a
  `DatetimeFn` string, a `DatetimeRangeFn` range, or an `InstantFn` moment.  The test
  behind `provers/shadowing-channels`' `:calendar`."
  [form]
  (and (sequential? form)
       (boolean (or (some? (term-fields form)) (instant-term? form) (some? (extent form))
                    (some? (utc-extent form))))))

(def ^:private time-functions
  "The functors of the terms `time-term?` can hold of."
  (into #{datetime-function range-function instant-function zoned-function}
        (keys calendar-functions)))

(defn moments
  "The `[frame fields]` of each point the calendar places of the time term `t`, in
  `timepoint/moment`'s frames: an `InstantFn` moment's own, else the start and end of the
  term's extent, `:local` in no zone and `:utc` with an offset or a zone.  Empty for any
  other term."
  [t]
  (if-let [f (instant-fields t)]
    [[:local f]]
    (or (some->> (extent t) (mapv #(vector :local %)))
        (some->> (utc-extent t) (mapv #(vector :utc %)))
        [])))

(defn month-buckets
  "The `[frame year month]` of each point (`moments`) of each time term in `form`, as a
  set: the months of the calendar index's nodes (`kv/index-families`' `:calendar`) a stored
  fact enters under its functor."
  [form]
  (into #{} (comp (filter #(and (sequential? %) (contains? time-functions (first %))))
                  (mapcat moments)
                  (map (fn [[frame fs]] [frame (nth fs 0) (nth fs 1)])))
        (tree-seq sequential? seq form)))
