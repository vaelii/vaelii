;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.opts
  "The option-map entry point: a key nothing reads is refused, and so is an `opts` that is not
  a map.

  Nearly every public entry point that takes trailing options wants exactly this, and
  wants it for one reason: **an option nothing reads takes the default in silence.**
  That is the quietest failure the API has — `{:max-derivation 5}` for `:max-derivations`
  reads as no bound at all and the chain runs unbounded, `{:strengh :monotonic}` stores a
  default where known-true was meant, `{:varient :index}` writes a dump other than the one
  asked for.  Each returns a handle, a count, a summary that looks exactly right.

  So every such entry point runs one shape, identically bar the noun and one sentence, and this
  is that shape once.  What a caller supplies is the key set, the `subject` the
  message names, and the `consequence` — the clause saying what taking the default
  silently would have cost *here*, which is the sentence worth writing per entry point and the
  only part of the refusal that ever carried information the others did not.

  An entry point with further checks on the *values* of known keys keeps them; this is the key
  check, and it runs first because a misspelt key is not a bad value — it is a key that
  is not there."
  (:require [clojure.string :as str]))

(defn check!
  "Refuse a non-nil non-map `opts`, and any key outside `opt-keys` — `:unknown-option`
  both, carrying `:options` (the accepted keys) and, for the second, `:unknown` (what was
  passed).  `subject` names the entry point in the message; `consequence` is the clause on what
  the silent default would have done, and may be nil where the key set speaks for itself.

  `opt-keys` is a set, used as the membership predicate and sorted for the message.

  The second `map?` is redundant to a reader and required to clj-kondo, which does
  not narrow a type through a `when` whose body throws: a bare `(keys opts)` below tells
  it `opts` is seqable, and it propagates that up through every caller to
  `vaelii.core/assert`'s own signature — where the suite's deliberate `:nope` becomes a
  type error.  The guard is the narrowing, so keep it."
  ([opts opt-keys subject] (check! opts opt-keys subject nil))
  ([opts opt-keys subject consequence]
   (when (and (some? opts) (not (map? opts)))
     (throw (ex-info (str subject " options must be a map, got " (pr-str opts))
                     {:type :unknown-option :mismatch :not-a-map :options (vec (sort opt-keys))})))
   (when-let [unknown (and (map? opts)
                           (seq (sort-by pr-str (remove opt-keys (keys opts)))))]
     (throw (ex-info (str "unknown " subject " option" (when (next unknown) "s") " "
                          (str/join ", " (map pr-str unknown))
                          " — " subject " reads "
                          (str/join ", " (map pr-str (sort opt-keys)))
                          (when consequence (str ".  " consequence)))
                     {:type :unknown-option :mismatch :unknown-key :unknown (vec unknown)
                      :options (vec (sort opt-keys))})))))

(def bound-domains
  "What each numeric, callback or boolean bound a public entry point takes has to *be* —
  `[key, what it is in words, the predicate]`.  One table, read by every bounded entry
  point: `vaelii.core`'s search / chain / assert / extent checks and
  `vaelii.impl.budget/check-budget!` all run their known keys through `check-values!`
  below.

  A value outside a bound's domain is refused for the key check's reason at one remove.
  A key nothing reads is one silent default (`check!` above); a key that *is* read holding
  a value it cannot mean is the other, and quieter still where the value is not a cast
  error but a near-miss: a string `:max-ms` reaches arithmetic and throws bare, but a
  string `:believed?` reads as truthy and answers the stored extent where the believed one
  was asked for.  Either way the run happens at a setting nobody chose.

  Every numeric bound admits **0**, each a real question a caller may ask by name — no time
  at all (`:max-ms`), no rule expansion (`:max-depth`), realize nothing and hand back a
  resumable continuation (`:max-results`), report at every opportunity
  (`:progress-every-ms`) — so the domain is non-negative rather than positive, matching the
  anytime contract these bounds already keep and `vaelii.impl.spec`'s `nat-int?`.  What is
  refused is the value that is not a number of the right kind at all: a string, a float, a
  negative, a keyword where a function belongs, a string where a boolean belongs."
  [[:max-ms            "a non-negative number of milliseconds"
    #(and (number? %) (not (neg? (double %))))]
   [:max-depth         "a non-negative integer" nat-int?]
   [:max-results       "a non-negative integer" nat-int?]
   [:max-work          "a non-negative integer" nat-int?]
   [:max-derivations   "a non-negative integer" nat-int?]
   [:max-term-depth    "a non-negative integer" nat-int?]
   [:max-hypotheses    "a non-negative integer" nat-int?]
   [:node-budget       "a non-negative integer" nat-int?]
   [:max-term-growth   "a non-negative integer" nat-int?]
   [:progress-every-ms "a non-negative integer" nat-int?]
   [:commit-every-ms   "a non-negative integer" nat-int?]
   [:budget-ms         "a non-negative number of milliseconds"
    #(and (number? %) (not (neg? (double %))))]
   [:on-progress       "a function"             fn?]
   [:stop?             "a function"             fn?]
   [:on-stop           ":rollback or :keep"     #{:rollback :keep}]
   [:counters?         "true or false"          boolean?]
   [:believed?         "true or false"          boolean?]
   [:grounds?          "true or false"          boolean?]
   [:defeats?          "true or false"          boolean?]
   [:resume?           "true or false"          boolean?]
   [:retry-deferred?   "true or false"          boolean?]
   [:drop-principal?   "true or false"          boolean?]
   [:refuse-unsatisfiable? "true or false"      boolean?]
   [:refuse-depth-cut? "true or false"          boolean?]])

(def ^:private bound-domain-map
  "`bound-domains` as `{key [what pred]}`, for a per-key lookup rather than a scan of the
  whole table.  `check-values!` runs on the `assert` hot path (through
  `vaelii.core/check-assert-opts!`), where a bulk load calls it once per fact, so it reads
  the caller's `opts` — one or two keys — against this map rather than walking the table's
  twelve entries per call."
  (into {} (map (fn [[k what ok?]] [k [what ok?]])) bound-domains))

(defn check-values!
  "Refuse a bound in `opts` whose value is outside its domain (`bound-domains`), `subject`
  naming the entry point in the message as `check!` does.

  The **value** refusal beside the key one, and it runs *after* it: a misspelt key is not
  a bad value, so the key check (`check!`) is settled before any value is read, and by
  then every key present is one the entry point admits.  Reads the caller's `opts` against
  `bound-domain-map`, so a key with no row here (a `:strength`, a `:strategy`) is not this
  check's business, and a key the entry point does not read was already refused.

  An **absent** key, and an explicit `nil`, are no bound rather than a bad one — a
  legitimate request the domain does not judge, which every optional bound relies on.  When
  more than one bound is bad, the one whose key sorts first is reported, so the refusal does
  not turn on `opts`'s map order.  `:unknown-option` with `:mismatch :bad-value`, the shape
  every value refusal carries."
  [opts subject]
  (when (map? opts)
    ;; `reduce-kv` over the caller's map, not the twelve-entry table: on the `assert` hot
    ;; path `opts` is a key or two and holds no bound at all, so the common case is two map
    ;; lookups that miss and the shared empty vector back — no lazy seq allocated per call.
    (let [bad (reduce-kv (fn [acc k v]
                           (if-let [[what ok?] (bound-domain-map k)]
                             (if (and (some? v) (not (ok? v)))
                               (conj acc [k what v])
                               acc)
                             acc))
                         [] opts)]
      (when (seq bad)
        ;; a bound key is a keyword, so `sort-by first` orders by the keyword itself — a
        ;; content-stable order, not a `str` of it — and picks the same one to report
        ;; whatever order the map enumerated its keys in
        (let [[k what v] (first (sort-by first bad))]
          (throw (ex-info (str subject " " k " must be " what ", got " (pr-str v))
                          {:type :unknown-option :mismatch :bad-value :option k :value v}))))))
  opts)
