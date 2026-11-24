;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.edge
  "`edge-solver`, the ASP implementation of `vaelii.impl.types.solve/Solver`.  `translate`
  renders a `Program` to ASPIF, and the readers read a backend's answer set back:
  `interpret` for `edge-solver`, `kept-of`, `enumerate-optima` and `classify-program` for
  the imperatives.  A reader runs only on an answer (`answered?`); the imperative readers
  refuse any other result with `:solver-failed`.  The encoding, the objective levels,
  determinism and the no-answer policy: docs/asp.md."
  (:require
   [taoensso.trove :as trove]
   [vaelii.impl.asp.aspif :as aspif]
   [vaelii.impl.asp.atoms :as atoms]
   [vaelii.impl.asp.solver :as solver]
   [vaelii.impl.naming :as nm]
   [vaelii.impl.solve :as solve]
   [vaelii.impl.types.solve :as solve-types]))

;; Objective levels.  Violations sit above both, at 2 + the rank of the caller's
;; priority; these two are the fixed floor.
(def ^:private level-defeat-count 1)
(def ^:private level-tiebreak 0)

(defn- descriptor
  "The contradiction descriptor `atoms/intern-contradiction!` interns: a
  sentence-shaped value carrying the involved handles, so a witness atom can be
  read back without a secondary lookup."
  [{:keys [nogood sentence]}]
  (list 'contradiction sentence :involved (mapv (fn [h] [:sentex h]) (sort nogood))))

(defn- card-descriptor
  "The violation descriptor for a soft cardinality entry — the same shape
  `descriptor` gives a soft nogood, tagged `cardinality` and carrying every member."
  [{:keys [op k members sentence]}]
  (list 'cardinality (or sentence (list op k)) :involved (mapv (fn [h] [:sentex h]) (sort members))))

(defn- card-encoding
  "The weight body a cardinality entry over `weighted` (`[atom weight]` pairs sorted by
  atom, every weight positive) becomes, or a keyword for the two degenerate cases.
  Returns

      [lower-bound weighted-literals]   a weight body of that bound
      :vacuous                          every model meets the bound — emit nothing
      :infeasible                       no model meets the bound — a model is impossible

  With `n` the total weight: at-most-`k` forbids the sum reaching `k+1`, over the positive
  literals; `k >= n` cannot be reached, so it is vacuous.  at-least-`k` forbids the absent
  members' weight reaching `n-k+1`, over the default-negated literals; `k <= 0` is met by
  every model, `k > n` (or an empty member set with `k >= 1`) by none.  An unweighted
  bound is the case of every weight 1."
  [op k weighted]
  (let [n (reduce + 0 (map second weighted))]
    (case op
      :at-most  (if (>= k n) :vacuous
                    [(inc k) (vec weighted)])
      :at-least (cond (<= k 0) :vacuous
                      (> k n)  :infeasible
                      :else    [(- (inc n) k) (mapv (fn [[a w]] [(- a) w]) weighted)]))))

(defn translate
  "Render `program` to ASPIF.  Returns

      {:aspif      text or nil          ; nil when there is nothing to solve
       :stmts      [statement ...]      ; the structured program the clingo backend injects
       :table      the atom table
       :by-label   {label nogood}       ; violation atom -> the contradiction
       :assumptions [handle ...]        ; in content-key order
       :doomed     [nogood ...]}        ; all-fixed, unsatisfiable without solving

  `:tiebreak?` (default true) emits the level-0 content-keyed objective, which makes the
  optimum unique; an enumeration turns it off (docs/asp.md, \"Two things keep `classify`
  from reporting a tie as forced\").  `:keep-belief?` (default true) emits the level-1
  objective minimizing defeated assumptions; `do/label :sat` turns it off.  `:project`, a set
  of handles, emits a projection statement over their atoms, empty for an empty set."
  ([program] (translate program {}))
  ([{:keys [assumptions contradictions derived derivations] :as program}
    {:keys [tiebreak? keep-belief? project] :or {tiebreak? true keep-belief? true}}]
   (let [ordered   (nm/sort-by-content-key #(solve/content-key program %) compare assumptions)
         ;; a solve's derived atoms, allocated after the choices in the same content order
         ordered-d (nm/sort-by-content-key #(solve/content-key program %) compare derived)
         ;; the nogoods and cardinality entries in content order, since every emission
         ;; below walks them; each key is a vector built once per entry, not per comparison
         contradictions (let [ck #(solve/content-key program %)]
                          (->> contradictions
                               (map (fn [ng]
                                      [[(vec (sort (map ck (concat (:nogood ng) (:neg ng)))))
                                        (:priority ng)
                                        (boolean (:hard ng))]
                                       ng]))
                               (sort-by first)
                               (mapv second)))
         cardinalities (let [ck #(solve/content-key program %)]
                         (->> (:cardinalities program)
                              (map (fn [c]
                                     [[(vec (sort (map ck (:members c))))
                                       (name (:op c)) (:k c)
                                       (boolean (:hard c)) (:priority c 1)
                                       (vec (sort (map (fn [[m w]] [(ck m) w]) (:weights c))))]
                                      c]))
                              (sort-by first)
                              (mapv second)))
         n         (count ordered)
         table     (atoms/new-table)
         atom-of   (into {} (map (fn [h] [h (atoms/intern-sentex! table h)]))
                         (concat ordered ordered-d))
         ;; a nogood member is an atom when it is a choice or a derived atom; any other is
         ;; fixed background (a nogood's known-true members)
         atom?     (fn [h] (contains? atom-of h))
         ;; a body sorted by atom id, which is content order; `neg` members render
         ;; default-negated
         pos       (fn [ng] (sort-by atom-of (filter atom? (:nogood ng))))
         neg       (fn [ng] (sort-by atom-of (filter atom? (:neg ng))))
         involved  (fn [ng] (concat (pos ng) (neg ng)))
         ;; a fixed `:neg` member is assumed true, so the body never holds; dropping only
         ;; the member would tighten the nogood
         vacuous?  (fn [ng] (not-every? atom? (:neg ng)))
         grounded  (remove vacuous? contradictions)
         doomed    (filterv (comp empty? involved) grounded)
         live      (remove (comp empty? involved) grounded)
         hard-live (filter :hard live)
         soft-live (remove :hard live)
         card-specs (into []
                          (keep (fn [c]
                                  (let [weighted (->> (:members c)
                                                      (keep (fn [m]
                                                              (when-let [a (atom-of m)]
                                                                [a (get (:weights c) m 1)])))
                                                      (filter (comp pos? second))
                                                      (sort-by first))
                                        enc (card-encoding (:op c) (:k c) weighted)]
                                    (when-not (= :vacuous enc) (assoc c :enc enc)))))
                          cardinalities)
         hard-cards (filter :hard card-specs)
         soft-cards (remove :hard card-specs)
         ;; caller priorities become levels by ascending rank, clear of 0 and 1
         levels    (into {} (map-indexed (fn [i p] [p (+ 2 i)]))
                         (sort (distinct (concat (map :priority soft-live)
                                                 (map #(:priority % 1) soft-cards)))))
         v-atoms   (mapv (fn [ng] [ng (atoms/intern-contradiction! table (descriptor ng))]) soft-live)
         card-v    (mapv (fn [c] [c (atoms/intern-contradiction! table (card-descriptor c))]) soft-cards)
         stmts     (concat
                    ;; believed-or-defeated
                    (map (fn [h] (aspif/choice (atom-of h))) ordered)
                    ;; a solve's normal rules, sorted
                    (->> derivations
                         (map (fn [{:keys [head pos neg]}]
                                [(atom-of head)
                                 (vec (concat (sort (map atom-of pos))
                                              (map - (sort (map atom-of neg)))))]))
                         sort
                         (map (fn [[h body]] (if (seq body) (aspif/rule h body) (aspif/fact h)))))
                    ;; a hard nogood with no atom left holds in every model
                    (when (some :hard doomed) [(aspif/constraint [])])
                    ;; hard: forbid any model in which the whole (signed) body holds
                    (map (fn [ng] (aspif/constraint
                                   (concat (mapv atom-of (pos ng))
                                           (mapv #(- (atom-of %)) (neg ng)))))
                         hard-live)
                    ;; soft: v :- the whole signed body, the body the hard branch forbids
                    (mapcat (fn [[ng v]]
                              [(aspif/rule v (concat (mapv atom-of (pos ng))
                                                     (mapv #(- (atom-of %)) (neg ng))))
                               (aspif/minimize (levels (:priority ng)) [[v (:weight ng 1)]])])
                            v-atoms)
                    ;; hard cardinality: one weight-body integrity constraint per group, an
                    ;; empty one when `:infeasible`
                    (map (fn [{:keys [enc]}]
                           (if (= :infeasible enc)
                             (aspif/constraint [])
                             (aspif/weight-constraint (first enc) (second enc))))
                         hard-cards)
                    ;; soft cardinality: a violation atom, a fact when `:infeasible`
                    (mapcat (fn [[{:keys [enc priority]} v]]
                              [(if (= :infeasible enc)
                                 (aspif/fact v)
                                 (aspif/weight-rule v (first enc) (second enc)))
                               (aspif/minimize (levels (or priority 1)) [[v 1]])])
                            card-v)
                    ;; level 1: a defeated assumption is a false atom
                    (when (and keep-belief? (seq ordered))
                      [(aspif/minimize level-defeat-count
                                       (mapv (fn [h] [(- (atom-of h)) 1]) ordered))])
                    ;; level 0: cheapest to defeat is the greatest content-key
                    (when (and tiebreak? (seq ordered))
                      [(aspif/minimize level-tiebreak
                                       (map-indexed (fn [i h] [(- (atom-of h)) (- n i)]) ordered))])
                    (when (some? project) [(aspif/project (sort (keep atom-of project)))])
                    (map (fn [h] (aspif/show (atom-of h) (atoms/label-of-atom table (atom-of h))))
                         (concat ordered ordered-d))
                    (map (fn [[_ v]] (aspif/show v (atoms/label-of-atom table v))) v-atoms)
                    (map (fn [[_ v]] (aspif/show v (atoms/label-of-atom table v))) card-v))]
     {:aspif       (when (seq stmts) (aspif/render stmts))
      :stmts       stmts
      :table       table
      :by-label    (into {} (map (fn [[ng v]] [(atoms/label-of-atom table v) ng]))
                         (concat v-atoms card-v))
      :assumptions ordered
      :derived     ordered-d
      :doomed      doomed})))

(defn- answered?
  "Is `result` an answer set: `:optimum` or `:sat`?  Each reader handles `:unsat` on its
  own terms."
  [result]
  (contains? #{:optimum :sat} (:status result)))

(defn- unanswered-ex
  "The `:solver-failed` exception for a result that is not an answer, naming the mode
  and the status, as a value `edge-solver` returns in `:error`."
  [mode result]
  (ex-info (str "the ASP backend returned no answer for a " (name mode)
                " solve: " (name (:status result :unknown))
                (when (= :interrupted (:status result))
                  (str " (the solve limit, VAELII_ASP_SOLVE_LIMIT; the time limit,"
                       " VAELII_ASP_TIME_LIMIT; or a signal)")))
           {:type :solver-failed :mode mode :status (:status result)}))

(defn- unanswered!
  "Refuse a result that is not an answer, naming the mode and the status."
  [mode result]
  (throw (unanswered-ex mode result)))

(defn- backend-failed-ex
  "`e`, whatever the backend threw, as one exception: `:type :solver-failed` unless
  `e`'s own `ex-data` names a type, which wins, and `e` as the cause (docs/asp.md, \"A
  backend that throws\")."
  [^Throwable e]
  (ex-info (str "the ASP backend failed: " (or (ex-message e) (.getName (class e))))
           (merge {:type :solver-failed} (ex-data e))
           e))

(defn- interpret
  "Read an answered `result` back into the `Solver` contract.  `:violated` is ordered
  highest caller priority first, then by sentence.  `translate`'s nogood key omits
  `:sentence`, so the order is set here, over the violated nogoods alone."
  [{:keys [table by-label assumptions doomed]} result]
  (let [true-labels (set (:atoms result))
        defeated    (into #{} (remove #(true-labels (atoms/label-of-atom table (atoms/atom-of-sentex table %))))
                          assumptions)
        violated    (into (vec doomed)
                          (keep by-label)
                          (sort true-labels))]
    {:defeat defeated
     :violated (nm/sort-by-content-key
                (fn [ng] [(- (long (or (:priority ng) 0))) (:sentence ng)])
                nm/compare-form violated)}))

(defn kept-of
  "The chosen-true assumption handles and the true derived atoms of one `:label` result,
  read through translation `t`'s atom table; `do/label :one` and `:sat` read a labeling
  with it.  An `:unsat` result keeps `#{}`, a `:best-effort` one is read as an answer, and
  an `:interrupted` or `:unknown` one is refused (`:solver-failed`)."
  [{:keys [table assumptions derived]} result]
  (when-not (or (answered? result) (contains? #{:unsat :best-effort} (:status result)))
    (unanswered! :label result))
  (let [true-labels (set (:atoms result))]
    (into #{} (filter #(true-labels (atoms/label-of-atom table (atoms/atom-of-sentex table %))))
          (concat assumptions derived))))

(defn handles-of
  "The assumption handles behind `labels` — a solver's answer set, as label strings."
  [table labels]
  (into #{} (keep #(some->> (atoms/atom-of-label table %)
                            (atoms/sentex-id-of-atom table)))
        labels))

(defn classify-program
  "Classify `program`'s assumptions into `:true` / `:supportable` / `:false` by
  brave/cautious reasoning over its optimal answer sets — in every optimum, in some,
  in none.

  `:fixed` handles are `:true`.  With no ASP backend every contested assumption is
  `:supportable`.  An enumeration the backend did not finish is refused (`:solver-failed`).
  `asp.label` re-exports it."
  [{:keys [assumptions fixed] :as program}]
  (let [base {:true (set fixed) :supportable #{} :false #{}}]
    (cond
      (empty? assumptions) base
      (not (solver/available?)) (assoc base :supportable (set assumptions))
      :else
      (let [{:keys [aspif table]} (translate program {:tiebreak? false})
            {:keys [cautious brave]} (solver/classify-both aspif)
            _        (doseq [[mode r] [[:classify-true cautious] [:classify-supportable brave]]]
                       (when-not (or (answered? r) (= :unsat (:status r)))
                         (unanswered! mode r)))
            in-every (handles-of table (:atoms cautious))
            in-some  (handles-of table (:atoms brave))]
        {:true        (into (set fixed) (filter in-every) assumptions)
         :supportable (into #{} (filter #(and (in-some %) (not (in-every %)))) assumptions)
         :false       (into #{} (remove in-some) assumptions)}))))

(defn enumerate-optima
  "Every optimal answer set of `program`, each as the set of its chosen-true assumption
  handles, from an `:all-optima` solve of the tiebreak-off encoding:

  * `[]`        — no assumptions, or an `:unsat` program;
  * `nil`       — no ASP backend;
  * `[#{h} …]`  — one handle set per optimum otherwise.

  An enumeration the backend did not finish is refused (`:solver-failed`)."
  [{:keys [assumptions] :as program}]
  (cond
    (empty? assumptions)      []
    (not (solver/available?)) nil
    :else
    (let [{:keys [table] :as t} (translate program {:tiebreak? false})
          result                (solver/solve t :all-optima)
          {:keys [witnesses]}   (if (or (answered? result) (= :unsat (:status result)))
                                  result
                                  (unanswered! :all-optima result))]
      ;; two optimal models that differ only in violation atoms are one labeling
      (into [] (distinct) (map #(handles-of table %) witnesses)))))

(defn- undecided
  "The `Solver` answer for a solve that produced no answer set with a backend present:
  no defeat, `:violated` holding the `:doomed` nogoods, and `:error` the exception naming
  why, which `asp.label`'s `solved-defeat` raises (docs/asp.md, \"Refuse rather than
  degrade, whenever a backend is present\")."
  [t ^Throwable err]
  (trove/log! {:level :error :id ::no-answer-set
               :msg  (str "deciding nothing — " (ex-message err))
               :data (assoc (ex-data err) :assumptions (count (:assumptions t)))})
  {:defeat #{} :violated (vec (:doomed t)) :error err})

(def edge-solver
  "The ASP `solve-types/Solver`, `(core/set-solver kb :asp)`.  With no ASP backend
  reachable it is `solve/local-solver`; with one it answers from the backend or decides
  nothing (`undecided`), and throws only a `VirtualMachineError`."
  (reify solve-types/Solver
    (solve [_ program]
      (let [{:keys [aspif] :as t} (translate program)]
        (cond
          ;; nothing contested: only the `:doomed` nogoods remain
          (nil? aspif)             {:defeat #{} :violated (vec (:doomed t))}
          (not (solver/available?)) (solve-types/solve solve/local-solver program)
          :else
          ;; `Throwable`, since a native call fails as a JNA `Error` too; a
          ;; `VirtualMachineError` is rethrown, and an interrupt keeps the thread's flag
          (let [result (try (solver/solve t :label)
                            (catch VirtualMachineError e (throw e))
                            (catch InterruptedException e
                              (.interrupt (Thread/currentThread))
                              {:status :failed :error (backend-failed-ex e)})
                            (catch Throwable e {:status :failed :error (backend-failed-ex e)}))]
            (cond
              (answered? result) (interpret t result)
              (:error result) (undecided t (:error result))
              ;; a dilemma program's nogoods are all soft, so `:unsat` is unreachable
              (= :unsat (:status result))
              (do (trove/log! {:level :warn :id ::unsat
                               :msg  "the ASP program was unsatisfiable; deciding with the local solver"
                               :data {:assumptions (count (:assumptions t))}})
                  (solve-types/solve solve/local-solver program))
              ;; `:interrupted`, `:unknown` and `:best-effort` all decide nothing
              :else (undecided t (unanswered-ex :label result)))))))))
