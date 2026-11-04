;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.solve-context
  "`(do/label Base Into [mode])` and `(do/classify Into)`: ground the `assumptionRule`s,
  solve rules and constraint rules visible from a base context into a `Program`, solve it,
  and write each optimal answer set as an inert labeling context under the base; then
  aggregate brave/cautious over those contexts.  The labeling and classification extents
  are inert, the `(genlCx <labeling> Base)` placement edge is asserted `:monotonic`, and
  the grounding is not stored.  See docs/solving.md."
  (:require [clojure.set :as set]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wiring :as wiring]))

;; `ctx`'s stored extent, believed or not: `vaelii.core/sentexes-in-context` below core
(defn- stored-in [kb ctx]
  (keep #(p/get-sentex (:records kb) %) (reads/as-stored-in-context (:index kb) ctx)))

;; ---- context naming and ownership ----------------------------------------
;; `Into` seeds the names `<Into>1`, `<Into>2`, … and `<Into>Class`.  Ownership is the
;; inert `(labelingOf <ctx> <Into> <i>)` and `(classificationOf <Into>Class <Into>)`
;; markers, never the name (docs/solving.md, "`(do/label Base Into [mode])`").

(defn- ctx-sym [base & parts] (symbol (apply str (name base) parts)))
(defn- class-context [into-cx]      (ctx-sym into-cx "Class"))
(defn- labeling-context [into-cx i] (ctx-sym into-cx i))

(defn- marker?
  "Is this stored sentence a `labelingOf` ownership marker?"
  [sentence]
  (and (seq? sentence) (= 'labelingOf (first sentence))))

(defn- class-marker [into-cx]
  (list 'classificationOf (class-context into-cx) into-cx))

(defn- labeling-contexts
  "The labeling contexts a prior `label` created for `into-cx`, in labeling order, read
  from their `labelingOf` markers through the term index."
  [kb into-cx]
  (->> (kb/find-sentexes kb into-cx)
       (keep (fn [s]
               (let [f (:sentence s)]
                 (when (and (marker? f) (= into-cx (nth f 2 nil)))
                   [(nth f 3 0) (second f)]))))
       (sort-by first)
       (mapv second)))

(defn- free-labeling-contexts
  "`n` labeling context names `<Into><i>` counting up from 1, skipping a name that is in
  the hierarchy or has a non-empty extent."
  [kb into-cx n]
  (let [existing (set (tax/contexts (reasoning/taxonomy kb)))
        taken?   (fn [c] (or (existing c) (pos? (reads/stored-count-in-context (:index kb) c))))]
    (->> (iterate inc 1)
         (map #(labeling-context into-cx %))
         (remove taken?)
         (take n)
         vec)))

;; ---- replace-on-rerun ----------------------------------------------------

(defn- believed-extent?
  "Does `ctx` hold a believed sentex?  A solve writes only inert ones."
  [kb ctx]
  (boolean (some #(jtms/in? (reasoning/tms kb) (:id %)) (stored-in kb ctx))))

(defn- placed-under?
  "Does `ctx` carry the whole sentence `(genlCx ctx base)`, the edge a solve writes to
  place a labeling under `base`?"
  [kb ctx base]
  (boolean (some #(= (:sentence %) (list 'genlCx ctx base)) (kb/find-sentexes kb ctx))))

(defn- marked-for?
  "Does `ctx` carry a `labelingOf` ownership marker naming `into-cx`?"
  [kb ctx into-cx]
  (boolean (some (fn [{:keys [sentence]}]
                   (and (marker? sentence)
                        (= ctx (second sentence))
                        (= into-cx (nth sentence 2 nil))))
                 (stored-in kb ctx))))

(defn- class-blocked
  "What stands between a run and replacing `<Into>Class`: `{:believed [klass]}` when
  its extent holds a believed sentex, `{:unmarked [klass]}` when its extent is non-empty
  with no `(classificationOf <Into>Class <Into>)` marker, else `{}`."
  [kb into-cx]
  (let [klass  (class-context into-cx)
        extent (stored-in kb klass)]
    (cond
      (some #(jtms/in? (reasoning/tms kb) (:id %)) extent) {:believed [klass]}
      (and (seq extent) (not-any? #(= (class-marker into-cx) (:sentence %)) extent))
      {:unmarked [klass]}
      :else {})))

(defn- blocked-artifacts
  "What stands between a re-run and replacing the previous run, as `{:believed [ctx …]
  :orphaned [ctx …] :unmarked [ctx …]}`, all empty when nothing does.  `:believed` is a
  marked labeling context, or the class context, holding a believed sentex.  `:orphaned`
  is a slot `<Into><i>`, walked to the first free one, that has a non-empty extent, nothing
  believed, this run's placement edge under `base`, and no marker.  `:unmarked` is
  `class-blocked`'s.  See docs/solving.md, \"`(do/label Base Into [mode])`\"."
  [kb base into-cx]
  (let [existing (set (tax/contexts (reasoning/taxonomy kb)))
        taken?   (fn [c] (or (existing c) (pos? (reads/stored-count-in-context (:index kb) c))))
        slots    (take-while taken? (map #(labeling-context into-cx %) (iterate inc 1)))
        mine     (set (labeling-contexts kb into-cx))
        klass    (class-blocked kb into-cx)]
    {:believed (into (filterv #(believed-extent? kb %) mine) (:believed klass))
     :orphaned (filterv #(and (not (mine %))
                              (seq (stored-in kb %))
                              (not (believed-extent? kb %))
                              (placed-under? kb % base)
                              (not (marked-for? kb % into-cx)))
                        slots)
     :unmarked (vec (:unmarked klass))}))

(defn- refuse-blocked!
  "Throw `:labeling-run-blocked` when any of `blocked`'s three lists is non-empty."
  [into-cx base {:keys [believed orphaned unmarked]}]
  (when (or (seq believed) (seq orphaned) (seq unmarked))
    (throw (ex-info (str "a previous solve's artifacts under " into-cx
                         " cannot be replaced"
                         (when (seq believed)
                           (str "; believed sentexes in " (pr-str believed)))
                         (when (seq orphaned)
                           (str "; no labelingOf marker on " (pr-str orphaned)))
                         (when (seq unmarked)
                           (str "; no classificationOf marker on " (pr-str unmarked)
                                ", so it is not known to be a classification"))
                         " — a solve clears only the inert content it wrote, so retract"
                         " what is believed there, retract the unmarked contexts' extents"
                         " (and a labeling's genlCx edge), or label into a different Into")
                    {:type :labeling-run-blocked
                     :into into-cx :base base
                     :believed (vec believed) :orphaned (vec orphaned)
                     :unmarked (vec unmarked)}))))

(defn- refuse-blocked-run!
  "Throw `:labeling-run-blocked` when `blocked-artifacts` finds anything.  `label` calls
  it before the solve, and `clear-run!` again before it retracts."
  [kb base into-cx]
  (refuse-blocked! into-cx base (blocked-artifacts kb base into-cx)))

(defn- clear-context!
  "Retract `ctx`'s stored extent and, with a `base`, the whole sentence `(genlCx ctx
  base)`; other sentexes naming `ctx` are left.  Touches nothing when the extent holds a
  believed sentex."
  [kb ctx base]
  (let [extent (stored-in kb ctx)]
    (when (not-any? #(jtms/in? (reasoning/tms kb) (:id %)) extent)
      (doseq [s extent]
        (wiring/retract-sentex kb (:id s)))
      (when base
        (doseq [{:keys [id sentence]} (kb/find-sentexes kb ctx)
                :when (= sentence (list 'genlCx ctx base))]
          (wiring/retract-sentex kb id))))))

(defn- clear-run!
  "Retract every artifact a previous run under `into-cx` left: each marked labeling
  context's extent and placement edge under `base`, and the classification's extent when
  it carries its marker.  Refuses first (`refuse-blocked-run!`), so nothing is retracted
  unless everything can be."
  [kb base into-cx]
  (refuse-blocked-run! kb base into-cx)
  (doseq [ctx (labeling-contexts kb into-cx)]
    (clear-context! kb ctx base))
  (when (some #(= (class-marker into-cx) (:sentence %)) (stored-in kb (class-context into-cx)))
    (clear-context! kb (class-context into-cx) nil)))

;; ---- grounding: assumptionRules × visible facts → choice heads -----------

(defn- program-rules
  "Every believed rule a solve reads (`rules/solve-sentex?`) stored in `base` or its
  `genlCx` ancestor set, in content order: off the rule extent's `:solve` node, believed by
  `res/rule-believed?`, and not withdrawn at `base`."
  [kb base]
  (let [out (or (exc/belief-hidden-fn kb base) (constantly false))]
    (->> (reads/as-stored-rules-in (:index kb) :solve
                                   (conj (set (tax/context-up (reasoning/taxonomy kb) base)) base))
         (keep #(p/get-sentex (:records kb) %))
         (filter #(and (res/rule-believed? kb (:id %)) (not (out (:id %)))))
         (nm/sort-by-content-key #(nm/print-key [(sx/sentence-of %) (:context %)]) compare))))

(defn- assumption-rules
  "The believed `assumptionRule`s visible from `base` (`program-rules`)."
  [kb base]
  (filter rules/assumption? (program-rules kb base)))

(defn- registry-bounds
  "`res/prove` bounds whose leaf is the prover registry (`provers/solve-goal`, costed by
  `provers/registry-est-override`), so a grounding join reaches an antecedent a registered
  prover or evaluatable answers, as `vaelii.core/query` does."
  [kb base]
  {:leaf-solver  provers/solve-goal
   :est-override (provers/registry-est-override kb base)})

(defn- ground-heads
  "The distinct ground choice heads: each assumptionRule's antecedents proved in `base`
  over `registry-bounds`, its head substituted per solution the rule's `exceptWhen` guard
  admits."
  [kb base]
  (let [bounds (registry-bounds kb base)]
    (distinct
     (for [rsx (assumption-rules kb base)
           :let [ante  (vec (:antecedent rsx))
                 head  (:consequent rsx)
                 guard (provers/rule-guard kb rsx base)]
           binding (res/prove kb (fn [g] (provers/candidate-rules kb g base)) ante base bounds)
           :when (or (nil? guard) (guard binding))]
       (res/substitute head binding)))))

;; ---- the auto-clash detectors among the choice heads ----------------------

(defn- negation-pair? [s1 s2]
  (or (= s1 (list 'not s2)) (= s2 (list 'not s1))))

(defn- functional-clash?
  "Two heads of a predicate `functional` at `base` that agree on the first argument and
  differ on the second."
  [kb base s1 s2]
  (and (sequential? s1) (sequential? s2)
       (= 3 (count s1)) (= 3 (count s2))
       (= (first s1) (first s2))
       (= (second s1) (second s2))
       (not= (nth s1 2) (nth s2 2))
       (tax/has-prop? (reasoning/taxonomy kb) :functional (first s1) base)))

(defn- disjoint-clash?
  "Two unary type memberships of one individual whose types are disjoint at `base`."
  [kb base s1 s2]
  (and (sequential? s1) (sequential? s2)
       (= 2 (count s1)) (= 2 (count s2))
       (= (second s1) (second s2))
       (not= (first s1) (first s2))
       (kb/disjoint? kb (first s1) (first s2) base)))

(defn- clash? [kb base s1 s2]
  (or (negation-pair? s1 s2)
      (functional-clash? kb base s1 s2)
      (disjoint-clash? kb base s1 s2)))

(defn- pairs [xs]
  (let [v (vec xs)]
    (for [i (range (count v)), j (range (inc i) (count v))] [(v i) (v j)])))

(defn- positive-core
  "A head's positive body — a `(not X)` unwrapped to X, else the head itself."
  [s]
  (if (and (seq? s) (= 'not (first s))) (second s) s))

(defn- clash-key
  "The first argument of a head's positive body, or nil: a negation pair, a functional
  clash and a disjoint clash each need two heads that agree on it."
  [s]
  (let [p (positive-core s)]
    (when (and (sequential? p) (> (count p) 1)) (nth p 1))))

(defn- nogoods
  "The nogoods the auto-clash detectors find among the heads of `head->id`, one per
  clashing pair at priority 1, comparing heads only within a `clash-key` bucket.  Each
  bucket is sorted by `nm/print-key`, so the set is order-independent."
  [kb base head->id]
  (for [bucket (vals (group-by (comp clash-key key) head->id))
        [[s1 _] [s2 _]] (pairs (nm/sort-by-content-key (comp nm/print-key key) compare bucket))
        :when   (clash? kb base s1 s2)]
    {:nogood #{(head->id s1) (head->id s2)}
     :priority 1
     :sentence (list 'contradicts s1 s2)}))

;; ---- constraint rules: a conjunctive nogood over facts + choice heads -----
;; A body joins its background literals over `base` belief and its program literals over
;; the program's atoms (docs/solving.md, "`hardConstraint` / `softConstraint`").

(defn- constraint-rules
  "The believed constraint rules visible from `base` (`program-rules`), cardinality rules
  excepted (`cardinality-rules`)."
  [kb base]
  (filter #(and (rules/constraint? %) (not (rules/cardinality-of %))) (program-rules kb base)))

(defn- choice-arg-index
  "Index the ground heads for join lookup: `{:by-pred {pred [head …]} :by-arg {[pred pos
  val] #{head …}}}`, `pos` 1-based.  With `idx`, extends that index by `heads`."
  ([heads] (choice-arg-index {} heads))
  ([idx heads]
   (reduce
    (fn [idx head]
      (let [pred (first head)]
        (reduce (fn [idx [i a]]
                  (update-in idx [:by-arg [pred (inc i) a]] (fnil conj #{}) head))
                (update-in idx [:by-pred pred] (fnil conj []) head)
                (map-indexed vector (rest head)))))
    idx
    heads)))

(defn- literal-heads
  "The heads of `idx` a partially ground literal `lit` can match: the intersection of
  the `:by-arg` sets of its ground positions, or with none every head of its predicate."
  [idx lit]
  (let [pred   (first lit)
        ground (for [[i a] (map-indexed vector (rest lit))
                     :when (not (sx/variable? a))]
                 [pred (inc i) a])]
    (if (seq ground)
      (reduce set/intersection (map #(get-in idx [:by-arg %] #{}) ground))
      (get-in idx [:by-pred pred] []))))

(defn- join-choice-literals
  "Extend binding `b` (and its accumulated choice-head-id set `ids`) across the choice
  literals `chs`, matching each against `idx`.  Returns `[[binding ids] …]`."
  [idx head->id chs b ids]
  (if (empty? chs)
    [[b ids]]
    (let [lit (res/substitute (first chs) b)]
      (mapcat (fn [head]
                (when-let [b2 (res/unify lit head b)]
                  (join-choice-literals idx head->id (rest chs) b2 (conj ids (head->id head)))))
              (literal-heads idx lit)))))

(defn- join-negated-literals
  "`join-choice-literals` for the negated program literals `lits`, each a head required
  absent.  A ground literal naming an atom the program does not have holds and adds no
  member."
  [idx head->id lits b ids]
  (if (empty? lits)
    [[b ids]]
    (let [lit (res/substitute (first lits) b)]
      (if (sx/ground-term? lit)
        (join-negated-literals idx head->id (rest lits) b
                               (if-let [id (head->id lit)] (conj ids id) ids))
        (mapcat (fn [head]
                  (when-let [b2 (res/unify lit head b)]
                    (join-negated-literals idx head->id (rest lits) b2 (conj ids (head->id head)))))
                (literal-heads idx lit))))))

(defn- neg-choice-lit?
  "Is `l` `(not <program literal>)`, a head required absent?  `choice-preds` holds the
  choice heads' predicates and the solve rules' derived ones."
  [choice-preds l]
  (and (seq? l) (= 'not (first l)) (sequential? (second l))
       (choice-preds (first (second l)))))

(defn- ground-constraint-body
  "Join `body`: its background literals proved in `base` over `bounds`, then its positive
  program literals (predicate in `choice-preds`) against `idx`, then its negated ones the
  same way.  Returns `[[#{pos-ids} #{neg-ids} marker] …]`, one per binding, or nil when the
  body holds no program literal.  Negated background literals are outside the contract."
  [kb base body consequent choice-preds head->id idx bounds]
  (let [neg?        #(neg-choice-lit? choice-preds %)
        neg-lits    (mapv second (filter neg? body))
        rest-body   (remove neg? body)
        choice-lit? #(and (sequential? %) (choice-preds (first %)))
        bg  (remove choice-lit? rest-body)
        chs (filter choice-lit? rest-body)]
    (when (or (seq chs) (seq neg-lits))
      (for [bgb          (if (seq bg) (res/prove kb (fn [g] (provers/candidate-rules kb g base)) (vec bg) base bounds) [{}])
            [b ids]      (join-choice-literals idx head->id chs bgb #{})
            [b2 neg-ids] (join-negated-literals idx head->id neg-lits b #{})]
        [ids neg-ids (res/substitute consequent b2)]))))

(defn- check-minimize-weight
  "Throw `:not-well-formed` unless `weight`, bound by one binding of the `asp/minimize`
  rule `rsx`, is an integer in the solver's 32-bit range.  A backend refuses a program
  holding any other weight as `:solver-failed`, naming no fact."
  [rsx weight]
  (when-not (and (integer? weight) (<= Integer/MIN_VALUE weight Integer/MAX_VALUE))
    (let [surface (rules/rewrap (sx/sentence-of rsx) nil nil nil (rules/constraint-of rsx))]
      (throw (ex-info (str "an asp/minimize weight must be an integer in the solver's 32-bit "
                           "range; a background fact bound " (pr-str weight) " in "
                           (pr-str surface))
                      {:type :not-well-formed :sentence surface :weight weight})))))

(defn- constraint-nogoods
  "Ground every constraint rule visible from `base` into nogoods, one per binding of its
  body (`ground-constraint-body`) over the atoms of `head->id`, with `program-preds` the
  solve rules' derived predicates.  A negated body adds `:neg`; a hard rule's nogoods carry
  `:hard true`; a soft's carry the `:priority` and `:weight` its marker reads
  (`rules/soft-cost-of`)."
  [kb base head->id program-preds]
  (let [choice-preds (into program-preds (map first) (keys head->id))
        idx          (choice-arg-index (keys head->id))
        bounds       (registry-bounds kb base)]
    (for [rsx (constraint-rules kb base)
          :let [body   (vec (:antecedent rsx))
                conseq (:consequent rsx)
                hard?  (= :hard (rules/constraint-of rsx))]
          [ids neg-ids marker] (ground-constraint-body kb base body conseq choice-preds head->id idx bounds)
          :let [{:keys [priority weight marker]} (rules/soft-cost-of marker)
                _ (when (some? weight) (check-minimize-weight rsx weight))]]
      (cond-> {:nogood ids :priority priority :sentence (list 'contradicts marker)}
        weight        (assoc :weight weight)
        (seq neg-ids) (assoc :neg neg-ids)
        hard?         (assoc :hard true)))))

;; ---- cardinality rules: a bound over a whole set of choice heads ----------
;; One `:cardinalities` entry per group (docs/solving.md, "`atMost` / `atLeast`").

(defn- cardinality-rules
  "The believed cardinality rules visible from `base` (`program-rules`)."
  [kb base]
  (filter rules/cardinality-of (program-rules kb base)))

(defn- check-sum-weights
  "Throw `:not-well-formed` unless every weight in `weights`, bound by the weighted bound
  `rsx`, is a non-negative integer and, with `total?`, their total fits the solver's
  32-bit range: a weight body's bound and weights are int32, and a negative weight has no
  ASPIF spelling."
  [rsx weights total?]
  (let [bad   (first (remove #(and (integer? %) (<= 0 % Integer/MAX_VALUE)) weights))
        total (when (and total? (nil? bad)) (reduce + 0 weights))]
    (when (or (some? bad) (and total (< Integer/MAX_VALUE total)))
      (let [surface (rules/rewrap (sx/sentence-of rsx) nil nil nil (rules/constraint-of rsx))]
        (throw (ex-info (str "a weighted bound's weights must be non-negative integers whose "
                             "total per group fits the solver's 32-bit range; "
                             (if (some? bad)
                               (str "a background fact bound " (pr-str bad))
                               (str "one group's weights total " total))
                             " in " (pr-str surface))
                        {:type :not-well-formed :sentence surface :weight bad}))))))

(defn- sum-groups
  "The weighted bound `rsx`'s groups: `{gkey {id weight}}`, its body grounded as a
  constraint body (`ground-constraint-body`) over the atoms of `head->id`, each distinct
  binding of the weight, counted and group variables adding its weight to the one
  program atom it names, summed per atom as `#sum` sums distinct tuples.  Throws
  `:not-well-formed` for a body naming other than one positive program literal."
  [kb base rsx head->id idx]
  (let [{:keys [counted weight]} (rules/cardinality-of rsx)
        body       (vec (:antecedent rsx))
        preds      (into #{} (map first) (keys head->id))
        prog       (filter #(and (sequential? %) (preds (first %))) body)
        group-vars (vec (remove #{counted weight} (distinct (sx/form-vars body))))]
    (when-not (and (= 1 (count prog)) (not-any? #(neg-choice-lit? preds %) body))
      (throw (ex-info (str "a weighted bound's body names exactly one positive choice or "
                           "derived literal, the head each weight counts toward; got "
                           (pr-str (rules/rewrap (sx/sentence-of rsx) nil nil nil
                                                 (rules/constraint-of rsx))))
                      {:type :not-well-formed :sentence (sx/sentence-of rsx)})))
    (let [rows (distinct (ground-constraint-body kb base body (list* 'sumKey weight counted group-vars)
                                                 preds head->id idx (registry-bounds kb base)))
          _    (check-sum-weights rsx (map (fn [[_ _ [_ w]]] w) rows) false)
          grouped (group-by (fn [[_ _ [_ _ _ & g]]] (zipmap group-vars g)) rows)]
      (if (and (empty? rows) (empty? group-vars))
        {{} {}}
        (into {}
              (map (fn [[gkey gs]]
                     (let [ws (reduce (fn [m [ids _ [_ w]]] (update m (first ids) (fnil + 0) w)) {} gs)]
                       (check-sum-weights rsx (vals ws) true)
                       [gkey ws])))
              grouped)))))

(defn- cardinality-constraints
  "Ground every cardinality rule visible from `base` into `vaelii.impl.types.solve/Program` cardinality
  entries: its single antecedent matched against the atoms of `head->id`, the matches
  grouped by the bindings of its variables other than the counted one, one entry per
  group.  `(build ?c transport)` counted over `?c` is one group; `(ferry ?a ?t)` counted
  over `?a` is one per `?t`.  A global bound with no match is one empty group.  A weighted
  bound's entry adds `:weights {id w}` (`sum-groups`)."
  [kb base head->id]
  (let [idx (choice-arg-index (keys head->id))]
    (for [rsx (cardinality-rules kb base)
          :let [{:keys [op k counted weight]} (rules/cardinality-of rsx)
                hard?      (= :hard (rules/constraint-of rsx))
                pattern    (first (:antecedent rsx))
                group-vars (remove #{counted}
                                   (distinct (sx/form-vars pattern)))
                matches    (when-not weight
                             (for [head (literal-heads idx pattern)
                                   :let  [b (res/unify pattern head {})]
                                   :when b]
                               [(dissoc b counted) (head->id head)]))
                groups     (cond
                             weight (sum-groups kb base rsx head->id idx)
                             (and (empty? matches) (empty? group-vars)) {{} []}
                             :else (group-by first matches))]
          [gkey members] groups]
      (if weight
        (let [body (:antecedent rsx)]
          {:op op :k k
           :members  (set (keys members))
           :weights  members
           :hard     hard?
           :priority 1
           :sentence (list 'sumBound op k (res/substitute (if (next body) (cons 'and body) (first body))
                                                          gkey))})
        {:op op :k k
         :members  (into #{} (map second) members)
         :hard     hard?
         :priority 1
         :sentence (list 'cardinalityBound op k (res/substitute pattern gkey))}))))

;; ---- solve rules: the normal rules a solve grounds ------------------------
;; A body splits by predicate as a constraint's does; grounding is a semi-naive fixpoint
;; (docs/solving.md, "`solveRule`").

(def ^:private max-derived-atoms
  "The most atoms a solve's rules may derive before grounding refuses."
  200000)

(defn- solve-rules
  "The believed `set/solveRule`s visible from `base` (`program-rules`): the `:derive`
  rules a solve runs."
  [kb base]
  (filter #(= :derive (:effect %)) (program-rules kb base)))

(defn- program-literal?
  "Is `lit` a literal over one of the program predicates `preds`?"
  [preds lit]
  (and (sequential? lit) (seq lit) (contains? preds (first lit))))

(defn- negated-program-literal
  "The atom pattern of `lit` when it is `(not <program literal>)`, else nil."
  [preds lit]
  (when (and (seq? lit) (= 'not (first lit)) (program-literal? preds (second lit)))
    (second lit)))

(defn- join-order
  "The step order a round joins a rule's body in when its positive program literal `i`
  reads the new atoms: `i` first, then each literal sharing a variable with what is bound,
  the background bindings one step among them, keyed on the variables bound where it
  falls.  Returns `[[:atom j] … [:bg key-vars] …]`."
  [pos bg-vars bg? i]
  (loop [steps [[:atom i]]
         bound (sx/form-variables (nth pos i))
         left  (remove #{i} (range (count pos)))
         bg?   bg?]
    (if (and (empty? left) (not bg?))
      steps
      (let [shares? #(seq (set/intersection bound %))
            j       (or (first (filter #(shares? (sx/form-variables (nth pos %))) left))
                        (when-not (and bg? (shares? bg-vars)) (first left)))]
        (if j
          (recur (conj steps [:atom j]) (into bound (sx/form-variables (nth pos j))) (remove #{j} left) bg?)
          (recur (conj steps [:bg (vec (sort-by nm/name-key (set/intersection bound bg-vars)))])
                 (into bound bg-vars) left false))))))

(defn- join-steps
  "Extend binding `b` along `steps`: an `[:atom j literal]` step matches its literal
  against the index `idx-of` gives position `j`, and a `[:bg key-vars index]` step reads
  the background bindings filed under what `b` binds those variables to.  Returns
  `[[binding [atom …]] …]`."
  [steps idx-of b atoms]
  (if (empty? steps)
    [[b atoms]]
    (let [[kind x y] (first steps)]
      (if (= :atom kind)
        (let [lit (res/substitute y b)]
          (mapcat (fn [a]
                    (when-let [b2 (res/unify lit a b)]
                      (join-steps (rest steps) idx-of b2 (conj atoms a))))
                  (literal-heads (idx-of x) lit)))
        (mapcat (fn [b0]
                  (when-let [b2 (reduce-kv (fn [acc k v] (or (res/unify k v acc) (reduced nil))) b0 b)]
                    (join-steps (rest steps) idx-of b2 atoms)))
                (get y (mapv #(res/substitute % b) x)))))))

(defn- prepared-solve-rule
  "Split solve rule `rsx` for grounding: `{:rsx :pos :neg :head :guard :bg :plans}`, its
  background bindings proved once in `base` and one `join-order` plan per positive
  literal.  Throws `:not-well-formed` for a negated head."
  [kb base preds bounds rsx]
  (let [body (vec (:antecedent rsx))
        head (:consequent rsx)
        neg  (into [] (keep #(negated-program-literal preds %)) body)
        pos  (filterv #(program-literal? preds %) body)
        bg   (filterv #(not (or (program-literal? preds %) (negated-program-literal preds %))) body)]
    (when (and (seq? head) (= 'not (first head)))
      (throw (ex-info (str "a solve rule's head must be a positive literal, as a choice head"
                           " is: " (pr-str (sx/sentence-of rsx)))
                      {:type :not-well-formed :sentence (sx/sentence-of rsx) :base base})))
    (let [bindings (vec (if (seq bg)
                          (res/prove kb (fn [g] (provers/candidate-rules kb g base)) bg base bounds)
                          [{}]))
          by-key   (memoize (fn [kv] (group-by (fn [b0] (mapv #(res/substitute % b0) kv)) bindings)))
          step     (fn [[kind x]]
                     (if (= :atom kind) [:atom x (nth pos x)] [:bg x (by-key x)]))]
      {:rsx rsx :pos pos :neg neg :head head
       :guard (provers/rule-guard kb rsx base)
       :bg    bindings
       :plans (mapv #(mapv step (join-order pos (sx/form-variables bg) (boolean (seq bg)) %))
                    (range (count pos)))})))

(defn- rule-instances
  "The ground instances `{:head atom :pos #{atom} :neg #{atom}}` of prepared rule `r`
  one round finds, positive literal `i` matched against the new atoms.  Throws
  `:not-well-formed` when the head or a negated literal is left open."
  [r idx-of i]
  (for [[b atoms] (if (empty? (:pos r))
                    (map (fn [b0] [b0 []]) (:bg r))
                    (join-steps (nth (:plans r) i) idx-of {} []))
        :when     (or (nil? (:guard r)) ((:guard r) b))]
    (let [head (res/substitute (:head r) b)
          neg  (mapv #(res/substitute % b) (:neg r))]
      (when-let [open (first (remove sx/ground-term? (cons head neg)))]
        (throw (ex-info (str "a solve rule's head and negated literals must be bound by its"
                             " positive ones; " (pr-str open) " is not, in "
                             (pr-str (sx/sentence-of (:rsx r))))
                        {:type :not-well-formed :sentence (sx/sentence-of (:rsx r))
                         :unbound open})))
      {:head head :pos (set atoms) :neg (set neg)})))

(defn- ground-derivations
  "Every ground instance of the prepared solve rules `rules` over the atoms that can
  become true, from the choice heads and the `seeds`, by a semi-naive fixpoint that
  ignores negation.  Throws `:not-well-formed` past `max-derived-atoms`."
  [rules choice-heads seeds]
  (let [delta0 (into (set choice-heads) (map :head) seeds)
        i0     (choice-arg-index delta0)]
    (loop [full delta0, i-old {}, i-new i0, i-full i0, insts (set seeds), round 0]
      (when (> (count full) max-derived-atoms)
        (throw (ex-info (str "a solve's rules derive more than " max-derived-atoms
                             " atoms — a head that builds a larger term from its"
                             " body's derives without bound")
                        {:type :not-well-formed :atoms (count full)})))
      (let [found  (into #{}
                         (mapcat (fn [r]
                                   (let [k (count (:pos r))]
                                     (if (zero? k)
                                       (when (zero? round) (rule-instances r nil 0))
                                       (mapcat (fn [i]
                                                 (rule-instances r #(cond (< % i) i-old
                                                                          (= % i) i-new
                                                                          :else   i-full)
                                                                 i))
                                               (range k))))))
                         rules)
            fresh  (remove insts found)
            added  (into #{} (comp (map :head) (remove full)) fresh)
            insts' (into insts fresh)]
        (if (empty? added)
          insts'
          (let [i-added (choice-arg-index added)]
            (recur (into full added) i-full i-added (choice-arg-index i-full added)
                   insts' (inc round))))))))

(defn- seed-derivations
  "The instances of each solve rule's head that `Base` already holds — proved there, over
  the same registry leaf — as instances with an empty body: true in every answer set, as
  a base fact is true in every labeling context below the base."
  [kb base rules bounds]
  (into #{}
        (comp (map :head)
              (distinct)
              (mapcat (fn [h]
                        (for [b (res/prove kb (fn [g] (provers/candidate-rules kb g base)) [h] base bounds)]
                          {:head (res/substitute h b) :pos #{} :neg #{}})))
              (filter #(sx/ground-term? (:head %))))
        rules))

;; ---- the program ---------------------------------------------------------

(defn- build
  "Ground the choice heads, the solve rules' instances, the auto-clash and constraint-rule
  nogoods and the cardinality entries in `base` into a `Program`, writing nothing.
  Returns `{:program p :head->id {sentence id} :derived->id {sentence id}}`, or nil with no
  choice head.  The ids are program-local, numbered over the heads sorted by
  `nm/print-key`, then the derived atoms in the same order; `edge/translate` orders the
  encoding by them.  Eager, so `provers/with-unenumerated` around it sees every join.
  Throws `:choice-head-not-positive` for a negated head."
  [kb base]
  (let [heads (nm/sort-by-content-key nm/print-key compare (ground-heads kb base))]
    ;; a negated head would read back from `(not head)` with its polarity flipped
    (when-let [neg (seq (filter #(and (seq? %) (= 'not (first %))) heads))]
      (throw (ex-info (str "a choice head must be a positive literal; negated assumptionRule "
                           "head(s): " (pr-str (vec neg)))
                      {:type :choice-head-not-positive :negated (vec neg) :base base})))
    (when (seq heads)
      (let [head->id (into {} (map-indexed (fn [i s] [s (inc i)])) heads)
            bounds   (registry-bounds kb base)
            srules   (solve-rules kb base)
            dpreds   (into #{} (map #(first (:consequent %))) srules)
            preds    (into dpreds (map first) heads)
            prepared (mapv #(prepared-solve-rule kb base preds bounds %) srules)
            insts    (when (seq prepared)
                       (ground-derivations prepared heads (seed-derivations kb base prepared bounds)))
            ;; a derived atom's id follows the choices', minted in the same content order
            derived  (nm/sort-by-content-key nm/print-key compare
                                             (into #{} (comp (map :head) (remove head->id)) insts))
            atom->id (into head->id (map-indexed (fn [i s] [s (+ 1 (count heads) i)])) derived)
            derivs   (into []
                           (comp (map (fn [{:keys [head pos neg]}]
                                        {:head (atom->id head)
                                         :pos  (into #{} (map atom->id) pos)
                                         ;; an atom nothing can derive is false, so its
                                         ;; default negation holds and drops out
                                         :neg  (into #{} (keep atom->id) neg)}))
                                 (distinct))
                           insts)
            content  (into {} (map (fn [[s id]] [id {:sentence s :context base}])) atom->id)
            ngoods   (into [] cat [(nogoods kb base head->id)
                                   (constraint-nogoods kb base atom->id dpreds)])
            cards    (vec (cardinality-constraints kb base atom->id))
            program  (solve/program (set (vals head->id)) ngoods content cards derivs)]
        {:program program :head->id head->id :derived->id (apply dissoc atom->id heads)}))))

;; ---- do/label: one inert labeling context per optimal answer set ---------

(defn- one-optimum
  "One answer set of `program` from a single `:label` solve with the tiebreak off:
  `{:optima [#{ids}] :best-effort? b :translate-ms t :solve-ms t}`, `:optima` `[]` when
  the program is unsatisfiable and nil with no backend.  `keep-belief?` false drops the
  keep-belief objective (`:sat`)."
  [program keep-belief?]
  (if-not (solver/available?)
    {:optima nil}
    (let [ta         (System/nanoTime)
          translated (edge/translate program {:tiebreak? false :keep-belief? keep-belief?})
          tb         (System/nanoTime)
          result     (solver/solve translated :label)
          tc         (System/nanoTime)]
      {:optima       (if (= :unsat (:status result)) [] [(edge/kept-of translated result)])
       :best-effort? (= :best-effort (:status result))
       :translate-ms (/ (- tb ta) 1e6)
       :solve-ms     (/ (- tc tb) 1e6)})))

(defn label
  "`do/label`: ground and solve the program `build` makes in `base`.  `mode` is `:all`
  (the default), `:one` or `:sat`:

    * `:all` writes each optimal answer set as an inert labeling context `<Into><i>`
      under `base`, holding `(head)` per true atom, `(not head)` per false one and its
      `labelingOf` marker, after clearing the previous run (`clear-run!`);
    * `:one` returns one optimal answer set and writes nothing;
    * `:sat` is `:one` without the keep-belief objective.

  An `:all` run refuses `:labeling-run-blocked` before grounding when the previous run
  cannot be replaced (`blocked-artifacts`).  A run grounding no choice clears too; a run
  with no backend leaves the previous run standing.

  Returns `{:base :into :choices [..] :derived [..] :labelings [{:context :true [..]
  :false [..]}] :count n :unenumerated [..] :unenumerated-in-guards [..] :ground-ms
  :translate-ms :solve-ms}`, `:context` nil under `:one` / `:sat`, `:best-effort? true`
  when a stopped solve held a model.  `:unenumerated` names each transitive predicate the
  grounding read with both arguments open (`provers/*unenumerated*`).  `:count 0`
  carries a `:reason`: `:no-choices`, `:no-backend`, or `:unsatisfiable` under `:one` /
  `:sat`.  See docs/solving.md, \"`(do/label Base Into [mode])`\"."
  ([kb base into-cx] (label kb base into-cx :all))
  ([kb base into-cx mode]
   (let [single? (contains? #{:one :sat} mode)
         _       (when-not single? (refuse-blocked-run! kb base into-cx))
         t0      (System/nanoTime)
         [built unenumerated] (provers/with-unenumerated #(build kb base))
         t1      (System/nanoTime)]
     (if-let [{:keys [program head->id derived->id]} built]
       (let [atom->id (merge head->id derived->id)
             id->head (zipmap (vals atom->id) (keys atom->id))
             all-ids  (set (vals atom->id))
             ;; the derived atoms in id order — content order, after the choices
             derived  (mapv id->head (range (inc (count head->id)) (inc (count atom->id))))
             ;; the heads in id order, as `build` sorted them
             choices  (mapv id->head (range 1 (inc (count head->id))))
             {:keys [optima translate-ms solve-ms best-effort?]}
             (if single?
               (one-optimum program (= mode :one))     ; :sat ⇒ keep-belief off (plain SAT)
               (let [ta (System/nanoTime), o (edge/enumerate-optima program)]
                 {:optima o :solve-ms (/ (- (System/nanoTime) ta) 1e6)}))
             timing   (merge unenumerated
                             {:ground-ms (/ (- t1 t0) 1e6) :translate-ms translate-ms :solve-ms solve-ms})
             labeling (fn [chosen] {:true  (into [] (map id->head) chosen)
                                    :false (into [] (map id->head) (remove (set chosen) all-ids))})]
         (cond
           (nil? optima)
           (merge {:base base :into into-cx :count 0 :choices choices
                   :derived derived :reason :no-backend :labelings []} timing)

           ;; no answer set: under `:all` that is an empty enumeration
           (and single? (empty? optima))
           (merge {:base base :into into-cx :count 0 :choices choices
                   :derived derived :reason :unsatisfiable :labelings []} timing)

           single?
           (merge {:base base :into into-cx :count 1 :choices choices :derived derived
                   :labelings [(assoc (labeling (first optima)) :context nil)]}
                  (when best-effort? {:best-effort? true})
                  timing)

           ;; :all — materialize each optimum as its own inert labeling context
           :else
           (do
             (clear-run! kb base into-cx)
             (let [ctxs (free-labeling-contexts kb into-cx (count optima))]
               (merge {:base base :into into-cx :count (count optima) :choices choices
                       :derived derived
                       :labelings
                       (vec (map-indexed
                             (fn [i chosen]
                               (let [ctx    (nth ctxs i)
                                     l      (labeling chosen)
                                     truths (:true l)
                                     falses (:false l)]
                                 (wiring/assert-sentence kb (list 'genlCx ctx base) base {:strength :monotonic})
                                 (kb/find-or-create-sentex kb (list 'labelingOf ctx into-cx (inc i)) ctx)
                                 (doseq [s truths] (kb/find-or-create-sentex kb s ctx))
                                 (doseq [s falses] (kb/find-or-create-sentex kb (list 'not s) ctx))
                                 (assoc l :context ctx)))
                             optima))}
                      timing)))))
       (do (when-not single? (clear-run! kb base into-cx))
           (merge {:base base :into into-cx :count 0 :choices []
                   :reason :no-choices :labelings []}
                  unenumerated))))))

;; ---- do/classify: gather brave/cautious over the labelings ---------------

(defn- polarity-table
  "One labeling context's extent, its marker skipped, as `{head :true|:false}`: `:true`
  for `(head)`, `:false` for `(not head)`."
  [kb ctx]
  (into {}
        (keep (fn [{:keys [sentence]}]
                (cond
                  (marker? sentence) nil
                  (and (seq? sentence) (= 'not (first sentence))) [(second sentence) :false]
                  :else [sentence :true])))
        (stored-in kb ctx)))

(defn classify
  "`do/classify`: aggregate the labelings a prior `(do/label _ Into)` wrote and write
  `(forced H)` (true in every labeling), `(excluded H)` (false in every one) or
  `(supportable H)` per head, with its `classificationOf` marker, into `<Into>Class`,
  replacing the previous classification.  Refuses `:labeling-run-blocked` when
  `class-blocked` finds anything.  Returns `{:into :class-context :count :forced [..]
  :supportable [..] :excluded [..]}`, or `:count 0 :reason :no-labelings`.  See
  docs/solving.md, \"`(do/classify Into)`\"."
  [kb into-cx]
  (let [labelings (labeling-contexts kb into-cx)
        klass     (class-context into-cx)]
    (refuse-blocked! into-cx nil (class-blocked kb into-cx))
    (if (empty? labelings)
      {:into into-cx :count 0 :reason :no-labelings
       :forced [] :supportable [] :excluded []}
      (let [tables (mapv #(polarity-table kb %) labelings)
            heads  (distinct (mapcat keys tables))
            classify-one
            (fn [s]
              (let [ps (map #(get % s) tables)]
                (cond (every? #(= :true %) ps)  :forced
                      (every? #(= :false %) ps) :excluded
                      :else                     :supportable)))
            grouped (group-by classify-one heads)]
        (clear-context! kb klass nil)
        (kb/find-or-create-sentex kb (class-marker into-cx) klass)
        (doseq [[k ss] grouped, s ss]
          (kb/find-or-create-sentex kb (list (symbol (name k)) s) klass))
        {:into into-cx :class-context klass :count (count labelings)
         :forced      (vec (:forced grouped))
         :supportable (vec (:supportable grouped))
         :excluded    (vec (:excluded grouped))}))))
