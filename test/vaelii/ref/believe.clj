;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ref.believe
  "The belief reference: what a context believes, computed from the world's premises
  alone, one context at a time, with no memo, no region and no budget (docs/reference.md,
  \"The function\").

  `resolve-at` runs the rounds at one context `C`: `derive-at` fires the rules visible at
  `C` over the premises stored in `up(C)` minus the OUT set, `class-fixpoint` and
  `inherit-at` add the classes and the inherited claims, and `decide` gives each nogood
  its verdict.

  The families are passed in (`families`, a seq of functions of a view returning
  nogoods); this namespace requires none of them.

  The view a family receives is `{:context C :sees up(C) :believed #{S …} :class f
  :genl g :inherited #{S …}}`. `:believed` holds every ground literal believed at `C`:
  facts, denials, `genl` and `genlCx` edges and declarations, premises, derivations and
  inherited claims alike. `:inherited` is the subset of `:believed` that no visible write
  states and no rule derives at `C`: the claims only `inherit-at` reaches, which the
  engine stores no sentex for. Rules and `exceptWhen` exceptions are not in `:believed`:
  nothing defeats either, so a rule is believed at `C` exactly when its context is in
  `up(C)`. `(f S)` is the class of `S` at `C`, nil when `S` is not believed. `(g t)` is
  `t` plus every type `t` reaches over the edges the believed `genl` edges and
  `covering` declarations install at `C`.

  A nogood is `{:kind k :members #{S …} :ground #{D …}}`: members believed at `C`, and the
  declarations and edges the clash is read through, which `decide` never weighs
  (docs/nmtms.md, \"What qualifies as a nogood\")."
  (:require [clojure.set :as set]
            [vaelii.ref.world :as world]))

;; ---- classes ----------------------------------------------------------------

(def ^:private rank {:default 0 :monotonic 1})

(defn- weakest [& cs] (reduce #(if (< (rank %2) (rank %1)) %2 %1) :monotonic cs))
(defn- strongest [& cs] (reduce #(if (> (rank %2) (rank %1)) %2 %1) :default cs))

;; ---- the context lattice ----------------------------------------------------

(defn- context-edges
  "`{sub #{super}}` over every genlCx write of `world`."
  [world]
  (reduce (fn [m {:keys [sentence]}]
            (if (world/genlCx-edge? sentence)
              (update m (second sentence) (fnil conj #{}) (nth sentence 2))
              m))
          {} (:writes world)))

(defn- up-with
  "`up(C)`: `c`, CxUniverse, and every context they reach over the genlCx edges `edges`
  (`{sub #{super}}` off `context-edges`), whatever context stores each edge
  (docs/reference.md, item 1 of \"The function\")."
  [edges c]
  (let [start (conj #{c} 'CxUniverse)]
    (loop [seen start todo (vec start)]
      (if-let [x (peek todo)]
        (let [new (remove seen (get edges x))]
          (recur (into seen new) (into (pop todo) new)))
        seen))))

;; ---- the prepared world -------------------------------------------------------

(defn- key-of
  "The stratification key of literal `l`: its functor, or `[:not functor]` for a denial."
  [l]
  (if (world/denial? l) [:not (first (second l))] (first l)))

(defn- covering?
  "Is `s` a `(covering Whole Part …)` declaration."
  [s]
  (and (seq? s) (= 'covering (first s))))

(defn- edges-of
  "The `[sub super]` edges sentence `s` installs in the genl closure: its own for a
  `(genl a b)`, one per part for a `(covering W P1 … Pn)` (docs/taxonomy.md, \"A cover
  states the specialization it rests on\"), none otherwise."
  [s]
  (cond (world/genl-edge? s) [[(second s) (nth s 2)]]
        (covering? s)        (for [p (drop 2 s)] [p (second s)])
        :else                []))

(defn- written-genl
  "`{sub #{super}}` over every edge a write of `world` installs, whatever its context or
  strength."
  [world]
  (reduce (fn [m [a b]] (update m a (fnil conj #{}) b))
          {} (mapcat (comp edges-of :sentence) (:writes world))))

(defn- closure-over
  "`x` plus every node `adj` reaches from it."
  [adj x]
  (loop [seen #{x} todo [x]]
    (if-let [y (peek todo)]
      (let [new (remove seen (get adj y))]
        (recur (into seen new) (into (pop todo) new)))
      seen)))

(defn- read-keys
  "The keys a literal read at key `k` depends on: through the written genl edges, a
  positive read of `p` is met by every sub-predicate of `p`, and a read of `[:not p]` by
  the denial of every super-predicate of `p` (docs/inference.md, \"Predicate subsumption
  in matching\")."
  [up-adj down-adj k]
  (if (vector? k)
    (map #(vector :not %) (closure-over up-adj (second k)))
    (closure-over down-adj k)))

(defn- strata
  "`{key stratum}` for the heads of `rules`: a head sits at or above every key a join
  antecedent reads, and strictly above every key an `unknown` or `exceptWhen` conjunct
  reads. Throws `:unsupported` when no assignment exists: the rule set is not
  stratified, which the engine refuses at assert (docs/naf.md, \"Stratification\")."
  [world rules]
  (let [up-adj   (written-genl world)
        down-adj (reduce-kv (fn [m a bs] (reduce #(update %1 %2 (fnil conj #{}) a) m bs))
                            {} up-adj)
        cons     (for [{:keys [parsed]} rules
                       :let [h (key-of (:consequent parsed))]
                       [lits d] [[(:antecedents parsed) 0]
                                 [(concat (apply concat (:unknowns parsed))
                                          (apply concat (:exceptions parsed))) 1]]
                       l lits
                       k (read-keys up-adj down-adj (key-of l))]
                   [h k d])
        bound    (+ 2 (count (into #{} (mapcat (fn [[h k _]] [h k])) cons)))]
    (loop [s {} n 0]
      (let [s' (reduce (fn [m [h k d]]
                         (let [need (+ d (get m k 0))]
                           (if (< (get m h 0) need) (assoc m h need) m)))
                       s cons)]
        (cond (= s' s) s
              (> n bound) (world/unsupported "the rule set is not stratified" {})
              :else (recur s' (inc n)))))))

(defn- prepare
  "The world, checked, and read into the tables the per-context computation uses:
  `:premises` `{S {home strength}}`, `:rules` (one entry per rule sentex, keyed by its
  bare form and its context), the genlCx `:edges`, the rule strata and the contexts."
  [world]
  (let [world    (world/check-world world)
        writes   (:writes world)
        premises (reduce (fn [m {:keys [sentence strength] :as w}]
                           (if (= :rule (world/write-kind sentence))
                             m
                             (update-in m [sentence (world/home w)]
                                        #(if % (strongest % strength) strength))))
                         {} writes)
        rules    (->> writes
                      (filter #(= :rule (world/write-kind (:sentence %))))
                      (map (fn [w] (assoc w :parsed (world/parse-rule (:sentence w)))))
                      (group-by (juxt (comp :rule :parsed) :context))
                      (map (fn [[[r k] ws]]
                             ;; every spelling in `ws` shares `:rule`, hence the joins,
                             ;; the unknowns and the consequent; the slots that differ
                             ;; are resolved from content, strict over defeasible
                             ;; (docs/canonicalization.md) and the exceptions unioned
                             (let [exc  (into #{} (mapcat (comp :exceptions :parsed)) ws)
                                   def? (every? (comp :defeasible? :parsed) ws)]
                               {:rule        r
                                :context     k
                                :parsed      (-> (:parsed (first ws))
                                                 (dissoc :direction)
                                                 (assoc :defeasible? def?
                                                        :exceptions (vec (sort-by pr-str exc))))
                                :defeasible? def?
                                :exceptions  exc})))
                      (sort-by #(pr-str [(:context %) (:rule %)])))
        st       (strata world rules)]
    {:world    world
     :premises premises
     :rules    (mapv #(assoc % :stratum (get st (key-of (:consequent (:parsed %))) 0)) rules)
     :edges    (context-edges world)
     :contexts (into (sorted-set) (concat (:contexts world) (world/contexts-of world)))}))

;; ---- matching -----------------------------------------------------------------

(defn- genl-adjacency
  "`{sub {super #{support}}}` over the edges the sentences of `believed` install: a
  believed `(genl a b)` supports its edge, and a believed `covering` supports the edge
  from each of its parts to its whole."
  [believed]
  (reduce (fn [m s]
            (reduce (fn [m [a b]] (update-in m [a b] (fnil conj #{}) s)) m (edges-of s)))
          {} believed))

(defn- genls-at
  "`t` plus every node the genl adjacency `adj` reaches from it."
  [adj t]
  (loop [seen #{t} todo [t]]
    (if-let [y (peek todo)]
      (let [new (remove seen (keys (get adj y)))]
        (recur (into seen new) (into (pop todo) new)))
      seen)))

(defn- genl-paths
  "Every simple path from `from` to `to` over `adj`, each as the set of believed
  sentences supporting its edges, one support chosen per edge. The empty path when
  `from` is `to`."
  [adj from to]
  (letfn [(walk [x seen]
            (if (= x to)
              [#{}]
              (for [[n sups] (get adj x)
                    :when (not (seen n))
                    sup  sups
                    path (walk n (conj seen n))]
                (conj path sup))))]
    (distinct (walk from #{from}))))

(defn- unify-args
  "`bindings` extended so the pattern arguments `ps` equal the constants `cs`, or nil."
  [bindings ps cs]
  (when (= (count ps) (count cs))
    (reduce (fn [b [p c]]
              (cond (world/variable? p) (let [v (get b p ::none)]
                                          (cond (= v ::none) (assoc b p c)
                                                (= v c) b
                                                :else (reduced nil)))
                    (= p c) b
                    :else (reduced nil)))
            bindings (map vector ps cs))))

(defn- matches
  "Every way the believed sentence `s` meets the literal pattern `l` under `bindings`,
  as `{:bindings b :edges #{…}}`. A positive pattern on `p` is met by a fact of any
  sub-predicate of `p`; a denial pattern on `p` by the denial of any super-predicate of
  `p`; each path over the believed `genl` edges between the two functors is its own match
  (docs/inference.md, \"Predicate subsumption in matching\"). Polarity never crosses. A
  positive match of a sub-predicate's fact is dropped where `(undercut? sub p args)`."
  [adj undercut? l s bindings]
  (let [neg? (world/denial? l)]
    (when (= neg? (world/denial? s))
      (let [[pf & pargs] (if neg? (second l) l)
            [sf & sargs] (if neg? (second s) s)]
        (when (and (not (world/genl-edge? (if neg? (second s) s)))
                   (not (world/genlCx-edge? (if neg? (second s) s)))
                   (not (world/declaration? (if neg? (second s) s))))
          (when-let [b (unify-args bindings pargs sargs)]
            (when-not (and (not neg?) (undercut? sf pf sargs))
              (for [path (if neg? (genl-paths adj pf sf) (genl-paths adj sf pf))]
                {:bindings b :edges path}))))))))

(defn- substitute
  "`form` with every variable `bindings` binds replaced."
  [form bindings]
  (cond (world/variable? form) (get bindings form form)
        (seq? form) (apply list (map #(substitute % bindings) form))
        (vector? form) (mapv #(substitute % bindings) form)
        :else form))

(defn- holds?
  "Is the ground literal `l` met by some sentence of `believed` (a positive literal
  through its sub-predicates, docs/naf.md \"Evaluated over the registry\"). `match` is
  `matches` over the adjacency and undercut of a context."
  [match believed l]
  (boolean (some #(seq (match l % {})) believed)))

(defn- join
  "Every way the literals `lits` are met in sequence by sentences of `believed`, as
  `{:bindings b :facts #{S …} :edges #{E …}}`."
  [match believed lits]
  (reduce (fn [partials l]
            (for [{:keys [bindings facts edges]} partials
                  s believed
                  m (match l s bindings)]
              {:bindings (:bindings m) :facts (conj facts s) :edges (into edges (:edges m))}))
          [{:bindings {} :facts #{} :edges #{}}]
          lits))

;; ---- derivation -------------------------------------------------------------

(defn- visible-rules
  "The rule sentexes of `prep` whose context is in `sees`, by stratum."
  [prep sees]
  (->> (:rules prep)
       (filter #(contains? sees (:context %)))
       (group-by :stratum)
       (sort-by key)
       (map val)))

(defn- blocked?
  "Is the firing of rule sentex `r` under `bindings` blocked at the view `believed`: an
  `unknown` whose conjuncts all hold, or an exception whose conjuncts all hold. Both
  are asked at the reading context (docs/reference.md, decision 4)."
  [match believed r bindings]
  (let [all-hold? (fn [conj] (every? #(holds? match believed (substitute % bindings)) conj))]
    (boolean (or (some all-hold? (:unknowns (:parsed r)))
                 (some all-hold? (:exceptions r))))))

(defn- fire-stratum
  "The fixpoint of the rule sentexes `rs` over `state` `{:believed #{S} :justs {S #{j}}}`.
  A justification is `{:rule [R K] :facts #{S} :edges #{E}}`. A conclusion in `out` is
  never added."
  [match rs out state]
  (loop [state state]
    (let [next (reduce
                (fn [st r]
                  (let [p (:parsed r)]
                    (reduce
                     (fn [st {:keys [bindings facts edges]}]
                       (let [c (substitute (:consequent p) bindings)
                             j {:rule [(:rule r) (:context r)] :facts facts :edges edges}]
                         (if (or (contains? out c)
                                 (contains? (get-in st [:justs c]) j)
                                 (blocked? match (:believed state) r bindings))
                           st
                           (-> st
                               (update :believed conj c)
                               (update-in [:justs c] (fnil conj #{}) j)))))
                     st
                     (join match (:believed state) (:antecedents p)))))
                state rs)]
      (if (= next state) state (recur next)))))

(defn- void-at?
  "Does rule sentex `r` conclude a literal in the forced-monotonic set `forced?` reads, or its denial,
  without being a forced-monotonic rule there: a `set/defaultRule`, an `unknown`, an exception, or
  an antecedent outside that set (docs/reference.md, decision 17)?"
  [forced? r]
  (let [{:keys [consequent antecedents unknowns]} (:parsed r)
        body (if (world/denial? consequent) (second consequent) consequent)]
    (boolean (and (forced? body)
                  (or (world/denial? consequent) (:defeasible? r) (seq unknowns)
                      (seq (:exceptions r)) (some #(not (forced? %)) antecedents))))))

(defn derive-at
  "The believed sentences at `c` when `out` is taken OUT, before inheritance: `{:believed
  #{S} :justs {S #{j}} :supports {S {home strength}} :sees up(c)}`. Each stratum of the
  visible rules fires to a fixpoint before the next. No rule reads an inherited claim
  (`world/check-world`), so derivation runs before `inherit-at`. `:forced?` reads
  `world/forced?` and the predicates a forced-monotonic declaration visible at `c` names,
  which only a forced-monotonic rule concludes (`void-at?`). A believed denial undercuts a
  subtype match with no `:monotonic` path, and the derivation repeats until the denials it
  reads are the ones it believes (docs/inference.md, \"An edge's reading\")."
  [prep c out]
  (let [sees     (up-with (:edges prep) c)
        vis      (fn [homes] (select-keys homes sees))
        ;; the predicates a forced-monotonic declaration visible at `c` makes forced-monotonic there
        declared (into #{} (keep (fn [[s homes]] (when (and (world/forced-declaration? s)
                                                            (seq (vis homes)))
                                                   (second s))))
                       (:premises prep))
        forced?  (fn [s] (or (world/forced? s) (and (seq? s) (contains? declared (first s)))))
        supports (into {} (for [[s homes] (:premises prep)
                                :when (not (contains? out s))
                                :let [v (vis homes)]
                                :when (seq v)]
                            [s v]))
        believed (set (keys supports))
        adj      (genl-adjacency believed)
        strict?  (fn [sup] (= :monotonic (some->> (get supports sup) vals (apply strongest))))
        derive   (fn [denied]
                   (let [undercut? (fn [sf pf args]
                                     (and (not= sf pf)
                                          (contains? denied (list 'not (apply list pf args)))
                                          (not-any? #(every? strict? %) (genl-paths adj sf pf))))
                         match     #(matches adj undercut? %1 %2 %3)]
                     (reduce (fn [st rs] (fire-stratum match (remove #(void-at? forced? %) rs) out st))
                             {:believed believed :justs {}}
                             (visible-rules prep sees))))
        denials  #(into #{} (filter world/denial?) %)
        d        (loop [denied (denials believed) n 0]
                   (let [d (derive denied) ends (denials (:believed d))]
                     (cond (= denied ends) d
                           (< n 8)         (recur ends (inc n))
                           :else           (throw (ex-info "the denials an undercut reads do not settle"
                                                           {:type :unsupported})))))]
    (assoc d :supports supports :sees sees :forced? forced?)))

;; ---- classes ------------------------------------------------------------------

(defn class-fixpoint
  "`{S class}` for every sentence the derivation `d` believes, the least fixpoint of
  docs/nmtms.md \"Strength propagates from the antecedents\":

  - a premise support holds at its write strength;
  - a justification confers the weakest of: `:default` when its rule is a
    `set/defaultRule` and `:monotonic` otherwise (the rule's own write strength does not
    cap), the class of each fact it matched, and the class of each sentence supporting a
    `genl` edge it climbed. The informant, a premise rule in every world this model reads,
    is out of the cap; its defeasibility is not;
  - a justification whose rule has an `unknown` antecedent or an `exceptWhen` confers
    `:default` whatever the other classes (docs/reference.md, decision 14);
  - the class of a sentence is the strongest of its supports.

  `matches` makes each `genl` route a firing climbs its own justification, so a
  conclusion over several routes takes the widest bottleneck (docs/reference.md,
  decision 9)."
  [prep {:keys [believed justs supports]}]
  (let [rules  (into {} (map (juxt (juxt :rule :context) identity)) (:rules prep))
        class0 (into {} (for [s believed]
                          [s (if-let [hs (get supports s)] (apply strongest (vals hs)) :default)]))
        cap    (fn [r] (if (or (:defeasible? r) (seq (:unknowns (:parsed r)))
                               (seq (:exceptions r)))
                         :default
                         :monotonic))
        conf   (fn [cls {:keys [rule facts edges]}]
                 (apply weakest (cap (get rules rule)) (map cls (concat facts edges))))]
    (loop [cls class0]
      (let [cj   (into {} (for [[s js] justs] [s (apply strongest (map #(conf cls %) js))]))
            cls' (merge-with strongest cls cj)]
        (if (= cls cls') cls (recur cls'))))))

;; ---- inherited claims -------------------------------------------------------

(defn- preserved-positions
  "`{P #{k}}` over the `(transitiveInArgInverse P k genl)` declarations in `believed`."
  [believed]
  (reduce (fn [m s]
            (if (and (seq? s) (= 'transitiveInArgInverse (first s)) (= 4 (count s)))
              (let [[_ p k r] s]
                (if (and (= 'genl r) (integer? k) (pos? k) (world/ordinary-predicate? p))
                  (update m p (fnil conj #{}) k)
                  m))
              m))
          {} believed))

(defn- genl-subs
  "`{super #{[sub edge]}}` over the `(genl sub super)` sentences in `believed`. A
  `covering` part edge is not among them: the inherited family reads the stated `genl`
  sentences only."
  [believed]
  (reduce (fn [m s]
            (if (world/genl-edge? s)
              (update m (nth s 2) (fnil conj #{}) [(second s) s])
              m))
          {} believed))

(defn- bottlenecks
  "`{sub class}` for every term strictly below `sup` over `subs`: the widest bottleneck
  over the routes from `sub` up to `sup`, the maximum over routes of the minimum `class`
  of the route's edges."
  [subs class sup]
  (loop [best {sup :monotonic}]
    (let [best' (reduce (fn [b [y cy]]
                          (reduce (fn [b [x e]]
                                    (let [old (get b x)
                                          new (weakest (class e) cy)
                                          new (if old (strongest old new) new)]
                                      (if (= old new) b (assoc b x new))))
                                  b (get subs y)))
                        best best)]
      (if (= best' best) (dissoc best sup) (recur best')))))

(defn- reaches
  "`[T class]` for every claim `T` one preserved position moves a claim `G` of `claims`
  to: `G` a tuple over a predicate `P` with `(transitiveInArgInverse P k genl)` in `believed`,
  and `T` the tuple `G` with the term at position `k` replaced by a term strictly below
  it over the `genl` sentences of `believed`. The class is the weakest of `G`'s class
  and the widest bottleneck of the routes (`bottlenecks`)."
  [believed class claims]
  (let [pos  (preserved-positions believed)
        subs (genl-subs believed)]
    (for [g     claims
          :when (and (seq? g) (contains? pos (first g)))
          k     (sort (get pos (first g)))
          :when (< k (count g))
          [sub c] (bottlenecks subs class (nth g k))]
      [(apply list (assoc (vec g) k sub)) (weakest (class g) c)])))

(defn- inherit-at
  "`{:believed :class :inherited}` at a context, from the derivation `d`, its classes
  `cls` and the OUT set `out` (docs/reference.md, item 4 of \"The function\").

  With `(transitiveInArgInverse P k genl)` believed, a believed claim `(P … sup …)` and
  `sub` strictly below `sup` over believed `genl` sentences, `(P … sub …)` is believed at
  the widest bottleneck of the claim's class and the route's edges (decision 9). The
  declaration caps nothing. Several declarations on one position union their reaches.
  The claim is not believed while its denial is believed, nor when a decision took it
  OUT; the inherited family (`vaelii.ref.nogoods/inherited`) takes a weaker denial OUT
  beside a `:monotonic` reading. `:inherited` holds only the sentences no write states
  and no rule derives.

  Readings the docs leave open, and the one taken here:

  - Two preserved positions on one predicate: each step moves one position, so `(P dog
    cat)` under both positions reaches `(P chi siamese)` through `(P chi cat)` or `(P
    dog siamese)`.
  - A denial of an intermediate tuple does not stop the route to `sub`.
  - A `covering` part edge carries no claim; only a stated `genl` sentence does.
  - The declaration is read for `P` itself and never for a sub-predicate of `P`."
  [d cls out]
  (let [base    (:believed d)
        denied? #(contains? base (list 'not %))]
    (loop [inh {}]
      (let [believed (into base (keys inh))
            class    (fn [s] (strongest (get cls s :default) (get inh s :default)))
            inh'     (reduce (fn [m [t c]]
                               (if (or (contains? out t) (denied? t))
                                 m
                                 (update m t #(if % (strongest % c) c))))
                             {} (reaches believed class believed))]
        (if (= inh' inh)
          {:believed  believed
           :class     (merge-with strongest cls inh)
           :inherited (into #{} (remove base) (keys inh))}
          (recur inh'))))))

;; ---- nogoods and decision -------------------------------------------------

(defn negation-nogoods
  "The negation family: one nogood `{:kind :negation :members #{S (not S)} :ground #{}}`
  for every believed denial whose body is believed too. The body is matched exactly;
  a denial of a supertype does not pair with a subtype's fact here
  (docs/nmtms.md, \"Soft, prioritized contradictions\": the pairs are keyed on one
  body stored in both polarities)."
  [{:keys [believed]}]
  (for [s believed
        :when (and (world/denial? s) (contains? believed (second s)))]
    {:kind :negation :members #{(second s) s} :ground #{}}))

(def ^:private merge-kinds
  "The nogood kinds a merge answers when every member is `:monotonic` (docs/reference.md
  D6)."
  #{:functional :functional-in-arg :anti-symmetric})

(defn- symbol-merge?
  "Is `ng` a nogood of a `merge-kinds` kind whose members are tuples of one arity that
  differ at one argument position or more, every differing argument a symbol."
  [ng]
  (let [ms (:members ng)]
    (boolean
     (and (contains? merge-kinds (:kind ng))
          (<= 2 (count ms))
          (every? seq? ms)
          (apply = (map count ms))
          (let [diff (remove #(apply = %) (apply map vector (map rest ms)))]
            (and (seq diff) (every? symbol? (apply concat diff))))))))

(defn decide
  "The verdict on nogood `ng` from its members' classes under `class`
  (docs/nmtms.md, \"Soft, prioritized contradictions\", step 3):

  - every member `:monotonic`, and `ng` a `:functional`, `:functional-in-arg` or
    `:anti-symmetric` nogood whose members differ only in symbol arguments: `:merge`,
    nobody OUT (docs/reference.md D6: the engine merges the two terms, and equality is
    outside the reference);
  - exactly one member a denial `(not S)` of a forced-monotonic member `S` (`forced?`,
    the set at the reading context; `world/forced?` when not given): `:defeat`, that
    denial is the `:loser` at either class (invariant 2);
  - no `:default` member outside the forced-monotonic set otherwise: `:hard`, nobody OUT,
    since a forced-monotonic member is never a loser (invariant 2);
  - exactly one `:default` member outside the set: `:defeat`, that member is the `:loser`;
  - two or more `:default` members outside the set: `:dilemma`, nobody OUT.

  The ground is not weighed. Defeat-class is the only axis (docs/nmtms.md, \"There is
  no second axis\"), so nothing breaks a tie."
  ([class ng] (decide class ng world/forced?))
  ([class ng forced?]
   (let [cs    (into {} (map (juxt identity class)) (:members ng))
         weak  (keep (fn [[s c]] (when (and (= :default c) (not (forced? s))) s)) cs)
         yield (filter #(and (world/denial? %) (contains? cs (second %)) (forced? (second %)))
                       (keys cs))]
     (cond (and (every? #{:monotonic} (vals cs)) (symbol-merge? ng)) (assoc ng :verdict :merge)
           (= 1 (count yield)) (assoc ng :verdict :defeat :loser (first yield))
           (empty? weak)      (assoc ng :verdict :hard)
           (= 1 (count weak)) (assoc ng :verdict :defeat :loser (first weak))
           :else              (assoc ng :verdict :dilemma)))))

(defn- check-nogood
  "`ng` when it is well formed at the view (members a non-empty set of believed
  sentences, ground a set), and a throw of `:bad-nogood` otherwise."
  [{:keys [believed]} ng]
  (when-not (and (keyword? (:kind ng)) (set? (:members ng)) (seq (:members ng))
                 (set/subset? (:members ng) believed) (set? (:ground ng)))
    (throw (ex-info "a family returned a nogood that is not well formed at this view"
                    {:type :bad-nogood :nogood ng})))
  ng)

(defn- ground-sentence?
  "Does the defeat of `s` withdraw something a clash is read through: a `genl` edge, a
  declaration, or a sentence some nogood of the round names as ground."
  [grounds s]
  (or (world/genl-edge? s) (world/declaration? s) (contains? grounds s)))

(defn- view-of
  "The view at `c` a family reads, from the derivation `d` and the inheritance `inh`."
  [c d {:keys [believed class inherited]}]
  (let [adj (genl-adjacency believed)]
    {:context   c
     :sees      (:sees d)
     :believed  believed
     :inherited inherited
     :class     (fn [s] (get class s))
     :genl      (fn [t] (genls-at adj t))}))

(defn- nogood-key [ng] (pr-str [(:kind ng) (sort-by pr-str (:members ng))]))

(defn resolve-at
  "The belief at `c` of the prepared world `prep`: the fixpoint of derivation and
  decision over a growing OUT set.

  Each round derives from the premises minus OUT, computes the classes and the inherited
  claims, gathers every nogood (negation plus `families`), and decides each. A defeat
  only adds to OUT. A round with any defeat whose loser is a ground (`ground-sentence?`)
  applies those defeats alone and re-enters. The loop stops at the round with no defeat,
  and OUT grows by at least one believed sentence per round, so it terminates
  (docs/reference.md, item 8 of \"The function\" and decision 2)."
  [prep c families]
  (loop [out #{} decided []]
    (let [d         (derive-at prep c out)
          cls       (class-fixpoint prep d)
          inh       (inherit-at d cls out)
          view      (view-of c d inh)
          ngs       (->> (concat (negation-nogoods view)
                                 (mapcat #(% view) families))
                         (map #(check-nogood view %))
                         (reduce (fn [m ng] (assoc m (nogood-key ng) ng)) {})
                         vals)
          verdicts  (map #(decide (:class view) % (:forced? d)) ngs)
          defeats   (filter #(= :defeat (:verdict %)) verdicts)]
      (if (empty? defeats)
        (assoc view
               :out out
               :nogoods (vec (sort-by nogood-key (concat decided verdicts))))
        (let [grounds (into #{} (mapcat :ground) ngs)
              first?  (filter #(ground-sentence? grounds (:loser %)) defeats)
              applied (if (seq first?) first? defeats)]
          (recur (into out (map :loser) applied) (into decided applied)))))))

;; ---- the entry points -----------------------------------------------------

(defn view
  "The view at context `c` of `world` once belief there is settled:
  `{:context :sees :believed :inherited :class :genl :out :nogoods}`. `:out` is the set
  of sentences a decision at `c` took OUT; `:nogoods` holds every nogood decided at `c`,
  each with its `:verdict` (and `:loser` for a `:defeat`). Throws `:unsupported` on a
  world outside the v1 fragment."
  [world c families]
  (resolve-at (prepare world) c families))

(defn believed?
  "Is the ground sentence `s` believed at context `c` of `world`, with the nogood
  `families` decided: the contract the engine is held to per sentence
  (docs/reference.md, \"The function\"). An inherited claim answers true as a stored
  sentence does.
  Computed from the prepared world at `c` alone; the reference answers by settling the
  whole view at `c`, which is correct and not local."
  [world s c families]
  (contains? (:believed (resolve-at (prepare world) c families)) s))

(defn believed-candidates
  "The sentences the reference answers at context `c` of `world`: every sentence
  believed there, every sentence a decision took OUT there, and every tuple a preserved
  position reaches from a believed claim, blocked by a denial or not. A harness asks
  `believed?` of each; a reached tuple that is not believed is a claim the engine's
  `ask?` must answer false."
  [world c families]
  (let [v (view world c families)]
    (-> (:believed v)
        (into (:out v))
        (into (map first) (reaches (:believed v) (constantly :monotonic) (:believed v))))))

(defn believe
  "`{C {:believed #{…} :inherited #{…} :out #{…} :nogoods […]}}` for every context of
  `world`: its `:contexts` and every context `world/contexts-of` finds. `:inherited` is
  the subset of `:believed` only inheritance supports (`inherit-at`). Deterministic and
  pure; the order of the writes is not read."
  [world families]
  (let [prep (prepare world)]
    (into (sorted-map)
          (for [c (:contexts prep)]
            [c (select-keys (resolve-at prep c families)
                            [:believed :inherited :out :nogoods])]))))
