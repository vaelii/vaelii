;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ref.world
  "The world a belief reference reads: the premises a KB stores, as a plain value.

  A world is `{:contexts #{…} :writes [{:sentence S :context C :strength s} …]}`. A write
  is a premise: a ground fact, a denial `(not S)`, a taxonomy edge, a definitional
  declaration, or a forward rule. A derived sentex is never a write. The order of
  `:writes` carries no meaning; the vector exists so a generator can permute it.

  `check-world` holds a world to the v1 fragment and throws `(ex-info … {:type
  :unsupported})` on anything outside it, so a generator or an extraction cannot produce
  a shape the reference does not model. The fragment, by write kind:

  - **fact**: `(p a1 … an)`, `p` an ordinary predicate (no entry in
    `vaelii.impl.predicates`, and none of the special words below), every argument a
    constant symbol.
  - **genl edge**: `(genl a b)`, two constant symbols.
  - **genlCx edge**: `(genlCx Sub Super)`, two `Cx…` symbols, written `:monotonic`. The
    genlCx edges together are acyclic.
  - **declaration**: `(d a1 … an)` with `d` in `declaration-predicates`, every argument a
    constant symbol or an integer. A `transitiveInArgInverse` declaration is `(transitiveInArgInverse
    P k genl)`, `P` an ordinary predicate and `k` a positive integer.
  - **denial**: `(not S)` with `S` a fact, a `genl` edge, a separation (`separations`),
    or a write of the forced-monotonic set.
  - **rule**: the shapes `parse-rule` accepts.

  **The forced-monotonic set** (`forced?`, docs/reference.md, \"Invariants the reference
  states\"): the functors of `forced-monotonic` and a `genl` between two predicates
  (`predicate-genl?`). A `genlCx` write is read `:monotonic` (`force-monotonic`). A rule
  concluding a forced-monotonic literal or its denial is stored and inert, never refused
  (`inert-write?`), and `check-world` sets it aside under `:inert`. v1 admits `genlCx`,
  the marks, `negates` and a predicate `genl`; the rest of the forced-monotonic set is
  outside v1. The separations `disjoint` and `covering` are defeasible, as a type `genl`
  edge is.

  Refused besides (`check-computed-reads`): a rule that reads a predicate some write
  declares `transitiveInArgInverse`, or a positive literal on a predicate the written `genl`
  edges put above one, because the engine satisfies such an antecedent with a claim
  nobody stored (docs/inference.md, \"Antecedents nothing stored\"), and an `unknown` or
  `exceptWhen` conjunct on a part of some `covering`, which level 6 answers through
  `CoveringProver`. The reference models neither reading.

  **A forced-monotonic declaration** `(forced_monotonic_predicate T)` of an ordinary type `T`
  (`forced-declaration?`) makes `T` forced-monotonic at the contexts that see it and nowhere
  else (docs/reference.md, decision 17; `vaelii.ref.believe/derive-at`)."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.impl.predicates :as predicates]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]))

(def strengths
  "The two assumption strengths a write may carry (docs/nmtms.md, \"Strengths and the
  defeat-class\")."
  #{:monotonic :default})

(def declaration-predicates
  "The definitional declarations v1 admits. Each is read by a nogood family
  (`vaelii.ref.nogoods`), never by derivation."
  '#{disjoint covering functional functionalInArg irreflexive anti_symmetric asymmetric
     anti_transitive negates transitiveInArgInverse})

(def separations
  "The separations v1 admits: declarations a nogood family reads as grounds, each kept at
  the strength it was written at and defeated like a type `genl` edge (docs/reference.md,
  invariant 6)."
  '#{disjoint covering})

(def forced-monotonic
  "The functors whose every write is never a loser, whose denial loses its negation nogood
  at either strength, and which a v1 rule concludes only inertly (docs/reference.md,
  invariants 1, 2 and 6 to 8).  `injective_predicate`, `surjective_predicate`, `bijective_predicate`, the arity
  bindings, `except`, `rewriteOf`, `sameAs` and `equals` are outside v1, and
  `write-kind` refuses a write of one."
  '#{genlCx irreflexive anti_symmetric asymmetric functional functionalInArg
     anti_transitive negates injective_predicate surjective_predicate bijective_predicate arity unary binary ternary unary_predicate
     binary_predicate ternary_predicate unary_function binary_function ternary_function
     variable_arity variable_arity_predicate variable_arity_function arityMin except
     rewriteOf sameAs equals})

(def ^:private direction-wrappers
  '{set/forwardRule :forward, set/forwardOnlyRule :forward-only})

(def ^:private refused-wrappers
  '#{set/backwardRule set/inertRule set/solveRule set/assumptionRule set/hardConstraint
     set/softConstraint set/monotonic set/inert})

(def ^:private special-words
  (into '#{not and implies unknown exceptWhen genl genlCx thereExists forall}
        (concat declaration-predicates forced-monotonic (keys direction-wrappers)
                refused-wrappers
                ['set/defaultRule])))

(defn unsupported
  "Throw the refusal every v1 check throws: `ex-info` with `:type :unsupported`, the
  message `msg`, and `data`."
  [msg data]
  (throw (ex-info msg (assoc data :type :unsupported))))

(defn variable?
  "Is `x` a variable: a symbol whose name starts with `?`."
  [x]
  (and (symbol? x) (str/starts-with? (name x) "?")))

(defn context-term?
  "Is `x` a context name: a symbol spelled `Cx` followed by an uppercase letter."
  [x]
  (and (symbol? x) (boolean (re-matches #"Cx[A-Z].*" (name x)))))

(defn ordinary-predicate?
  "Is `f` a predicate the engine does not interpret: a constant symbol that is not a
  special word of v1 and has no entry in `vaelii.impl.predicates`."
  [f]
  (and (symbol? f) (not (variable? f)) (not (contains? special-words f))
       (nil? (predicates/entry f))))

(defn denial?
  "Is `s` a denial `(not S)`."
  [s]
  (and (seq? s) (= 'not (first s)) (= 2 (count s))))

(defn genl-edge?
  "Is `s` a `(genl a b)` edge."
  [s]
  (and (seq? s) (= 'genl (first s)) (= 3 (count s))))

(defn genlCx-edge?
  "Is `s` a `(genlCx Sub Super)` edge."
  [s]
  (and (seq? s) (= 'genlCx (first s)) (= 3 (count s))))

(defn declaration?
  "Is `s` a declaration whose functor is in `declaration-predicates`."
  [s]
  (and (seq? s) (contains? declaration-predicates (first s))))

(defn camel-case-predicate?
  "Is `x` spelled as a predicate of arity 2 or more: a symbol that starts lowercase and
  holds an uppercase letter after its first character (docs/naming.md). A bare lowercase
  word such as `dog` satisfies the type spelling as well, and is taken as a type here."
  [x]
  (and (symbol? x) (boolean (re-matches #"[a-z][a-zA-Z0-9]*[A-Z][a-zA-Z0-9]*" (name x)))))

(defn predicate-genl?
  "Is `s` a `(genl P Q)` edge between two `camel-case-predicate?` terms, the forced-monotonic
  spelling (docs/reference.md, invariant 5)?"
  [s]
  (and (genl-edge? s) (every? camel-case-predicate? (rest s))))

(defn forced?
  "Is the sentence `s` in the baseline forced-monotonic set: its functor is in
  `forced-monotonic`, or `s` is a `predicate-genl?` edge."
  [s]
  (and (seq? s) (or (contains? forced-monotonic (first s)) (predicate-genl? s))))

(defn forced-declaration?
  "Is `s` a `(forced_monotonic_predicate T)` declaration of an ordinary predicate `T`."
  [s]
  (and (seq? s) (= 'forced_monotonic_predicate (first s)) (= 2 (count s))
       (ordinary-predicate? (second s))))

(defn- literal?
  "Is `l` an atomic formula over an ordinary predicate whose arguments are constant
  symbols, integers, strings or (when `open?`) variables.  An integer or a string is a
  filler a `functional` position can hold without a merge (a symbol pair there is an
  equality, outside v1)."
  [l open?]
  (and (seq? l) (>= (count l) 2) (ordinary-predicate? (first l))
       (every? #(or (integer? %) (string? %)
                    (and (symbol? %) (or open? (not (variable? %)))))
               (rest l))))

(defn- signed-literal?
  "Is `l` a literal or the denial of one."
  [l open?]
  (if (denial? l) (literal? (second l) open?) (literal? l open?)))

(defn vars-of
  "The variables `form` mentions, as a set."
  [form]
  (cond (variable? form) #{form}
        (or (seq? form) (vector? form)) (into #{} (mapcat vars-of) form)
        :else #{}))

(defn- peel
  "`[direction defeasible? exception-conjuncts inner]` of a rule form: the wrappers
  stripped in any nesting order. Two `exceptWhen`s written together conjoin, as the
  engine's `sentex/peel-rule-wrapper` reads them."
  [form]
  (loop [f form, dir nil, def? false, exc nil]
    (let [h (when (and (seq? f) (seq f)) (first f))]
      (cond
        (contains? direction-wrappers h)
        (let [d (direction-wrappers h)]
          (when (and dir (not= dir d))
            (unsupported "two direction wrappers around one rule" {:sentence form}))
          (recur (second f) d def? exc))
        (= 'set/defaultRule h) (recur (second f) dir true exc)
        (and (= 'exceptWhen h) (= 3 (count f)))
        (let [q (second f)]
          (recur (nth f 2) dir def? (into (or exc []) (if (vector? q) q [q]))))
        (contains? refused-wrappers h)
        (unsupported (str h " is outside the v1 fragment") {:sentence form})
        :else [dir def? exc f]))))

(defn- unknown-conjuncts
  "The conjunct literals of an `(unknown X)` antecedent, or nil when `item` is not one."
  [item]
  (when (and (seq? item) (= 'unknown (first item)) (= 2 (count item)))
    (let [x (second item)]
      (if (and (seq? x) (= 'and (first x))) (vec (rest x)) [x]))))

(defn parse-rule
  "Parse a v1 rule form into
  `{:rule R :direction d :defeasible? b :antecedents [L …] :unknowns [[L …] …]
  :consequent C :exceptions [[L …] …]}`, or throw `:unsupported`.

  `:rule` is the bare `(implies …)` with every wrapper removed; it and the write's context
  identify the rule sentex, so two spellings of one rule are one rule only when their
  bare forms are `=`. `:antecedents` are the join literals (a literal or a denial of one,
  variables allowed). `:unknowns` holds one conjunct vector per `(unknown …)` antecedent.
  `:exceptions` holds the one conjunct vector the `exceptWhen` wrappers of this form
  conjoin into, or is empty.

  The accepted shape follows docs/inference.md (\"Rules are sentexes\", \"Rule
  direction\"), docs/naf.md (\"In a rule antecedent\") and docs/exceptions.md (\"The
  exception is a query, not a literal\"):

  - wrappers in any order: exactly one forward direction (`set/forwardRule` or
    `set/forwardOnlyRule`), optionally `set/defaultRule`, optionally `(exceptWhen Q R)`
    with `Q` a literal or a vector of literals. A bare `implies` is backward-only, which
    stores no conclusion, and is refused, as are the other `set/*` wrappers.
  - `(implies A C)`, `A` one antecedent or `(and A1 A2 …)`, no nested `and`.
  - an antecedent is a literal or its denial over an ordinary predicate, or
    `(unknown L)` / `(unknown (and L1 L2 …))` over positive literals. A negated literal
    inside `unknown` or `exceptWhen` is refused: the engine answers one there through
    level-6 provers (disjointness among them) the reference does not model.
  - `C` is a literal or its denial over an ordinary predicate, or a member of the
    forced-monotonic set (`forced?`) or its denial. A rule concluding a forced-monotonic member
    parses with `:inert? true` (docs/reference.md, decision 17). A rule concluding a
    type-level `genl` or a rule is refused as outside v1.
  - at least one join antecedent; every variable of `C`, of each `unknown` and of the
    exception occurs in a join antecedent (range restriction and closure)."
  [form]
  (let [[dir def? exc inner] (peel form)]
    (when-not (and (seq? inner) (= 'implies (first inner)) (= 3 (count inner)))
      (unsupported "not a rule form" {:sentence form}))
    (when-not dir
      (unsupported "a rule with no forward direction wrapper is backward-only or inert"
                   {:sentence form}))
    (let [[_ ante conseq] inner
          items    (if (and (seq? ante) (= 'and (first ante))) (vec (rest ante)) [ante])
          unknowns (into [] (keep unknown-conjuncts) items)
          joins    (into [] (remove unknown-conjuncts) items)
          bound    (vars-of joins)]
      (when (some #(and (seq? %) (= 'and (first %))) items)
        (unsupported "a nested conjunction in an antecedent" {:sentence form}))
      (when (empty? joins)
        (unsupported "a rule with no join antecedent" {:sentence form}))
      (when-not (every? #(signed-literal? % true) joins)
        (unsupported "a join antecedent outside the v1 literals" {:sentence form}))
      (when-not (every? #(literal? % true) (concat (apply concat unknowns) exc))
        (unsupported "an unknown or exceptWhen conjunct outside the positive v1 literals"
                     {:sentence form}))
      (when-not (or (signed-literal? conseq true)
                    (forced? (if (denial? conseq) (second conseq) conseq)))
        (unsupported "a consequent outside the v1 literals" {:sentence form}))
      (when-not (set/subset? (vars-of [conseq unknowns exc]) bound)
        (unsupported "a variable no join antecedent binds" {:sentence form}))
      {:rule        inner
       :direction   dir
       :defeasible? def?
       :antecedents joins
       :unknowns    unknowns
       :consequent  conseq
       :exceptions  (if (seq exc) [exc] [])
       :inert?      (forced? (if (denial? conseq) (second conseq) conseq))})))

(defn rule-form?
  "Does `s` look like a rule form: an `implies` under zero or more wrappers."
  [s]
  (and (seq? s)
       (or (= 'implies (first s)) (= 'exceptWhen (first s)) (= 'set/defaultRule (first s))
           (contains? direction-wrappers (first s)) (contains? refused-wrappers (first s)))))

(defn write-kind
  "The kind of the sentence `s`: `:rule`, `:genlCx`, `:genl`, `:declaration`,
  `:forced-declaration`, `:denial` or `:fact`. Throws `:unsupported` for a sentence outside the v1 fragment."
  [s]
  (cond
    (rule-form? s) (do (parse-rule s) :rule)
    (genlCx-edge? s)
    (if (every? context-term? (rest s))
      :genlCx
      (unsupported "a genlCx edge between non-context terms" {:sentence s}))
    (genl-edge? s)
    (if (every? #(and (symbol? %) (not (variable? %))) (rest s))
      :genl
      (unsupported "a genl edge between non-constant terms" {:sentence s}))
    (forced-declaration? s) :forced-declaration
    (declaration? s)
    (if (every? #(or (integer? %) (and (symbol? %) (not (variable? %)) (not= 'genlCx %)))
                (rest s))
      :declaration
      (unsupported "a declaration argument outside the v1 fragment" {:sentence s}))
    (denial? s)
    (let [b (second s)]
      (if (or (literal? b false) (genl-edge? b) (forced? b)
              (and (seq? b) (contains? separations (first b))))
        (do (write-kind b) :denial)
        (unsupported "a denial outside the v1 fragment" {:sentence s})))
    (literal? s false) :fact
    :else (unsupported "a sentence outside the v1 fragment" {:sentence s})))

(defn write
  "A write of `sentence` in `context` at `strength` (`:default` when omitted, the
  engine's default)."
  ([sentence context] (write sentence context :default))
  ([sentence context strength]
   (when-not (contains? strengths strength)
     (unsupported "a strength outside :monotonic / :default" {:strength strength}))
   {:sentence sentence :context context :strength strength}))

(defn home
  "The context the engine stores write `w` in: the write's own context, a genlCx edge
  included. The engine moves every genlCx edge into CxUniverse only while
  `(forced_decontextualized_predicate genlCx)` is stored (docs/contexts.md,
  \"forced_decontextualized_predicate\"), which CxUniverse's vocabulary asserts and v1
  refuses, so a v1 KB holds an edge where it was written."
  [w]
  (:context w))

(defn contexts-of
  "Every context the writes of `world` name: each write's storage context (`home`) and
  both ends of every genlCx edge."
  [world]
  (into (sorted-set)
        (mapcat (fn [{:keys [sentence] :as w}]
                  (cons (home w) (when (genlCx-edge? sentence) (rest sentence)))))
        (:writes world)))

(defn from-writes
  "The world whose writes are `writes`, with `:contexts` from `contexts-of`."
  [writes]
  (let [w {:writes (vec writes)}]
    (assoc w :contexts (contexts-of w))))

(defn- check-acyclic-contexts
  "Throw `:unsupported` when the genlCx edges of `writes` close a cycle."
  [writes]
  (let [adj   (reduce (fn [m [_ a b]] (update m a (fnil conj #{}) b)) {}
                      (filter genlCx-edge? (map :sentence writes)))
        reach (fn reach [seen c]
                (reduce (fn [s n] (if (s n) s (reach (conj s n) n))) seen (adj c)))]
    (doseq [c (keys adj)]
      (when (contains? (reach #{} c) c)
        (unsupported "the genlCx edges close a cycle" {:context c})))))

(defn- written-subs
  "`{super #{sub}}` over the edges the writes of `writes` install in the genl closure: one
  per `(genl a b)`, and one from each part to the whole of a `(covering W P1 … Pn)`,
  whatever the write's context or strength."
  [writes]
  (reduce (fn [m s]
            (cond (genl-edge? s) (update m (nth s 2) (fnil conj #{}) (second s))
                  (and (seq? s) (= 'covering (first s)))
                  (reduce #(update %1 (second s) (fnil conj #{}) %2) m (drop 2 s))
                  :else m))
          {} (map :sentence writes)))

(defn- below
  "`t` and every term the adjacency `subs` reaches from it."
  [subs t]
  (loop [seen #{t} todo [t]]
    (if-let [y (peek todo)]
      (let [new (remove seen (get subs y))]
        (recur (into seen new) (into (pop todo) new)))
      seen)))

(defn- check-computed-reads
  "Throw `:unsupported` when a rule of `writes` reads a predicate whose answers the
  engine computes rather than stores: any literal of a rule on a predicate some write
  declares `transitiveInArgInverse`, a positive literal on a predicate the written genl edges
  put above such a predicate (a read of `q` is met by the facts of every predicate below
  `q`, docs/inference.md, \"Predicate subsumption in matching\"), and an `unknown` or
  `exceptWhen` conjunct on a part some `covering` write names, which level 6's
  `CoveringProver` answers (docs/inference.md, \"The pluggable prover engine\")."
  [writes]
  (let [sentences (map :sentence writes)
        preserved (into #{} (keep #(when (and (seq? %) (= 'transitiveInArgInverse (first %)))
                                     (second %)))
                        sentences)
        subs      (written-subs writes)
        parts     (into #{} (mapcat #(when (and (seq? %) (= 'covering (first %))) (drop 2 %)))
                        sentences)
        functor   #(first (if (denial? %) (second %) %))
        reads-preserved? (fn [l]
                           (or (contains? preserved (functor l))
                               (and (not (denial? l))
                                    (some preserved (below subs (functor l))))))]
    (doseq [s sentences
            :when (= :rule (write-kind s))
            :let [{:keys [antecedents unknowns exceptions consequent]} (parse-rule s)
                  queries (concat (apply concat unknowns) (apply concat exceptions))]]
      (when-let [l (first (filter reads-preserved? (concat antecedents queries)))]
        (unsupported "a rule reads a predicate declared transitiveInArgInverse, or one above it"
                     {:sentence s :literal l :consequent consequent}))
      (when-let [f (some parts (map functor queries))]
        (unsupported "an unknown or exceptWhen reads a covering part"
                     {:sentence s :predicate f})))))

(defn inert-write?
  "Is write `w` one the forced-monotonic set makes inert (docs/reference.md, decision 17):
  a rule concluding a `forced?` sentence or its denial, whose every firing the engine
  holds void?"
  [{:keys [sentence]}]
  (and (rule-form? sentence) (:inert? (parse-rule sentence))))

(defn- check-transitive-in-arg
  "Throw `:unsupported` when write `w` is a `transitiveInArgInverse` declaration other than
  `(transitiveInArgInverse P k genl)` over an ordinary predicate `P` and a positive integer `k`."
  [{:keys [sentence] :as w}]
  (let [f (when (seq? sentence) (first sentence))]
    (when (= 'transitiveInArgInverse f)
      (let [[_ p k r] sentence]
        (when-not (and (= 4 (count sentence)) (ordinary-predicate? p) (integer? k) (pos? k)
                       (= 'genl r))
          (unsupported "a transitiveInArgInverse declaration other than (transitiveInArgInverse P k genl)"
                       {:write w}))))))

(defn force-monotonic
  "`write` with its strength set to `:monotonic` when its sentence is a `genlCx` edge, as
  the engine's labeller reads one (docs/reference.md, invariant 1); any other write
  unchanged."
  [{:keys [sentence] :as write}]
  (if (genlCx-edge? sentence)
    (assoc write :strength :monotonic)
    write))

(defn check-world
  "Throw `:unsupported` unless every write of `world` is inside the v1 fragment (the
  namespace docstring), and return `world` with its `inert-write?` writes moved from
  `:writes` to `:inert` and every `genlCx` write read `:monotonic` (`force-monotonic`).
  The fragment's structural checks read the writes that stay."
  [world]
  (let [ws (:writes world)]
    (doseq [{:keys [sentence context strength] :as w} ws]
      (when-not (and (map? w) (context-term? context) (contains? strengths strength))
        (unsupported "a write without a context term and a strength" {:write w}))
      (check-transitive-in-arg w)
      (write-kind sentence))
    (let [{inert true live false} (group-by (comp boolean inert-write?) ws)
          live (vec live)]
      (check-acyclic-contexts live)
      (check-computed-reads live)
      (assoc world
             :writes (mapv force-monotonic live)
             :inert  (vec inert)))))

;; ---- extraction from a KB ---------------------------------------------------

(defn- rule-write-sentence
  "The authored form of the rule sentex `rx`: its canonical sentence under the wrappers
  its record fields spell. Throws `:unsupported` for a rule the forward chainer does not
  run."
  [rx]
  (when-not (and (= :derive (:effect rx)) (contains? (set (:engines rx)) :forward)
                 (not (contains? (set (:engines rx)) :solve)))
    (unsupported "a stored rule that does not forward-chain"
                 {:sentence (sx/sentence-of rx) :engines (:engines rx)}))
  (rules/rewrap-sentex (sx/sentence-of rx) rx))

(defn- premise-sentence
  "The write sentence of the stored premise `x`, read off `records`."
  [records x]
  (let [s (sx/sentence-of x)]
    (cond
      (some? (:antecedent x)) (rule-write-sentence x)
      (sx/exceptWhen-meta? s)
      (let [rx (p/get-sentex records (sx/exceptWhen-rule-handle s))
            cs (sx/exception-query-conjuncts s)]
        (when-not (and rx (= (:context rx) (:context x)))
          (unsupported "an exceptWhen stored apart from its rule" {:sentence s}))
        (list 'exceptWhen (if (= 1 (count cs)) (first cs) (vec cs))
              (rule-write-sentence rx)))
      :else s)))

(defn- content-key
  "A printed key for ordering writes on content."
  [w]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (pr-str [(:context w) (:sentence w) (:strength w)])))

(defn world-of
  "The world `kb` stores: one write per premise sentex, with the sentex's context and
  its recorded premise strength, in content order. A derived sentex is not a premise and
  is not a write; a rule is a premise and is. An `exceptWhen` meta-sentex becomes the
  `(exceptWhen Q R)` write that stores it, beside the write of `R` itself. Throws
  `:unsupported` on anything outside the v1 fragment (`check-world`)."
  [kb]
  (let [records (:records kb)
        writes  (for [h (sort (p/premise-ids records))
                      :let [x (p/get-sentex records h)]
                      :when x]
                  (write (premise-sentence records x) (:context x)
                         (p/premise-strength records h)))]
    (check-world (from-writes (sort-by content-key writes)))))
