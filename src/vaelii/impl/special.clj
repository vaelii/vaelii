;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.special
  "The special-predicate dispatch table: what each functor the engine interprets
  *does* to the derived state around the store, stated once, with every half of every
  behaviour side by side.

  A special predicate needs behaviour in four places — reflecting a stored sentex
  into the caches, the removal mirror, `recover`'s cache-only replay, and `wff`'s
  per-functor well-formedness check — and the compiler cross-checks none of them, so
  the arms live once here, in `arms`, keyed by functor:

    :integrate    (fn [kb sentex handle])  reflect a newly stored sentex into the caches
    :disintegrate (fn [kb sentex])         the mirror, reference-counted on (:id sentex)
    :rebuild      (fn [tax sentex])        recover's cache-only replay — no re-check
                                           posting, no migration, no universal lifting,
                                           because the store already holds what those
                                           side effects produced
    :wff          (fn [tax sentence context]) structural well-formedness (vaelii.impl.wff
                                           keeps the check fns; the table points at them.
                                           `context` scopes the arms that read it — today
                                           only `disjoint-problems`)

  and `check-entries` refuses an asymmetric entry **at namespace load**, so an
  add-side arm without its removal and rebuild halves is a build failure rather
  than a cache that drifts on the first retraction or restart.

  **The enumeration is not here.**  Which functors the engine interprets, in what
  order, what each one *says* — its sentence shape, the `:props` kind it maintains,
  whether its arms run on the derivation path — is one entry per term in
  `vaelii.impl.predicates`, which requires nothing and so can be read by `taxonomy`,
  `wff` and `provers`, none of which can read this namespace.  That split is what
  lifts the four-place ceiling above: the arms need functions from four layers and
  can only ever live at layer three, while what a predicate *says* is needed at every
  layer there is.  `entries` joins the two, `check-declarations` refuses a
  disagreement, and `predicates_test` checks the join against the live tables.

  `structural-integrate` stays outside that framework permanently and no declaration
  can name its arms: they dispatch on a sentence's *shape* rather than on its functor
  — a rule, an `exceptWhen` meta, a visibility `except`, and a disjoint metatype's
  member, whose functor is the metatype and so is data rather than vocabulary.

  What this namespace still owns is everything the arms are and everything they need:
  all four arm columns, the five walks over them, the exception re-check queue the
  taxonomy arms post to, the universal-predicate lifting, and the equality migration.
  Third layer of the engine stack (kb <- checks <- special <- integrate <- chain <-
  settle): everything here reads kb and checks, and the store-mutation choke points in
  `vaelii.impl.integrate` sit directly above."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.except :as exc]
            [vaelii.impl.graph :as graph]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]
            [vaelii.impl.wff :as wff]))

;; ## The exception re-check queue
;;
;; These forms queue rule handles into `(reasoning/recheck kb)` as `{rule-handle ->
;; triggers}`: a sentence, a withdrawal marker, `:all` or `:all-rejoin`.  See
;; docs/exceptions.md, "The re-check index".

(def ^:dynamic *recheck-reads*
  "nil, or a volatile `{key rule-handles}` of the watched rules a re-check trigger reads
  for one predicate, which `recheck-read` answers from.  A sweep that mints many
  memberships of few types binds one (`with-recheck-reads`), as does
  `chain/sync-arity-classes!` placing class memberships: each placement posts the trigger
  of its type, and the rules read for a type are the same for every placement of it.  The key
  carries the `genl` generation, since a sweep can mint a `genl` edge (`genlArg`); the
  sweeps store no rule and no declaration a read here names."
  nil)

(defmacro with-recheck-reads
  "Run `body` with a `*recheck-reads*` memo, the one already bound if there is one.  The
  caller's body stores no rule and no declaration."
  [& body]
  `(binding [*recheck-reads* (or *recheck-reads* (volatile! {}))] ~@body))

(defn- recheck-read
  "`(f)`, the watched rules a trigger reads under `k`, answered from `*recheck-reads*`
  when bound."
  [kb k f]
  (if-let [m *recheck-reads*]
    (let [tax (reasoning/taxonomy kb)
          k   (conj k (tax/relation-epoch tax) (tax/relation-gen tax :genl))]
      (caches/get-or! m k f))
    (f)))

(defn- mark-recheck
  "Queue `rule-handles` for exception re-evaluation at the next `settle`, recording
  `trigger`: the sentence whose arrival or departure could have flipped the exception, a
  withdrawal marker, `:all` when every firing must be re-checked, or `:all-rejoin` when
  that check must also force a fresh join.

  The unconditional markers are absorbing, and `:all-rejoin` is the stronger one: adding
  a narrower trigger does not narrow it back.  `:all` meeting a `{::nonempty types}`
  marker is `:all-rejoin`, since that move owes its re-join."
  [kb rule-handles trigger]
  (when (seq rule-handles)
    (swap! (reasoning/recheck kb)
           (fn [m]
             (reduce (fn [m rh]
                       (let [cur (get m rh)]
                         (assoc m rh
                                (cond
                                  (or (= :all-rejoin cur) (= :all-rejoin trigger))
                                  :all-rejoin

                                  (or (= :all cur) (= :all trigger))
                                  (if (some ::nonempty (cons trigger (when (set? cur) cur)))
                                    :all-rejoin
                                    :all)

                                  :else (conj (or cur #{}) trigger)))))
                     m rule-handles)))))

(defn- answered-predicates
  "The predicates whose goals a fact on `pred` answers, by the global closure: `pred`'s
  supertypes across `genl` and `genlInverse` edges (`rules/signed-reach`), and those of every
  predicate an `inverse` declares of one of them, since `(inverse P Q)` answers a `Q`
  goal from a `P` tuple.  The `genls` closure on a KB declaring neither.  Unscoped, for
  `recheck-declaration`'s reason."
  [tax pred]
  (let [ups (rules/signed-reach tax :up pred)]
    (into ups (comp (mapcat #(tax/inverses-of tax %)) (mapcat #(rules/signed-reach tax :up %))) ups)))

(def ^:private declaration-subjects
  "Declaration functors, mapped to the argument positions naming a predicate the
  declaration licenses a level-6 answer **about** without touching its extent.
  `predicates/check-facets` reads the absent functors in three groups, listed in
  docs/exceptions.md, \"Five channels\"."
  '{transitive           [1]
    symmetric            [1]
    asymmetric           [1]
    reflexive            [1]
    commutative              [1]
    commutativeInArgs        [1]
    commutativeInArgAndRest  [1]
    inverse              [1 2]
    negates              [1 2]
    genlInverse          [2]
    transitiveInArgInverse [1]
    transitiveInArg        [1]})

(def recheck-subjects
  "`declaration-subjects`' functors as a set — which declarations post to the exception
  re-check queue through the shared path rather than from arms of their own.

  Public because `predicates/check-facets` holds every declaration that answers goals
  about a predicate to posting by one route or the other, and the two routes live in
  different namespaces: a `:retriggers` facet says the arms do it, this says
  `recheck-declaration` does.  A declaration in neither decides by arrival order, which
  is what that rule refuses at load."
  (set (keys declaration-subjects)))

(def ^:private opaque-negated-body-functors
  "Functors under a `not` that `recheck-negated-exceptions` cannot key on, because the
  negation is over a *frame* rather than over a literal and the predicates that decide
  it are the frame's, at whatever depth.  A rule carrying one is queued rather than
  reasoned about.  `sx/connective-problems` refuses a condition negating `unknown`,
  `thereExists` or `forall`, so none of the three is here."
  '#{and or implies exceptWhen ist})

(defn- negated-block-literals
  "The `not`-headed literals among rule `rh`'s re-check conditions: its believed
  `exceptWhen` conjuncts, its `unknown` antecedents' queries and its aggregate bodies,
  each read through `rules/watched-literals`, since a joined census body is a
  conjunction."
  [kb rh]
  (let [rsx (p/get-sentex (:records kb) rh)]
    (filterv #(and (sequential? %) (= 'not (nm/functor %)))
             (concat (apply concat (provers/rule-exceptions kb rh))
                     (when rsx (rules/naf-queries rsx))
                     (when rsx (mapcat rules/watched-literals (rules/aggregate-queries rsx)))))))

(defn- negation-under-moved-closure?
  "Could a `genl` edge whose subtype's spec closure is `below` flip one of rule `rh`'s
  negated re-check conditions?  Matching under a negation walks the up-closure of the
  conjunct's own predicate, and an edge `[sub super]` moves that closure for the
  predicates at or below `sub`, so a condition whose body's functor is in `below`
  answers yes.  `below` is the same set before and after the edge, since an edge putting
  `sub` above `super` is a refused cycle.  Answers **keep** where it cannot read the
  conjunct: a variable or compound functor, a frame (`opaque-negated-body-functors`),
  or a rule under `not` whose conditions it cannot find."
  [kb rh below]
  (let [lits (negated-block-literals kb rh)]
    (or (empty? lits)
        (boolean (some (fn [lit]
                         (let [f (nm/functor (sx/underlying-body lit))]
                           (or (not (symbol? f))
                               (contains? opaque-negated-body-functors f)
                               (contains? below f))))
                       lits)))))

(defn- negated-rechecks
  "The rules watched under `not` whose negated re-check condition a move at the
  predicates `moved` can reach: `negation-under-moved-closure?` over `moved` and their
  specs.  The specs are the unscoped closure, since a trigger over-approximates
  (`recheck-declaration`).  One record read per such rule, and none for a KB with none."
  [kb moved]
  (let [tx    (reasoning/taxonomy kb)
        below (into #{} (mapcat #(tax/specs-global tx %)) moved)]
    (filterv #(negation-under-moved-closure? kb % below)
             (reads/watched-rules-on (:index kb) 'not))))

(defn- recheck-negated-exceptions
  "Queue `:all` the `negated-rechecks` of a move at `sub`: a `genl` edge with subtype
  `sub`, or a declaration about `sub` (`recheck-declaration`), which answers a denial on
  `sub` and on the predicates below it."
  [kb sub]
  (when (seq (reads/watched-rules-on (:index kb) 'not))
    (mark-recheck kb (negated-rechecks kb [sub]) :all)))

(defn- recheck-preserving-along
  "`rel` is the relation of some `(transitiveInArg P n rel)` declaration and its extent
  just moved: a fact on it arrived or left, or it is `genl` / `genlCx` and an edge moved.
  Queues every rule whose exception mentions a declaring `P`, and the `negated-rechecks`
  of a move at `P`, which a denial reached along `rel` answers, as `:all`, since the
  sentence is on `rel` and the exception on `P` (docs/inherit.md, \"Four things that
  follow from reading claims out of belief\")."
  [kb rel]
  (let [idx (:index kb)]
    (mark-recheck kb (recheck-read kb [::along rel]
                                   #(let [ps (into #{} (comp (filter (fn [[_ r]] (= r rel))) (map first))
                                                   (inherit/declared kb))]
                                      (into [] (distinct)
                                            (concat (mapcat (fn [p] (reads/watched-rules-on idx p)) ps)
                                                    (when (seq ps) (negated-rechecks kb ps))))))
                  :all)))

(defn- recheck-declaration
  "A declaration licensing an inference about a predicate arrived or left: queue `:all`
  every rule whose exception mentions a predicate a fact on the subject answers
  (`answered-predicates`), or for a `negates` side the keys
  `rules/negates-denial-predicates` names.  Any other declaration also queues the negated
  conditions on the subject (`recheck-negated-exceptions`); `(transitive R)` also posts
  through `recheck-preserving-along`.  Runs only while some rule carries a re-check
  condition.  The fan is unscoped.  See docs/exceptions.md, \"Five channels\"."
  [kb sentence]
  (when-let [poss (get declaration-subjects (nm/functor sentence))]
    (let [idx (:index kb)]
      (when (pos? (reads/watched-rule-count idx))
        (doseq [i    poss
                :let [pred (nth sentence i nil)]
                :when (symbol? pred)]
          ;; the global closure on purpose, as everywhere here: an over-selected
          ;; re-check re-evaluates and changes nothing, an under-selected one is a
          ;; wrong belief
          (doseq [p (if (= 'negates (nm/functor sentence))
                      (conj (set (tax/specs-global (reasoning/taxonomy kb) pred)) pred)
                      (answered-predicates (reasoning/taxonomy kb) pred))]
            (mark-recheck kb (reads/watched-rules-on idx p) :all))
          (when-not (= 'negates (nm/functor sentence))
            (recheck-negated-exceptions kb pred))
          (when (= 'transitive (nm/functor sentence))
            (recheck-preserving-along kb pred)))))))

(def ^:private instance-type-shapes
  "The declarations `ArgTypeProver` reads a membership from (`res/arg-constraints`'
  `:instance` kind), each with the length of its sentence and the index its type sits at."
  '{arg [4 3] argAndRest [4 3]})

(defn- instance-type-declared?
  "Is any `functor` declaration of the `instance-type-shapes` stored?  `arg` by its O(1)
  count, the read this trigger has always paid; `argAndRest` by its
  `:declares-arg-and-rest-isa` mark, a `:props` lookup its own arms keep as it arrives
  and leaves (`prop-entry`), so a KB declaring no tail pays no second count per fact —
  the presence check `checks/covering-args-problem` already reads."
  [kb functor]
  (if (= 'argAndRest functor)
    (boolean (seq (tax/props (reasoning/taxonomy kb) :declares-arg-and-rest-isa)))
    (pos? (reads/stored-count-with-functor (:index kb) functor))))

(defn- declared-instance-type
  "The type `sentence` declares when it is one of the `instance-type-shapes`, else nil."
  [sentence]
  (when-let [[len at] (get instance-type-shapes (nm/functor sentence))]
    (when (= len (count sentence))
      (let [t (nth sentence at)] (when (symbol? t) t)))))

(defn- arg-declared-types
  "The types some `(arg pred n T)` or `(argAndRest pred n T)` declares of `pred`'s
  argument positions, read off the roots, globally, and including `pred`'s
  super-predicates (`res/constraining-predicates`)."
  [kb pred]
  (let [idx (:index kb)
        fs  (filter #(instance-type-declared? kb %) (keys instance-type-shapes))]
    (when (seq fs)
      (into #{}
            (comp (mapcat (fn [q] (mapcat #(reads/as-stored-with-args idx % {1 q}) fs)))
                  (keep #(p/get-sentex (:records kb) %))
                  (keep #(declared-instance-type (:sentence %))))
            (tax/genls-global (reasoning/taxonomy kb) pred)))))

(defn- recheck-arg-inferred
  "A fact on `pred`, or the `(arg pred n T)` declaration `sen` (or an `argAndRest` one,
  which `ArgTypeProver` reads as it reads `arg`, and which an `args` declaration's forward
  rule stores), arrived or left: queue `:all` every rule whose exception mentions a
  supertype of a type those declare of `pred`'s arguments, which `ArgTypeProver` infers
  from the fact.  A KB declaring neither pays one cardinality read (`instance-type-declared?`).  The `genls` fan is unscoped, for
  `recheck-declaration`'s reason.  See docs/exceptions.md, \"Five channels\"."
  [kb pred sen]
  (let [idx   (:index kb)
        rules (fn [ts] (into [] (comp (mapcat #(tax/genls-global (reasoning/taxonomy kb) %))
                                      (mapcat #(reads/watched-rules-on idx %))
                                      (distinct))
                             ts))]
    (mark-recheck kb (if (contains? instance-type-shapes pred)
                       (rules (some-> (declared-instance-type sen) vector))
                       (recheck-read kb [::arg-inferred pred] #(rules (arg-declared-types kb pred))))
                  :all)))

(defn- composed-exception-rules
  "The watched rules with a block literal a calculus moved by a predicate in `preds`
  answers: a literal on a predicate the calculus claims or on a super-predicate of one.
  `preds` are a fact's predicates or an edge's supertype, each read over its `genls`
  closure by `qkb/calculi-triggered-by`; empty when none moves a network.  The closure is
  the global one, as in `recheck-on-predicate`.  The caller queues them with the
  `::entailment` marker (docs/exceptions.md, \"Five channels\")."
  [kb preds]
  (let [cs (into #{} (mapcat #(qkb/calculi-triggered-by kb %)) preds)]
    (if (empty? cs)
      #{}
      (let [tx (reasoning/taxonomy kb) idx (:index kb)]
        (into #{}
              (comp (mapcat :predicates)
                    (mapcat #(tax/genls-global tx %))
                    (distinct)
                    (mapcat #(reads/watched-rules-on idx %)))
              cs)))))

(defn- recheck-separated-exceptions
  "A membership, a separation or a `genl` edge `sentence` arrived or left and moved which
  memberships `inherit/claims` reads as denials of a preserved predicate's goal
  (`inherit/separation-moved-predicates`): queue every rule whose exception mentions one of
  those predicates, `:all` for `recheck-preserving-along`'s reason.  The caller runs
  this only when some rule carries an `exceptWhen`."
  [kb sentence]
  (let [idx (:index kb)]
    (doseq [p (inherit/separation-moved-predicates kb sentence)]
      (mark-recheck kb (recheck-read kb [::on p] #(reads/watched-rules-on idx p)) :all))))

(defn- nonempty-moved-types
  "The types `C` whose `(nonempty C)` the membership `s`, `(T x)`, can move: `T` and its
  supertypes, read over every context.  Nil for an edge, a `genl` or a `genlCx` one."
  [kb s]
  (when (= 2 (count s))
    (set (tax/genls-global (reasoning/taxonomy kb) (first s)))))

(defn- recheck-nonempty-readers
  "`s` arrived, left or moved in belief and can move what `NonemptyProver` answers
  (`provers/nonempty-source?`): queue every rule posted under `nonempty`
  (`rules/nonempty-recheck-predicates`) with the `{::nonempty types}` marker of the types
  a membership moves (`nonempty-moved-types`), so the settle re-joins the rule per type,
  which an arriving member owes with no firing blocked; an edge queues them
  `:all-rejoin`.  One re-check index read, shared by a sweep's memberships
  (`recheck-read`)."
  [kb s]
  (when (provers/nonempty-source? kb s)
    (mark-recheck kb (recheck-read kb [::on 'nonempty] #(reads/watched-rules-on (:index kb) 'nonempty))
                  (if-let [ts (nonempty-moved-types kb s)] {::nonempty ts} :all-rejoin))))

(defn- recheck-on-predicate
  "A fact with predicate `pred` arrived or left: queue every rule whose exception
  mentions a predicate the fact answers (`answered-predicates`: `pred`, its supertypes
  and their inverses), with `trigger`, the sentence, as the narrowing trigger, and post
  the sideways channels the fact can move (`composed-exception-rules`,
  `recheck-separated-exceptions`, `recheck-preserving-along`, `recheck-arg-inferred`).
  Runs only while some rule carries a re-check condition.  The fan is unscoped, for
  `recheck-declaration`'s reason."
  [kb pred trigger]
  (when (symbol? pred)
    ;; no watched rule: skip the `genls(pred)` walk, an up-closure per assert
    (let [idx (:index kb)]
      (when (pos? (reads/watched-rule-count idx))
        (mark-recheck kb (recheck-read kb [::ups pred]
                                       #(into [] (comp (mapcat (fn [p] (reads/watched-rules-on idx p)))
                                                       (distinct))
                                              (answered-predicates (reasoning/taxonomy kb) pred)))
                      trigger)
        (mark-recheck kb (recheck-read kb [::composed pred] #(vec (composed-exception-rules kb [pred])))
                      ::entailment)
        ;; once per sentence: a negation's own functor is not its body's
        (when (= pred (nm/functor (or (sx/underlying-body trigger) trigger)))
          (recheck-separated-exceptions kb trigger)
          (recheck-nonempty-readers kb (or (sx/underlying-body trigger) trigger)))
        (recheck-preserving-along kb pred)
        (recheck-arg-inferred kb pred trigger)))))

(defn- recheck-on-qualitative
  "Queue for `chain/entailment-withdrawn?` every forward rule on a predicate of each
  calculus a sentence on `pred` moves (`qkb/calculi-triggered-by`).  `pred` is a fact's
  underlying body's functor or a `genl` edge's supertype.  The `::entailment` marker, not
  the sentence, is the trigger: a constraint anywhere moves what the network entails
  everywhere."
  [kb pred]
  (when-let [calcs (qkb/calculi-triggered-by kb pred)]
    (let [idx (:index kb)]
      (mark-recheck kb
                    (into #{} (comp (mapcat :predicates)
                                    (mapcat #(reads/as-stored-rules-by-antecedent-global idx %)))
                          calcs)
                    ::entailment))))

(defn- recheck-typed-admission
  "A membership `(t x)` arrived or left, or a `(genl sub t)` edge moved what is a `t`:
  for each registered calculus's `:typed` predicate with an `arg`-declared type a
  separation holds apart from `t` (`tax/pair-separated?`), queue `:all-rejoin` every
  stored rule carrying an antecedent on the predicate, and `:all` every rule whose
  exception mentions it or a supertype of it.  The admission (`qkb/typed-admits?`) reads
  an absence no support handle names (docs/qcn.md, \"What every algebra does with it\").
  The reads are unscoped, for `recheck-declaration`'s reason."
  [kb t]
  (when (symbol? t)
    (when-let [typed (seq (into [] (mapcat :typed) (qkb/registered-calculi kb)))]
      (let [idx (:index kb)
            tx  (reasoning/taxonomy kb)]
        (doseq [p     typed
                :when (and (or (reads/stored-rule-key? idx p) (pos? (reads/watched-rule-count idx)))
                           (tax/separable? tx t)
                           (some #(tax/pair-separated? tx t %) (arg-declared-types kb p)))]
          (mark-recheck kb (reads/as-stored-rules-by-antecedent-global idx p) :all-rejoin)
          (mark-recheck kb (into [] (comp (mapcat #(reads/watched-rules-on idx %)) (distinct))
                                 (tax/genls-global tx p))
                        :all))))))

(defn- recheck-preserving-firings
  "A sentence moved what a preserved predicate licenses: queues every forward rule
  carrying an antecedent on one (`inherit/rejoin-rules`), so the firings that joined on an
  inherited claim are put in front of `chain/inheritance-withdrawn?` at the next settle.
  A more specific contrary claim arriving withdraws such a firing with every antecedent
  still believed (docs/inherit.md, \"Forward chaining on a claim nobody stored\").  The
  `{::preserving sentence}` marker narrows by the goals the sentence can move
  (`inherit/moved-goal-test`)."
  [kb sentence]
  (when-let [rs (inherit/rejoin-rules kb sentence)]
    (mark-recheck kb rs {::preserving sentence})))

(defn- rules-taking
  "The stored rules, in every context, carrying an antecedent on one of the functors
  `answers`, a set, or nil: the answers some rule takes, read from the smaller side
  (`reads/as-stored-rule-keys-meeting`), and the rules only for those."
  [kb answers]
  (let [idx (:index kb)]
    (not-empty
     (into #{} (mapcat #(reads/as-stored-rules-by-antecedent-global idx %))
           (reads/as-stored-rule-keys-meeting
            idx (fn [n] (when (<= (count answers) (long n)) answers)) #(contains? answers %))))))

(defn computed-reading-rules
  "The forward rules a datum on `bfn` re-joins and re-checks because `bfn` is a
  predicate a registered `SupportingProver` reads: the rules carrying an antecedent that a
  prover reading `bfn` answers (`provers/support-answers-reading`).  `bfn` is the functor
  of the sentence's underlying body, so a believed `(not (conversionFactor …))` counts.
  Reads the rules stated in every context; one map lookup for a datum no prover reads.
  `s` is the sentence: a `genl` edge moves only the expression kinds at or above its
  upper end."
  [kb bfn s]
  (when-let [answers (provers/support-answers-reading kb bfn s)]
    (rules-taking kb answers)))

(defn- recheck-on-computed
  "A sentence on `bfn` arrived or left and moved what a `SupportingProver` computes: queue
  every rule `computed-reading-rules` names with the `::computed` marker, so each firing
  is put in front of `chain/computed-withdrawn?` and the rule is re-joined at the next
  settle.  A tightest bound narrows as a source arrives and widens as one leaves, and the
  firing's handles name neither move (docs/inference.md, \"What a computed answer rests
  on\")."
  [kb bfn s]
  (when-let [rs (computed-reading-rules kb bfn s)]
    (mark-recheck kb rs ::computed)))

(defn recheck-on-lengths
  "The settle pass moved the length of the relations `moved` (`arity/drain!`'s `:moved`,
  a set or `:all`): queue `:all-rejoin` every rule carrying an antecedent a relation's
  length can move (`provers/relation-moved-answers`).  Reads nothing while `moved` is
  empty."
  [kb moved]
  (when (and (or (= :all moved) (seq moved))
             (provers/quoted-anywhere? kb)
             (or (= :all moved) (some #(provers/quoted-head? kb %) moved)))
    (when-let [answers (provers/relation-moved-answers kb)]
      (mark-recheck kb (rules-taking kb answers) :all-rejoin))))

(defn- separation-moved-types
  "The types whose separations `s` arriving or leaving can move, as a set, or nil when it
  moves none: the subtypes of the types `tax/sentence-separation-ends` names.  A pair's
  separation reads the supertypes of its two types and the declarations over them, so a
  pair neither of whose types is below one of those reads the same separation before
  and after `s`.  The trigger index fires a rule at a stated `disjoint`'s own pair, so one
  over two types with no subtype moves nothing here.  The subtypes are read globally:
  the re-join reads every context."
  [kb s]
  (let [tx    (reasoning/taxonomy kb)
        below #(tax/specs-global tx %)]
    (when-not (and (seq? s) (= 'disjoint (nm/functor s))
                   (not-any? #(next (below %)) (nm/args s)))
      (not-empty (into #{} (mapcat below) (tax/sentence-separation-ends tx s))))))

(defn- negated-recheck-types
  "The types of the negated unary literals rule `rh` re-checks
  (`provers/negated-recheck-bodies`)."
  [kb rh]
  (into #{} (keep #(when (= 2 (count %)) (first %))) (provers/negated-recheck-bodies kb rh)))

(defn- repost-separation-denial-rules
  "A sentence `s` arrived or left and moved the separations of the types
  `tax/sentence-separation-ends` names: post every rule watched under `not`
  (`reads/watched-rules-on`) with a negated re-check literal over one of them under the
  types a separation now keeps apart from the literal's type
  (`rules/separation-denial-predicates`), unscoped, and queue it for a blanket re-check.
  A posting the move took away stays.  A sentence that moves no separation reads only the
  taxonomy."
  [kb s]
  (let [tx (reasoning/taxonomy kb)]
    (when-let [ends (seq (tax/sentence-separation-ends tx s))]
      (let [idx (:index kb)]
        (when-let [rhs (seq (reads/watched-rules-on idx 'not))]
          (let [moved (into #{} (mapcat #(tax/specs-global tx %)) ends)]
            (doseq [rh  rhs
                    :let [ts (filter moved (negated-recheck-types kb rh))]
                    :when (seq ts)]
              (let [sd (distinct (mapcat #(tax/separating-partners tx % nil (constantly false)) ts))]
                (when (seq sd) (rules/index-exception idx rh (sort sd)))
                (mark-recheck kb [rh] :all)))))))))

(defn- repost-negates-denial-rules
  "A `(negates A B)` sentence `s` arrived or left, or a `(genl sub super)` edge with a
  declaration reaching `super`: post every rule watched under `not` with a negated
  re-check literal on a predicate at or below `A` or `B` under the predicates that now
  negate it (`rules/negates-denial-predicates`), and queue it for a blanket re-check.  A
  posting the departure takes away stays, as in `repost-separation-denial-rules`.  Any
  other sentence reads one functor."
  [kb s]
  (when (and (seq? s)
             (or (= 'negates (nm/functor s))
                 (and (= 'genl (nm/functor s)) (= 3 (count s)) (symbol? (nth s 2))
                      (seq (tax/negates-over (reasoning/taxonomy kb) (nth s 2))))))
    (let [idx (:index kb)]
      (when-let [rhs (seq (reads/watched-rules-on idx 'not))]
        (let [tx (reasoning/taxonomy kb)]
          (doseq [rh  rhs
                  :let [nd (rules/negates-denial-predicates
                            tx (map #(list 'not %) (provers/negated-recheck-bodies kb rh)))]
                  :when (seq nd)]
            (rules/index-exception idx rh (sort nd))
            (mark-recheck kb [rh] :all)))))))

(defn- requeue-separation-denial-rules
  "A sentence `s` arrived or left and moved the separations of the ends
  `tax/sentence-separation-ends` names: queue `:all-rejoin` every rule with a `(not (T …))`
  antecedent whose `T` lies below an end, above one (an edge relating two marked types), or
  apart from one by a declaration (`tax/pair-separated?`).  The forward join answers such an
  antecedent from a separation's denial (`chain/solve-separation-denial`), which no stored
  negation triggers.  Reads the unscoped closures and every context, as the re-join does.
  A sentence that moves no separation reads only the taxonomy."
  [kb s]
  (let [tx (reasoning/taxonomy kb)]
    (when-let [ends (seq (tax/sentence-separation-ends tx s))]
      (let [idx   (:index kb)
            moved (delay (into #{} (mapcat #(tax/specs-global tx %)) ends))
            ks    (reads/as-stored-rule-keys-meeting
                   idx (constantly nil)
                   #(and (vector? %)
                         (let [t (second %)]
                           (or (contains? @moved t)
                               (some (fn [e] (or (tax/pair-separated? tx e t)
                                                 (contains? (tax/genls-global tx e) t)))
                                     ends)))))]
        (doseq [k ks]
          (mark-recheck kb (reads/as-stored-rules-by-antecedent-global idx k) :all-rejoin))))))

(defn- recheck-on-separation
  "A sentence `s` arrived or left and moved the separations of the types
  `separation-moved-types` names: queue every rule carrying a `disjoint` antecedent with
  the `{::separation types}` marker, queue the rules `requeue-separation-denial-rules`
  names, and post the rules with a negated re-check literal over a moved type
  (`repost-separation-denial-rules`).  The next settle re-decides the firings and refusals
  whose bindings name one of the types (`chain/separation-exempted?`) and re-joins the
  rules per type (`chain/*moved-types*`).  Reads the rules stated in every context.
  A sentence that moves no separation reads no index.  See docs/inference.md, \"A
  `disjoint` antecedent reads the separations\"."
  [kb s]
  (when-let [moved (separation-moved-types kb s)]
    (when (reads/stored-rule-key? (:index kb) 'disjoint)
      (mark-recheck kb (reads/as-stored-rules-by-antecedent-global (:index kb) 'disjoint)
                    {::separation moved})))
  (requeue-separation-denial-rules kb s)
  (repost-separation-denial-rules kb s))

(defn- index-closed-extent-rules
  "A closed-extent grant `s` on `P`, `(closed_extent_predicate P)` or
  `(closedExtentForArg P n v)`, arrived, left or moved in belief: post in the re-check
  index under `P`, and queue `:all-rejoin`, every stored rule the grant governs
  (`provers/closed-extent-rules`).  A defeat, an except or a suspension of the grant moves
  its belief with nothing stored or removed, and a firing it licensed holds no support
  handle for the literal it withheld.  A posting stays when the grant leaves (docs/naf.md,
  \"Under the grant, a negative antecedent is NAF\").  A no-op for any other sentence."
  [kb s]
  (when (and (sequential? s) (contains? '#{closed_extent_predicate closedExtentForArg} (first s)))
    (let [pred (second s)]
      (doseq [rh (provers/closed-extent-rules kb pred)]
        (rules/index-exception (:index kb) rh [pred])
        (mark-recheck kb [rh] :all-rejoin)))))

(defn- mention-read-rule?
  "Does the stored rule `rsx` hold an antecedent applying a functor the taxonomy `tx`
  marks as declaring a mention to a compound: one a join may read through a mention probe
  (`res/mention-probes`)?"
  [tx rsx]
  (boolean (some (fn [a] (and (seq? a) (symbol? (first a))
                              (some #(and (seq? %) (seq %)) (rest a))
                              (res/declares-mention? tx (first a))))
                 (:antecedent rsx))))

(defn- index-mention-rules
  "A `(quotedArg P n T)` or `(quotedArgAndRest P n T)` `s` arrived, left or moved in belief:
  post in the re-check index, and queue `:all-rejoin`, every stored rule with an antecedent
  applying `P` to a compound, since a reader the declaration reaches or leaves reads the
  compound at the mention in another order (`chain/mention-unread?`).  A no-op for any
  other sentence."
  [kb s]
  (when (and (sequential? s) (contains? '#{quotedArg quotedArgAndRest} (first s)) (symbol? (second s)))
    (let [pred   (second s)
          reads? (fn [a] (and (seq? a) (= pred (first a)) (some #(and (seq? %) (seq %)) (rest a))))]
      (doseq [rh (rules-taking kb #{pred})
              :when (some reads? (:antecedent (p/get-sentex (:records kb) rh)))]
        (rules/index-exception (:index kb) rh [])
        (mark-recheck kb [rh] :all-rejoin)))))

(defn- lazy-guard-readers
  "The forward rules reading a lazy-forward rule's conclusion, directly or through the
  lazy rules proving what they read (`ls`), whose placement a `genl` edge from `sub` to
  `sup` moves: one concluding on a predicate whose `genls` hold `sub` beside a rule of `ls`
  reading one in the `genls` of `sup` (`chain/converse-lazy-reading?`), and one concluding
  a membership in the `genls` of `sup` beside a type at or below `sub`, with a stored fact,
  at or below a predicate the reader or `ls` reads without this edge
  (`chain/unrestated-placements`).  Each functor's readers are read once, and the rules and
  closures over every context, as `chain/lazy-readers` reads them."
  [kb sub sup]
  (let [tx   (reasoning/taxonomy kb)
        idx  (:index kb)
        rec  #(p/get-sentex (:records kb) %)
        ups  (set (tax/genls-global tx sup))
        fns  (fn [r] (into #{} (keep nm/functor) (:antecedent r)))
        held (delay (filterv #(pos? (long (reads/stored-count-with-functor idx %)))
                             (tax/specs-global tx sub)))
        by-c (group-by #(nm/functor (:consequent %))
                       (filter rules/lazy-sentex? (keep rec (reads/as-stored-rules-in-global idx :lazy))))
        lzs  (fn [g] (loop [todo [g], seen #{}, out []]
                       (if-let [f (peek todo)]
                         (if (contains? seen f)
                           (recur (pop todo) seen out)
                           (let [ls (get by-c f)]
                             (recur (into (pop todo) (mapcat fns) ls) (conj seen f) (into out ls))))
                         out)))]
    (into []
          (comp (filter symbol?)
                (mapcat (fn [g]
                          (let [ls    (lzs g)
                                reads (into #{} (mapcat fns) ls)
                                conv  (when (some ups reads)
                                        (disj (into #{} (map #(nm/functor (:consequent %))) ls) g))
                                below #(and (symbol? %) (contains? (set (tax/genls-global tx %)) sub))
                                meets (fn [fs] (some #(tax/genls-global-meets-without? tx % fs sub sup) @held))]
                            (when (or conv (seq @held))
                              (for [r (keep rec (reads/as-stored-rules-by-antecedent-global idx g))
                                    :when (rules/forward-sentex? r)
                                    :let [c (nm/functor (:consequent r))]
                                    :when (and (symbol? c)
                                               (or (and conv (some below (conj conv c)))
                                                   (and (= 2 (count (:consequent r))) (contains? ups c)
                                                        (let [fs (into reads (fns r))]
                                                          (or (some sx/variable? fs) (meets fs))))))]
                                (:id r))))))
                (distinct))
          (keys by-c))))

(defn- recheck-lazy-guards
  "A `genl` edge `s` arrived, left or moved in belief: queue `:all-rejoin` the readers whose
  placement it moves (`lazy-guard-readers`), so the settle blocks a firing the edge makes
  a converse reading or a membership its taxonomy holds, and re-joins a firing it no
  longer withholds.  Reads nothing on a store holding no lazy-forward rule."
  [kb s]
  (when (and (= 3 (count s)) (= 'genl (first s)) (kb/stores-lazy-rule? kb))
    (let [[_ sub sup] s]
      (when (and (symbol? sub) (symbol? sup))
        (mark-recheck kb (lazy-guard-readers kb sub sup) :all-rejoin)))))

(defn recheck-on-sentence
  "The re-check trigger for a whole sentence: post it under its functor and, for a
  negation, under the functor of its `underlying-body`, both with the whole sentence as
  the narrowing trigger; then post the declaration, qualitative, computed, separation,
  preservation and closed-extent grant triggers on the body, and for a unary body the
  typed-admission trigger. `underlying-body` rather than `positive-body`, because a
  `(not (penguin X))` arriving defeats a believed `(penguin X)` and moves a condition that
  reads belief with no fact stored or removed."
  [kb sentence]
  (let [b (sx/underlying-body sentence)]
    (recheck-on-predicate kb (nm/functor sentence) sentence)
    (when (and b (not= b sentence))
      (recheck-on-predicate kb (nm/functor b) sentence))
    (recheck-declaration kb (or b sentence))
    (repost-negates-denial-rules kb (or b sentence))
    (recheck-on-qualitative kb (nm/functor (or b sentence)))
    (recheck-on-computed kb (nm/functor (or b sentence)) (or b sentence))
    (recheck-on-separation kb (or b sentence))
    (recheck-preserving-firings kb (or b sentence))
    (index-closed-extent-rules kb (or b sentence))
    (index-mention-rules kb (or b sentence))
    (recheck-lazy-guards kb (or b sentence))
    (when (= 2 (count (or b sentence)))
      (recheck-typed-admission kb (nm/functor (or b sentence))))))

(defn- note-mark-reach!
  "Queue on `:respell` each predicate a statement of whose permuting mark rests on
  `target`, and `[:reifiable f]` each function a statement of whose `reifiable_function`
  mark does: a `defeat` or an `except` of `target` moves which readers believe the mark
  with no label moving, and so which spellings the facts under it are read in
  (`chain/reconcile-spellings!`, `chain/reconcile-reified!`).  Reads the supports of the
  marks' statements, so it costs the marks stored and not the facts under them."
  [kb target]
  (let [t      @(reasoning/taxonomy kb)
        tms    (reasoning/tms kb)
        rests? (fn [k] (some #(contains? (exc/support tms % (constantly false)) target)
                             (keys (tax/supporters (reasoning/taxonomy kb) k))))
        moved  (-> #{}
                   (into (filter #(rests? [:prop :symmetric %])) (get-in t [:props :symmetric]))
                   (into (keep (fn [[p gs]] (when (some #(rests? [:commuting p %]) gs) p)))
                         (:commuting t))
                   (into (comp (filter #(rests? [:prop :reifiable %])) (map #(vector :reifiable %)))
                         (get-in t [:props :reifiable])))]
    (when (seq moved)
      (swap! (reasoning/respell kb) into moved))))

(defn- note-split-marks!
  "Queue on `:respell` each predicate whose permuting marks, and `[:reifiable f]` each
  function whose `reifiable_function` mark, some reader does not believe
  (`res/uniform-marks?`): a `genlCx` edge moves which readers see which defeats and
  excepts, and so which spellings a fact's readers read.  Reads nothing while no
  `defeat` or `except` is stored, since every reader then believes every mark."
  [kb]
  (when (or (reads/stores-any? (:index kb) sx/defeat-functor)
            (reads/stores-any? (:index kb) sx/except-functor))
    (let [t      @(reasoning/taxonomy kb)
          split? (fn [k] (let [sup (tax/supporters (reasoning/taxonomy kb) k)]
                           (and (seq sup) (not (res/uniform-marks? kb {k sup})))))
          moved  (-> #{}
                     (into (filter #(split? [:prop :symmetric %])) (get-in t [:props :symmetric]))
                     (into (keep (fn [[p gs]] (when (some #(split? [:commuting p %]) gs) p)))
                           (:commuting t))
                     (into (comp (filter #(split? [:prop :reifiable %])) (map #(vector :reifiable %)))
                           (get-in t [:props :reifiable])))]
      (when (seq moved)
        (swap! (reasoning/respell kb) into moved)))))

(defn recheck-defeat-target
  "Post the re-check a `(defeat (sentexHandle H))` sentex `sx` owes H's watchers when it is
  stored, removed or relabelled: the defeat moves H's belief at the contexts that see it
  with no relabel of H, so H's sentence posts what its own arrival posts
  (`recheck-on-sentence`), and a permuting mark resting on H re-spells its facts
  (`note-mark-reach!`).  A no-op for any other sentex, and for an H no longer stored."
  [kb sx]
  (when-let [t (kb/defeat-target (:sentence sx))]
    (note-mark-reach! kb t)
    (when-let [ts (p/get-sentex (:records kb) t)]
      (recheck-on-sentence kb (:sentence ts)))))

(defn recheck-every-exception
  "Queue `:all` every rule carrying a re-check condition.  `recover` takes it."
  [kb]
  (mark-recheck kb (reads/watched-rules (:index kb)) :all))

(def ^:private closure-answered-exception-functors
  "Exception functors a `genl` edge can flip across arguments, with neither endpoint
  near the registered predicate, so `recheck-genl-edge` queues their rules `:all`:
  `genl`, which the transitivity prover answers from the moved closure, and `disjoint`,
  closed under `genl` on both sides.  A negated conjunct is keyed by
  `recheck-negated-exceptions` instead, and a preserved argument position by
  `recheck-preserving-along`."
  '#{genl disjoint})

(defn- recheck-genl-edge
  "A `genl` edge `(genl sub super)` was added or removed: queue `:all` the rules whose
  exception mentions a predicate a fact on `super` answers (`answered-predicates`) or a
  `closure-answered-exception-functors` functor, the composed-exception rules on `super`,
  the negated conditions at `sub` (`recheck-negated-exceptions`) and the preserved
  positions along `genl`; then post the calculus and typed-admission triggers on `super`.
  Reads after the mutation.  See docs/exceptions.md, \"Taxonomy changes are keyed on what
  the closure moved\"."
  [kb sub super]
  (let [tx (reasoning/taxonomy kb) idx (:index kb)]
    ;; no watched rule: skip the `genls(super)` walk, an up-closure per edge
    (when (pos? (reads/watched-rule-count idx))
      (let [ups (answered-predicates tx super)]
        (doseq [pe (into ups closure-answered-exception-functors)]
          (mark-recheck kb (reads/watched-rules-on idx pe) :all))
        (mark-recheck kb (composed-exception-rules kb [super]) :all))
      (recheck-negated-exceptions kb sub)
      (recheck-preserving-along kb 'genl))
    (recheck-on-qualitative kb super)
    (recheck-typed-admission kb super)))

(defn arrival-releasable-rule?
  "Can an arriving fact release a block on the rule stored at `rh`?  True when
  `rules/arrival-releasable?` holds of it, or `rules/exception-arrival-releasable?` of
  its exceptions.  The settle loop owes such a rule a re-join, and the two edge triggers
  below exempt it from their firing-side narrowing."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (and (rules/rule? rsx)
         (or (rules/arrival-releasable? rsx)
             (rules/exception-arrival-releasable? (provers/rule-exceptions kb rh))))))

(defn- refusals-reach?
  "Does rule `rh` hold a refusal `hit?` accepts, or an `:overflow` record, which holds no
  entries to test?  The two edge triggers ask it so a rule refused on every firing is
  not read as a rule that never fired.  Reads `(reasoning/refused kb)` directly, since
  `chain`, which writes it, sits above this namespace."
  [kb rh hit?]
  (let [r (get @(reasoning/refused kb) rh)]
    (if (set? r) (boolean (some hit? r)) (= :overflow r))))

(defn- recheck-genlCx-edge
  "A `genlCx` edge moved (`context-move`'s `m`): queue `:all` each watched rule an
  arrival can release (`arrival-releasable-rule?`), one with a firing placed in a context
  of `(:seen m)` (where a context under `sub` sees it, so a guard defeat can move), and
  one with a refusal whose placement context is in `(:under m)`; then post the preserved
  positions along `genlCx`.  Costs a record fetch per watched rule and a context lookup
  per firing up to the first hit.  See docs/exceptions.md, \"Taxonomy changes are keyed
  on what the closure moved\"."
  [kb m]
  (let [idx (:index kb) tms (reasoning/tms kb)
        excepted (reads/watched-rules idx)]
    (when (and m (seq excepted))
      (let [affected @(:under m)
            ;; a firing placed where a context under `sub` sees it can gain or lose a
            ;; guard defeat there (`chain/place-guard-defeats!`)
            seen     @(:seen m)
            in-ancestor-set? (fn [jid]
                               (when-let [j (jtms/justification tms jid)]
                                 (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
                                   (contains? seen (:context csx)))))]
        (doseq [rh excepted]
          (when (or (arrival-releasable-rule? kb rh)
                    (some in-ancestor-set? (jtms/dependents tms rh))
                    (refusals-reach? kb rh #(contains? affected (:pctx %))))
            (mark-recheck kb [rh] :all)))
        (recheck-preserving-along kb 'genlCx)))))

(defn names-any?
  "Does the binding map `b` of a firing or a refusal bind a variable to one of `terms`,
  at any depth?"
  [terms b]
  (boolean (some (fn [v] (some terms (tree-seq sequential? seq v))) (vals b))))

(defn- binds-any?
  "Does the firing behind justification `jid` bind one of `terms`, at any depth?  Reads
  the justification record, since `jtms/graph-just` drops the bindings."
  [kb terms jid]
  (when-let [j (p/get-justification (:records kb) jid)]
    (names-any? terms (:bindings j))))

(defn- different-only-rule?
  "Is the rule at `rh` re-checked for a `(different …)` antecedent and for nothing else:
  no `unknown` antecedent, no aggregate, no closed-extent negative and no `exceptWhen`
  stored naming it?  A merge can only withdraw such a rule's firings, never release one."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (and (rules/rule? rsx)
         (rules/has-different? rsx)
         (not (rules/has-naf? rsx))
         (not (rules/has-aggregate? rsx))
         (empty? (rules/closed-extent-recheck-predicates-of (reasoning/taxonomy kb)
                                                            (sx/sentence-of rsx)))
         (empty? (provers/stored-exception-metas kb rh)))))

(defn- sentence-moved-terms
  "The terms whose `different` the sentence `s` arriving or leaving can flip: the
  equality class of every symbol among its arguments, at any depth, read unscoped.  A
  split leaves each side of a removed link in the class of the link's end it stays
  joined to, so the current classes hold both ends of every pair the sentence moved.
  Nil for any other functor the guard is watched under, a `genl` edge among them, which
  moves every member of a kind and names none of them."
  [kb s]
  (let [s (or (sx/underlying-body s) s)]
    (when (contains? '#{sameAs rewriteOf equals indeterminate_term} (nm/functor s))
      (let [tx (reasoning/taxonomy kb)]
        (into #{}
              (comp (mapcat #(tree-seq sequential? seq %))
                    (filter #(and (symbol? %) (not (sx/variable? %))))
                    (mapcat #(tax/equiv-class tx %)))
              (nm/args s))))))

(defn different-rechecked-terms
  "The terms a firing or a refusal of the rule at `rh` must bind for one of its queued
  `triggers` to have flipped it, or nil when the triggers say nothing that narrow.  Only
  a `different-only-rule?` narrows, and only when every trigger is a merge's
  `{::merged class}` marker or a sentence `sentence-moved-terms` reads."
  [kb rh triggers]
  (when (and (set? triggers) (different-only-rule? kb rh))
    (reduce (fn [acc t]
              (if-let [ts (cond (map? t)     (::merged t)
                                (keyword? t) nil
                                :else        (sentence-moved-terms kb t))]
                (into acc ts)
                (reduced nil)))
            #{}
            triggers)))

(defn- recheck-equality-edge
  "The equality closure moved (an equality asserted, derived or retracted, or a schematic
  rewrite rule arriving or leaving): queue `:all` each watched rule with a firing or a
  refusal that binds a term of the merged class `terms`, and each rule an arrival can
  release (`arrival-releasable-rule?`).  A `different-only-rule?` takes a `{::merged
  terms}` marker in place of `:all`: the settle re-decides the firings and refusals
  binding a term of the class and re-joins nothing.  `terms` nil, for a split or a
  schematic rewrite, queues every watched rule `:all`.  See docs/exceptions.md, \"Five
  channels\"."
  ([kb] (recheck-equality-edge kb nil))
  ([kb terms]
   (let [tms (reasoning/tms kb)]
     (when-let [rules (seq (reads/watched-rules (:index kb)))]
       (doseq [rh rules]
         (when (or (nil? terms)
                   (arrival-releasable-rule? kb rh)
                   (some #(binds-any? kb terms %) (jtms/dependents tms rh))
                   (refusals-reach? kb rh #(names-any? terms (:bindings %))))
           (mark-recheck kb [rh] (if (and terms (different-only-rule? kb rh))
                                   {::merged terms}
                                   :all))))))))

(defn rule-recheck-keys
  "The keys the re-check index posts the rule `rule-sentex` under, read against the
  taxonomy `tx`: `rules/recheck-predicates`, the closed-extent, separation-denial and
  negates-denial keys of its sentence, and `rules/nonempty-recheck-predicates`.  Nil when
  the rule carries none of them, no re-check condition (`rules/rechecked?`) and no
  antecedent read through a mention probe (`mention-read-rule?`); a rule with a condition
  and no key answers an empty vector, which posts it into the `:rules` set alone."
  [tx rule-sentex]
  (let [s  (sx/sentence-of rule-sentex)
        ce (rules/closed-extent-recheck-predicates-of tx s)
        sd (concat (rules/separation-denial-predicates-of tx s)
                   (rules/negates-denial-predicates-of tx s)
                   (rules/nonempty-recheck-predicates rule-sentex))]
    (when (or (rules/rechecked? rule-sentex) (seq ce) (seq sd) (mention-read-rule? tx rule-sentex))
      (vec (distinct (concat (rules/recheck-predicates rule-sentex) ce sd))))))

(defn index-rule-sentex
  "Index a rule handle by all of its predicates (antecedent and consequent), so
  `reads/as-stored-rules-by-consequent-in` answers \"what could conclude P?\" for a
  forward-only rule too, and in the re-check index under the keys `rule-recheck-keys`
  names.  A variable consequent functor is filed under `p/var-consequent-key`
  (`rules/consequent-index-pred`); `resolution/concluding-rule-handles` unions that
  bucket.  The record holds `:engines` and `:defeasible`; no rule index keys on them.
  This is the add half of the structural arm of `integrate-sentex`."
  [kb handle rule-sentex]
  (let [antes (:antecedent rule-sentex)]
    (rules/index-rule (:index kb) handle
                      (rules/antecedent-keys antes)
                      (rules/consequent-index-pred rule-sentex)
                      (:context rule-sentex))
    (when-let [ks (rule-recheck-keys (reasoning/taxonomy kb) rule-sentex)]
      (rules/index-exception (:index kb) handle ks)
      ;; `:all`: no trigger sentence, and the rule may have fired before the drain
      (mark-recheck kb [handle] :all))))

;; ---- the inert rules the mints are justified under ---------------------------

(def ^:private entailing-declarations
  "The argument-constraint declarations that entail, with the arity each is written at —
  the table `entail-existing` dispatches on, so another kind is one line rather than a
  widened `and`.  Every kind of the `:argument-constraint` family but `quotedArg`, which
  types the term as written and has nothing to derive (docs/argtypes.md), and `args`,
  which entails through the `(argAndRest P 1 T)` its core.txt forward rule stores: that
  twin's arrival sweeps the stored facts, and its handle is what each mint rests on
  (`checks/covering-entailments`)."
  '{arg 3, argArg 3, genlArg 3, interArg 5, interArgEqual 5, argAndRest 3, argsGenl 2,
    argAndRestGenl 3, interArgs 2, interArgAndRest 3})

(defn firing-informant?
  "Is `informant` a rule a forward or backward run fired: a rule handle that is not one of
  `kv/mint-rules`, which no engine runs."
  [kb informant]
  (and (integer? informant) (nil? (kb/mint-kind kb informant))))

(defn mint-rule-retraction-problem
  "The `:mint-rule` refusal of retracting the sentex at `handle` (`kb/mint-rule-refusal`), as
  a value, or nil.  The engine stores the rule again at the next mint (`mint-rule-handle!`).
  `where` names the entry point."
  [kb handle where]
  (kb/mint-rule-refusal (kb/mint-kind kb handle) handle where "is not retracted"))

;; ---- exceptWhen meta-sentexes: the re-check posting for an exception ------
;; An `(exceptWhen <query> (sentexHandle H))` arriving or leaving posts or withdraws H in
;; the re-check index under the query's keys and queues H for re-evaluation.

(defn restrength-firings!
  "Set the strength of every justification rule `rh` informs to the rule's current
  `provers/firing-strength`, in both copies: the record store's justification records
  (what `supporting-justifications` shows and what `recover` rebuilds the network from)
  and the network's (`jtms/restrength-informant`, which relabels the region).  A rule's
  firing strength moves when its defeasibility resolves or an `exceptWhen` arrives or
  leaves; `dropping-id` is the exception meta-sentex leaving, if any."
  ([kb rh] (restrength-firings! kb rh nil))
  ([kb rh dropping-id]
   (when-let [rsx (p/get-sentex (:records kb) rh)]
     (when (rules/rule? rsx)
       (let [strength (provers/firing-strength kb rh rsx (reads/watched-rule? (:index kb) rh)
                                               dropping-id)
             tms      (reasoning/tms kb)]
         (doseq [jid (jtms/dependents tms rh)
                 :let [j (p/get-justification (:records kb) jid)]
                 :when (and j (= rh (:informant j)) (not= strength (:strength j)))]
           (p/put-justification (:records kb) (assoc j :strength strength)))
         (jtms/restrength-informant tms rh strength))))))

(defn- force-rule!
  "Rewrite the forced memberships of the stored rule at `rh` and of its firings
  (`checks/force-sentexes!`): an `exceptWhen` arriving on a forced-monotonic rule convicts its
  firings, and the last one leaving releases them."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (when (rules/rule? rsx)
      (checks/force-sentexes! kb [rsx]))))

(defn exception-recheck-predicates
  "The re-check keys of the exceptWhen meta-sentence `meta`, read against the taxonomy
  `tx`: the predicates its query mentions, the types a separation's denial and the
  predicates a `negates` denial move a negated conjunct of it on
  (`rules/separation-denial-predicates`, `rules/negates-denial-predicates`), and the
  predicates of its closed-extent negatives (`rules/closed-extent-query-predicates`)."
  [tx meta]
  (let [qs (sx/exception-query-conjuncts meta)]
    (concat (rules/watched-predicates qs)
            (rules/separation-denial-predicates tx qs)
            (rules/negates-denial-predicates tx qs)
            (rules/closed-extent-query-predicates tx qs))))

(defn index-exceptWhen-meta
  "Register the exceptWhen meta-sentex `meta-sentex` in the re-check index: post the
  rule it names under its keys (`exception-recheck-predicates`) and into the `:rules`
  set, queue the rule for a blanket re-check (a fact may already have arrived that its
  new exception blocks), lower the rule's firings to `:default`
  (`restrength-firings!`), and hold void the firings of a forced-monotonic rule it convicts
  (`checks/force-sentexes!`)."
  [kb meta-sentex]
  (let [rh    (sx/exceptWhen-rule-handle (:sentence meta-sentex))
        preds (exception-recheck-predicates (reasoning/taxonomy kb) (:sentence meta-sentex))]
    (when rh
      (rules/index-exception (:index kb) rh preds)
      (mark-recheck kb [rh] :all)
      (restrength-firings! kb rh)
      (force-rule! kb rh))
    nil))

(defn- rule-remaining-recheck-preds
  "The predicates the rule `rh` must stay registered under after the exceptWhen
  meta-sentex `dropping-id` leaves: those of its *other* believed exceptWhen
  meta-sentexes' queries, plus the rule's own keys (`rules/recheck-predicates`, its
  separation-denial and closed-extent keys) — so a predicate two exceptions share, or one
  shared with a NAF antecedent, is not wrongly dropped."
  [kb rh dropping-id]
  (let [tx     (reasoning/taxonomy kb)
        others (into #{}
                     (comp (map #(p/get-sentex (:records kb) %))
                           (filter some?)
                           (filter #(and (sx/exceptWhen-meta? (:sentence %))
                                         (= rh (sx/exceptWhen-rule-handle (:sentence %)))
                                         (not= dropping-id (:id %))))
                           (mapcat #(exception-recheck-predicates tx (:sentence %))))
                     (reads/as-stored-naming-handle (:index kb) rh))
        rsx    (p/get-sentex (:records kb) rh)]
    (into others (when rsx (rule-recheck-keys tx rsx)))))

(defn unindex-exceptWhen-meta
  "The mirror of `index-exceptWhen-meta`: withdraw the departing exceptWhen
  meta-sentex's postings, then re-post the rule from the predicates its *remaining*
  exceptions and NAF antecedents still need — a set re-add restores any shared
  predicate the blanket withdraw over-removed, and leaves the rule out of the `:rules`
  set exactly when nothing watches it any more.  Queues the rule for re-check, since
  losing an exception may revive what it was blocking, restores the rule's firing
  strength when no guard remains (`restrength-firings!`), and releases the firings of a
  forced-monotonic rule no exception convicts any more (`checks/force-sentexes!`)."
  [kb meta-sentex]
  (let [rh        (sx/exceptWhen-rule-handle (:sentence meta-sentex))
        this-preds (exception-recheck-predicates (reasoning/taxonomy kb) (:sentence meta-sentex))]
    (when rh
      (rules/unindex-exception! (:index kb) rh this-preds)
      (when-let [remaining (seq (rule-remaining-recheck-preds kb rh (:id meta-sentex)))]
        (rules/index-exception (:index kb) rh remaining))
      (mark-recheck kb [rh] :all)
      (restrength-firings! kb rh (:id meta-sentex))
      (force-rule! kb rh))))

;; ---- except: visibility removal blocks derivations too -------------------
;; The trigger below queues the rules of every firing resting on H
;; (`chain/justification-excepted?`; docs/exceptions.md).

(defn note-except-move!
  "Queue handle `h` on `:except-moves`: an `except` of it stated in `context` arrived,
  left or flipped, so what `h` restates or merges is visible to a different set of
  readers there and below.  `edge`, a `(genlCx sub super)` edge's `[sub super]`, says the
  move is that edge's and reaches the contexts under `sub` alone (`:scoped`); nil says the
  `except` itself moved (`:whole`).  The settle drains the queue (`drain-except-moves!`,
  `take-except-moves!`)."
  [kb h context edge]
  (swap! (reasoning/except-moves kb)
         #(cond-> (update-in % [:pending h] (fnil conj #{}) context)
            edge       (update-in [:scoped h] (fnil conj #{}) edge)
            (nil? edge) (update :whole (fnil conj #{}) h))))

(defn- recheck-defeats-reached
  "Post the re-check of the target of each placed `defeat` an `except` of `h` can take in
  or out of force (`recheck-defeat-target`): each defeat in `closure`, `h`'s consequence
  closure with `h` in it, and each defeat of `h`.  A defeat in the closure rests on `h`
  through a member or a ground of its nogood, and an except of `h` can lower that member's
  class at a reader (docs/nmtms.md, \"A conflict a reader's excepts lower\").  An except
  moves a defeat's force with no relabel of its target."
  [kb h closure]
  (when (reads/stores-any? (:index kb) sx/defeat-functor)
    (let [tms  (reasoning/tms kb)
          recs (:records kb)
          ;; only the engine derives a defeat, under one of two informants
          placed? (fn [d] (some #(contains? #{exc/nogood-informant exc/guard-informant}
                                            (:informant (jtms/justification tms %)))
                                (jtms/supports tms d)))]
      (doseq [d (into (filterv placed? closure) (reads/as-stored-naming (:index kb) sx/defeat-functor h))
              :let [sx (p/get-sentex recs d)]
              :when sx]
        (recheck-defeat-target kb sx)))))

(defn recheck-except
  "An `(except (sentexHandle H))` fact arrived or left, or the `genlCx` edge `edge`, a
  `[sub super]`, moved which contexts see it: queue what the visibility change touches.
    * The firings resting on H through any chain (`jtms/consequence-closure`) are queued
      under `{::except-closure c}`.
    * `:except-moves` records H with `edge`, and the drain re-joins from the closure
      (`note-except-move!`, `drain-except-moves!`).
    * A rule H is queued `:all`; an except H re-checks its own target down the cascade.
  Re-runs H's arrival sweep for the restatements the move reaches.  See docs/exceptions.md,
  \"Five channels\"."
  ([kb except-sentex] (recheck-except kb except-sentex nil))
  ([kb except-sentex edge]
   (when-let [h (sx/handle-id (second (:sentence except-sentex)))]
     (note-mark-reach! kb h)
     (let [tms     (reasoning/tms kb)
           ;; what rests on H through any chain, H included: bounded by H's consequences
           closure (jtms/consequence-closure tms [h])
           users   (into #{}
                         (comp (mapcat #(jtms/dependents tms %))
                               (keep (fn [jid]
                                       (let [inf (:informant (jtms/justification tms jid))]
                                         (when (firing-informant? kb inf) inf)))))
                         closure)
           target  (p/get-sentex (:records kb) h)]
       (mark-recheck kb users {::except-closure closure})
       (when (and target (rules/rule? target)) (mark-recheck kb [h] :all))
       (note-except-move! kb h (:context except-sentex) edge)
       (recheck-defeats-reached kb h closure)
       ;; the except moves H's visibility with no relabel, so this sentence posts what H's removal posts
       (when-let [fact (loop [s target, seen #{}]
                         (let [t (some-> s :sentence kb/except-target)]
                           (if (and t (not (seen t)))
                             (recur (p/get-sentex (:records kb) t) (conj seen t))
                             s)))]
         (when-not (rules/rule? fact)
           (recheck-on-sentence kb (:sentence fact))))
       ;; H an except: its force moved, so what rests on its own target moves too
       (when (some-> target :sentence kb/except-target)
         (recheck-except kb target edge))))))

(defn- move-except-contexts
  "The contexts that split the readers under a moved `genlCx` edge into classes
  (`exc/genlCx-except-contexts` over the stored `genlCx` facts, either polarity)."
  [kb]
  (let [idx  (:index kb)
        recs (:records kb)]
    (exc/genlCx-except-contexts
     kb {:supports? #(= 'genlCx (nm/functor (some-> (p/get-sentex recs %) sx/body)))
         :count     (reads/stored-count-with-functor idx 'genlCx)
         :handles   #(reads/as-stored-with-functor idx 'genlCx)})))

(defn- context-move*
  "`context-move` with the reader-class contexts `ctxs` (`move-except-contexts`) in hand,
  and `off`, the other edges moved with this one (`tax/context-move`'s `:gains`)."
  [kb ctxs sub super off]
  (let [idx (:index kb)]
    (tax/context-move (reasoning/taxonomy kb) sub super ctxs
                      (fn [a b] (not (reads/stored-opposed? idx (list 'genlCx a b))))
                      off)))

(defn context-move
  "What the move of the `genlCx` edge `[sub super]` shows or hides (`tax/context-move`),
  with the reader classes the stored `except`s on `genlCx` supporters' support split the
  readers into (`exc/genlCx-except-contexts`).  The walks without the edge do not cross an
  edge stored in both polarities, so that edge can only enlarge the answer."
  [kb sub super]
  (context-move* kb (move-except-contexts kb) sub super nil))

(defn recheck-except-ancestors
  "Re-check each `except` the `genlCx` move `m` (`context-move`) moves (`recheck-except`,
  over its target's consequence closure): one stated in a context of the move's raw stratum
  (`:raw`), where the excepts in force at a reader under the edge's `sub` are read, and
  the `except` each of those names, whose cascade moves with it.  An edge whose `sub`
  already sees every context stating an `except` re-checks none (`lein perf`'s
  `genlcx-edge-beside-excepted-declarations`, `genlcx-edge-beside-seen-excepts`)."
  [kb {:keys [edge raw]}]
  (let [idx (:index kb)]
    (when (and (seq raw) (reads/stores-any? idx sx/except-functor))
      (let [recs (:records kb)
            seen (into (sorted-set) (reads/as-stored-with-functor-in idx sx/except-functor raw))]
        (loop [todo (vec seen) done #{}]
          (when-let [eh (peek todo)]
            (let [todo (pop todo)]
              (if (contains? done eh)
                (recur todo done)
                (let [esx   (p/get-sentex recs eh)
                      inner (some->> esx :sentence kb/except-target)
                      esx   (when inner esx)
                      inner (when (some->> inner (p/get-sentex recs) :sentence kb/except-target)
                              inner)]
                  (when esx (recheck-except kb esx edge))
                  (recur (cond-> todo inner (conj inner)) (conj done eh)))))))))))

(defn- belief-change-region
  "`moved` plus the targets of any visibility-excepts it names.  Runs only when an `except`
  is stored (`reads/stores-any?`); otherwise returns `moved` unread."
  [kb moved]
  (if-not (reads/stores-any? (:index kb) sx/except-functor)
    (set moved)
    (into (set moved)
          (keep (fn [h]
                  (some-> (p/get-sentex (:records kb) h)
                          :sentence
                          kb/except-target)))
          moved)))

(defn- permuting-marks
  "What the store spells sentences by: the `symmetric` predicates, the commuting-group
  table, the `reifiable_function` functions, the term marks (the `associative` and
  `idempotent` functions, the `meetFunctionOf` and `distinctInArgAndRest` tables), and the
  predicates declaring a `quotedArg` or `quotedArgAndRest` mention (`res/mention-at`).  Nine
  persistent values, compared by identity first.

  The marks are read unscoped: they decide the stored spelling, which every reader
  shares."
  [tax]
  [(tax/props tax :symmetric) (get @tax :commuting {}) (tax/props tax :reifiable)
   (tax/props tax :associative) (tax/props tax :idempotent) (get @tax :meet {})
   (tax/props tax :declares-quoted-arg) (tax/props tax :declares-quoted-arg-and-rest)
   (get @tax :distinct {})])

(defn- note-permuting-moves!
  "Queue on `:respell` every predicate whose permuting marks differ between `before` (a
  `permuting-marks` reading) and now, `[:mention p]` for every predicate whose mention mark
  does, and `[:reifiable f]` for every function whose `reifiable_function` mark does, or
  whose `symmetric` or commuting mark does while it is reifiable before or after.  A
  mark that stops holding leaves rows spelled by it, and one that starts holding leaves rows
  it would have folded, with no sentex arriving, so `chain/reconcile-spellings!` and
  `chain/reconcile-reified!` are told here: at a record leaving, a relabel, and for the
  reifiable mark a record arriving (`reifiable-entry`).  Nearly always nine `identical?` tests."
  [kb [sym0 com0 rf0 as0 id0 mt0 qa0 qr0 ds0]]
  (let [[sym1 com1 rf1 as1 id1 mt1 qa1 qr1 ds1] (permuting-marks (reasoning/taxonomy kb))]
    (when-not (and (identical? sym0 sym1) (identical? com0 com1) (identical? rf0 rf1)
                   (identical? as0 as1) (identical? id0 id1) (identical? mt0 mt1)
                   (identical? qa0 qa1) (identical? qr0 qr1) (identical? ds0 ds1))
      (let [moved (-> #{}
                      (into (remove #(contains? sym1 %)) sym0)
                      (into (remove #(contains? sym0 %)) sym1)
                      (into (comp (remove #(contains? qa1 %)) (map #(vector :mention %))) qa0)
                      (into (comp (remove #(contains? qa0 %)) (map #(vector :mention %))) qa1)
                      (into (comp (remove #(contains? qr1 %)) (map #(vector :mention %))) qr0)
                      (into (comp (remove #(contains? qr0 %)) (map #(vector :mention %))) qr1)
                      (into (filter #(not= (get com0 %) (get com1 %)))
                            (concat (keys com0) (keys com1)))
                      (into (remove #(contains? as1 %)) as0)
                      (into (remove #(contains? as0 %)) as1)
                      (into (remove #(contains? id1 %)) id0)
                      (into (remove #(contains? id0 %)) id1)
                      (into (filter #(not= (get mt0 %) (get mt1 %)))
                            (concat (keys mt0) (keys mt1)))
                      (into (filter #(not= (get ds0 %) (get ds1 %)))
                            (concat (keys ds0) (keys ds1)))
                      (into (comp (remove #(contains? rf1 %)) (map #(vector :reifiable %))) rf0)
                      (into (comp (remove #(contains? rf0 %)) (map #(vector :reifiable %))) rf1)
                      (into (comp (filter #(or (contains? rf0 %) (contains? rf1 %)))
                                  (map #(vector :reifiable %)))
                            (concat (remove #(contains? sym1 %) sym0) (remove #(contains? sym0 %) sym1)
                                    (filter #(not= (get com0 %) (get com1 %))
                                            (concat (keys com0) (keys com1))))))]
        (when (seq moved)
          (swap! (reasoning/respell kb) into moved))))))

(defn reconcile-belief-change
  "Reconcile every belief-derived taxonomy cache after `moved` may have changed truth.
  Stores nothing; re-running it recomputes from current belief.  `moved` may name
  declaration handles or except handles (expanded to their targets by
  `belief-change-region`).  The scoped read filters through `res/supporter-believed?` and
  is keyed on the change clock, which every write moves."
  ([kb] (reconcile-belief-change kb nil))
  ([kb moved]
   (let [region (when (some? moved) (belief-change-region kb moved))
         before (permuting-marks (reasoning/taxonomy kb))]
     (tax/refresh-beliefs (reasoning/taxonomy kb) (partial jtms/in? (reasoning/tms kb)) region)
     (note-permuting-moves! kb before))))

;; In-file cycle through the table: `derived-sentex-added` calls `wff-problems` and
;; `wff-violation`, which walk the table whose arms call it.  Four declares close it.
(declare derived-sentex-added integrate-twin wff-problems wff-violation)

(defn taxonomy-generations
  "The `genl` and `genlCx` generations with the rebuild epoch (`tax/relation-epoch`), the
  value `conviction-generations` extends with the separations.  A caller re-asks an entry
  only when this moves from the value the entry records, so the recorded value and the
  comparison are this one function.  The epoch moves at every `recover`, which restarts the generations at 0."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    [(tax/relation-epoch tax) (tax/relation-gen tax :genl) (tax/relation-gen tax :genlCx)]))

(defn conviction-generations
  "`taxonomy-generations` with the separations (`tax/separation-inputs`): the value an
  argument conviction is decided under, an argument hold's
  (`checks/refresh-argument-holds!`).  A conviction reads a type the taxonomy separates
  from the declared one, so a separation moving re-asks it."
  [kb]
  (conj (taxonomy-generations kb) (tax/separation-inputs (reasoning/taxonomy kb))))

;; ---- the argument constraints, drawn as entailments ----------------------
;; Each entailment is a derived sentex justified by `[triggering fact, declaration]`, as
;; the lift is.  `deduce-arg-types` is fact-meets-declaration, `entail-existing`
;; declaration-meets-facts, so belief does not depend on arrival order.

(defn naming-violation
  "The `:naming` violation `sentence` in `context` carries under `kb`'s naming policy, or
  nil: `nm/blocking-problems` as the value a caller that may not throw drops a sentence
  for.  Nil under `:warn` and `:off`."
  [kb sentence context]
  (when-let [ps (nm/blocking-problems (:naming kb) sentence context)]
    {:violation :naming
     :detail    {:message (str "naming invariant: " (str/join "; " ps))}}))

(defn inadmissible
  "The violation that stops `sentence` from being stored in `context`, or nil: naming,
  the definitional constraints, well-formedness and edge stratification.  Returns a
  value and never throws, since its callers run after their triggering sentex is stored
  (argument-type entailment, the computed `genlCx` edge of `context-nat`) or must refuse a
  hypothesis without failing the query (abduction).
  `constraint-arm` is `checks/constraint-violation` by default; a nil arm omits the
  definitional-constraint check for a caller that already ran it.  See docs/argtypes.md."
  ([kb sentence context] (inadmissible kb sentence context checks/constraint-violation))
  ([kb sentence context constraint-arm]
   (or (naming-violation kb sentence context)
       (when constraint-arm (constraint-arm kb sentence context))
       (wff-violation kb sentence context)
       (checks/edge-stratification-violation kb sentence))))

(def ^:private empty-entailment-result
  "What an entailment step that minted nothing returns, and the seed of every reduce that
  `merge-with into`s step results, so the accumulator and the steps have one shape."
  {:new [] :violations []})

(def ^:private route-functors
  "The edges a route names: `genl` between predicates, a `covering`, `separating` or
  `partition` for the edge it installs per part (`tax/installed-edges`), and `genlCx`."
  '#{genl genlCx covering separating partition})

(defn- route-sentence?
  [sentence]
  (and (seq? sentence) (contains? route-functors (nm/functor sentence))))

(defn- edge-functor
  "The functor of the sentex at `h` when it is an edge a route names (`route-functors`),
  and nil for anything else."
  [kb h]
  (let [s (:sentence (p/get-sentex (:records kb) h))]
    (when (route-sentence? s) (nm/functor s))))

(defn- route-edge?
  "Is the sentex at `h` an edge a route names (`route-functors`)?"
  [kb h]
  (some? (edge-functor kb h)))

(defn- firing-bindings
  "A justification's bindings less the join's context variable `?ctx`, which one join
  binds and a re-join under an arriving edge does not, for the same firing."
  [j]
  (dissoc (:bindings j) '?ctx))

(defn- same-pairing?
  "Do `just` and `j` pair their facts with the same literals: equal subsumptions?  A `j`
  with none whose `extra` antecedents name a `genl` edge or a cover was written before
  subsumptions were recorded, and pairs as `just` does (docs/nmtms.md, \"Where the layer
  stops\")."
  [kb just j extra]
  (or (= (:subsumptions just) (:subsumptions j))
      (and (nil? (:subsumptions j)) (some #(some-> (edge-functor kb %) (not= 'genlCx)) extra))))

(defn drop-replaced-routes!
  "Drop the justifications the one just added as `just` replaces: the same firing over
  a route the witness rule no longer names.  Returns the merged
  `jtms/drop-justification!` results for the caller to apply to its stores; the dropped
  records are deleted here.  A justification is replaced when it has `just`'s informant,
  consequence, bindings and subsumptions (`same-pairing?`), holds every antecedent of
  `just` outside `route`, and differs only in believed `genl` / `genlCx` edges.  `route`
  is `just`'s route handles; nil reads them off the antecedents.  An edge that is OUT
  keeps its justification (docs/nmtms.md, \"Where the layer stops\")."
  ([kb just] (drop-replaced-routes! kb just nil))
  ([kb just route]
   (let [tms  (reasoning/tms kb)
         recs (:records kb)
         h    (:consequence just)
         sups (jtms/supports tms h)]
     (when (< 1 (count sups))
       (let [antes    (set (:antecedents just))
             core     (reduce disj antes (or route (filter #(route-edge? kb %) antes)))
             replaced (fn [jid]
                        (let [j     (jtms/justification tms jid)
                              a     (set (:antecedents j))
                              extra (reduce disj a core)]
                          (and (not= jid (:id just))
                               (= (:informant just) (:informant j))
                               (seq extra)
                               (= (count core) (- (count a) (count extra)))
                               (every? #(and (jtms/in? tms %) (route-edge? kb %)) extra)
                               (same-pairing? kb just j extra)
                               (= (firing-bindings just)
                                  (firing-bindings (p/get-justification recs jid))))))
             ;; a replaced support holds every member of `core`, so it is a dependent
             ;; of the first antecedent when that is in `core`: a fact's dependents are
             ;; its own firings and mints, where a mint named by n facts has n supports
             lead     (first (:antecedents just))
             deps     (when (contains? core lead) (jtms/dependents tms lead))
             gone     (filterv replaced
                               (if (and deps (< (count deps) (count sups)))
                                 (sort (filter #(= h (:consequence (jtms/justification tms %))) deps))
                                 sups))]
         (reduce (fn [acc jid]
                   (let [r (jtms/drop-justification! tms jid)]
                     (p/delete-justification! recs jid)
                     (merge-with into acc r)))
                 nil gone))))))

;; ---- the mint family (docs/indexing.md, "The mint family") ----------------------

(defn- mint-rule-handle!
  "The handle of `kind`'s rule of `kv/mint-rules`, stored first when `kb` does not hold it: a
  `:default` premise in `kv/mint-rule-context`, as `core.txt` states it, marked in the network and the record store
  as `assert-entry/put-premise-mark` marks one, and indexed as an asserted rule is
  (`index-rule-sentex`).  Inert, so storing it chains nothing."
  [kb kind]
  (or (get (kb/mint-rule-table kb) kind)
      (let [[h s] (kb/create-sentex kb (kv/mint-rules kind) kv/mint-rule-context :default)]
        (jtms/add-premise (reasoning/tms kb) h :default)
        (p/mark-premise (:records kb) h :default)
        (index-rule-sentex kb h s)
        h)))

(defn- store-declared-mint-rule!
  "Store the rule of `kv/mint-rules` for the kind of `sentex` when it is an entailing
  declaration (a kind of `kv/mint-rules`, at its declared arity) and `kb` lacks the rule
  (`mint-rule-handle!`).  The integration choke points call it, so a KB holds a kind's
  rule from its first declaration of that kind, in every arrival order and under either
  reading of the declarations.  Every other sentex costs a field read and a set lookup."
  [kb sentex]
  (when (nil? (:antecedent sentex))
    (let [s (:sentence sentex)
          f (nm/functor s)]
      (when (and (contains? kv/mint-rules f)
                 (= (get entailing-declarations f (when (= 'resultArg f) 2)) (nm/arity s)))
        (mint-rule-handle! kb f)))))

(defn- membership-shaped?
  "Is `sentence` a membership `(t x)` of one symbol in another?  A membership subsumes a
  mint of any supertype over the same term, and this test reads no index, so
  `subsumed-mint-blocks` runs it on every sentex a settle moved."
  [sentence]
  (and (= 1 (nm/arity sentence)) (symbol? (nm/functor sentence))
       (symbol? (first (nm/args sentence)))))

(defn- edge-shaped?
  "Is `sentence` a `genl` edge `(genl x S)`: a minted edge, or the one record that
  subsumes a mint out of `x` by itself (`says-more-than?`)?"
  [sentence]
  (and (= 'genl (nm/functor sentence)) (= 3 (count sentence)) (symbol? (nth sentence 1))))

(defn- context-edge-shaped?
  "Is `sentence` a `genlCx` edge, which shows the contexts under `sub` memberships and
  edges they could not see?"
  [sentence]
  (and (= 'genlCx (nm/functor sentence)) (= 3 (count sentence)) (symbol? (nth sentence 1))))

(defn- subsumer-shaped?
  "Can `sentence` subsume a mint?  A membership can, and so can a record that gives terms
  a route they did not have: a `genl` edge or a cover (`tax/installed-edges`), or a `genlCx`
  edge."
  [sentence]
  (or (membership-shaped? sentence) (seq (tax/installed-edges sentence))
      (context-edge-shaped? sentence)))

(defn- closes-genl-cycle?
  "Does a `genl` edge `sentence` installs (`tax/installed-edges`) lie on a cycle of the
  unscoped closure?  Two types in a cycle are coextensive where the cycle is seen, so a
  membership in one no longer withholds a mint of the other there (`tax/strict-genl?`):
  the edge's arrival releases as an edge's departure does.  A candidate filter: each
  released mint is asked again from its own placement."
  [tax sentence]
  (boolean (some (fn [[sub super]] (tax/genl?-global tax super sub)) (tax/installed-edges sentence))))

(defn- mint-term
  "The term the mint family files `sentence` under — `x` of a membership `(t x)` or of an
  edge `(genl x t)` — or nil for a shape no membership or edge can make redundant."
  [sentence]
  (when (or (membership-shaped? sentence) (edge-shaped? sentence))
    (second sentence)))

(defn post-mint!
  "File record `h`, holding `sentence` in `context` and concluded by a stored justification
  `kb/mint-informant?` accepts, in `index`'s mint family, when the sentence has a
  `mint-term`.  Posted from the sentence in hand: `entail-arg-type` as it stores the
  justification, and `reindex` from the record it is indexing."
  [index sentence context h]
  (when-let [x (mint-term sentence)]
    (p/family-apply! index [[:post :mint [x context] h] [:post :mint-in [context] h]])))

(defn unpost-mint!
  "The mirror of `post-mint!`: take record `h`, holding `sentence` in `context`, out of
  `index`'s mint family, when the sentence has a `mint-term`."
  [index sentence context h]
  (when-let [x (mint-term sentence)]
    (p/family-apply! index [[:retire :mint [x context] h] [:retire :mint-in [context] h]])))

(defn retire-mint!
  "Take the departing `sentex` out of the mint family, when it is filed there."
  [kb sentex]
  (unpost-mint! (:index kb) (sx/sentence-of sentex) (:context sentex) (:id sentex)))

(defn refile-mint!
  "Bring record `h`'s entry in the mint family to its stored spelling: out from under the
  filing term of `old`, the record `h` held before (nil when its spelling did not move),
  and under the current one while a mint justification concludes it.  The callers are the
  store mutations that move a record's spelling (`integrate/respell!`) or the
  justifications concluding it (`integrate/fold-row!`)."
  [kb old h]
  (some->> old (retire-mint! kb))
  (let [tms (reasoning/tms kb)]
    (when (some #(kb/mint-informant? kb (:informant (jtms/justification tms %))) (jtms/supports tms h))
      (when-let [sx (p/get-sentex (:records kb) h)]
        (post-mint! (:index kb) (sx/sentence-of sx) (:context sx) h)))))

(defn retire-unjustified-mints!
  "Take out of the mint family each record a mint justification removed in `removals`
  concluded, once no other mint justification concludes it.  `removals` is a
  `jtms/retract!`-shaped result, whose `:removed-supports` names each removed
  justification's consequence and informant, read off the network before the removal.  A
  consequence the removal swept leaves through `retire-mint!`; one still in the network
  is retired here, and its record is the one fetch."
  [kb removals]
  (let [tms (reasoning/tms kb)]
    (doseq [h (into (sorted-set)
                    (keep (fn [[c informant]] (when (kb/mint-informant? kb informant) c)))
                    (:removed-supports removals))
            :when (and (jtms/known-datum? tms h)
                       (not-any? #(kb/mint-informant? kb (:informant (jtms/justification tms %)))
                                 (jtms/supports tms h)))
            :let [sx (p/get-sentex (:records kb) h)]
            :when sx]
      (retire-mint! kb sx))))

;; In-file cycles: `entail-arg-type` calls `deduce-placed` for a minted type's own
;; entailments; `restate-retired` calls `migrate-sentex`, whose twin runs
;; `integrate-twin` and the declaration arms; `deduce-lifts` draws entailments through
;; `deduce-placed`.
(declare deduce-lifts deduce-placed restate-retired)

(def ^:private ^:dynamic *admission-memo*
  "nil, or a volatile `{[sentence context checked?] answer}` of what `inadmissible` said of
  a mint, which `entail-arg-type` reads before asking again.  `rederive-mints` and
  `entail-over` bind one per call: the facts naming one term draw a handful of distinct
  mints, each from many of them, and the checks read neither the fact nor the
  justification.  What they read is the stored content and belief, so the memo is emptied
  whenever a mint is created or restated or a justification brings one IN; a
  justification added to a mint already IN moves neither."
  nil)

(def ^:private ^:dynamic *fact-deadline*
  "nil, or the `budget/now` instant past which the fact a pass is drawing is set aside
  (`draw-fact`).  The checks a mint reads before it writes run under it (`within-fact`),
  and the writes never do (`outside-fact`), so the throw lands before a mint is stored or
  after it is justified, never between."
  nil)

(def ^:private ^:dynamic *transitions*
  "nil, or a volatile vector of `[handle new?]`, each mint the fact a pass is drawing
  brought IN, filed before its own entailments are drawn.  A fact set aside part-way names
  them, and its re-run draws theirs (`redraw-deferred`): the mints are stored and
  justified by then, so drawing the fact again reaches them as dedup targets and would
  not cascade from them."
  nil)

(defn- within-fact
  "`(f)`, the read-only part of a mint, under the drawn fact's deadline (`*fact-deadline*`)
  with `phase` named for the signal; `(f)` when no pass set one."
  [phase f]
  (if-let [dl *fact-deadline*]
    (binding [budget/*unit-deadline* dl]
      (budget/unit-phase! phase)
      (budget/check-unit!)
      (f))
    (f)))

(defn- outside-fact
  "`(f)` with no fact deadline, for a write that may draw mints of its own (a restatement,
  a route dropped): it runs to its end."
  [f]
  (if *fact-deadline*
    (binding [*fact-deadline* nil] (f))
    (f)))

(defn- entail-arg-type
  "Materialize one entailment: store `(:assert ent)` in `context` and justify it by
  `[src-handle, the declaration, the genl edges it descended through]`.  Returns
  `{:new [handle] :violations [v]}`: the handle when the sentex was newly created, the
  violation when it could not be admitted.  Depth is one past the deepest supporter and
  the strength is `conferred-class`'s.  The informant is the inert rule of the declaring
  kind (`kv/mint-rules`, `mint-rule-handle!`); an arity-class membership (`:class`) keeps
  its `declaredType` informant.  A created sentex or a fresh justification that brings an
  out node in draws its own entailments.  See docs/argtypes.md."
  [kb ent src-handle context pre-checked?]
  (let [sentence (:assert ent)
        because  (vec (:because ent))
        memo     *admission-memo*
        ;; one inheritance memo for the whole ask: its cover arm asks the inheritance
        ;; prover a denial per part, and the ask writes nothing
        ask      #(within-fact :admission
                               (fn []
                                 (inherit/with-memo
                                   (inadmissible kb sentence context
                                                 (when-not pre-checked? checks/derivation-violation)))))
        k        [sentence context (boolean pre-checked?)]]
    ;; a pass past the drawn fact's deadline sets the fact aside here, before this mint
    ;; reads or writes anything
    (when *fact-deadline* (within-fact :mints (constantly nil)))
    ;; A type the KB already holds more specifically is withheld only where there is no
    ;; record yet, and `subsumed-mint-blocks` withdraws it when the specific membership
    ;; arrives last (docs/argtypes.md, "Nothing is withheld for redundancy").  The stored
    ;; handle is read once and both branches share it: a dedup to a stored record is the
    ;; common case per assert (`assert_cost_test`'s `declared` workload).  A withheld mint
    ;; is decided before the admission checks, since it stores nothing
    ;; (`withheld-mint-beside-covers`).  An arity-class membership (`:class`) is never
    ;; withheld (`unary-entailments`).
    (let [stored (kb/find-sentex-handle kb sentence context)
          class? (:class ent)]
      (if (and (not class?)
               (within-fact
                :subsumed
                #(or (and (not stored) (checks/subsumed-mint kb sentence context))
                     ;; an ingredient an `except` hides from `context`, as a rule firing is
                     ;; not placed there (`except-move-sweeps` drops one the except meets)
                     (when-let [hidden? (exc/except-hidden-fn kb context)]
                       (or (hidden? src-handle) (some hidden? because))))))
        empty-entailment-result
        (if-let [v (if memo
                     (caches/get-or! memo k ask)
                     (ask))]
          {:new [] :violations [(assoc v :sentence sentence :context context
                                       :entailed-from src-handle)]}
          (let [[h2 s2 new?] (if stored
                               [stored (p/get-sentex (:records kb) stored) false]
                               (let [[h sx] (kb/create-sentex kb sentence context nil)]
                                 [h sx true]))]
            (if (= h2 src-handle)
              empty-entailment-result
              (do
                ;; a derived sentex in a context that did not have it: it reaches the
                ;; closures and posts its exception re-check trigger exactly as a rule
                ;; conclusion does
                (when new? (outside-fact #(derived-sentex-added kb s2 h2)))
                (let [antes  (into [src-handle] because)
                      depth  (inc (long (reduce max (map #(jtms/depth (reasoning/tms kb) %) antes))))
                      _      (jtms/ensure-node (reasoning/tms kb) h2 depth)
                      ;; a mint names its kind's inert rule; an arity-class membership
                      ;; names `declaredType`
                      inf    (if class? (:kind ent) (outside-fact #(mint-rule-handle! kb (:kind ent))))
                      fresh? (not (or (jtms/has-justification? (reasoning/tms kb) inf antes h2)
                                      (and (not class?)
                                           (jtms/has-justification? (reasoning/tms kb) (:kind ent) antes h2))))
                      ;; `was-in?` records whether `h2` is already believed by another support,
                      ;; read before this justification is added.  It is an O(1) fixpoint read
                      ;; (`jtms/in?`), not an index read, and the cascade below reads it.
                      was-in? (jtms/in? (reasoning/tms kb) h2)]
                  (when (and memo (or new? (and fresh? (not was-in?))))
                    (vreset! memo {}))
                  (when fresh?
                    (let [jid  (p/next-id (:records kb))
                          just (jtms/->just jid inf antes h2 {} :monotonic)]
                      (p/put-justification (:records kb) just)
                      ;; no rule fired: a write's audit of its firings' conclusions
                      ;; (`observe/*fired-sink*`) does not take a mint
                      (binding [observe/*fired-sink* nil]
                        (jtms/add-justification (reasoning/tms kb) just))
                      (when-not class? (post-mint! (:index kb) sentence context h2))
                      ;; the route this pair named before is replaced; `just` holds the
                      ;; mint up, so the drop sweeps nothing and only the records go
                      ;; a trigger membership is an ingredient, not a route
                      (when-not new?
                        (outside-fact
                         #(drop-replaced-routes! kb just
                                                 (cond->> (rest because)
                                                   (:trigger ent) (remove #{(:trigger ent)})))))))
                  (when-let [t *transitions*]
                    (when (or new? (and fresh? (not was-in?)))
                      (vswap! t conj [h2 new?])))
                  (merge-with into
                              {:new (if new? [h2] []) :violations []}
                              ;; Recur only on a transition to believed: a created sentex, or a fresh justification
                              ;; that brings an out node in (docs/argtypes.md).
                              (if (or new? (and fresh? (not was-in?)))
                                (deduce-placed kb sentence h2 context)
                                empty-entailment-result)
                              ;; a new mint lifts into CxUniverse as an asserted fact does;
                              ;; one stored before the declaration is `lift-existing`'s
                              (when new?
                                (let [r (outside-fact #(deduce-lifts kb sentence h2 context))]
                                  ;; the copy is content the admission checks read
                                  (when (and memo (seq (:new r))) (vreset! memo {}))
                                  r))
                              (when new?
                                (let [r (outside-fact #(restate-retired kb s2))]
                                  ;; a restatement can write a twin and supersede `s2`
                                  (when memo (vreset! memo {}))
                                  r))))))))))))

(defn deduce-arg-types
  "Materialize the entailments `checks/constraint-entailments` drew over a sentence
  stored at `handle` in `context`: `{:new [handles] :violations [v]}`.  Called from
  `assert` and from forward chaining's `place-conclusion`.  `pre-checked?` skips the
  definitional constraint check of each mint (`inadmissible`); only the assert path's
  first level passes true."
  ([kb entailments handle context] (deduce-arg-types kb entailments handle context false))
  ([kb entailments handle context pre-checked?]
   (reduce (fn [acc e] (merge-with into acc (entail-arg-type kb e handle context pre-checked?)))
           empty-entailment-result
           entailments)))

(def ^:private trigger-declarations
  "The entailing declarations whose derivation waits on a trigger membership: `interArg`
  and the homogeneity forms (`checks/trigger-supports`)."
  '#{interArg interArgs interArgAndRest})

(defn- trigger-types
  "The types the stored `interArg` and homogeneity declarations read a trigger at: `T` of
  `(interArg P n T m U)`, `(interArgs R T)` and `(interArgAndRest R n T)`."
  [kb]
  (let [idx (:index kb) recs (:records kb)]
    (into #{}
          (comp (mapcat (fn [k] (map #(vector k %) (reads/as-stored-with-functor idx k))))
                (keep (fn [[k h]]
                        (let [s (:sentence (p/get-sentex recs h))]
                          (when (and (seq? s) (= k (nm/functor s)))
                            (case k
                              interArg        (when (= 6 (count s)) (nth s 3))
                              interArgs       (when (= 3 (count s)) (nth s 2))
                              interArgAndRest (when (= 4 (count s)) (nth s 3)))))))
                (filter symbol?))
          (sort trigger-declarations))))

(defn- facts-naming
  "The stored facts holding the symbol `x` as an argument, snapshotted before any mint
  is written."
  [kb x]
  (let [recs (:records kb)]
    (into []
          (comp (keep #(p/get-sentex recs %))
                (filter #(some #{x} (rest (:sentence %)))))
          (reads/as-stored-with-term (:index kb) x))))

(defn- trigger-alternatives
  "nil when the declaration `dsentence` waits on no trigger (`trigger-declarations`).  Else
  the ingredients each trigger of the fact `sentence` adds to a mint's placement, as a
  vector of `[handle ctx]` vectors: per believed membership `(T' x)` anywhere that makes a
  trigger argument `x` a `T`, the membership with the supporters of one `genl` route from
  `T'` to `T` (`tax/general-reach-supports`).  Empty when no membership makes a trigger.  A
  homogeneity trigger counts only beside another argument of its suffix to mint over."
  [kb sentence dsentence]
  (let [k (nm/functor dsentence)]
    (when (contains? trigger-declarations k)
      (let [as        (vec (rest sentence))
            at        #(when (and (integer? %) (<= 1 % (count as))) (nth as (dec %)))
            [t terms] (case k
                        interArg        [(nth dsentence 3 nil) [(at (nth dsentence 2 nil))]]
                        interArgs       [(nth dsentence 2 nil) as]
                        interArgAndRest [(nth dsentence 3 nil)
                                         (let [n (nth dsentence 2 nil)]
                                           (if (and (integer? n) (pos? n))
                                             (subvec as (min (dec n) (count as)))
                                             []))])
            terms     (filter #(and (symbol? %) (not (sx/variable? %))) terms)
            terms     (if (= 'interArg k)
                        terms
                        (filter (fn [x] (some #(not= x %) terms)) terms))
            tax       (reasoning/taxonomy kb)]
        (if-not (symbol? t)
          []
          (into []
                (for [x terms
                      m (res/type-memberships kb x)
                      :let [t' (nm/functor (:sentence m))]
                      r (if (= t' t) [[]] (tax/general-reach-supports tax :genl t' t nil))]
                  (into [[(:id m) (:context m)]] r))))))))

(defn- sees-under?
  "Is `via` above `pred` through the `genl` edges `fc` sees: a member of `pred`'s scoped
  closure (`tax/genls`), the closure the fact's own declarations are read through
  (`checks/constraint-entailments`).  The closure cache holds it while the change clock
  stands, so the facts of one functor ask it once, not once per declaration each."
  [tax pred via fc]
  (contains? (tax/genls tax pred fc) via))

(defn pair-placements
  "The contexts a mint drawn over the fact `fsx` through the declaration `dsx` (sentexes)
  is placed in, in content order: each maximal context that sees every ingredient of the
  derivation where no `except` hides one (docs/argtypes.md, \"Where a mint is placed\").
  Empty when no context sees them all.  Ingredients beyond the fact and declaration are a
  `genl` route's supporters (`tax/general-reach-supports`) and a trigger's
  (`trigger-alternatives`); placements are taken per combination and the most general
  kept.  Past an `except`, `res/exception-aware-placements` places each combination."
  [kb fsx dsx]
  (let [tax    (reasoning/taxonomy kb)
        fc     (:context fsx)
        dc     (:context dsx)
        pred   (nm/functor (:sentence fsx))
        via    (second (:sentence dsx))
        direct (or (= pred via) (not (symbol? pred)) (not (symbol? via)))
        alts   (or (trigger-alternatives kb (:sentence fsx) (:sentence dsx)) [[]])
        sees?  #(tax/sees? tax fc %)
        hid?   (if (reads/stores-any? (:index kb) sx/except-functor)
                 (memoize #(exc/closure-excepted-anywhere? kb %))
                 (constantly false))
        base   [[(:id fsx) fc] [(:id dsx) dc]]]
    (if (and (sees? dc)
             (or direct (sees-under? tax pred via fc))
             (some (fn [alt] (every? (comp sees? second) alt)) alts)
             (not (hid? (:id fsx))) (not (hid? (:id dsx))))
      [fc]
      (let [routes (if direct [] (tax/general-reach-supports tax :genl pred via nil))
            cands  (into #{}
                         (for [r   (if (seq routes) routes [[]])
                               alt alts
                               :let [ings (-> base (into r) (into alt))
                                     hs   (into [] (comp (map first) (remove nil?)) ings)
                                     cs   (into [] (comp (map second) (remove nil?)) ings)]
                               c   (if (some hid? hs)
                                     (res/exception-aware-placements kb hs cs)
                                     (tax/maximal-common-descendant-contexts tax cs))]
                           c))]
        (nm/sort-by-content-key
         nm/name-key compare
         (remove (fn [c] (some #(and (not= c %) (tax/sees? tax c %) (not (tax/sees? tax % c)))
                               cands))
                 cands))))))

(defn- placements-of
  "`pair-placements` of the declaration stored at `dh` against a stored fact, as a fn of
  the fact's sentex, memoized on its context and functor for one sweep over a lattice that
  does not move under it.  A trigger declaration's placements read the fact's arguments
  (`trigger-alternatives`), and while an `except` is stored they read the fact's handle,
  so neither is memoized."
  [kb dh]
  (let [dsx  (p/get-sentex (:records kb) dh)
        each (or (contains? trigger-declarations (nm/functor (:sentence dsx)))
                 (reads/stores-any? (:index kb) sx/except-functor))
        memo (volatile! {})]
    (fn [fsx]
      (if each
        (pair-placements kb fsx dsx)
        (let [k [(:context fsx) (nm/functor (:sentence fsx))]]
          (or (get @memo k)
              (let [pl (pair-placements kb fsx dsx)]
                (vswap! memo assoc k pl)
                pl)))))))

(defn- placements-of-pair
  "`pair-placements` of the fact stored at `f` and the declaration stored at `d`."
  [kb f d]
  (let [recs (:records kb)
        fsx  (p/get-sentex recs f)
        dsx  (p/get-sentex recs d)]
    (if (and fsx dsx) (pair-placements kb fsx dsx) [])))

(defn- declarations-below
  "The stored entailing declarations binding the tuples of the fact `sentence` whose
  placements against `context` (`pair-placements`) are other than `context` itself, as
  `[handle placements]` pairs in content order: the declarations a fact stated in
  `context` meets below it, where they, a `genl` route or a trigger are stated.

  Read off each declaring kind's argument root at `pred` and at each super-predicate the
  kind's `:props` set names (`tax/props-over`), so the read is bounded by the declarations
  written of `pred`'s ancestors.  The super-predicates are read over every `genl` edge,
  since an edge stated below `context` binds `pred` there; each candidate is asked again
  from its placement (`checks/declaration-entailments`).  Empty, with no index read, when
  no `genlCx` edge comes up to `context` (`tax/context-children-global`); CxUniverse
  reads every posting whole.  A posting whose count exceeds `context`'s descendants is
  read narrowed to the contexts that share a descendant with `context`, so a declaration
  in a context no descendant sees is not read.  A `natFormula` fact meets the
  `resultArg`s written of its expression's function, read off their argument root."
  [kb sentence handle context]
  (let [tax  (reasoning/taxonomy kb)
        pred (nm/functor sentence)
        fsx  {:id handle :context context :sentence sentence}]
    (if-not (and (symbol? pred) (or (tax/root-context? context)
                                    (seq (tax/context-children-global tax context))))
      []
      (let [idx   (:index kb)
            recs  (:records kb)
            root? (tax/root-context? context)
            down  (delay (tax/context-down tax context))
            ;; the contexts sharing a descendant with `context`, read when a posting holds
            ;; more declarations than `context` has descendants
            meets (delay (into #{} (mapcat #(tax/context-up tax %)) @down))]
        (into []
              (concat
               (for [k     (nm/sort-by-content-key nm/name-key compare (keys entailing-declarations))
                     s     (nm/sort-by-content-key
                            nm/name-key compare
                            (tax/props-over tax (tax/arg-declaration-props k) pred))
                     h     (sort (if (or root?
                                         (<= (reads/stored-count-with-arg-in idx k 1 s p/every-context)
                                             (count @down)))
                                   (reads/as-stored-with-args idx k {1 s})
                                   (reads/as-stored-with-args-in idx k {1 s} @meets)))
                     :let  [dsx (p/get-sentex recs h)]
                     :when (and dsx (= (entailing-declarations k) (nm/arity (:sentence dsx)))
                                (= s (second (:sentence dsx))))
                     :let  [pl (pair-placements kb fsx dsx)]
                     :when (and (seq pl) (not= [context] pl))]
                 [h pl])
               ;; a `natFormula` fact meets the `resultArg`s written of its function
               (let [e (nth sentence 2 nil)]
                 (when (and (= 'natFormula pred) (sequential? e) (symbol? (first e)))
                   (for [h     (sort (reads/as-stored-with-args idx 'resultArg {1 (first e)}))
                         :let  [dsx (p/get-sentex recs h)]
                         :when (and dsx (= 2 (nm/arity (:sentence dsx))))
                         :let  [pl (pair-placements kb fsx dsx)]
                         :when (and (seq pl) (not= [context] pl))]
                     [h pl])))))))))

(defn- below-entailments
  "What the declarations `declarations-below` finds say about the fact `sentence` stored
  at `handle` in `context`, as `[entailments placement]` pairs, one per placement
  (`checks/declaration-entailments`)."
  [kb sentence handle context]
  (let [below (declarations-below kb sentence handle context)]
    (into [] (for [[dh pl] below, pctx pl]
               [(checks/declaration-entailments kb sentence pctx dh handle) pctx]))))

(defn- inert-handle?
  "Is the sentex at `id` inert (`assert-inert`, or one `import!` restored): no premise, no
  justification concluding it, and stored with no strength?  A derived sentex has a
  justification even when defeated, so the three read an inert one apart from it.  The
  two TMS reads come first and settle a premise or a derived sentex without a record
  fetch."
  [kb id]
  (let [tms (reasoning/tms kb)]
    (boolean (and id
                  (not (jtms/premise? tms id))
                  (empty? (jtms/supports tms id))
                  (when-let [sx (p/get-sentex (:records kb) id)] (nil? (:strength sx)))))))

(defn deduce-below
  "Materialize what the declarations `declarations-below` finds say about the fact
  `sentence` stored at `handle` in `context`, at each of their placements:
  `{:new [handles] :violations [v]}`.  Each mint names the fact, the declaration and the
  `genlCx` edges its placement sees both through (`checks/declaration-entailments`).  The
  assert path and `chain/place-conclusion` call it beside `deduce-arg-types`.  `keep?`,
  when given, takes an entailment and its placement."
  ([kb sentence handle context] (deduce-below kb sentence handle context nil))
  ([kb sentence handle context keep?]
   (if-not argument/*assertive-arg-types?*
     empty-entailment-result
     (reduce (fn [acc [es pctx]]
               (merge-with into acc
                           (deduce-arg-types kb (cond->> es keep? (filterv #(keep? % pctx)))
                                             handle pctx)))
             empty-entailment-result
             (within-fact :below #(below-entailments kb sentence handle context))))))

(defn- deduce-placed
  "Materialize every entailment of the stored literal fact `sentence` at `handle` in
  `context`: those of the declarations `context` sees, there (`deduce-arg-types`), and
  those of the declarations below it, at their placements (`deduce-below`).  `keep?`,
  when given, takes an entailment and its placement.  An inert sentex draws none
  (`inert-handle?`), whichever sweep reaches it."
  ([kb sentence handle context] (deduce-placed kb sentence handle context nil))
  ([kb sentence handle context keep?]
   (if (inert-handle? kb handle)
     empty-entailment-result
     (merge-with into
                 (deduce-arg-types
                  kb (cond->> (within-fact :entailments
                                           #(checks/constraint-entailments kb sentence context))
                       keep? (filterv #(keep? % context)))
                  handle context)
                 (deduce-below kb sentence handle context keep?)))))

(defn redraw-mints
  "Draw the argument-type entailments of the stored literal fact at `h` over the spelling
  it holds now, after a store mutation moved that spelling (`integrate/move-row!`):
  `[drawn stale]`.  `drawn` is `deduce-placed`'s `{:new :violations}`.  `stale` holds the
  ids of the mint justifications `h` triggers that this spelling does not draw, for the
  caller to drop.  A declaration reads the argument at its own position, so a mint drawn
  over the spelling the row held before can name the declaration of another position
  (docs/canonicalization.md)."
  [kb h]
  (let [sx (p/get-sentex (:records kb) h)]
    (if-not (and argument/*assertive-arg-types?* (sx/positive-fact? sx))
      [empty-entailment-result []]
      (let [s     (:sentence sx)
            c     (:context sx)
            drawn (deduce-placed kb s h c)
            tms   (reasoning/tms kb)
            owed  (into #{}
                        (map (fn [e] [(:kind e) (into #{h} (:because e)) (:assert e)]))
                        (concat (checks/constraint-entailments kb s c)
                                (mapcat first (below-entailments kb s h c))))]
        [drawn
         (into []
               (filter (fn [jid]
                         (when (kb/mint-informant? kb (:informant (jtms/justification tms jid)))
                           ;; the record keeps the antecedents in the order written, the
                           ;; trigger first; the network need not
                           (let [recs (:records kb)
                                 j    (p/get-justification recs jid)]
                             (and j (= h (first (:antecedents j)))
                                  (not (owed [(kb/mint-kind kb (:informant j)) (set (:antecedents j))
                                              (some-> (p/get-sentex recs (:consequence j))
                                                      sx/sentence-of)])))))))
               (sort (jtms/dependents tms h)))]))))

(defn- retroactive-mints
  "The entailments a newly stored declaration `dh` draws over one already-stored sentex
  `sx`, materialized at each placement of the pair (`placements`, a fn of `sx`'s context;
  `placements-of` by default).  Asks `checks/declaration-entailments`, the narrowing of
  `checks/constraint-entailments`, so both directions agree.  A negation, a rule, an inert
  sentex (`inert-handle?`) and a computed `genlCx` edge
  (`nat-read/computed-genlCx-edge?`) entail nothing.  The fact-side path draws no mint from
  an inert fact, so a sweep that read one would mint on a rechain what the load did not."
  ([kb sx dh] (retroactive-mints kb sx dh (placements-of kb dh)))
  ([kb sx dh placements]
   (if-not (and (sx/positive-fact? sx) (not (inert-handle? kb (:id sx)))
                (not (nat-read/computed-genlCx-edge? kb sx)))
     empty-entailment-result
     (let [sctx (:context sx)
           h    (:id sx)]
       (reduce (fn [acc pctx]
                 (merge-with into acc
                             (deduce-arg-types
                              kb (checks/declaration-entailments kb (:sentence sx) pctx dh
                                                                 (when (not= pctx sctx) h))
                              h pctx)))
               empty-entailment-result
               (placements sx))))))

(defn- subtree-sentexes
  "Every stored sentex whose functor is `pred` or any spec of it, as a vector
  snapshotted before the caller's first write.  Stored rather than believed, and filtered
  by index cardinality before any record is read (docs/taxonomy.md).  With `limit`, stops
  after `limit` sentexes, visiting predicates in content order.  With `contexts`, a set,
  reads only the sentexes stated in one of them (`reads/as-stored-with-functor-in`)."
  ([kb pred] (subtree-sentexes kb pred nil))
  ([kb pred limit] (subtree-sentexes kb pred limit nil))
  ([kb pred limit contexts]
   (let [idx   (:index kb)
         recs  (:records kb)
         preds (filter #(pos? (reads/stored-count-with-functor idx %))
                       (tax/specs-global (reasoning/taxonomy kb) pred))
         read  (if contexts
                 #(reads/as-stored-with-functor-in idx % contexts)
                 #(reads/as-stored-with-functor idx %))]
     (into [] (cond-> (comp (mapcat read)
                            (distinct)
                            (keep #(p/get-sentex recs %)))
                limit (comp (take limit)))
           (cond->> preds limit (sort-by nm/name-key))))))

(defn- result-arg-extent
  "The stored `natFormula` facts whose expression is an application of the function `f`,
  read off the term index, which posts the terms of the expression: the extent a
  `(resultArg f n)` binds."
  [kb f]
  (let [recs (:records kb)]
    (into [] (comp (keep #(p/get-sentex recs %))
                   (filter #(let [s (:sentence %) e (nth s 2 nil)]
                              (and (= 'natFormula (nm/functor s)) (sequential? e) (= f (first e))))))
          (sort (reads/as-stored-with-term (:index kb) f)))))

(defn- trigger-extent
  "The stored sentexes of `pred` and its specs holding the value `v` at argument `n`: the
  extent an `(interArgEqual pred n v m U)` binds.  The value is an `unrepresented_term`,
  which has no argument root, so the extent is read and filtered."
  [kb pred n v]
  (filterv #(= v (nth (:sentence %) n nil)) (subtree-sentexes kb pred)))

(defn- declared-types
  "The types an entailing declaration mints memberships in: the last argument of every
  kind but `interArg` and `interArgEqual`, whose target type is their fifth argument, and
  `argArg`, which names no type of its own: each fact's argument `m` names it.  The type
  is the declaration's last argument in every case."
  [sentence]
  (case (nm/functor sentence)
    (interArg interArgEqual) [(nth sentence 5)]
    argArg   []
    (when (contains? entailing-declarations (nm/functor sentence))
      [(last sentence)])))

(defn- waiting-types
  "The types the declaration `sentence` names that `arity/mintable-type?` refuses, `thing`
  left out: an arity statement binds each to a length other than one.  `thing` mints
  nothing."
  [kb sentence]
  (into [] (remove #(or (= 'thing %) (arity/mintable-type? kb %))) (declared-types sentence)))

(def declared-type-informant
  "The informant of the justification of `(unary_predicate T)` by an argument declaration
  naming `T` (`unary-entailments`).  No mint informant (`kb/mint-informant?`): the membership
  enters no mint family, and only a conflicting length withdraws it
  (`withdrawn-type-entailments`)."
  'declaredType)

(defn- declared-type-justifications
  "The `declaredType` justifications of `(unary_predicate t)` in every context, as
  `[jid declaration-handle]` pairs in id order: one per declaration naming `t` whose sweep
  ran while `t` was mintable (`unary-entailments`).  Every context, since `t`'s length
  holds at every context (`arity/relation-length`) and a declaration's entailment stands
  in the declaration's context, so the read is global."
  [kb t]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (for [h (reads/as-stored-unary-with-arg-global (:index kb) t)
          :let [sx (p/get-sentex recs h)]
          :when (and sx (= (list 'unary_predicate t) (:sentence sx)))
          jid (sort (jtms/supports tms h))
          :let [j (jtms/justification tms jid)]
          :when (= declared-type-informant (:informant j))]
      [jid (first (:antecedents j))])))

(defn withdrawn-type-entailments
  "The `declaredType` justifications of `(unary_predicate T)` to drop for each relation
  `T` of `bound` (the relations whose own arity bindings moved, the keys of
  `arity/drain!`'s `:bound`) whose length no longer admits one alone (`arity/mintable-type?`): an arity
  statement binding `T` to another length arrived after a declaration naming `T` minted.
  `withdrawn-type-mints` drops what it minted.  When the length admits one again,
  `mints-on-lengths` sweeps the declaration.  Returns the justification ids, for the
  caller to drop.  The stored entailment is read before the length, so a binding of a
  relation no declaration names reads no length."
  [kb bound]
  (into []
        (for [t     (sort-by nm/print-key (filter symbol? bound))
              :let  [js (declared-type-justifications kb t)]
              :when (and (seq js) (not (arity/mintable-type? kb t)))
              [jid _] js]
          jid)))

(defn- binds-another-length?
  "Does the moved binding `[kind value]` refuse its type a mint (`arity/unary-consistent?`):
  an exact length other than one, an `arityMin` floor above one, or a `variable_arity`
  release?  Only such a binding's arrival withdraws a mint, and only its departure
  releases one."
  [[kind v]]
  (case kind :exact (not= 1 v) :min (< 1 (long v)) true))

(defn withdrawn-type-mints
  "The mint justifications to drop for each type `t` of `bound` (`arity/drain!`'s
  `:bound`) with a moved binding that refuses a mint (`binds-another-length?`) and an IN
  length that does not admit one (`arity/mintable-type?`), whether or not a length of one
  is IN beside it: those concluding a membership `(t x)` or an edge `(genl x t)`.  A
  record with other support stays.  Returns the justification ids, for the caller to
  drop.  Reads nothing more while the mint family is empty, and reads `t`'s one-argument
  tuples alone.  Every context, since `t`'s length holds at every context
  (`arity/relation-length`)."
  [kb bound]
  (let [idx (:index kb)
        ts  (when (and argument/*assertive-arg-types?* (seq bound)
                       (pos? (reads/stored-mint-count-global idx)))
              (into [] (comp (keep (fn [[t kvs]] (when (some binds-another-length? kvs) t)))
                             (remove #(arity/mintable-type? kb %)))
                    (sort-by (comp nm/print-key key) (filter (comp symbol? key) bound))))]
    (if (empty? ts)
      []
      (let [tms (reasoning/tms kb)]
        (into []
              (for [t  ts
                    h  (concat (sort (reads/as-stored-shape-tuples-global idx t 1))
                               (sort (reads/as-stored-with-args idx 'genl {2 t})))
                    jid (sort (jtms/supports tms h))
                    :when (kb/mint-informant? kb (:informant (jtms/justification tms jid)))]
                jid))))))

;; ---- a mint the KB holds more specifically ---------------------------------
;; `checks/subsumed-mint` reads whether a believed record already says a minted type
;; more precisely.  The mint path withholds a record it answers for; the settle's
;; withdrawal (`subsumed-mint-blocks`) and release (`withheld-releases`) take the other
;; two directions.  A withdrawal blocks the mint's justifications and does not retract
;; them (docs/argtypes.md).

(defn- mint-only?
  "Is `h` a record the argument entailment alone holds up: no premise support, at least
  one justification, and every one of them an argument declaration's?  Read off the
  network, not the store."
  [kb h]
  (let [tms (reasoning/tms kb)]
    (and (not (jtms/premise? tms h))
         (let [js (keep #(jtms/justification tms %) (jtms/supports tms h))]
           (and (seq js) (every? #(kb/mint-informant? kb (:informant %)) js))))))

(defn- rests-on?
  "Does `h` rest on `mint`: is `h` believed no longer once `mint` is forced OUT?

  The one shape a block cannot take: withdrawing the mint would take the membership with
  it, which would release the mint, which would derive the membership again.  The read is
  `jtms/region-in` over the support of `h` (`exc/support`, which stops at a premise), so a
  premise, or a second derivation that does not reach the mint, keeps `h` IN.  The shipped
  ontology has no such pair, and a KB that writes one keeps both records."
  [kb h mint]
  (let [tms    (reasoning/tms kb)
        region (exc/support tms h (constantly false))]
    (and (contains? region mint)
         (not (contains? (jtms/region-in tms region region #{} #{mint} nil #{}) h)))))

(defn- says-more-than?
  "Does the record `by` say, in `context`, what `sentence` says and more precisely?

  The subsumption test `checks/subsumed-mint` makes, asked of **one** candidate rather
  than searched for: the trigger is already holding the record that moved, so running that
  search — the term's slot predicate set, then a fetch per predicate above the type — would be
  looking up what the caller has in hand.  `context` is the mint's, since that is the
  vantage its record is read from, and `by` counts only where that context sees it."
  [kb sentence context by]
  (let [tax (reasoning/taxonomy kb)
        s   (:sentence by)]
    (boolean
     (and (tax/sees? tax context (:context by))
          (cond
            (and (membership-shaped? sentence) (membership-shaped? s))
            (and (= (first (nm/args sentence)) (first (nm/args s)))
                 (tax/strict-genl? tax (nm/functor s) (nm/functor sentence) context))

            (and (edge-shaped? sentence) (edge-shaped? s))
            (and (= (nth sentence 1) (nth s 1))
                 (tax/strict-genl? tax (nth s 2) (nth sentence 2) context)))))))

(defn- withdrawable-mint
  "The handle of the record that makes the mint at `h` redundant, or nil when the mint
  stays.  `by` is the moved record when it is the only possible subsumer, nil when
  `checks/subsumed-mint` must find the subsumer.  The candidate is not `by` itself, is the
  entailment's own record (`mint-only?`), and has a believed subsumer that does not rest
  on it (docs/argtypes.md)."
  [kb h by]
  (when (and (not= h (:id by)) (mint-only? kb h))
    (let [sx (p/get-sentex (:records kb) h)]
      (when (and sx (nil? (:antecedent sx)))
        (if by
          (when (and (says-more-than? kb (:sentence sx) (:context sx) by)
                     (not (rests-on? kb (:id by) h)))
            (:id by))
          (checks/subsumed-mint kb (:sentence sx) (:context sx) #(not (rests-on? kb % h))))))))

(def ^:private withdrawal-hint-chunk
  "`[handle by]` pairs per prefetch hint of the withdrawal loop (`withdrawal-hinter`)."
  256)

(defn- withdrawal-hinter
  "`(fn [pairs] …)` hinting the record store (`cap/prefetcher`) with the records
  `withdrawable-mint` reads for the `[handle by]` pairs: each handle's record, then, for a
  pair with no `by` whose handle is `mint-only?`, the records `checks/subsumed-mint` can
  fetch (`checks/subsumer-reads`).  Two hints a chunk, since the second is read off the
  records the first fetched.  nil when the store does not prefetch."
  [kb]
  (when-let [pf (cap/prefetcher (:records kb))]
    (let [recs (:records kb)]
      (fn [pairs]
        (let [hs (into [] (comp (map first) (distinct)) pairs)]
          (pf hs)
          (pf (into [] (comp (keep (fn [[h by]] (when (and (nil? by) (mint-only? kb h))
                                                  (p/get-sentex recs h))))
                             (filter #(nil? (:antecedent %)))
                             (mapcat #(checks/subsumer-reads kb (:sentence %) (:context %)))
                             (distinct))
                    pairs)))))))

(defn- mint-members-in
  "The terms some mint is about that hold a stored membership `(z x)` with `z` in `below`,
  a spec closure: the members `subtree-sentexes` would name, narrowed to the mint family.
  Reads from the smaller side, by comparing two index cardinalities.  Stored, not
  believed."
  [kb below]
  (let [idx    (:index kb)
        recs   (:records kb)
        specs  (into #{} (filter #(pos? (reads/stored-count-with-functor idx %))) below)
        extent (transduce (map #(reads/stored-count-with-functor idx %)) + 0 specs)]
    (if (< (reads/stored-mint-term-count idx) extent)
      (filter (fn [x]
                (some (fn [h]
                        (when-let [sx (p/get-sentex recs h)]
                          (let [sen (:sentence sx)]
                            (and (membership-shaped? sen)
                                 (= x (first (nm/args sen)))
                                 (contains? specs (nm/functor sen))))))
                      (reads/as-stored-unary-with-arg-global idx x)))
              (reads/as-stored-mint-terms idx))
      (into [] (comp (mapcat #(reads/as-stored-with-functor idx %))
                     (distinct)
                     (keep #(p/get-sentex recs %))
                     (map :sentence)
                     (filter membership-shaped?)
                     (map #(first (nm/args %)))
                     (distinct)
                     (filter #(reads/stored-mint-term? idx %)))
            specs))))

(defn- move-groups
  "The groups of readers the `genlCx` move `m` splits its `:under` into by what each sees
  through the edge alone (`tax/context-move`'s `:gains`), or nil when the sweeps read the
  whole move: under `checks/*whole-move-sweeps?*`, while an `except` reaches a `genlCx`
  supporter, or past `tax/move-gain-readers`."
  [m]
  (when-not checks/*whole-move-sweeps?*
    (some-> (:gains m) deref)))

(defn- stored-count-across
  "The sentexes stored in the contexts `cs`, by index counts."
  ^long [kb cs]
  (let [idx (:index kb)]
    (transduce (map #(reads/stored-count-in-context idx %)) + 0 cs)))

(defn- states-any-of?
  "Does a context of `cs` state a sentex of a functor of `fs`?"
  [kb fs cs]
  (let [idx (:index kb)]
    (boolean (some #(seq (reads/as-stored-with-functor-in idx % cs)) fs))))

(defn- displaceable-contexts
  "The contexts under the `genlCx` move `m` where a placement can lose its place to a more
  general one: `tax/context-move`'s `:displaced`, or every context under the move's `sub`
  while an `except` is stated where a reader there sees it, or while the move reads no
  `:displaced`.  An except can hide an ingredient from the more general context that
  would have held the placement."
  [kb m]
  (let [{:keys [displaced seen]} @(:displaced m)]
    (if (or (nil? displaced) (states-any-of? kb [sx/except-functor] seen))
      @(:under m)
      displaced)))

(defn- plain-gain?
  "`checks/plain-gain?`: may a sweep of a group of readers (`move-groups`) read the facts
  of its gain `g` in place of what the readers, seeing `seen`, saw?  Then every pair or
  meeting the move gives such a reader holds a fact stored in `g` and visible to it."
  [kb g seen]
  (checks/plain-gain? kb g seen))

(defn- gain-subjects
  "The terms the memberships stored in the contexts `gain` type, in content order."
  [kb gain]
  (let [idx  (:index kb)
        recs (:records kb)]
    (into (sorted-set-by #(compare (nm/name-key %1) (nm/name-key %2)))
          (comp (mapcat #(reads/as-stored-in-context idx %))
                (keep #(p/get-sentex recs %))
                (map :sentence)
                (filter membership-shaped?)
                (map #(first (nm/args %))))
          (nm/sort-by-content-key nm/name-key compare gain))))

(defn- edge-mint-plan
  "How the mint withdrawal reads the arriving `genlCx` edge record `sx`, which arrived
  with the edges `off`, over its move (`context-move*` with the reader-class contexts
  `ctxs`): `{:groups [plan …] :displaced #{context}}`, or nil when the move reads no
  groups (`move-groups`).  A group is `{:readers R}` (ask every mint filed in their
  contexts) or `{:gain G :readers R}` (ask what the facts of the gain meet).
  `:displaced` is the contexts under `sub` where a placement can lose its place
  (`displaceable-contexts`)."
  [kb ctxs sx off]
  (let [[_ sub super] (:sentence sx)]
    (when (and (symbol? sub) (symbol? super))
      (let [m (context-move* kb ctxs sub super off)]
        (when-let [groups (move-groups m)]
          (let [idx (:index kb)]
            {:groups    (mapv (fn [{:keys [gain readers seen]}]
                                (if (and (plain-gain? kb gain seen)
                                         (<= (stored-count-across kb gain) (reads/stored-mint-count-in idx readers)))
                                  {:gain gain :readers readers :seen seen}
                                  {:readers readers}))
                              groups)
             :displaced (displaceable-contexts kb m)}))))))

(defn- withdrawal-candidates
  "The minted records that `sx`, a sentex this settle moved, can have made redundant, as
  `[handle by]` pairs for `withdrawable-mint`, read off the mint family: a membership
  subsumes the mints about its term, a `genl` edge the edges minted out of `sub`, a
  `genlCx` edge the mints stated under `sub` (the side read is whichever of the mint
  contexts and `tax/context-down` is fewer).  Any other fact reads nothing.  With `plan`
  (`edge-mint-plan`) the mints are read per group.  See docs/argtypes.md."
  ([kb sx] (withdrawal-candidates kb sx nil))
  ([kb sx plan]
   (let [s   (:sentence sx)
         idx (:index kb)]
     (cond
       (and plan (context-edge-shaped? s))
       (for [{:keys [gain readers]} (:groups plan)
             h (if gain
                 (mapcat #(reads/as-stored-mints-about-global idx %) (gain-subjects kb gain))
                 (mapcat #(reads/as-stored-mints-in idx %) (nm/sort-by-content-key nm/name-key compare readers)))]
         [h nil])

       (membership-shaped? s)
       (for [h (reads/as-stored-mints-about-global idx (first (nm/args s)))] [h sx])

       (edge-shaped? s)
       (for [h (reads/as-stored-mints-about-global idx (nth s 1))] [h sx])

       (context-edge-shaped? s)
       (let [tax (reasoning/taxonomy kb)
             sub (nth s 1)]
         (for [c (if (< (reads/stored-mint-context-count idx)
                        (count (tax/context-down-global tax sub)))
                   (filter #(and (some? %) (tax/sees? tax % sub))
                           (reads/as-stored-mint-contexts-global idx))
                   (tax/context-down tax sub))
               h (reads/as-stored-mints-in idx c)]
           [h nil]))))))

(defn- edge-route-candidates
  "The mints the `genl` edges in `edges` (`tax/installed-edges`) gave a route they did
  not have, as `[handle nil]` pairs: the mints about every type strictly under an edge's
  `sub` and about every member of one.  One walk serves all the edges (`tax/specs-of-all`).
  Unscoped (E17): each candidate is asked in its own context.  A part of a declaration is
  asked about its own mints too.  See docs/argtypes.md."
  [kb edges]
  (let [idx  (:index kb)
        subs (into #{} (comp (mapcat #(tax/installed-edges (:sentence %))) (map first)) edges)
        parts (into #{} (comp (remove #(edge-shaped? (:sentence %)))
                              (mapcat #(tax/installed-edges (:sentence %))) (map first))
                    edges)]
    (when (and (seq subs) (pos? (reads/stored-mint-count-global idx)))
      (let [tax     (reasoning/taxonomy kb)
            below   (if (= 1 (count subs))
                      (tax/specs-global tax (first subs))
                      (tax/specs-of-all tax subs))
            strict? (fn [z]
                      (or (not (contains? subs z))
                          (contains? parts z)
                          (some #(and (not= z %) (contains? subs %)) (tax/genls-global tax z))))
            types   (if (< (reads/stored-mint-term-count idx) (count below))
                      (filter #(contains? below %) (reads/as-stored-mint-terms idx))
                      (filter #(reads/stored-mint-term? idx %) below))]
        (distinct
         (for [x (concat (filter strict? types) (mint-members-in kb below))
               h (reads/as-stored-mints-about-global idx x)]
           [h nil]))))))

(defn- declaring-predicates
  "The predicates an entailing argument declaration is written of, off the taxonomy's
  global `:props` sets (`tax/arg-declaration-props`) — no index read — of the declarations
  of the functors `kinds`.

  The `:props` sets are read unscoped, a superset: each declaration they name is read again
  from its placement."
  [kb kinds]
  (let [tax (reasoning/taxonomy kb)]
    (reduce (fn [acc k] (into acc (tax/props tax (tax/arg-declaration-props k))))
            #{}
            kinds)))

(defn- any-declaring?
  "Does any predicate carry an entailing argument declaration, of `kinds` when given?  Read
  off the taxonomy's global `:props` sets (`tax/arg-declaration-props`), so the check every
  settle runs reads no index and builds no set."
  ([kb] (any-declaring? kb (keys entailing-declarations)))
  ([kb kinds]
   (let [tax (reasoning/taxonomy kb)]
     (boolean (some #(seq (tax/props tax (tax/arg-declaration-props %))) kinds)))))

(defn- super-reaches-declaration?
  "Does `super`, or a genl-ancestor of it, carry an entailing argument declaration?
  `entail-under-edge` reads this before it walks a subtree: an edge draws a new type only
  through a declaration it supports (`checks/edge-support`).  Reads `tax/genls-global`
  and `tax/arg-declaration-props`, so the check over-approximates (E17)."
  [kb super]
  (and (symbol? super)
       (let [tax (reasoning/taxonomy kb)]
         ;; per kind's `:props` set, so the check builds no union of every declaring predicate
         (boolean (some #(tax/genls-global-meets? tax super (tax/props tax (tax/arg-declaration-props %)))
                        (keys entailing-declarations))))))

(defn- trigger-named-facts
  "The stored facts in a context of `seen`, kept by `before?`, naming a term a membership
  stated in `gain` types under a trigger type (`trigger-types`): the third ingredient of
  an `interArg` or homogeneity mint, beside the fact and the declaration, which the facts
  of `gain` do not reach.  Empty with no index read past one count when no trigger
  declaration is stored.  The trigger types are read over the unscoped `genl` closure
  (`tax/genls-global`): the memberships of the gain are read for every reader of a group
  at once, and a spare fact is drawn again where a missed one is a mint the gain side
  never draws."
  [kb gain seen before?]
  (let [idx (:index kb)]
    (if-not (some #(pos? (reads/stored-count-with-functor idx %)) trigger-declarations)
      []
      (let [tax  (reasoning/taxonomy kb)
            tts  (trigger-types kb)
            recs (:records kb)
            xs   (into (sorted-set-by #(compare (nm/name-key %1) (nm/name-key %2)))
                       (comp (mapcat #(reads/as-stored-in-context idx %))
                             (keep #(p/get-sentex recs %))
                             (map :sentence)
                             (filter #(and (membership-shaped? %)
                                           (let [t (nm/functor %)]
                                             (or (contains? tts t) (some tts (tax/genls-global tax t))))))
                             (map #(first (nm/args %))))
                       (nm/sort-by-content-key nm/name-key compare gain))]
        (into []
              (comp (mapcat #(facts-naming kb %))
                    (filter #(and (contains? seen (:context %)) (before? (:id %))))
                    (distinct))
              xs)))))

(defn surplus-placements
  "The mint justifications, in id order, that a `genlCx` edge among `edges` (sentexes)
  left at a context that is no longer a placement of their fact and declaration
  (`pair-placements`).  `plans` maps an edge record to its `edge-mint-plan`, whose
  `:displaced` contexts are the only ones read.  The caller checks that the entailment is
  on and the mint family holds a record."
  ([kb edges] (surplus-placements kb edges nil))
  ([kb edges plans]
   (when (seq edges)
     (let [tms  (reasoning/tms kb)
           idx  (:index kb)
           recs (:records kb)
           cx   (fn [h] (:context (p/get-sentex recs h)))
           jids (fn [e]
                  (let [plan (get plans e)]
                    (if-not plan
                      (for [[h _] (withdrawal-candidates kb e)
                            jid   (jtms/supports tms h)]
                        jid)
                      (for [c   (nm/sort-by-content-key nm/name-key compare (:displaced plan))
                            h   (reads/as-stored-mints-in idx c)
                            jid (jtms/supports tms h)]
                        jid))))]
       (into (sorted-set)
             (for [e     edges
                   jid   (jids e)
                   :let  [j (jtms/justification tms jid)]
                   :when (and j (kb/mint-informant? kb (:informant j)))
                   :let  [c     (cx (:consequence j))
                          [f d] (:antecedents j)
                          fc    (cx f)]
                   :when (and fc (not= c fc)
                              (not-any? #{c} (placements-of-pair kb f d)))]
               jid))))))

(defn descent-surplus-placements
  "The mint justifications, in id order, that a record among `moved` left at a context
  no longer a placement of their fact and declaration (`pair-placements`): a `genl` route
  or trigger membership stated in a more general context places the pair above, and the
  placement below goes.  A record installing `genl` edges whose `super` reaches a
  declaration (`super-reaches-declaration?`) reads its `sub`s' facts; a membership whose
  type reaches a trigger type (`trigger-types`, through `tax/genls-global`, E17) reads the
  facts naming its term."
  [kb moved]
  (let [tax   (reasoning/taxonomy kb)
        idx   (:index kb)
        subs  (into #{} (comp (mapcat #(tax/installed-edges (:sentence %)))
                              (filter (fn [[_ super]] (super-reaches-declaration? kb super)))
                              (map first)
                              (filter symbol?))
                    moved)
        mems  (filter #(membership-shaped? (:sentence %)) moved)
        tts   (delay (trigger-types kb))
        xs    (when (and (seq mems) (any-declaring? kb trigger-declarations)
                         (seq @tts))
                (into [] (comp (filter (fn [m] (let [t (nm/functor (:sentence m))]
                                                 (or (contains? @tts t)
                                                     (some @tts (tax/genls-global tax t))))))
                               (map #(first (nm/args (:sentence %))))
                               (distinct))
                      mems))
        facts (-> []
                  (into (comp (filter #(pos? (reads/stored-count-with-functor idx %)))
                              (mapcat #(reads/as-stored-with-functor idx %)))
                        (when (seq subs) (tax/specs-of-all tax subs)))
                  (into (comp (mapcat #(facts-naming kb %)) (map :id)) xs))]
    (when (seq facts)
      (let [tms (reasoning/tms kb)
            cx  (fn [h] (:context (p/get-sentex (:records kb) h)))]
        (into (sorted-set)
              (for [f     (distinct facts)
                    jid   (jtms/dependents tms f)
                    :let  [j (jtms/justification tms jid)]
                    :when (and j (kb/mint-informant? kb (:informant j))
                               (= f (first (:antecedents j))))
                    :let  [c  (cx (:consequence j))
                           fc (cx f)]
                    :when (and c fc (not= c fc)
                               (not-any? #{c} (placements-of-pair kb f (second (:antecedents j)))))]
                jid))))))

(defn note-unpremised!
  "Queue the record at `h`, whose premise mark a retraction removed while a derivation
  still holds it up, for the settle's withdrawal question: a record an author stated
  beside a mint of the same sentence is not the entailment's to withdraw, and once the
  statement goes it is (`mint-only?`), so a believed record that says it more
  specifically withdraws it as it withdraws a mint it meets on arrival."
  [kb h]
  (when (and argument/*assertive-arg-types?* checks/*prune-subsumed-mints?*)
    (swap! (reasoning/mint-queues kb) update :unpremised (fnil conj []) h)))

(defn- drain-unpremised!
  "The handles `note-unpremised!` queued since the last drain, and the queue emptied."
  [kb]
  (let [[old] (swap-vals! (reasoning/mint-queues kb) dissoc :unpremised)]
    (:unpremised old)))

(defn subsumed-mint-blocks
  "The justifications to block because the records they hold up are redundant:
  `{:blocked #{jid} :withdrawn #{handle}}`, plus `:surplus` (`surplus-placements`) for the
  settle to drop, over the records the sentexes in `moved` can have displaced.  Blocks
  every justification of a withdrawn record.  `moved` is a delay, forced only when the
  entailment is on, the mint is prunable and the mint family is non-empty; forced, it is
  filtered by `subsumer-shaped?` and read through `withdrawal-candidates` and
  `edge-route-candidates`.  Only a record that became believed is asked, and also each
  record a retraction left standing on a derivation alone (`note-unpremised!`).  `asked`
  is the settle's record of the records already asked, so each is asked once per settle.
  `believed?` is belief now.  With `routes?`, `descent-surplus-placements` is asked too.
  `whole` is the region's size for a `recover`, else nil; with fewer mints stored than
  that, `moved` is never forced.  See docs/argtypes.md."
  [kb moved was-in asked believed? routes? whole]
  (let [tms    (reasoning/tms kb)
        idx    (:index kb)
        lost   (drain-unpremised! kb)
        prune? (and argument/*assertive-arg-types?* checks/*prune-subsumed-mints?*)
        mints  (when argument/*assertive-arg-types?* (reads/stored-mint-count-global idx))
        each?  (and whole mints (< mints whole))
        ask?   #(let [h (:id %)]
                  (and (nil? (:antecedent %))
                       (not (contains? @asked h))
                       ;; the transition, not the region: a record the settle relabelled
                       ;; without moving subsumes exactly what it subsumed before, and most
                       ;; of a relabelled region does not move (`jtms/touched-in`)
                       (believed? h)
                       (not (contains? was-in h))))
        moved  (when (and mints (pos? mints))
                 (seq (if each?
                        (filter #(and (context-edge-shaped? (:sentence %)) (ask? %))
                                (keep #(p/get-sentex (:records kb) %)
                                      (cap/hinting (cap/prefetcher (:records kb))
                                                   cap/recovery-hint-chunk
                                                   (reads/as-stored-with-functor idx 'genlCx))))
                        (filter #(and (ask? %) (subsumer-shaped? (:sentence %))) @moved))))
        ;; the `genlCx` edges among the moved records, each read per group of the readers
        ;; it gives a context, without the others (`edge-mint-plan`)
        edges   (filter #(context-edge-shaped? (:sentence %)) moved)
        plans   (when (seq edges)
                  (let [ctxs (move-except-contexts kb)
                        off  (into #{} (map #(let [s (:sentence %)] [(nth s 1) (nth s 2)])) edges)]
                    (into {} (keep #(some->> (edge-mint-plan kb ctxs % off) (vector %))) edges)))
        surplus (into (or (surplus-placements kb edges plans)
                          (sorted-set))
                      (when routes? (descent-surplus-placements kb moved)))]
    (vswap! asked into (map :id) moved)
    (cond->
     (when (and prune? (or each? moved (seq lost)))
       (reduce
        ;; `:withdrawn` keeps a mint two moved records displace from being withdrawn twice;
        ;; a mint one of them does not displace is still asked of the next
        (fn [acc [h by]]
          (if (or (contains? (:withdrawn acc) h) (not (withdrawable-mint kb h by)))
            acc
            (-> acc
                (update :withdrawn conj h)
                (update :blocked into
                        (comp (keep #(jtms/justification tms %)) (map :id))
                        (jtms/supports tms h)))))
        {:blocked #{} :withdrawn #{}}
        (cap/hinting
         (withdrawal-hinter kb) withdrawal-hint-chunk
         (concat (if each?
                   (map (fn [h] [h nil])
                        (mapcat #(reads/as-stored-mints-in idx %)
                                (reads/as-stored-mint-contexts-global idx)))
                   (concat (mapcat #(distinct (withdrawal-candidates kb % (get plans %))) moved)
                           (edge-route-candidates
                            kb (filter #(seq (tax/installed-edges (:sentence %))) moved))))
                 (map (fn [h] [h nil]) lost)))))
      ;; a placement an edge displaced leaves by a drop of its own justification, so
      ;; another support of the record keeps it; a dropped one is not also blocked
      (seq surplus) (-> (or {:blocked #{} :withdrawn #{}})
                        (update :blocked #(reduce disj % surplus))
                        (assoc :surplus surplus)))))

(defn note-departure!
  "Queue `sentex`, leaving the store, when it is a `genlCx` edge, whose `[sub super]` the
  context-move drain reads (`drain-context-moves!`), or a record that can have subsumed a
  mint (`subsumer-shaped?`) with pruning on, for `withheld-releases`.  Called from
  `integrate/sentex-removed!`, the one place a record leaves."
  [kb sentex]
  (let [s (sx/sentence-of sentex)]
    (when (or (context-edge-shaped? s)
              (and argument/*assertive-arg-types?* checks/*prune-subsumed-mints?*
                   (subsumer-shaped? s)))
      (swap! (reasoning/mint-queues kb) update :departed (fnil conj [])
             (assoc (select-keys sentex [:id :context]) :sentence s)))))

(defn drain-departures!
  "The records `note-departure!` queued since the last drain, and the queue emptied."
  [kb]
  (let [[old] (swap-vals! (reasoning/mint-queues kb) dissoc :departed)]
    (:departed old)))

(def ^:dynamic *release-withheld?*
  "False under `*bulk-load?*` and in the settles an open, a recover or an upgrade runs,
  the first settle after a trusted image install among them (`defer-first-release!`):
  `withheld-releases` then draws nothing and keeps the departures and arrivals it would
  have read owed (`:owed` in `mint-queues`, which the image carries), and
  `release-withheld!` draws them."
  true)

(defn defer-first-release!
  "Make `kb`'s next settle run with `*release-withheld?*` false (`take-first-deferral!`)."
  [kb]
  (swap! (reasoning/mint-queues kb) assoc :defer-next true))

(defn take-first-deferral!
  "Whether `defer-first-release!` marked this settle, with the mark cleared."
  [kb]
  (let [[old] (swap-vals! (reasoning/mint-queues kb) dissoc :defer-next)]
    (boolean (:defer-next old))))

(defn owed-releases
  "How many departures and arrivals `withheld-releases` left owed (`*release-withheld?*`)."
  [kb]
  (count (:owed @(reasoning/mint-queues kb))))

(defn- owe-releases!
  "Keep the departures `out` and the arrivals `twins` owed, each once by handle, as
  `{:id :context :sentence}` with `:twin?` on an arrival."
  [kb out twins]
  (let [row #(assoc (select-keys % [:id :context]) :sentence (:sentence %))]
    (swap! (reasoning/mint-queues kb) update :owed
           (fn [o] (let [o (or o [])
                         have (into #{} (map (juxt :id :twin?)) o)]
                     (into o (comp (remove #(have [(:id %) (:twin? %)])) (distinct))
                           (concat (map row out) (map #(assoc (row %) :twin? true) twins))))))))

(defn- unchanged-mint?
  "Would `entail-arg-type` write nothing for the entailment `ent` over the fact at `src`
  in `context`, whatever its checks found?  So when the mint is stored there with a
  support under the same kind's rule (`kv/mint-rules`) over the same antecedents, and when it
  is not stored and a believed record still subsumes it (`checks/subsumed-mint`), withheld
  again — an arity-class membership (`:class`) excepted, which nothing withholds.  The
  two questions `entail-arg-type` asks after its checks, asked first."
  [kb ent src context]
  (boolean
   (if-let [h (kb/find-sentex-handle kb (:assert ent) context)]
     (let [tms   (reasoning/tms kb)
           antes (into [src] (:because ent))
           rh    (when-not (:class ent) (get (kb/mint-rule-table kb) (:kind ent)))]
       (or (jtms/has-justification? tms (:kind ent) antes h)
           (boolean (and rh (jtms/has-justification? tms rh antes h)))))
     (and (not (:class ent))
          (checks/subsumed-mint kb (:assert ent) context)))))

(defn- rederive-mints
  "Draw again the mints of each stored fact in `facts` that `keep?` accepts (a fn of the
  minted sentence and its placement), as `deduce-placed` draws them: `{:new [handle …]}`.
  An inert fact (`assert-inert`) draws no mint.  Idempotent, deciding on current belief:
  a mint already holding this justification or still withheld is skipped before
  `entail-arg-type` (`unchanged-mint?`).  Violations are dropped.  `*admission-memo*`
  holds the checks' answers for the call."
  [kb facts keep?]
  (with-recheck-reads
    (binding [*admission-memo* (volatile! {})]
      ;; each fact naming the term adds one support to the same mints, which a dedup
      ;; question without the cache answers by scanning every support already added
      (jtms/with-dedup-cache (reasoning/tms kb)
        (reduce (fn [acc sx]
                  (if-not (and (sx/positive-fact? sx)
                               (jtms/known-datum? (reasoning/tms kb) (:id sx)))
                    acc
                    (let [h (:id sx)]
                      (update acc :new into
                              (:new (deduce-placed kb (:sentence sx) h (:context sx)
                                                   (fn [e c] (and (keep? (:assert e) c)
                                                                  (not (unchanged-mint? kb e h c))))))))))
                {:new []}
                facts)))))

(defn- released-terms
  "The terms whose withheld mints the departure of `sx` can release, for `mints-about`:
  a membership `(T x)` or an edge `(genl x S)` subsumed the mints about `x`, and each
  edge `(genl sub super)` a record installs (`tax/installed-edges`, so a cover's per part) was
  also a route from every type under `sub` and every member of one — the terms
  `edge-route-candidates` asks about when the same record arrives.

  The closures are unscoped: the terms are a superset over every reader, and each
  withheld mint is asked again from its own placement."
  [kb sx]
  (let [s (:sentence sx)]
    (cond
      (membership-shaped? s) [(first (nm/args s))]

      (seq (tax/installed-edges s))
      (into []
            (comp (map first)
                  (mapcat (fn [sub]
                            (into (vec (tax/specs-global (reasoning/taxonomy kb) sub))
                                  (comp (map :sentence) (filter membership-shaped?)
                                        (map #(first (nm/args %))))
                                  (subtree-sentexes kb sub))))
                  (distinct))
            (tax/installed-edges s)))))

(defn- may-release
  "The mints about a term that the departures `g` releasing it (`released-terms`) can
  have withheld, as a predicate on the mint's sentence.  A membership `(T x)` withholds
  only a membership `(t x)` of `T` itself, at a placement its own made surplus, or of a
  type above `T` (`checks/subsumed-mint`), read over the unscoped closure as a superset
  of every placement's; an edge or a cover, any mint about the terms it releases.  Each
  departure's closure is read once, before the predicate is asked of any mint."
  [tax g]
  (if (some #(not (membership-shaped? (:sentence %))) g)
    (constantly true)
    (let [ups (mapv #(tax/genls-global tax (nm/functor (:sentence %))) g)]
      (fn [sentence]
        (and (membership-shaped? sentence)
             (let [t (nm/functor sentence)]
               (boolean (some #(contains? % t) ups))))))))

(defn- departed-context-edge-mints
  "Draw again, at the placements the taxonomy now gives (`pair-placements`), every mint
  pair the `genlCx` move `m` (`context-move`, an edge removed or out) can have kept from a
  placement under its `sub`: `{:new [handle …] :violations [v …]}`.  The pairs are read off
  the mint family in the contexts of `:moved`, and only when `:seen` meets `:up`.  With
  subsumed mints pruned, a placement can be withheld instead: the records stored there
  release the terms they name (`released-terms`) and the facts under `sub` draw again,
  read from the smaller side by index counts.  Off unless `*assertive-arg-types?*`, some
  predicate declares, and pruning is on or a mint is stored in any context."
  [kb m]
  (when (and argument/*assertive-arg-types?* (any-declaring? kb)
             (or checks/*prune-subsumed-mints?*
                 (pos? (reads/stored-mint-count-global (:index kb)))))
    (let [tms  (reasoning/tms kb)
          idx  (:index kb)
          recs (:records kb)
          cx   #(:context (p/get-sentex recs %))
          ;; the contexts the edge took from a reader under its `sub`
          lost (sort-by nm/name-key (:moved m))
          seen @(:seen m)
          ;; a fact stated in a lost context's ancestor is in `:up`
          pairs (into (sorted-set)
                      (for [c     (if (some (:up m) seen) lost [])
                            h     (reads/as-stored-mints-in idx c)
                            jid   (jtms/supports tms h)
                            :let  [j (jtms/justification tms jid)]
                            :when (and j (kb/mint-informant? kb (:informant j)))
                            :let  [[f d] (:antecedents j)
                                   fc    (cx f)]
                            :when (and (not= c fc) (contains? seen fc))]
                        [f d]))
          mints (reduce (fn [acc [d fs]]
                          (let [pl (placements-of kb d)]
                            (reduce (fn [acc f]
                                      (if-let [sx (p/get-sentex recs f)]
                                        (merge-with into acc (retroactive-mints kb sx d pl))
                                        acc))
                                    acc (map second fs))))
                        empty-entailment-result
                        (group-by first (map (fn [[f d]] [d f]) pairs)))]
      (if-not checks/*prune-subsumed-mints?*
        (select-keys mints [:new])
        (let [under @(:under m)
              ;; the facts stored under `sub` draw below, over every placement
              above (into (sorted-set-by #(compare (nm/name-key %1) (nm/name-key %2)))
                          (remove under) seen)
              count-in #(reduce + 0 (map (fn [c] (reads/stored-count-in-context idx c)) %))
              stored-in #(into [] (comp (mapcat (fn [c] (reads/as-stored-in-context idx c)))
                                        (keep (fn [h] (p/get-sentex recs h))))
                               %)
              released
              (if (<= (count-in lost) (count-in above))
                (reduce (fn [acc x]
                          (merge-with into acc
                                      (rederive-mints kb (filterv #(above (:context %)) (facts-naming kb x))
                                                      (fn [s c] (and (= x (mint-term s))
                                                                     (contains? under c))))))
                        {:new []}
                        (->> (stored-in lost)
                             (into [] (comp (filter #(and (subsumer-shaped? (:sentence %))
                                                          (not (context-edge-shaped? (:sentence %)))
                                                          (jtms/in? tms (:id %))))
                                            (mapcat #(released-terms kb %))
                                            (filter symbol?)
                                            (distinct)))
                             (sort-by nm/name-key)))
                (rederive-mints kb (stored-in above)
                                (fn [s c] (and (some? (mint-term s)) (contains? under c)))))]
          (merge-with into
                      (select-keys mints [:new])
                      released
                      (rederive-mints kb
                                      (into []
                                            (comp (mapcat #(reads/as-stored-in-context idx %))
                                                  (keep #(p/get-sentex recs %)))
                                            (sort-by nm/name-key under))
                                      (fn [s _] (some? (mint-term s))))))))))

(defn- release-departures
  "Re-draw the mints the departures `out` can have withheld and the justifications the
  arrivals `twins` owe (`withheld-releases`'s sweep): `{:new [handle …]}`.  `asked` holds
  what the caller's settle has asked, and a departure believed again leaves it."
  [kb out twins asked believed?]
  (with-recheck-reads
    (let [tax     (reasoning/taxonomy kb)
          ;; term -> the departures releasing it, in `out`'s order
          by-term (reduce (fn [m sx]
                            (reduce #(update %1 %2 (fnil conj []) sx) m
                                    (distinct (filter symbol? (released-terms kb sx)))))
                          {} out)
          terms (sort-by nm/name-key (keys by-term))
          recs  (:records kb)
          ;; read again as each term's turn comes: re-drawing an earlier term can
          ;; relabel a departure IN, and one stored as it was and believed again
          ;; subsumes what it did before, so its term owes no re-draw
          gone? (fn [sx]
                  (let [now (p/get-sentex recs (:id sx))]
                    (or (not= (:sentence now) (:sentence sx)) (not= (:context now) (:context sx))
                        (not (believed? (:id sx)))
                        (closes-genl-cycle? tax (:sentence sx)))))
          back  (volatile! #{})]
      (merge-with
       into
       (let [r (reduce (fn [acc x]
                         (let [[g b] ((juxt filter remove) gone? (by-term x))]
                           (vswap! back into (map :id) b)
                           (if (seq g)
                             (let [released? (may-release tax g)]
                               (merge-with into acc (rederive-mints kb (facts-naming kb x)
                                                                    (fn [s _] (and (= x (mint-term s))
                                                                                   (released? s))))))
                             acc)))
                       {:new []}
                       terms)]
         ;; a departure believed again released nothing, and is asked again should a
         ;; later pass take it out
         (vswap! asked #(reduce disj % @back))
         r)
       (reduce (fn [acc sx]
                 (let [s (:sentence sx) c (:context sx)]
                   (merge-with into acc (rederive-mints kb (facts-naming kb (mint-term s))
                                                        (fn [s' c'] (and (= s s') (= c c')))))))
               {:new []}
               twins)))))

(defn withheld-releases
  "The mints no longer withheld because a record that subsumed them left, and the
  justifications a withheld mint owes a record of its sentence that arrived:
  `{:new [handle …]}`, drawn by `rederive-mints` (docs/argtypes.md, \"Nothing records a
  withheld mint\").  Pruning only; a `genlCx` edge's departure is the drain's
  (`departed-context-edge-mints`).  Under `*release-withheld?*` false the departures and
  arrivals stay owed (`owe-releases!`) and nothing is drawn.  Departures are the records
  `note-departure!` queued and the records in `moved` (a delay) that went IN to OUT against
  `was-in`; arrivals came IN.  `withdrawn` holds the mints this settle withdrew, which
  release nothing; `asked` holds the records already asked, so each is asked once per
  settle.  A term is re-drawn only for the mints one of its departures could have
  withheld (`may-release`)."
  [kb moved was-in asked withdrawn believed?]
  (let [queued (drain-departures! kb)
        mover? (fn [s] (and (subsumer-shaped? s) (not (context-edge-shaped? s))))]
    (when (and argument/*assertive-arg-types?* checks/*prune-subsumed-mints?* (any-declaring? kb))
      (let [;; the transition, not the region, as `subsumed-mint-blocks` reads it
            moves (into []
                        (filter #(let [h (:id %)]
                                   (and (nil? (:antecedent %))
                                        (not (contains? @asked h))
                                        (not (contains? withdrawn h))
                                        (not= (contains? was-in h) (believed? h))
                                        (mover? (:sentence %)))))
                        @moved)
            tax   (reasoning/taxonomy kb)
            out   (-> []
                      (into (remove #(or (contains? withdrawn (:id %)) (not (mover? (:sentence %))))) queued)
                      (into (remove #(and (believed? (:id %))
                                          (not (closes-genl-cycle? tax (:sentence %)))))
                            moves))
            ;; a record a mint justification already concludes still owes the withheld
            ;; ones while a premise or a firing holds it up: in the order where the
            ;; record arrives first, each of them is drawn onto it
            twins (filterv #(let [s (:sentence %)]
                              (and (believed? (:id %))
                                   (not (mint-only? kb (:id %)))
                                   (checks/subsumed-mint kb s (:context %))))
                           moves)]
        (vswap! asked into (map :id) moves)
        (if *release-withheld?*
          (release-departures kb out twins asked believed?)
          (do (owe-releases! kb out twins) {:new []}))))))

(defn release-withheld!
  "Draw what the departures and arrivals `withheld-releases` left owed can have withheld
  (`owed-releases`), and empty the debt: `{:terms n :released n :new [handle …]}`, the
  terms the owed rows release and the records drawn.  The caller settles."
  [kb]
  (let [[old] (swap-vals! (reasoning/mint-queues kb) dissoc :owed)
        owed  (:owed old)
        tms   (reasoning/tms kb)
        in?   #(jtms/in? tms %)
        recs  (:records kb)
        [twins out] ((juxt filter remove) :twin? owed)
        twins (filterv #(and (in? (:id %)) (p/get-sentex recs (:id %))) twins)
        r     (if (and (seq owed) argument/*assertive-arg-types?* checks/*prune-subsumed-mints?*
                       (any-declaring? kb))
                (exc/with-reader-states (release-departures kb (vec out) twins (volatile! #{}) in?))
                {:new []})]
    {:terms    (count (into #{} (filter symbol?)
                            (concat (mapcat #(released-terms kb %) out) (map (comp mint-term :sentence) twins))))
     :released (count (:new r)) :new (:new r)}))

(defn call-with-pass-caches
  "`(f)` holding, across the facts a pass over `kb` draws, the admission checks' answers
  (`*admission-memo*`), each context's reader state (`exc/with-reader-states`) and the
  justification dedup index (`jtms/with-dedup-cache`); the ones already bound are kept."
  [kb f]
  (exc/with-reader-states
    (binding [*admission-memo* (or *admission-memo* (volatile! {}))]
      (jtms/with-dedup-cache (reasoning/tms kb) (f)))))

(defn- entail-over
  "Draw the entailments of each stored literal fact in `facts` at their placements, as
  `deduce-placed` draws them for a fact arriving now: `{:new :violations}`.  With
  `kinds`, only the entailments of those declaring functors.

  The facts naming one term draw the same mints, so the pass holds the admission checks'
  answers (`*admission-memo*`), each context's reader state (`exc/with-reader-states`)
  and the justification dedup index (`jtms/with-dedup-cache`) across them."
  ([kb facts] (entail-over kb facts nil))
  ([kb facts kinds]
   (call-with-pass-caches
    kb
    #(reduce (fn [acc sx]
               (if-not (sx/positive-fact? sx)
                 acc
                 (merge-with into acc
                             (deduce-placed kb (:sentence sx) (:id sx) (:context sx)
                                            (when kinds (fn [e _] (contains? kinds (:kind e))))))))
             empty-entailment-result
             facts))))

(defn entail-under-edge
  "When a `(genl sub super)` edge arrives, draw what the declarations on `super` now say
  about the `(sub …)` sentexes already stored, the third arrival order beside
  `deduce-arg-types` and `entail-existing`.  A `covering`, `separating` or `partition`
  installs an edge per part (`tax/installed-edges`), each read as an arriving edge.  nil
  when `sentence` installs no edge.  Covers the whole spec subtree of `sub`
  (`subtree-sentexes`), each sentex put back through `checks/constraint-entailments` in
  its own context.  Off unless `*assertive-arg-types?*`, some predicate carries an
  entailing declaration (`any-declaring?`) and a genl-ancestor of `super` does
  (`super-reaches-declaration?`)."
  [kb sentence]
  (when-let [edges (when-let [es (and argument/*assertive-arg-types?* (seq (tax/installed-edges sentence)))]
                     (when (any-declaring? kb)
                       (seq (filter (fn [[sub super]]
                                      (and (symbol? sub) (super-reaches-declaration? kb super)))
                                    es))))]
    (reduce (fn [acc sx]
              (if-not (sx/positive-fact? sx)
                acc
                (merge-with into acc
                            (deduce-placed kb (:sentence sx) (:id sx) (:context sx)))))
            empty-entailment-result
            ;; a cover's parts can share specs, and a fact under two of them draws once
            (into [] (comp (mapcat (fn [[sub]] (subtree-sentexes kb sub))) (distinct)) edges))))

(defn- declared-functors
  "Every functor holding a stored sentex that an entailing declaration reaches — the specs
  of each declaring predicate (`declaring-predicates`, of `kinds` when given), in content
  order.  Unscoped (`tax/specs-global`, E17): the callers read facts across every context
  they are stored in, and each fact is put back through `checks/constraint-entailments`
  in its own context, so the unscoped walk only reads more facts than a scoped one."
  ([kb] (declared-functors kb (keys entailing-declarations)))
  ([kb kinds]
   (let [tax (reasoning/taxonomy kb)
         idx (:index kb)]
     (into []
           (comp (mapcat #(tax/specs-global tax %))
                 (distinct)
                 (filter #(pos? (reads/stored-count-with-functor idx %))))
           (nm/sort-by-content-key nm/name-key compare (declaring-predicates kb kinds))))))

(defn- declarations-meeting
  "Draw what each entailing declaration stated in a context of `below` says about the
  facts of its extent stated in a context of `seen` (`subtree-sentexes`), at the
  placements of each pair (`retroactive-mints`): `{:new :violations}`.  The declarations
  are read per kind off the predicate extent ending in `below`'s contexts
  (`reads/as-stored-with-functor-in`).  Only the declarations and facts whose handles
  `before?` keeps are read."
  [kb below seen before?]
  (let [idx  (:index kb)
        recs (:records kb)]
    (reduce (fn [acc dsx]
              (let [dh (:id dsx)
                    pl (placements-of kb dh)]
                (reduce (fn [acc sx] (merge-with into acc (retroactive-mints kb sx dh pl)))
                        acc
                        (filter #(before? (:id %)) (subtree-sentexes kb (second (:sentence dsx)) nil seen)))))
            empty-entailment-result
            (for [k     (nm/sort-by-content-key nm/name-key compare (keys entailing-declarations))
                  h     (sort (reads/as-stored-with-functor-in idx k below))
                  :when (before? h)
                  :let  [dsx (p/get-sentex recs h)]
                  :when (and (sx/positive-fact? dsx)
                             (= (entailing-declarations k) (nm/arity (:sentence dsx)))
                             (symbol? (second (:sentence dsx))))]
              dsx))))

(defn- declared-facts-in
  "The stored literal facts in the contexts `cs` whose handles `before?` keeps and whose
  functor an entailing declaration reaches (`declared-functors`), in content order of the
  contexts, read from the smaller of two sides, compared by index counts: the facts
  stored in `cs`, kept when a declaration reaches their functor, or the extent in `cs` of
  each functor a declaration reaches (`reads/as-stored-with-functor-in`), priced at the
  lesser of the declared extent and one probe per functor and context."
  [kb cs before?]
  (let [recs  (:records kb)
        idx   (:index kb)
        ctxs  (nm/sort-by-content-key nm/name-key compare cs)
        by-cx (reduce + 0 (map #(reads/stored-count-in-context idx %) ctxs))
        ;; contexts storing nothing read no declared functor
        fs    (if (zero? by-cx) [] (declared-functors kb))
        ;; the functor side reads each functor's extent in `cs` alone, so it costs at
        ;; most its extent and at most one probe per functor and context
        by-fn (min (reduce + 0 (map #(reads/stored-count-with-functor idx %) fs))
                   (* (count fs) (count ctxs)))]
    (if (<= by-cx by-fn)
      (let [fset (set fs)]
        (into []
              (comp (mapcat #(reads/as-stored-in-context idx %))
                    (filter before?)
                    (keep #(p/get-sentex recs %))
                    (filter #(contains? fset (nm/functor (:sentence %)))))
              ctxs))
      (let [cset (set ctxs)]
        (into []
              (comp (mapcat #(reads/as-stored-with-functor-in idx % cset))
                    (distinct)
                    (filter before?)
                    (keep #(p/get-sentex recs %)))
              fs)))))

(defn- move-entail-side
  "`:gain` when the argument-type sweep of a group of readers (`move-groups`) may read the
  facts of what the readers gain, `gain`, in place of the facts and declarations of what
  they saw beside, `below`: `gain` states facts alone and the readers, seeing `seen`, see
  no `except` (`plain-gain?`, so no declaration and no `genl` edge there meets a fact the
  readers saw) and `gain` stores no more than `below`.
  Else `:below`."
  [kb gain seen below]
  (if (and (plain-gain? kb gain seen)
           (<= (stored-count-across kb gain) (stored-count-across kb below)))
    :gain
    :below))

(def ^:dynamic *entail-moves?*
  "False while a `*bulk-load?*` write settles: the drain draws no argument types over the
  facts a `genlCx` move shows (`entail-under-context-edge`).  `record-arg-types` draws them
  after the load."
  true)

(defn entail-under-context-edge
  "When the `genlCx` move `m` (`context-move`) shows contexts, draw what the declarations
  it makes visible say about the facts already stored in `sub` and every context under
  it, the fourth arrival order beside the fact, the declaration and the `genl` edge.  Each
  derivation names the `genlCx` edges it sees its declaration through
  (`checks/entailment-support`).  Facts and declarations stated in `below` draw at their
  new common placements (`deduce-placed`, `declarations-meeting`); the settle drops a
  placement left below a more general one (`surplus-placements`).  Off unless
  `*assertive-arg-types?*` and `*entail-moves?*` hold, some predicate declares, and a
  context of `:moved` stores a sentex older than `:floor`.  Per group of readers
  (`move-groups`) one side is read (`move-entail-side`, `trigger-named-facts`,
  `declared-facts-in`).  `:floor` (`seed-floor`) excludes content that arrived with the
  edge; `:entailed` (a volatile set, one per drain) excludes facts an earlier move drew."
  [kb m]
  (when (and argument/*assertive-arg-types?*
             *entail-moves?*
             (symbol? (first (:edge m)))
             (any-declaring? kb))
    (let [idx     (:index kb)
          before? (if-let [f (:floor m)] #(< (long %) (long f)) (constantly true))
          shows?  (fn [cs] (some #(and (pos? (reads/stored-count-in-context idx %))
                                       (some before? (reads/as-stored-in-context idx %)))
                                 cs))
          draw    (fn [facts meeting]
                    (let [done  (:entailed m)
                          facts (if done (into [] (remove #(contains? @done (:id %))) facts) facts)]
                      (some-> done (vswap! into (map :id) facts))
                      (merge-with into (entail-over kb facts) meeting)))]
      (when (shows? (:moved m))
        (if-let [groups (move-groups m)]
          ;; per group of readers, the facts of the side `move-entail-side` picks
          (reduce (fn [acc {:keys [gain seen below]}]
                    (if-not (shows? gain)
                      acc
                      (merge-with into acc
                                  (if (= :gain (move-entail-side kb gain seen below))
                                    (draw (into (declared-facts-in kb gain before?)
                                                (trigger-named-facts kb gain seen before?))
                                          empty-entailment-result)
                                    (draw (declared-facts-in kb below before?)
                                          (declarations-meeting kb below gain before?))))))
                  empty-entailment-result
                  groups)
          (let [below (into @(:under m) @(:below m))]
            (draw (declared-facts-in kb below before?)
                  (declarations-meeting kb below (:moved m) before?))))))))

(defn- trigger-shaped?
  "Is `sx` a stored literal that can be a trigger: a membership, or a record that
  installs `genl` edges?"
  [sx]
  (let [s (:sentence sx)]
    (and (nil? (:antecedent sx))
         (or (membership-shaped? s) (seq (tax/installed-edges s))))))

(defn- trigger-entailments
  "Draw what the trigger records `ins` (`trigger-shaped?`, believed) trigger over the
  stored facts naming the terms they type: `{:new [handle …] :violations [v …]}`, or nil
  when none reaches a trigger type.  A membership `(T x)` reaches the facts naming `x`; an
  edge `(genl sub super)` whose `super` reaches a trigger type reaches every member of a
  type under `sub` (`released-terms`).  Each fact goes back through
  `checks/constraint-entailments` in its own context, narrowed to the trigger kinds.  Reads
  from the smaller of two sides by index counts; the trigger types come from
  `tax/genls-global` (E17)."
  [kb ins]
  (when (seq ins)
    (let [tax    (reasoning/taxonomy kb)
          tts    (delay (trigger-types kb))
          ;; a membership or an edge triggers only through a trigger type it reaches
          reach? (fn [t] (or (contains? @tts t) (some @tts (tax/genls-global tax t))))
          terms  (->> ins
                      (mapcat (fn [sx]
                                (let [s (:sentence sx)]
                                  (if (membership-shaped? s)
                                    (when (reach? (nm/functor s)) [(first (nm/args s))])
                                    (when (some (fn [[_ super]] (reach? super))
                                                (tax/installed-edges s))
                                      (released-terms kb sx))))))
                      (filter symbol?)
                      distinct
                      (sort-by nm/name-key))]
      (when (seq terms)
        (let [idx    (:index kb)
              recs   (:records kb)
              fs     (declared-functors kb trigger-declarations)
              fset   (set fs)
              by-fn  (reduce + 0 (map #(reads/stored-count-with-functor idx %) fs))
              names  (fn [xs sx] (some xs (rest (:sentence sx))))
              ;; the declared extent, read once for every term whose postings outnumber it
              extent (fn [xs]
                       (into []
                             (comp (mapcat #(reads/as-stored-with-functor idx %))
                                   (distinct)
                                   (keep #(p/get-sentex recs %))
                                   (filter #(names xs %)))
                             fs))
              posted (fn [[x posting]]
                       (into []
                             (comp (keep #(p/get-sentex recs %))
                                   (filter #(and (contains? fset (nm/functor (:sentence %)))
                                                 (names #{x} %))))
                             posting))
              facts  (if (< by-fn (count terms))
                       (extent (set terms))
                       (let [{small true large false}
                             (group-by (fn [[_ posting]]
                                         (<= (bounded-count (inc by-fn) posting) by-fn))
                                       (map (fn [x] [x (reads/as-stored-with-term idx x)]) terms))]
                         (cond-> (into [] (mapcat posted) small)
                           (seq large) (into (extent (into #{} (map first) large))))))]
          (entail-over kb (into [] (distinct) facts)
                       trigger-declarations))))))

(defn triggered-mints
  "Draw what the memberships and `genl` edges among `moved` that came IN this settle
  trigger (`trigger-entailments`): `{:new [handle …] :violations [v …]}`.  A membership
  `(T x)` arriving after a fact and an `interArg` or homogeneity declaration over it is
  the trigger's arrival order, which the fact and the declaration cannot reach because
  the trigger did not hold when each arrived.  `was-in` and `believed?` are belief before
  the settle and now; `asked` holds the records this settle has asked."
  [kb moved was-in asked believed?]
  (when (and argument/*assertive-arg-types?*
             (any-declaring? kb trigger-declarations))
    (let [ins (into []
                    (filter #(let [h (:id %)]
                               (and (not (contains? @asked h))
                                    (not (contains? was-in h))
                                    (believed? h)
                                    (trigger-shaped? %))))
                    @moved)]
      (vswap! asked into (map :id) ins)
      (trigger-entailments kb ins))))

(defn arg-type-extents
  "The facts the argument-type pass draws, as `[[functor handles] …]`: every functor an
  entailing declaration reaches, in content order (`declared-functors`), with the handles
  stored now.  Empty under `VAELII_ASSERTIVE_ARG_TYPES=0`.  A store loaded around `assert`
  (a dump import, `*bulk-load?*`, `bulk-assert-facts!`) holds no derived memberships; the
  pass draws them per fact (`draw-fact`)."
  [kb]
  (if-not argument/*assertive-arg-types?*
    []
    (let [idx (:index kb)]
      (mapv (fn [f] [f (reads/as-stored-with-functor idx f)]) (declared-functors kb)))))

(defn- drawn-within
  "`(f)` under the fact deadline `deadline` (nil: none): `{:new [h …] :violations [v …]}`,
  with `:deferred {:phase :transitions}` added when the deadline passed inside the
  checks.  A deferred draw answers the mints it created before the deadline under
  `:new`, and its violations are asked again by the re-run."
  [deadline f]
  (if-not deadline
    (f)
    (let [t     (volatile! [])
          phase (volatile! nil)]
      (try
        (binding [*fact-deadline*      deadline
                  *transitions*        t
                  budget/*unit-phase*  phase]
          (f))
        (catch clojure.lang.ExceptionInfo e
          (if (budget/unit-over? e)
            {:new        (into [] (keep (fn [[h new?]] (when new? h))) @t)
             :violations []
             :deferred   {:phase (:phase (ex-data e)) :transitions @t}}
            (throw e)))))))

(defn- changed-only
  "The `keep?` of a pass drawing the stored fact at `h`: an entailment whose mint the
  draw would change (`unchanged-mint?`).  A mint stored with this support, or one still
  withheld, is passed over before its admission checks run, as `rederive-mints` passes
  it over: `entail-arg-type` would write nothing for it and cascade nothing, and the
  checks are a mint's cost."
  [kb h]
  (fn [e c] (within-fact :unchanged #(not (unchanged-mint? kb e h c)))))

(defn draw-fact
  "Draw the argument-type entailments of the stored fact at `h`, at its placements
  (`deduce-placed`): `{:new [h …] :violations [v …]}`, nothing for a rule, a negation or a
  handle the store no longer holds.  A mint the draw would leave as it is
  (`changed-only`) is not asked about, so a violation of one already stored is not
  reported again.  With `deadline`, a `budget/now` instant, a draw whose checks run past
  it stops at the next mint and adds `:deferred {:phase :transitions}`: the part of the
  checks that ran out, and every mint it brought IN, whose own entailments the re-run
  draws (`redraw-deferred`).  Run under `call-with-pass-caches`."
  [kb h deadline]
  (let [sx (p/get-sentex (:records kb) h)]
    (if-not (sx/positive-fact? sx)
      empty-entailment-result
      (drawn-within deadline
                    #(deduce-placed kb (:sentence sx) h (:context sx) (changed-only kb h))))))

(defn redraw-deferred
  "Draw again what `draw-fact` set aside for `h`: the fact, then each mint of
  `transitions` it brought IN, whose entailments are drawn and, for one it created, its
  restatement at a merged term (`restate-retired`), as the cascade it stopped in
  would have.  The answer is `draw-fact`'s; a draw deferred again names the transitions of
  both attempts."
  [kb h transitions deadline]
  (let [recs (:records kb)
        r    (drawn-within
              deadline
              (fn []
                (reduce
                 (fn [acc [h2 new?]]
                   (let [sx (p/get-sentex recs h2)]
                     (if-not (sx/positive-fact? sx)
                       acc
                       (merge-with into acc
                                   (deduce-placed kb (:sentence sx) h2 (:context sx)
                                                  (changed-only kb h2))
                                   (when new? (outside-fact #(restate-retired kb sx)))))))
                 (let [sx (p/get-sentex recs h)]
                   (if (sx/positive-fact? sx)
                     (deduce-placed kb (:sentence sx) h (:context sx) (changed-only kb h))
                     empty-entailment-result))
                 transitions)))]
    (cond-> r
      (:deferred r) (update-in [:deferred :transitions]
                               #(into [] (distinct) (concat transitions %))))))

;; ---- definitional collection relations, expanded into forward rules -------
;; `(defnNecessary Coll C)` / `(defnSufficient Coll C)` / `(defnIff Coll C)` (docs/defns.md)
;; materialize as derived rules justified by the `defn*` fact, by the mint path
;; `chain/mint-rule` takes for a generator minus the join bindings.  Open-world only:
;; nothing concludes a non-member from the condition's failure.

(defn- materialize-defn-rule
  "Store one companion rule `r` (one conjunct or alternative from `rules/expand-rule`) as
  a derived rule sentex in `context`, justified by `[defn-handle]` under `informant`.
  Indexes the rule (`index-rule-sentex`), gives it a node one past the `defn*` fact's,
  and adds the justification once (`has-justification?`).  Returns `{:new [handles]
  :violations [v]}`; a rule that cannot be admitted is reported, not thrown.  A rule the
  `:arg-variable` arm convicts is stored and held inert (`checks/hold-rule-conviction!`)."
  [kb r defn-handle context informant]
  (let [minted (rules/expand-rule r)]
    (if-let [v (some #(checks/rule-violation kb % context) minted)]
      {:new [] :violations [(assoc v :sentence r :context context)]}
      (reduce
       (fn [acc one]
         (let [[h s new?] (kb/find-or-create-sentex kb one context)]
           (when new? (index-rule-sentex kb h s))
           (let [depth (inc (long (jtms/depth (reasoning/tms kb) defn-handle)))]
             (jtms/ensure-node (reasoning/tms kb) h depth)
             (when new? (checks/hold-rule-conviction! kb s))
             (when-not (jtms/has-justification? (reasoning/tms kb) informant [defn-handle] h)
               (let [jid  (p/next-id (:records kb))
                     ;; :monotonic conferred, capped by the `defn*` fact's own class in
                     ;; `conferred-class` — the rule adds no defeasibility of its own, so
                     ;; a default `defn*` makes a default rule, exactly as the lift does
                     just (jtms/->just jid informant [defn-handle] h {} :monotonic)]
                 (p/put-justification (:records kb) just)
                 (jtms/add-justification (reasoning/tms kb) just))))
           (if new? (update acc :new conj h) acc)))
       empty-entailment-result
       minted))))

(defn materialize-defn-rules
  "Materialize the forward rules a `defn*` fact stored at `defn-handle` in `context`
  expands into (`sx/defn-companion-rules`), each a derived rule sentex justified by the
  `defn*` fact alone: `{:new [handles] :violations [v]}`.  Called from `assert-one`.  A
  non-`defn*` sentence returns the empty result after one `defn-sentence?` read."
  [kb sentence defn-handle context]
  (if-not (sx/defn-sentence? sentence)
    empty-entailment-result
    (let [informant (nm/functor sentence)]
      (reduce (fn [acc r]
                (merge-with into acc
                            (materialize-defn-rule kb r defn-handle context informant)))
              empty-entailment-result
              (sx/defn-companion-rules sentence)))))

(defn- licensing-functors
  "The functors besides a rule antecedent's own whose facts move what that antecedent
  answers, for the antecedent keys `ruled?` accepts (`reads/stored-rule-key-test`, or the
  set `reads/as-stored-rule-keys`): the predicates a `SupportingProver` reads, a
  registered calculus's trigger predicates, `transitive` and the `inverse` partners for a
  declared-transitive predicate, and the declarations a preservation reads
  (`inherit/licensing-functors`).  Each family is tested against `ruled?` by membership.
  Read unscoped."
  [kb tx ruled?]
  (let [walked (filter ruled? (tax/props tx :transitive))]
    (-> #{}
        (cond-> (some ruled? (provers/support-answered-preds kb))
          (into (provers/support-source-preds kb)))
        (into (comp (filter #(some ruled? (:predicates %))) (mapcat :trigger-predicates))
              (qkb/registered-calculi kb))
        (cond-> (seq walked)
          (-> (conj 'transitive)
              (into (mapcat #(tax/inverses-under tx %)) walked)))
        (into (inherit/licensing-functors kb ruled?)))))

(defn- genl-inverse-edges
  "The `[sub super]` pair a `(genlInverse sub super)` sentence adds to the signed closure,
  as `tax/installed-edges` names a `genl` edge's; none for any other sentence."
  [sentence]
  (when (and (seq? sentence) (= 'genlInverse (nm/functor sentence)) (= 3 (count sentence))
             (symbol? (nth sentence 1)))
    [[(nth sentence 1) (nth sentence 2)]]))

(defn- rule-reads-above
  "A test of a `genl` edge's upper end `super`: does a stored rule read a term at or above
  `super`, an antecedent on one by `ruled?` (`reads/stored-rule-key-test`, or the stored
  key set), or an antecedent a re-join family moves when a fact on one arrives
  (`licensing-functors`)?  These are the readers whose answer a fact below a `(genl sub
  super)` edge changes.  The closure is global, as the seeds it filters are.  The fn reads
  the families once and holds each `super`'s answer and the terms whose upward closure
  meets no key (`tax/genls-global-meets?`), over one still store and taxonomy."
  [kb tax ruled?]
  (let [lf     (delay (licensing-functors kb tax ruled?))
        missed (volatile! #{})
        memo   (volatile! {})]
    (fn [super]
      (caches/get-or!
       memo super
       #(or (tax/genls-global-meets? tax super ruled? missed)
            (tax/genls-global-meets? tax super @lf)
            ;; above `super` across `genlInverse` edges too, read either way round
            (when-not (tax/genl-inverse-free? tax)
              (boolean (some (fn [t] (or (ruled? t) (contains? @lf t)))
                             (rules/signed-reach tax :up super)))))))))

(defn- negative-subsumption-seeds
  "The half of `subsumption-seeds` a negated antecedent is owed for the `[sub super]` pairs
  `edges`, read up `super`'s `genl` closure where the positive half reads down `sub`'s spec
  closure (docs/inference.md, \"Under a negation the fan reverses\").  A pair runs only when
  a stored rule reads a negated antecedent under `sub`: `ruled?` tests each term of a spec
  walk the key count bounds (`tax/specs-global-within`), and a larger reach meets
  `rules/stored-negated-keys`, read once for every pair, from the smaller side.  A
  functor's believed negative sentexes, decided by the head `not`, are read once.  Spec
  and `genls` reads are unscoped."
  [kb tx ruled? edges]
  (let [idx    (:index kb)
        recs   (:records kb)
        tms    (reasoning/tms kb)
        n      (reads/stored-rule-key-count idx)
        nk     (delay (rules/stored-negated-keys idx))
        under? (fn [sub]
                 ;; the bounded spec walk sees no genlInverse edge, so a KB declaring one
                 ;; meets the negated keys
                 (if-let [walk (when (tax/genl-inverse-free? tx) (tax/specs-global-within tx sub n))]
                   (some #(ruled? [:not %]) walk)
                   (let [nk @nk]
                     (when (seq nk)
                       (let [specs (rules/signed-reach tx :down sub)]
                         (if (< (count nk) (count specs))
                           (some #(contains? specs (second %)) nk)
                           (some #(contains? nk [:not %]) specs)))))))
        negs   (volatile! {})
        neg-in (fn [f]
                 (caches/get-or!
                  negs f
                  #(into [] (filter (fn [h]
                                      (and (jtms/in? tms h)
                                           (some-> (p/get-sentex recs h) sx/negative?))))
                         (reads/as-stored-with-functor idx f))))]
    (into [] (mapcat (fn [[sub super]]
                       (when (and (symbol? super) (under? sub))
                         (into [] (comp (mapcat neg-in) (distinct))
                               (rules/signed-reach tx :up super)))))
          edges)))

(defn- edges-subsumption-seeds
  "`subsumption-seeds` of the `[sub super]` pairs `edges`: the stored keys and each half's
  tests read once for all of them (`rule-reads-above`, `negative-subsumption-seeds`)."
  [kb edges]
  (if-let [ruled? (reads/stored-rule-key-test (:index kb))]
    (let [idx    (:index kb)
          tms    (reasoning/tms kb)
          tax    (reasoning/taxonomy kb)
          above? (rule-reads-above kb tax ruled?)]
      (into (into [] (comp (filter (fn [[_ super]] (above? super)))
                           (mapcat (fn [[sub _]] (rules/signed-reach tax :down sub)))
                           (distinct)
                           (mapcat #(reads/as-stored-with-functor idx %))
                           (distinct)
                           (filter #(jtms/in? tms %)))
                  edges)
            (negative-subsumption-seeds kb tax ruled? edges)))
    []))

(defn sentence-edges
  "The `[sub super]` pairs `sentence` adds to the signed `genl` closure."
  [sentence]
  (concat (tax/installed-edges sentence) (genl-inverse-edges sentence)))

(defn subsumption-seeds
  "The stored facts the `genl` edges `sentence` installs newly make matchable, as
  chaining seeds: the taxonomy twin of `lift-existing`.  The edges are
  `tax/installed-edges`' (a `genl` edge, or one per part of a cover).  The seeds are
  `sub`'s whole spec subtree, believed only, and per edge only when its `super` passes
  `rule-reads-above`.  The negated half is `negative-subsumption-seeds`; the removal side is
  `resubsumption-seeds`.  See docs/inference.md and docs/taxonomy.md."
  [kb sentence]
  (when-let [edges (seq (sentence-edges sentence))]
    (edges-subsumption-seeds kb edges)))

(defn batch-subsumption-seeds
  "`subsumption-seeds` of every sentence of `sentences` at once: an edge two of them install,
  and a functor two edges' subtrees share, are read once, and each seed appears once."
  [kb sentences]
  (when-let [edges (seq (into [] (comp (mapcat sentence-edges) (distinct)) sentences))]
    (into [] (distinct) (edges-subsumption-seeds kb edges))))

(def ^:dynamic *owed-subsumption*
  "A volatile `{opts [sentence …]}`: an assert under it records its sentence here, under the
  opts it chains with, in place of chaining its `subsumption-seeds`, and its binder chains
  each group's `batch-subsumption-seeds` once (`edit!`).  Nil chains them per assert."
  nil)

(defn minted-seeds
  "`handles` — sentexes an entailment minted — as chaining seeds, followed by the
  `subsumption-seeds` of each one that is a `genl` edge.  A `genlArg` mint is an edge
  like an asserted one, and the facts under it become matchable at the new supertype
  whichever of the two stored it: seeding the handle alone fires the rules keyed on
  `genl`, not the rules the edge connected, so `(wolf Rex)` and a rule on `(animal ?x)`
  stored before a minted `(genl wolf animal)` would derive nothing in that order only."
  [kb handles]
  (if (empty? handles)
    []
    (into (vec handles)
          (mapcat #(some->> (p/get-sentex (:records kb) %) :sentence (subsumption-seeds kb)))
          handles)))

(defn- transitive-left-ends
  "`a`, and every term that already reached it through believed stored `pred` links — the
  terms whose reach an arriving `(pred a b)` just extended.

  A stored walk rather than `provers/preds-of`, and context-free on purpose: these are
  CANDIDATES for the agenda, and the join that fires re-decides context, belief and
  placement for every one of them.  Bounded by the believed extent of `pred` reachable
  backwards from `a`, which on the ordinary load order — a chain arriving in its own
  direction — is the chain behind the new link and nothing else."
  [kb pred a]
  (let [idx  (:index kb)
        recs (:records kb)
        tms  (reasoning/tms kb)
        left (fn [h]
               (when-let [sx (p/get-sentex recs h)]
                 (let [sent (:sentence sx)]
                   (when (and (not (sx/negative? sx))
                              (nil? (:antecedent sx))
                              (= 3 (count sent))
                              (= pred (nm/functor sent)))
                     (second sent)))))]
    (graph/reach-all [a]
                     (fn [t]
                       (into [] (comp (filter #(jtms/in? tms %)) (keep left))
                             (reads/as-stored-with-arg-global idx 2 t))))))

(defn- transitive-partner-functors
  "The functors of the antecedents some rule has BESIDE a `pred` one — the triggers a
  grown `pred` closure could newly join to.  Empty when no rule takes a `pred`
  antecedent at all, which is the presence check that keeps an ordinary assert free."
  [kb pred]
  (let [idx  (:index kb)
        recs (:records kb)]
    (into #{}
          (comp (keep #(p/get-sentex recs %))
                (mapcat :antecedent)
                (keep nm/functor)
                (remove #{pred}))
          (reads/as-stored-rules-by-antecedent-global idx pred))))

(defn- believed-facts-with-functors
  "The believed stored FACT handles among `handles` whose functor is one of `functors`."
  [kb functors handles]
  (let [recs (:records kb)
        tms  (reasoning/tms kb)]
    (into []
          (comp (distinct)
                (filter #(jtms/in? tms %))
                (filter (fn [h]
                          (when-let [sx (p/get-sentex recs h)]
                            (and (nil? (:antecedent sx))
                                 (contains? functors (nm/functor (:sentence sx))))))))
          handles)))

(defn transitive-seeds
  "The stored facts a declared-transitive predicate's closure makes newly matchable, as
  chaining seeds: the `TransitivePredicateProver`'s twin of `subsumption-seeds`.  Two
  arrival orders: a link `(pred a b)` with `pred` already transitive seeds the believed
  facts mentioning a left end (`transitive-left-ends`); a declaration `(transitive pred)`
  over stored links seeds every believed fact on a partner functor.  Off unless some rule
  takes a `pred` antecedent.  The removal side needs no twin.  The mark is read unscoped.
  See docs/inference.md, \"Seeding a transitive closure\"."
  [kb sentence]
  (let [functor (nm/functor sentence)]
    (cond
      ;; the declaration arriving last, over links already stored
      (and (= 'transitive functor) (sequential? sentence) (= 2 (count sentence)))
      (let [pred (second sentence)]
        (when (and (symbol? pred) (not (contains? tax/closure-relations pred)))
          (let [partners (transitive-partner-functors kb pred)]
            (when (seq partners)
              (believed-facts-with-functors
               kb partners
               (mapcat #(reads/as-stored-with-functor (:index kb) %) partners))))))

      ;; a link arriving under a declaration already in force
      (and (symbol? functor)
           (sequential? sentence)
           (= 3 (count sentence))
           (not (contains? tax/closure-relations functor))
           (tax/has-prop? (reasoning/taxonomy kb) :transitive functor))
      (let [partners (transitive-partner-functors kb functor)]
        (when (seq partners)
          (believed-facts-with-functors
           kb partners
           (mapcat #(reads/as-stored-with-term (:index kb) %)
                   (transitive-left-ends kb functor (second sentence)))))))))

(defn transitive-rule-seeds
  "The stored facts a newly forward-capable rule needs back on the agenda when one of its
  antecedents reads a declared-transitive predicate: the third arrival order of
  `transitive-seeds`.  Off unless an antecedent is declared transitive.  Read unscoped."
  [kb rule-sentex]
  (let [antes (:antecedent rule-sentex)]
    (when (seq antes)
      (let [functors (into #{} (keep nm/functor) antes)
            trans    (into #{} (filter #(and (symbol? %)
                                             (not (contains? tax/closure-relations %))
                                             (tax/has-prop? (reasoning/taxonomy kb) :transitive %)))
                           functors)]
        (when (seq trans)
          (let [partners (into #{} (remove trans) functors)]
            (when (seq partners)
              (believed-facts-with-functors
               kb partners
               (mapcat #(reads/as-stored-with-functor (:index kb) %) partners)))))))))

(defn- rule-key-functors
  "The index functors the facts matchable by a stored rule's antecedent key root under:
  a positive key is a functor symbol whose `genl` spec closure is included, and a negated
  key `[:not g]` roots under `g` and `g`'s genl closure (docs/inference.md, \"Under a
  negation the fan reverses\").  The closures are global: the seeds are candidates for a
  re-join and the firing's placement narrows them."
  [tx k]
  (if (vector? k)
    (tax/genls-global tx (second k))
    (tax/specs-global tx k)))

(defn- key-fan
  "The functors a fact roots under for a rule keyed in `rule-keys`, a delay of the set,
  to match it, or a licensing functor: `{:all :member? :bound}`.  `:all` is a delay of
  `rule-key-functors` of every key with `licensing-functors`.  `:member?` answers one
  functor without building `:all` (`tax/genls-global-meets?`).  `:bound` is the key
  count `n`, below which `seeds-in` tests a context's postings one at a time."
  [kb tx rule-keys n]
  (let [lic    (delay (licensing-functors kb tx @rule-keys))
        small  (delay (into (into #{} (comp (filter vector?) (mapcat #(rule-key-functors tx %)))
                                  @rule-keys)
                            @lic))
        missed (volatile! #{})
        seen   (volatile! {})]
    {:all     (delay (into (into #{} (mapcat #(rule-key-functors tx %)) @rule-keys) @lic))
     :member? (fn [f]
                (let [m (get @seen f ::none)]
                  (if (identical? ::none m)
                    (let [m (or (contains? @small f)
                                (tax/genls-global-meets? tx f @rule-keys missed))]
                      (vswap! seen assoc f m)
                      m)
                    m)))
     :bound   n}))

(defn- seed-counts
  "`[by-functor by-context]`: the postings `seeds-in` would read under `functors`, and
  in `ctxs`, one count per functor and per context."
  [idx ctxs functors]
  [(transduce (map #(reads/stored-count-with-functor idx %)) + functors)
   (transduce (map #(reads/stored-count-in-context idx %)) + ctxs)])

(defn- seed-cost
  "The postings `seeds-in` reads for `ctxs` and `functors`: the smaller of the two sides."
  [kb ctxs functors]
  (apply min (seed-counts (:index kb) ctxs functors)))

(defn- seeds-in
  "The believed fact handles stored in one of `ctxs` under one of `functors`, a set or a
  `key-fan`, a negation counted under its body's functor.  Reads from whichever side
  holds fewer postings, decided by one count per functor and one per context.  With
  `keep?`, only the handles it keeps are read further.  The functor extents are the smaller
  side when the contexts hold the ontology, the contexts when they hold a context just wired
  in (empty, the commonest edge)."
  ([kb ctxs functors] (seeds-in kb ctxs functors nil))
  ([kb ctxs functors keep?]
   (let [idx  (:index kb)
         recs (:records kb)
         tms  (reasoning/tms kb)
         fan? (map? functors)
         by-c (transduce (map #(reads/stored-count-in-context idx %)) + ctxs)
         few? (<= by-c (if fan? (:bound functors) 0))
         member? (if fan? (:member? functors) #(contains? functors %))
         functors (when-not few? (if fan? @(:all functors) functors))
         by-f (if few? 0 (transduce (map #(reads/stored-count-with-functor idx %)) + functors))
         root (fn [s] (let [f (nm/functor s)]
                        (if (= sx/not-functor f) (nm/functor (second s)) f)))]
     (if (or few? (< by-c by-f))
       (into [] (comp (mapcat #(reads/as-stored-in-context idx %))
                      (distinct)
                      (if keep? (filter keep?) identity)
                      (filter #(jtms/in? tms %))
                      (filter (fn [h]
                                (when-let [s (p/get-sentex recs h)]
                                  (and (nil? (:antecedent s))
                                       (sequential? (:sentence s))
                                       (member? (root (:sentence s))))))))
             ctxs)
       (into [] (comp (mapcat #(reads/as-stored-with-functor idx %))
                      (distinct)
                      (if keep? (filter keep?) identity)
                      (filter #(jtms/in? tms %))
                      (filter (fn [h]
                                (when-let [s (p/get-sentex recs h)]
                                  (contains? ctxs (:context s))))))
             functors)))))

(defn- under-seen-edges
  "The believed facts stored in `up` that a `genl` edge stated in `seen` newly brings
  under a rule, as chaining seeds, read from the cheaper of two sides.  `n-edges` is the
  number of such edges `seen` states (`tax/supporter-count-in`).  When `up`'s facts under
  `functors` cost no more postings (`seed-cost`) they are the seeds; otherwise each edge
  is read as `subsumption-seeds` reads one arriving.  Only handles `before?` keeps are
  read (`move-seeds`' floor)."
  [kb tx rule-keys seen up functors n-edges before?]
  (if (<= (seed-cost kb up functors) n-edges)
    (seeds-in kb up functors before?)
    (let [edges  (into [] (comp (keep #(:sentence (p/get-sentex (:records kb) %)))
                                (mapcat tax/installed-edges))
                       (seeds-in kb seen tax/edge-installing-functors before?))
          above? (rule-reads-above kb tx rule-keys)
          negs   (into #{} (comp (filter vector?) (map second)) rule-keys)
          fs     (into #{} (mapcat (fn [[sub super]]
                                     (let [specs (tax/specs-global tx sub)]
                                       (concat (when (above? super) specs)
                                               (when (and (symbol? super)
                                                          (if (< (count negs) (count specs))
                                                            (some #(contains? specs %) negs)
                                                            (some #(contains? negs %) specs)))
                                                 (tax/genls-global tx super))))))
                       edges)]
      (if (seq fs) (seeds-in kb up fs before?) []))))

(defn move-seeds
  "The stored facts the `genlCx` move `m` (`context-move`) newly makes matchable, as
  chaining seeds: the context twin of `subsumption-seeds`.  `up` is `super`'s ancestor
  set (`:up`), `seen` what the contexts below `sub` that gain a context see beside it
  (`:gained-below`; `:below` in the unfiltered arity), `fresh` the contexts some reader
  below `sub` sees through the edge alone (`:moved`).  The unfiltered arity seeds every
  such fact of `up` and `seen`.  With `m`'s `:floor` (`seed-floor`), content stored at or
  above the floor arrived after the edge and is excluded.  See docs/contexts.md, \"A
  `genlCx` edge owes the same debt\"."
  [kb m filtered?]
  (let [idx           (:index kb)
        [n rule-keys] (when m (reads/as-stored-rule-keys-deferred idx))]
    (when rule-keys
      (let [tx      (reasoning/taxonomy kb)
            floor   (:floor m)
            before? (if floor #(< (long %) (long floor)) (constantly true))
            ruled?  (fn [cs] (reads/stores-rule-in? idx (set cs)))
            up      (:up m)
            seen    @(if filtered? (:gained-below m) (:below m))
            fresh   (:moved m)
            counts  (memoize (fn [cs] (tax/supporter-count-in tx :genl cs)))
            edged?  (fn [cs] (pos? (counts cs)))
            ;; the checks on `seen`, read below the floor: `seen` holds the contexts under
            ;; `sub`, which a batch stating the edge first goes on to fill
            ruled-seen? (delay (if floor
                                 (boolean (some before? (reads/as-stored-rules-in idx :rule (set seen))))
                                 (ruled? seen)))
            edged-seen? (delay (if floor
                                 (boolean (some before? (mapcat #(reads/as-stored-with-functor-in idx % (set seen))
                                                                tax/edge-installing-functors)))
                                 (edged? seen)))
            fan     (key-fan kb tx rule-keys n)
            ancestor-set
            (if filtered?
              (let [sides (cond-> []
                            @ruled-seen?                        (conj fresh)
                            (or (ruled? fresh) (edged? fresh)) (conj seen))]
                (cond
                  (seq sides) (into #{} cat sides)
                  (ruled? (remove fresh up))
                  (min-key #(transduce (map (fn [c] (reads/stored-count-in-context idx c))) + %)
                           seen fresh)
                  :else #{}))
              (into up seen))]
        ;; distinct: `under-seen-edges` reads `up`, which a side above may hold too
        (into [] (comp (distinct) (filter before?))
              (concat (when (seq ancestor-set) (seeds-in kb ancestor-set fan before?))
                      (when (and filtered? @edged-seen?)
                        (under-seen-edges kb tx @rule-keys seen up @(:all fan) (counts seen) before?))
                      (when (and filtered? @ruled-seen? (edged? fresh))
                        (under-seen-edges kb tx @rule-keys fresh up @(:all fan) (counts fresh) before?))))))))

(defn visibility-seeds
  "`move-seeds` for `sentence`, a `genlCx` edge between two symbols, and nil for any other
  sentence."
  ([kb sentence] (visibility-seeds kb sentence true))
  ([kb sentence filtered?]
   (when (and (= 'genlCx (nm/functor sentence)) (= 3 (count sentence))
              (symbol? (nth sentence 1)) (symbol? (nth sentence 2)))
     (move-seeds kb (context-move kb (nth sentence 1) (nth sentence 2)) filtered?))))

(def ^:private edge-functors
  "The two relations a firing can name a witness for, and so the two whose removal owes
  a re-chain.  The same set the taxonomy names `closure-relations`, aliased for the
  local reading the way `provers/transitive-predicates` and `inherit/virtual-relations`
  are: a firing rests on a *reachability* rather than on a stored link precisely because
  these two answer from a cached closure, so the two readings are one fact."
  tax/closure-relations)

(defn- closure-reader-rules
  "The rules carrying a positive antecedent on the closure relation `rel` (`genl` or
  `genlCx`), as chaining seeds: the rules a forward join answers from that closure
  (`chain/solve-closure`).  A firing of one names a single path between two terms, so
  the edge that leaves took a conclusion a second path may still license, and the facts
  under the edge are not what the rule joins over.  A rule handle on the agenda re-joins
  that rule in full.

  Nil off one membership test on a KB whose rules read neither relation."
  [kb rel]
  (when (reads/stored-rule-key? (:index kb) rel)
    (reads/as-stored-rules-by-antecedent-global (:index kb) rel)))

(defn closure-edge-relation
  "The closure relation `sentence` puts edges into: its functor for a binary `genl` or
  `genlCx` edge, `genl` for a cover (`tax/installed-edges`), and nil for any other sentence."
  [sentence]
  (when (seq? sentence)
    (let [f (nm/functor sentence)]
      (cond (and (contains? edge-functors f) (= 3 (count sentence))) f
            (seq (tax/installed-edges sentence))                        'genl))))

(defn- departed-edge-rejoin
  "The chaining seeds the edges `sentence` held in a closure owe on leaving it: the facts
  under its `genl` edges, the contexts its `genlCx` edge showed each other unless
  `sighted?` is false, and the rules that join over the closure it moved.
  `closure-edge-relation` must name one."
  ([kb sentence] (departed-edge-rejoin kb sentence true))
  ([kb sentence sighted?]
   (cond-> (vec (subsumption-seeds kb sentence))
     sighted? (into (visibility-seeds kb sentence false))
     true     (into (closure-reader-rules kb (closure-edge-relation sentence))))))

(defn firing-seeds
  "The antecedents of the rule firings (`firing-informant?`) among the justification
  records `js` that name a handle `edge?` holds as an antecedent, less the handles `gone?`
  holds, as chaining seeds.  The re-chain a departing edge owes a firing that named it as
  its witness: `sighting-seeds` here, and `vaelii.impl.record-edit/sweep!` for the firings
  a record edit left to its settle."
  [kb js edge? gone?]
  (into []
        (comp (filter #(and (firing-informant? kb (:informant %)) (some edge? (:antecedents %))))
              (mapcat :antecedents)
              (remove gone?)
              (distinct))
        js))

(defn- sighting-seeds
  "`firing-seeds` of the rule firings among `removed-jids` that name a `genlCx` edge in
  `removed`, less the handles in `removed`.  Every firing records its justification, a
  re-derivation of a stored conclusion included (`chain/place-fact-conclusion`), and a
  firing names the edges its placement saw each ingredient over
  (`chain/visibility-support`), so a firing whose placement the departing edge moved is
  one of these.  Empty, and no justification record read, unless `removed` holds a
  `genlCx` edge."
  [kb removed removed-jids]
  (let [edges (into #{} (comp (filter #(= 'genlCx (closure-edge-relation (:sentence %))))
                              (map :id))
                    removed)]
    (if (empty? edges)
      []
      (firing-seeds kb (keep #(p/get-justification (:records kb) %) removed-jids)
                    edges
                    (into #{} (map :id) removed)))))

(defn- edge-own-mints
  "The records among `removed` whose every justification in `removed-jids` is an
  argument-type mint (`kb/mint-informant?`) of a removed closure edge: the edge is the first
  antecedent, the fact the declaration typed.  Empty, and no justification record read,
  unless `removed` holds a closure edge and something besides it."
  [kb removed removed-jids]
  (let [edges (into #{} (comp (filter #(closure-edge-relation (:sentence %))) (map :id)) removed)]
    (if (or (empty? edges) (not (next removed)))
      #{}
      (let [by-conclusion (group-by :consequence
                                    (keep #(p/get-justification (:records kb) %) removed-jids))
            own? (fn [j] (and (kb/mint-informant? kb (:informant j))
                              (contains? edges (first (:antecedents j)))))]
        (into #{}
              (filter (fn [sx] (let [js (by-conclusion (:id sx))]
                                 (and (seq js) (every? own? js)))))
              removed)))))

(defn resubsumption-seeds
  "The chaining seeds a teardown owes, given the `removed` sentexes its sweep collected
  and the `removed-jids` justifications: `subsumption-seeds` and `visibility-seeds` in
  the retraction direction.  A departing `genl` edge seeds its spec subtree, read before
  the teardown, and the rules with an antecedent on the edge's own relation
  (`closure-reader-rules`), both only when the sweep took something besides the records
  asked for (`edge-own-mints` excluded).  A departing `genlCx` edge seeds the antecedents
  of the firings that named it (`sighting-seeds`) and its closure-reading rules.  See
  docs/contexts.md, \"A `genlCx` edge owes the same debt\"."
  [kb removed removed-jids]
  (let [rejoin (when (next (remove (edge-own-mints kb removed removed-jids) removed))
                 (into []
                       (comp (map :sentence)
                             (filter closure-edge-relation)
                             (distinct)
                             (mapcat #(departed-edge-rejoin kb % false)))
                       removed))
        sighted (sighting-seeds kb removed removed-jids)]
    (when (or (seq rejoin) (seq sighted))
      (into [] (distinct) (concat rejoin sighted)))))

(defn departed-edge-seeds
  "The chaining seeds a settle owes the records among `handles` that hold closure edges
  (`closure-edge-relation`) and went IN to OUT: `resubsumption-seeds` for an edge that
  lost belief rather than its record.  Runs per edge only when a dependent is now OUT
  (docs/nmtms.md, \"Where the layer stops\")."
  [kb handles]
  (let [tms (reasoning/tms kb)
        lost-dependent? (fn [h]
                          (some (fn [jid]
                                  (when-let [j (jtms/justification tms jid)]
                                    (not (jtms/in? tms (:consequence j)))))
                                (jtms/dependents tms h)))]
    (into []
          ;; the dependents are a network read and the record a store fetch, so the filter
          ;; that drops nearly every departed datum runs first
          (comp (filter lost-dependent?)
                (keep (fn [h]
                        (let [s (:sentence (p/get-sentex (:records kb) h))]
                          (when (closure-edge-relation s) s))))
                (distinct)
                (mapcat #(departed-edge-rejoin kb %))
                (distinct))
          handles)))

(defn- handle-twins
  "The live twins a merge has already made of sentex `orig`, a reader's copies among
  them: `[{:twin :informant :witnesses :reader}]`.  A twin is the `:consequence` of a
  `rewriteOf`- or `except`-informant justification whose first antecedent is `orig`
  (`justify-twin!`).  Empty when `orig` has no twin, and for an equality sentence, which
  migration never restates (`kb/rewritable-sentex?`; docs/equational.md)."
  [kb orig]
  (let [tms (reasoning/tms kb)]
    (->> (when-not (some-> (p/get-sentex (:records kb) orig) :sentence kb/equality-sentence?)
           (jtms/dependents tms orig))
         (map #(jtms/justification tms %))
         (filter #(and (#{'rewriteOf 'except} (:informant %)) (= orig (first (:antecedents %)))))
         (group-by (juxt :consequence :informant))
         (keep (fn [[[twin informant] justs]]
                 (when-let [tsx (p/get-sentex (:records kb) twin)]
                   {:twin      twin
                    :informant informant
                    :witnesses (into [] (comp (map #(subvec (vec (:antecedents %)) 1)) (distinct))
                                     justs)
                    :reader    (:context tsx)}))))))

;; A mint withdrawn by a sweep leaves no OUT conclusion for `departed-edge-seeds`'
;; condition to read, and the firings naming it as their witness are deleted with it, so
;; this fn draws them again over the route that made the mint redundant.
(defn withdrawn-edge-seeds
  "The chaining seeds a settle owes the closure edges among `handles`, mints it is about
  to withdraw as redundant (`subsumed-mint-blocks`) or spellings a merge retired
  (`settle/withdraw-retired-firings!`), that a rule firing names as its witness:
  `departed-edge-rejoin`'s facts and rules for each such edge and each of its twins
  (`handle-twins`).  The condition is a dependent justification whose informant is a rule,
  read before the sweep deletes it.  See docs/argtypes.md."
  [kb handles]
  (let [tms (reasoning/tms kb)
        fired-over? (fn [h]
                      (some (fn [jid]
                              (when-let [j (jtms/justification tms jid)]
                                (firing-informant? kb (:informant j))))
                            (jtms/dependents tms h)))]
    (into []
          (comp (filter fired-over?)
                (mapcat (fn [h] (cons h (map :twin (handle-twins kb h)))))
                (keep (fn [h]
                        (let [s (:sentence (p/get-sentex (:records kb) h))]
                          (when (closure-edge-relation s) s))))
                (distinct)
                (mapcat #(departed-edge-rejoin kb %))
                (distinct))
          handles)))

;; ---- equality: rewriteOf / sameAs / equals ------------------------------
;; Migration, supersession and the collision merges (docs/equality.md, "What a merge
;; does").  The partition is `vaelii.impl.taxonomy`'s, and the goal rewrite and
;; `rewritable-sentex?` are `vaelii.impl.kb`'s.

(defn- wff-violation*
  "`wff-problems` as a **value** in the shape `checks/constraint-violation` returns —
  the derivation-path form of the well-formedness check.  Public as `wff-violation`
  below the table; declared-through here because migration needs it before the
  table exists."
  [kb sentence context]
  (when-let [ps (seq (wff-problems (reasoning/taxonomy kb) sentence context))]
    {:violation :not-well-formed
     :detail    {:problems (vec ps)
                 :message  (str "not well-formed: " (str/join "; " ps))}}))

(defn- justify-twin!
  "Justify a migrated twin `twin-handle` by `[orig-handle & w]` under `informant` for each
  witness `w` in `witnesses`: `[equality]` under `rewriteOf` for a twin, `[equality except]`
  under `except` for a reader's copy (`migrate-into`).  One justification per witness, each
  conferring `:monotonic`, so `conferred-class` caps the twin at its weakest antecedent.
  Idempotent (`has-justification?`)."
  [kb orig-handle twin-handle informant witnesses]
  (let [tms (reasoning/tms kb)]
    (doseq [w (distinct witnesses)]
      (let [antes (into [orig-handle] w)
            depth (inc (reduce max (map #(jtms/depth tms %) antes)))]
        (jtms/ensure-node tms twin-handle depth)
        (when-not (jtms/has-justification? tms informant antes twin-handle)
          (let [jid  (p/next-id (:records kb))
                just (jtms/->just jid informant antes twin-handle {} :monotonic)]
            (p/put-justification (:records kb) just)
            (jtms/add-justification tms just)))))))

(defn- varmap-realign
  "The substitution mapping the *original* rule's canonical variables to the `twin`'s:
  the inverse of `(:varmap twin)`, since the twin is built from the original's canonical
  sentence.  A migrated exception's query is stored in the original's variables
  (`assert-exceptWhen-meta!`).  The identity unless the merge reordered the antecedents."
  [twin]
  (into {} (keep (fn [[tv ov]] (when (not= tv ov) [ov tv]))) (:varmap twin)))

(defn- retarget-handle
  "Replace every `(sentexHandle orig)` in `form` with `(sentexHandle twin)`, recursively —
  the handle-swap that re-points a meta from a superseded sentex onto its twin.  Any other
  handle and every non-handle term is untouched."
  [form orig twin]
  (cond
    (and (sx/sentex-handle? form) (= orig (sx/handle-id form))) (sx/sentex-handle twin)
    (sequential? form) (apply list (map #(retarget-handle % orig twin) form))
    :else form))

(defn- meta-target
  "The handle a handle-naming meta-sentex `s` names, or nil.  An `exceptWhen` names its
  rule, an `except` its sentex, and a `target_following_predicate` meta its single
  `(sentexHandle H)` argument.  Read unscoped."
  [kb s]
  (or (sx/exceptWhen-rule-handle s)
      (kb/except-target s)
      (when (and (sequential? s) (symbol? (first s))
                 (tax/has-prop? (reasoning/taxonomy kb) :target-following (first s)))
        (some #(when (sx/sentex-handle? %) (sx/handle-id %)) s))))

(defn- rebuild-handle-meta
  "The twin meta naming `twin` where `s` named `orig`.  An `exceptWhen` re-points and
  realigns its query — the terms to `reader`'s representatives, the variables to the twin's
  canonical numbering — and rebuilds through `exceptWhen-meta` so the conjuncts sort
  canonically.  Every other handle-naming meta (`except`, a target-following reply) is
  ground: rewrite its terms to `reader`'s representatives (a no-op when it mentions no
  merged term) and retarget the handle."
  [kb s orig twin realign reader]
  (if (sx/exceptWhen-meta? s)
    (sx/exceptWhen-meta
     (mapv #(sx/canon (sx/rename-vars (kb/rewrite-term kb % reader) realign))
           (sx/exception-query-conjuncts s))
     twin)
    (sx/canon (retarget-handle (kb/rewrite-term kb s reader) orig twin))))

(defn migrate-handle-metas
  "Carry every believed handle-naming meta of sentex `orig` onto its migrated twin `twin`
  (docs/equality.md, \"Handle-naming metas travel with their target\"): each meta gets a
  twin naming `twin`, its terms rewritten to `reader`'s representatives, registered through
  `integrate-twin` and justified by the meta and each of `witnesses` under `informant`
  (`justify-twin!`).  The 5-arity takes `eqs`, the migrating equalities, under `rewriteOf`.
  Public for `integrate/commute-existing`."
  ([kb orig twin eqs reader]
   (migrate-handle-metas kb orig twin 'rewriteOf (map vector eqs) reader))
  ([kb orig twin informant witnesses reader]
   (let [realign (varmap-realign (p/get-sentex (:records kb) twin))]
     (doseq [mh   (reads/as-stored-naming-handle (:index kb) orig)
             :let  [msx (p/get-sentex (:records kb) mh)
                    s   (and msx (:sentence msx))]
             :when (and msx (jtms/in? (reasoning/tms kb) mh) (= orig (meta-target kb s)))]
       (let [m'  (rebuild-handle-meta kb s orig twin realign reader)
             ctx (:context msx)
             [h sx2 new?] (kb/find-or-create-sentex kb m' ctx)]
         (when new? (integrate-twin kb sx2 h))
         (justify-twin! kb mh h informant witnesses))))))

(defn migrate-meta-onto-twins
  "The handle-naming meta `sentex` was just stored: when its target already has twins, the
  merge ran before the meta existed, so replay `migrate-handle-metas` onto each twin.
  Idempotent for the metas already carried.  nil, and a no-op when `sentex` names nothing
  or its target has no twin."
  [kb sentex]
  (when-let [target (meta-target kb (:sentence sentex))]
    (doseq [{:keys [twin informant witnesses reader]} (handle-twins kb target)]
      (migrate-handle-metas kb target twin informant witnesses reader))))

(defn bearing-equalities
  "The handles of every equality edge and schematic rewrite rule that could bear on
  `sentence`: the supporters across the whole **class** of each merged symbol it names
  (docs/equality.md, \"The reader is not the fact's own context\"), unbelieved ones
  included, since each candidate reader re-reads belief and visibility.  Empty when no
  symbol of `sentence` is merged and no rule applies, decided before any class walk or
  record read: the assert path offers every sentex to migration."
  [kb sentence]
  (let [tx      (reasoning/taxonomy kb)
        merged? (tax/merged-term-pred tx)
        terms   (when merged? (sx/symbols-where merged? sentence))
        rules   (filterv #(rewrite/rule-applies? % sentence) (tax/rewrite-rules tx))]
    (if (and (empty? terms) (empty? rules))
      #{}
      (into #{}
            (concat (for [t terms, m (tax/equiv-class tx t), eh (tax/equality-supporters tx m)]
                      eh)
                    (map :handle rules))))))

(defn- except-contexts
  "The contexts holding an `except` of one of the handles `ehs`, read by target
  (`reads/as-stored-naming-by-context`).  Empty on one count read for a KB storing no
  `except`."
  [kb ehs]
  (let [idx (:index kb)]
    (if-not (reads/stores-any? idx sx/except-functor)
      #{}
      (into #{} (comp (mapcat #(reads/as-stored-naming-by-context idx sx/except-functor %))
                      (map first))
            ehs))))

(defn reader-contexts-at
  "The contexts whose election could restate `sentence`, stated in `pctx`, differently:
  `pctx`, and every context where it meets an equality that bears on `sentence` or an
  `except` of one.  Migration passes a stored sentex's own; a guard passes its placement
  and its substituted condition (`chain/guard-solutions`).

  **The reader is not the fact's own context.**  A merge holds where it is visible, and
  who reads the fact is any context below it — each electing a representative over a
  different set of visible edges (`tax/scoped-class`).  A single normal form computed
  at the fact's context serves only that one reader; one computed globally serves none
  reliably, since it can be elected by an edge no reader of the fact inherits.  So the
  parties are `tax/meet-closure` of the fact's context with the equalities' — the same
  enumeration a qualitative network takes (docs/qcn.md) and for the same reason.  The
  contexts holding an `except` of one of those equalities are parties too: a reader
  below the fact that reads the except sees less than the fact's context, and
  `migrate-into` stores the fact's spelling there when the fact's context supersedes it.

  Filtered to contexts that **see** the fact: a context the fact is invisible from has
  nothing of it to restate.  Ordered most-general first, by the size of the context's
  own up-closure and then by name — a content-keyed order, so which twin a duplicate
  form collapses into cannot depend on arrival.  The fact's own context leads
  explicitly rather than by that key: it is the only reader that supersedes, and two
  mutually-visible contexts have up-closures of a size that would otherwise let a name
  decide which of them is the fact's.

  **No equality bearing on the sentence means no reader**, and that is the presence check:
  nothing can restate it, so migration reads no closure and runs no rewrite.  One equality
  context closes almost as fast — `meet-closure` of a comparable pair is the pair, and
  the filter leaves the fact's own context alone."
  [kb pctx sentence]
  (let [tx    (reasoning/taxonomy kb)
        ehs   (bearing-equalities kb sentence)]
    (when (seq ehs)
      (->> (tax/meet-closure tx (-> #{pctx}
                                    (into (keep #(:context (p/get-sentex (:records kb) %))) ehs)
                                    (into (except-contexts kb ehs))))
           (filter #(tax/sees? tx % pctx))
           ;; the middle key is a taxonomy-closure read — built once per context, not
           ;; ~2·n·log n times; the tuple is `[0/1 long string]`, ordered by `compare`
           (nm/sort-by-content-key
            (juxt #(if (= % pctx) 0 1) #(count (tax/context-up tx %)) nm/print-key)
            compare)))))

(defn- copy-witnesses
  "The `[equality except]` witnesses of a reader's copy of `sentex` in `reader`, sorted:
  each equality among `cands` that is believed and stated where the sentex's own context
  sees it, paired with each believed `except` of it stated in a context `reader` sees and
  the sentex's own context does not.  Empty for the sentex's own context, and on one
  deref for a KB storing no `except`.  An except of that `except` is not read here: it
  withdraws the copy through the copy's third antecedent, so the copies stored do not
  depend on whether it arrived first."
  [kb sentex reader cands]
  (let [idx  (:index kb)
        pctx (:context sentex)]
    (when (and (not= reader pctx) (reads/stores-any? idx sx/except-functor))
      (let [tx  (reasoning/taxonomy kb)
            tms (reasoning/tms kb)
            x?  #(and (tax/sees? tx reader %) (not (tax/sees? tx pctx %)))]
        (not-empty
         (sort (for [eh     (distinct cands)
                     :let   [esx (p/get-sentex (:records kb) eh)]
                     :when  (and esx (jtms/in? tms eh) (tax/sees? tx pctx (:context esx)))
                     [c xs] (reads/as-stored-naming-by-context idx sx/except-functor eh)
                     :when  (x? c)
                     xh     xs
                     :when  (jtms/in? tms xh)]
                 [eh xh])))))))

(defn- store-restatement
  "Store `form`, `sentex`'s restatement for `reader`, in `reader`, justified by `[sentex &
  w]` under `informant` for each witness `w` (`justify-twin!`), and carry the sentex's
  handle-naming metas onto it.  Returns `{:form :new}`, or `{:form :violations}` when the
  form is inadmissible on the derivation path (`checks/derivation-violation`, or
  malformed).  An arbitrable clash is admitted: the twin is stored and its clash decided
  at each reader like any stored clash."
  [kb sentex reader form informant witnesses]
  (let [existing (kb/find-sentex-handle kb form reader)
        v        (when-not existing
                   (or (checks/derivation-violation kb form reader)
                       (wff-violation* kb form reader)))]
    (if v
      {:form form :violations [(assoc v :sentence form :context reader :rule (:id sentex))]}
      ;; a rule's wrappers ride the record, so the bare rewritten implication is re-wrapped
      (let [twin-sentence (if (rules/rule-sentence? form) (rules/rewrap-sentex form sentex) form)
            [h s new?]    (kb/find-or-create-sentex kb twin-sentence reader)]
        ;; every integration arm an asserted sentex reaches, not only the genl edges
        (when new? (integrate-twin kb s h))
        (justify-twin! kb (:id sentex) h informant witnesses)
        (migrate-handle-metas kb (:id sentex) h informant witnesses reader)
        {:form form :new (if new? [h] []) :handle h}))))

(defn- migrate-into
  "Restate `sentex` as `reader` sees it, and store the result there.  Returns
  `{:form <normal form> :new [h] :superseded [[datum reason]] :violations [v]}`, or nil
  when `reader`'s election leaves the sentence alone, rests on nothing it believes, or
  reproduces a form `placed` already holds somewhere `reader` can see — that twin is
  already this reader's answer and a second copy would report the fact twice.

  A reader strictly below the sentex's context whose election leaves the sentence alone
  because it reads an `except` of an equality the sentex's context rewrites under gets a
  **copy**: the sentex's own spelling stored in `reader`, justified by `[sentex equality
  except]` under informant `except` (`copy-witnesses`).  The sentex's context supersedes
  the original and the twin rests on the equality `reader` cannot see, so without the copy
  `reader` reads the fact under neither spelling.  The copy is handed to the reconcile as
  a `:superseded` candidate, which retires it while the original is not superseded
  (`displacement`)."
  [kb sentex reader placed]
  (let [sentence  (sx/sentence-of sentex)
        tx        (reasoning/taxonomy kb)
        vis       (res/visible-supporter-fn kb reader)
        rewritten (sx/canon (kb/rewrite-term* kb sentence vis))
        ;; each witness also names the `genlCx` edges `reader` sees the sentex and the
        ;; witness through, so retracting one withdraws the restatement and a surviving
        ;; path draws it again (`rederive-descended`)
        sighted   (fn [ws]
                    (let [seen (checks/visibility-support kb (:id sentex) reader)
                          via  #(checks/visibility-support kb % reader)]
                      (map (fn [w] (into (vec w) (distinct) (concat seen (mapcat via w)))) ws)))]
    (when-not (some (fn [[c f]] (and (= f rewritten) (tax/sees? tx reader c))) placed)
      ;; the equalities incident on a term of the sentence, and the schematic rewrite
      ;; rules that normalize a subterm of it
      (let [rule-hs (for [{:keys [handle] :as rule} (tax/rewrite-rules tx)
                          :when (rewrite/rule-applies? rule sentence)]
                      handle)
            cands   (concat (mapcat #(tax/equality-supporters tx %)
                                    (filter symbol? (tree-seq sequential? seq sentence)))
                            rule-hs)]
        (if (= rewritten (sx/canon sentence))
          (when-let [ws (seq (copy-witnesses kb sentex reader cands))]
            (let [r (store-restatement kb sentex reader rewritten 'except (sighted ws))]
              (cond-> (dissoc r :handle)
                (:handle r) (assoc :superseded [[(:handle r) {}]]))))
          ;; a twin's witness names, for each term the reader's election displaces, every
          ;; equality on one path from it to its representative, and each schematic rule
          ;; that normalizes a subterm, so dropping any one withdraws the twin and a
          ;; surviving path draws it again (`rederive-descended`).  One witness per choice
          ;; of supporter along the paths (`tax/path-alternatives`); all of them are
          ;; believed and visible from the reader whose restatement this is
          (let [displaced (kb/displaced-terms* kb sentence vis)
                ws        (reduce (fn [acc path] (for [a acc, alt (tax/path-alternatives path)] (into a alt)))
                                  [(into (sorted-set) (filter vis) rule-hs)]
                                  (keep (fn [[t r]] (tax/scoped-path-supporters tx t r vis)) displaced))]
            (when (seq (first ws))
              (let [r (store-restatement kb sentex reader rewritten 'rewriteOf
                                         (sighted (map vec (distinct ws))))]
                (cond-> (dissoc r :handle)
                  ;; only the fact's own context supersedes
                  (and (:handle r) (= reader (:context sentex)))
                  (assoc :superseded [[(:id sentex) displaced]]))))))))))

(defn migrate-sentex
  "Restate one stored sentex under its terms' representatives, once per reader whose
  election differs (`reader-contexts-at`; docs/equality.md, \"What a merge does\").
  `{:new [handles] :superseded [[datum reason]] :violations [v]}`.

  Each twin is re-canonicalized through find-or-create rather than substituted, justified
  by the original and the equalities of one path per displaced term (`migrate-into`),
  placed in the reader that elected it, and checked as a derivation
  (`checks/derivation-violation`).  Only the fact's own context supersedes.  An
  inadmissible twin is dropped into `:violations`, and its original stays believed."
  [kb sentex]
  (-> (reduce (fn [acc reader]
                (if-let [r (migrate-into kb sentex reader (:placed acc))]
                  (-> acc
                      (update :placed conj [reader (:form r)])
                      (update :new into (:new r))
                      (update :superseded into (:superseded r))
                      (update :violations into (:violations r)))
                  acc))
              {:placed [] :new [] :superseded [] :violations []}
              (reader-contexts-at kb (:context sentex) (sx/sentence-of sentex)))
      (dissoc :placed)))

(defn- migrate-class
  "Restate every stored rewritable sentex naming a term of `terms` that some reader's
  election retires (`tax/retirable?`), the global representative included, whatever its
  label.  Walking the whole class re-migrates when a late `rewriteOf` moves the
  representative, and an OUT sentex takes a twin labelled OUT with it."
  [kb terms]
  (reduce
   (fn [acc t]
     (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
             acc
             (filter #(kb/rewritable-sentex? kb %) (kb/find-sentexes kb t))))
   {:new [] :superseded [] :violations []}
   (filter #(tax/retirable? (reasoning/taxonomy kb) %) terms)))

(defn- integrate-equality
  "The symbol equality's add arm: reflect the sentex into the closure, queue the re-check
  over its class (`recheck-equality-edge`) and migrate the class.  `derive-equality`
  calls it directly."
  [kb sentex handle]
  (let [sentence (:sentence sentex)
        [_ a b]  sentence]
    (tax/add-equality (reasoning/taxonomy kb) a b handle (kb/preferred-term sentence))
    (let [class (tax/equiv-class (reasoning/taxonomy kb) a)]
      (recheck-equality-edge kb (set class))
      (migrate-class kb class))))

(defn- migrate-matching
  "Migrate every rewritable stored sentex naming symbol `head` — the candidate set for
  a schematic rewrite rule whose LHS is headed by `head`.  The head is present in
  every occurrence of the redex, so the term index gives a superset in one lookup;
  `migrate-sentex` recomputes each sentence's normal form and twins only the ones that
  actually change.  Same shape as `migrate-class`, keyed by the rule's LHS head rather
  than by a merged term's class, and like it whatever the sentex's label."
  [kb head]
  (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
          {:new [] :superseded [] :violations []}
          (filter #(kb/rewritable-sentex? kb %) (kb/find-sentexes kb head))))

(defn- confluence-violations
  "Non-confluent conflicts the just-cached rule `handle` forms with the other active
  rewrite rules, as violation entries for the ledger — **detection, not completion**
  (docs/equational.md).  A `:non-confluent` entry names the two rules and the two
  forms a shared term normalizes to, so the author sees that two schematic equations
  disagree; the engine still gives a deterministic normal form, so nothing is dropped."
  [kb sentex handle lhs rhs]
  (let [new-rule {:handle handle :lhs lhs :rhs rhs}]
    (for [nj (rewrite/non-joining-pairs new-rule (tax/rewrite-rules (reasoning/taxonomy kb)))]
      {:violation :non-confluent
       :rule      handle
       :with      (:with nj)
       :sentence  (:sentence sentex)
       :message   (str "non-confluent schematic rewrite rules " handle " and " (:with nj)
                       ": a shared term normalizes to both " (pr-str (:form-a nj))
                       " and " (pr-str (:form-b nj)))})))

(defn- integrate-rewrite-rule
  "A schematic equation's add arm (docs/equational.md): orient `(equals a b)` into a
  terminating rewrite, cache it belief-following in the taxonomy, migrate every stored
  sentex it normalizes to a justified twin — exactly the shape `integrate-equality`
  has for a symbol merge — and **surface** any non-confluent conflict with an existing
  rule into the migration result's `:violations` (filed by `assert` through
  `violations/report`, and logged).  Returns the migration result so the twins seed
  chaining.  Orientability was already enforced by `wff/equality-problems`, so `orient`
  never returns nil here."
  [kb sentex handle]
  (let [[_ a b]   (:sentence sentex)
        [lhs rhs] (rewrite/orient a b)]
    (tax/add-rewrite-rule (reasoning/taxonomy kb) handle lhs rhs (:context sentex))
    (recheck-equality-edge kb)
    (update (migrate-matching kb (first lhs))
            :violations into (confluence-violations kb sentex handle lhs rhs))))

(defn- equality-wff-problems
  "`wff/equality-problems` for the `rewriteOf` / `sameAs` / `equals` sentence `s`.  Under
  `checks/*entry-mints?*`, the check replaces a ground application of a
  `reifiable_function` in a `sameAs` or `equals` argument with `nat/minted`, the symbol
  standing for the constant the entry point mints, since the firing or `check` asking has
  not minted it yet (docs/nat.md, Derivation path).  The mark is read KB-wide, as
  `nat-read/reifiable-function?` reads it for the mint.  A `rewriteOf` payload is a
  verbatim expression and is checked as written."
  [tax [f & args :as s] context]
  (let [minted? (fn [a] (and (sequential? a) (seq a) (symbol? (first a))
                             (not (nat-read/reified-nat-symbol? (first a)))
                             (not (contains? nat-read/*withheld* (first a)))
                             (tax/has-prop? tax :reifiable (first a))
                             (sx/ground-term? a)))]
    (wff/equality-problems
     tax
     (if (and checks/*entry-mints?* tax (not (contains? res/nat-quoting-predicates f)))
       (apply list f (map #(if (minted? %) 'nat/minted %) args))
       s)
     context)))

(defn integrate-equality-sentex
  "The three equality relations' add arm on every entry point, asserted or derived.
  Returns the migration result `{:new :superseded :violations}`, which the derivation
  path seeds chaining with and files (docs/equality.md, \"A rule concluding one of the
  three relations merges\").  A schematic `(equals L R)` goes to
  `integrate-rewrite-rule`, and a `(rewriteOf T E)` with a compound `E` is a NAT
  reify-to-term declaration the partition holds no part of (`equality-entry`)."
  [kb sentex handle]
  (let [s (:sentence sentex) [_ _ b] s]
    (cond
      (rewrite/schematic-equation? s) (integrate-rewrite-rule kb sentex handle)
      (sequential? b)                 nil   ; NAT rewriteOf-to-compound
      :else                           (integrate-equality kb sentex handle))))

(defn- believed-restatements
  "Every believed equality sentex and schematic rewrite rule stated in one of `ctxs`, as
  `{:context :terms}`: an equality contributes the retirable members of its arguments'
  classes (`migrate-class`'s candidates), a rule its LHS head (`migrate-matching`'s).
  Read off the equality predicates' extents ending in `ctxs` and the rule cache, so the
  cost follows the merges stated in `ctxs` and not every standing merge."
  [kb ctxs]
  (let [tx   (reasoning/taxonomy kb)
        idx  (:index kb)
        recs (:records kb)
        tms  (reasoning/tms kb)]
    (into (into []
                (comp (mapcat #(reads/as-stored-with-functor-in idx % ctxs))
                      (distinct)
                      (filter #(jtms/in? tms %))
                      (keep #(p/get-sentex recs %))
                      (map (fn [sx]
                             {:context (:context sx)
                              :terms   (into #{}
                                             (comp (filter symbol?)
                                                   (mapcat #(tax/equiv-class tx %))
                                                   (filter #(tax/retirable? tx %)))
                                             (rest (:sentence sx)))})))
                (sort kb/equality-predicates))
          (comp (filter #(and (contains? ctxs (:context %))
                              (sequential? (:lhs %)) (symbol? (first (:lhs %)))))
                (map (fn [r] {:context (:context r) :terms #{(first (:lhs r))}})))
          (tax/rewrite-rules tx))))

(defn- restated-terms-in
  "The terms the `restatements` stored in one of `ctxs` put in play."
  [restatements ctxs]
  (into #{} (comp (filter #(contains? ctxs (:context %))) (mapcat :terms)) restatements))

(defn- ancestor-migration-candidates
  "The stored sentexes naming one of `terms` whose context is in `ctxs` and which
  migration may restate: rewritable, whatever its label, as `migrate-class` admits them.
  Keyed by handle, so a sentex reached through two of its terms is migrated once."
  [kb terms ctxs]
  (into {}
        (comp (mapcat #(kb/find-sentexes kb %))
              (filter #(and (contains? ctxs (:context %)) (kb/rewritable-sentex? kb %)))
              (map (juxt :id identity)))
        terms))

(defn migrate-under-context-edge
  "When the `genlCx` move `m` (`context-move`) shows contexts, restate the sentexes the
  widened ancestor set newly exposes to a merge: the edge-arriving-last order
  (docs/equality.md, \"A late `genlCx` edge is a third arrival order\").  Both halves
  run: a merge in the shown contexts meets the facts the readers already saw, and a fact
  there meets the merges they already saw.  Each half is enumerated from the merges
  through the term index."
  [kb m]
  (let [tx            (reasoning/taxonomy kb)
        [sub super]   (:edge m)]
    (when (and (symbol? sub) (symbol? super)
               (or (seq (tax/equality-edges tx)) (seq (tax/rewrite-rules tx))))
      (let [;; the contexts some reader under `sub` sees through the edge alone
            above   (:moved m)
            ;; every context a reader under `sub` sees, each reading the merges and the
            ;; facts of its own ancestor set
            readers @(:seen m)
            rs      (believed-restatements kb (into readers above))
            near    (restated-terms-in rs above)
            far     (restated-terms-in rs readers)
            cands   (merge (when (seq near) (ancestor-migration-candidates kb near readers))
                           (when (seq far)  (ancestor-migration-candidates kb far above)))]
        (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
                {:new [] :superseded [] :violations []}
                (vals cands))))))

(defn- spelling-displacement
  "The supersession entry `[d {displaced-term representative}]` for datum `d`, or nil when
  `d`'s spelling is not displaced or `d` is no longer stored.  Read from the sentex's own
  context, as migration writes it, and displaced only while the restatement is stored.

  `visible-for` is the caller's memo from context to visibility predicate, so the walk
  fetches each supporter record once rather than once per entry."
  [kb visible-for d]
  (when-let [sx (p/get-sentex (:records kb) d)]
    (let [ctx       (:context sx)
          visible?  (visible-for ctx)
          sentence  (sx/sentence-of sx)
          rewritten (sx/canon (kb/rewrite-term* kb sentence visible?))]
      (when (and (not= rewritten (sx/canon sentence))
                 (kb/find-sentex-handle kb rewritten ctx))
        [d (kb/displaced-terms* kb sentence visible?)]))))

(defn- reader-copies
  "The reader's copies of datum `d` (`migrate-into`): the consequences of the `except`
  justifications whose first antecedent is `d`."
  [kb d]
  (let [tms (reasoning/tms kb)]
    (into []
          (keep (fn [jid]
                  (let [j (jtms/justification tms jid)]
                    (when (and (= 'except (:informant j)) (= d (first (:antecedents j))))
                      (:consequence j)))))
          (jtms/dependents tms d))))

(defn- retired-copy
  "The supersession entry `[d {}]` for a reader's copy `d` whose reason is gone, or nil.
  A copy (`migrate-into`) restates an original its own context supersedes, and it is
  retired once one of its originals is no longer displaced: the reader then reads that
  original, and the copy would report the fact a second time.  A datum that is a premise,
  or holds any justification besides a copy's, is not retired.  Nil on one deref for a
  KB storing no `except`."
  [kb visible-for d]
  (when (reads/stores-any? (:index kb) sx/except-functor)
    (let [tms (reasoning/tms kb)
          js  (keep #(jtms/justification tms %) (jtms/supports tms d))]
      (when (and (seq js)
                 (not (jtms/premise? tms d))
                 (every? #(= 'except (:informant %)) js)
                 (some #(nil? (spelling-displacement kb visible-for (first (:antecedents %)))) js))
        [d {}]))))

(defn- displacement
  "The supersession entry for datum `d`: `spelling-displacement`'s, or a retired reader's
  copy's (`retired-copy`), or nil."
  [kb visible-for d]
  (or (spelling-displacement kb visible-for d) (retired-copy kb visible-for d)))

(defn- with-copies
  "`ds` followed by the reader's copies of each (`reader-copies`): a copy's retirement
  reads its original's displacement (`retired-copy`), so a reconcile that examines the
  original examines its copies.  `ds` alone on one count read for a KB storing no
  `except`."
  [kb ds]
  (if-not (reads/stores-any? (:index kb) sx/except-functor)
    ds
    (into (vec ds) (mapcat #(reader-copies kb %)) ds)))

(defn- note-supersession-moves!
  "Add `changed` to the moves `(reasoning/supersessions kb)` holds for the next settle
  (`take-supersession-moves!`), each with its entry in `held`, the map before the change,
  the first time it moves since the last `take-supersession-moves!`."
  [kb held changed]
  (when (seq changed)
    (some-> (reasoning/supersessions kb)
            (swap! (fn [a]
                     (-> (or a {})
                         (update ::moved (fnil into #{}) changed)
                         (update ::was (fn [w]
                                         (reduce (fn [w d] (if (contains? w d) w (assoc w d (get held d))))
                                                 (or w {}) changed)))))))))

(defn- supersession-map
  "The `datum -> displaced-terms` map of spellings the equality closure displaces,
  reconciled against the taxonomy (docs/equality.md, \"The reconcile in step 2 runs on
  the write path\").  Entries are only dropped or restated here; a spelling starts being
  displaced when migration hands it over in `extra`.  With a `region`, the walk examines
  `extra`, the entries `region` names and the entries naming a term of a class the
  partition moved (`tax/take-equality-moves!`); `region` nil is the full pass.  Returns
  `[map changed]` and records `changed` for the next settle (`note-supersession-moves!`)."
  [kb extra region]
  (let [tms   (reasoning/tms kb)
        held  (jtms/superseded tms)
        vis   (memoize #(res/visible-supporter-fn kb %))
        moved (tax/take-equality-moves! (reasoning/taxonomy kb) :supersessions)
        diff  (fn [m ds] (into #{} (filter #(not= (get held %) (get m %))) ds))
        [m changed]
        (if (some? region)
          (let [ds (with-copies kb (-> (mapv first extra)
                                       (into (filter #(contains? held %)) region)
                                       (into (comp (mapcat #(kb/find-sentexes kb %))
                                                   (map :id)
                                                   (filter #(contains? held %))
                                                   (distinct))
                                             moved)))
                m  (reduce (fn [m d] (if-let [e (displacement kb vis d)] (conj m e) (dissoc m d)))
                           (into held extra)
                           ds)]
            [m (diff m ds)])
          (let [m (into {} (keep #(displacement kb vis %)) (with-copies kb (keys (into held extra))))]
            [m (diff m (concat (keys held) (keys m)))]))]
    (note-supersession-moves! kb held changed)
    [m changed]))

(defn pending-supersession-moves
  "The datums whose supersession entry changed since the last `take-supersession-moves!`,
  read without emptying them."
  [kb]
  (some-> (reasoning/supersessions kb) deref ::moved))

(defn take-supersession-moves!
  "`{:moved #{datum} :was {datum entry}}`: the datums whose supersession entry changed
  since the last call, each with its entry before the first change (nil when it was not
  superseded), emptied; nil when the KB keeps no supersession moves.  `settle-finish`
  reads it once per settle: a supersession moves belief with no relabel, so
  `jtms/touched` does not name these."
  [kb]
  (when-let [a (reasoning/supersessions kb)]
    (let [{moved ::moved was ::was} @a]
      (reset! a {})
      {:moved (or moved #{}) :was (or was {})})))

(defn refresh-supersessions
  "Reconcile the superseded set with the equality closure (`supersession-map`), on the
  write path: where a migration hands over `extra` (the two-arity, which examines `extra`
  and the moved classes), where a sentence leaves the store
  (`reconcile-removed-supersession!`), and at `recover`, which passes nil for the full
  pass.  The settle calls it for a `genlCx` move that shows contexts (`reconcile-move`,
  from `drain-context-moves!`), for an `except` that moved and for an equality edge that
  moved in belief (`settle/settle-finish`)."
  ([kb] (refresh-supersessions kb nil))
  ([kb extra] (refresh-supersessions kb extra #{}))
  ([kb extra region]
   (jtms/supersede (reasoning/tms kb) (first (supersession-map kb extra region)))))

(defn restate-retired
  "Restate the derived row `sx` just stored (a mint `entail-arg-type` draws, or a
  correspondence derivation `chain/sync-values!` places) when its sentence names a term
  the equality closure already displaces, as `assert-one` restates an asserted fact
  (docs/equality.md, \"What a merge does\"): `sx` is superseded and its twin under the
  representative is stored (`migrate-sentex`).  `{:new [twin handles] :violations [v]}`,
  empty when nothing in the sentence merged."
  [kb sx]
  (if (kb/rewritable-sentex? kb sx)
    (let [mig (migrate-sentex kb sx)]
      (when (seq (:superseded mig))
        (refresh-supersessions kb (:superseded mig)))
      (select-keys mig [:new :violations]))
    empty-entailment-result))

(defn reconcile-removed-supersession!
  "The supersession reconcile `sentex` leaving the store owes, from the removal choke
  point: the full pass for a `genlCx` edge or a schematic rewrite rule while any spelling
  is superseded, and the narrowed one over `sentex` and the classes it moved for a
  superseded datum or an equality sentence.  A superseded datum leaving drops its entry,
  and an equality leaving gives back the spellings its class displaced."
  [kb sentex]
  (let [held (jtms/superseded (reasoning/tms kb))
        s    (sx/sentence-of sentex)]
    (cond
      (or (= 'genlCx (nm/functor s)) (rewrite/schematic-equation? s))
      (when (seq held) (refresh-supersessions kb nil nil))

      (or (contains? held (:id sentex)) (kb/equality-sentence? s))
      (refresh-supersessions kb nil #{(:id sentex)}))))

(defn derive-merge
  "Store the equality `sentence` in `context` as a derivation from `antes` under
  `informant`, and merge with it.  Returns the migration result.  The antecedents are
  ordered by content (`kb/antecedent-order`), so the list `why` prints does not depend on
  which fact arrived first."
  [kb sentence context informant antes]
  (let [antes      (kb/antecedent-order kb antes)
        [h s new?] (kb/find-or-create-sentex kb sentence context)
        depth      (inc (reduce max 0 (map #(jtms/depth (reasoning/tms kb) %) antes)))]
    (jtms/ensure-node (reasoning/tms kb) h depth)
    (when-not (jtms/has-justification? (reasoning/tms kb) informant antes h)
      (let [jid  (p/next-id (:records kb))
            just (jtms/->just jid informant antes h {} :monotonic)]
        (p/put-justification (:records kb) just)
        (jtms/add-justification (reasoning/tms kb) just)))
    (when new? (derived-sentex-added kb s h))
    (integrate-equality kb s h)))

(defn- derive-equality
  "`derive-merge` of `(equals x y)`, the arguments ordered by content, so the sentence
  key does not depend on which fact arrived first."
  [kb x y context informant antes]
  (let [[lo hi] (sort [x y])]
    (derive-merge kb (list 'equals lo hi) context informant antes)))

(defn- monotonic-pair?
  "Are both members `h` and `o` of a collision `:monotonic`?  Only such a pair of two
  symbols merges; any other is a nogood the settle places (docs/reference.md, decision 6)."
  [kb h o]
  (let [tms (reasoning/tms kb)]
    (and (tuple/monotonic-member? tms h) (tuple/monotonic-member? tms o))))

(defn- pair-antecedents
  "One antecedent list per declaring sentex in `decls`, for a merge drawn in `context` from
  the facts `handle` (of `pred`) and `oh` under the mark on `via`: the two facts, the
  declaration, the `genl` edges each fact's functor descends to reach `via`
  (`checks/edge-support`), and the `genlCx` edges `context` sees each fact and the
  declaration through (`checks/visibility-support`).  Deduplicated, since the two descents
  and the three sightings share every hop they have in common."
  [kb pred via handle oh context decls]
  (let [other  (some-> (p/get-sentex (:records kb) oh) :sentence nm/functor)
        shared (concat (checks/edge-support kb pred via context)
                       (when (and (symbol? other) (not= other pred))
                         (checks/edge-support kb other via context))
                       (checks/visibility-support kb handle context)
                       (checks/visibility-support kb oh context))]
    (map (fn [d]
           (into [handle oh d] (distinct)
                 (concat shared (checks/visibility-support kb d context))))
         decls)))

(defn- derive-functional-equalities-in
  "The functional merges `sentence`, stored as `handle`, forms in exactly `context`
  (docs/equality.md, \"`functional` infers equality instead of throwing\").  Each clash
  whose filler is a mergeable symbol, whose two members are `:monotonic`, and whose pair
  `context` does not already hold in one class (`res/same-class-in?`) derives
  `(equals V1 V2)`.  Returns `{:new :superseded :violations}`, or nil when nothing clashes.
  The equality takes one justification per declaration of the convicting mark `via`
  (`checks/functional-declaration-supporters`, docs/defenses.md, \"A functional merge
  rests on every declaration of the convicting mark\"), each naming both facts and the
  `genl` and `genlCx` edges they descended through (`pair-antecedents`)."
  [kb sentence context handle]
  (let [tax     (reasoning/taxonomy kb)
        recs    (:records kb)
        pred    (nm/functor sentence)
        ;; ordered by the whole clash's content, never the handle: two handles can fill
        ;; a slot with one value, and `oh` goes into the antecedents.  A `:default`
        ;; arrival reads no clash.
        clashes (when (tuple/monotonic-member? (reasoning/tms kb) handle)
                  (nm/sort-by-content-key
                   (fn [[oh v via n]] (let [s (p/get-sentex recs oh)]
                                        [v (:sentence s) (:context s) via n]))
                   (filter (fn [[oh v :as clash]]
                             (and (checks/mergeable-values? v (checks/functional-filler sentence clash))
                                  (monotonic-pair? kb handle oh)))
                           (checks/functional-clashes kb sentence context))))]
    (when (seq clashes)
      (reduce (fn [acc [oh v via n :as clash]]
                (let [b (checks/functional-filler sentence clash)]
                  ;; skip a pair only when a merge `context` can see already holds it
                  (if-not (and (checks/mergeable-values? v b)
                               (monotonic-pair? kb handle oh)
                               (not (res/same-class-in? kb v b context)))
                    acc
                    ;; every declaration constraining `via` at this position — the
                    ;; `(functional via)` sentexes at position 2 and the
                    ;; `(functionalInArg via n)` sentexes always, so a merge holding
                    ;; under both spellings survives retracting either.
                    (reduce (fn [acc a]
                              (merge-with into acc
                                          (derive-equality kb v b context 'functional a)))
                            acc
                            (pair-antecedents kb pred via handle oh context
                                              (sort (checks/functional-declaration-supporters
                                                     tax via n)))))))
              {:new [] :superseded [] :violations []}
              clashes))))

(defn- functional-mark-relevant?
  "Could the predicate `f`, or something it descends from, carry a `functional` or
  `functionalInArg` mark?  Two unscoped, over-approximating reads (`tax/props-over`,
  `tax/functional-in-arg-over`): the per-functor presence check
  `derive-functional-equalities` and `equate-under-edge` ask before a sweep."
  [tax f]
  (and (symbol? f)
       (or (seq (tax/props-over tax :functional f))
           (seq (tax/functional-in-arg-over tax f)))))

(defn- merge-readers
  "The readers a merge of `sentence`, stored in `context`, is derived at: `tax/context-down`
  of `context`, narrowed to `readers` when given, most general first (by ancestor-set size,
  then name).  A reader below one that placed the merge sees it and skips the pair, so the
  merge lands at the most general readers that see the pair in every arrival order.  At
  CxUniverse the readers are CxUniverse and every context storing a fact of a predicate
  under one above the functor: a partner's context sees the pair."
  [kb tax sentence context readers]
  (nm/sort-by-content-key (juxt #(count (tax/context-up tax %)) nm/print-key)
                          compare
                          (cond->> (if (tax/root-context? context)
                                     (into #{context}
                                           (comp (mapcat #(tax/specs-global tax %))
                                                 (mapcat #(first (reads/as-stored-contexts-with-functor-global
                                                                  (:index kb) %))))
                                           (tax/genls-global tax (nm/functor sentence)))
                                     (tax/context-down tax context))
                            readers (filter readers))))

(defn- derive-at-readers
  "The body `derive-functional-equalities` and `derive-antisymmetric-equalities` share:
  nil unless the family's KB-wide `declares?` holds; then `derive-in` run at every reader
  of `merge-readers` when `relevant?` admits the functor, else at `context` alone."
  [kb sentence context handle readers declares? relevant? derive-in]
  (let [tax (reasoning/taxonomy kb)]
    (when (declares? tax)
      (if (relevant? tax (nm/functor sentence))
        (reduce (fn [acc r]
                  (merge-with into acc (derive-in kb sentence r handle)))
                {:new [] :superseded [] :violations []}
                (merge-readers kb tax sentence context readers))
        (derive-in kb sentence context handle)))))

(defn derive-functional-equalities
  "`derive-functional-equalities-in` run from every reader at or below `context`
  (`merge-readers`).  `readers`, when given, narrows that set; only
  `equate-under-context-edge-via` passes it.  Two presence checks precede the reader
  sweep: `tax/functional-family-declared?` and `functional-mark-relevant?`."
  ([kb sentence context handle] (derive-functional-equalities kb sentence context handle nil))
  ([kb sentence context handle readers]
   (derive-at-readers kb sentence context handle readers
                      tax/functional-family-declared?
                      functional-mark-relevant?
                      derive-functional-equalities-in)))

(defn- functional-family-declaration
  "The predicate `sentence` marks when it is `(functional P)` or `(functionalInArg P n)`,
  else nil: the entry point of the declaration-arriving-last merge (`equate-existing`).
  The spellings come from `tax/functional-family-marks`; the arity is checked here.  The
  other merge directions are `derive-functional-equalities` (fact last),
  `equate-under-edge` (`genl` edge last) and `equate-under-context-edge` (`genlCx` edge
  last), and the family's nogoods are `vaelii.impl.decide`'s."
  [sentence]
  (when (case (tax/functional-family-marks (nm/functor sentence))
          :mark        (= 1 (nm/arity sentence))
          :mark-in-arg (= 2 (nm/arity sentence))
          false)
    (first (nm/args sentence))))

(defn- equate-declared-subtree
  "The body `equate-existing` and `antisym-equate-existing` share: every **stored** fact of
  `pred`'s spec subtree handed to the family's `derive` in its own context.  Stored rather
  than believed, so a merge drawn off a defeated fact revives with it.  nil when `pred` is
  not a symbol."
  [kb pred derive]
  (when (symbol? pred)
    (reduce (fn [acc sx]
              (merge-with into acc
                          (derive kb (:sentence sx) (:context sx) (:id sx))))
            {:new [] :superseded [] :violations []}
            (subtree-sentexes kb pred))))

(defn equate-existing
  "When a `(functional P)` or `(functionalInArg P n)` declaration arrives, derive the
  equalities the stored facts of `P`'s spec subtree license, each handed to
  `derive-functional-equalities` (docs/equality.md, \"Four directions\").  nil when
  `sentence` declares neither."
  [kb sentence]
  (when-let [pred (functional-family-declaration sentence)]
    (equate-declared-subtree kb pred derive-functional-equalities)))

(defn- derive-over-premises
  "Each premise among `sxs` (a fact, not a rule, not a negation) handed to the family's
  `derive` in its own context, as one `{:new :superseded :violations}`."
  [kb sxs derive]
  (reduce (fn [acc sx]
            (if-not (sx/positive-fact? sx)
              acc
              (merge-with into acc (derive kb (:sentence sx) (:context sx) (:id sx)))))
          {:new [] :superseded [] :violations []}
          sxs))

(defn- equate-under-edge-via
  "The body `equate-under-edge` and `antisym-equate-under-edge` share: a `(genl sub super)`
  edge arriving over stored facts hands every believed premise of `sub`'s spec subtree to
  the family's `derive` in its own context.  The subtree is read only when `declares?`
  (the KB-wide presence check) and `relevant?` (a mark at or above `super`) both hold, the
  two checks `revived-edge-sweep` asks."
  [kb sentence declares? relevant? derive]
  (when (and (= 'genl (nm/functor sentence)) (= 2 (nm/arity sentence)))
    (let [tax           (reasoning/taxonomy kb)
          [_ sub super] sentence]
      (when (and (symbol? sub) (declares? tax) (relevant? tax super))
        (derive-over-premises kb (subtree-sentexes kb sub) derive)))))

(defn equate-under-edge
  "When a `(genl sub super)` edge arrives, derive the equalities a `functional` or
  `functionalInArg` mark at or above `super` now licenses over the stored facts of `sub`'s
  spec subtree (`equate-under-edge-via`).  nil when `sentence` is not a `genl` edge, and
  no subtree read when no mark of the family stands over `super`."
  [kb sentence]
  (equate-under-edge-via kb sentence
                         tax/functional-family-declared?
                         functional-mark-relevant?
                         derive-functional-equalities))

(defn- derive-antisymmetric-equalities-in
  "The antisymmetric merges `sentence`, stored as `handle`, forms in exactly `context`:
  `(anti_symmetric P)` and a believed converse `(P b a)` of `(P a b)` derive `(equals a
  b)`, with one justification per declaration (`tax/prop-supporters`), each naming both
  facts, the `genl` edges either member descended through, and the `genlCx` edges
  `context` sees them through (`pair-antecedents`).  Both arguments must be
  mergeable symbols and both members `:monotonic`; a self tuple, or a pair `context`
  already holds in one class, is skipped.  Any other converse is a nogood
  (`vaelii.impl.decide`)."
  [kb sentence context handle]
  (let [tax (reasoning/taxonomy kb)]
    (when (seq (tax/props tax :anti-symmetric))
      (let [pred (nm/functor sentence)
            args (vec (nm/args sentence))]
        (when (= 2 (count args))
          (let [[a b] args]
            (when (checks/mergeable-values? a b)
              (let [recs      (:records kb)
                    ;; ordered by content, never by handle
                    converses (nm/sort-by-content-key
                               (fn [[h via]] (let [s (p/get-sentex recs h)]
                                               [(:sentence s) (:context s) via]))
                               (checks/antisymmetric-converses kb sentence context))]
                (reduce
                 (fn [acc [oh via]]
                   ;; a self tuple, or a pair a merge `context` sees already holds
                   (if (or (= oh handle) (not (monotonic-pair? kb handle oh))
                           (res/same-class-in? kb a b context))
                     acc
                     (reduce (fn [acc a-list]
                               (merge-with into acc
                                           (derive-equality kb a b context 'anti_symmetric a-list)))
                             acc
                             (pair-antecedents kb pred via handle oh context
                                               (sort (tax/prop-supporters tax :anti-symmetric via))))))
                 {:new [] :superseded [] :violations []}
                 converses)))))))))

(defn- anti-symmetric-mark-relevant?
  "The antisymmetric twin of `functional-mark-relevant?`: could the predicate `f`, or
  something it descends from, carry an `anti_symmetric` mark?  One unscoped
  `tax/props-over` read — no `functionalInArg` twin exists for this mark, so this is
  the whole of the check."
  [tax f]
  (and (symbol? f) (seq (tax/props-over tax :anti-symmetric f))))

(defn derive-antisymmetric-equalities
  "`derive-antisymmetric-equalities-in` run from every reader at or below `context`, with
  the presence checks and the `readers` narrowing `derive-functional-equalities` takes."
  ([kb sentence context handle] (derive-antisymmetric-equalities kb sentence context handle nil))
  ([kb sentence context handle readers]
   (derive-at-readers kb sentence context handle readers
                      #(seq (tax/props % :anti-symmetric))
                      anti-symmetric-mark-relevant?
                      derive-antisymmetric-equalities-in)))

(defn- note-and-derive-antisymmetric
  "`derive-antisymmetric-equalities`, after offering the stored fact `handle` to the
  converse candidates again (`decide/offer!`): a mark or a predicate edge arriving after
  its tuples makes converse pairs the candidate index did not read at their store.  The
  other families read no `anti_symmetric` mark, so the fact is not offered to them."
  [kb sentence context handle]
  (some->> (p/get-sentex (:records kb) handle) vector (#(decide/offer! kb % :converse)))
  (derive-antisymmetric-equalities kb sentence context handle))

(defn antisym-equate-existing
  "When an `(anti_symmetric P)` declaration arrives, hand every stored fact of `P`'s spec
  subtree to `derive-antisymmetric-equalities`, as `equate-existing` does for the
  functional family.  nil when `sentence` declares nothing antisymmetric."
  [kb sentence]
  (when (and (= 'anti_symmetric (nm/functor sentence)) (= 1 (nm/arity sentence)))
    (equate-declared-subtree kb (first (nm/args sentence)) note-and-derive-antisymmetric)))

(defn antisym-equate-under-edge
  "When a `(genl sub super)` edge arrives, derive the equalities an `(anti_symmetric …)`
  mark above `super` now licenses over the `(sub …)` facts already stored — the twin of
  `equate-under-edge`.  Free for an edge no `anti_symmetric` mark stands above, decided
  before the subtree is read.  nil when `sentence` is not a `genl` edge."
  [kb sentence]
  (equate-under-edge-via kb sentence
                         #(seq (tax/props % :anti-symmetric))
                         anti-symmetric-mark-relevant?
                         note-and-derive-antisymmetric))

(def ^:private offered-marks
  "The marks whose nogoods the settle places from a candidate index, each with the arity
  it is written at: their arrival offers the stored tuples beneath each predicate the
  mark names to `decide/offer!`."
  '{functional 1, functionalInArg 2, asymmetric 1, anti_transitive 1, negates 2})

(defn- offered-mark-over?
  "Does a mark of `offered-marks` stand on `p` or above it?  Five map reads for a KB
  declaring none.

  Read unscoped: the candidate rows `decide/offer!` keeps are a superset over every
  reader."
  [tax p]
  (boolean (or (seq (tax/props-over tax :functional p))
               (seq (tax/functional-in-arg-over tax p))
               (seq (tax/props-over tax :asymmetric p))
               (seq (tax/props-over tax :anti-transitive p))
               (seq (tax/negates-over tax p)))))

(defn offer-marked-existing
  "When a `functional`, `functionalInArg`, `asymmetric`, `anti_transitive` or `negates`
  mark arrives, offer every stored fact of the spec subtree of each predicate it names
  (the first argument, both of a `negates`) to `decide/offer!`, which reads the nogoods
  each forms under the mark.  nil."
  [kb sentence]
  (when (and (seq? sentence) (= (offered-marks (nm/functor sentence)) (nm/arity sentence)))
    (let [ps (if (= 'negates (nm/functor sentence)) (distinct (nm/args sentence)) [(first (nm/args sentence))])]
      (doseq [p ps :when (symbol? p)]
        (decide/offer! kb (subtree-sentexes kb p))))))

(defn offer-marked-under-edge
  "When a `(genl sub super)` edge arrives under an `offered-marks` mark on `super` or
  above it, offer the stored facts of `sub`'s spec subtree to `decide/offer!`.  nil, and
  free for a KB declaring none of the marks."
  [kb sentence]
  (when (and (seq? sentence) (= 'genl (nm/functor sentence)) (= 2 (nm/arity sentence)))
    (let [[_ sub super] sentence]
      (when (and (symbol? sub) (symbol? super)
                 (offered-mark-over? (reasoning/taxonomy kb) super))
        (decide/offer! kb (subtree-sentexes kb sub))))))

(def ^:private collision-informants
  "The informants a collision merge's justification carries (`derive-equality`)."
  '#{functional anti_symmetric})

(defn- collision-members
  "The antecedents of the collision justification `j` that are its colliding tuples: the
  ones with a term of the equality `j` concludes among their arguments.  The others are
  the declarations and the `genl` edges."
  [recs j]
  (let [terms (set (nm/args (:sentence (p/get-sentex recs (:consequence j)))))]
    (filterv #(when-let [s (:sentence (p/get-sentex recs %))]
                (and (not (contains? '#{functional functionalInArg anti_symmetric genl}
                                     (nm/functor s)))
                     (some terms (nm/args s))))
             (:antecedents j))))

(defn class-moved-merges
  "Re-ask the collision merges of the handles in `region` (a delay over `jtms/touched`)
  whose class can have moved: drop each collision justification whose members are all IN
  and one at `:default` (off when `drop?` is false), and re-derive from each member IN at
  `:monotonic` but a premise this settle created at that class.  `asked` is the settle's
  volatile set of `[handle class]` asked already.  `{:new :superseded :violations :removed
  :members}`, `:removed` the merged removals for the caller's stores and `:members` the
  dropped justifications' members; nil, with `region` unforced, when no merge mark is
  declared.  See docs/equality.md, \"`functional` infers equality instead of throwing\"."
  [kb region asked drop?]
  (let [tax (reasoning/taxonomy kb)]
    (when (or (tax/functional-family-declared? tax) (seq (tax/props tax :anti-symmetric)))
      (let [tms   (reasoning/tms kb)
            recs  (:records kb)
            born  (jtms/touched-new tms)
            fresh (fn [cls] (into [] (filter #(and (= cls (jtms/defeat-class tms %))
                                                   (not (contains? @asked [% cls]))))
                                  @region))
            down  (fresh :default)
            up    (into [] (remove #(and (contains? born %)
                                         (= :monotonic (jtms/premise-strength tms %))))
                        (fresh :monotonic))
            _     (vswap! asked into (concat (map #(vector % :default) down)
                                             (map #(vector % :monotonic) up)))
            stale (when drop?
                    (into (sorted-set)
                          (comp (mapcat #(jtms/dependents tms %))
                                (keep #(jtms/justification tms %))
                                (filter #(contains? collision-informants (:informant %)))
                                (keep (fn [j]
                                        (let [ms (collision-members recs j)]
                                          (when (and (every? #(jtms/defeat-class tms %) ms)
                                                     (not-every? #(tuple/monotonic-member? tms %) ms))
                                            [(:id j) ms])))))
                          down))
            removed (reduce (fn [acc [jid]]
                              (let [r (jtms/drop-justification! tms jid)]
                                (p/delete-justification! recs jid)
                                (merge-with into acc r)))
                            nil stale)
            sxs   (nm/sort-by-content-key (juxt :sentence :context)
                                          (into [] (comp (keep #(p/get-sentex recs %))
                                                         (filter #(nil? (:antecedent %))))
                                                up))
            mig   (reduce (fn [acc {:keys [sentence context id]}]
                            (merge-with into acc
                                        (derive-functional-equalities kb sentence context id)
                                        (derive-antisymmetric-equalities kb sentence context id)))
                          {:new [] :superseded [] :violations []}
                          sxs)]
        (assoc mig :removed removed :members (into [] (comp (mapcat second) (distinct)) stale))))))

(defn- collision-justifications
  "The justifications of the stored handle `h` whose informant is a collision mark's."
  [tms h]
  (filterv #(contains? collision-informants (:informant (jtms/justification tms %)))
           (jtms/supports tms h)))

(defn- covered-copies
  "The collision justifications of each merge `(equals a b)` supporting an edge of
  `term`'s equality class that the supporters stored above its context `c` cover: `a` and
  `b` are one class as `c` sees the merges (`res/same-class-in?`, the reader's own skip
  test), read over the supporters stored in a context that `c` sees and that does not see
  `c`."
  [kb tax term]
  (let [tms    (reasoning/tms kb)
        recs   (:records kb)
        sxs    (into {} (keep #(some->> (p/get-sentex recs %) (vector %))) (tax/class-supporters tax term))
        ctxs   (into #{} (keep :context) (vals sxs))
        above? (memoize (fn [c q] (and (tax/sees? tax c q) (not (tax/sees? tax q c)))))]
    (for [[h {[_ a b] :sentence c :context}] sxs
          :let  [jids (collision-justifications tms h)]
          :when (and (seq jids)
                     ;; no supporter of the class is stored above `c`, so none covers `h`
                     (some #(above? c %) ctxs)
                     (res/same-class-in? kb a b c #(some->> (:context (get sxs %)) (above? c))))
          jid   jids]
      jid)))

(defn- collision-merges-declared?
  "Does the KB declare a mark that merges a collision?"
  [tax]
  (or (tax/functional-family-declared? tax) (seq (tax/props tax :anti-symmetric))))

(defn covered-merges
  "The collision justifications, in id order, of every merge copy `covered-copies` finds
  in a class the equality partition moved since the last call (`tax/take-equality-moves!`
  as `:covers`, every merged term after a `recover`'s replay) or in the class of a merge
  of `moved` (`move-covered-merges`).  A reader that sees a pair in one class derives no
  merge of it, so a covered copy is one that an arrival order placing the more general
  merges first never stores (docs/equality.md, \"A merge copy that a more general merge
  covers is dropped\").  nil when no merge mark is declared; the moved terms are taken
  either way."
  [kb moved]
  (let [tax   (reasoning/taxonomy kb)
        terms (tax/take-equality-moves! tax :covers)]
    (when (collision-merges-declared? tax)
      (let [tms  (reasoning/tms kb)
            recs (:records kb)]
        (into (sorted-set)
              (comp (map #(tax/representative tax %))
                    (distinct)
                    (mapcat #(covered-copies kb tax %))
                    (filter #(jtms/justification tms %)))
              (concat terms (keep #(some-> (p/get-sentex recs %) :sentence second) moved)))))))

(defn- move-covered-merges
  "The collision merges stored in the contexts under the `genlCx` move `m` where a placement
  can lose its place to a more general one (`displaceable-contexts`), for `covered-merges`
  to ask.  Empty with no read when no merge mark is declared."
  [kb m]
  (when (collision-merges-declared? (reasoning/taxonomy kb))
    (let [idx (:index kb)
          tms (reasoning/tms kb)
          cs  (displaceable-contexts kb m)]
      (when (seq cs)
        (filterv #(seq (collision-justifications tms %))
                 (reads/as-stored-with-functor-in idx 'equals cs))))))

;; ---- a departing `genl` edge re-derives what descended through it ----------
;; The argument-type entailment and the equality a `functional` or `anti_symmetric` mark
;; on a super-predicate licenses name one route through `genl` edges
;; (`checks/edge-support`), so removing an edge on it deletes the justification even
;; where a second route survives.  The removal re-derives from the taxonomy it left, as
;; `resubsumption-seeds` does for a firing; a removed trigger membership is re-derived
;; over a surviving one.

(def ^:private edge-descended-informants
  "The informants other than a mint's of the derivations that cite the `genl` edges they
  descended through and the `genlCx` edges they see their ingredients through, mapped to
  how each is drawn again for the fact at the head of its antecedents.  A merge's
  restatement and a reader's copy (`migrate-into`) name the `genlCx` edges their reader
  sees the original through."
  '{functional     :functional
    anti_symmetric :anti-symmetric
    rewriteOf      :migration
    except         :migration})

(defn- edge-descended-kind
  "How the derivation a justification with `informant` concludes is drawn again: the kind
  `edge-descended-informants` names, `:entailment` for a mint (`kb/mint-informant?`), or nil."
  [kb informant]
  (or (get edge-descended-informants informant)
      (when (kb/mint-informant? kb informant) :entailment)))

(defn- past-the-pair?
  "Is `h` an antecedent of the entailment justification `j` other than its fact and its
  declaration, the first two (`entail-arg-type`): a route edge, a `genlCx` edge, a trigger
  membership or the trigger's route?"
  [kb j h]
  (and (= :entailment (edge-descended-kind kb (:informant j)))
       (boolean (some #{h} (drop 2 (:antecedents j))))))

(defn edge-descended-justifications
  "The justifications among `removed-jids` that a departing route edge (`route-functors`)
  or trigger membership invalidated while the fact and the declaration survive, as
  records: the derivations a teardown owes a re-derivation (`rederive-descended`).
  `gone` is the sentexes the sweep removed.  Read before the teardown deletes the
  records.  Runs only when `gone` holds a route edge, or a membership while a trigger
  declaration is stored.  An entailment qualifies when a removed antecedent is past its
  fact and declaration (`past-the-pair?`) and neither is removed; a descended equality
  or a restatement (`:migration`) when a removed route edge is its only removed
  antecedent (a removed equality counts as one)."
  [kb gone removed-jids]
  (let [edges (into #{} (comp (filter #(route-sentence? (:sentence %))) (map :id)) gone)
        links (into edges
                    (comp (filter #(let [s (:sentence %)] (and (seq? s) (kb/equality-sentence? s))))
                          (map :id))
                    gone)]
    (when (or (seq links)
              (and (some #(membership-shaped? (:sentence %)) gone)
                   (any-declaring? kb trigger-declarations)))
      (let [ids  (into #{} (map :id) gone)
            recs (:records kb)
            owed? (fn [j]
                    (let [antes (:antecedents j)
                          kind  (edge-descended-kind kb (:informant j))
                          route (if (= :migration kind) links edges)]
                      (if (= :entailment kind)
                        (and (not-any? ids (take 2 antes))
                             (boolean (some ids (drop 2 antes))))
                        (and (boolean (some route antes))
                             (not-any? #(and (contains? ids %) (not (contains? route %)))
                                       antes)))))]
        (into []
              (comp (keep #(p/get-justification recs %))
                    (filter #(edge-descended-kind kb (:informant %)))
                    (filter owed?))
              removed-jids)))))

(defn lost-descended-derivations
  "The edge-descended derivations among the dependents of `handles` whose conclusion is
  OUT, as justification records: `edge-descended-justifications` for an ingredient that
  lost belief rather than its record.  `edges-only?` keeps a dependent only where its
  handle is a route edge (`route-functors`), an entailment antecedent past the pair
  (`past-the-pair?`), or an equality a restatement rests on.  Only a justification whose
  conclusion is OUT, or withdrawn at its own context (`exc/believed-own?`), qualifies.
  The network filter runs before the record fetch."
  [kb handles edges-only?]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        lost (fn [h]
               (into []
                     (comp (keep #(jtms/justification tms %))
                           (filter #(edge-descended-kind kb (:informant %)))
                           ;; OUT, or withdrawn where it is stored
                           (remove #(exc/believed-own? kb (:consequence %))))
                     (jtms/dependents tms h)))]
    (into []
          (comp (map (juxt identity lost))
                (filter (comp seq second))
                (mapcat (fn [[h js]]
                          (let [s (:sentence (p/get-sentex recs h))]
                            (cond
                              (or (not edges-only?) (route-sentence? s)) js
                              ;; an equality is a link of the restatements resting on it
                              (and (seq? s) (kb/equality-sentence? s))
                              (filter #(= :migration (edge-descended-kind kb (:informant %))) js)
                              :else (filter #(past-the-pair? kb % h) js)))))
                (distinct))
          handles)))

(defn rederive-descended
  "Draw each of `justs` (`edge-descended-justifications`) again from the taxonomy as it
  now stands, and return the handles it created as chaining seeds.  Violations are
  reported and displaced spellings refreshed, as the arrival path does.  An entailment is
  asked through `retroactive-mints` narrowed to its declaration; a descended equality
  through `derive-functional-equalities` or `derive-antisymmetric-equalities` over the
  fact at the head of its antecedents (read off by functor); a restatement through
  `migrate-sentex` over its original or the target a restated meta names.  Each task is
  drawn once."
  [kb justs]
  (let [recs  (:records kb)
        facts (fn [antes]
                (filter (fn [h]
                          (when-let [s (:sentence (p/get-sentex recs h))]
                            (not (contains? '#{genl genlCx functional functionalInArg anti_symmetric}
                                            (nm/functor s)))))
                        antes))
        tasks (into []
                    (comp (mapcat (fn [j]
                                    (let [kind  (edge-descended-kind kb (:informant j))
                                          antes (:antecedents j)]
                                      (case kind
                                        :entailment [[kind (nth antes 0) (nth antes 1)]]
                                        :migration  [[kind (first antes) nil]]
                                        (map (fn [src] [kind src nil]) (facts antes))))))
                          (distinct))
                    justs)
        res   (reduce
               (fn [acc [kind src dh]]
                 (if-let [sx (p/get-sentex recs src)]
                   (merge-with into acc
                               (case kind
                                 :entailment     (retroactive-mints kb sx dh)
                                 :functional     (derive-functional-equalities
                                                  kb (:sentence sx) (:context sx) src)
                                 :anti-symmetric (derive-antisymmetric-equalities
                                                  kb (:sentence sx) (:context sx) src)
                                 ;; a meta's restatement is drawn by restating its target
                                 :migration      (let [t   (meta-target kb (:sentence sx))
                                                       tsx (if t (p/get-sentex recs t) sx)]
                                                   (if (and tsx (kb/rewritable-sentex? kb tsx))
                                                     (migrate-sentex kb tsx)
                                                     {}))))
                   acc))
               {:new [] :superseded [] :violations []}
               tasks)]
    (when (seq (:superseded res))
      (refresh-supersessions kb (:superseded res)))
    (violations/report kb (:violations res))
    (minted-seeds kb (:new res))))

;; ---- the decontextualized predicate ---------------------------------------
;; `(decontextualized_predicate P)` deduces a copy of every `(P ...)` into CxUniverse,
;; justified by the original and the declaration
;; (docs/contexts.md#decontextualized_predicate-a-fact-that-belongs-to-the-kb-not-to-one-theory).

(def universal-context sx/root-context)

(defn storage-context
  "The context a fact whose functor is `pred` is stored in when written in `context`:
  CxUniverse for a `forced_decontextualized_predicate`, `context` otherwise.  The mark is
  read KB-wide: a storage context decides what the store holds, which every reader
  shares, so no reader's view may move it.  `assert-entry/storage-context` stores with
  it, and `unary-entailments` places a declaration's arity-class memberships with it."
  [kb pred context]
  (if (and pred (tax/has-prop? (reasoning/taxonomy kb) :forced-decontextualized pred))
    universal-context
    context))

(defn- copy-merges
  "The equalities a lifted copy at `h` licenses as content new to CxUniverse, as `{:new
  :superseded :violations}`: the copy meeting a `functional` or `anti_symmetric` mark
  above its predicate, and the copy *being* one and meeting that predicate's stored
  facts.  The assert entry point and `chain/place-fact-conclusion` run the same four for
  what they store, and a copy is stored by neither.  Each arm runs only on its own functor."
  [kb sentence h]
  (merge-with into {:new [] :superseded [] :violations []}
              (derive-functional-equalities kb sentence universal-context h)
              (equate-existing kb sentence)
              (derive-antisymmetric-equalities kb sentence universal-context h)
              (antisym-equate-existing kb sentence)))

(defn- deduce-lift
  "Deduce `sentence` (stored at `src-handle` in `src-context`) into CxUniverse, justified
  by `src-handle` and each of `witnesses` in turn, a vector of the further antecedents one
  justification rests on.  A declared lift passes one `[declaration]` per declaring
  sentex; a permuting mark's passes `[[]]` (`deduce-lifts`).  The copy is not checked:
  `src-context` sees CxUniverse, so the checks at the source assert read its constraints.
  Returns `{:new [handle …] :violations [v]}`: the copy's handle when newly created, with
  the twins its merges wrote (`copy-merges`), and their violations."
  [kb sentence src-handle src-context witnesses]
  (if (or (empty? witnesses) (= src-context universal-context))
    empty-entailment-result
    (let [[h2 s2 new?] (kb/find-or-create-sentex kb sentence universal-context)]
      (if (= h2 src-handle)
        empty-entailment-result
        (do
          ;; the copy is a derived sentex in a context that did not have it: it
          ;; reaches the closures and posts its exception re-check trigger exactly as
          ;; a rule conclusion does
          (when new? (derived-sentex-added kb s2 h2))
          (doseq [w witnesses]
            (let [antes (into [src-handle] w)
                  depth (inc (reduce max (map #(jtms/depth (reasoning/tms kb) %) antes)))]
              (jtms/ensure-node (reasoning/tms kb) h2 depth)
              (when-not (jtms/has-justification? (reasoning/tms kb) 'decontextualized_predicate antes h2)
                (let [jid  (p/next-id (:records kb))
                      ;; The lift adds no defeasibility of its own, so it confers
                      ;; :monotonic and `conferred-class` caps it at the weakest of its
                      ;; antecedents.
                      just (jtms/->just jid 'decontextualized_predicate antes h2 {} :monotonic)]
                  (p/put-justification (:records kb) just)
                  (jtms/add-justification (reasoning/tms kb) just)))))
          ;; ...and the merges the copy owes as content new to CxUniverse, after the
          ;; justifications because a merge takes only the supporters it believes,
          ;; and the argument-type derivations it draws there, as a fact stated in
          ;; CxUniverse draws them
          (let [mig  (when new? (copy-merges kb sentence h2))
                args (when new? (deduce-placed kb sentence h2 universal-context))]
            (when (seq (:superseded mig))
              (refresh-supersessions kb (:superseded mig)))
            {:new        (-> (if new? [h2] []) (into (:new mig)) (into (:new args)))
             :violations (-> [] (into (:violations mig)) (into (:violations args)))}))))))

(defn lifts-to-universe?
  "Does `deduce-lifts` deduce a sentence on `pred` into CxUniverse: is `pred` a permuting
  mark (`inherit/permuting-marks`), or a predicate the KB declares decontextualized?  The
  declaration is read unscoped: a decontextualized predicate's facts belong to the KB, not
  to the context that declares it."
  [kb pred]
  (or (inherit/permuting-mark? pred)
      (and (some? pred) (tax/has-prop? (reasoning/taxonomy kb) :decontextualized pred))))

(defn deduce-lifts
  "Deduce `sentence` (stored at `handle` in `context`) into CxUniverse when
  `lifts-to-universe?` holds of its predicate — `{:new [handles] :violations [v]}`, nil
  otherwise.  Called by `assert` and by forward chaining's `place-conclusion`.  A
  permuting mark is lifted on its statement alone, whatever the KB declares; any other
  is lifted once per declaring sentex
  (docs/contexts.md#decontextualized_predicate-a-fact-that-belongs-to-the-kb-not-to-one-theory)."
  [kb sentence handle context]
  (let [pred (nm/functor sentence)]
    (when (lifts-to-universe? kb pred)
      (deduce-lift kb sentence handle context
                   (if (inherit/permuting-mark? pred)
                     [[]]
                     (map vector (tax/prop-supporters (reasoning/taxonomy kb)
                                                      :decontextualized pred)))))))
(defn- unary-entailments
  "The `unary_predicate` memberships the declaration `sentence` stored at `dh` entails of
  the types it mints in, each justified by the declaration alone: a declared type no
  arity statement binds to another length is a unary predicate (`arity/mintable-type?`).
  Each is stored where `assert` stores the membership stated in the declaration's
  context (`storage-context`), CxUniverse in the shipped KB, so the declarations naming
  a type justify one record.  Never withheld as a subsumed mint is, since a type's arity
  holds at every context (`arity/relation-length`).  `thing` is left out."
  [kb sentence dh]
  (let [ctx (storage-context kb 'unary_predicate (:context (p/get-sentex (:records kb) dh)))]
    (reduce (fn [acc t]
              (merge-with into acc
                          (entail-arg-type kb {:assert (list 'unary_predicate t) :because []
                                               :kind declared-type-informant :class true}
                                           dh ctx false)))
            empty-entailment-result
            (distinct (remove #{'thing} (declared-types sentence))))))

(defn declared-types-rehomed
  "The `declaredType` memberships stored where `unary-entailments` no longer places them,
  drawn again where it does: `{:new [handle …] :violations [v …] :dropped [jid …]}`, the
  records the draw created, and the justifications of the `(unary_predicate T)` records
  stored outside `storage-context` that the caller drops.  The draw runs first, so the
  record at the new home holds the declaration before the old justification goes.
  Empty unless `pred` is `unary_predicate`: a `(forced_decontextualized_predicate
  unary_predicate)` arriving after a declaration below CxUniverse minted there leaves
  the KB the other order builds (`core/rehome-forced-extent!`)."
  [kb pred]
  (if-not (= 'unary_predicate pred)
    (assoc empty-entailment-result :dropped [])
    (let [tms   (reasoning/tms kb)
          recs  (:records kb)
          stale (for [h (sort (reads/as-stored-with-functor (:index kb) 'unary_predicate))
                      :let [sx (p/get-sentex recs h)]
                      :when (and sx (not= (:context sx) (storage-context kb pred (:context sx))))
                      jid (sort (jtms/supports tms h))
                      :let [j (jtms/justification tms jid)]
                      :when (= declared-type-informant (:informant j))]
                  [jid (first (:antecedents j))])
          drawn (reduce (fn [acc dh]
                          (if-let [d (p/get-sentex recs dh)]
                            (merge-with into acc (unary-entailments kb (:sentence d) dh))
                            acc))
                        empty-entailment-result
                        (distinct (map second stale)))]
      (assoc drawn :dropped (mapv first stale)))))

(defn entail-existing
  "When an `(arg P n T)` / `(genlArg P n T)` / `(interArg P n T m U)` declaration
  arrives, draw what it now says about the `(P …)` sentexes already stored.  Same
  `{:new :violations}` result; nil when `sentence` is not an argument constraint.  Sweeps
  what is stored, not believed, over `P`'s whole spec subtree (`subtree-sentexes`,
  snapshotted before the first mint); `(resultArg F n)` reads the `natFormula` facts of
  `F`'s applications (`result-arg-extent`) and an `interArgEqual` the tuples holding its
  value at its trigger position (`trigger-extent`).  A declaration whose type is not
  mintable (`arity/mintable-type?`) or whose every type is `thing` reads no extent;
  `mints-on-lengths` runs it later.  An inert sentex or computed `genlCx` edge draws
  nothing (`retroactive-mints`).  A declaration that mints entails its types'
  `unary_predicate` memberships (`unary-entailments`).  `triggered-mints` reaches a trigger
  arriving last.  See docs/argtypes.md."
  [kb sentence dh]
  (when argument/*assertive-arg-types?*
    (let [[f pred] sentence
          ra?      (and (= 'resultArg f) (= 2 (nm/arity sentence)))
          types    (declared-types sentence)]
      (when (and (or ra? (= (entailing-declarations f) (nm/arity sentence))) (symbol? pred))
        (if (or (seq (waiting-types kb sentence))
                (and (seq types) (every? #{'thing} types)))
          empty-entailment-result
          (let [placements (placements-of kb dh)]
            (merge-with into
                        (unary-entailments kb sentence dh)
                        (with-recheck-reads
                          (reduce (fn [acc sx]
                                    (merge-with into acc (retroactive-mints kb sx dh placements)))
                                  empty-entailment-result
                                  (cond ra?                  (result-arg-extent kb pred)
                                        (= 'interArgEqual f) (trigger-extent kb pred (nth sentence 2) (nth sentence 3))
                                        :else                (subtree-sentexes kb pred)))))))))))

(defn mints-on-lengths
  "The mints the stored content naming a type of `bound` owes now that the type's own
  length admits one (`arity/mintable-type?`), as one `{:new :violations}`.  `bound` maps
  each relation whose arity bindings moved to those bindings' `#{[kind value]}`
  (`arity/drain!`'s `:bound`).  Per mintable type `t`, in content order: each stored
  entailing declaration naming `t` with no `declaredType` justification of
  `(unary_predicate t)` (`declared-type-justifications`) runs `entail-existing`; each stored
  fact naming `t` where an `argArg` names its type, and each `natFormula` fact naming `t`
  under a `resultArg` function, draws through `deduce-placed`.  The `argArg` predicates are
  read KB-wide.  An inert declaration sweeps nothing."
  [kb bound]
  (let [ts     (when argument/*assertive-arg-types?*
                 (into [] (comp (keep (fn [[t kvs]] (when (some binds-another-length? kvs) t)))
                                (filter #(arity/mintable-type? kb %)))
                       (sort-by (comp nm/print-key key) (filter (comp symbol? key) bound))))]
    (if (empty? ts)
      empty-entailment-result
      (let [idx   (:index kb)
            recs  (:records kb)
            tax   (reasoning/taxonomy kb)
            kinds (sort-by nm/print-key (remove #{'argArg} (keys entailing-declarations)))
            sx-of #(p/get-sentex recs %)
            ;; the argument positions an `argArg` names a fact's type at, and the
            ;; functions a `resultArg` types the results of
            aa-at (into (sorted-set)
                        (keep #(when-let [d (:sentence (sx-of %))]
                                 (when (and (= 3 (nm/arity d)) (pos-int? (nth d 3))) (nth d 3))))
                        (reads/as-stored-with-functor idx 'argArg))
            ra-fs (into #{} (keep #(when-let [d (:sentence (sx-of %))]
                                     (when (= 2 (nm/arity d)) (second d))))
                        (reads/as-stored-with-functor idx 'resultArg))
            aa?   #(seq (tax/props-over tax (tax/arg-declaration-props 'argArg) %))
            ra?   (fn [t sx]
                    (let [s (:sentence sx) e (nth s 2 nil)]
                      (and (= 'natFormula (nm/functor s)) (sequential? e)
                           (contains? ra-fs (first e)) (some #{t} (rest e)))))]
        (reduce
         (fn [acc t]
           (let [swept (into #{} (map second) (declared-type-justifications kb t))
                 decls (into []
                             (for [f kinds
                                   :let [n (entailing-declarations f)]
                                   h (sort (reads/as-stored-with-args idx f {n t}))
                                   :when (and (not (swept h)) (not (inert-handle? kb h)))
                                   :let [d (sx-of h)]
                                   :when (and d (= n (nm/arity (:sentence d))))]
                               d))
                 facts (into (sorted-set)
                             cat
                             [(for [m aa-at
                                    q (sort-by nm/print-key (reads/as-stored-predicates-at-arg idx m t))
                                    :when (aa? q)
                                    h (reads/as-stored-with-args idx q {m t})]
                                h)
                              (when (seq ra-fs)
                                (filter #(some->> (sx-of %) (ra? t)) (reads/as-stored-with-term idx t)))])]
             (as-> acc acc
               (reduce (fn [acc d]
                         (merge-with into acc (or (entail-existing kb (:sentence d) (:id d))
                                                  empty-entailment-result)))
                       acc decls)
               (reduce (fn [acc h]
                         (if-let [sx (sx-of h)]
                           (merge-with into acc (deduce-placed kb (:sentence sx) h (:context sx)))
                           acc))
                       acc facts))))
         empty-entailment-result
         ts)))))

(defn- lift-statements
  "Deduce every stored `(pred ...)` sentex outside CxUniverse into it on `witnesses`
  (`deduce-lift`), as one `{:new :violations}`.  The extent is snapshotted before the
  first copy is made, since each copy posts to the term-index entry being walked."
  [kb pred witnesses]
  (reduce (fn [acc s]
            (if-not (and (= pred (nm/functor (:sentence s)))
                         (not= universal-context (:context s)))
              acc
              (merge-with into acc (deduce-lift kb (:sentence s) (:id s)
                                                (:context s) witnesses))))
          empty-entailment-result
          (vec (kb/find-sentexes kb pred))))

(defn- lift-existing
  "Deduce every stored `(pred ...)` sentex outside CxUniverse into it on the declaration
  at `dh`, believed or not, as `{:new :violations}`; the copies are chaining seeds.  A
  permuting mark returns the empty result, its statements being lifted as they arrive."
  [kb pred dh]
  (if (inherit/permuting-mark? pred)
    empty-entailment-result
    (lift-statements kb pred [[dh]])))

(defn- revived-edge-sweep
  "The merges and candidate offers a revived `(genl sub super)` edge owes the facts of
  `sub`'s spec subtree: `equate-under-edge`, `antisym-equate-under-edge` and
  `offer-marked-under-edge` over one walk, bounded at `tax/*exposure-instance-budget*`
  sentexes.  nil when `sentence` is not a `genl` edge or no merge mark and no
  `offered-marks` mark stands at or above `super`.  A cut files one
  `:genl-edge-revival-truncated` entry naming the edge.  `context` is the edge's."
  [kb sentence context]
  (when (and (= 'genl (nm/functor sentence)) (= 2 (nm/arity sentence)))
    (let [tax           (reasoning/taxonomy kb)
          [_ sub super] sentence
          fun?  (and (tax/functional-family-declared? tax)
                     (functional-mark-relevant? tax super))
          anti? (and (seq (tax/props tax :anti-symmetric))
                     (anti-symmetric-mark-relevant? tax super))
          offer? (and (symbol? super) (offered-mark-over? tax super))]
      (when (and (symbol? sub) (or fun? anti? offer?))
        (let [budget (max 0 (long tax/*exposure-instance-budget*))
              walked (subtree-sentexes kb sub (inc budget))
              cut?   (> (count walked) budget)
              sxs    (cond-> walked cut? (subvec 0 budget))]
          (cond offer? (decide/offer! kb sxs)
                anti?  (decide/offer! kb sxs :converse))
          (cond-> (merge-with into
                              (when fun? (derive-over-premises kb sxs derive-functional-equalities))
                              (when anti? (derive-over-premises kb sxs derive-antisymmetric-equalities)))
            cut? (update :violations (fnil conj [])
                         {:violation :genl-edge-revival-truncated
                          :detail    {:edge    sentence
                                      :context context
                                      :budget  budget
                                      :message (str "revived " (pr-str sentence) " in " context
                                                    " bounded its merge sweep over the "
                                                    sub " subtree at " budget
                                                    " facts; facts past the cut that arrived"
                                                    " while the edge was OUT stay unmerged")}})))))))

(defn revived-declaration-sweeps
  "Run, for each sentex in `handles` the settle just brought back OUT to IN, the sweeps
  its arrival runs over the facts already stored: `equate-existing` and
  `antisym-equate-existing` for a merge mark, `revived-edge-sweep` for a `genl` edge under
  one, `lift-existing` for a `decontextualized_predicate` (docs/equality.md, \"A mark that
  revives runs its arrival sweep again\").  Returns one `{:new :superseded :violations}`, or
  nil when the KB declares no merge, nogood-candidate or lift mark.  The sweeps read
  stored content and are idempotent; handles are walked in content order."
  [kb handles]
  (let [tax (reasoning/taxonomy kb)]
    (when (and (seq handles)
               (or (tax/functional-family-declared? tax)
                   (seq (tax/props tax :anti-symmetric))
                   (seq (tax/props tax :asymmetric))
                   (seq (tax/props tax :anti-transitive))
                   (tax/negates? tax)
                   (seq (tax/props tax :decontextualized))))
      (let [sxs (sort-by (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                         (keep #(p/get-sentex (:records kb) %) handles))]
        (reduce (fn [acc {:keys [sentence context id]}]
                  (offer-marked-existing kb sentence)
                  (merge-with into acc
                              (equate-existing kb sentence)
                              (antisym-equate-existing kb sentence)
                              (revived-edge-sweep kb sentence context)
                              (when (and (= 'decontextualized_predicate (nm/functor sentence))
                                         (= 1 (nm/arity sentence))
                                         (symbol? (second sentence)))
                                (lift-existing kb (second sentence) id))))
                {:new [] :superseded [] :violations []}
                sxs)))))

(defn- equality-arrival-sweep
  "The migration an equality sentex's arrival runs, run again over what is stored now:
  `migrate-matching` over a schematic equation's LHS head, `migrate-class` over a ground
  merge's class.  nil for a NAT `rewriteOf`-to-compound, which restates nothing."
  [kb sentence]
  (let [[_ a b] sentence]
    (cond
      (rewrite/schematic-equation? sentence)
      (migrate-matching kb (first (first (rewrite/orient a b))))

      (and (symbol? a) (symbol? b))
      (let [tx (reasoning/taxonomy kb)]
        (migrate-class kb (into (set (tax/equiv-class tx a)) (tax/equiv-class tx b)))))))

(defn believed-again-sweeps
  "Run, for each symbol-merge supporter in `handles` that is stored and believed, what
  its arrival runs over the stored facts: the re-check of the merged class
  (`recheck-equality-edge`) and the migration (`equality-arrival-sweep`).  Returns one
  `{:new :superseded :violations}`.  `handles` is `tax/take-believed-again!`'s answer: a
  supporter whose firing was held void met its arrival with nothing to restate, and a
  relabel brings it IN with no arrival.  Walked in content order, and scoped to each
  supporter's class."
  [kb handles]
  (let [tms (reasoning/tms kb)
        sxs (sort-by (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                     (keep #(when (jtms/in? tms %) (p/get-sentex (:records kb) %)) handles))]
    (reduce (fn [acc {:keys [sentence]}]
              (let [[_ a b] sentence
                    tx      (reasoning/taxonomy kb)]
                (recheck-equality-edge kb (into (set (tax/equiv-class tx a)) (tax/equiv-class tx b)))
                (merge-with into acc (equality-arrival-sweep kb sentence))))
            {:new [] :superseded [] :violations []}
            sxs)))

(defn- except-moved-records
  "The records whose visibility an `except` of one of `sxs` moved: `sxs`, and for each
  record that is itself an `except` the record it names, since the cascade moves that
  one's visibility too.  In content order."
  [kb sxs]
  (let [recs (:records kb)]
    (loop [seen #{} out [] todo (vec sxs)]
      (if-let [sx (peek todo)]
        (let [todo (pop todo)]
          (if (contains? seen (:id sx))
            (recur seen out todo)
            (let [inner (some->> (:sentence sx) kb/except-target (p/get-sentex recs))]
              (recur (conj seen (:id sx)) (conj out sx) (cond-> todo inner (conj inner))))))
        (sort-by (juxt (comp nm/print-key :sentence) (comp nm/print-key :context)) out)))))

(defn- drop-hidden-mints!
  "Drop each argument-type derivation resting on a record of `sxs`, stored in a context
  `in?` accepts, that an `except` now hides from that context (`exc/except-hidden-fn`),
  as `entail-arg-type` stores none when the `except` arrived first, or that is no longer
  stored at a placement of its fact and declaration (`pair-placements`): an `except`
  leaving can place the pair above a placement it had descended to.  Returns the merged
  `jtms/drop-justification!` results for the caller to apply; the dropped records are
  deleted here."
  [kb sxs in?]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (reduce (fn [acc jid]
              (let [j (jtms/justification tms jid)]
                (if (and j (kb/mint-informant? kb (:informant j))
                         (when-let [c (p/get-sentex recs (:consequence j))]
                           (when (in? (:context c))
                             (or (when-let [hidden? (exc/except-hidden-fn kb (:context c))]
                                   (some hidden? (:antecedents j)))
                                 (let [[f d] (:antecedents j)]
                                   (not-any? #{(:context c)} (placements-of-pair kb f d)))))))
                  (let [r (jtms/drop-justification! tms jid)]
                    (p/delete-justification! recs jid)
                    (merge-with into acc r))
                  acc)))
            nil
            (into (sorted-set) (mapcat #(jtms/dependents tms (:id %))) sxs))))

(defn- revealed-entailments
  "The argument-type entailments the believed records of `sxs` owe the facts already
  stored, drawn as each record's arrival draws them: `entail-existing` for an entailing
  declaration, `entail-over` for a literal fact, and `trigger-entailments` for a trigger
  membership or edge.  Every draw reads the `except` hidden filter, so a record an
  `except` now hides draws nothing, and one it stopped hiding draws what a KB that never
  had the `except` holds.  Returns `{:new [handle …] :violations [v …]}`, the new handles
  as chaining seeds (`minted-seeds`)."
  [kb sxs]
  (let [tms (reasoning/tms kb)
        ins (filter #(jtms/in? tms (:id %)) sxs)
        r   (merge-with into
                        (reduce (fn [acc {:keys [sentence id]}]
                                  (merge-with into acc (entail-existing kb sentence id)))
                                empty-entailment-result
                                ins)
                        (entail-over kb ins)
                        (when (any-declaring? kb trigger-declarations)
                          (trigger-entailments kb (filter trigger-shaped? ins))))]
    (update r :new #(minted-seeds kb %))))

(defn except-move-sweeps
  "Run, for each handle in `handles` whose visibility an `except` moved, the sweep its
  arrival runs over the facts already stored: the equality migration for an equality
  sentex (`equality-arrival-sweep`) and `revived-declaration-sweeps`' for a merge or lift
  mark (docs/equational.md, \"An except of an equation\").  Returns one `{:new :superseded
  :violations :removed}`, or nil when `handles` is empty.  With `sweep?`, the
  argument-type derivations resting on a record an `except` now hides are dropped
  (`drop-hidden-mints!`, `:removed` for the caller to apply) and the records it stopped
  hiding draw again (docs/argtypes.md, \"An except of an ingredient\"): for a handle in
  `whole`, every context and the record's own arrival sweep (`revealed-entailments`); for
  one only in `scoped`, `{handle #{[sub super]}}`, the contexts under each `sub`
  (`entail-under-context-edge`)."
  [kb handles sweep? whole scoped]
  (when (seq handles)
    (let [sxs   (sort-by (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                         (keep #(p/get-sentex (:records kb) %) handles))
          on?   (and argument/*assertive-arg-types?* (any-declaring? kb))
          mints (when on? (except-moved-records kb (filter #(contains? whole (:id %)) sxs)))
          edges (when on?
                  (->> scoped
                       (remove #(contains? whole (key %)))
                       (into #{} (mapcat val))
                       (sort-by #(mapv nm/name-key %))))
          moved (when (seq edges)
                  (except-moved-records kb (remove #(contains? whole (:id %)) sxs)))
          tx    (reasoning/taxonomy kb)
          under (fn [c] (some (fn [[sub _]] (or (= c sub) (tax/sees? tx c sub))) edges))
          gone  (when sweep?
                  (merge-with into
                              (when (seq mints) (drop-hidden-mints! kb mints (constantly true)))
                              (when (seq moved) (drop-hidden-mints! kb moved under))))
          ;; the except moved what the readers under `sub` see, not the edge, so the
          ;; sweep reads the whole move rather than its gain (`move-groups`)
          drawn (reduce (fn [acc [sub super]]
                          (merge-with into acc
                                      (binding [checks/*whole-move-sweeps?* true]
                                        (entail-under-context-edge kb (context-move kb sub super)))))
                        (if (seq mints) (revealed-entailments kb mints) empty-entailment-result)
                        edges)]
      (reduce (fn [acc {:keys [sentence id]}]
                (merge-with into acc
                            (cond
                              (kb/equality-sentence? sentence)
                              (equality-arrival-sweep kb sentence)
                              :else
                              (revived-declaration-sweeps kb [id]))))
              (assoc drawn :superseded [] :removed gone)
              sxs))))

(defn- except-move-terms
  "The terms whose occurrences an `except` of one of `targets` can re-spell: for every
  equality sentex in the targets' forward consequence closure, a ground merge's class and
  a schematic equation's LHS head — `migrate-class`'s and `migrate-matching`'s candidate
  keys.  The closure is walked because an equality can rest on the excepted handle (a
  merge a `functional` mark derived), and a reader that cannot see the handle cannot see
  what rests only on it.  A target that is itself an `except` adds its own target, since
  the meta-exception cascade moves that one's visibility."
  [kb targets]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        tx   (reasoning/taxonomy kb)
        seen (graph/reach-all (vec targets)
                              (fn [d]
                                (let [meta (some-> (p/get-sentex recs d) :sentence kb/except-target)]
                                  (cond-> (into [] (comp (keep #(jtms/justification tms %))
                                                         (map :consequence))
                                                (jtms/dependents tms d))
                                    meta (conj meta)))))]
    (into #{}
          (comp (keep #(p/get-sentex recs %))
                (map :sentence)
                (mapcat (fn [[_ a b :as s]]
                          (cond
                            (not (kb/equality-sentence? s))    nil
                            (rewrite/schematic-equation? s) [(first (first (rewrite/orient a b)))]
                            (and (symbol? a) (symbol? b))   (into (set (tax/equiv-class tx a))
                                                                  (tax/equiv-class tx b))))))
          seen)))

(defn except-move-region
  "The superseded data whose supersession an `except` that moved can change: the ones
  naming a term an equality in the excepted handles' reach re-spells
  (`except-move-terms`), stored in a context that sees one of the contexts the moving
  `except`s are stated in.  `pending` is `{target #{except-context}}`."
  [kb pending]
  (let [held (jtms/superseded (reasoning/tms kb))]
    (if (or (empty? held) (empty? pending))
      #{}
      (let [tx   (reasoning/taxonomy kb)
            ctxs (into #{} cat (vals pending))]
        (into #{}
              (comp (mapcat #(kb/find-sentexes kb %))
                    (filter #(contains? held (:id %)))
                    (filter (fn [sx] (some #(tax/sees? tx (:context sx) %) ctxs)))
                    (map :id))
              (except-move-terms kb (keys pending)))))))

(defn except-moved
  "The handles an `except` of which arrived, left or flipped since the last
  `drain-except-moves!`, read without emptying the queue (`note-except-move!`)."
  [kb]
  (keys (:pending @(reasoning/except-moves kb))))

(defn take-except-moves!
  "Empty `:except-moves` and return what the settle owes it:
  `{:extra [[datum reason]] :region #{datum} :full? bool :moved #{h}}` — the
  supersessions `except-move-sweeps` found, the superseded data an `except` that moved
  can change (`except-move-region`), whether a move is still pending undrained, which
  leaves the supersession reconcile nothing narrower than a full pass, and the handles
  the drained moves hid or showed.  nil when nothing moved."
  [kb]
  (let [a (reasoning/except-moves kb)
        m @a]
    (when (or (seq (:pending m)) (seq (:extra m)) (seq (:region m)) (seq (:moved m)))
      (reset! a {})
      {:extra (:extra m) :region (:region m) :moved (:moved m)
       :full? (boolean (seq (:pending m)))})))

(defn drain-except-moves!
  "Take the pending handles off `:except-moves`, sweep them (`except-move-sweeps`, with
  `sweep?`), and keep the handles, the supersessions the sweeps found and the region the
  moves can change (`except-move-region`) for `take-except-moves!`.  Returns the sweeps' result,
  its `:new` joined by the believed facts of the targets' consequence closure and of the
  antecedents resting on it, and by the believed rules of that closure, to chain from, or
  nil when nothing was pending."
  [kb sweep?]
  (let [a                               (reasoning/except-moves kb)
        {:keys [pending whole scoped]} @a]
    (when (seq pending)
      (swap! a dissoc :pending :whole :scoped)
      (let [mig (or (except-move-sweeps kb (keys pending) sweep? (set whole) scoped)
                    {:new [] :superseded [] :violations []})
            reg (except-move-region kb pending)
            tms (reasoning/tms kb)
            ;; the firings the except refused or swept, re-joined from the moved targets'
            ;; consequence closure and the antecedents of the justifications resting on
            ;; it, so a firing a second route carries is placed again; that bounds the join
            cl  (jtms/consequence-closure tms (keys pending))
            src (into [] (comp (distinct)
                               (filter #(and (jtms/in? tms %)
                                             (some-> (p/get-sentex (:records kb) %) rules/rule? not))))
                      (concat cl (mapcat #(some-> (jtms/justification tms %) :antecedents)
                                         (mapcat #(jtms/dependents tms %) cl))))
            rls (into [] (filter #(and (not (contains? pending %)) (jtms/in? tms %)
                                       (some-> (p/get-sentex (:records kb) %) rules/rule?)))
                      cl)]
        (swap! a #(-> %
                      (update :moved (fnil into #{}) (keys pending))
                      (update :extra (fnil into []) (:superseded mig))
                      (update :region (fnil into #{}) reg)))
        (update mig :new (fnil into []) (into src rls))))))

(defn clear-except-moves!
  "Empty `:except-moves` outright — a rebuild reconciles every supersession from scratch."
  [kb]
  (reset! (reasoning/except-moves kb) {}))

(defn- marked-roots
  "The predicates carrying `prop` — `:functional` or `:anti-symmetric` — whose specs are
  every functor `functional-mark-relevant?` or `anti-symmetric-mark-relevant?` admits:
  the `functional` `:props` set and every `functionalInArg` predicate, or the
  `anti_symmetric` `:props` set.

  The sets are read unscoped, a superset for the checks that read them."
  [tax prop]
  (case prop
    :functional     (into (tax/props tax :functional) (keys (:functional-in-arg @tax)))
    :anti-symmetric (tax/props tax :anti-symmetric)))

(defn- stored-facts-in-ancestors
  "Stored, positive, non-rule sentexes across `contexts`, kept when `marked?` admits
  them: the ancestor-set analogue of `subtree-sentexes`, lazy, and not belief-filtered
  for `equate-existing`'s reason.  Read from the smaller side, by two stored counts:
  the facts of the `roots`' specs (`tax/specs-global`, unscoped) that sit in `contexts`,
  or the facts in `contexts` that `marked?` admits.  The enumeration order, and so which
  prefix a cut budget takes, follows the side read
  (`budgeted-context-edge-candidates`)."
  [kb contexts marked? roots]
  (let [tax   (reasoning/taxonomy kb)
        idx   (:index kb)
        cs    (filterv symbol? contexts)
        ;; `marked?` reads the functor alone and admits a spec of a marked root, so these
        ;; are every functor it can admit
        fs    (into [] (comp (mapcat #(tax/specs-global tax %))
                             (distinct)
                             (filter #(pos? (reads/stored-count-with-functor idx %))))
                    roots)
        keep? (fn [s] (and (sx/positive-fact? s)
                           (sequential? (:sentence s))
                           (marked? tax (nm/functor (:sentence s)))))]
    (if (< (transduce (map #(reads/stored-count-with-functor idx %)) + 0 fs)
           (transduce (map #(reads/stored-count-in-context idx %)) + 0 cs))
      (let [in-set? (set cs)]
        (for [f     fs
              h     (reads/as-stored-with-functor idx f)
              :let  [s (p/get-sentex (:records kb) h)]
              :when (and s (contains? in-set? (:context s)) (keep? s))]
          s))
      (for [c     cs
            h     (reads/as-stored-in-context idx c)
            :let  [s (p/get-sentex (:records kb) h)]
            :when (keep? s)]
        s))))

(defn- budgeted-context-edge-candidates
  "Up to `tax/*exposure-instance-budget*` of `xs`, the `[sentex readers]` pairs a moved
  `genlCx` edge's merge sweep hands its `derive`, as `[candidates cut-budget-or-nil]`.
  `stored-facts-in-ancestors` enumerates in handle order, so past the budget which merges
  an edge derives depends on arrival order.  The caller files
  `:context-edge-exposure-truncated` whenever the cut happens (docs/equality.md)."
  [xs]
  (let [budget (max 0 (long tax/*exposure-instance-budget*))
        xs     (into [] (take (inc budget)) xs)]
    (if (> (count xs) budget)
      [(subvec xs 0 budget) budget]
      [xs nil])))

(defn- context-edge-exposure-truncation
  "The violation entry `equate-under-context-edge`/`antisym-equate-under-context-edge`
  file when `budgeted-context-edge-candidates` cuts short — never silently, matching
  every other bounded sweep in this KB."
  [sub mark budget]
  {:violation :context-edge-exposure-truncated
   :detail    {:context sub :mark mark :budget budget
               :message (str "genlCx edge into " sub " bounded its " (name mark)
                             " merge sweep at " budget " instances; some pairs the"
                             " widened ancestor set newly makes jointly visible may go"
                             " unmerged for this edge")}})

(defn- below-sweep-side
  "The contexts whose stored facts a merge sweep reads on the side of what the readers
  already saw: `below`, the contexts they see that `super` does not, or all of `seen`
  when one of `below` states a cached relation (`pr/cached`: a mark, a `genl` edge, an
  equality) or an `except`, any of which can make a pair of facts `super` sees clash at a
  reader and not at `super`."
  [kb below seen]
  (if (states-any-of? kb (conj pr/cached sx/except-functor) below)
    seen
    below))

(defn- move-merge-candidates
  "The `[sentex readers]` pairs a merge sweep of the `genlCx` move `m` hands its `derive`,
  kept when `relevant?` admits the functor (`stored-facts-in-ancestors` over `roots`).
  Per group of readers that gain one set of contexts (`move-groups`) the sweep reads one
  side: the gain's facts when the gain states facts alone (`plain-gain?`) and stores no
  more than the other side, else the facts of what the readers saw outside `super`'s
  ancestor set (`below-sweep-side`).  A group's candidates go with the readers of every
  group its readers see (`:seen`).  With no groups, `below-sweep-side` of the whole move
  at every reader of `:under`."
  [kb m relevant? roots]
  (if-let [groups (move-groups m)]
    (let [gainers (into #{} (mapcat :readers) groups)]
      (for [{:keys [gain seen below]} groups
            :let [other   (below-sweep-side kb below seen)
                  side    (if (and (plain-gain? kb gain seen)
                                   (<= (stored-count-across kb gain) (stored-count-across kb other)))
                            gain
                            other)
                  readers (into #{} (filter gainers) seen)]
            sx (stored-facts-in-ancestors kb side relevant? roots)]
        [sx readers]))
    (let [widened @(:under m)]
      (map #(vector % widened)
           (stored-facts-in-ancestors kb (below-sweep-side kb (into @(:under m) @(:below m)) @(:seen m))
                                      relevant? roots)))))

(defn- equate-under-context-edge-via
  "The body `equate-under-context-edge` and `antisym-equate-under-context-edge` share:
  a `(genlCx sub super)` edge arriving over facts a widened ancestor set newly makes
  jointly visible hands each `move-merge-candidates` pair to the family's `derive` in its
  own context, and files the budget's cut as `prop`'s truncation.  `declares?` is the
  family's KB-wide presence check and `relevant?` keeps the facts a mark of it can reach.
  `derive` takes a fifth argument, the readers whose ancestor set the edge changed."
  [kb m declares? relevant? derive prop]
  (let [tax         (reasoning/taxonomy kb)
        [sub super] (:edge m)]
    (when (and (symbol? sub) (symbol? super) (declares? tax))
      (let [[candidates cut] (budgeted-context-edge-candidates
                              (move-merge-candidates kb m relevant? (marked-roots tax prop)))
            result (reduce (fn [acc [sx readers]]
                             (merge-with into acc
                                         (derive kb (:sentence sx) (:context sx) (:id sx)
                                                 readers)))
                           {:new [] :superseded [] :violations []}
                           candidates)]
        (cond-> result
          cut (update :violations conj
                      (context-edge-exposure-truncation sub prop cut)))))))

(defn equate-under-context-edge
  "When a `(genlCx sub super)` edge arrives, derive the equalities a `(functional …)`
  mark licenses over facts the readers under `sub` newly see together: the context twin
  of `equate-under-edge`.  Hands each stored fact of `:seen` that
  `functional-mark-relevant?` admits to `derive-functional-equalities` at its own context.
  Free for a KB that declares nothing functional.  Budgeted
  (`budgeted-context-edge-candidates`) and idempotent.  The equality rests on the `genlCx`
  edges its reader sees each fact and the declaration through (`pair-antecedents`)."
  [kb m]
  (equate-under-context-edge-via
   kb m
   tax/functional-family-declared?
   functional-mark-relevant?
   derive-functional-equalities
   :functional))

(defn antisym-equate-under-context-edge
  "When a `(genlCx sub super)` edge arrives, derive the equalities an `(anti_symmetric …)`
  mark licenses over the facts the widened ancestor set newly makes jointly visible: the
  twin of `equate-under-context-edge`, over `derive-antisymmetric-equalities`."
  [kb m]
  (equate-under-context-edge-via
   kb m
   #(seq (tax/props % :anti-symmetric))
   anti-symmetric-mark-relevant?
   derive-antisymmetric-equalities
   :anti-symmetric))

(defn- superseded-under
  "The superseded datums stored in a context of the `genlCx` move `m`'s `:under`, the
  contexts whose ancestor set the move changed.  A datum's displacement reads the
  merges its own context sees (`spelling-displacement`), so no other entry can move.
  Read from the smaller side: the superseded set, or the extents of `:under`."
  [kb m]
  (let [held  (jtms/superseded (reasoning/tms kb))
        idx   (:index kb)
        under @(:under m)]
    (if (< (count held) (transduce (map #(reads/stored-count-in-context idx %)) + 0 under))
      (into #{} (filter #(contains? under (:context (p/get-sentex (:records kb) %)))) (keys held))
      (into #{} (comp (mapcat #(reads/as-stored-in-context idx %)) (filter #(contains? held %)))
            under))))

(defn- reconcile-move
  "What the `genlCx` move `m` (`context-move`, an edge active now) means for the equality
  closure and the argument-type entailments: the sentexes the readers under `sub` newly
  see restated under a standing merge (`migrate-under-context-edge`), the merges the same
  widening licenses (`equate-under-context-edge`, `antisym-equate-under-context-edge`),
  and the derivations the declarations it shows draw (`entail-under-context-edge`).
  Returns `{:new :superseded :violations}`, or nil when no sweep did anything.  While any
  spelling is superseded it runs the supersession reconcile itself over the superseded
  datums stored under `sub` (`superseded-under`) and hands back no `:superseded`."
  [kb m]
  (let [cme (migrate-under-context-edge kb m)
        cfn (equate-under-context-edge kb m)
        cax (antisym-equate-under-context-edge kb m)
        ent (let [r (entail-under-context-edge kb m)]
              (when (or (seq (:new r)) (seq (:violations r))) r))
        mig (when (or cme cfn cax ent)
              (merge-with into {:new [] :superseded [] :violations []} cme cfn cax ent))]
    (if (seq (jtms/superseded (reasoning/tms kb)))
      (do (refresh-supersessions kb (:superseded mig) (superseded-under kb m))
          (some-> mig (assoc :superseded [])))
      mig)))

(def ^:dynamic *seed-moves?*
  "False while a write asserted with `{:chain? false}` settles: the drain re-checks what a
  `genlCx` move moves and seeds no chaining from it (`drain-context-moves!`)."
  true)

(def ^:dynamic *producer-moves*
  "A volatile of `{:edges #{[sub super]} :arrived #{handle} :derived {functor #{handle}}}`,
  or nil: the belief moves a write's settles make that the structural genlCx producer
  reads once the write has settled (`context-nat/reconcile-moves`).  A write entry point
  binds it to `producer-moves`.  The context-move drain adds the edges it read, a settle
  pass the datums it revived, and `derived-sentex-added` each derivation."
  nil)

(defn producer-moves
  "A fresh value for a write entry point to bind `*producer-moves*` to."
  []
  (volatile! {}))

(defn note-producer-moves!
  "Add `xs` under `k` of `*producer-moves*`, when it is bound."
  [k xs]
  (when-let [v *producer-moves*]
    (when (seq xs) (vswap! v update k (fnil into #{}) xs))))

(defn take-producer-moves!
  "`*producer-moves*`' moves, emptied, or nil when it is unbound."
  []
  (when-let [v *producer-moves*]
    (let [m @v]
      (vreset! v {})
      m)))

(defn- note-derived-move!
  "Add a derived sentex's `handle` under its functor `f` in `*producer-moves*`' `:derived`,
  which `context-nat/reconcile-moves` reads by the functors it reconciles."
  [f handle]
  (when-let [v *producer-moves*]
    (vswap! v update-in [:derived f] (fnil conj #{}) handle)))

(defn- note-moved-values
  "Queue the minted constants whose values the `genlCx` move `m` can place differently
  (`chain/sync-values!`): the constants each sentence stored in `:gained-below` names
  (`nat-read/note-values`), and for each declaration stored there `[:valued-facts f]`.
  Linear in what `:gained-below` stores, behind `nat-read/values-reachable?` or
  `nat-read/rewrites-reachable?`."
  [kb m]
  (when (or (nat-read/values-reachable? kb) (nat-read/rewrites-reachable? kb))
    (let [idx   (:index kb)
          recs  (:records kb)
          sxs   (into [] (comp (mapcat #(reads/as-stored-in-context idx %))
                               (keep #(p/get-sentex recs %))
                               (map sx/sentence-of))
                      (sort-by nm/name-key @(:gained-below m)))
          decl? #(and (seq? %) (= res/correspondence-predicate (first %)))]
      (nat-read/note-values kb (remove decl? sxs) true)
      (when-let [fs (seq (into #{} (comp (filter decl?) (map second) (filter symbol?)) sxs))]
        (swap! (reasoning/respell kb) into (map #(vector :valued-facts %)) fs)))))

(defn- note-moved-correspondences!
  "Queue `[:corresponded f]` on `:respell` for each function `f` whose correspondence
  declarations can meet a rule differently after the `genlCx` move `m`: every function a
  declaration stated in the move's effective stratum (`:moved`) declares, and, when a
  context of `:moved` stores a rule, every function a stored declaration declares.  The
  settle re-spells the rules holding an open application of `f` and the rules a
  correspondence of `f` respelled (`chain/reconcile-corresponded!`, docs/nat.md, The
  corresponding predicate).  One functor count on a KB declaring none."
  [kb m]
  (when (and (seq (:moved m)) (res/any-corresponding-predicates? kb))
    (let [idx  (:index kb)
          recs (:records kb)
          fns  (fn [hs] (into #{} (comp (keep #(p/get-sentex recs %))
                                        (map #(second (:sentence %)))
                                        (filter symbol?))
                              hs))
          fs   (into (fns (reads/as-stored-with-functor-in idx res/correspondence-predicate (:moved m)))
                     (when (reads/stores-rule-in? idx (:moved m))
                       (fns (reads/as-stored-with-args idx res/correspondence-predicate {}))))]
      (when (seq fs)
        (swap! (reasoning/respell kb) into (map #(vector :corresponded %)) fs)))))

(def ^:private move-families
  "Every family a `genlCx` move re-checks, read by `drain-context-moves!` with the move's
  `context-move` value.  `:on` names the kinds of move a row reads: `:shown` an edge
  stored or relabelled and active now, `:hidden` one removed or out, `:excepted` an active
  edge an `except` that moved reaches the support of (the readers under the except's
  context gain or lose it).  `:stratum` names the sets of the move the row reads
  (`:raw`, the excepts in force; `:effective`, fact visibility), and `:run` takes the KB
  and the move and answers `{:seeds [handle …] :covered [handle …] :mig {:new :superseded
  :violations}}` or nil.  The placement families read the moves' projection (`:reach`), not a row."
  [{:family :exception-rules :on #{:shown :hidden :excepted} :stratum :effective
    :run (fn [kb m] (recheck-genlCx-edge kb m) nil)}
   {:family :excepts :on #{:shown :hidden} :stratum :raw
    :run (fn [kb m] (recheck-except-ancestors kb m) nil)}
   {:family :firing-seeds :on #{:shown :excepted} :stratum :effective
    :run (fn [kb m] (when *seed-moves?* {:seeds (move-seeds kb m true)}))}
   {:family :merges-and-mints :on #{:shown :excepted} :stratum :effective
    :run (fn [kb m] {:mig (reconcile-move kb m)})}
   {:family :covered-merges :on #{:shown :excepted} :stratum :effective
    :run (fn [kb m] {:covered (move-covered-merges kb m)})}
   {:family :departed-mints :on #{:hidden} :stratum :effective
    :run (fn [kb m] {:mig (departed-context-edge-mints kb m)})}
   {:family :correspondences :on #{:shown :hidden :excepted} :stratum :effective
    :run (fn [kb m]
           (note-moved-correspondences! kb m)
           (when (seq (:moved m)) (note-moved-values kb m))
           nil)}])

(defn- take-departed-edges!
  "The `genlCx` records `note-departure!` queued since the last call, taken off the
  queue."
  [kb]
  (let [edge? (comp context-edge-shaped? :sentence)
        [old] (swap-vals! (reasoning/mint-queues kb) update :departed
                          #(not-empty (into [] (remove edge?) %)))]
    (filterv edge? (:departed old))))

(defn- moved-edges
  "The `genlCx` edges `[sub super]` moved since the last call of this settle, in content
  order: for each lower end of `ends` (`tax/moves-since`), the stored `genlCx` facts out
  of it the touched set holds at a label `read` (a volatile of `[handle in?]`) has not
  seen, and the `departed` records."
  [kb ends departed read]
  (let [idx  (:index kb)
        tms  (reasoning/tms kb)
        recs (:records kb)
        tchd (jtms/touched tms)
        hs   (into [] (comp (mapcat #(reads/as-stored-with-args idx 'genlCx [[1 %]]))
                            (filter #(contains? tchd %))
                            (map #(vector % (jtms/in? tms %)))
                            (remove #(contains? @read %)))
                   ends)
        edge (fn [sx] (let [s (:sentence sx)]
                        (when (and s (context-edge-shaped? s) (symbol? (nth s 2)))
                          [(nth s 1) (nth s 2)])))]
    (vswap! read into hs)
    (into (sorted-set-by #(compare (mapv nm/name-key %1) (mapv nm/name-key %2)))
          (concat (keep #(edge (p/get-sentex recs (first %))) hs)
                  (keep edge departed)))))

(defn- excepted-edges
  "The active `genlCx` edges `[sub super]` whose supporter rests on a handle an `except`
  of which arrived, left or flipped since the last drain (`:except-moves`' `:whole`),
  or on a handle down that handle's except cascade, through the consequence closure, in
  content order.  An edge is active when the unscoped relation holds it: the move is read
  for every reader under its `sub` (`context-move`), so no one reader's view decides it."
  [kb]
  (let [whole (:whole @(reasoning/except-moves kb))]
    (when (seq whole)
      (let [tms    (reasoning/tms kb)
            recs   (:records kb)
            tax    (reasoning/taxonomy kb)
            sups   (set (reads/as-stored-with-functor (:index kb) 'genlCx))
            target #(some-> (p/get-sentex recs %) :sentence kb/except-target)
            roots  (into #{} (mapcat #(take-while some? (iterate target %))) whole)]
        (into (sorted-set-by #(compare (mapv nm/name-key %1) (mapv nm/name-key %2)))
              (comp (filter #(contains? sups %))
                    (keep #(:sentence (p/get-sentex recs %)))
                    (filter context-edge-shaped?)
                    (map (fn [[_ a b]] [a b]))
                    (remove (fn [[_ b]] (tax/root-context? b)))
                    (filter (fn [[a b]] (contains? (tax/context-parents-global tax a) b))))
              (jtms/consequence-closure tms roots))))))

(defn- seed-floor
  "The least believed supporter of the active `genlCx` edge `[sub super]` when this settle
  created every believed one (`created`, `jtms/touched-new`), else nil.  A
  supporter created in this settle has been believed since it was stored, since leaving
  belief takes a retraction, whose settle resets the touched sets.  Handles are allocated in
  assertion order, so a fact, rule or `genl` edge stored at or above the floor arrived
  with the edge in the taxonomy and was chained or joined with it there (`move-seeds`)."
  [kb [sub super] created]
  (let [tms (reasoning/tms kb)
        ins (filterv #(jtms/in? tms %) (keys (tax/supporters (reasoning/taxonomy kb) [:genlCx sub super])))]
    (when (and (seq ins) (every? #(contains? created %) ins))
      (reduce min ins))))

(defn- drain-moves!
  "`drain-context-moves!` outside a rebuild."
  [kb read]
  (let [tax            (reasoning/taxonomy kb)
        [since first?] (decide/take-edge-cursor! kb)
        departed       (take-departed-edges! kb)
        rebuilt?       (and since (< (tax/relation-gen tax :genlCx) since))
        ends           (if (and since (not rebuilt?)) (tax/moves-since tax :genlCx since) #{})]
    (if (and (empty? ends) (empty? departed) (empty? (:whole @(reasoning/except-moves kb))))
      {:reach (delay (cond rebuilt? {:all? true} since {:under #{} :below #{}})) :first? first?}
      (let [ctxs   (move-except-contexts kb)
            moved  (moved-edges kb ends departed read)
            _      (note-producer-moves! :edges moved)
            memo   (volatile! {})
            ;; each move's gains are read without every edge this drain moved: a context
            ;; two of them reach is gained through neither alone
            move   (fn [[sub super]]
                     (or (get @memo [sub super])
                         ((vswap! memo assoc [sub super] (context-move* kb ctxs sub super moved)) [sub super])))
            ;; a delay: `:below` walks the ancestor set of the contexts under each lower end,
            ;; quadratic in a chain of n edges moved in one pass, and only a pass that holds
            ;; a placement candidate reads it
            reach  (delay
                     (cond
                       rebuilt?     {:all? true}
                       (nil? since) nil
                       :else
                       (let [ups (into [] (mapcat (fn [l] (map #(vector l %) (tax/context-parents-global tax l))))
                                       ends)]
                         {:under (into #{} (mapcat #(tax/context-down-global tax %)) ends)
                          :below (into #{} (mapcat #(deref (:below (move %)))) ups)})))
            created (delay (jtms/touched-new (reasoning/tms kb)))
            ;; the facts `entail-under-context-edge` drew for an earlier move of this drain
            entailed (volatile! #{})
            ms     (-> (mapv #(let [m (assoc (move %) :entailed entailed)]
                                (if (:active? m)
                                  [:shown (assoc m :floor (seed-floor kb % @created))]
                                  [:hidden m]))
                             moved)
                       (into (comp (remove (set moved))
                                   (map #(vector :excepted (assoc (move %) :entailed entailed))))
                             (excepted-edges kb)))
            steps  (vec (for [[kind m] ms
                              {:keys [on run]} move-families
                              :when (contains? on kind)]
                          [m run]))
            ;; a step boundary is a point a shutdown can stop the write at, as a settle
            ;; pass's is, and a drain past `progress/first-line-ms` logs its progress
            out    (if (empty? steps)
                     []
                     (with-open [r (progress/start ::context-moves
                                                   (str "settle: read " (count ms) " genlCx moves, by family")
                                                   (count steps))]
                       (into [] (map (fn [[m run]]
                                       (dur/check-abort!)
                                       (let [x (run kb m)] (progress/tick! r) x)))
                             steps)))]
        (when (seq ms) (note-split-marks! kb))
        ;; the moves a write's report reads the reach of (`settle-finish`)
        (when (and observe/*write-record* (seq ms))
          (.addAll ^java.util.List (observe/record-of ::context-moves #(java.util.ArrayList.)) (mapv second ms)))
        {:reach  reach
         :first? first?
         :seeds  (into [] (mapcat :seeds) out)
         :covered (into [] (mapcat :covered) out)
         :mig    (apply merge-with into {:new [] :superseded [] :violations []} (keep :mig out))}))))

(defn drain-context-moves!
  "Once a settle pass: read the `genlCx` moves since the placement cursor
  (`decide/take-edge-cursor!`), compute each one's `context-move` once, and hand it to
  every row of `move-families` the move reads.  The edges are `moved-edges`'; the
  placement families read `:reach`, a delay of `{:under :below}` over the unscoped
  closures (`decide/unscoped-closures`); the active edges an `except` that moved reaches
  are moves of their own (`excepted-edges`).  `read` is the settle's volatile of supporter
  labels drained.  Each row a move runs is a step (`dur/check-abort!`), and a drain past
  `progress/first-line-ms` logs a line per doubling.  Returns `{:reach :first? :seeds
  :covered :mig}`.  A rebuild takes the departures, leaves the cursor and runs no row.  See
  docs/contexts.md, \"One context move\"."
  [kb read rebuilding?]
  (if rebuilding?
    ;; the cursor is left for the first pass that places, which owes every placement;
    ;; the inherited clashes a rebuild reads start from an emptied memo
    (do (take-departed-edges! kb) {:reach (delay nil) :first? false})
    (drain-moves! kb read)))

(defn- stored-declarations
  "Every stored sentex whose functor is `f`, believed or not, and positive: a
  `(not (genl a b))` opposes the edge and is excluded.  Read by the passes that sweep what
  is already there (`post-taxonomy-supporters!`, `rebuild-taxonomy`, the `disjoint_metatype`
  arm), since each records supporters (docs/taxonomy.md).  Records are hinted a chunk
  ahead (`cap/hinting`); `r`, a progress reporter, ticks once per stored handle read."
  ([kb f] (stored-declarations kb f nil))
  ([kb f r]
   (let [hs (cap/hinting (cap/prefetcher (:records kb)) cap/recovery-hint-chunk
                         (reads/as-stored-with-functor (:index kb) f))]
     (->> (if r (progress/each r hs) hs)
          (keep #(p/get-sentex (:records kb) %))
          (filter sx/positive-fact?)))))

;; ---- the table -----------------------------------------------------------

(defn- commuting-args-group
  "The runtime group descriptor a `(commutativeInArgs P p1 p2 …)` sentence names, or nil
  when it names none.  **Sorted and deduped**, so the three arms below key on one value
  however the author wrote the positions: `(commutativeInArgs P 2 1)` installs and
  uninstalls the same entry `(commutativeInArgs P 1 2)` does, and a rebuild of either
  finds it.  Nil for a declaration naming fewer than two distinct positions, which
  `wff/commutative-in-args-problems` refuses at the entry point and `recover` may still
  replay from an older or foreign store."
  [sentence]
  (let [ps (vec (sort (distinct (drop 2 sentence))))]
    (when (and (symbol? (second sentence))
               (> (count ps) 1)
               (every? #(and (integer? %) (pos? %)) ps))
      [:args ps])))

(defn- prop-entry
  "The arms for a predicate-metadata mark (`(transitive P)`, `(symmetric P)`, …), which
  differ only in the `:props` key they maintain, read off `functor`'s declaration
  (`pr/prop-kind`).  `skip` is the set of predicates whose property is the engine's own to
  compute (the `closure-relations` genl and genlCx): their prop is not marked, applied
  identically on integrate, disintegrate and rebuild.  The `:derived` facet is argued on
  `predicates/prop`."
  ([functor] (prop-entry functor nil))
  ([functor skip]
   (let [kind    (pr/prop-kind functor)
         marked? (fn [pred] (not (contains? skip pred)))]
     {:integrate    (fn [kb sx h] (let [pred (second (:sentence sx))]
                                    (when (marked? pred)
                                      (tax/mark-prop (reasoning/taxonomy kb) kind pred h (:context sx)))))
      :disintegrate (fn [kb sx] (let [pred (second (:sentence sx))]
                                  (when (marked? pred)
                                    (tax/unmark-prop! (reasoning/taxonomy kb) kind pred (:id sx)))))
      :rebuild      (fn [tax {[_ pred] :sentence id :id ctx :context}]
                      (when (marked? pred) (tax/mark-prop tax kind pred id ctx)))
      :wff          wff/prop-problems})))

(defn- reifiable-entry
  "`prop-entry`'s arms for `(reifiable_function F)`, with the arrival queued as its leaving
  and a relabel are (`note-permuting-moves!`): the mark arriving re-spells the
  applications of `F` stored before it (`chain/reconcile-reified!`, docs/nat.md)."
  []
  (let [e (prop-entry 'reifiable_function)
        g (:integrate e)]
    (assoc e :integrate (fn [kb sx h]
                          (let [before (permuting-marks (reasoning/taxonomy kb))]
                            (g kb sx h)
                            (note-permuting-moves! kb before))))))

(defn- quoted-arg-entry
  "`prop-entry`'s arms for `(quotedArg P n T)` or `(quotedArgAndRest P n T)`, each followed
  by `[:mention P]` queued on `:respell`: the declaration makes position `n` a mention,
  which the canonical walk keeps as written (`res/mention-at`), so the rows of P a mark
  sorts (`integrate/rows-a-mention-spells`) are respelled.  A relabel reaches the queue
  through `note-permuting-moves!`."
  [functor]
  (let [{:keys [integrate disintegrate] :as e} (prop-entry functor)
        queue! (fn [kb sx] (let [p (second (:sentence sx))]
                             (when (symbol? p) (swap! (reasoning/respell kb) conj [:mention p]))))]
    (assoc e
           :integrate    (fn [kb sx h] (let [r (integrate kb sx h)] (queue! kb sx) r))
           :disintegrate (fn [kb sx] (let [r (disintegrate kb sx)] (queue! kb sx) r)))))

(defn- forcing-entry
  "`prop-entry`'s arms for a forced-monotonic declaration `(functor P)`, each followed by
  the switch when P joins or leaves the forced-monotonic set over every reader or the
  baseline set (`decide/forced-monotonic?`, `decide/global?`, so a baseline member never
  switches):
  `checks/force-reach!` rewrites the forced memberships over what P reaches, and the
  rules in that reach are queued for a fresh join.  The verdicts over P's facts are
  placed again by the settle (`chain/place-nogoods!`, docs/nmtms.md, \"The
  forced-monotonic set\")."
  [functor]
  (let [{:keys [integrate disintegrate] :as entry} (prop-entry functor)
        kind    (pr/prop-kind functor)
        state   (fn [kb pred] (let [tax (reasoning/taxonomy kb)]
                                [(decide/forced-monotonic? tax kind pred) (decide/global? tax kind pred)]))
        switch! (fn [kb pred [u g] [u' g']]
                  (when (or (not= u u') (not= g g'))
                    (mark-recheck kb (checks/force-reach! kb pred (not= g g')) :all-rejoin)))]
    (assoc entry
           :integrate    (fn [kb sx h]
                           (let [pred   (second (:sentence sx))
                                 before (state kb pred)
                                 r      (integrate kb sx h)]
                             (switch! kb pred before (state kb pred))
                             r))
           :disintegrate (fn [kb sx]
                           (let [pred   (second (:sentence sx))
                                 before (state kb pred)
                                 r      (disintegrate kb sx)]
                             (switch! kb pred before (state kb pred))
                             r)))))

(def ^:private equality-entry
  "One entry-shape for all three equality relations; whether a preferred term is named
  is read off the sentence by `kb/preferred-term` inside the arms.  Two compound shapes
  are not a symbol merge: `(rewriteOf T E)` with a compound `E` is a NAT reify-to-term
  declaration (docs/nat.md), skipped by every arm; `(equals L R)` with a variable-bearing
  compound side is a schematic equational rule, cached in the taxonomy's rewrite-rule set
  (docs/equality.md).  `wff/equality-problems` waves both through.  The add arm is
  `integrate-equality-sentex`, which the derivation path calls too."
  {:integrate    integrate-equality-sentex
   ;; the merge (or rule) survives while any other sentex still asserts it; the last supporter's removal splits the class and returns the displaced spellings, which owes the re-check trigger
   :disintegrate (fn [kb sx]
                   (let [s (:sentence sx) [_ a b] s]
                     (cond
                       (rewrite/schematic-equation? s)
                       (do (tax/del-rewrite-rule! (reasoning/taxonomy kb) (:id sx))
                           (recheck-equality-edge kb))
                       (sequential? b) nil
                       :else
                       (do (tax/del-equality! (reasoning/taxonomy kb) a b (:id sx))
                           ;; no class to narrow by on this side: what a released
                           ;; condition owes a re-derivation to is the firings the block
                           ;; swept, which hold no bindings to test
                           (recheck-equality-edge kb)))))
   ;; no migration is replayed on rebuild: the twins and their justifications are
   ;; already in the durable store, so recovery restores the *closure* / *rule set* and
   ;; lets the caller's `refresh-supersessions` decide which spellings it displaces
   :rebuild      (fn [tax {s :sentence id :id ctx :context}]
                   (let [[_ a b] s]
                     (cond
                       (rewrite/schematic-equation? s)
                       (when-let [[lhs rhs] (rewrite/orient a b)]
                         (tax/add-rewrite-rule tax id lhs rhs ctx))
                       (sequential? b) nil
                       :else (tax/add-equality tax a b id (kb/preferred-term s)))))
   :wff          equality-wff-problems})

(defn check-entries
  "Refuse an ill-formed table at namespace load: an entry with some of the cache arms
  (`:integrate`, `:disintegrate`, `:rebuild`) and not all, or with no arm at all.  Throws
  `:bad-table-entry` with `:mismatch` `:partial-cache-triple` or `:no-arm`.  Returns
  `entries` unchanged."
  [entries]
  (doseq [[f spec] entries]
    (let [cache-arms [:integrate :disintegrate :rebuild]
          present    (filterv #(get spec %) cache-arms)]
      (when (and (seq present) (not= (count present) (count cache-arms)))
        (throw (ex-info (str "special-predicate table entry for " f " is asymmetric: has "
                             (str/join ", " (map name present)) " but not "
                             (str/join ", " (map name (remove (set present) cache-arms)))
                             " — an add arm without its removal and rebuild halves leaks")
                        {:type     :bad-table-entry
                         :mismatch :partial-cache-triple
                         :functor  f
                         :present  (set present)
                         :missing  (vec (remove (set present) cache-arms))})))
      (when-not (or (:wff spec) (seq present))
        (throw (ex-info (str "special-predicate table entry for " f " has no arm at all"
                             " — an entry carries a :wff arm, the cache triple"
                             " :integrate / :disintegrate / :rebuild, or both; it holds "
                             (pr-str (vec (sort (keys spec)))))
                        {:type :bad-table-entry :mismatch :no-arm :functor f})))))
  entries)

(defn- defn-wff-problems
  "The `:wff` arm for the three `defn*` collection definitions — the member-variable
  check (`sx/defn-condition-problems`), read in the table's `[tax sentence context]` shape."
  [_tax sentence _context]
  (sx/defn-condition-problems sentence))

(def ^:private ^:dynamic *edge-replay-skips*
  "Bound by `post-taxonomy-supporters!` to a volatile the genl / genlCx `:rebuild` arms bump each
  time `replay-edge` drops a stored declaration that is not a well-formed edge.  Nil off
  the replay path, where `replay-edge` still guards but counts nothing."
  nil)

(defn- replay-edge
  "Replay one stored `genl` / `genlCx` declaration through `add` (`tax/add-genl` or
  `tax/add-genlCx`), but only when the stored sentence is exactly
  `(expected-f <symbol> <symbol>)`.  A malformed sentex is skipped and counted, as
  `rebuild-tms` skips a justification the store cannot root (docs/taxonomy.md).  `reindex`
  replays stored sentexes, so a foreign or stale store can hand up a 2-element row (a nil
  endpoint that makes `strong-components` throw), an over-arity row (a fabricated edge) or
  a wrong-functor row (`disjoint` under the genl root).  Returns tax."
  [add tax sentence expected-f id ctx]
  (if (and (= 3 (count sentence))
           (= expected-f (first sentence))
           (symbol? (second sentence))
           (symbol? (nth sentence 2)))
    (add tax (second sentence) (nth sentence 2) id ctx)
    (do (when-let [v *edge-replay-skips*] (vswap! v inc)) tax)))

(defn- cover-arms
  "The integrate / disintegrate / rebuild triple the three whole-and-parts declarations
  share, differing in `kind` (`tax/cover-kinds`).  The part list goes into the taxonomy
  under one key (`tax/add-cover`), and a `genl` edge per part goes in against the
  covering sentex's own handle, posting the exception re-check the `genl` arm posts.  A
  part equal to the whole installs no edge (`wff/covering-problems` refuses it)."
  [kind]
  (letfn [(edges! [kb tax h ctx whole parts]
            (doseq [p parts :when (not= p whole)]
              (tax/add-genl tax p whole h ctx)
              (recheck-genl-edge kb p whole)))]
    {:integrate    (fn [kb sx h]
                     (when-let [[whole parts] (tax/cover-parts (:sentence sx))]
                       (let [tax (reasoning/taxonomy kb) ctx (:context sx)]
                         (tax/add-cover tax whole parts kind h ctx)
                         (edges! kb tax h ctx whole parts))))
     :disintegrate (fn [kb sx]
                     (when-let [[whole parts] (tax/cover-parts (:sentence sx))]
                       (let [tax (reasoning/taxonomy kb)]
                         (tax/del-cover! tax whole parts kind (:id sx))
                         (doseq [p parts :when (not= p whole)]
                           (tax/del-genl! tax p whole (:id sx))
                           (recheck-genl-edge kb p whole)))))
     ;; The rebuild arm takes `tax` alone, so it replays both halves and posts no
     ;; re-check — the `recover` after a `reindex` re-evaluates every exception rather
     ;; than per edge.
     :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                     (if-let [[whole parts] (tax/cover-parts sentence)]
                       (do (tax/add-cover tax whole parts kind id ctx)
                           (doseq [p parts :when (not= p whole)]
                             (tax/add-genl tax p whole id ctx))
                           tax)
                       (do (when-let [v *edge-replay-skips*] (vswap! v inc)) tax)))
     :wff          wff/covering-problems}))

(def ^:private arms
  "What the engine does about each functor it interprets, keyed by functor: the
  integrate / disintegrate / rebuild triple and the structural `:wff` check.  A map, so
  the order of the table stays the declaration's (`predicates/entries`), which
  `post-taxonomy-supporters!` replays.  What each functor says is in
  `vaelii.impl.predicates`; `entries` joins the two and refuses a disagreement."
  (merge
   {;; the two transitive relations: closure edges, belief-tracked in the taxonomy.
    ;; Their arms post the exception re-check *edge* trigger — on the derivation path
    ;; as well as the assert path, so a rule-concluded edge re-checks the exceptions
    ;; too.
    'genl {:integrate    (fn [kb sx h]
                           (let [[_ a b] (:sentence sx)]
                             (tax/add-genl (reasoning/taxonomy kb) a b h (:context sx))
                             (recheck-genl-edge kb a b)))
           :disintegrate (fn [kb sx]
                           (let [[_ a b] (:sentence sx)]
                             (tax/del-genl! (reasoning/taxonomy kb) a b (:id sx))
                             (recheck-genl-edge kb a b)))
           :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                           (replay-edge tax/add-genl tax sentence 'genl id ctx))
           :wff          wff/genl-problems}
    ;; The `genlCx` arms update the taxonomy alone: what the move shows or hides is the
    ;; settle's drain (`drain-context-moves!`), which reads every edge moved by an
    ;; assert, a rule, the structural producer, a retraction or a relabel.
    'genlCx {:integrate    (fn [kb sx h]
                             (let [[_ a b] (:sentence sx)]
                               (tax/add-genlCx (reasoning/taxonomy kb) a b h (:context sx))))
             :disintegrate (fn [kb sx]
                             (let [[_ a b] (:sentence sx)]
                               (tax/del-genlCx! (reasoning/taxonomy kb) a b (:id sx))))
             :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                             (replay-edge tax/add-genlCx tax sentence 'genlCx id ctx))
             :wff          wff/genlCx-problems}
    'covering   (cover-arms :covering)
    'separating (cover-arms :separating)
    'partition  (cover-arms :partition)
    'disjoint {:integrate    (fn [kb sx h]
                               (let [[_ a b] (:sentence sx)]
                                 (tax/add-disjoint (reasoning/taxonomy kb) a b h (:context sx))))
               :disintegrate (fn [kb sx]
                               (let [[_ a b] (:sentence sx)]
                                 (tax/del-disjoint! (reasoning/taxonomy kb) a b (:id sx))))
               :rebuild      (fn [tax {[_ a b] :sentence id :id ctx :context}]
                               (tax/add-disjoint tax a b id ctx))
               :wff          wff/disjoint-problems}
    'disjoint_metatype
    {:integrate    (fn [kb sx h]
                     (let [[_ m] (:sentence sx)]
                       (tax/mark-disjoint-metatype (reasoning/taxonomy kb) m h (:context sx))
                       ;; Members already asserted are recorded, not expanded into a clique of `(disjoint a b)`
                       ;; sentexes (`tax/disjoint?` consults the membership).  A later member is picked up by
                       ;; the structural member arm in `integrate-sentex`.  The sweep reads stored, not
                       ;; believed, sentexes: it records a supporter, so a skipped defeated membership could
                       ;; never be revived (`stored-declarations`).
                       (doseq [{[_ t] :sentence id :id mctx :context}
                               (stored-declarations kb m)]
                         (tax/add-metatype-member (reasoning/taxonomy kb) m t id mctx))))
     :disintegrate (fn [kb sx]
                     (let [[_ m] (:sentence sx)]
                       (tax/unmark-disjoint-metatype! (reasoning/taxonomy kb) m (:id sx))))
     ;; marks only: membership is replayed by post-taxonomy-supporters!' second pass, once every
     ;; metatype is known — the member functors are the metatypes themselves, which no
     ;; static table key can name
     :rebuild      (fn [tax {[_ m] :sentence id :id ctx :context}]
                     (tax/mark-disjoint-metatype tax m id ctx))
     :wff          wff/disjoint-metatype-problems}
    ;; `(sibling_disjoint C)` stores only the mark; `tax/disjoint?` reads C's
    ;; specializations off `specs`, so there is no member sweep.
    'sibling_disjoint
    {:integrate    (fn [kb sx h]
                     (let [[_ c] (:sentence sx)]
                       (tax/mark-sibling-disjoint (reasoning/taxonomy kb) c h (:context sx))))
     :disintegrate (fn [kb sx]
                     (let [[_ c] (:sentence sx)]
                       (tax/unmark-sibling-disjoint! (reasoning/taxonomy kb) c (:id sx))))
     :rebuild      (fn [tax {[_ c] :sentence id :id ctx :context}]
                     (tax/mark-sibling-disjoint tax c id ctx))
     :wff          wff/sibling-disjoint-problems}
    ;; `(orthogonal x y)` exempts nothing and fills no cache: `decide.related` reports its
    ;; clash with a genl edge or with a separation a reader sees.
    'orthogonal
    {:wff          wff/type-pair-problems}
    ;; `(siblingDisjointException x y)` exempts one pair from the separation marks — the
    ;; plain add/drop `disjoint` has, keyed as the same unordered pair.  A reader reads the
    ;; exemption where it reads the separation (`membership/sync-memberships`).
    'siblingDisjointException
    {:integrate    (fn [kb sx h]
                     (let [[_ a b] (:sentence sx)]
                       (tax/add-sib-exception (reasoning/taxonomy kb) a b h (:context sx))))
     :disintegrate (fn [kb sx]
                     (let [[_ a b] (:sentence sx)]
                       (tax/del-sib-exception! (reasoning/taxonomy kb) a b (:id sx))))
     :rebuild      (fn [tax {[_ a b] :sentence id :id ctx :context}]
                     (tax/add-sib-exception tax a b id ctx))
     :wff          wff/type-pair-problems}
    ;; `(arity P n)` is read by the per-assert arity check, so it is cached like the
    ;; other declarations the engine interprets rather than re-queried per assertion.
    ;; No `:wff` arm: the arity of `arity` is what would check it.
    'arity
    {:integrate    (fn [kb sx h]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n))
                         (tax/add-arity (reasoning/taxonomy kb) pred n h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n))
                         (tax/del-arity! (reasoning/taxonomy kb) pred n (:id sx)))))
     :rebuild      (fn [tax {[_ pred n] :sentence id :id ctx :context}]
                     (when (and (symbol? pred) (integer? n))
                       (tax/add-arity tax pred n id ctx)))}
    ;; `(functionalInArg P n)` is cached as `arity` is, because the definitional checks read
    ;; it on every assert.  It is read up the hierarchy (`tax/functional-in-arg-over`),
    ;; where `transitiveInArg` is read for the goal's own predicate, so it does not go
    ;; through `prop-entry`.
    'functionalInArg
    {:integrate    (fn [kb sx h]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n) (pos? n))
                         (tax/add-functional-in-arg (reasoning/taxonomy kb) pred n h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n) (pos? n))
                         (tax/del-functional-in-arg! (reasoning/taxonomy kb) pred n (:id sx)))))
     :rebuild      (fn [tax {[_ pred n] :sentence id :id ctx :context}]
                     (when (and (symbol? pred) (integer? n) (pos? n))
                       (tax/add-functional-in-arg tax pred n id ctx)))
     :wff          wff/functional-in-arg-problems}
    ;; The three commutativity relations (docs/canonicalization.md) are cached, because the
    ;; canonicalizer reads them on every assert, and share one group descriptor
    ;; (`sentex/commuting-components`).  The mark is read off the literal's exact functor
    ;; (`res/kb-sentex`, `tax/commuting-groups`).  `commutative` installs its group here
    ;; and not through a core.txt rule, which would be a cycle (docs/canonicalization.md).
    'commutative
    {:integrate    (fn [kb sx h]
                     (let [pred (second (:sentence sx))
                           tax  (reasoning/taxonomy kb)]
                       (when (symbol? pred)
                         (tax/mark-prop tax (pr/prop-kind 'commutative) pred h (:context sx))
                         (tax/add-commuting tax pred [:rest 1] h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [pred (second (:sentence sx))
                           tax  (reasoning/taxonomy kb)]
                       (when (symbol? pred)
                         (tax/unmark-prop! tax (pr/prop-kind 'commutative) pred (:id sx))
                         (tax/del-commuting! tax pred [:rest 1] (:id sx)))))
     :rebuild      (fn [tax {[_ pred] :sentence id :id ctx :context}]
                     (when (symbol? pred)
                       (tax/mark-prop tax (pr/prop-kind 'commutative) pred id ctx)
                       (tax/add-commuting tax pred [:rest 1] id ctx)))
     :wff          wff/relation-prop-problems}
    'commutativeInArgAndRest
    {:integrate    (fn [kb sx h]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n) (pos? n))
                         (tax/add-commuting (reasoning/taxonomy kb) pred [:rest n] h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n) (pos? n))
                         (tax/del-commuting! (reasoning/taxonomy kb) pred [:rest n] (:id sx)))))
     :rebuild      (fn [tax {[_ pred n] :sentence id :id ctx :context}]
                     (when (and (symbol? pred) (integer? n) (pos? n))
                       (tax/add-commuting tax pred [:rest n] id ctx)))
     :wff          wff/commutative-in-arg-and-rest-problems}
    'commutativeInArgs
    {:integrate    (fn [kb sx h]
                     (when-let [g (commuting-args-group (:sentence sx))]
                       (tax/add-commuting (reasoning/taxonomy kb) (second (:sentence sx))
                                          g h (:context sx))))
     :disintegrate (fn [kb sx]
                     (when-let [g (commuting-args-group (:sentence sx))]
                       (tax/del-commuting! (reasoning/taxonomy kb) (second (:sentence sx))
                                           g (:id sx))))
     :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                     (when-let [g (commuting-args-group sentence)]
                       (tax/add-commuting tax (second sentence) g id ctx)))
     :wff          wff/commutative-in-args-problems}
    ;; The two one-place term marks: `prop-entry`'s arms, with `commutative`'s structural
    ;; check, since a function is a `…Fn` symbol.
    'associative (assoc (prop-entry 'associative) :wff wff/relation-prop-problems)
    'idempotent  (assoc (prop-entry 'idempotent) :wff wff/relation-prop-problems)
    ;; `(meetFunctionOf F R)` records the order `R` against `F`, for the canonicalizer's
    ;; absorption arm (`res/meet-order`).
    'meetFunctionOf
    {:integrate    (fn [kb sx h]
                     (let [[_ f r] (:sentence sx)]
                       (when (and (symbol? f) (symbol? r))
                         (tax/add-meet (reasoning/taxonomy kb) f r h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [[_ f r] (:sentence sx)]
                       (when (and (symbol? f) (symbol? r))
                         (tax/del-meet! (reasoning/taxonomy kb) f r (:id sx)))))
     :rebuild      (fn [tax {[_ f r] :sentence id :id ctx :context}]
                     (when (and (symbol? f) (symbol? r))
                       (tax/add-meet tax f r id ctx)))
     :wff          wff/meet-function-problems}
    'distinctInArgAndRest
    {:integrate    (fn [kb sx h]
                     (let [[_ f n] (:sentence sx)]
                       (when (and (symbol? f) (integer? n) (pos? n))
                         (tax/add-distinct (reasoning/taxonomy kb) f n h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [[_ f n] (:sentence sx)]
                       (when (and (symbol? f) (integer? n) (pos? n))
                         (tax/del-distinct! (reasoning/taxonomy kb) f n (:id sx)))))
     :rebuild      (fn [tax {[_ f n] :sentence id :id ctx :context}]
                     (when (and (symbol? f) (integer? n) (pos? n))
                       (tax/add-distinct tax f n id ctx)))
     :wff          wff/commutative-in-arg-and-rest-problems}
    'inverse {:integrate    (fn [kb sx h]
                              (let [[_ p q] (:sentence sx)]
                                (tax/add-inverse (reasoning/taxonomy kb) p q h (:context sx))))
              :disintegrate (fn [kb sx]
                              (let [[_ p q] (:sentence sx)]
                                (tax/del-inverse! (reasoning/taxonomy kb) p q (:id sx))))
              :rebuild      (fn [tax {[_ p q] :sentence id :id ctx :context}]
                              (tax/add-inverse tax p q id ctx))
              :wff          wff/inverse-problems}
    'negates {:integrate    (fn [kb sx h]
                              (let [[_ p q] (:sentence sx)]
                                (tax/add-negates (reasoning/taxonomy kb) p q h (:context sx))))
              :disintegrate (fn [kb sx]
                              (let [[_ p q] (:sentence sx)]
                                (tax/del-negates! (reasoning/taxonomy kb) p q (:id sx))))
              :rebuild      (fn [tax {[_ p q] :sentence id :id ctx :context}]
                              (tax/add-negates tax p q id ctx))
              :wff          wff/negates-problems}
    'genlInverse {:integrate    (fn [kb sx h]
                                  (let [[_ p q] (:sentence sx)]
                                    (tax/add-genl-inverse (reasoning/taxonomy kb) p q h (:context sx))))
                  :disintegrate (fn [kb sx]
                                  (let [[_ p q] (:sentence sx)]
                                    (tax/del-genl-inverse! (reasoning/taxonomy kb) p q (:id sx))))
                  :rebuild      (fn [tax {[_ p q] :sentence id :id ctx :context}]
                                  (tax/add-genl-inverse tax p q id ctx))
                  :wff          wff/genl-inverse-problems}
    ;; the mark plus the retroactive lift; the lift's justifications are justified by this
    ;; sentex, so the dependency-directed sweep withdraws them.  The rebuild replays the mark
    ;; only.  The integrate arm returns `{:new :violations}` as the equality arms do.  This
    ;; mark carries no `:derived` flag (`predicates/prop`).
    'decontextualized_predicate
    (assoc (prop-entry 'decontextualized_predicate)
           :integrate (fn [kb sx h]
                        (let [pred (second (:sentence sx))]
                          (tax/mark-prop (reasoning/taxonomy kb) :decontextualized pred h (:context sx))
                          (lift-existing kb pred h))))
    'forced_decontextualized_predicate (prop-entry 'forced_decontextualized_predicate)
    ;; a forced-monotonic declaration's arrival or departure rewrites the forced memberships
    ;; and re-joins the rules in its reach (docs/nmtms.md, "The forced-monotonic set")
    'forced_monotonic_predicate (forcing-entry 'forced_monotonic_predicate)
    'forced_monotonic_between_predicates (forcing-entry 'forced_monotonic_between_predicates)
    ;; `(target_following_predicate P)` marks a target-following meta-sentex: a
    ;; `(P … (sentexHandle H) …)` is removed with H (`core/retract-following-metas!`).
    ;; `except` and `exceptWhen` do not carry it.
    'target_following_predicate (prop-entry 'target_following_predicate)
    ;; `(abducible_predicate P)` lets abduction hypothesize a `(P …)` (docs/abduction.md).
    ;; Not decontextualized: it is a policy of the context that grants it (docs/belief.md).
    'abducible_predicate (prop-entry 'abducible_predicate)
    ;; `(closed_extent_predicate P)`: a scoped mark, as `abducible_predicate`'s is.  The
    ;; re-check postings for the rules it governs are `recheck-on-sentence`'s, which runs
    ;; on every move of the grant's belief and not only on its storage (docs/naf.md).
    'closed_extent_predicate (prop-entry 'closed_extent_predicate)
    ;; `(closedExtentForArg P n v)`: the same mark under `:closed-extent-arg`, the
    ;; presence check `provers/closed-extent-for-arg?` reads.
    'closedExtentForArg
    (assoc (prop-entry 'closedExtentForArg) :wff wff/closed-extent-for-arg-problems)
    ;; `(modal_predicate P)` makes `(P agent sentence)` project into the agent's context
    ;; (docs/belief.md).  Not decontextualized, for `abducible_predicate`'s reason.
    'modal_predicate (prop-entry 'modal_predicate)
    ;; `(reifiable_function F)` marks `:reifiable` and `(unreifiable_function F)`
    ;; `:unreifiable`, belief-following through the prop cache; the reify presence check
    ;; (`vaelii.impl.nat`) reads `:reifiable`.  The argument is a function name, so
    ;; `function-decl-problems` replaces `prop-problems`.
    'reifiable_function   (assoc (reifiable-entry) :wff wff/function-decl-problems)
    'unreifiable_function (assoc (prop-entry 'unreifiable_function) :wff wff/function-decl-problems)
    ;; `(contextArgSubrelation F pos R)` orders `F`-contexts by `R` at `pos`
    ;; (docs/context-nat.md).  Read through the index per producer run, so the entry is the
    ;; wff arm alone.
    'contextArgSubrelation {:wff wff/context-arg-subrelation-problems}
    ;; `(functionCorrespondingPredicate F P N)` is read by the reify through the index
    ;; (docs/nat.md), so the entry is the wff arm alone.
    'functionCorrespondingPredicate {:wff wff/correspondence-problems}
    ;; The four argument constraints are read back through `matches-visible` per check; the
    ;; predicates that are the subject of one are marked
    ;; (`tax/arg-declaration-props`, `res/constraining-predicates`).
    'arg       (assoc (prop-entry 'arg)       :wff wff/arg-constraint-problems)
    'genlArg   (assoc (prop-entry 'genlArg)   :wff wff/arg-constraint-problems)
    'quotedArg (assoc (quoted-arg-entry 'quotedArg) :wff wff/arg-constraint-problems)
    'interArg  (assoc (prop-entry 'interArg)  :wff wff/inter-arg-constraint-problems)
    'argArg    (assoc (prop-entry 'argArg)    :wff wff/arg-arg-constraint-problems)
    'interArgEqual (assoc (prop-entry 'interArgEqual) :wff wff/inter-arg-equal-constraint-problems)
    ;; the covering constraints type a whole tail at once — each marks its subject
    ;; predicate as declaring one, exactly as the four above, and validates its own form
    ;; through one arm reading both the two- and three-argument shapes
    'args           (assoc (prop-entry 'args)           :wff wff/covering-constraint-problems)
    'argsGenl       (assoc (prop-entry 'argsGenl)       :wff wff/covering-constraint-problems)
    'argAndRest     (assoc (prop-entry 'argAndRest)     :wff wff/covering-constraint-problems)
    'argAndRestGenl (assoc (prop-entry 'argAndRestGenl) :wff wff/covering-constraint-problems)
    'quotedArgAndRest (assoc (quoted-arg-entry 'quotedArgAndRest) :wff wff/covering-constraint-problems)
    ;; the homogeneity constraints share the covering forms' shape — a relation, an
    ;; optional start, a type — and so their wff arm
    'interArgs       (assoc (prop-entry 'interArgs)       :wff wff/covering-constraint-problems)
    'interArgAndRest (assoc (prop-entry 'interArgAndRest) :wff wff/covering-constraint-problems)
    ;; The two preservation declarations really are wff-only — read back per query, with
    ;; the transitivity of the relation they name checked here because `arg`'s open-world
    ;; reading cannot (docs/inherit.md).
    'transitiveInArgInverse {:wff wff/arg-preserving-problems}
    'transitiveInArg        {:wff wff/arg-preserving-problems}
    ;; the three definitional collection relations expand into forward rules at assert
    ;; (docs/defns.md), so the wff arm is the whole entry
    'defnNecessary  {:wff defn-wff-problems}
    'defnSufficient {:wff defn-wff-problems}
    'defnIff        {:wff defn-wff-problems}
    ;; `different` is never stored at all — its wff arm *is* the refusal
    'different      {:wff wff/different-problems}
    ;; the minimal common genls and maximal common specs, computed from the genl closure
    ;; by provers/CommonGenlProver and never stored
    'minCommonGenl  {:wff wff/common-genl-problems}
    'maxCommonSpec  {:wff wff/common-genl-problems}
    ;; ...and the query operators, never stored (docs/naf.md, docs/aggregate.md); `forall`
    ;; is desugared at the rule entry point
    'unknown        {:wff wff/naf-problems}
    'thereExists    {:wff wff/naf-problems}
    'forall         {:wff wff/naf-problems}
    ;; `bravely` / `cautiously` are answered by the opt-in :brave-cautious prover and never
    ;; stored (docs/labeling.md)
    'bravely        {:wff wff/brave-cautious-problems}
    'cautiously     {:wff wff/brave-cautious-problems}
    ;; the two durations the :duration reasoner computes from the stored lengths, and
    ;; never reads stored (docs/duration.md)
    'totalDuration   {:wff wff/duration-problems}
    'overlapDuration {:wff wff/duration-problems}}
   ;; the eight predicate-metadata marks, each differing only in the `:props` kind its
   ;; declaration names (`pr/prop-kind`).  `commutative` is not here: it also installs a
   ;; commuting group.  `anti_symmetric` derives `(equals a b)` from a believed converse
   ;; (`derive-antisymmetric-equalities`); `anti_transitive` convicts the two-step chain
   ;; and the direct step (`checks/antitransitivity-problems`); both read the mark up the
   ;; predicate hierarchy (`tax/props-over`).
   (into {} (map (fn [f] [f (prop-entry f tax/closure-relations)]))
         '[transitive symmetric asymmetric reflexive functional irreflexive
           anti_symmetric anti_transitive])
   ;; the three equality relations share one entry-shape
   (into {} (map (fn [f] [f equality-entry])) kb/equality-predicates)
   (into {} (map (fn [f] [f {:wff wff/naf-problems}])) (keys sx/aggregate-functors))
   (into {} (map (fn [f] [f {:wff wff/structure-problems}]))
         (concat (keys sx/structure-relations) (keys sx/structure-predicates)))))

(defn- declared-half
  "The half of a table entry `vaelii.impl.predicates` owns: the `:props` kind a mark
  maintains, and whether the entry's arms run on the derivation path as well as the assert
  path.  Both are read off the declaration (the argument is on the facet in `predicates`)."
  [term]
  (cond-> {}
    (pr/prop-kind term)         (assoc :prop (pr/prop-kind term))
    (contains? pr/derived term) (assoc :derived? true)))

(defn check-declarations
  "Refuse a table whose arms and declarations disagree, at namespace load, as the
  cross-layer half of `check-entries`: a functor with arms and no declaration or the
  reverse (`arm-functors` is read before `entries` filters to `pr/in-special-table`; the
  one-argument arity reads the functors off `entries`); a `:cached` declaration whose arms
  have no cache triple, or the reverse; a `:checked` declaration whose arms have no
  `:wff`, or the reverse.  Throws `:bad-table-entry` with `:mismatch`.  The two validators
  stay separate (docs/predicates.md)."
  ([entries] (check-declarations entries (set (map first entries))))
  ([entries arm-functors]
   (let [unarmed    (vec (sort (remove arm-functors pr/in-special-table)))
         undeclared (vec (sort (remove pr/in-special-table arm-functors)))]
     (when (or (seq unarmed) (seq undeclared))
       (throw (ex-info (str "the special-predicate arms and the declarations in"
                            " vaelii.impl.predicates enumerate different functors —"
                            " declared with no arms: " (pr-str unarmed)
                            "; armed with no declaration: " (pr-str undeclared))
                       {:type       :bad-table-entry
                        :mismatch    :enumeration
                        :unarmed     unarmed
                        :undeclared  undeclared})))
     (doseq [[f spec] entries]
       (let [cached?  (contains? pr/cached f)
             checked? (contains? pr/checked f)]
         (when (not= cached? (boolean (:integrate spec)))
           (throw (ex-info (str "special-predicate " f " is declared "
                                (if cached? "" "un") "cached but its arms "
                                (if cached? "have no" "have a") " cache triple")
                           {:type :bad-table-entry :mismatch :cached :functor f})))
         (when (not= checked? (boolean (:wff spec)))
           (throw (ex-info (str "special-predicate " f " is declared "
                                (if checked? "" "un") "checked but its arms "
                                (if checked? "have no" "have a") " :wff arm")
                           {:type :bad-table-entry :mismatch :checked :functor f})))))
     entries)))

(def entries
  "The special-predicate dispatch table: an ordered vector of `[functor spec]` pairs,
  joined from the arms above and the declarations in `vaelii.impl.predicates`.  The order
  is the declaration's (`predicates/entries` filtered to the functors this table holds),
  and `post-taxonomy-supporters!` replays it top to bottom.  The four walks (integrate,
  disintegrate, rebuild, wff) all walk this vector; `table` is the lookup table."
  (-> (into [] (comp (map first)
                     (filter pr/in-special-table)
                     (map (fn [f] [f (merge (declared-half f) (arms f))])))
            pr/entries)
      check-entries
      (check-declarations (set (keys arms)))))

(def table
  "`entries` as the lookup map the walks below dispatch through."
  (into {} entries))

;; ---- the table walks -----------------------------------------------------

(defn wff-problems
  "Structural well-formedness problems for `sentence` (empty if OK): the `:wff` column of
  the table, walked.  A functor with no entry or no `:wff` arm is structurally
  unconstrained here.  `context` is passed to every arm.  A nil `tax` skips the checks that
  read stored content (the `genl`, `genlCx`, cover and `rewriteOf` cycles and the
  transitivity a preservation names), as an import does.  A `not` over a `pr/query-only`
  term, at any depth, is checked by that term's arm."
  [tax sentence context]
  (let [body     (loop [s sentence] (if (sx/negation? s) (recur (second s)) s))
        sentence (if (and (sequential? body) (contains? pr/query-only (first body)))
                   body
                   sentence)]
    (if-let [wf (:wff (get table (and (sequential? sentence) (first sentence))))]
      (wf tax sentence context)
      [])))

(defn wff-violation
  "`wff-problems` as a value, for content a rule derived: nil when `sentence` is
  well-formed, else a violation map in the shape `checks/constraint-violation` returns.
  Dropped and reported rather than thrown, since chaining is a fixpoint."
  [kb sentence context]
  (wff-violation* kb sentence context))

(defn- structural-integrate
  "The structural integrate arms, which no functor can key and so dispatch on the
  sentence's shape: a rule, an exceptWhen meta-sentex, a visibility `except`, and a
  disjoint metatype's member.  Shared by `integrate-sentex`, `integrate-twin` and
  `derived-sentex-added`.  `derived?` drops the rule arm only, since `chain/mint-rule`
  posts a generated rule by name through `index-rule-sentex`; running the arm again would
  post the rule twice and mark it for a second blanket re-check."
  ([kb sentex handle] (structural-integrate kb sentex handle false))
  ([kb sentex handle derived?]
   (let [sentence (sx/sentence-of sentex)
         f        (nm/functor sentence)]
     (cond
       ;; an exceptWhen meta-sentex names a rule it qualifies — register it in the
       ;; re-check index under that rule
       (sx/exceptWhen-meta? sentence)  (index-exceptWhen-meta kb sentex)
       ;; a visibility `(except (sentexHandle H))` fact: queue the firings that use H
       ;; so settle sweeps any conclusion now resting on an invisible antecedent
       (= sx/except-functor f)         (do (recheck-except kb sentex)
                                           (reconcile-belief-change kb #{handle}))
       ;; a rule reaching the general path (e.g. rebuilt by recover, or a migrated
       ;; twin) is indexed from its own record, so it keeps the direction its wrapper
       ;; gave it
       (and (not derived?)
            (rules/rule-sentence? sentence)) (index-rule-sentex kb handle sentex)
       ;; a member (M T) of a disjoint metatype: record T's membership, which makes it disjoint
       ;; from every other member in O(1) and reversibly.  Runs when the mark is stored, not
       ;; believed: a member stated while the mark is defeated separates once it revives.
       (and (= 1 (nm/arity sentence)) (tax/stored-disjoint-metatype? (reasoning/taxonomy kb) f))
       (tax/add-metatype-member (reasoning/taxonomy kb) f (first (nm/args sentence)) handle
                                (:context sentex))))))

(defn- run-integrate-arms
  "Run the one integrate arm that fits `sentex`: the table `:integrate` arm for a
  special functor, else the structural arm.  Shared by `integrate-sentex` (assert
  path) and `integrate-twin` (migration), so the dispatch lives in one place."
  [kb sentex handle]
  (store-declared-mint-rule! kb sentex)
  (if-let [e (get table (nm/functor (sx/sentence-of sentex)))]
    (when-let [g (:integrate e)] (g kb sentex handle))
    (structural-integrate kb sentex handle)))

(defn integrate-sentex
  "Reflect a newly stored sentex into the taxonomy, rule index and disjointness: the
  `:integrate` column of the table, walked, plus the structural arms.  Returns
  `{:new [handles] :superseded [[datum reason]] :violations [v]}` for an equality sentex,
  whose twins are chaining seeds, and nil for everything else."
  [kb sentex handle]
  (let [result (run-integrate-arms kb sentex handle)]
    (when (map? result) result)))

(defn integrate-twin
  "Full integration for a migrated twin (`migrate-sentex`): the same arms
  `integrate-sentex` runs, so a twin reaches the same caches an asserted declaration
  does.  `derived-sentex-added` narrows the table half to the `:derived?` entries.  The
  equality arm is skipped (`kb/rewritable-sentex?` holds equalities back from migration),
  then the re-check post every derived sentex gets.  Migration can run inside a
  forward-chaining pass; none of the arms re-enter `assert` or `chain`."
  [kb sentex handle]
  (let [sentence (sx/sentence-of sentex)]
    (when-not (kb/equality-sentence? sentence)
      (run-integrate-arms kb sentex handle))
    (recheck-on-sentence kb sentence)))

(defn disintegrate-sentex!
  "The mirror walk: reverse a departing sentex's cache effects through the
  `:disintegrate` column, or the matching structural arm.  Every cache below is
  reference-counted on the departing sentex's id, so an entry survives while
  another sentex still asserts the same claim."
  [kb sentex]
  (let [sentence (sx/sentence-of sentex)
        f        (nm/functor sentence)]
    (cond
      (contains? table f)
      (when-let [g (:disintegrate (get table f))]
        (let [before (permuting-marks (reasoning/taxonomy kb))]
          (g kb sentex)
          (note-permuting-moves! kb before)))
      (sx/exceptWhen-meta? sentence)
      (unindex-exceptWhen-meta kb sentex)
      ;; a visibility `except` leaving: queue the firings that use its target so settle
      ;; revives the conclusions it was hiding — the mirror of the integrate arm
      (= sx/except-functor f)
      (recheck-except kb sentex)
      (rules/rule-sentence? sentence)
      (do (rules/unindex-rule! (:index kb) (:id sentex)
                               (rules/antecedent-keys (:antecedent sentex))
                               (rules/consequent-index-pred sentex)
                               (:context sentex))
          ;; Deregistration recomputes the re-check predicates from the stored sentex, so a
          ;; mismatched call cannot leave a stale posting.  An exceptWhen exception's are withdrawn
          ;; by its meta-sentex leaving.
          (let [sd (concat (rules/separation-denial-predicates-of (reasoning/taxonomy kb)
                                                                  (sx/sentence-of sentex))
                           (rules/nonempty-recheck-predicates sentex))]
            (when (or (rules/rechecked? sentex) (seq sd))
              (rules/unindex-exception! (:index kb) (:id sentex)
                                        (distinct (concat (rules/recheck-predicates sentex) sd)))))
          ;; ...and the firings it refused before they could become justifications.  A
          ;; refusal is dead when its rule goes, and this is the event that says so —
          ;; entries are otherwise dropped lazily, when a queued rule's record is
          ;; walked, and a departed rule is never queued again.
          (swap! (reasoning/refused kb) dissoc (:id sentex)))
      ;; a member leaving a disjoint metatype: it stops being disjoint from the rest.
      ;; This checks storage like the integrate arm, so a member retracted while the mark
      ;; is defeated drops its support entry rather than leaving it behind for good.
      (and (= 1 (nm/arity sentence)) (tax/stored-disjoint-metatype? (reasoning/taxonomy kb) f))
      (tax/del-metatype-member! (reasoning/taxonomy kb) f (first (nm/args sentence)) (:id sentex)))))

(defn integrate-transitive
  "The table half of `derived-sentex-added`: for a functor the table keys, only the arms
  flagged `:derived?` run for a rule-derived conclusion.  A derived equality is reached
  through `integrate-equality-sentex` by name, since this fn discards what an arm returns.
  A functor the table does not key is the structural walk's.  See docs/taxonomy.md."
  [kb sentex handle]
  (let [e (get table (nm/functor (:sentence sentex)))]
    (when (:derived? e)
      ((:integrate e) kb sentex handle))))

(defn derived-sentex-added
  "The derivation-path add choke point: the integration arms a derived sentex may reach
  (`integrate-transitive` for a functor the table keys; the structural walk minus the rule
  arm otherwise) and the exception re-check post.  The except arm's
  `reconcile-belief-change` runs inline mid-fixpoint: it only swaps the taxonomy and
  writes cache entries.  `mark-premise` runs before `integrate/sentex-added`, with no
  read between the store and the justification.  Callers: forward chaining's
  `place-conclusion`, the `decontextualized_predicate` lift, the argument-constraint
  entailment and `derive-equality`.  See docs/taxonomy.md and docs/exceptions.md."
  [kb sentex handle]
  (store-declared-mint-rule! kb sentex)
  (let [sentence (sx/sentence-of sentex)]
    (note-derived-move! (nm/functor sentence) handle)
    (if (contains? table (nm/functor sentence))
      (integrate-transitive kb sentex handle)
      (structural-integrate kb sentex handle true))
    (recheck-on-sentence kb sentence)))

;; ---- rebuild: recover's replay of the table ------------------------------

(defn- post-recheck-keys!
  "Post every stored rule and every stored `exceptWhen` meta-sentex of `kb` in the
  re-check index under the keys `index-rule-sentex` and `index-exceptWhen-meta` post at a
  write (`rule-recheck-keys`, `exception-recheck-predicates`), read against the taxonomy
  `tx`.  Reads every context, since the re-check index holds the rules of every context.
  Queues no re-check."
  [kb tx]
  (let [idx  (:index kb)
        recs (:records kb)]
    (doseq [h    (reads/as-stored-rules-in-global idx :rule)
            :let [ks (some->> (p/get-sentex recs h) (rule-recheck-keys tx))]
            :when ks]
      (rules/index-exception idx h ks))
    (doseq [h    (reads/as-stored-with-functor idx sx/except-wrapper)
            :let [s  (:sentence (p/get-sentex recs h))
                  rh (when (sx/exceptWhen-meta? s) (sx/exceptWhen-rule-handle s))]
            :when rh]
      (rules/index-exception idx rh (exception-recheck-predicates tx s)))))

(defn post-taxonomy-supporters!
  "Post the taxonomy's supporter families (`tax/post!`) for every stored declaration in
  `kb`: the `:rebuild` column replayed in entry order over a scratch taxonomy whose index
  store is `kb`'s, then each stored disjoint metatype's members, then the re-check keys of
  every stored rule and `exceptWhen` (`post-recheck-keys!`).  `kb`'s own taxonomy is
  untouched and the equality relations post nothing.  A malformed `genl` / `genlCx` row is
  dropped (`replay-edge`) and the count warned once."
  [kb]
  (let [scratch (tax/create-taxonomy)
        skips   (volatile! 0)]
    (tax/install-index! scratch (:index kb))
    (binding [tax/*defer-depths?*    true
              tax/*defer-cycle-scc?* true
              *edge-replay-skips*    skips]
      (let [fs (for [[f {:keys [rebuild]}] entries
                     :when (and rebuild (not (contains? kb/equality-predicates f)))]
                 [f rebuild])]
        (with-open [r (progress/start ::post-supporters "reindex: post the declarations' supporters"
                                      (transduce (map #(reads/stored-count-with-functor
                                                        (:index kb) (first %)))
                                                 + fs))]
          (doseq [[f rebuild] fs
                  sx (stored-declarations kb f r)]
            (rebuild scratch sx))))
      (doseq [m (tax/stored-disjoint-metatypes scratch)
              {[_ t] :sentence id :id ctx :context} (stored-declarations kb m)]
        (tax/add-metatype-member scratch m t id ctx)))
    (when (pos? (long @skips))
      (trove/log! {:level :warn :id ::edges-malformed
                   :msg  (str @skips " stored genl/genlCx declarations are not well-formed"
                              " edges and are left out of the taxonomy")
                   :data {:skipped @skips}}))
    (tax/restore-depths scratch)
    (post-recheck-keys! kb scratch)
    nil))

(defn post-declaration-supporters!
  "Post the supporter families of the stored literal declarations `sxs` alone, each a
  sentex carrying its `:id`: the `:rebuild` column `post-taxonomy-supporters!` replays,
  over a scratch taxonomy whose index store is `kb`'s.  The index half of a declaration's
  arrival on a KB whose taxonomy is not built (`vaelii.impl.record-edit`), the mirror of
  `tax/retire-stored-supporter!`.  A functor with no `:rebuild` arm and an equality
  relation post nothing, and a posting already present is posted again unchanged."
  [kb sxs]
  (let [scratch (tax/create-taxonomy)]
    (tax/install-index! scratch (:index kb))
    (binding [tax/*defer-depths?*    true
              tax/*defer-cycle-scc?* true]
      (doseq [sx   sxs
              :let [f (nm/functor (:sentence sx))
                    rebuild (when-not (contains? kb/equality-predicates f)
                              (:rebuild (get table f)))]
              :when rebuild]
        (rebuild scratch sx)))
    nil))

(defn rebuild-taxonomy
  "Rebuild the in-memory taxonomy over a cleared one: the believed side of every key the
  index's supporter families hold (`tax/refresh-beliefs` with no region), and the equality
  partition and rewrite rules replayed from their stored declarations by the `:rebuild`
  column.  Drops every cache first."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (tax/clear-relations! tax)
    (doseq [f    kb/equality-predicates
            :let [rebuild (:rebuild (get table f))]
            :when rebuild
            sx   (stored-declarations kb f)]
      (rebuild tax sx))
    (tax/refresh-beliefs tax (partial jtms/in? (reasoning/tms kb)))))

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :S5 :label "Refused firings" :kind :index :keyed-by :handle :reads [:records :T1]
  :holds-content? true
  :retired-by {:integrated :K :removed :K :settle-pass :G :recover :R :image-install :R
               :cleared :W}
  :computed :write :imaged? :state :at [[:refused]]
  :note "`{rule #{refusal}}`"})

(caches/register-derived
 {:id :Q8 :label "Mint departures" :kind :queue :keyed-by :handle :reads [:records]
  :holds-content? false
  :retired-by {:settle-pass :Q :recover :W :cleared :W}
  :computed :write :imaged? false :at [[:mint-queues :departed]]
  :note "the removed `genlCx` edges, whose upper ends J5 does not record, and the removed records that can have subsumed a mint (`note-departure!`); `drain-context-moves!` takes the edges and `withheld-releases` the rest"})

(caches/register-derived
 {:id :Q9 :label "Unpremised mints" :kind :queue :keyed-by :handle :reads [:records]
  :holds-content? false
  :retired-by {:settle-pass :Q :recover :W :cleared :W}
  :computed :write :imaged? false :at [[:mint-queues :unpremised]]
  :note "the records a retraction left on a derivation alone (`note-unpremised!`); `subsumed-mint-blocks` drains it"})

(caches/register-derived
 {:id :Q10 :label "Owed mint releases" :kind :queue :keyed-by :handle :reads [:records :Q8]
  :holds-content? false
  :retired-by {:image-install :R :cleared :W}
  :computed :write :imaged? :state :at [[:mint-queues :owed] [:mint-queues :defer-next]]
  :bound "one row per departure or arrival a settle under `*release-withheld?*` false left unread, until `release-withheld!`"
  :note "the departures and arrivals `withheld-releases` kept owed while `*release-withheld?*` was false (`owe-releases!`), carried by the image so a close and a reopen keep the debt; `release-withheld!` drains it, and `:defer-next` marks the first settle after a trusted install"})

(caches/register-derived
 {:id :K13 :label "Mint rule handles" :kind :cache :keyed-by :value :reads [:index]
  :holds-content? false
  :retired-by {:stored :W :removed :W :recover :W :cleared :W}
  :computed :read :imaged? false :at [[:mint-rules]]
  :note "`{kind handle}`, the index's `[:mint-rules]` family read once (`kb/mint-rule-table`); the store and removal of a rule of `kv/mint-rules`, a wipe, `reindex` and the import's record phase drop it (`kb/forget-mint-rules!`), and a fill installs only over the generation it read"})

(caches/register-derived
 {:id :K14 :label "Lazy-forward rule presence" :kind :cache :keyed-by :value :reads [:index]
  :holds-content? false
  :retired-by {:stored :W :removed :W :recover :W :cleared :W}
  :computed :read :imaged? false :at [[:lazy-rules]]
  :note "whether the rule extent's `[:lazy]` node counts a rule, read once (`kb/stores-lazy-rule?`); the store and removal of a rule taking `:lazy`, an engines join adding it, a wipe, `reindex` and the import's record phase drop it (`kb/forget-lazy-rules!`), and a fill installs only over the generation it read"})

(caches/register-derived
 {:id :Q1 :label "Exception re-check queue" :kind :queue :keyed-by :handle :reads [:records]
  :holds-content? false
  :retired-by {:settle-pass :Q :recover :R :image-install :R}
  :computed :write :imaged? :state :at [[:recheck]]
  :note "`{rule triggers}` posted by `mark-recheck`, drained by `settle/drain-recheck!` each pass"})

(caches/register-derived
 {:id :Q2 :label "Supersession moves" :kind :queue :keyed-by :value :reads [:Q5 :M1]
  :holds-content? false
  :retired-by {:settle-exit :Q :cleared :W :recover :R :image-install :R}
  :computed :write :imaged? :state :at [[:supersessions]]
  :note "the datums whose supersession entry moved, with each entry before its first move; `take-supersession-moves!` drains it"})

(caches/register-derived
 {:id :Q3 :label "Except moves" :kind :queue :keyed-by :handle :reads [:index :T1]
  :holds-content? false
  :retired-by {:settle-pass :Q :settle-exit :Q :recover :W}
  :computed :write :imaged? false :at [[:except-moves]]
  :note "the handles an except began or stopped hiding, drained in two stages (`drain-except-moves!`, `take-except-moves!`); the context-move drain reads the excepts that moved (`:whole`) for the `genlCx` edges they reach"})

(caches/register-derived
 {:id :Q4 :label "Respell queue" :kind :queue :keyed-by :functor :reads [:index]
  :holds-content? false
  :retired-by {:held :Q :recover :W}
  :computed :write :imaged? false :at [[:respell]]
  :note "the predicates whose permuting marks moved; `settle/respelled-seeds` drains it"})
