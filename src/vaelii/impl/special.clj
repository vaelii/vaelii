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
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.except :as exc]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
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
;; The forms below decide **when** a re-check condition is re-evaluated.  They queue rule
;; handles into `(reasoning/recheck kb)` as `{rule-handle -> triggers}`: the sentences
;; that arrived or left, a withdrawal marker (`::entailment`, `::computed`,
;; `{::separation types}`, `{::preserving s}`, `{::except-closure c}`), `:all`, or
;; `:all-rejoin`, which also forces the rule's join.  `recheck/exception-candidates`
;; narrows the rule's firings by them.  See docs/exceptions.md, "The re-check index".

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
      (if-let [e (find @m k)]
        (val e)
        (let [v (f)] (vswap! m assoc k v) v)))
    (f)))

(defn- mark-recheck
  "Queue `rule-handles` for exception re-evaluation at the next `settle`, recording
  `trigger` — the sentence whose arrival or departure could have flipped the exception,
  or a withdrawal marker — `:all` when there is no such sentence and every firing must
  be re-checked, or `:all-rejoin` when that unconditional check must also force a fresh
  join.

  The unconditional markers are absorbing, and `:all-rejoin` is the stronger one:
  once queued, adding a narrower trigger must not narrow it back."
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
                                  :all

                                  :else (conj (or cur #{}) trigger)))))
                     m rule-handles)))))

(defn signed-all
  "`p`'s global `genl` closure in direction `dir`, with every predicate `genlInverse`
  edges reach either way round (`tax/signed-closure`) — what the matching fan meets from
  `p`.  The plain closure on a KB declaring no `genlInverse`."
  [tax dir p]
  (let [[st sw] (tax/signed-closure tax dir p nil)]
    (if (empty? sw) st (into st sw))))

(defn- answered-predicates
  "The predicates whose goals a fact on `pred` answers, by the global closure: `pred`'s
  supertypes across `genl` and `genlInverse` edges (`signed-all`), and those of every
  predicate an `inverse` declares of one of them, since `(inverse P Q)` answers a `Q`
  goal from a `P` tuple.  The `genls` closure on a KB declaring neither.  Unscoped, for
  `recheck-declaration`'s reason."
  [tax pred]
  (let [ups (signed-all tax :up pred)]
    (into ups (comp (mapcat #(tax/inverses-of tax %)) (mapcat #(signed-all tax :up %))) ups)))

(def ^:private declaration-subjects
  "Declaration functors, mapped to the argument positions naming a predicate the
  declaration licenses a level-6 answer **about** without touching its extent: argument 1,
  both arguments of `inverse` and `negates`, and argument 2 of `genlInverse`
  (docs/exceptions.md, \"Five channels\").

  Who is **absent**, in the three groups `predicates/check-facets` reads this table
  against — a declaration answering goals about the predicate at argument 1 posts by one
  of the three routes or the rule refuses it at load:

  * **Answers no goal**, so the rule never asks: `functional` is read by the definitional
    checks and moves nothing a query says; `arity` and the decontextualization marks
    likewise.  They carry no `:answers` facet.
  * **Posts from its own arms** rather than through this shared path, which the
    `:retriggers` facet says: `arg`, whose arms post the arg-type re-check, and
    `closed_extent_predicate`.
  * **Reaches an exception through an ordinary fact trigger**, so there is nothing left
    for either route to post: `genlArg`, `quotedArg` and `interArg` — the rest of the
    argument-constraint family — each licensing inferences that are themselves stored
    sentexes.  Each records that in `:stops-short`, with its own version of the reason."
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
  "A declaration licensing an inference about some predicate arrived or left: queue `:all`
  every rule whose exception mentions a predicate a fact on the subject answers
  (`answered-predicates`), or for a `negates` side the side and its specs, the keys a
  denial the side answers is posted under (`rules/negates-denial-predicates`).  Any
  other declaration also queues the negated conditions on the subject
  (`recheck-negated-exceptions`), since such a rule is posted under `not`.
  `(transitive R)` also posts through `recheck-preserving-along`, since it is the licence
  `inherit/usable-relation?` reads.  Runs only while some rule carries a re-check
  condition.  The fan is unscoped: a trigger over-approximates, and the queued re-check
  reads each rule from the rule's own context.  See docs/exceptions.md, \"Five
  channels\"."
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

(defn- declared-instance-type
  "The type `sentence` declares when it is one of the `instance-type-shapes`, else nil."
  [sentence]
  (when-let [[len at] (get instance-type-shapes (nm/functor sentence))]
    (when (= len (count sentence))
      (let [t (nth sentence at)] (when (symbol? t) t)))))

(defn- arg-declared-types
  "The types some `(arg pred n T)` or `(argAndRest pred n T)` declares of `pred`'s
  argument positions — read off the roots rather than through `matches-visible`,
  and globally rather than per context, because a trigger has to be conservative in the
  direction the answer is and a declaration this context cannot see still qualifies a
  rule in one that can.

  `pred`'s **super-predicates** are read too, and globally for the same reason: a
  declaration on `parentOf` types the arguments of a `fatherOf` fact
  (`res/constraining-predicates`), so a trigger keyed on the exact functor would miss
  exactly the channel the descension opened."
  [kb pred]
  (let [idx (:index kb)
        fs  (filter #(pos? (reads/stored-count-with-functor idx %)) (keys instance-type-shapes))]
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
  from the fact.  A KB declaring neither pays a cardinality read per functor.  The `genls` fan is unscoped, for
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
          (recheck-separated-exceptions kb trigger))
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
  `answers`, or nil: the stored rule keys read once, and the rules only for the answers
  some rule takes."
  [kb answers]
  (let [idx   (:index kb)
        ruled (reads/as-stored-rule-keys idx)]
    (not-empty
     (into #{} (comp (filter #(contains? ruled %))
                     (mapcat #(reads/as-stored-rules-by-antecedent-global idx %)))
           answers))))

(defn computed-reading-rules
  "The forward rules a datum on `bfn` re-joins and re-checks because `bfn` is a predicate
  a registered `SupportingProver` **reads**: the rules carrying an antecedent that a
  prover reading `bfn` answers (`provers/support-answers-reading`).  A rule whose
  computed antecedents only other provers answer rests on no answer the datum moves.

  Nothing connects the two predicates: a `(conversionFactor Gram Kilogram 0.001)` decides
  whether `(quantityGreaterThan ?q (QuantityFn 1 Kilogram))` holds of a mass in grams, the
  trigger index keys on the antecedent's own functor, and the facts that would have
  triggered the rule have already arrived.  `bfn` is the functor of the sentence's
  **underlying body**, so a believed `(not (conversionFactor …))` reaches here too: it
  defeats the positive row and so moves the reading exactly as removing it would.

  The rules stated in every context are read, since the re-join and the re-check place
  each firing from its antecedents' contexts.  One map lookup for every datum that is not
  one of these.  For one that is, the stored rules' antecedent keys are read once, and the
  rules only for the answers some rule takes.  `s` is the sentence: a `genl` edge moves
  only the expression kinds at or above its upper end (`provers/support-answers-reading`)."
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
  "The settle pass moved the length of the relations `moved` (`arity/drain!`'s `:moved`, a
  set or `:all`): queue every rule carrying an antecedent a relation's length can move
  (`provers/relation-moved-answers`) for a re-check of every firing and a fresh join in
  this pass (`:all-rejoin`).  A binding, a `genl` edge and a relabel each move a length
  with no datum on a functor the prover reads, so no write-time re-join
  (`computed-reading-rules`) takes these.  Reads nothing while `moved` is empty, then the
  term index for a stored quoted form (`provers/quoted-anywhere?`), then, for a set, the
  term index for a stored quoted application headed by a member of `moved`
  (`provers/quoted-head?`), and when one is stored, the stored rule keys once."
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
  "A sentence `s` arrived or left and moved the separations of the types at or below
  the types `tax/sentence-separation-ends` names: post every rule watched under `not`
  (`reads/watched-rules-on`) with a negated re-check literal over one of them under the
  types a separation now keeps apart from that literal's type
  (`rules/separation-denial-predicates`), read unscoped as the re-check index is, and
  queue it for a blanket re-check, since a membership already stored can deny the literal
  now.  A posting the move took away is left in place: a spurious re-check costs a query,
  as `index-closed-extent-rules` says.  A sentence that moves no separation reads only
  the taxonomy, and the index is read only once one does."
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
  "A `(negates A B)` sentence `s` arrived or left: post every rule watched under `not` with a
  negated re-check literal on a predicate at or below `A` or `B` under the predicates
  that now negate it (`rules/negates-denial-predicates`), and queue it for a blanket
  re-check, since a tuple already stored can deny the literal now.  A posting the
  declaration's departure takes away is left in place, as
  `repost-separation-denial-rules` leaves one, and `recheck-declaration` queues the rule
  from it.  A `(genl sub super)` edge with a declaration reaching `super` moves which
  declarations reach the predicates below `sub`, so it reposts too.  Any other sentence
  reads one functor."
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

(defn- recheck-on-separation
  "A sentence `s` arrived or left and moved the separations of the types
  `separation-moved-types` names: queue every rule carrying a `disjoint` antecedent with
  the `{::separation types}` marker.  The next settle re-decides the firings and the
  refusals whose bindings name one of the types (`chain/separation-exempted?`), and
  re-joins each rule with a `disjoint` antecedent's end bound to each of them
  (`chain/*separation-moved*`), so a write costs the types it moves and not the rule's
  extent.  The firing's handles name none of these moves (docs/inference.md, \"A
  `disjoint` antecedent reads the separations\").

  A sentence that moves no separation costs a functor compare and taxonomy reads, and no
  index read.  The rules stated in every context are read, since each firing is
  re-decided at its own conclusion's context.  The rules with a negated re-check literal
  over a moved type are posted again under the types a separation's denial moves it on
  (`repost-separation-denial-rules`)."
  [kb s]
  (when-let [moved (separation-moved-types kb s)]
    (when (reads/stored-rule-key? (:index kb) 'disjoint)
      (mark-recheck kb (reads/as-stored-rules-by-antecedent-global (:index kb) 'disjoint)
                    {::separation moved})))
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
  exception mentions a predicate a fact on `super` answers (`answered-predicates`: the
  spec closure of `pe` moves iff `pe` is at or above `super`, or above an inverse of
  such a predicate) or a `closure-answered-exception-functors` functor, the
  composed-exception rules on `super`, the negated conditions at `sub`
  (`recheck-negated-exceptions`) and the preserved positions along `genl`; then post the
  calculus and typed-admission triggers on `super`, which need no watched rule.  The fan
  is read after the mutation, as the edge cannot put `sub` above `super`.  See
  docs/exceptions.md,
  \"Taxonomy changes are keyed on what the closure moved\"."
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

(defn- binds-any?
  "Does the firing behind justification `jid` bind one of `terms`, at any depth?  Reads
  the justification record, since `jtms/graph-just` drops the bindings."
  [kb terms jid]
  (when-let [j (p/get-justification (:records kb) jid)]
    (boolean (some (fn [v] (some terms (tree-seq sequential? seq v)))
                   (vals (:bindings j))))))

(defn- recheck-equality-edge
  "The equality closure moved (an equality asserted, derived or retracted, or a schematic
  rewrite rule arriving or leaving): queue `:all` each watched rule with a firing or a
  refusal that binds a term of the merged class `terms`, and each rule an arrival can
  release (`arrival-releasable-rule?`).  `terms` nil, for a split or a schematic
  rewrite, queues every watched rule.  See docs/exceptions.md, \"Five channels\"."
  ([kb] (recheck-equality-edge kb nil))
  ([kb terms]
   (let [tms (reasoning/tms kb)]
     (when-let [rules (seq (reads/watched-rules (:index kb)))]
       (doseq [rh rules]
         (when (or (nil? terms)
                   (arrival-releasable-rule? kb rh)
                   (some #(binds-any? kb terms %) (jtms/dependents tms rh))
                   (refusals-reach? kb rh
                                    (fn [e] (some (fn [v] (some terms (tree-seq sequential? seq v)))
                                                  (vals (:bindings e))))))
           (mark-recheck kb [rh] :all)))))))

(defn index-rule-sentex
  "Index a rule handle by **all** of its predicates — both sets are complete, so
  `reads/as-stored-rules-by-consequent-in` answers \"what could conclude P?\" for a
  forward-only rule too.  A rule whose consequent functor is a variable is filed under the
  `p/var-consequent-key` catch-all instead of a canonical `?var0` (see
  `rules/consequent-index-pred`); completeness of the consequent read is then the
  concrete bucket unioned with that catch-all, which `resolution/concluding-rule-handles`
  does.

  Only the *predicates* are indexed.  The **record is the source of truth** for what
  a rule may do: a `set/*Rule` wrapper canonicalizes into the sentex (see
  `vaelii.impl.sentex`), and `:engines` / `:defeasible` are read off it by every
  consumer.  Nothing enumerates rules by defeasibility — defaults fire from the same
  agenda as strict rules — so there is no default-rule index to maintain.

  A rule is not a table entry: its trigger is the *shape* of the sentence (any
  functor can head an implication), so it is the structural arm of the
  `integrate-sentex` walk below, and this is its add half."
  [kb handle rule-sentex]
  (let [antes (:antecedent rule-sentex)]
    (rules/index-rule (:index kb) handle
                      (rules/antecedent-keys antes)
                      (rules/consequent-index-pred rule-sentex)
                      (:context rule-sentex))
    ;; ...and in the re-check index under its own conditions' keys: `recheck-predicates`
    ;; and the closed-extent, separation-denial and negates-denial keys, three taxonomy
    ;; reads that a later grant (`index-closed-extent-rules`), separation
    ;; (`repost-separation-denial-rules`) or `negates` (`repost-negates-denial-rules`)
    ;; re-posts.  An `exceptWhen` posts from its meta-sentex (`index-exceptWhen-meta`).
    (let [tx (reasoning/taxonomy kb)
          ce (rules/closed-extent-recheck-predicates-of tx (sx/sentence-of rule-sentex))
          sd (concat (rules/separation-denial-predicates-of tx (sx/sentence-of rule-sentex))
                     (rules/negates-denial-predicates-of tx (sx/sentence-of rule-sentex)))]
      (when (or (rules/rechecked? rule-sentex) (seq ce) (seq sd))
        (rules/index-exception (:index kb) handle
                               (distinct (concat (rules/recheck-predicates rule-sentex) ce sd)))
        ;; `:all`: no trigger sentence, and the rule may have fired before the drain
        (mark-recheck kb [handle] :all)))))

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

(defn- exception-recheck-predicates
  "The re-check keys of the exceptWhen meta-sentence `meta`: the predicates its query
  mentions, the types a separation's denial and the predicates a `negates` denial move a
  negated conjunct of it on (`rules/separation-denial-predicates`,
  `rules/negates-denial-predicates`), and the predicates of its closed-extent negatives
  (`rules/closed-extent-query-predicates`)."
  [kb meta]
  (let [qs (sx/exception-query-conjuncts meta)
        tx (reasoning/taxonomy kb)]
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
        preds (exception-recheck-predicates kb (:sentence meta-sentex))]
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
  (let [others (into #{}
                     (comp (map #(p/get-sentex (:records kb) %))
                           (filter some?)
                           (filter #(and (sx/exceptWhen-meta? (:sentence %))
                                         (= rh (sx/exceptWhen-rule-handle (:sentence %)))
                                         (not= dropping-id (:id %))))
                           (mapcat #(exception-recheck-predicates kb (:sentence %))))
                     (reads/as-stored-naming-handle (:index kb) rh))
        rsx    (p/get-sentex (:records kb) rh)]
    (into others (when rsx (let [tx (reasoning/taxonomy kb)
                                 s  (sx/sentence-of rsx)]
                             (concat (rules/recheck-predicates rsx)
                                     (rules/separation-denial-predicates-of tx s)
                                     (rules/negates-denial-predicates-of tx s)
                                     (rules/closed-extent-recheck-predicates-of tx s)))))))

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
        this-preds (exception-recheck-predicates kb (:sentence meta-sentex))]
    (when rh
      (rules/unindex-exception! (:index kb) rh this-preds)
      (when-let [remaining (seq (rule-remaining-recheck-preds kb rh (:id meta-sentex)))]
        (rules/index-exception (:index kb) rh remaining))
      (mark-recheck kb [rh] :all)
      (restrength-firings! kb rh (:id meta-sentex))
      (force-rule! kb rh))))

;; ---- except: visibility removal blocks derivations too -------------------
;; A believed `(except (sentexHandle H))` in context C hides H from C and its
;; descendants, for derivation as for reads: a firing that used H and placed its
;; conclusion where C sees it is blocked (`chain/justification-excepted?`).  The trigger
;; below queues the rules of every firing resting on H, keyed on the handle.

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
  `[sub super]`, moved which contexts see it: queue what the visibility change touches,
  so `settle` sweeps a conclusion now resting on an invisible antecedent and re-derives
  one the fact can be seen for again.

    * The firings that **rest on H** through any chain (the justifications of H's
      consequence closure, `jtms/consequence-closure`) are queued under a
      `{::except-closure c}` marker, so the settle re-decides those firings and not the
      extent of their rules (`recheck/except-candidates`).
    * The firings the except refused or swept are gone from `dependents`, so the drain
      re-joins from the closure and from the antecedents of the justifications resting
      on it (`note-except-move!`, `drain-except-moves!`).
    * **H itself, when H is a rule**, is queued `:all`: a firing rests on its rule as it
      rests on its antecedents, and no fact of the closure keys the rule's own sentence.
    * **H's own target, when H is an except**, is re-checked the same way, down the
      cascade: H's force moved, so what rests on its target moves.

  H goes on `:except-moves` with `edge`, which also re-runs H's arrival sweep for the
  restatements the move reaches: an equality or a merge mark H restates facts only where
  it is visible."
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
                                         (when (integer? inf) inf)))))
                         closure)
           target  (p/get-sentex (:records kb) h)]
       (mark-recheck kb users {::except-closure closure})
       (when (and target (rules/rule? target)) (mark-recheck kb [h] :all))
       (note-except-move! kb h (:context except-sentex) edge)
       (recheck-defeats-reached kb h closure)
       ;; the except moves the visibility of H, or through the cascade that of the first
       ;; non-except H's excepts name, with no relabel, so that sentence posts what its
       ;; removal posts: a guard reading it is re-decided, and a firing the guard refused
       ;; or swept is released from the refusal record
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
  "`context-move` with the reader-class contexts `ctxs` (`move-except-contexts`) in hand."
  [kb ctxs sub super]
  (let [idx (:index kb)]
    (tax/context-move (reasoning/taxonomy kb) sub super ctxs
                      (fn [a b] (not (reads/stored-opposed? idx (list 'genlCx a b)))))))

(defn context-move
  "What the move of the `genlCx` edge `[sub super]` shows or hides (`tax/context-move`),
  with the reader classes the stored `except`s on `genlCx` supporters' support split the
  readers into (`exc/genlCx-except-contexts`).  The walks without the edge do not cross an
  edge stored in both polarities, so that edge can only enlarge the answer."
  [kb sub super]
  (context-move* kb (move-except-contexts kb) sub super))

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
  "`moved` plus the targets of any visibility-excepts it names.

  A relabel reports the except handle because that is the TMS datum whose belief
  changed, while the derived cache is indexed by the declaration handle the except
  hides. Expanding at this boundary lets callers report the event they observed
  without knowing which cache supporter it invalidates.

  This runs only when an `except` is stored (`reads/stores-any?`): while none is stored no
  handle in `moved` can name one and the region is `moved` itself — without a record fetch
  per member, on a set that is the whole KB when a rebuild's settle reads it."
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
  table and the `reifiable_function` functions.  Three persistent values, compared by
  identity first.

  The marks are read unscoped: they decide the stored spelling, which every reader
  shares."
  [tax]
  [(tax/props tax :symmetric) (get @tax :commuting {}) (tax/props tax :reifiable)])

(defn- note-permuting-moves!
  "Queue on `:respell` every predicate whose permuting marks differ between `before`
  (a `permuting-marks` reading) and now, and `[:reifiable f]` for every function whose
  `reifiable_function` mark does.  A mark that stops holding leaves rows spelled by it,
  and one that starts holding again leaves rows it would have folded; neither is a sentex
  arriving, so `chain/reconcile-spellings!` and `chain/reconcile-reified!` are told here,
  at the places a mark can stop or start holding without a declaration being written — its
  record leaving, and a relabel — and, for the reifiable mark, its record arriving
  (`reifiable-entry`).  Nearly always three `identical?` tests and nothing else."
  [kb [sym0 com0 rf0]]
  (let [[sym1 com1 rf1] (permuting-marks (reasoning/taxonomy kb))]
    (when-not (and (identical? sym0 sym1) (identical? com0 com1) (identical? rf0 rf1))
      (let [moved (-> #{}
                      (into (remove #(contains? sym1 %)) sym0)
                      (into (remove #(contains? sym0 %)) sym1)
                      (into (filter #(not= (get com0 %) (get com1 %)))
                            (concat (keys com0) (keys com1)))
                      (into (comp (remove #(contains? rf1 %)) (map #(vector :reifiable %))) rf0)
                      (into (comp (remove #(contains? rf0 %)) (map #(vector :reifiable %))) rf1))]
        (when (seq moved)
          (swap! (reasoning/respell kb) into moved))))))

(defn reconcile-belief-change
  "Reconcile every belief-derived taxonomy cache after `moved` may have changed truth.

  Bare, like `recover` and every other recompute: it rebuilds caches from what the KB
  currently believes and stores nothing of its own, so re-running it is the whole of
  taking it back.

  This is the engine-level choke point above `tax/refresh-beliefs`: ordinary JTMS
  defeat/revival/supersession and visibility `except` both change whether a stored
  declaration currently has force. `moved` may name either declaration handles or
  except handles; the latter are expanded to their targets before the scoped refresh.

  The caches read the network (`jtms/in?`); a scoped read filters a supporter through
  the read walk (`res/supporter-believed?`) and is keyed on the change clock, which every
  write moves, so nothing here retires one."
  ([kb] (reconcile-belief-change kb nil))
  ([kb moved]
   (let [region (when (some? moved) (belief-change-region kb moved))
         before (permuting-marks (reasoning/taxonomy kb))]
     (tax/refresh-beliefs (reasoning/taxonomy kb) (partial jtms/in? (reasoning/tms kb)) region)
     (note-permuting-moves! kb before))))

;; Genuine in-file cycle, threaded through the table.  Three derivation sites live
;; above the table and must reach the choke point below it: the lift's copy, the
;; equality arms' migrated twin and the argument-constraint entailment are all derived
;; sentexes, so all three go through `derived-sentex-added`, and equality and the
;; entailment additionally check `wff-problems` / `wff-violation` — and each of those
;; walks the very table these arms sit in.  The cycle is data-shaped (the table's
;; values are the arm fns), so four declares close it.
(declare derived-sentex-added integrate-twin wff-problems wff-violation)

(defn taxonomy-generations
  "The `genl` and `genlCx` generations with the rebuild epoch (`tax/relation-epoch`), the
  value `conviction-generations` extends with the separations.  `settle` re-asks an entry only when this moves
  from the value the entry records, so the recorded value and the comparison are this one
  function.  The epoch moves at every `recover`, which restarts the generations at 0."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    [(tax/relation-epoch tax) (tax/relation-gen tax :genl) (tax/relation-gen tax :genlCx)]))

(defn conviction-generations
  "`taxonomy-generations` with the separations (`tax/separation-inputs`): the value an
  argument conviction is decided under, a refused lift's and (as
  `chain/constraint-generations`) a refused firing's.  A conviction reads a type the
  taxonomy separates from the declared one, so a separation moving re-asks it."
  [kb]
  (conj (taxonomy-generations kb) (tax/separation-inputs (reasoning/taxonomy kb))))

(defn argument-refusals?
  "Does the refusal record hold a refused firing or a refused lift, each waiting on an
  argument conviction?  Two map reads (`:kinds`)."
  [kb]
  (let [ks (:kinds @(reasoning/refused kb))]
    (boolean (or (seq (:constraint ks)) (seq (:lift ks))))))

;; ---- the refusal record's kind index ----------------------------------------
;; `:kinds` in the refusal record names, per kind, the handles holding an entry of it, and
;; is absent while none does (docs/exceptions.md, "A refused firing is remembered as
;; bindings").

(def ^:private refusal-kinds [:constraint :lift])

(defn- refusal-kind
  "The kind index key refusal entry `e` is named under, or nil for a rule's refused firing."
  [e]
  (some #(when (get e %) %) refusal-kinds))

(defn- update-kind [m kind f k]
  (let [s  (f (get-in m [:kinds kind] #{}) k)
        ks (if (empty? s) (dissoc (:kinds m) kind) (assoc (:kinds m) kind s))]
    (if (empty? ks) (dissoc m :kinds) (assoc m :kinds ks))))

(defn note-kind
  "Refusal record `m` with handle `k` named under entry `e`'s kind."
  [m k e]
  (if-let [kind (refusal-kind e)] (update-kind m kind conj k) m))

(defn drop-kinds
  "Refusal record `m`, from which the entries `gone` have left handle `k`, with `k` no
  longer named under a kind of `gone` that no entry still under `k` holds."
  [m k gone]
  (let [cur (get m k)]
    (reduce (fn [m kind]
              (if (and (set? cur) (some #(get % kind) cur)) m (update-kind m kind disj k)))
            m
            (into #{} (keep refusal-kind) gone))))

(defn forget-kinds
  "Refusal record `m` with handle `k` named under no kind: its entries left together."
  [m k]
  (reduce #(update-kind %1 %2 disj k) m (keys (:kinds m))))

(defn kind-entries
  "Every entry of `kind` in refusal record `m`, as `[handle entry]` pairs, read off the
  sets of the handles the kind index names under `kind`."
  [m kind]
  (for [k (get-in m [:kinds kind])
        :let [cur (get m k)]
        :when (set? cur)
        e cur
        :when (get e kind)]
    [k e]))

(defn advance-refusal-generations!
  "Record the generations now on the `:constraint` and `:lift` entries recorded under the
  generations `before` held (its `:taxonomy`, `:gens` and `:conviction`, read before a
  batch), when a rollback has put the relations and the separations back as they were
  (`tax/relations-match?`).  Generations only grow, so without it the next settle re-asks
  every entry the batch found settled (docs/preview.md, \"What the rollback restores\").
  An entry recorded under other generations stays owed its re-ask."
  [kb {:keys [taxonomy gens conviction]}]
  (let [now  (taxonomy-generations kb)
        conv (conviction-generations kb)]
    (when (and (not= gens now) (= (peek conviction) (peek conv))
               (tax/relations-match? (reasoning/taxonomy kb) taxonomy))
      (let [advance #(condp = (:gens %) gens (assoc % :gens now) conviction (assoc % :gens conv) %)]
        (swap! (reasoning/refused kb)
               (fn [m]
                 (reduce (fn [m k]
                           (let [cur (get m k)]
                             (if (set? cur) (assoc m k (into #{} (map advance) cur)) m)))
                         m (into #{} (mapcat val) (:kinds m)))))))))

(defn- note-pending!
  "Keep `entry` under `k` in the refusal record, in place of any entry `same?` matches.
  The record keeps, beside the rules' refused firings, a lift an argument conviction
  refused, under the source fact whose arrival would otherwise have been its only chance
  (docs/exceptions.md)."
  [kb k entry same?]
  (swap! (reasoning/refused kb)
         (fn [m]
           (let [cur (get m k)]
             (if (= :overflow cur)
               m
               (let [cur (when (set? cur) cur)]
                 (-> (assoc m k (conj (into #{} (remove same?) cur) entry))
                     (drop-kinds k (filter same? cur))
                     (note-kind k entry))))))))

(defn- drop-pending!
  "Retire the entries under `k` that `same?` matches."
  [kb k same?]
  (swap! (reasoning/refused kb)
         (fn [m]
           (let [cur (get m k)]
             (if (set? cur)
               (let [cur' (into #{} (remove same?) cur)]
                 (-> (if (empty? cur') (dissoc m k) (assoc m k cur'))
                     (drop-kinds k (filter same? cur))))
               m)))))

;; ---- the argument constraints, drawn as entailments ----------------------
;; `checks/constraint-entailments` reads what the visible `arg` / `genlArg`
;; declarations *say* about a sentence's arguments; this materializes it, and does so
;; the way the lift below does — as a derived sentex justified by `[the triggering
;; fact, the declaration]`.  That is the whole point: the type is **held** by its
;; supporters rather than merely produced, so retracting either one takes it back and
;; defeating the fact takes it out.
;;
;; Both directions, for the reason the lift has both: a declaration reaching back over
;; facts already stored must reach the same KB as one the facts arrive under, or belief
;; depends on which came first.  `deduce-arg-types` is fact-meets-declaration,
;; `entail-existing` is declaration-meets-facts.

(defn naming-violation
  "The `:naming` violation `sentence` in `context` carries under `kb`'s naming policy, or
  nil: `nm/blocking-problems` as the value a caller that may not throw drops a sentence
  for.  Nil under `:warn` and `:off`."
  [kb sentence context]
  (when-let [ps (nm/blocking-problems (:naming kb) sentence context)]
    {:violation :naming
     :detail    {:message (str "naming invariant: " (str/join "; " ps))}}))

(defn inadmissible
  "The violation that stops `sentence` from being stored in `context`, or nil — naming,
  the definitional constraints, well-formedness, and edge stratification, as one value.

  These hold of any content the engine mints on its own behalf: a `(T x)` can clash with
  a disjoint membership, a `(genl X T)` edge can close a taxonomy cycle or a cycle
  through negation, and a type used at the wrong arity is not a type membership at all.
  Three callers ask it — the argument-type entailment below, the computed `genlCx` edge
  of a context-valued function (`context-nat`), and abduction, which asks it *before*
  minting a hypothesis so that a sentence no assertion could legally make is never one
  the search assumes.  Forward chaining runs the same four over a rule's conclusion in
  `chain/place-conclusion`, the naming arm only where a consequent literal's functor is
  a variable.

  A **value**, never a throw.  Two of its callers run after their triggering sentex is
  stored (that is what gives them a handle to be justified by), and neither may abort
  halfway; the third would rather refuse a hypothesis than fail the query that wanted
  it.

  `constraint-arm` is the definitional-constraint check, `checks/constraint-violation`
  by default, which refuses every violation.  The argument-type mint passes
  `checks/derivation-violation` instead: a mint that clashes with a believed membership is
  placed, and `settle` weighs the pair as it weighs a rule's conclusion that clashes
  (docs/argtypes.md).

  A nil `constraint-arm` omits the arm, for a
  caller that has already run it against this exact content.  The assert path's
  first-level argument-type mints are the one such caller: `checks/entailment-check`
  runs `constraint-problem` (and `cascade-clash`, which reads the source's own
  membership) over every mint of the cascade **before** the trigger is stored, and
  refuses the trigger if any mint fails — so a first-level mint reaching the materializer
  has passed the constraint check already, and storing the trigger and the mints beside
  it only adds memberships, which cannot turn a passing `args`/`disjoint`/`arity` check
  into a failing one (each convicts on an absent type, never a present one).  Naming,
  well-formedness and edge stratification are **not** what `entailment-check` runs, so
  they are asked here whether or not the arm is.  Every other caller — forward
  chaining, the retroactive sweeps, and the cascade's own deeper levels, none of which
  `entailment-check` pre-validates — leaves it false and pays the full check."
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
  "Drop the justifications the one just added as `just` replaces: the same firing over a
  route the witness rule no longer names.  Returns the merged `jtms/drop-justification!`
  results, for the caller to apply to its stores; the dropped records are deleted here.

  A justification is replaced when it has `just`'s informant, consequence, bindings and
  subsumptions (`same-pairing?`), holds every antecedent of `just` outside `route`, and
  differs from it only in `genl` / `genlCx` edges that are all believed.  `route` is
  `just`'s own route handles; nil reads them off the antecedents by shape.  The
  consequence keeps `just`, whose antecedents are groundable, so the sweep collects
  nothing `just` does not hold up.

  An edge of the older route that is OUT keeps its justification: a route a defeat took
  away comes back when the defeat lifts, and the store then holds both
  (docs/nmtms.md, \"Where the layer stops\")."
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

(def ^:private mint-informants
  "The informants an argument declaration's mint is justified under: the kinds
  `entailing-declarations` names, and `resultArg`, whose mint types a reified constant
  off its `natFormula` fact (`checks/result-arg-rows`)."
  (conj (set (keys entailing-declarations)) 'resultArg))

(defn mint-informant?
  "Is `informant` one an argument declaration's mint is justified under?"
  [informant]
  (contains? mint-informants informant))

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

(defn- mint-term
  "The term the mint family files `sentence` under — `x` of a membership `(t x)` or of an
  edge `(genl x t)` — or nil for a shape no membership or edge can make redundant."
  [sentence]
  (when (or (membership-shaped? sentence) (edge-shaped? sentence))
    (second sentence)))

(defn post-mint!
  "File record `h`, holding `sentence` in `context` and concluded by a stored justification
  `mint-informant?` accepts, in `index`'s mint family, when the sentence has a
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
    (when (some #(mint-informant? (:informant (jtms/justification tms %))) (jtms/supports tms h))
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
                    (keep (fn [[c informant]] (when (mint-informant? informant) c)))
                    (:removed-supports removals))
            :when (and (jtms/known-datum? tms h)
                       (not-any? #(mint-informant? (:informant (jtms/justification tms %)))
                                 (jtms/supports tms h)))
            :let [sx (p/get-sentex (:records kb) h)]
            :when sx]
      (retire-mint! kb sx))))

;; Genuine in-file cycle: a minted type draws its own entailments, so `entail-arg-type`
;; calls back into `deduce-placed`, which folds `deduce-arg-types` over it.  Reordering
;; cannot break it — the recursion is the cascade, and its termination argument is in
;; `entail-arg-type`'s docstring.  A second cycle runs through the restatement of a mint
;; spelled at a retired term: `restate-retired-mint` calls `migrate-sentex`, whose twin
;; runs the integration arms (`integrate-twin`), and a declaration arm draws mints through
;; `entail-arg-type`.
(declare deduce-placed restate-retired-mint)

(def ^:private ^:dynamic *admission-memo*
  "nil, or a volatile `{[sentence context checked?] answer}` of what `inadmissible` said of
  a mint, which `entail-arg-type` reads before asking again.  `rederive-mints` binds one
  per call: the facts naming one term draw a handful of distinct mints, each from many of
  them, and the checks read neither the fact nor the justification.  What they read is
  the stored content and belief, so the memo is emptied whenever a mint is created or a
  justification brings one IN; a justification added to a mint already IN moves neither."
  nil)

(defn- entail-arg-type
  "Materialize one entailment: store `(:assert ent)` in `context` and justify it by
  `[src-handle, the declaration, the genl edges it descended through]`.
  `{:new [handle] :violations [v]}` — the handle when the sentex was newly created (the
  caller seeds chaining with it), the violation when it could not be admitted.

  **Every member of `:because`, not just the declaration.**  A declaration on a
  super-predicate reaches this fact through `genl` edges (`checks/edge-support`), and a
  type minted through one is entailed only while that edge holds — so the edges are
  antecedents like the declaration is, and retracting one takes the type back.

  Depth and strength are the lift's: one past the deepest of its supporters, and
  `:monotonic` conferred, because the entailment adds no defeasibility of its own —
  `conferred-class` caps it at the weaker of the fact and the declaration, so a default
  fact yields a default type.  The informant is the declaring predicate, so `why` names
  `arg` beside the two sentexes rather than an anonymous derivation.

  **A minted type draws its own entailments**, and must: the retroactive direction
  cascades whether or not this one does — a declaration arriving over a stored `(t1 x)`
  reaches it through `entail-existing` — so a forward direction that stopped at one
  level would make the two orders disagree.  It recurses only on *progress* (a sentex
  created, or a justification added), which is what bounds it: both are content-keyed
  and monotone within a pass — `find-or-create-sentex` returns the existing handle and
  `has-justification?` refuses a second copy — and the sentences that can be minted are
  a subset of the finite `{(type, term)}` product the KB's own vocabulary spans.  Each
  recursive step therefore consumes one element of a finite set that never shrinks, so
  the cascade closes; the cycle test in `argtype_entail_test` is the check on that."
  [kb ent src-handle context pre-checked?]
  (let [sentence (:assert ent)
        because  (vec (:because ent))
        memo     *admission-memo*
        ask      #(inadmissible kb sentence context
                                (when-not pre-checked? checks/derivation-violation))
        k        [sentence context (boolean pre-checked?)]]
    ;; A type the KB already holds more specifically is not written down: the record
    ;; would say what `(dog Fred)` says, one step less precisely, and subsumption
    ;; answers `(animal Fred)` without it.  Withheld only where there is no record yet
    ;; — an existing one takes the justification whatever else holds it up, or
    ;; retracting the specific membership would leave belief depending on which
    ;; arrived first — and the withdrawal half, for the orders where the specific
    ;; membership arrives last, is `settle`'s (`subsumed-mint-blocks`).
    ;;
    ;; The stored handle is read **once** and both branches share it, where
    ;; `find-or-create-sentex` would look it up a second time: this runs per mint per
    ;; assert, and a mint that dedups to a record already stored is the common case on
    ;; a declared ontology (`assert_cost_test`'s `declared` workload counts the lookup).
    ;;
    ;; A withheld mint is decided before the admission checks, since it stores nothing:
    ;; the checks would only report a violation of a sentence the KB does not hold, and
    ;; their cover arm asks the provers once per cover over the type
    ;; (`withheld-mint-beside-covers`).
    ;; An arity-class membership (`:class`) is no mint: nothing withholds it
    ;; (`unary-entailments`).
    (let [stored (kb/find-sentex-handle kb sentence context)
          class? (:class ent)]
      (if (and (not class?)
               (or (and (not stored) (checks/subsumed-mint kb sentence context))
                   ;; an ingredient an `except` hides from `context`, as a rule firing is
                   ;; not placed there (`except-move-sweeps` drops one the except meets)
                   (when-let [hidden? (exc/except-hidden-fn kb context)]
                     (or (hidden? src-handle) (some hidden? because)))))
        empty-entailment-result
        (if-let [v (if memo
                     (let [m @memo]
                       (if (contains? m k) (get m k) (let [v (ask)] (vswap! memo assoc k v) v)))
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
                (when new? (derived-sentex-added kb s2 h2))
                (let [antes  (into [src-handle] because)
                      depth  (inc (long (reduce max (map #(jtms/depth (reasoning/tms kb) %) antes))))
                      _      (jtms/ensure-node (reasoning/tms kb) h2 depth)
                      fresh? (not (jtms/has-justification? (reasoning/tms kb) (:kind ent) antes h2))
                      ;; `was-in?` records whether `h2` is already believed by another support,
                      ;; read before this justification is added.  It is an O(1) fixpoint read
                      ;; (`jtms/in?`), not an index read, and the cascade below reads it.
                      was-in? (jtms/in? (reasoning/tms kb) h2)]
                  (when (and memo (or new? (and fresh? (not was-in?))))
                    (vreset! memo {}))
                  (when fresh?
                    (let [jid  (p/next-id (:records kb))
                          just (jtms/->just jid (:kind ent) antes h2 {} :monotonic)]
                      (p/put-justification (:records kb) just)
                      (jtms/add-justification (reasoning/tms kb) just)
                      (when-not class? (post-mint! (:index kb) sentence context h2))
                      ;; the route this pair named before is replaced; `just` holds the
                      ;; mint up, so the drop sweeps nothing and only the records go
                      ;; a trigger membership is an ingredient, not a route
                      (when-not new?
                        (drop-replaced-routes! kb just
                                               (cond->> (rest because)
                                                 (:trigger ent) (remove #{(:trigger ent)}))))))
                  (merge-with into
                              {:new (if new? [h2] []) :violations []}
                              ;; A minted sentence materializes its own entailments when it first
                              ;; becomes believed, and re-materializing them adds nothing:
                              ;; `find-or-create-sentex` dedups the sentence and `has-justification?`
                              ;; refuses a duplicate justification.  The cascade therefore recurs only
                              ;; on a transition to believed — a newly created sentex, or a fresh
                              ;; justification that brings an out node in.  An already-believed dedup
                              ;; target (`fresh?` yet `was-in?`) takes the new support without
                              ;; re-querying its own declarations.  The condition is order-independent:
                              ;; whichever arrival first made the type believed ran the cascade once, so
                              ;; the KB holds the same sentexes and justifications either way.
                              (if (or new? (and fresh? (not was-in?)))
                                (deduce-placed kb sentence h2 context)
                                empty-entailment-result)
                              (when new? (restate-retired-mint kb s2))))))))))))

(defn deduce-arg-types
  "Materialize the entailments `checks/constraint-entailments` drew over a sentence
  stored at `handle` in `context` — `{:new [handles] :violations [v]}`.

  Called from both stores of new content — `assert` and forward chaining's
  `place-conclusion` — because what a declaration says about an argument is a claim
  about the predicate, not about how a particular sentence arrived.  Entailing only
  what a caller asserted would make belief depend on arrival order, exactly as lifting
  only asserted content would.

  `pre-checked?` says these entailments already passed the definitional constraint
  check, so each mint's admissibility test skips it (`inadmissible`).  Only the assert
  path passes true, and only for its first level: `checks/entailment-check` validated
  those before the trigger was stored.  The default is false, which every other caller
  takes and which the cascade the materializer walks itself takes — a mint drawn one
  level down was not on `entailment-check`'s pre-store list, so it is checked in full."
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

(defn pair-placements
  "The contexts a mint drawn over the fact `fsx` through the declaration `dsx` (sentexes)
  is placed in, in content order: each maximal context that sees every ingredient of the
  derivation where no `except` hides one (docs/argtypes.md, \"Where a mint is placed\").
  The fact's context when it sees them all, else the maximal common descendants of the
  ingredients' contexts (`tax/maximal-common-descendant-contexts`, the placement of a
  forward firing and of a placed nogood), and empty when no context sees them.

  The ingredients beyond the fact and the declaration join them as a firing's do
  (`chain`'s descent placement): a declaration written of a predicate the fact's functor
  descends to over `genl` edges adds one route's supporters (`tax/general-reach-supports`),
  for each route no other covers, and a trigger declaration adds one trigger's
  (`trigger-alternatives`), for each.  The placements are taken over each combination and
  the most general kept.  While an `except` hides an ingredient somewhere
  (`exc/closure-excepted-anywhere?`), each combination is placed past it
  (`res/exception-aware-placements`)."
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
             (or direct (tax/genl? tax pred via fc))
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
  no `genlCx` edge comes up to `context` (`tax/context-children-global`).  A posting whose
  count (one count read) exceeds `context`'s descendants is read narrowed to the contexts
  that share a descendant with `context`, so a declaration in a context no descendant
  sees is not read.  A `natFormula` fact meets the `resultArg`s written of
  its expression's function, read off their argument root."
  [kb sentence handle context]
  (let [tax  (reasoning/taxonomy kb)
        pred (nm/functor sentence)
        fsx  {:id handle :context context :sentence sentence}]
    (if-not (and (symbol? pred) (seq (tax/context-children-global tax context)))
      []
      (let [idx   (:index kb)
            recs  (:records kb)
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
                     h     (sort (if (<= (reads/stored-count-with-arg-in idx k 1 s p/every-context)
                                         (count @down))
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
             (below-entailments kb sentence handle context)))))

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
                  kb (cond->> (checks/constraint-entailments kb sentence context)
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
    (if-not (and argument/*assertive-arg-types?* sx (nil? (:antecedent sx)) (not (sx/negative? sx)))
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
                         (when (mint-informant? (:informant (jtms/justification tms jid)))
                           ;; the record keeps the antecedents in the order written, the
                           ;; trigger first; the network need not
                           (let [recs (:records kb)
                                 j    (p/get-justification recs jid)]
                             (and j (= h (first (:antecedents j)))
                                  (not (owed [(:informant j) (set (:antecedents j))
                                              (some-> (p/get-sentex recs (:consequence j))
                                                      sx/sentence-of)])))))))
               (sort (jtms/dependents tms h)))]))))

(defn- retroactive-mints
  "The entailments a newly stored declaration `dh` draws over one already-stored sentex
  `sx`, materialized at each placement of the pair (`placements`, a fn of `sx`'s context;
  `placements-of` by default).

  The stored sentex is put back through `checks/declaration-entailments`, which is
  `checks/constraint-entailments` narrowed to this declaration, rather than the
  conditions being re-decided here: the two directions must agree about what a
  declaration entails, and the only way to be sure of that is for them to ask the same
  function.

  A genuine negation is not argument-checked, so it entails nothing; nor does a rule,
  whose stored sentence is an implication; nor does an inert sentex (`inert-handle?`),
  which claims nothing and never revives.  The fact-side path draws no mint from an inert
  fact, so a sweep that read one would mint on a rechain, or on a context edge, what the
  load did not."
  ([kb sx dh] (retroactive-mints kb sx dh (placements-of kb dh)))
  ([kb sx dh placements]
   (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)) (not (inert-handle? kb (:id sx))))
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
  "Every **stored** sentex whose functor is `pred` or any spec of it — the extent a
  declaration or a mark written of `pred` binds, since a `genl` edge between predicates
  says the sub's tuples *are* the super's.  The four retroactive arms read it: a
  declaration meeting the facts, a mark meeting them, and each of those met by an edge
  instead.

  Stored rather than believed, for `lift-existing`'s reason, which every caller repeats:
  content derived off a defeated fact is defeated with it, where skipping the fact would
  leave the derivation missing when it revives — belief depending on the order the defeat
  and the declaration arrived in.

  **Filtered by index cardinality before anything is read.**  `genl` is the commonest
  edge in an ontology, so a spec subtree is routinely most of the vocabulary while only a
  little of it holds facts — and the walk without the filter costs a posting-list read
  and a record fetch per handle for every predicate in the subtree, whether or not it has
  one.  A predicate with nothing stored has nothing to constrain, and asking is one
  count.  What is left to pay per edge is that count per spec, against the whole
  subtree's extent without it.

  A vector, snapshotted before the caller's first write: a mint or a merge posts to the
  roots this walk reads, and no index backend promises whether a posting read is a
  snapshot or a live collection.

  With `limit`, the walk stops after `limit` sentexes, visiting the predicates in content
  order and each posting in the index's own order, so a budgeted caller reads a prefix
  and no more of the extent.  With `contexts`, a set, only the sentexes stated in one of
  them are read (`reads/as-stored-with-functor-in`)."
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
  naming `T` (`unary-entailments`).  No mint informant (`mint-informant?`): the membership
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
  "Does the moved binding `[kind value]` admit a length other than one?"
  [[kind v]]
  (case kind :exact (not= 1 v) :min (< 1 (long v)) true))

(defn withdrawn-type-mints
  "The mint justifications to drop for each type `t` of `bound` (`arity/drain!`'s
  `:bound`) whose moved bindings admit another length and whose length no longer admits
  one (`arity/mintable-type?`): those concluding a membership `(t x)` or an edge `(genl x
  t)`.  A declaration meeting its fact while `t` is bound to another length mints nothing,
  so the store then holds what the order with the binding first holds; a record with
  other support stays.  Returns the justification ids, for the caller to drop.  Reads
  nothing more while the mint family is empty, and reads `t`'s one-argument tuples
  alone, so a binary predicate's extent is not read.  Every context, since `t`'s length
  holds at every context (`arity/relation-length`)."
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
                    :when (mint-informant? (:informant (jtms/justification tms jid)))]
                jid))))))

;; ---- a mint the KB holds more specifically ---------------------------------
;; `checks/subsumed-mint` reads whether a minted type is one a believed record already
;; says more precisely.  The mint path above withholds a record it answers for; the
;; settle takes care of the other two directions, which are the functions below:
;;
;; - **withdrawal** — the specific membership, or the edge that makes it specific or
;;   visible, lands after the mint is stored, so the record has to *leave*
;;   (`subsumed-mint-blocks`);
;; - **release** — a record that could have been what subsumed a mint leaves belief or
;;   the store, so the mints about its term are drawn again (`withheld-releases`).
;;
;; A withdrawal is a **block**, not a retraction: the mint's supporters are all still
;; there and still entail it, so a dependency-directed retraction finds it groundable
;; and keeps it (`jtms/retract!`).  Blocking the justification is what `exceptWhen`
;; does to a firing it excepts, and the sweep that follows collects the record exactly
;; as it collects an excepted conclusion (docs/exceptions.md).
;;
;; Nothing remembers a withheld mint.  The release re-derives it from the facts about the
;; departing record's term, which is what the store says, so a KB rebuilt from its store
;; releases what the KB that withheld it releases (docs/argtypes.md).

(defn- mint-only?
  "Is `h` a record the argument entailment alone holds up — no premise support, at least
  one justification, and every one of them an argument declaration's?

  A record an author asserted, or a rule concluded, is not this feature's to withdraw:
  the mint may be redundant, but the record is somebody else's claim.

  Read off the **network**, which keeps each justification's informant, rather than off
  the store: this is asked of every candidate the trigger turns up, and fetching a record
  per justification to read one field of it is the cost `record_fetch_cost_test` counts."
  [kb h]
  (let [tms (reasoning/tms kb)]
    (and (not (jtms/premise? tms h))
         (let [js (keep #(jtms/justification tms %) (jtms/supports tms h))]
           (and (seq js) (every? #(mint-informants (:informant %)) js))))))

(defn- rests-on?
  "Does the support of `h` reach `mint` — is the membership that would make `mint`
  redundant itself derived from it?

  The one shape a block cannot take: withdrawing the mint would take the membership with
  it, which would release the mint, which would derive the membership again.  The walk is
  the support closure, each node visited once; the shipped ontology has no such pair, and
  a KB that writes one keeps both records."
  [kb h mint]
  (let [tms (reasoning/tms kb)]
    (loop [seen #{} frontier [h]]
      (if-let [x (peek frontier)]
        (let [antes (into [] (comp (keep #(jtms/justification tms %))
                                   (mapcat :antecedents)
                                   (remove seen))
                          (jtms/supports tms x))]
          (if (some #(= mint %) antes)
            true
            (recur (into seen antes) (into (pop frontier) antes))))
        false))))

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
                 (not= (nm/functor s) (nm/functor sentence))
                 (tax/genl? tax (nm/functor s) (nm/functor sentence) context))

            (and (edge-shaped? sentence) (edge-shaped? s))
            (and (= (nth sentence 1) (nth s 1))
                 (not= (nth s 2) (nth sentence 2))
                 (tax/genl? tax (nth s 2) (nth sentence 2) context)))))))

(defn- withdrawable-mint
  "The handle of the record that makes the mint at `h` redundant, or nil when the mint
  stays.  `by` is the moved record the trigger holds when that record is the only one that
  can be the subsumer (a membership, or an edge out of the mint's own term), and nil when
  the subsumer is some other record the move made reach further, which
  `checks/subsumed-mint` then finds.

  Three conditions, cheapest first: the candidate is not `by` itself; it is the
  entailment's own record (`mint-only?`, network reads); and a believed record that does
  not rest on it says it more specifically in its own context (the taxonomy, or the index
  behind `subsumed-mint`, then a support walk per subsumer, so a subsumer resting on the
  mint does not hide one that does not; docs/argtypes.md)."
  [kb h by]
  (when (and (not= h (:id by)) (mint-only? kb h))
    (let [sx (p/get-sentex (:records kb) h)]
      (when (and sx (nil? (:antecedent sx)))
        (if by
          (when (and (says-more-than? kb (:sentence sx) (:context sx) by)
                     (not (rests-on? kb (:id by) h)))
            (:id by))
          (checks/subsumed-mint kb (:sentence sx) (:context sx) #(not (rests-on? kb % h))))))))

(defn- mint-members-in
  "The terms some mint is about that hold a stored membership `(z x)` with `z` in `below`,
  a spec closure — the members `subtree-sentexes` would name, narrowed to the mint family.

  Read from the smaller side.  The extent below a type the ontology states an edge out of
  can be most of a corpus while the terms holding a mint are few, and walking the extent
  pages one record per membership to learn its term; walking the mint terms pages only each
  term's own unary facts (`reads/as-stored-unary-with-arg-global`), so the choice is made by comparing
  the two counts, both index cardinality reads.  Stored rather than believed, as
  `subtree-sentexes` is."
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

(defn- withdrawal-candidates
  "The minted records that `sx` — a sentex this settle moved — can have made redundant, as
  `[handle by]` pairs for `withdrawable-mint`, read off the mint family.

  - A **membership** `(T x)` subsumes the mints about `x`.
  - A **`genl` edge** `(genl sub super)` subsumes the edges minted out of `sub` itself.
    The route it gives the types and members under `sub` is `edge-route-candidates`',
    asked once for every edge the settle moved.
  - A **`genlCx` edge** shows every context under `sub` what `super` holds, so the mints
    stated in those contexts are asked the whole question.  The contexts are read off
    whichever of the mints' contexts and `sub`'s descendants is fewer: each mint context
    that sees `sub`, or `tax/context-down` of `sub`, which filters every descendant by
    what it sees.  A `recover` moves every `genlCx` edge, and a lattice
    where most contexts sit under a few holds far more descendants than mint contexts.
    The unscoped `tax/context-down-global` is read for its size alone, to pick the
    side; it is not scoped because it answers nothing, and both sides are.

  A fact of any other shape moves no subsumption and reads nothing."
  [kb sx]
  (let [s   (:sentence sx)
        idx (:index kb)]
    (cond
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
          [h nil])))))

(defn- edge-route-candidates
  "The mints the `genl` edges the records in `edges` install (`tax/installed-edges`: a `genl`
  edge, or a cover's edge per part) gave a route they did not have, as `[handle nil]`
  pairs: the mints about every type strictly under an edge's `sub`, and about every
  member of a type under one.  Each is asked the whole
  question, since the record that subsumes it is the membership or edge below, not the
  edge that moved.

  **One walk for all the edges.**  Asked per edge, the types under each `sub` are a
  closure of their own, and a settle that moves every edge at once — a `recover`, where
  every record comes IN — pays the sum of those closures, which counts a subtree once per
  edge above it rather than once.  The union is `tax/specs-of-all`, one traversal, and the
  members below it one read from whichever of the mint terms and the extent is smaller.  A
  single edge keeps `tax/specs-global` and its memo.

  \"Strictly\" is per edge: a `sub` counts when it sits under another edge's `sub`, which
  its own ancestors (`tax/genls-global`) answer, and only a `sub` holding a mint is asked.

  Unscoped (E17) for `checks/subsumed-mint`'s reason: the mints sit in contexts other than
  the edges', and each candidate is asked in its own context, so the unscoped walk only
  asks more candidates than a scoped one.

  A part of a declaration is asked about its own mints as well: the edge a declaration installs out
  of a part subsumes the edges minted out of that part, as a stated `genl` edge does, and
  no `[handle by]` pair names it, since `says-more-than?` reads a `genl` edge alone."
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
  `entail-under-edge` reads this before it walks a subtree.

  A `(genl sub super)` edge draws a new type over `sub`'s facts only through a
  declaration the edge is itself a support of: `checks/edge-support` cites the arriving
  edge in the mint's `:because`, so a route that does not run through the edge
  deduplicates against one that already held and adds nothing (`has-justification?`).  A
  route that does run through it reaches its declaring predicate `D` as
  `fact-functor →* sub → super →* D`, so `D` is a genl-ancestor of `super`.  When no
  ancestor of `super` declares, the edge mints and justifies nothing, and the subtree
  read is skipped.

  **`genls-global`, not the scoped `genls`** (E17): `entail-under-edge` sweeps stored
  sentexes across every context the subtree spans, so there is no one vantage to scope
  to, and the presence check must over-approximate in the direction the answer is — a
  declaration this edge cannot see from one context still mints a required justification
  in another that can, so a scoped check that returned false there would drop it, where a
  spare true only reads a subtree that yields nothing.  Read through the same global
  declaration set (`tax/arg-declaration-props`) `res/constraining-predicates` filters
  against, so the check and the reader it guards cannot disagree about which predicates
  declare."
  [kb super]
  (and (symbol? super)
       (let [tax (reasoning/taxonomy kb)]
         ;; per kind's `:props` set, so the check builds no union of every declaring predicate
         (boolean (some #(tax/genls-global-meets? tax super (tax/props tax (tax/arg-declaration-props %)))
                        (keys entailing-declarations))))))

(defn surplus-placements
  "The mint justifications, in id order, that a `genlCx` edge among `edges` (sentexes)
  left at a context that is no longer a placement of their fact and declaration
  (`pair-placements`).  An edge arriving can give the two a more general common
  descendant, and the placement under it then goes, so the store holds the same mints in
  every arrival order.  Every placement an edge can displace lies under its `sub`, and the
  mints stated there are read off the mint family (`withdrawal-candidates`).  A
  justification at its fact's own context is not asked: that context sees the
  declaration while the `genlCx` edges the justification names hold.  The caller checks
  the two preconditions: the entailment on and the mint family holding a record."
  [kb edges]
  (when (seq edges)
    (let [tms (reasoning/tms kb)
          cx  (fn [h] (:context (p/get-sentex (:records kb) h)))]
      (into (sorted-set)
            (for [e     edges
                  [h _] (withdrawal-candidates kb e)
                  :let  [c (cx h)]
                  jid   (jtms/supports tms h)
                  :let  [j (jtms/justification tms jid)]
                  :when (and j (mint-informant? (:informant j)))
                  :let  [[f d] (:antecedents j)
                         fc    (cx f)]
                  :when (and fc (not= c fc)
                             (not-any? #{c} (placements-of-pair kb f d)))]
              jid)))))

(defn descent-surplus-placements
  "The mint justifications, in id order, that a record among `moved` left at a context
  that is no longer a placement of their fact and declaration (`pair-placements`): a
  `genl` route or a trigger membership stated in a more general context than the one a
  placement descended to places the pair above it, and the placement below goes, as
  `surplus-placements` drops one a `genlCx` edge displaced.

  - A record that installs `genl` edges (`tax/installed-edges`) whose `super` reaches a
    declaration (`super-reaches-declaration?`) reads the facts of its `sub`s' spec
    subtrees, the extent `entail-under-edge` drew over.
  - A membership `(T x)` whose `T` reaches a trigger type (`trigger-types`) reads the
    facts naming `x`, the facts `trigger-entailments` drew over.

  Each fact's mint justifications are read off the network (`jtms/dependents`).  The
  trigger types are reached through `tax/genls-global` (E17), as `trigger-entailments`
  reaches them: the facts are read across every context, and each justification is asked
  its own pair's placements, so the unscoped presence check only reads more facts."
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
                    :when (and j (mint-informant? (:informant j))
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
  "The justifications to block because the records they hold up are redundant, and the
  records — `{:blocked #{jid} :withdrawn #{handle}}` over the records the sentexes in
  `moved` can have displaced.

  Every justification of a withdrawn record, because a record survives on any one of
  them: two facts can entail the same type, and blocking one would leave the record
  standing on the other, so how many facts happened to entail it would decide whether it
  stayed.

  `moved` is a **delay** over the region's records, and the checks in front of it decide
  whether it is ever forced: off unless the entailment is on, off unless the mint is
  prunable, and off while the mint family is empty.  A KB holding no mint therefore
  fetches no record here however much it asserts, which is what `record_fetch_cost_test`
  counts.  Forced, the region is filtered by **shape** (`subsumer-shaped?`) and the
  candidates are the mint family's (`withdrawal-candidates` per record,
  `edge-route-candidates` once for all the `genl` edges the records install), so a
  membership about a term holding no mint reads nothing.

  Only a record that **became** believed is asked, which is what keeps this off the price
  of a settle that relabels a large region without moving much of it — a qualitative
  network relabels its whole network per fact and moves a handful of nodes.

  The records a retraction left standing on a derivation alone (`note-unpremised!`) are
  asked too, each the whole question.

  A `genlCx` edge among the moved records is also asked which mint placements it
  displaced (`surplus-placements`), with pruning on or off; those justifications are
  returned under `:surplus`, for the settle to drop.

  `asked` is the settle's own record of which of them it has already put this question to,
  and a record is asked **once per settle** however many passes relabel it.  Nothing is
  missed by that: a mint stored *after* a pass examined its subsumer never reaches the
  store, since `entail-arg-type` asks the same question of every mint it is about to
  write.  `believed?` is belief now, `jtms/in?` or own-context belief.  With `routes?`,
  a `genl` edge or a trigger membership among them is asked the same of the placements it
  displaced (`descent-surplus-placements`).

  `whole` is the region's size when the region is the whole store (a `recover`), else
  nil.  With fewer mints stored than that, `moved` is never forced: each stored mint is
  asked the whole question, and the `genlCx` edges are read off the index."
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
                                      (reads/as-stored-with-functor idx 'genlCx)))
                        (filter #(and (ask? %) (subsumer-shaped? (:sentence %))) @moved))))
        surplus (into (or (surplus-placements kb (filter #(context-edge-shaped? (:sentence %)) moved))
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
        (concat (if each?
                  (map (fn [h] [h nil])
                       (mapcat #(reads/as-stored-mints-in idx %)
                               (reads/as-stored-mint-contexts-global idx)))
                  (concat (mapcat #(distinct (withdrawal-candidates kb %)) moved)
                          (edge-route-candidates
                           kb (filter #(seq (tax/installed-edges (:sentence %))) moved))))
                (map (fn [h] [h nil]) lost))))
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
  support from the same declaring predicate over the same antecedents, and when it is not
  stored and a believed record still subsumes it (`checks/subsumed-mint`), withheld
  again.  The two questions `entail-arg-type` asks after its checks, asked first."
  [kb ent src context]
  (boolean
   (if-let [h (kb/find-sentex-handle kb (:assert ent) context)]
     (jtms/has-justification? (reasoning/tms kb) (:kind ent)
                              (into [src] (:because ent)) h)
     (checks/subsumed-mint kb (:assert ent) context))))

(defn- rederive-mints
  "Draw again the mints of each stored fact in `facts` that `keep?` accepts, as
  `deduce-placed` draws them for the fact arriving now: `{:new [handle …]}`.
  `keep?` takes the minted sentence and its placement.  An inert fact (`assert-inert`) is
  no TMS datum and draws no mint.

  A mint already stored with this justification adds nothing (`has-justification?`), one
  a believed record still subsumes is withheld again, and the rest are written — so the
  call is idempotent and decides on current belief alone.  The violations are dropped:
  each was reported when the fact arrived, and a re-derivation exposes nothing new.

  Which is why an entailment whose mint would not change is skipped before
  `entail-arg-type` sees it (`unchanged-mint?`): one already holding this justification,
  or one still withheld.  There it would pass the admissibility checks only to write
  nothing and cascade nothing, and a failed check is a violation this drops.  The checks
  are the cost of a mint, and a recover's settle asks them of every mint about each
  released term.  The facts naming one term draw few distinct mints, each from many
  facts, so the checks' answers are held for the call (`*admission-memo*`)."
  [kb facts keep?]
  (with-recheck-reads
    (binding [*admission-memo* (volatile! {})]
      ;; each fact naming the term adds one support to the same mints, which a dedup
      ;; question without the cache answers by scanning every support already added
      (jtms/with-dedup-cache (reasoning/tms kb)
        (reduce (fn [acc sx]
                  (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx))
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
  placement under its `sub`: `{:new [handle …] :violations [v …]}`.

  The edge's arrival left such a placement below a more general one, which the settle
  dropped (`surplus-placements`), and that general placement lies in a context a reader
  under `sub` saw only through the edge (`context-move`'s `:moved`).  So the pairs are
  read off the mint family in those contexts, each mint justification placed below its
  fact's context naming its fact and declaration, and the cost is the mints the edge
  reaches.  A pair whose fact is stated outside `:seen` gains no placement under `sub`, so
  the pairs are read only when `:seen` meets `:up`, and only those with a fact in `:seen`
  are kept.

  With subsumed mints pruned, a placement there can be withheld instead: the believed
  records stored there that can subsume a mint release the terms they name, as their
  departure would (`released-terms`), and the facts stored under `sub` draw their mints
  again.  A released mint is placed in a context of `:under` and its fact is stated in a
  context of `:seen`, so only those facts draw, keeping only those placements.  The facts
  above `:under` are read from the smaller side by index counts: the records stored in
  `:moved`, through the terms they release, or every fact stored in `:seen` outside
  `:under`.

  Off unless `*assertive-arg-types?*`, some predicate declares, and pruning is on or a mint
  is stored in any context: the check counts every context's mints, since the move reaches
  readers under any of them."
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
                            :when (and j (mint-informant? (:informant j)))
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
                        (not (believed? (:id sx))))))
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
  justifications a withheld mint owes a record of its sentence that arrived: `{:new
  [handle …]}`, drawn by `rederive-mints` (docs/argtypes.md, \"Nothing records a withheld
  mint\").  Pruning only; a `genlCx` edge's departure is the drain's
  (`departed-context-edge-mints`).  Under `*release-withheld?*` false the departures and
  arrivals are kept owed (`owe-releases!`) and nothing is drawn.

  The departures are the records `note-departure!` queued as they left the store, and the
  records in `moved` (a delay over the settle's region) that went IN ⇒ OUT against
  `was-in`; the arrivals are the ones that came IN.  `believed?` is belief now.
  `withdrawn` holds the mints this settle withdrew, which release nothing.  `asked` holds
  what this settle has already asked, so each record is asked once per settle however
  many passes relabel it.  The queue is drained whether or not the checks pass.

  A departure is read again when its term's turn comes, and a term whose departures are
  all stored as they were and believed again is not re-drawn: re-drawing the terms before
  it adds justifications, and the relabel that follows can bring a departure back IN, so
  that what it subsumed is withheld still.  A term is re-drawn only for the mints one of
  its departures out could have withheld (`may-release`): a membership leaving releases
  the memberships of its type and the types above it, and no other mint about its term."
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
            out   (-> []
                      (into (remove #(or (contains? withdrawn (:id %)) (not (mover? (:sentence %))))) queued)
                      (into (remove #(believed? (:id %))) moves))
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

(defn- entail-over
  "Draw the entailments of each stored literal fact in `facts` at their placements, as
  `deduce-placed` draws them for a fact arriving now: `{:new :violations}`.  With
  `kinds`, only the entailments of those declaring functors."
  ([kb facts] (entail-over kb facts nil))
  ([kb facts kinds]
   (reduce (fn [acc sx]
             (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
               acc
               (merge-with into acc
                           (deduce-placed kb (:sentence sx) (:id sx) (:context sx)
                                          (when kinds (fn [e _] (contains? kinds (:kind e))))))))
           empty-entailment-result
           facts)))

(defn entail-under-edge
  "When a `(genl sub super)` edge arrives, draw what the declarations on `super` now say
  about the `(sub …)` sentexes **already stored** — the third arrival order of the same
  three ingredients, and there for the reason `subsumption-seeds` beside it is.  A
  `covering`, `separating` or `partition` installs an edge per part
  (`tax/installed-edges`), and each of those edges is read as an arriving `genl` edge.

  A constraint descends the predicate hierarchy, so the fact, the declaration and the
  **edge** are all ingredients of one entailment.  `deduce-arg-types` covers the fact
  arriving last and `entail-existing` the declaration arriving last; without this, the
  edge arriving last mints nothing and the same three sentences leave the KB holding a
  type in two orders out of three.  nil when `sentence` installs no edge.

  The whole **spec subtree** of `sub`, because subsumption is transitive: an edge at the
  top of a predicate hierarchy brings every predicate below it under the declarations
  above it.  Each stored sentex is put back through `checks/constraint-entailments` in
  its own context — the same function the other two directions ask, so the three cannot
  disagree — and the mints deduplicate on content, so a fact whose type was already
  entailed by a route that survives contributes a justification and no second record.

  **Three checks in front of the subtree, because this arm fires on a `genl` edge** — the
  commonest thing an ontology says, where the other two fire on a declaration.  Off
  unless `*assertive-arg-types?*`, since with the entailment off there is nothing to mint
  and the edge's other consequences are `subsumption-seeds`'; off unless some predicate
  carries an entailing declaration (`any-declaring?`, the taxonomy's `:props` sets, no
  index read); and off unless a genl-ancestor of `super` carries one
  (`super-reaches-declaration?`).  The first two
  keep an edge under a predicate nobody constrained from reading a subtree's extent to
  discover there was nothing to draw; the third keeps an edge whose `sub` is constrained
  but whose `super` reaches no declaration from reading it, since every mint this arm
  draws cites the arriving edge and so reaches its declaring predicate through `super`.
  The extent itself is `subtree-sentexes`, filtered by cardinality for the same reason
  one step further in."
  [kb sentence]
  (when-let [edges (when-let [es (and argument/*assertive-arg-types?* (seq (tax/installed-edges sentence)))]
                     (when (any-declaring? kb)
                       (seq (filter (fn [[sub super]]
                                      (and (symbol? sub) (super-reaches-declaration? kb super)))
                                    es))))]
    (reduce (fn [acc sx]
              (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
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
                  :when (and dsx (nil? (:antecedent dsx)) (not (sx/negative? dsx))
                             (= (entailing-declarations k) (nm/arity (:sentence dsx)))
                             (symbol? (second (:sentence dsx))))]
              dsx))))

(def ^:dynamic *entail-moves?*
  "False while a `*bulk-load?*` write settles: the drain draws no argument types over the
  facts a `genlCx` move shows (`entail-under-context-edge`).  `record-arg-types` draws them
  after the load."
  true)

(defn entail-under-context-edge
  "When the `genlCx` move `m` (`context-move`) shows contexts, draw what the declarations
  it makes visible say about the facts **already stored** in `sub` and every context under it — the fourth
  arrival order of an entailment through an inherited declaration, beside the fact, the
  declaration and the `genl` edge.  Each derivation names the `genlCx` edges it sees its
  declaration through (`checks/entailment-support`), so retracting this edge takes back
  what rests on it, and `rederive-descended` draws again what a second route still
  reaches.

  The edge also gives a fact and a declaration a new common descendant, under `sub`, when
  one of them is stated where `super` sees it and the other in a context a context under
  `sub` sees and `super` does not (`below`: `context-move`'s `:under` and `:below`).  The
  facts are read from every context of `below`, and each draws at its placements
  (`deduce-placed`); the declarations stated in `below` draw over the facts stated in a
  context a reader under `sub` sees through the edge alone (`:moved`), since a fact the
  reader already saw has its placements already (`declarations-meeting`).  A placement the edge
  leaves below a more general one is dropped by the settle (`surplus-placements`).

  Off unless `*assertive-arg-types?*` and `*entail-moves?*` hold and some predicate
  declares.  Off too when no context of `m`'s `:moved` stores a sentex older than the
  `:floor` (any sentex, without one): every reader under `sub` then sees the content it
  saw before the move, so no fact meets a new ingredient (`lein perf`'s
  `genlcx-edge-showing-an-empty-context`).  The facts are read from the smaller of two sides, compared by index counts: the facts stored in the
  contexts of `below`, kept when a declaration reaches their functor, or the extent in
  `below` of each functor a declaration reaches (`reads/as-stored-with-functor-in`),
  priced at the lesser of the declared extent and one probe per functor and context.  So
  the fact half costs the lesser of the edge's extent and the declared extent, and a
  context holding many undeclared facts or a KB holding many declared ones elsewhere
  costs only the other.
  Snapshotted before the first mint.  With `m`'s `:floor` (`seed-floor`), a fact or a
  declaration stored at or above it arrived with the edge in the taxonomy and drew its
  entailments then (`deduce-arg-types`, `entail-existing`), so neither half reads it.
  With `m`'s `:entailed` (a volatile set of handles, one per drain, `drain-moves!`), a
  fact an earlier move of the drain drew is not drawn again: every move of a drain reads
  one taxonomy, and `deduce-placed` reads no move."
  [kb m]
  (when (and argument/*assertive-arg-types?*
             *entail-moves?*
             (symbol? (first (:edge m)))
             (any-declaring? kb))
    (let [recs    (:records kb)
          idx     (:index kb)
          before? (if-let [f (:floor m)] #(< (long %) (long f)) (constantly true))]
      (when (some #(and (pos? (reads/stored-count-in-context idx %))
                        (some before? (reads/as-stored-in-context idx %)))
                  (:moved m))
        (let [below (into @(:under m) @(:below m))
              ctxs  (nm/sort-by-content-key nm/name-key compare below)
              by-cx (reduce + 0 (map #(reads/stored-count-in-context idx %) ctxs))
              ;; a `sub` storing nothing below it reads no declared functor
              fs    (if (zero? by-cx) [] (declared-functors kb))
              ;; the functor side reads each functor's extent in `below` alone, so it costs
              ;; at most its extent and at most one probe per functor and context
              by-fn (min (reduce + 0 (map #(reads/stored-count-with-functor idx %) fs))
                         (* (count fs) (count ctxs)))
              facts (if (<= by-cx by-fn)
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
                              fs)))]
          (let [done  (:entailed m)
                facts (if done (into [] (remove #(contains? @done (:id %))) facts) facts)]
            (some-> done (vswap! into (map :id) facts))
            (merge-with into (entail-over kb facts)
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
  type under `sub` (`released-terms`).  Each such fact is put back through
  `checks/constraint-entailments` in its own context, narrowed to the trigger kinds, so
  the derivation names the membership and its route as the fact's own arrival would.

  The facts are read from the smaller of two sides, compared by index counts: the
  postings naming a term, kept when a trigger declaration reaches their functor, or the
  facts of those functors, kept when they name one of the terms, read once for every term
  whose postings outnumber them.  So a membership beside many declared facts that do not
  name its term reads only the term's postings.

  The trigger types are reached through `tax/genls-global` (E17): the facts are read
  across every context they are stored in, and each is asked its own context's
  declarations and memberships, so the unscoped presence check only reads more facts."
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

(defn record-arg-types
  "Record the argument-type entailments every stored fact draws, over a store whose facts
  were written without them: `{:facts n :new [handle …] :violations [v …]}`.

  `assert` draws them as each fact arrives.  A store loaded around that path — a dump
  import, `*bulk-load?*`, `bulk-assert-facts!` — holds the facts and none of their
  derived memberships and edges, and `recover` rebuilds belief from the stored
  justifications without drawing any.  This is the one pass that records them, so the
  store then holds what a per-fact load of the same facts holds.  Run it once, after the
  load and after the store is recovered or reindexed, since the declarations and the
  hierarchy they name are read from the taxonomy.

  Facts are read per declared functor, every predicate under an entailing declaration
  in content order, and each fact is asked once whatever number of declarations reach
  it.  Idempotent: a derivation already recorded adds nothing (`has-justification?`)."
  [kb]
  (if-not argument/*assertive-arg-types?*
    (assoc empty-entailment-result :facts 0)
    (let [idx   (:index kb)
          recs  (:records kb)
          facts (into []
                      (comp (mapcat #(reads/as-stored-with-functor idx %))
                            (distinct)
                            (keep #(p/get-sentex recs %)))
                      (declared-functors kb))]
      (assoc (entail-over kb facts) :facts (count facts)))))

;; ---- definitional collection relations, expanded into forward rules -------
;; `(defnNecessary Coll C)` / `(defnSufficient Coll C)` / `(defnIff Coll C)` tie a
;; collection's membership to a condition on the member `?x` (docs/defns.md).  The
;; `defn*` fact is stored like any other; what it *means* is materialized here the way
;; `deduce-lift` materializes a decontextualized copy — as derived content justified by
;; the fact, so it inherits belief, retraction and placement for free.  The derived
;; content is a **rule** rather than a fact, so this is the mint path `chain/mint-rule`
;; takes for a generator, minus the join bindings: index it, node it, justify it once.
;;
;; Open-world only.  `defnSufficient` concludes membership from the condition and
;; `defnNecessary` the condition from membership; neither expands the collection's
;; *complement* — nothing concludes a non-member from the condition's failure, which is
;; closed-world membership completion and stated as an absence in docs/defns.md.

(defn- materialize-defn-rule
  "Store one companion rule `r` (polycanonicalized into one rule per conjunct of a
  conjunctive necessary consequent, and per alternative of a disjunctive condition, by
  `rules/expand-rule`) as a derived rule sentex in `context`,
  justified by `[defn-handle]` under `informant`.

  The mint a generator makes, minus the bindings: index the rule
  (`index-rule-sentex`), give it a node one past the `defn*` fact's, and add the
  justification once (`has-justification?` keeps a re-assert of the same `defn*` from
  duplicating it).  `{:new [handles] :violations [v]}` — the new handles the caller
  seeds chaining with, and a rule that could not be admitted, reported rather than
  thrown for the derivation path's reason.  A rule the `:arg-variable` arm convicts is
  stored and held inert (`checks/hold-rule-conviction!`)."
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
  "Materialize the forward rule(s) a `defn*` fact stored at `defn-handle` in `context`
  expands into (`sx/defn-companion-rules`), each a derived rule sentex justified by the
  `defn*` fact alone.  `{:new [handles] :violations [v]}` — the new rule handles the
  caller seeds chaining with (so a rule fires over the facts already stored), and any
  rule that could not be admitted.

  Called from `assert-one` once the `defn*` fact has a handle to be justified by.  A
  non-`defn*` sentence returns the empty result, so the caller pays one `defn-sentence?`
  read and stops — the presence check that keeps every ordinary assert free of it."
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
  answers, for the antecedent keys `rule-keys` (`reads/as-stored-rule-keys`) — each
  re-join family of `chain/fire-rules-for` named by the facts it reacts to.

  - The predicates a `SupportingProver` reads, when some antecedent is one such a prover
    answers: a unit table decides a `quantityGreaterThan`.
  - A registered calculus's trigger predicates, when some antecedent is on a predicate
    the calculus answers: two `nonTangentialProperPart` facts entail a `partOfRegion`.
  - `transitive`, and the partners an `inverse` records hops on, when some antecedent is
    on a declared-transitive predicate: the declaration turns the walk on, and a
    partner's fact is a hop of it.
  - The declarations and relations a preservation reads (`inherit/licensing-functors`).

  Each family is read against `rule-keys` by membership, so the cost is the families' size
  and not the size of `rule-keys`.

  The marks are read unscoped: a re-join family is a trigger over every reader, and
  each re-join reads its rule from the rule's own context."
  [kb tx rule-keys]
  (let [ruled? #(contains? rule-keys %)
        walked (filter ruled? (tax/props tx :transitive))]
    (-> #{}
        (cond-> (some ruled? (provers/support-answered-preds kb))
          (into (provers/support-source-preds kb)))
        (into (comp (filter #(some ruled? (:predicates %))) (mapcat :trigger-predicates))
              (qkb/registered-calculi kb))
        (cond-> (seq walked)
          (-> (conj 'transitive)
              (into (mapcat #(tax/inverses-under tx %)) walked)))
        (into (inherit/licensing-functors kb rule-keys)))))

(defn- genl-inverse-edges
  "The `[sub super]` pair a `(genlInverse sub super)` sentence adds to the signed closure,
  as `tax/installed-edges` names a `genl` edge's; none for any other sentence."
  [sentence]
  (when (and (seq? sentence) (= 'genlInverse (nm/functor sentence)) (= 3 (count sentence))
             (symbol? (nth sentence 1)))
    [[(nth sentence 1) (nth sentence 2)]]))

(defn- rule-reads-above?
  "Does a stored rule read a term at or above `super`: an antecedent on one, off the
  antecedent keys (`reads/as-stored-rule-keys`), or an antecedent a re-join family moves
  when a fact on one arrives (`licensing-functors`)?  These are the readers whose answer a
  fact below a `(genl sub super)` edge changes.  False off one set read on a KB with no
  rule.  The
  closure is global, as the seeds it filters are: a context seeing more edges reaches more
  of `super`'s supertypes."
  [kb tax super]
  (let [rule-keys (reads/as-stored-rule-keys (:index kb))]
    (when (seq rule-keys)
      (or (tax/genls-global-meets? tax super rule-keys)
          (tax/genls-global-meets? tax super (licensing-functors kb tax rule-keys))
          ;; above `super` across `genlInverse` edges too, read either way round
          (when-not (tax/genl-inverse-free? tax)
            (let [up (signed-all tax :up super)
                  lf (licensing-functors kb tax rule-keys)]
              (boolean (some #(or (contains? rule-keys %) (contains? lf %)) up))))))))

(defn- negative-subsumption-seeds
  "The half of `subsumption-seeds` that a **negated** antecedent is owed, read up
  `super`'s `genl` closure where the positive half reads down `sub`'s `spec` one.

  Subsumption is contravariant under a negation (docs/inference.md, \"Under a negation
  the fan reverses\"), so an arriving `(genl dog animal)` does not connect `dog`'s facts
  to an `(animal ?x)` antecedent here — it connects `animal`'s *negative* facts to a
  `(not (dog ?x))` one.  `(not (animal A))` stored, then the edge, and a rule negated on
  `dog` should fire; without this seed the same three sentences derive a conclusion in
  one order and not the other, which is what the positive half exists to prevent.

  **This runs only when some rule reads a negated antecedent under `sub`**, off the stored
  antecedent keys — the same keys `rules/trigger-keys` reads, and for the
  same reason.  Sound in both directions this is reached from: for an arriving edge
  nothing can newly match except through it, and for a departing one an edge no negated
  antecedent could ever have climbed licensed nothing to revive.  A KB whose rules read
  no negation, which is nearly every KB, pays one pass over the keys.

  Negative sentexes only, decided by the stored sentence's head `not`: a *positive* fact on a
  genl of `super` newly matches nothing, since a positive antecedent fans downward and
  the edge moved nothing above `super`.

  The `genls` read is unscoped: a seed over-approximates, and the firing it triggers
  is placed in a context the join decides."
  [kb sub super]
  ;; the keys first: `sub`'s spec closure costs its subtree, and a KB reading no negated
  ;; antecedent needs none of it
  (let [nkeys (into [] (filter vector?) (reads/as-stored-rule-keys (:index kb)))
        specs (when (seq nkeys) (signed-all (reasoning/taxonomy kb) :down sub))]
    (when (some #(contains? specs (second %)) nkeys)
      (let [idx  (:index kb)
            recs (:records kb)
            tms  (reasoning/tms kb)]
        (into [] (comp (mapcat #(reads/as-stored-with-functor idx %))
                       (distinct)
                       (filter #(jtms/in? tms %))
                       (filter (fn [h]
                                 (when-let [s (p/get-sentex recs h)]
                                   (sx/negative? s)))))
              (signed-all (reasoning/taxonomy kb) :up super))))))

(defn subsumption-seeds
  "The stored facts the `genl` edges `sentence` installs newly make matchable, as
  chaining seeds — the taxonomy twin of `lift-existing`, and there for exactly the same
  reason.  The edges are `tax/installed-edges`': a `(genl sub super)` edge, or one per part of
  a cover, whose edges subsume exactly as a stated one does.

  Matching fans an antecedent's functor over its `genl` **spec** closure, so an edge
  arriving after the facts changes which antecedents they satisfy: `(dog Muffet)` stored,
  then `(genl dog animal)`, and a rule on `(animal ?x)` should fire.  The semi-naive
  agenda never sees it — the arriving datum is the *edge*, and firing the rules keyed on
  `genl` is not the same thing as re-firing the rules the edge just connected.  Without
  this the same three sentences derive a conclusion in one order and not the other,
  which is the one thing belief may not depend on (docs/nmtms.md).

  The seeds are `sub`'s whole spec subtree, because subsumption is transitive: an edge at
  the top of a hierarchy makes every fact below it matchable at the new
  supertype.  Believed only — a disbelieved fact matches nothing, and it will seed the
  agenda itself when it revives.  **This runs per edge only when `rule-reads-above?`
  holds**: a fact below the edge newly reaches the terms at or above `super` and no other,
  so where no rule reads one the subtree is not read.  Every functor of the subtree
  reaches the same terms, so the check decides for all of its facts at once.  Sound on a
  departing edge for `negative-subsumption-seeds`' reason: a firing that climbed it read a
  term at or above `super`.

  A **negated** antecedent is answered contravariantly, so the facts an edge newly
  offers *it* sit on the other side of the edge entirely: `negative-subsumption-seeds`
  above reads them up `super`'s genl closure.

  The *removal* side is `resubsumption-seeds` below: a firing names the `genl` edges it
  subsumed through, so dropping one withdraws what it licensed — and the facts have to
  go back on the agenda when the reachability outlives the supporter that left."
  [kb sentence]
  (when-let [edges (seq (concat (tax/installed-edges sentence) (genl-inverse-edges sentence)))]
    (let [idx (:index kb)
          tms (reasoning/tms kb)
          tax (reasoning/taxonomy kb)]
      (into (into [] (comp (filter (fn [[_ super]] (rule-reads-above? kb tax super)))
                           (mapcat (fn [[sub _]] (signed-all tax :down sub)))
                           (distinct)
                           (mapcat #(reads/as-stored-with-functor idx %))
                           (distinct)
                           (filter #(jtms/in? tms %)))
                  edges)
            (mapcat (fn [[sub super]]
                      (when (symbol? super) (negative-subsumption-seeds kb sub super))))
            edges))))

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
    (loop [seen #{a} frontier [a]]
      (if-let [t (peek frontier)]
        (let [ups (into #{}
                        (comp (filter #(jtms/in? tms %))
                              (keep left)
                              (remove seen))
                        (reads/as-stored-with-arg-global idx 2 t))]
          (recur (into seen ups) (into (pop frontier) ups)))
        seen))))

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
  chaining seeds — the `TransitivePredicateProver`'s twin of `subsumption-seeds` above,
  and there for exactly the same reason.

  **A declared-transitive predicate's closure is answered, never stored.**  `(causes E0
  E2)` is provable the moment both links are in and is never a record — so it is never a
  datum, never on the agenda, and never a trigger.  A rule joined to that predicate,
  `[(does ?a ?act) (causes ?act ?e)]`, can reach a closure pair only from its OTHER
  antecedent's trigger; and when the closure grows, nothing puts that trigger back.
  Assert the `does` before the second link and the firing has already run against a
  shorter closure; assert it after and the join reaches the whole of it.  Same four
  sentences, two answer sets, which is the one thing belief may not depend on
  (docs/nmtms.md).  `subsumption-seeds` states the principle for the taxonomy: firing the
  rules keyed on the arriving predicate is not the same thing as re-firing the rules the
  arrival just connected.  This is that, one closure over.

  **Two arrival orders, because the closure has two ingredients** — the links and the
  declaration — and either can come last.  `deduce-arg-types` / `entail-existing` /
  `entail-under-edge` are the same three-cornered shape for an argument type:

  - a **link** `(pred a b)`, with `pred` already transitive: the reach that grew is `a`'s
    and that of everything behind it (`transitive-left-ends`), so the seeds are the
    believed facts mentioning one of those.
  - the **declaration** `(transitive pred)`, over links already stored: every pair of the
    closure appears at once, so every believed fact on a partner functor goes back.  This
    is the arm a `(transitive …)` asserted after its links needs, and without it a KB that
    declares its properties at the end of a file answers differently from one that
    declares them at the start.

  **The seeds are the partner triggers, not the links.**  Re-seeding the `pred` facts
  themselves buys nothing: their own trigger position joins the other antecedent at the
  term the link already names, which is the pair the run made anyway.

  **The presence checks keep an ordinary assert free.**  Both arms are off unless some rule
  takes a `pred` antecedent — with no such rule there is no join to re-drive — and the
  link arm reads the inverted index's posting per left end rather than any functor extent,
  so a KB whose transitive facts feed no rule pays two lookups and reads nothing.

  The **removal** side needs no twin: a retracted link withdraws the closure pairs that
  rested on it through the justifications the firings recorded, which is the TMS's
  ordinary business and not a reachability question.

  The mark is read unscoped: a seed over-approximates, and each seeded fact is joined
  from the rule's own context."
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
  "The stored facts a newly forward-capable RULE needs back on the agenda when one of its
  antecedents reads a declared-transitive predicate — the third arrival order of
  `transitive-seeds`' three ingredients, and there for the reason the other two are.

  A rule seeded on its own handle is joined over the stored facts, and that join reaches
  the closure only from whichever side it leads: led from the transitive antecedent it
  enumerates the STORED links and nothing else, since the closure is answered rather than
  stored and an open goal on it yields no record to lead from.  So a rule arriving after
  its facts derives the direct pairs and stops, where the same rule arriving before them
  derives the closure — the same sentences, two answer sets, decided by which came last.

  Seeding the partner facts fixes it the way it fixes the other two arms: each becomes a
  trigger, and a trigger binds the shared variable before the transitive antecedent is
  asked, which is the direction that reaches the closure.

  Off unless an antecedent is actually declared transitive, so an ordinary rule assert
  pays one property lookup per antecedent and reads nothing.

  The mark is read unscoped, for `transitive-seeds`' reason."
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
  "The index functors the facts matchable by a stored rule's antecedent key root under.

  A positive key IS a functor symbol; a **negated** key `[:not g]` roots its facts under
  `g` — a `(not (g A))` record indexes by its positive body's functor (`impl.kv`) — so a
  lookup goes there, not to the `[:not g]` key nothing is ever written to.  Without that
  a genlCx edge arriving after a negative fact never re-joins a rule with a negated
  antecedent, and the same three sentences derive a conclusion in one order and not the
  other — the arrival-order dependence `subsumption-seeds` has a negated half to prevent.

  **And one functor per key is not enough, because matching fans.**  An antecedent
  `(dog ?x)` is answered by a stored `(terrier Rex)` down `dog`'s `genl` spec closure,
  and a negation reverses the fan (docs/inference.md, \"Under a negation the fan
  reverses\"), so `(not (dog ?x))` is answered by a stored `(not (animal A))` up `dog`'s
  genl closure instead.  Reading the key's own functor alone finds the facts a rule
  *names* and not the facts it *matches*, so an edge re-joins the rule over half of what
  it newly sees, and a type hierarchy standing between the rule and the fact is enough
  to leave the conclusion in the orders that wired the contexts first and nowhere else.
  `subsumption-seeds` reads these same two closures, for the same reason from the other
  side of the pair.

  The closures are **global**, and that is `subsumption-seeds`' argument too: these are
  candidates for a re-join and the firing's placement narrows them afterwards, so fanning
  from one context would drop a fact that a context seeing both would match."
  [tx k]
  (if (vector? k)
    (tax/genls-global tx (second k))
    (tax/specs-global tx k)))

(defn- key-fan
  "The functors a fact roots under for a rule keyed in `rule-keys` to match it, or a
  licensing functor: `{:all :member? :bound}`.  `:all` is a delay of the set
  (`rule-key-functors` of every key, with `licensing-functors`), which holds a positive
  key's whole spec closure.  `:member?` answers one functor without building `:all`: a
  walk up its global `genl` closure to a positive key (`tax/genls-global-meets?`), or
  membership in the negated keys' genl closures and the licensing functors.  The walk is
  global for `rule-key-functors`' reason: the seeds are candidates for a re-join, and the
  firing's placement narrows them.  `:bound` is
  the key count: `seeds-in` tests a context's postings one at a time when they number no
  more than the keys whose closures `:all` reads."
  [kb tx rule-keys]
  (let [lic    (delay (licensing-functors kb tx rule-keys))
        small  (delay (into (into #{} (comp (filter vector?) (mapcat #(rule-key-functors tx %)))
                                  rule-keys)
                            @lic))
        missed (volatile! #{})
        seen   (volatile! {})]
    {:all     (delay (into (into #{} (mapcat #(rule-key-functors tx %)) rule-keys) @lic))
     :member? (fn [f]
                (let [m (get @seen f ::none)]
                  (if (identical? ::none m)
                    (let [m (or (contains? @small f)
                                (tax/genls-global-meets? tx f rule-keys missed))]
                      (vswap! seen assoc f m)
                      m)
                    m)))
     :bound   (count rule-keys)}))

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
  `key-fan`, a negation counted under its body's functor as the index roots it.

  Read from whichever side holds fewer postings, which is one count per functor and one
  per context to decide.  The functor extents are the smaller side when the contexts hold
  the ontology, and the contexts are when they hold a context just wired in — empty, the
  commonest edge there is — where reading the extents would cost every rule-relevant fact
  in the KB to find none.  The contexts are read first, and when they hold no more
  postings than a fan's `:bound` (none, for a set), they are the side read and a fan's
  set is never built.  With `keep?`, only the handles it keeps are read further."
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
  under a rule, as chaining seeds, read from the cheaper of two sides.  `n-edges` is how
  many such edges `seen` states (the census, `tax/supporter-count-in`).  When reading
  `up`'s facts under `functors`, the fan of the antecedent keys, costs no more postings
  (`seed-cost`), those facts are the seeds, so a `seen` that holds a large taxonomy is
  never walked.  Otherwise each edge is read as `subsumption-seeds` reads one arriving:
  `sub`'s spec closure when a rule reads at or above `super` (`rule-reads-above?`), and
  `super`'s genl closure when a rule reads a negated antecedent under `sub`.  The
  closures are global, as `subsumption-seeds`' are: the seeds are candidates for a
  re-join, and the firing's placement narrows them.  Only the facts and edges whose
  handles `before?` keeps are read (`move-seeds`' floor)."
  [kb tx rule-keys seen up functors n-edges before?]
  (if (<= (seed-cost kb up functors) n-edges)
    (seeds-in kb up functors before?)
    (let [edges (into [] (comp (keep #(:sentence (p/get-sentex (:records kb) %)))
                               (mapcat tax/installed-edges))
                      (seeds-in kb seen tax/edge-installing-functors before?))
          fs    (into #{} (mapcat (fn [[sub super]]
                                    (let [specs (tax/specs-global tx sub)]
                                      (concat (when (rule-reads-above? kb tx super) specs)
                                              (when (and (symbol? super)
                                                         (some #(and (vector? %) (contains? specs (second %)))
                                                               rule-keys))
                                                (tax/genls-global tx super))))))
                      edges)]
      (if (seq fs) (seeds-in kb up fs before?) []))))

(defn move-seeds
  "The stored facts the `genlCx` move `m` (`context-move`) newly makes matchable, as
  chaining seeds: the context twin of `subsumption-seeds`.  `up` is `super`'s ancestor
  set (`:up`), `seen` what the contexts below `sub` that gain a context see beside it
  (`:gained-below`; `:below` in the unfiltered arity), and `fresh` the contexts some reader
  below `sub` sees through the edge alone (`:moved`).  The facts
  of `fresh` are seeded when `seen` states a rule, the facts of `seen` when `fresh` states
  a rule or a `genl` edge, the smaller side when only the rest of `up` states a rule, the
  facts of `up` under a `genl` edge `seen` states (`under-seen-edges`), and, when `seen`
  states a rule, the facts of `up` under a `genl` edge `fresh` states.  A fact is read under an antecedent
  key fanned by `genl` or a licensing functor (`seeds-in`).  The unfiltered arity,
  `departed-edge-seeds`' re-join, seeds every such fact of `up` and `seen`.

  With `m`'s `:floor` (`seed-floor`), the move is read as of the edge's arrival: a rule,
  a `genl` edge or a fact of `seen`, or a seed, stored at a handle at or above the floor
  arrived after the edge and was chained or joined with the edge in the taxonomy, so the
  checks on `seen` read and the seeds keep only those below it.  See docs/contexts.md, \"A
  `genlCx` edge owes the same debt\"."
  [kb m filtered?]
  (let [idx       (:index kb)
        rule-keys (reads/as-stored-rule-keys idx)]
    (when (and m (seq rule-keys))
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
            fan     (key-fan kb tx rule-keys)
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
                        (under-seen-edges kb tx rule-keys seen up @(:all fan) (counts seen) before?))
                      (when (and filtered? @ruled-seen? (edged? fresh))
                        (under-seen-edges kb tx rule-keys fresh up @(:all fan) (counts fresh) before?))))))))

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

(defn- sighting-seeds
  "The antecedents of the rule firings among `removed-jids` (an integer informant) that
  name a `genlCx` edge in `removed` as an antecedent, less the handles in `removed`, as
  chaining seeds.  Every firing records its justification, a re-derivation of a stored
  conclusion included (`chain/place-fact-conclusion`), and a firing names the edges its
  placement saw each ingredient over (`chain/visibility-support`), so a firing whose
  placement the departing edge moved is one of these.  Empty, and no justification
  record read, unless `removed` holds a `genlCx` edge."
  [kb removed removed-jids]
  (let [edges (into #{} (comp (filter #(= 'genlCx (closure-edge-relation (:sentence %))))
                              (map :id))
                    removed)]
    (if (empty? edges)
      []
      (let [gone (into #{} (map :id) removed)]
        (into []
              (comp (keep #(p/get-justification (:records kb) %))
                    (filter #(and (integer? (:informant %)) (some edges (:antecedents %))))
                    (mapcat :antecedents)
                    (remove gone)
                    (distinct))
              removed-jids)))))

(defn- edge-own-mints
  "The records among `removed` whose every justification in `removed-jids` is an
  argument-type mint (`mint-informant?`) of a removed closure edge: the edge is the first
  antecedent, the fact the declaration typed.  Empty, and no justification record read,
  unless `removed` holds a closure edge and something besides it."
  [kb removed removed-jids]
  (let [edges (into #{} (comp (filter #(closure-edge-relation (:sentence %))) (map :id)) removed)]
    (if (or (empty? edges) (not (next removed)))
      #{}
      (let [by-conclusion (group-by :consequence
                                    (keep #(p/get-justification (:records kb) %) removed-jids))
            own? (fn [j] (and (mint-informant? (:informant j))
                              (contains? edges (first (:antecedents j)))))]
        (into #{}
              (filter (fn [sx] (let [js (by-conclusion (:id sx))]
                                 (and (seq js) (every? own? js)))))
              removed)))))

(defn resubsumption-seeds
  "The chaining seeds a teardown owes, given the `removed` sentexes its sweep collected
  and the `removed-jids` justifications — `subsumption-seeds` and `visibility-seeds` in
  the retraction direction.

  A firing names **one** witness for each reachability it rests on: the `genl` path a
  subsumed match climbed, and the `genlCx` path its placement saw each ingredient
  context over (`taxonomy/reach-support`, `chain/visibility-support`).  So removing an
  edge on one of those paths invalidates the justification and the dependency-directed
  sweep collects the conclusion.  A reachability can outlive one of its supporters — the
  same edge asserted from a second context, or a second path around the one that went —
  and then the firing is still licensed and must come back, as a **re-derivation** at a
  fresh handle (docs/contexts.md, \"A `genlCx` edge owes the same debt\").

  A departing `genl` edge seeds its spec subtree (each part's, for a cover), read
  **before** the teardown while `specs` still names the facts that subsumed through it,
  and the rules with an antecedent on the edge's own relation
  (`closure-reader-rules`).  Both run only when the sweep has taken **something besides
  the records asked for**, not counting an argument-type mint of the edge itself
  (`edge-own-mints`).  A departing `genlCx` edge seeds the antecedents of the firings that
  named it (`sighting-seeds`), unconditionally, and its closure-reading rules under the
  same condition.  Whether a surviving route still licenses a firing is `place-conseq`'s
  question, so most of what this seeds places nothing, and that pass files no
  `:no-placement` (`chain/*report-no-placement?*`)."
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
  (`closure-edge-relation`: a `genl` or `genlCx` edge, or a cover) and went **IN ⇒ OUT**
  in it — `resubsumption-seeds` for an edge that lost belief rather than its record.

  A defeat sweeps nothing: the firings that named the edge as a witness go OUT with it and
  are retained for revival, so the retraction path's re-join never runs, and a
  reachability that outlives the edge over a second route never re-derives them.  The same
  three sentences then leave a conclusion believed where the negation arrived first and
  withdrawn where it arrived last (docs/nmtms.md, \"Where the layer stops\").

  This runs per edge only when a dependent is now OUT, the defeat's counterpart of
  `resubsumption-seeds`' condition on the sweep having taken something: an edge nothing
  rests on, or whose dependents all kept another justification, owes no re-join.  The spec
  subtree is read with the edge already OUT, which changes no answer: `specs` of the
  edge's own `sub` is what lies below `sub`, and the edge runs above it."
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
  "The live twins a merge has already made of sentex `orig`, a reader's copies among them:
  `[{:twin :informant :witnesses :reader}]`.  A twin is the `:consequence` of a
  `rewriteOf`- or `except`-informant justification whose first antecedent is `orig`
  (`justify-twin!`); `jtms/dependents` names those from the original's side.  Grouping by
  consequence and informant recovers each twin, the witnesses that raised it, and its
  context — the same `reader` its form was elected from — exactly the arguments the first
  migration took.  Empty when `orig` has no twin, the common path.  A forward-chaining or
  defeat use of `orig` carries a different informant and is filtered out.

  Empty for an **equality sentence** too.  Migration never restates one
  (`kb/rewritable-sentex?`), and an equality is the *other* antecedent of every twin it
  raised, so reading its `rewriteOf` dependents as twins of its own would carry an
  `except` of the equality onto every fact the equality restated, hiding a premise
  stated in the representative's spelling along with it."
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

;; `departed-edge-seeds` reads an edge that left belief by a relabel, and its condition
;; is a dependent whose conclusion went OUT.  A redundant mint the settle withdraws
;; (`subsumed-mint-blocks`) leaves by a sweep instead, and the firings that named it as
;; their witness are deleted with it while their conclusion usually stands on another
;; firing — so that condition would read nothing, and the firing itself is never drawn
;; again over the route that made the mint redundant.
(defn withdrawn-edge-seeds
  "The chaining seeds a settle owes the closure edges among `handles` — mints it is about
  to withdraw as redundant (`subsumed-mint-blocks`), or spellings a merge retired
  (`settle/withdraw-retired-firings!`) — that a rule firing names as its witness:
  `departed-edge-rejoin`'s facts and rules for each such edge and for each of its twins
  (`handle-twins`).  The closure holds a retired edge's twin in place of the edge, so the
  re-join over the twin draws the firing the merge-first order makes.

  The firing is what is owed, not the conclusion.  A `genl` mint is withdrawn because a
  stated route now reaches as far as it did, so every firing that climbed it has a
  surviving route, and the same content loaded with the stated route first stores that
  firing over it.  Its conclusion keeping another firing says nothing about this one, so
  the condition is a dependent justification whose informant is a rule, read **before**
  the sweep deletes it, and not a dependent conclusion that went OUT.  Without the re-join
  the store keeps whichever firings the arrival order happened to draw, and a later full
  join — a re-join, `forward-chain` — draws the rest at fresh handles."
  [kb handles]
  (let [tms (reasoning/tms kb)
        fired-over? (fn [h]
                      (some (fn [jid]
                              (when-let [j (jtms/justification tms jid)]
                                (integer? (:informant j))))
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
  "The handle a **handle-naming meta-sentex** `s` names, or nil for any other sentence.
  Three kinds name a sentex by handle and so must follow it through a merge: an
  `exceptWhen` names the rule it guards, an `except` names the sentex it hides, and any
  `target_following_predicate` meta (koinii's reply acts) names the claim it hangs on.  A
  target-following meta carries exactly one `(sentexHandle H)` argument, and that is its
  target.

  The mark is read unscoped: a merge retargets the stored meta-sentex, which every
  reader shares."
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
  (`justify-twin!`).  The 5-arity takes `eqs`, the equalities that migrated the sentex,
  under `rewriteOf`.

  Public for `integrate/commute-existing`: a `(symmetric P)` mark folding two mirrored rows
  into one carries the dropped row's metas, with the declaration as the single witness."
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
  "Every believed equality sentex and schematic rewrite rule, as `{:context :terms}`: an
  equality contributes the retirable members of its arguments' classes (`migrate-class`'s
  candidates), a rule its LHS head (`migrate-matching`'s).  Read off the equality
  predicates' extents and the rule cache, so the cost follows the standing merges and not
  the store."
  [kb]
  (let [tx   (reasoning/taxonomy kb)
        idx  (:index kb)
        recs (:records kb)
        tms  (reasoning/tms kb)]
    (into (into []
                (comp (mapcat #(reads/as-stored-with-functor idx %))
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
          (comp (filter #(and (sequential? (:lhs %)) (symbol? (first (:lhs %)))))
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
            rs      (believed-restatements kb)
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
  the write path\").  Entries are only dropped or restated here: a spelling starts being
  displaced when migration hands it over in `extra`, and a reader's copy is retired when
  its original is examined (`with-copies`).

  With a `region`, the walk examines `extra`, the entries `region` names and the entries
  naming a term of a class the partition moved (`tax/take-equality-moves!`); `region` nil
  is the full pass.  Returns `[map changed]`, `changed` the datums whose entry differs
  from the held map's, and records `changed` for the next settle
  (`note-supersession-moves!`)."
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

(defn- restate-retired-mint
  "Restate the mint `sx` that `entail-arg-type` just stored when its sentence names a term
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

(defn- derive-equality
  "Store `(equals x y)` in `context` as a derivation from `antes` under `informant`, and
  merge with it.  Returns the migration result.  The arguments and the antecedents are
  ordered by content (`kb/antecedent-order`), so the sentence key and the list `why`
  prints do not depend on which fact arrived first."
  [kb x y context informant antes]
  (let [[lo hi]    (sort [x y])
        sentence   (list 'equals lo hi)
        antes      (kb/antecedent-order kb antes)
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
  `(equals V1 V2)`.  `{:new :superseded :violations}`, or nil when nothing clashes.

  The equality takes one justification per declaration of the convicting mark `via` at
  the clash's position (`checks/functional-declaration-supporters`), unfiltered by what
  `context` sees (docs/defenses.md, \"A functional merge rests on every declaration of
  the convicting mark\").  Each justification names both facts, the `genl` edges both
  members descended through to reach `via`, and the `genlCx` edges `context` sees each
  fact and the declaration through (`pair-antecedents`)."
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

(defn derive-functional-equalities
  "`derive-functional-equalities-in` run from every reader at or below `context`
  (`tax/context-down`), since a reader below two blind siblings sees a clash neither
  sibling sees.  `readers`, when given, narrows that set; only
  `equate-under-context-edge-via` passes it, with the contexts the edge widened
  (`genlcx_sweep_test`, `genlcx_sweep_cost_test`).

  Two presence checks run before `context-down` is read: the KB-wide
  `tax/functional-family-declared?`, one map read, and `functional-mark-relevant?` of the
  functor, so a fact no mark reaches pays for no reader sweep."
  ([kb sentence context handle] (derive-functional-equalities kb sentence context handle nil))
  ([kb sentence context handle readers]
   (let [tax (reasoning/taxonomy kb)]
     (when (tax/functional-family-declared? tax)
       (if (functional-mark-relevant? tax (nm/functor sentence))
         (reduce (fn [acc r]
                   (merge-with into acc (derive-functional-equalities-in kb sentence r handle)))
                 {:new [] :superseded [] :violations []}
                 (cond->> (tax/context-down tax context)
                   readers (filter readers)))
         (derive-functional-equalities-in kb sentence context handle))))))

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
            (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
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
   (let [tax (reasoning/taxonomy kb)]
     (when (seq (tax/props tax :anti-symmetric))
       (if (anti-symmetric-mark-relevant? tax (nm/functor sentence))
         (reduce (fn [acc r]
                   (merge-with into acc (derive-antisymmetric-equalities-in kb sentence r handle)))
                 {:new [] :superseded [] :violations []}
                 (cond->> (tax/context-down tax context)
                   readers (filter readers)))
         (derive-antisymmetric-equalities-in kb sentence context handle))))))

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

;; ---- a departing `genl` edge re-derives what descended through it ----------
;; Three derivations descend the predicate hierarchy and name the `genl` edges they
;; descended through (`checks/edge-support`): the argument-type entailment, and the
;; equality a `functional` or `anti_symmetric` mark on a super-predicate licenses.  Each
;; names **one** route, a shortest visible one, so removing an edge on that route
;; deletes the justification even where a second route still reaches the declaration.
;; The removal then re-derives from the taxonomy it left, as `resubsumption-seeds` does
;; for a firing: the justification is a conjunction of supports, not a proof that no
;; other route exists.  An entailment through an `interArg` or homogeneity declaration
;; also names one trigger membership, and a removed trigger is re-derived the same way
;; over a trigger that survives.

(def ^:private edge-descended-informants
  "The informants of the derivations that cite the `genl` edges they descended through
  and the `genlCx` edges they see their ingredients through, mapped to how each is drawn
  again for the fact at the head of its antecedents.  A merge's restatement and a reader's
  copy (`migrate-into`) name the `genlCx` edges their reader sees the original through."
  (into {'functional     :functional
         'anti_symmetric :anti-symmetric
         'rewriteOf      :migration
         'except         :migration}
        (map (fn [k] [k :entailment]))
        (keys entailing-declarations)))

(defn- past-the-pair?
  "Is `h` an antecedent of the entailment justification `j` other than its fact and its
  declaration, the first two (`entail-arg-type`): a route edge, a `genlCx` edge, a trigger
  membership or the trigger's route?"
  [j h]
  (and (= :entailment (edge-descended-informants (:informant j)))
       (boolean (some #{h} (drop 2 (:antecedents j))))))

(defn edge-descended-justifications
  "The justifications among `removed-jids` that a departing route edge (`route-functors`)
  or trigger membership invalidated while the fact and the declaration survive, as
  records — the derivations a teardown owes a re-derivation (`rederive-descended`).
  `gone` is the sentexes the sweep removed.

  Read **before** the teardown deletes the justification records, since the records are
  what name the fact and the declaration to derive from again.  This runs only when `gone`
  holds a route edge, or a membership while a trigger declaration is stored, so a removal
  that took neither fetches no justification record.

  An entailment qualifies when a removed antecedent is past its fact and declaration
  (`past-the-pair?`) and neither of those two is removed; a descended equality, when one
  of its antecedents is a removed route edge and no removed antecedent is anything else;
  a restatement (`:migration`) the same way, with a removed equality counted as a route
  edge.
  A removed fact or declaration withdraws the derivation, and re-deriving it would undo
  the removal."
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
                          kind  (edge-descended-informants (:informant j))
                          route (if (= :migration kind) links edges)]
                      (if (= :entailment kind)
                        (and (not-any? ids (take 2 antes))
                             (boolean (some ids (drop 2 antes))))
                        (and (boolean (some route antes))
                             (not-any? #(and (contains? ids %) (not (contains? route %)))
                                       antes)))))]
        (into []
              (comp (keep #(p/get-justification recs %))
                    (filter #(contains? edge-descended-informants (:informant %)))
                    (filter owed?))
              removed-jids)))))

(defn lost-descended-derivations
  "The edge-descended derivations among the dependents of `handles` whose conclusion is
  OUT, as justification records — `edge-descended-justifications` for an ingredient that
  lost belief rather than its record.  `edges-only?` keeps a dependent only where its
  handle is a route edge (`route-functors`), an entailment antecedent past the fact and
  the declaration (`past-the-pair?`), such as a trigger membership, or an equality a
  restatement rests on.

  Two settle arms read it.  A `genl` edge that went **IN ⇒ OUT** takes the derivation
  naming it OUT, where a second route to the declaration still licenses it; a defeat
  deletes nothing, so the justification stays and nothing else draws the derivation
  again.  And a spelling an un-merge gives back is a fact the derivation could not be
  drawn from while the merge superseded it: an equality over two spellings of one merged
  pair is found by matching both, so it is drawn only once both are believed again.

  Only a justification whose conclusion is OUT, or withdrawn at its own context
  (`exc/believed-own?`), qualifies: one that kept another support
  owes nothing to belief, and asking it again every pass of the settle would re-read a
  conclusion that cannot move.  The dependents are a network read and the record a
  store fetch, so the filter that drops nearly every handle runs first."
  [kb handles edges-only?]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        lost (fn [h]
               (into []
                     (comp (keep #(jtms/justification tms %))
                           (filter #(contains? edge-descended-informants (:informant %)))
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
                              (filter #(= :migration (edge-descended-informants (:informant %))) js)
                              :else (filter #(past-the-pair? % h) js)))))
                (distinct))
          handles)))

(defn rederive-descended
  "Draw each of `justs` (`edge-descended-justifications`) again from the taxonomy as it
  now stands, and return the handles it created as chaining seeds.  The violations are
  reported and the spellings a merge displaces are refreshed here, as the arrival path
  does for the same derivations.

  Each derivation is asked for through the function its arrival arms ask: the entailment
  through `retroactive-mints`, narrowed to the declaration the removed justification
  named; a descended equality through `derive-functional-equalities` or
  `derive-antisymmetric-equalities` over the fact at the head of its antecedents.  So
  where a second route survives, the derivation comes back resting on it, and where none
  does, nothing is drawn.  A conclusion that kept another justification takes the
  surviving route's as well, which is the justification the same content loaded without
  the edge records.  A restatement is drawn again by `migrate-sentex` over the original at
  the head of its antecedents, or over the target a restated meta names.

  An entailment's antecedents lead with the fact and the declaration, in that order
  (`entail-arg-type`).  An equality's are in content order (`derive-equality`), so its
  facts are read off by functor: every antecedent that is neither a `genl` or `genlCx`
  edge nor a mark declaration.  Each task is drawn once however many of the removed
  justifications name it."
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
                                    (let [kind  (edge-descended-informants (:informant j))
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

(defn- unchecked-target?
  "Does `src-context` fail to see CxUniverse, so that the definitional checks run there
  never considered a copy lifted out of it?"
  [kb src-context]
  (not (tax/sees? (reasoning/taxonomy kb) src-context universal-context)))

(defn- lift-of? [dh] #(and (:lift %) (= dh (:dh %))))

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
  "Deduce `sentence` (stored at `src-handle` in `src-context`) into CxUniverse, checked
  there when `(unchecked? src-context)` (`unchecked-target?`), and justified by
  `src-handle` and each of `witnesses` in turn — a vector of the further antecedents one
  justification rests on.  A declared lift passes one `[declaration]`
  per declaring sentex, as a migrated twin gets one witness per equality, so retracting
  one of two declarations leaves the copy standing on the other; a permuting mark's lift
  passes `[[]]`, since nothing but the mark's own statement holds it
  (`deduce-lifts`).  A refused lift is kept once per witness, under its declaration's
  handle, or under nil for a permuting mark's.

  Returns `{:new [handle …] :violations [v]}` — the copy's handle when it was newly
  created, with the twins its merges wrote (`copy-merges`; the caller seeds chaining with
  all of them), and the violation when the copy could not be admitted, reported rather
  than thrown since a lift runs inside a fixpoint and inside `settle`."
  [kb unchecked? sentence src-handle src-context witnesses]
  (if (or (empty? witnesses) (= src-context universal-context))
    empty-entailment-result
    (if-let [v (and (unchecked? src-context)
                    (checks/derivation-violation kb sentence universal-context))]
      (do
        ;; an argument conviction reads memberships and separations later content can
        ;; move — so the lift waits to be re-asked rather than being lost to the order
        ;; they and the declaration arrived in (`release-lift!`)
        (doseq [[dh] witnesses]
          (note-pending! kb src-handle
                         (merge {:lift true :dh dh :gens (conviction-generations kb)}
                                (checks/conviction-watch v))
                         (lift-of? dh)))
        {:new [] :violations [(-> v
                                  (assoc :sentence sentence :context universal-context)
                                  (assoc-in [:detail :lifted-from] src-context))]})
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
               :violations (-> [] (into (:violations mig)) (into (:violations args)))})))))))

(defn deduce-lifts
  "Deduce `sentence` (stored at `handle` in `context`) into CxUniverse if its
  predicate is decontextualized or is a permuting mark — `{:new [handles] :violations
  [v]}`, nil when neither holds.  Called by `assert` and by forward chaining's
  `place-conclusion`.  A permuting mark (`inherit/permuting-marks`) is lifted on its
  statement alone, whatever the KB declares; any other is lifted once per declaring
  sentex.  The declaration is read unscoped
  (docs/contexts.md#decontextualized_predicate-a-fact-that-belongs-to-the-kb-not-to-one-theory)."
  [kb sentence handle context]
  (let [tax  (reasoning/taxonomy kb)
        pred (nm/functor sentence)]
    (cond
      (inherit/permuting-mark? pred)
      (deduce-lift kb #(unchecked-target? kb %) sentence handle context [[]])
      (and pred (tax/has-prop? tax :decontextualized pred))
      (deduce-lift kb #(unchecked-target? kb %) sentence handle context
                   (map vector (tax/prop-supporters tax :decontextualized pred))))))

(defn- unary-entailments
  "The `unary_predicate` memberships the declaration `sentence` stored at `dh` entails of
  the types it mints in, each justified by the declaration alone, in the declaration's
  context: a type is a unary predicate, and a declared type no arity statement binds to
  another length is one (`arity/mintable-type?`).  Never withheld as a subsumed mint is,
  since a type's arity holds at every context (`arity/relation-length`); a new membership
  lifts as an asserted one does (`deduce-lifts`).  `thing` is left out."
  [kb sentence dh]
  (let [ctx (:context (p/get-sentex (:records kb) dh))]
    (reduce (fn [acc t]
              (let [r (entail-arg-type kb {:assert (list 'unary_predicate t) :because []
                                           :kind declared-type-informant :class true}
                                       dh ctx false)]
                (reduce (fn [acc h]
                          (merge-with into acc
                                      (deduce-lifts kb (:sentence (p/get-sentex (:records kb) h)) h ctx)))
                        (merge-with into acc r)
                        (:new r))))
            empty-entailment-result
            (distinct (remove #{'thing} (declared-types sentence))))))

(defn entail-existing
  "When an `(arg P n T)` / `(genlArg P n T)` / `(interArg P n T m U)` declaration
  arrives, draw what it now says about the `(P …)` sentexes **already stored** — so a
  declaration arriving after the facts reaches them exactly as one arriving before
  reaches the facts that follow.  Same `{:new :violations}` result, so the types it mints
  are chaining seeds like any other new content.  nil when `sentence` is not an argument
  constraint.

  `triggered-mints` reaches a conditional form's trigger arriving after both the fact
  and the declaration, in the settle.

  Sweeps what is **stored**, not what is believed, for `lift-existing`'s reason: a type
  minted off a defeated fact is justified by that fact and so is defeated too — the
  JTMS already says what a disbelieved antecedent means — whereas skipping it would
  leave the type missing when the fact revives, which is belief depending on the order
  the defeat and the declaration arrived in.

  An inert sentex draws nothing (`retroactive-mints`).

  The extent is read off the **predicate extents of `P`'s whole spec subtree**, which is the
  precise answer to \"every stored tuple this declaration constrains\": a declaration on
  `P` binds every predicate beneath it (`res/constraining-predicates`), so an extent read
  off `P` alone would mint over `(parentOf …)` and not over `(fatherOf …)` —
  a type the same three sentences produce in one arrival order and not the other.
  `subtree-sentexes` reads it, and snapshots it before the first mint.  A `(resultArg F
  n)` binds the stored `natFormula` facts of `F`'s applications (`result-arg-extent`), and
  an `interArgEqual` the tuples holding its value at its trigger position
  (`trigger-extent`).

  A declaration whose type is not mintable reads no extent and records nothing: every arm
  asks `arity/mintable-type?` of that type before it draws, so no fact would yield an
  entailment, and `mints-on-lengths` runs the sweep once the type's length admits one.  A
  declaration whose every type is `thing` reads none either.  A declaration that mints
  entails its types' `unary_predicate` memberships (`unary-entailments`)."
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
  each relation whose own arity bindings moved to those bindings' `#{[kind value]}`
  (`arity/drain!`'s `:bound`).  A type's mintability reads its own bindings alone, and
  only a binding admitting a length other than one moves it, so a type whose moved
  bindings all bind one is not read, nor is any type no write bound.  A declaration
  arriving while its type was bound to another length minted nothing and recorded nothing
  (`entail-existing`), and this is where it mints.

  For each mintable type `t` of `bound`, in content order:
  - each stored entailing declaration naming `t` with no `declaredType` justification of
    `(unary_predicate t)` (`declared-type-justifications`) runs its sweep
    (`entail-existing`).  That justification stands for every declaration whose sweep ran
    while `t` was mintable, so a declaration that already minted reads no extent;
  - each stored fact naming `t` where an `argArg` names its type at the fact's own
    argument, and each `natFormula` fact naming `t` in the expression of a function a
    `resultArg` declares, draws what its arrival draws (`deduce-placed`), deduplicated on
    content.

  Reads, per type of `bound`, its arity bindings, then for a mintable one the declaration
  postings naming it and its `(unary_predicate t)` justifications, and the slot or term
  postings only when an `argArg` or `resultArg` is stored.  The predicates an `argArg` is
  declared of are read KB-wide (`tax/props-over` with no context), a superset: each fact
  found draws through its own context's declarations.  An inert declaration sweeps
  nothing."
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

(defn lift-refusals
  "The lifts waiting on an argument conviction, as `[source-handle entry]` pairs in
  handle order."
  [kb]
  (->> (kind-entries @(reasoning/refused kb) :lift)
       (sort-by (fn [[h e]] [h (:dh e)]))
       vec))

(defn release-lift!
  "Re-ask the lift of the fact at `src-handle` under declaration `(:dh entry)`, or on
  the statement alone where that is nil (a permuting mark's):
  `{:new [handle …]}` when it is admitted now, the entry re-recorded under `gens` and the
  term of the conviction read now (`checks/conviction-watch`) when the conviction still
  holds, and retired when the fact or the declaration has left.  An admitted lift
  withdraws the ledger entry its refusal filed, since the order that brought the type
  first would have filed none."
  [kb src-handle entry gens]
  (let [rec (:records kb)
        sx  (p/get-sentex rec src-handle)
        dh  (:dh entry)]
    (if-not (and sx (or (nil? dh) (p/get-sentex rec dh)))
      (do (drop-pending! kb src-handle (lift-of? dh)) empty-entailment-result)
      (do (drop-pending! kb src-handle (lift-of? dh))
          (let [r (deduce-lift kb #(unchecked-target? kb %) (:sentence sx) src-handle
                               (:context sx) [(if dh [dh] [])])]
            (if-let [v (first (:violations r))]
              (do (note-pending! kb src-handle
                                 (merge entry {:gens gens} (checks/conviction-watch v))
                                 (lift-of? dh))
                  empty-entailment-result)
              (do (violations/withdraw! kb (:sentence sx) universal-context nil)
                  r)))))))

(defn- lift-statements
  "Deduce every stored `(pred ...)` sentex outside CxUniverse into it on `witnesses`
  (`deduce-lift`), as one `{:new :violations}`.  The extent is snapshotted before the
  first copy is made, since each copy posts to the term-index entry being walked.
  `unchecked-target?` is asked once per stating context: the walk writes no `genlCx`
  edge, so the answer holds for the whole walk."
  [kb pred witnesses]
  (let [unchecked? (memoize #(unchecked-target? kb %))]
    (reduce (fn [acc s]
              (if-not (and (= pred (nm/functor (:sentence s)))
                           (not= universal-context (:context s)))
                acc
                (merge-with into acc (deduce-lift kb unchecked? (:sentence s) (:id s)
                                                  (:context s) witnesses))))
            empty-entailment-result
            (vec (kb/find-sentexes kb pred)))))

(defn- lift-existing
  "Deduce every stored `(pred ...)` sentex outside CxUniverse into it on the declaration
  at `dh`, believed or not, as `{:new :violations}`; the copies are chaining seeds.  A
  permuting mark returns the empty result, its statements being lifted as they arrive."
  [kb pred dh]
  (if (inherit/permuting-mark? pred)
    empty-entailment-result
    (lift-statements kb pred [[dh]])))

(defn rebuild-pending!
  "Rebuild the engine's own waiting lifts after `recover`: every decontextualized lift an
  argument conviction refuses (a permuting mark's included), re-noted as its arrival
  noted it.  The refusal record is in-memory state no store holds, and
  `chain/rerecord-refusals!` rebuilds only the rules' half of it.  The lift sweep is
  `lift-existing`'s, which over copies already stored adds nothing and so only re-notes
  the refused ones.

  The marks are read unscoped: the rebuild covers every stored mark, whichever reader
  sees it."
  [kb]
  (with-open [_ (progress/start ::rebuild-pending "recover: rebuild the waiting lifts" nil)]
    (let [tax (reasoning/taxonomy kb)]
      (doseq [pred (sort-by nm/name-key (tax/props tax :decontextualized))
              dh   (sort (tax/prop-supporters tax :decontextualized pred))]
        (lift-existing kb pred dh)))
    ;; the permuting marks, which lift on their statement alone
    (doseq [f inherit/permuting-marks]
      (lift-statements kb f [[]]))))

(defn- revived-edge-sweep
  "The merges and candidate offers a revived `(genl sub super)` edge owes the facts of
  `sub`'s spec subtree: `equate-under-edge`, `antisym-equate-under-edge` (its converse
  re-offer included) and `offer-marked-under-edge` over one walk, bounded at
  `tax/*exposure-instance-budget*` sentexes.  nil when `sentence` is not a `genl` edge or
  no merge mark and no `offered-marks` mark stands at or above `super`.

  The walk reads the subtree's predicates in content order and each posting in the
  index's order, so past the budget the prefix merged is in handle order within a
  predicate.  A cut files one `:genl-edge-revival-truncated` entry naming the edge, and
  the facts past it stay unmerged until something else re-derives them.  `context` is the
  edge's."
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
  "Run, for each sentex in `handles` the settle just brought back **OUT ⇒ IN**, the sweeps
  its arrival runs over the facts already stored: `equate-existing` and
  `antisym-equate-existing` for a merge mark, `revived-edge-sweep` for a `genl` edge under
  one, and `lift-existing` for a `decontextualized_predicate` (docs/equality.md, \"A mark
  that revives runs its arrival sweep again\").  Returns one `{:new :superseded
  :violations}`, or nil when the KB declares no merge, nogood-candidate or lift mark,
  which costs one map read per kind.

  The sweeps read what is **stored** and are idempotent, and the handles are walked in
  content order.  A revived permuting mark re-spells its rows through
  `chain/reconcile-spellings!` instead."
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
                (if (and j (mint-informant? (:informant j))
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
  sentex (`equality-arrival-sweep`), and `revived-declaration-sweeps`' for a merge or lift
  mark.  Returns one `{:new :superseded :violations :removed}`, or nil when `handles` is
  empty.

  An equality restates a fact for the readers that see it, and an `except` changes which
  readers those are without the equality arriving, leaving or changing label.  A fact
  stored while the except hid the equality from the fact's context was stored as spelled,
  with no twin, and every goal from that context is normalized under the equality the
  moment the except goes — so without this sweep the fact is believed and answered by no
  read (docs/equational.md, \"An except of an equation\").  The sweeps are the arrival
  ones and idempotent, so a twin already made gains nothing, and a handle that is no
  longer stored, or restates nothing, costs a record fetch.  The handles are walked in
  content order.

  The argument-type derivations move the same way (docs/argtypes.md, \"An except of an
  ingredient\"): with `sweep?`, the ones resting on a record an `except` now hides are
  dropped (`drop-hidden-mints!`, `:removed` for the caller to apply), and the records it
  stopped hiding draw again.  For a handle in `whole`, whose `except` itself moved, that
  is every context and the record's own arrival sweep (`revealed-entailments`).  For one
  only in `scoped`, `{handle #{[sub super]}}`, moved by `genlCx` edges, it is the contexts
  under each `sub` and the edge's own sweep over them (`entail-under-context-edge`)."
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
          drawn (reduce (fn [acc [sub super]]
                          (merge-with into acc
                                      (entail-under-context-edge kb (context-move kb sub super))))
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
        seen (loop [seen #{}, stack (vec targets)]
               (if (empty? stack)
                 seen
                 (let [d (peek stack), stack (pop stack)]
                   (if (contains? seen d)
                     (recur seen stack)
                     (let [meta (some-> (p/get-sentex recs d) :sentence kb/except-target)]
                       (recur (conj seen d)
                              (cond-> (into stack
                                            (comp (keep #(jtms/justification tms %))
                                                  (map :consequence))
                                            (jtms/dependents tms d))
                                meta (conj meta))))))))]
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
  `except`s are stated in.  `pending` is `{target #{except-context}}`.

  A supersession is decided at the datum's own context from the equalities that context
  sees (`displacement`), and an `except` changes that only for the contexts that read it
  and only for the equalities it withdraws, so this set is the whole of what the
  settle's reconcile re-examines for it.  Each candidate costs a term-index lookup per
  term, the same lookups the arrival sweep makes, and a KB superseding nothing costs one
  deref."
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
  "Empty `:except-moves` and return what the settle's supersession reconcile owes it:
  `{:extra [[datum reason]] :region #{datum} :full? bool}` — the supersessions
  `except-move-sweeps` found, the superseded data an `except` that moved can change
  (`except-move-region`), and whether a move is still pending undrained, which leaves the
  reconcile nothing narrower than a full pass.  nil when nothing moved."
  [kb]
  (let [a (reasoning/except-moves kb)
        m @a]
    (when (or (seq (:pending m)) (seq (:extra m)) (seq (:region m)))
      (reset! a {})
      {:extra (:extra m) :region (:region m)
       :full? (boolean (seq (:pending m)))})))

(defn drain-except-moves!
  "Take the pending handles off `:except-moves`, sweep them (`except-move-sweeps`, with
  `sweep?`), and keep the supersessions the sweeps found and the region the moves can
  change (`except-move-region`) for `take-except-moves!`.  Returns the sweeps' result,
  its `:new` joined by the believed facts of the targets' consequence closure and of the
  antecedents resting on it, to chain from, or nil when nothing was pending."
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
                                         (mapcat #(jtms/dependents tms %) cl))))]
        (swap! a #(-> %
                      (update :extra (fnil into []) (:superseded mig))
                      (update :region (fnil into #{}) reg)))
        (update mig :new (fnil into []) src)))))

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
  them — the ancestor-set-scoped analogue of `subtree-sentexes`' spec-subtree walk, over
  contexts instead of predicates, and lazy for the same reason: a budgeted caller
  realizes only its prefix, and a context cycle can make an ancestor set the whole graph.

  This walk is deliberately not **belief**-filtered, for `equate-existing`'s reason:
  an equality derived off a defeated fact rests on that fact and is defeated with it,
  so skipping a defeated candidate here would leave a revival's merge missing —
  `derive-functional-equalities`/`-in` read the store, never the belief filter, and
  this feeds them, so it has to agree.

  **Read from the smaller side.**  `roots` are the predicates carrying the mark, and a
  fact `marked?` admits is one of their specs', so the candidates are the facts of those
  functors that sit in `contexts` as well as the facts in `contexts` that `marked?` admits
  — one set read two ways.  The ancestor set of an edge into a corpus context holds
  the corpus, where the marked predicates hold a few of its facts, and every handle
  walked is a record paged; the side is chosen by the two stored counts, index
  cardinality reads.  The functors are the roots' `tax/specs-global`, unscoped, because
  `marked?` reads the mark unscoped (`tax/props-over` with no context) and this has to
  enumerate every functor it admits.  The enumeration order, and so which prefix a cut budget takes,
  follows the side read (`budgeted-context-edge-candidates` names that residual)."
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
        keep? (fn [s] (and s (nil? (:antecedent s)) (not (sx/negative? s))
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
  "Up to `tax/*exposure-instance-budget*` stored, positive, non-rule sentexes stored in
  `ctxs` (what the readers under a moved `genlCx` edge see, `context-move`'s `:seen`), kept
  when `marked?` admits them, as `[candidates cut-budget-or-nil]`: the shape
  `equate-under-context-edge` and `antisym-equate-under-context-edge` fold
  `derive-functional-equalities` / `derive-antisymmetric-equalities` over.

  `stored-facts-in-ancestors` enumerates in handle order, and `take` keeps a prefix, so
  past the budget which merges an edge derives depends on arrival order.  Sorting to
  content order would force the whole extent, the cost the cap refuses
  (`constraint-exposure-context-edge`), so the caller files
  `:context-edge-exposure-truncated` whenever the cut happens (docs/equality.md).  Below
  the cap the sweep is exact."
  [kb ctxs marked? roots]
  (let [budget (max 0 (long tax/*exposure-instance-budget*))
        xs     (into [] (take (inc budget))
                     (stored-facts-in-ancestors kb ctxs marked? roots))]
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

(defn- equate-under-context-edge-via
  "The body `equate-under-context-edge` and `antisym-equate-under-context-edge` share: a
  `(genlCx sub super)` edge arriving over facts a widened ancestor set newly makes jointly
  visible hands each candidate to the family's `derive` in its own context, and files the
  budget's cut as `prop`'s truncation.  `declares?` is the family's KB-wide presence check
  and `relevant?` keeps the facts a mark of it can reach.

  `derive` takes a fifth argument here, the readers whose ancestor set the edge changed
  (`:under`), and narrows its reader sweep to them.  The budget cuts a prefix of the
  candidates and the reader set cuts the contexts each is re-derived at; the two do not
  interact (`genlcx_sweep_test`)."
  [kb m declares? relevant? derive prop]
  (let [tax         (reasoning/taxonomy kb)
        [sub super] (:edge m)]
    (when (and (symbol? sub) (symbol? super) (declares? tax))
      (let [[candidates cut] (budgeted-context-edge-candidates kb @(:seen m) relevant?
                                                               (marked-roots tax prop))
            ;; the readers whose ancestor set this edge changed, computed once
            widened @(:under m)
            result (reduce (fn [acc sx]
                             (merge-with into acc
                                         (derive kb (:sentence sx) (:context sx) (:id sx)
                                                 widened)))
                           {:new [] :superseded [] :violations []}
                           candidates)]
        (cond-> result
          cut (update :violations conj
                      (context-edge-exposure-truncation sub prop cut)))))))

(defn equate-under-context-edge
  "When a `(genlCx sub super)` edge arrives, derive the equalities a `(functional …)`
  mark licenses over facts the readers under `sub` newly see together: the fourth arrival
  order of the three ingredients, and the context twin of `equate-under-edge`.  Sweeps
  the stored facts the readers under `sub` see (`context-move`'s `:seen`), kept when
  `functional-mark-relevant?` admits their functor, and hands each to
  `derive-functional-equalities` at its own context, which sweeps the readers below it.
  Free for a KB that declares nothing functional.  Budgeted
  (`budgeted-context-edge-candidates`), and idempotent: a pair `same-class-in?` holds
  is skipped.  An equality derived here rests on the `genlCx` edges its reader sees each
  fact and the declaration through (`pair-antecedents`), so retracting the edge
  un-merges."
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

(defn- reconcile-move
  "What the `genlCx` move `m` (`context-move`, an edge active now) means for the equality
  closure and the argument-type entailments: the sentexes the readers under `sub` newly
  see restated under a standing merge (`migrate-under-context-edge`), the merges the same
  widening licenses (`equate-under-context-edge`, `antisym-equate-under-context-edge`),
  and the derivations the declarations it shows draw (`entail-under-context-edge`).
  Returns `{:new :superseded :violations}`, or nil when no sweep did anything.  While any
  spelling is superseded it runs the supersession reconcile itself and hands back no
  `:superseded`."
  [kb m]
  (let [cme (migrate-under-context-edge kb m)
        cfn (equate-under-context-edge kb m)
        cax (antisym-equate-under-context-edge kb m)
        ent (let [r (entail-under-context-edge kb m)]
              (when (or (seq (:new r)) (seq (:violations r))) r))
        mig (when (or cme cfn cax ent)
              (merge-with into {:new [] :superseded [] :violations []} cme cfn cax ent))]
    (if (seq (jtms/superseded (reasoning/tms kb)))
      (do (refresh-supersessions kb (:superseded mig) nil)
          (some-> mig (assoc :superseded [])))
      mig)))

(def ^:dynamic *seed-moves?*
  "False while a write asserted with `{:chain? false}` settles: the drain re-checks what a
  `genlCx` move moves and seeds no chaining from it (`drain-context-moves!`)."
  true)

(def ^:private move-families
  "Every family a `genlCx` move re-checks, read by `drain-context-moves!` with the move's
  `context-move` value.  `:on` names the kinds of move a row reads: `:shown` an edge
  stored or relabelled and active now, `:hidden` one removed or out, `:excepted` an active
  edge an `except` that moved reaches the support of (ruling 24: the readers under the
  except's context gain or lose it).  `:stratum` names the sets of the move the row reads
  (`:raw`, the excepts in force; `:effective`, fact visibility), and `:run` takes the KB
  and the move and answers `{:seeds [handle …] :mig {:new :superseded :violations}}` or
  nil.  The placement families read the moves' projection (`:reach`), not a row."
  [{:family :exception-rules :on #{:shown :hidden :excepted} :stratum :effective
    :run (fn [kb m] (recheck-genlCx-edge kb m) nil)}
   {:family :excepts :on #{:shown :hidden} :stratum :raw
    :run (fn [kb m] (recheck-except-ancestors kb m) nil)}
   {:family :firing-seeds :on #{:shown :excepted} :stratum :effective
    :run (fn [kb m] (when *seed-moves?* {:seeds (move-seeds kb m true)}))}
   {:family :merges-and-mints :on #{:shown :excepted} :stratum :effective
    :run (fn [kb m] {:mig (reconcile-move kb m)})}
   {:family :departed-mints :on #{:hidden} :stratum :effective
    :run (fn [kb m] {:mig (departed-context-edge-mints kb m)})}])

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
            memo   (volatile! {})
            move   (fn [[sub super]]
                     (or (get @memo [sub super])
                         ((vswap! memo assoc [sub super] (context-move* kb ctxs sub super)) [sub super])))
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
            moved  (moved-edges kb ends departed read)
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
            out    (into [] (for [[kind m] ms
                                  {:keys [on run]} move-families
                                  :when (contains? on kind)]
                              (run kb m)))]
        (when (seq ms) (note-split-marks! kb))
        ;; the moves a write's report reads the reach of (`settle-finish`)
        (when (and observe/*write-record* (seq ms))
          (.addAll ^java.util.List (observe/record-of ::context-moves #(java.util.ArrayList.)) (mapv second ms)))
        {:reach  reach
         :first? first?
         :seeds  (into [] (mapcat :seeds) out)
         :mig    (apply merge-with into {:new [] :superseded [] :violations []} (keep :mig out))}))))

(defn drain-context-moves!
  "Once a settle pass: read the `genlCx` moves since the placement cursor
  (`decide/take-edge-cursor!`, register J6 over J5), compute each one's `context-move`
  once, and hand it to every row of `move-families` the move reads.  The edges are the
  ones `moved-edges` names; the placement families read `:reach`, a delay of `{:under :below}` over
  every lower end moved and each active edge up from it (`{:all? true}` when the relation
  was rebuilt), read over the unscoped closures: a superset over every reader, where no
  reader exists, as the candidate rows are (`decide/unscoped-closures`).  The active edges an
  `except` that moved reaches are moves of their own (`excepted-edges`), read by the
  effective rows.  `read` is the settle's volatile of supporter labels drained.  Returns
  `{:reach :first? :seeds :mig}`.  A rebuild takes the departures, leaves the cursor for
  the first pass that places, and runs no row.  See docs/contexts.md, \"One context
  move\"."
  [kb read rebuilding?]
  (if rebuilding?
    ;; the cursor is left for the first pass that places, which owes every placement;
    ;; the inherited clashes a rebuild reads start from an emptied memo
    (do (take-departed-edges! kb) {:reach (delay nil) :first? false})
    (drain-moves! kb read)))

(defn- stored-declarations
  "Every **stored** sentex whose functor is `f`, believed or not.

  Read by the passes that sweep what is *already there* — `post-taxonomy-supporters!`'
  replay, `rebuild-taxonomy`'s replay of the equality relations, and the
  `disjoint_metatype` arm picking up memberships asserted before the declaration —
  because each records supporters rather than deciding belief, and a supporter omitted
  here is one no later reconcile can find.  The supporter families and the equality
  partition record *every* asserting sentex, with `refresh-beliefs` deciding which
  entries are active: omit a disbelieved supporter and clearing its defeat could never
  revive the entry, so a defeated `(disjoint dog cat)` would answer differently either
  side of a restart.

  Stored, not believed — but **positive**: `sentexes-with-functor` returns both
  polarities, and a `(not (genl a b))` *opposes* the edge rather than asserting it.
  The rebuild arms read the positive shape positionally, so a negation would bind
  its inner sentence as a taxonomy node and nil as the other — and the assert path
  never routes one here either, since its dispatch reads the functor `not`.

  Every caller consumes the whole extent, so the records are hinted a chunk ahead
  (`cap/hinting`). `r`, a progress reporter, ticks once per stored handle read."
  ([kb f] (stored-declarations kb f nil))
  ([kb f r]
   (let [hs (cap/hinting (cap/prefetcher (:records kb)) cap/recovery-hint-chunk
                         (reads/as-stored-with-functor (:index kb) f))]
     (->> (if r (progress/each r hs) hs)
          (keep #(p/get-sentex (:records kb) %))
          (filter #(and (nil? (:antecedent %)) (not (sx/negative? %))))))))

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
  "The arms for a predicate-metadata mark — `(transitive P)`, `(symmetric P)`, … —
  which differ only in the `:props` key they maintain, and which they now read off
  `functor`'s declaration (`pr/prop-kind`) rather than take as a parameter.  Reading
  it is what lets `spec/::prop-kind` be derived from the declarations rather than from
  this table: a kind exists because a term declares it, not because an arm was written
  with it.

  `skip` is the set of predicates whose property is the engine's own to compute — the
  `closure-relations` genl / genlCx, whose transitivity comes off the cached closures.
  A `(transitive genl)` fact stays stored and queryable, but its prop is **not** marked,
  so `has-prop? :transitive genl` stays false and genl is never handed to the generic
  closure prover.  The skip is applied identically on integrate, disintegrate and
  rebuild, so the live and recovered stores agree.

  Why a mark that arrives by *derivation* must install like an asserted one is the
  `:derived` facet's argument, and it lives with the facet on `predicates/prop`."
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
  "One entry-shape for all three equality relations: they produce the same class,
  and the whole of their difference — whether a preferred term is named — is read
  off the sentence by `kb/preferred-term` inside the arms.

  Two compound shapes are **not** a symbol merge, and each arm dispatches on them:

  * `(rewriteOf T E)` with a compound `E` is a NAT reify-to-term declaration
    (docs/nat.md) — a quoted NAT expression the partition (over symbols) can hold no
    part of.  Skipped by every arm: stored as an ordinary quoting fact, findable by
    the term index, never in the partition.

  * `(equals L R)` with a variable-bearing compound side is a **schematic equational
    rule** — an oriented rewrite, cached in the taxonomy's rewrite-rule set rather
    than the partition (docs/equality.md, symbolic equational reasoning).  Its add arm
    orients and migrates; its removal drops the rule (the sweep collects the twins and
    `refresh-supersessions` revives the originals); its rebuild re-orients on recover.

  `wff/equality-problems` waves both compound shapes through the same way.

  The add arm is `integrate-equality-sentex`, named rather than written out here
  because the derivation path calls it too: a rule concluding one of the three merges
  like an asserted one, and it reaches the arm by that name for the reason stated
  there."
  {:integrate    integrate-equality-sentex
   ;; the merge (or rule) survives while any other sentex still asserts it; when the
   ;; last supporter goes the class splits (or the rule leaves) and
   ;; the removal choke point's `reconcile-removed-supersession!` gives the displaced
   ;; spellings back —
   ;; which moves a census and a NAF judgement exactly as the merge moved them, so the
   ;; re-check trigger is owed on this side too
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
   :wff          wff/equality-problems})

(defn check-entries
  "Refuse an ill-formed table at namespace load, so add/remove symmetry is a
  structural property rather than a review item.

  Two shapes are refused.  An entry with *some* of the cache arms — an `:integrate`
  whose `:disintegrate` or `:rebuild` is missing (or any other partial triple) is
  exactly the mirrored-cond drift this table exists to end: the cache would fill on
  assert and leak on retract, or come back wrong after `recover`.  And an entry with
  no arm at all, which is a typo.  `:mismatch` says which — `:partial-cache-triple`
  or `:no-arm` — the same discriminant every other `:bad-table-entry` in the tree
  carries, so a caller reads one key rather than guessing from the message.  Returns
  `entries` unchanged so it can wrap the def."
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
  `tax/add-genlCx`), but only when the stored sentence's **complete shape** is exactly
  `(expected-f <symbol> <symbol>)` — a valid two-endpoint taxonomy edge.

  `reindex` replays the **stored** sentexes rather than the checked ones
  (`post-taxonomy-supporters!`), and `stored-declarations` is a candidate read over the durable predicate extent, not proof that
  every returned sentence has the requested functor or the current WFF shape.  So a store
  an older, foreign, or stale writer left reaches here as a malformed edge, and reading it
  positionally (`[_ a b]`) reads three distinct malformations as a spurious edge:

    - a 2-element declaration (`(genl foo)`, a metatype membership, an `arity` / `arg`
      row) binds the member as `a` and nil as `b` — the nil enters the closure's node set,
      and `strong-components` throws on it (`java.util.ArrayDeque` rejects a null element)
      the moment `restore-depths` walks a loose relation (the `recover` crash of #80);
    - an **over-arity** row (`(genl a b surplus)`) binds `a` and `b` and silently discards
      the surplus, fabricating `(genl a b)` from a sentence that never was one;
    - a **wrong-functor** row (`(disjoint a b)` handed up under the genl root by a foreign
      or stale index) has symbols in both positions and would replay as `(genl a b)`.

  The last two both satisfy `(symbol? a) (symbol? b)`, so the endpoint-only guard passed
  them; requiring the whole shape — arity three, the literal expected functor, both
  endpoints symbols — is the producer boundary #80 drew, applied to the whole sentence.

  Dropping the malformed declaration is `rebuild-tms`'s discipline for a justification the
  store cannot root: the bad sentex is skipped and counted, never a spurious edge added.
  Returns tax."
  [add tax sentence expected-f id ctx]
  (if (and (= 3 (count sentence))
           (= expected-f (first sentence))
           (symbol? (second sentence))
           (symbol? (nth sentence 2)))
    (add tax (second sentence) (nth sentence 2) id ctx)
    (do (when-let [v *edge-replay-skips*] (vswap! v inc)) tax)))

(defn- cover-arms
  "The integrate / disintegrate / rebuild triple the three whole-and-parts declarations
  share, differing only in `kind` — which of the two claims the part list makes
  (`tax/cover-kinds`).

  Each arm does two things, because the declaration says two things. The part list goes
  into the taxonomy under one key (`tax/add-cover`), which is what `disjointness-test`
  reads for a partition and what `CoveringProver` reads for either. And a `genl` edge
  per part goes in **against the covering sentex's own handle**, so the specialization
  the cover rests on is one the closure holds rather than one every reader has to
  re-derive: belief follows the declaration through the same supporter map an asserted
  edge uses, and retracting the cover drops the edges with it. The edges post the
  exception re-check the `genl` arm posts, for the reason that arm posts it.

  A part equal to the whole installs no edge — `wff/covering-problems` refuses the
  declaration, and the rebuild arm replays a store that never passed it."
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
  "What the engine *does* about each functor it interprets, keyed by functor: the
  integrate / disintegrate / rebuild triple and the structural `:wff` check.

  A **map**, deliberately, where the table it feeds is an ordered vector: the order is
  the declaration's (`predicates/entries`), because it is a statement about the
  predicates rather than about the arms, and `post-taxonomy-supporters!` replays it.  Writing
  the arms in an order of their own would give the table two orders that had to agree
  and no way to notice when they stopped.

  What each functor *says* — its sentence shape, the `:props` kind it maintains,
  whether it runs on the derivation path — is not here; it is one entry in
  `vaelii.impl.predicates`, which sits below `taxonomy` and `wff` and so can be read
  by the layers this namespace cannot reach.  `entries` below joins the two and
  refuses a disagreement."
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
                       ;; Members already asserted are *recorded*, not turned into a
                       ;; clique of `(disjoint a b)` sentexes; `tax/disjoint?` consults
                       ;; the membership directly.  A member asserted later is picked up
                       ;; by the structural member arm in `integrate-sentex`.
                       ;;
                       ;; **Stored, not believed**, which is the discipline every other
                       ;; retroactive sweep here follows (`lift-existing`,
                       ;; `equate-existing`, `entail-existing`) and for a sharper reason:
                       ;; this one records a *supporter*.  The structural member arm is
                       ;; belief-blind, so a membership asserted after the declaration is
                       ;; counted whatever its label — and a belief-filtered sweep here
                       ;; would skip a defeated membership asserted *before* it, leaving
                       ;; that handle out of the supporter families entirely.  Clearing the
                       ;; defeat could then never revive the entry, since the reconcile
                       ;; has no key to find: belief depending on the order the defeat and
                       ;; the declaration arrived in, and permanently.  It would also put
                       ;; the live KB and a reindexed one at odds over one store,
                       ;; `post-taxonomy-supporters!`' second pass reading what is stored
                       ;; through this very function.
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
    ;; `(sibling_disjoint C)` is the metatype clique keyed off the genl closure: only the
    ;; mark is stored, and `tax/disjoint?` reads C's specializations off `specs`.  So
    ;; there is no member sweep to run on integrate — unlike `disjoint_metatype`, nothing
    ;; was recorded to pick up — and the three arms are the plain mark/unmark, the shape
    ;; `disjoint` itself has.
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
    ;; `(functionalInArg P n)` says the other arguments of `P` determine argument `n` —
    ;; `functional` generalized off its fixed arg-2 slot.  Cached exactly as `arity` is
    ;; and for the same reason: the definitional checks read it on every assert, and a
    ;; declaration is not something to re-derive per write.
    ;;
    ;; Registered here beside `arity` rather than through `prop-entry`, which cannot
    ;; carry the integer, and deliberately NOT the way `transitiveInArg` is: that one
    ;; licenses tuples and is read for the goal's own predicate, this one refuses them
    ;; and is read up the hierarchy (`tax/functional-in-arg-over`).  The two share a name
    ;; shape and sit on opposite sides of the prover/checker divide — the same line
    ;; `props-over`'s docstring draws, and the reason `functional` is absent from the
    ;; recheck table above.
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
    ;; The three commutativity relations.  `(commutativeInArgAndRest P f)` licences every
    ;; position from `f` to the literal's own arity to permute; `(commutativeInArgs P p …)`
    ;; licences exactly the positions named; `(commutative P)` licences every position,
    ;; which is the tail from position 1.  All three are cached for `arity`'s reason twice
    ;; over: the canonicalizer reads them on **every** assert, not only on a declaration,
    ;; so a re-query per write would be a read on the hottest path the engine has.
    ;;
    ;; One table between them, since the three written shapes are one runtime group
    ;; descriptor (`sentex/commuting-components`).  Registered here rather than through
    ;; `prop-entry`, which carries no position, and unlike `functionalInArg` these read
    ;; **down** to nothing: the mark is read off the literal's exact functor, because a
    ;; sentex has one key and a `genl` edge below a commutative predicate does not make
    ;; the sub-predicate commutative (`res/kb-sentex`, `tax/commuting-groups`).
    ;;
    ;; `commutative` installs its group **here**, beside the `:commutative` prop the mark
    ;; is queried by, rather than through a core.txt rule deriving `(commutativeInArgAndRest
    ;; P 1)`.  The two spellings state one licence, and a derivation between them is a
    ;; rule whose conclusion re-derives its own premise: the pair was written as a cycle
    ;; and the backward engine has no ancestor-goal guard to stop on it
    ;; (`provers/candidate-rules`).  Installing both marks at their own arms leaves the
    ;; canonicalizer one table to read and the resolution prover no cycle to walk, and the
    ;; equivalence stays in core.txt as two `set/inertRule`s that document it.
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
     :wff          wff/prop-problems}
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
    ;; the mark plus the retroactive lift; the lift's justifications need no removal arm
    ;; of their own — each is justified by this sentex, so the ordinary
    ;; dependency-directed sweep withdraws them when it goes.  The rebuild replays the
    ;; mark only: the lifted copies are already stored.  The integrate arm returns the
    ;; `{:new :violations}` the equality arms return, so a retroactively lifted copy is a
    ;; chaining seed like any other new content.  This is the one mark the declaration
    ;; withholds `:derived` from, and the reason is stated there.
    'decontextualized_predicate
    (assoc (prop-entry 'decontextualized_predicate)
           :integrate (fn [kb sx h]
                        (let [pred (second (:sentence sx))]
                          (tax/mark-prop (reasoning/taxonomy kb) :decontextualized pred h (:context sx))
                          (lift-existing kb pred h))))
    'forced_decontextualized_predicate (prop-entry 'forced_decontextualized_predicate)
    ;; A forced-monotonic declaration is a switch: its arriving or leaving rewrites the forced
    ;; memberships over what the predicate reaches and re-joins the rules in that reach,
    ;; so the stored content a firing swept while held void comes back
    ;; (docs/nmtms.md, "The forced-monotonic set")
    'forced_monotonic_predicate (forcing-entry 'forced_monotonic_predicate)
    'forced_monotonic_between_predicates (forcing-entry 'forced_monotonic_between_predicates)
    ;; `(target_following_predicate P)` marks P as forming a **target-following
    ;; meta-sentex**: a `(P … (sentexHandle H) …)` names sentex H and must not outlive it,
    ;; so a teardown that removes H removes the meta with it
    ;; (`core/retract-following-metas!`).  Belief-following and recover-safe like the
    ;; marks above.  koinii's reply acts (`answers` / `disputes` / `endorses` /
    ;; `justifies`) declare it, so retracting a claim cascades to the replies about it —
    ;; the property a message bus cannot give.  The engine's own meta-sentexes (`except`
    ;; / `exceptWhen`) deliberately do **not** carry it: a rule's exception orphans
    ;; harmlessly when the rule is retracted (`meta_sentex_test`), leaves the re-check
    ;; index at the removal choke point, and that amend-in-place behavior is correct as is — the
    ;; mark is opt-in precisely to leave it untouched.
    'target_following_predicate (prop-entry 'target_following_predicate)
    ;; `(abducible_predicate P)` is what lets abduction hypothesize a `(P …)` when a proof
    ;; dead-ends on one (docs/abduction.md).  Deliberately **not** decontextualized,
    ;; unlike the marks above it: `transitive` / `symmetric` are claims about a predicate
    ;; that hold wherever it is mentioned, while this is a *policy* of the context that
    ;; grants it — one theory may be willing to assume `was_washed` and another, reading
    ;; the same predicate, may not.  The scoped `has-prop?` arity is what reads it, so the
    ;; grant reaches exactly the contexts that see the grantor.
    'abducible_predicate (prop-entry 'abducible_predicate)
    ;; `(closed_extent_predicate P)`: a scoped mark, as `abducible_predicate`'s is.  The
    ;; re-check postings for the rules it governs are `recheck-on-sentence`'s, which runs
    ;; on every move of the grant's belief and not only on its storage (docs/naf.md).
    'closed_extent_predicate (prop-entry 'closed_extent_predicate)
    ;; `(closedExtentForArg P n v)`: the same mark under `:closed-extent-arg`, the
    ;; presence check `provers/closed-extent-for-arg?` reads.
    'closedExtentForArg
    (assoc (prop-entry 'closedExtentForArg) :wff wff/closed-extent-for-arg-problems)
    ;; `(modal_predicate P)` is what makes `(P agent sentence)` project into the agent's
    ;; context (docs/belief.md) — `BeliefProjectionProver` reads it.  Not
    ;; decontextualized, and for `abducible_predicate`'s reason: which predicates a theory
    ;; reads modally is a *policy* of the context that grants it, so the scoped
    ;; `has-prop?` arity reaches exactly the contexts that see the grant.  `believes`
    ;; ships granted in core.txt; `knows` / `desires` / `intends` are one assertion away.
    'modal_predicate (prop-entry 'modal_predicate)
    ;; a NAT function's kind is predicate metadata like the marks above —
    ;; `(reifiable_function F)` marks `:reifiable`, `(unreifiable_function F)`
    ;; `:unreifiable`, belief-following through the same prop cache.  The reify presence
    ;; check (`vaelii.impl.nat`) reads `:reifiable` in memory, so declaring a function
    ;; reifiable is what turns the reify pass on.  Their argument is a function name (a
    ;; `FruitFn`-shaped constant), so `prop-problems` — which refuses an individual — is
    ;; replaced by `function-decl-problems`.
    'reifiable_function   (assoc (reifiable-entry) :wff wff/function-decl-problems)
    'unreifiable_function (assoc (prop-entry 'unreifiable_function) :wff wff/function-decl-problems)
    ;; `(contextArgSubrelation F pos R)` declares the structural genlCx ordering: two
    ;; `F`-contexts identical except at argument `pos` are ordered by sub-relation `R` on
    ;; that arg, so the producer materializes `(genlCx sub super)` when `R` holds
    ;; (docs/context-nat.md).  Read back through the index per producer run like the
    ;; correspondence declaration, so the entry is the wff arm alone.
    'contextArgSubrelation {:wff wff/context-arg-subrelation-problems}
    ;; `(functionCorrespondingPredicate F P N)` is read by the reify (both ways —
    ;; docs/nat.md), which reaches it through the index rather than a cache: the
    ;; declaration is consulted once per NAT, where the reify is already probing for a
    ;; `rewriteOf` target and a dedup, and the *presence check* a KB declaring none pays
    ;; is an O(1) functor count.  So there is nothing to integrate, and the wff arm is the
    ;; whole entry.
    'functionCorrespondingPredicate {:wff wff/correspondence-problems}
    ;; The four argument constraints are consumed at match time — the declarations
    ;; themselves are read back through `matches-visible` per check, not cached — but
    ;; **which predicates are the subject of one** is marked, because a constraint binds
    ;; the tuples of every predicate beneath the one it names and the check therefore asks
    ;; that question per super-predicate on every assert (`tax/arg-declaration-props`,
    ;; `res/constraining-predicates`).
    'arg       (assoc (prop-entry 'arg)       :wff wff/arg-constraint-problems)
    'genlArg   (assoc (prop-entry 'genlArg)   :wff wff/arg-constraint-problems)
    'quotedArg (assoc (prop-entry 'quotedArg) :wff wff/arg-constraint-problems)
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
    'quotedArgAndRest (assoc (prop-entry 'quotedArgAndRest) :wff wff/covering-constraint-problems)
    ;; the homogeneity constraints share the covering forms' shape — a relation, an
    ;; optional start, a type — and so their wff arm
    'interArgs       (assoc (prop-entry 'interArgs)       :wff wff/covering-constraint-problems)
    'interArgAndRest (assoc (prop-entry 'interArgAndRest) :wff wff/covering-constraint-problems)
    ;; The two preservation declarations really are wff-only — read back per query, with
    ;; the transitivity of the relation they name checked here because `arg`'s open-world
    ;; reading cannot (docs/inherit.md).
    'transitiveInArgInverse {:wff wff/arg-preserving-problems}
    'transitiveInArg        {:wff wff/arg-preserving-problems}
    ;; the three definitional collection relations: stored as ordinary facts and expanded
    ;; into forward rules at assert (docs/defns.md), so the wff arm — the member-variable
    ;; check — is the whole table entry, exactly as it is for `transitiveInArg`, which is
    ;; likewise read back rather than integrated
    'defnNecessary  {:wff defn-wff-problems}
    'defnSufficient {:wff defn-wff-problems}
    'defnIff        {:wff defn-wff-problems}
    ;; `different` is never stored at all — its wff arm *is* the refusal
    'different      {:wff wff/different-problems}
    ;; the minimal common genls and maximal common specs, computed from the genl closure
    ;; by provers/CommonGenlProver and never stored
    'minCommonGenl  {:wff wff/common-genl-problems}
    'maxCommonSpec  {:wff wff/common-genl-problems}
    ;; ...and the query operators, never stored either, for the same reason: negation as
    ;; failure (docs/naf.md) and the five aggregates below, which are the same family and
    ;; take the same arm (docs/aggregate.md).  `forall` is sugar for a nested `unknown`
    ;; and is desugared at the rule entry point, so nothing ever stores one either.
    'unknown        {:wff wff/naf-problems}
    'thereExists    {:wff wff/naf-problems}
    'forall         {:wff wff/naf-problems}
    ;; `bravely` / `cautiously` read the current dilemmas (in every optimal labeling, in
    ;; some) and are answered by the opt-in :brave-cautious prover — never stored, for the
    ;; same reason the aggregates are not: a stored one is a computed value nothing keeps
    ;; current (docs/labeling.md).
    'bravely        {:wff wff/brave-cautious-problems}
    'cautiously     {:wff wff/brave-cautious-problems}
    ;; the two durations the :duration reasoner computes from the stored lengths, and
    ;; never reads stored (docs/duration.md)
    'totalDuration   {:wff wff/duration-problems}
    'overlapDuration {:wff wff/duration-problems}}
   ;; the eight predicate-metadata marks, each differing only in the `:props` kind its
   ;; declaration names.  `commutative` is the ninth mark and is **not** here: it
   ;; maintains a `:props` kind like these and a commuting group besides, so its arms are
   ;; written out above rather than built by `prop-entry`.
   ;;
   ;; `anti_symmetric` and `anti_transitive` sit in the same list as
   ;; the six below them because the kind is read off the declaration: theirs are the two
   ;; functors whose keyword is not their own spelling (`anti_transitive` stores under
   ;; `:anti-transitive`), so converting the functor would put them somewhere else
   ;; (`pr/prop-kind`).
   ;; `(anti_symmetric P)` derives `(equals a b)` from a believed converse
   ;; (`derive-antisymmetric-equalities`); `(anti_transitive P)` convicts the two-step
   ;; chain and the direct step together (`checks/antitransitivity-problems`).  The mark
   ;; is what both of those read, and reading it up the predicate hierarchy
   ;; (`tax/props-over`) is what makes a `parentOf` mark convict a `fatherOf` chain.
   (into {} (map (fn [f] [f (prop-entry f tax/closure-relations)]))
         '[transitive symmetric asymmetric reflexive functional irreflexive
           anti_symmetric anti_transitive])
   ;; the three equality relations share one entry-shape
   (into {} (map (fn [f] [f equality-entry])) kb/equality-predicates)
   (into {} (map (fn [f] [f {:wff wff/naf-problems}])) (keys sx/aggregate-functors))))

(defn- declared-half
  "The half of a table entry `vaelii.impl.predicates` owns: the `:props` kind a mark
  maintains, and whether the entry's arms run on the derivation path as well as the
  assert path.

  Both are statements about the *predicate* — a mark that arrives by derivation must
  install like an asserted one; a kind exists because something declares it — rather
  than about the functions, which is why they are read off the declaration rather than
  written beside the arms.  The whole argument for each sits on the facet in
  `predicates`."
  [term]
  (cond-> {}
    (pr/prop-kind term)         (assoc :prop (pr/prop-kind term))
    (contains? pr/derived term) (assoc :derived? true)))

(defn check-declarations
  "Refuse a table whose arms and declarations disagree — the cross-layer half of
  `check-entries`, which sees only the arms and so can only check that they mirror each
  other.  Three disagreements are refused, all at namespace load:

  * a functor with arms and no declaration, or a declaration and no arms.  The two are
    one enumeration now, and a functor in only one of them is a predicate the engine
    either interprets without saying so or says something about and does nothing with.
    `arm-functors` is the set of functors the `arms` map keys, read **before** `entries`
    filters to `pr/in-special-table` — so an arm keyed on a functor no declaration places
    in the table is refused here rather than left out of the join unreported.  The
    one-argument arity reads the functors off `entries` itself, for a caller driving the
    validator over a hand-built table.
  * a `:cached` declaration whose arms have no cache triple, or the reverse.
  * a `:checked` declaration whose arms have no `:wff`, or the reverse.

  `check-entries` catches a *missing* arm; neither validator can catch an arm attached
  to the wrong functor, which is what `special_table_test` and `predicates_test` are
  for.  Two validators at two layers, each checking what it can see: they are not to be
  merged.

  One `:type` between them — `:bad-table-entry`, discriminated by `:mismatch` — for the
  reason `check-entries` already gives itself two shapes under one word: whichever way
  the table is bad, the caller catching it is the namespace load, and there is nothing
  a second keyword would let that caller do."
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
  "The special-predicate dispatch table: an **ordered** vector of `[functor spec]`
  pairs, joined from the arms above and the declarations in `vaelii.impl.predicates`.

  **The order is the declaration's** — `predicates/entries` filtered to the functors
  this table holds an entry for.  `post-taxonomy-supporters!` replays it top to bottom and a
  rebuild arm may read what an earlier one wrote (metatype membership reads the marks;
  nothing else is order-sensitive today, and keeping the assert path's traditional
  order adds no work), so the order is content and belongs with the other content.

  This vector is *the* functor enumeration the four walks use: integrate,
  disintegrate, rebuild and wff all walk it, so a predicate declared and armed is added
  to all four at once, `check-entries` refuses it half-armed and `check-declarations`
  refuses it armed without being declared — the latter reading the `arms` map keys, which
  hold every armed functor, not this filtered vector, which by construction holds only the
  declared ones.  `table` below is the lookup table."
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
  "Structural well-formedness problems for `sentence` (empty if OK) — the `:wff`
  column of the table, walked.  A sentence whose functor has no entry (or no `:wff`
  arm) is structurally unconstrained here; its argument *types* are still checked
  by the arg constraints.

  `context` is the asserting (or, on the derivation path, the landing) context, passed
  to every arm.  Every arm is a context-free structural check and ignores it.  A nil
  `tax` skips the checks that read stored content: the `genl`, `genlCx`, cover and
  `rewriteOf` cycles and the transitivity a preservation names.  An import reads it so,
  since the content a check reads can arrive in a later frame.

  A `not` over a `pr/query-only` term, at any depth of `not`s, is checked by that
  term's arm, so `(not (unknown S))` is refused as `(unknown S)` is: the negation of a
  query is a query too."
  [tax sentence context]
  (let [body     (loop [s sentence] (if (sx/negation? s) (recur (second s)) s))
        sentence (if (and (sequential? body) (contains? pr/query-only (first body)))
                   body
                   sentence)]
    (if-let [wf (:wff (get table (and (sequential? sentence) (first sentence))))]
      (wf tax sentence context)
      [])))

(defn wff-violation
  "The same check as a **value**, for content a rule *derived* rather than one a
  caller asserted: nil when `sentence` is well-formed, else a violation map in the
  shape `checks/constraint-violation` returns.

  `assert` checks this on the way in, but a rule may conclude a special predicate —
  `(implies (relates ?x ?y) (genl ?x ?y))` derives taxonomy edges — and the
  derivation path had no such check.  A derived edge reaches the closure through
  `integrate-transitive`, so a rule could close a `genl` cycle that the same edge
  asserted directly would have been refused for, leaving `genls`/`specs` cyclic —
  and those are what matching, placement and stratification all read.

  Dropped and reported rather than thrown, like every check on that path: chaining
  is a fixpoint and must not abort halfway through one."
  [kb sentence context]
  (wff-violation* kb sentence context))

(defn- structural-integrate
  "The **structural** integrate arms — the ones no functor can key, dispatched on the
  sentence's *shape* instead: a rule (any functor can head an implication), an
  exceptWhen meta-sentex (its second argument is a `(sentexHandle H)`), a visibility
  `except`, and a disjoint metatype's member (the functor is the metatype itself,
  known only at runtime).  Shared by `integrate-sentex` (the assert path),
  `integrate-twin` (migration) and `derived-sentex-added` (the derivation path), so a
  migrated rule / meta twin and a rule-derived except reach exactly the indexing an
  asserted one does.

  `derived?` drops the **rule** arm and nothing else.  The derivation path's own caller
  posts a generated rule by name and before it justifies it (`chain/mint-rule` ->
  `index-rule-sentex`), because a mint is dispatched as a rule rather than as a fact and
  never reaches here; running the arm again would post the same rule twice and mark it
  for a second blanket re-check.  Every other arm is content the derivation path can
  reach only through this walk."
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
       ;; a member (M T) of a disjoint metatype: record T's membership, which is what
       ;; makes it disjoint from every other member.  Recording is O(1) and reversible;
       ;; asserting a `(disjoint t o)` per existing member would be O(n) sentexes per
       ;; member — quadratic overall — and premises no retraction could reach.
       ;; This runs only when the mark is **stored**, not believed: the membership is a
       ;; supporter, and belief follows it through `refresh-cache-support` — a member
       ;; stated while the mark is defeated is recorded now and separates the moment
       ;; the mark revives, in either order of arrival.
       (and (= 1 (nm/arity sentence)) (tax/stored-disjoint-metatype? (reasoning/taxonomy kb) f))
       (tax/add-metatype-member (reasoning/taxonomy kb) f (first (nm/args sentence)) handle
                                (:context sentex))))))

(defn- run-integrate-arms
  "Run the one integrate arm that fits `sentex`: the table `:integrate` arm for a
  special functor, else the structural arm.  Shared by `integrate-sentex` (assert
  path) and `integrate-twin` (migration), so the dispatch lives in one place."
  [kb sentex handle]
  (if-let [e (get table (nm/functor (sx/sentence-of sentex)))]
    (when-let [g (:integrate e)] (g kb sentex handle))
    (structural-integrate kb sentex handle)))

(defn integrate-sentex
  "Reflect a newly stored sentex into the taxonomy / rule index / disjointness —
  the `:integrate` column of the table, walked, plus the structural arms above.

  Returns `{:new [handles] :superseded [[datum reason]] :violations [v]}` for an
  equality sentex — the twins it created are chaining seeds and the violations are
  the caller's to report — and nil for everything else.  (Only the equality arm
  has anything to say; every other arm mutates a cache and its return value is
  whatever that mutator handed back, so the result is normalized here rather than
  left for the caller to sort out.)"
  [kb sentex handle]
  (let [result (run-integrate-arms kb sentex handle)]
    (when (map? result) result)))

(defn integrate-twin
  "Full integration for a **migrated twin** — a restated declaration or fact the
  equality migration derives (`migrate-sentex`).  A twin must reach the same caches
  an asserted declaration would, or its class-representative spelling is stored and
  believed while the taxonomy never learns what it *declares*: a merged `(disjoint
  dog cat)` twin `(disjoint canine cat)` must reach `add-disjoint`, a `(transitive
  containedBy)` twin must reach `mark-prop`, and a migrated rule twin must reach the
  rule index or it never fires.  So this runs the same arms `integrate-sentex` does,
  where `derived-sentex-added` (the forward-chaining conclusion path) narrows the table
  half to the `:derived?` entries and drops the rule arm its own caller posts by name.

  The **equality arm is skipped**: a twin is never an equality sentex (those are held
  back from migration, `kb/rewritable-sentex?`), and running `migrate-class` from
  inside a migration would recurse.  Then the same re-check post every derived
  sentex gets — a migrated fact / declaration arriving is a trigger like an asserted
  one.

  Migration can run inside a forward-chaining pass (`derive-functional-equalities`
  infers an equality from a derived fact), so the table/structural arms can fire
  mid-fixpoint.  That is safe: none of them re-enter `assert` or `chain` — they add
  cache entries, justifications, and re-check queue items — and the common functional
  merge is of two individual *values*, whose twins are facts that match no
  declaration arm at all."
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
          ;; Deregistration **recomputes** the re-check predicates from the stored
          ;; sentex rather than trusting anything a caller has in hand.  The index
          ;; holds no derived state, so a mismatched deregistration only leaks a stale
          ;; posting — harmless, but recomputing is the rule that cannot drift.  The
          ;; rule's `unknown` antecedents' predicates come back out here; an exceptWhen
          ;; exception's are withdrawn by its own meta-sentex leaving (above).
          (let [sd (rules/separation-denial-predicates-of (reasoning/taxonomy kb)
                                                          (sx/sentence-of sentex))]
            (when (or (rules/rechecked? sentex) (seq sd))
              (rules/unindex-exception! (:index kb) (:id sentex)
                                        (distinct (concat (rules/recheck-predicates sentex) sd)))))
          ;; ...and the firings it refused before they could become justifications.  A
          ;; refusal is dead when its rule goes, and this is the event that says so —
          ;; entries are otherwise dropped lazily, when a queued rule's record is
          ;; walked, and a departed rule is never queued again.
          (swap! (reasoning/refused kb) #(-> (dissoc % (:id sentex)) (forget-kinds (:id sentex)))))
      ;; a member leaving a disjoint metatype: it stops being disjoint from the rest.
      ;; This checks storage like the integrate arm, so a member retracted while the mark
      ;; is defeated drops its support entry rather than leaving it behind for good.
      (and (= 1 (nm/arity sentence)) (tax/stored-disjoint-metatype? (reasoning/taxonomy kb) f))
      (tax/del-metatype-member! (reasoning/taxonomy kb) f (first (nm/args sentence)) (:id sentex)))))

(defn integrate-transitive
  "The **table** half of `derived-sentex-added`: for a functor the table keys, only the
  arms flagged `:derived?` — the genl / genlCx closure edges, and the marks that carry
  the flag for their own reasons — run for a rule-derived conclusion, because the rest
  of integration either does not apply to a derived sentex or would re-enter `assert`
  from inside forward chaining.  Without this on the derivation path, a rule concluding
  `(genl a b)` stored and believed the sentex while the taxonomy never learned the edge
  — and `recover`, which reads the store, then disagreed with the running KB about what
  the KB entailed.  (A derived *equality* is not reached from here:
  `chain/place-fact-conclusion` calls `integrate-equality-sentex` by name, because this
  fn discards what an arm returns and there the return value is the work — the twins and
  the violations.)  A functor the table does **not** key is the structural walk's, not
  this one's."
  [kb sentex handle]
  (let [e (get table (nm/functor (:sentence sentex)))]
    (when (:derived? e)
      ((:integrate e) kb sentex handle))))

(defn derived-sentex-added
  "The derivation-path add choke point: everything that must happen because a
  **derived** sentex landed in the store — the integration arms a derived sentex may
  reach, and the exception re-check post, since a derived fact is a re-check trigger
  like an asserted one (an exception may be stated over a predicate that only ever
  arrives by inference — the cried-wolf case, where `liar` is concluded by another
  rule).

  **The dispatch is `run-integrate-arms`'s, narrowed.**  A functor the table keys runs
  its `:integrate` arm iff the entry is flagged `:derived?` (`integrate-transitive`);
  a functor it does not key runs the structural walk, minus the rule arm the caller
  posts by name (`structural-integrate`'s `derived?`).  Both halves have to be here or
  the derivation path reaches a strictly smaller set of caches than `recover`'s rebuild
  does, and the running KB and the restarted one then disagree about one store: a rule
  concluding a disjoint metatype's member separated nothing until a restart replayed it,
  and a rule-derived `(except (sentexHandle H))` hid its target from the *reads* — the
  index holds it from the store primitive (`kb/create-sentex`) — while no firing that
  used H was ever queued for the sweep.

  **The except arm's `reconcile-belief-change` is called inline, mid-fixpoint, and
  that is safe.**  It does not re-enter chaining or settling: `tax/refresh-beliefs` is a
  `swap!` over the taxonomy that reads `jtms/in?` and writes cache entries — no assert, no
  chain, no settle, and no relabel.  It is scoped to the
  arriving except and the handle it hides, so it costs two handles' worth of edge
  lookups rather than the vocabulary's.  `recheck-except` beside it only pushes rule
  handles onto the re-check queue, which is what the settle around this drains; that is
  exactly what the assert path does from inside its own `integrate-sentex`.

  The one ordering difference from the assert path is that `mark-premise` runs *before*
  `integrate/sentex-added`, where two of this fn's four callers run it before the
  justification — so the except is stored and indexed a few lines
  ahead of being believed.  Nothing reads a scoped taxonomy answer between the store and
  the justification (the callers write a justification and nothing else), and the JTMS
  labels the region as the justification lands, so the first read after it recomputes
  against settled belief.

  Lives here rather than beside `sentex-added` in `vaelii.impl.integrate` because
  the equality arms are themselves derivation sites: a migrated twin and a
  functional-inferred `equals` are derived sentexes, and hand-rolling this pair at
  those sites is exactly the copy-paste the choke points exist to end.  Callers:
  forward chaining's `place-conclusion`, the `decontextualized_predicate` lift, the
  argument-constraint entailment, and `derive-equality`."
  [kb sentex handle]
  (let [sentence (sx/sentence-of sentex)]
    (if (contains? table (nm/functor sentence))
      (integrate-transitive kb sentex handle)
      (structural-integrate kb sentex handle true))
    (recheck-on-sentence kb sentence)))

;; ---- rebuild: recover's replay of the table ------------------------------

(defn post-taxonomy-supporters!
  "Post the taxonomy's supporter families (`tax/post!`) for every stored
  declaration in `kb`: the `:rebuild` column replayed in entry order over a scratch
  taxonomy whose index store is `kb`'s, then each stored disjoint metatype's members.
  `reindex`'s share of the index that its per-record pass cannot post, since the key a
  declaration installs is the table's to say.  `kb`'s own taxonomy is not touched, and the
  equality relations, whose partition keeps its own supporters, post nothing.

  A stored `genl` / `genlCx` declaration whose positional read is not a well-formed edge
  is dropped rather than posted (`replay-edge`), and the count is warned once — the same
  discipline `rebuild-tms` follows for a justification the store cannot root.  A
  well-formed store never has one; a store an older or foreign writer left a non-edge
  sentex in the genl / genlCx predicate extent does, and posting it would seed a null
  closure node that crashes `restore-depths`."
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
    nil))

(defn rebuild-taxonomy
  "Rebuild the in-memory taxonomy over a cleared one: the believed side of every key the
  index's supporter families hold (`tax/refresh-beliefs` with no region, reading the
  network's labels), and the equality partition and rewrite rules, which keep their own
  supporters, replayed from their stored declarations by the `:rebuild` column.  Reads
  no other record.

  Drops every cache first: a rebuild that merged into the existing one could only ever
  *add*, so an entry whose sentex is gone would survive the recovery that was supposed to
  re-derive it."
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
  :note "`{rule #{refusal}}` and the `:kinds` index; a constraint or lift entry carries the `[genl genlCx]` generations it was refused under, and a settle pass releases it when they move"})

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
