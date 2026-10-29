;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.predall
  "The audits of the predAll / predExists / predInstance / predSpecified matrix: the
  *Specified* pair's and the *Exists* four's (docs/predall.md, resources/kb/upper/core.txt).

  Reached from outside through `vaelii.core/specified-violations`,
  `vaelii.core/exists-violations` and `vaelii.core/all-specified-violations`, which are
  thin delegations to the readers here.
  The audit reads through `vaelii.core/ask`'s per-context step (`quasiquote/ask-prepared`),
  so this namespace sits **below** `vaelii.core` and `vaelii.core` requires it — no layering
  inversion.  The audit still answers what a user's `ask` answers: it passes only concrete
  contexts and expands no rule, and the `genlCx` ancestor scoping is applied in the matching
  layer below (docs/namespaces.md, \"The layering\").

  Where the *Instance* relations generate real inference and the *Exists* relations are
  records beside a sanctioned placeholder functor, audited for existence alone
  (`exists-violations`), `predAllSpecified` / `predSpecifiedAll` are an **integrity
  audit**: given a declaration that every instance of a collection ought to have a
  *determinate*, contract-satisfying filler, the reader here reports the instances
  with no admissible one — `{:status :audited :violations #{…}}` — or an explicit
  `{:status :gap …}` declaration-contract diagnostic.  It is not a
  stored rule and concludes nothing — it reads the declaration and the beliefs and hands
  back the violations, the way a solve-time report does.

  **Indeterminate = the `indeterminate_term` category.**  A filler counts as determinate
  unless it is a member of the extensible `indeterminate_term` collection (core.txt).
  Skolem constants are its built-in first member — a reified NAT whose expression is a
  `SkolemFn` application (docs/skolem.md), detected structurally because a skolem's
  membership is never a stored fact — and a further kind is added with
  `(genl NewKind indeterminate_term)`.  Whether a non-skolem NAT is determinate by default
  is not decided: a plain individual, a literal and an *Exists* placeholder alike are
  all treated as determinate here, which is what makes `predAllSpecified` the exact
  antagonist of `predAllExists`."
  (:require [vaelii.impl.budget :as budget]
            [vaelii.impl.defining :as defining]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.quasiquote :as quasiquote]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn indeterminate-term?
  "Is `term` an **indeterminate** filler in `ctx` — a member of the extensible
  `indeterminate_term` category (core.txt)?  A skolem constant is the built-in first
  member, read off its `SkolemFn` minting expression because a skolem's membership is
  never a stored fact; a further kind added with `(genl NewKind indeterminate_term)` is
  picked up through ordinary collection membership.

  `vaelii.impl.provers/indeterminate-term?` **is** the implementation, so the audit and
  the `different` prover's UNA identity exemption cannot disagree about a term.  This
  namespace sits above the prover registry, which is what makes the call possible; two
  copies agreeing by inspection did diverge, on a membership one reader derived and the
  other read as stored.

  A non-skolem NAT that is not declared an `indeterminate_term`, a bare individual and a
  literal are all determinate; the blanket non-skolem-NAT determinacy question is not
  decided."
  [kb term ctx]
  (provers/indeterminate-term? kb term ctx))

(defn- ask?
  "Is `goal` answerable in `ctx`?  The boolean form of `quasiquote/ask-prepared`, matching
  `vaelii.core/ask?`'s no-clock branch."
  [kb goal ctx]
  (boolean (seq (quasiquote/ask-prepared kb goal ctx))))

(defn- slot-typings
  "The visible slot-`n` typing constraints binding `pred`'s tuples in `ctx`, as a set
  of `{:check :membership|:subtype|:type-position :type t}` entries — one per instance
  constraint (`arg`, or an `argAndRest` / `args` reaching `n`: membership) and per
  type-level one (`genlArg`, `argAndRestGenl`, `argsGenl`: subtype) the argnum chokepoint
  answers for slot `n` (`res/arg-constraints-at`), over `pred` and every super-predicate
  whose declarations bind its tuples, the union the assert-time checker reads; plus one
  `:type-position` entry when `pred` is a believed `type_relation_predicate` — core.txt's
  note beside `genl`: \"the position is not thereby unconstrained: genl is a
  type_relation_predicate, which says of every one of its positions what genlArg says
  of one.\"  A `quotedArg` constrains the filler as written, not what it denotes, and
  is not read here.

  A set, because the constraints compose as an unordered conjunction and the same
  constraint reached through two ancestors is one question."
  [kb pred n ctx]
  (into #{}
        cat
        [(for [{:keys [type kind]} (res/arg-constraints-at kb pred ctx n)
               :let [check (case kind :instance :membership :type :subtype nil)]
               :when check]
           {:check check :type type})
         (when (ask? kb (list 'type_relation_predicate pred) ctx)
           [{:check :type-position :type 'thing}])]))

(defn- satisfies-typing?
  "Does filler `y` satisfy one derived slot constraint in `ctx`?

  A `:membership` constraint asks `(t y)`; a `:subtype` constraint asks `(genl y t)`
  — the closure `ask` answers is reflexive-transitive, so the constraint type itself
  passes with no floor of the audit's own.  A `:type-position` constraint (derived
  from a `type_relation_predicate` membership) accepts `y` on **either** type reading
  — `(genl y thing)` or `(unary_predicate y)` — because the assert-time checker
  carries no ground-fact arm for a type-level position at all (its
  `type_relation_predicate` handling types rule variables only), so the audit's arm
  is deliberately the union: anything visibly a type passes, and only a filler with
  no type evidence of any kind violates.  Neither the root (`thing`, whose typehood
  is its reflexive `genl`) nor a declared-but-unplaced `unary_predicate` is convicted.

  Every question is answered from the KB's own reading, and no separate audit
  semantics is introduced.  For an `arg`-typed slot
  that means argument-type inference usually answers the membership off the very
  declaration the constraint was derived from, so a stored filler passes unless its
  membership is actively refuted — the conformance bite for instance-positions lives
  at the assert-time checker, which refuses a filler it can convict, and an audit
  stricter than the contract it derives from would be the second type system the
  binary form removes.  The subtype arm still convicts on its own: nothing derives a
  `genl` edge for a filler, so a kind with no visible path to the constraint type
  violates even though the open-world checker excused it."
  [kb y {:keys [check type]} ctx]
  (case check
    :membership    (ask? kb (list type y) ctx)
    :subtype       (ask? kb (list 'genl y type) ctx)
    :type-position (or (ask? kb (list 'genl y type) ctx)
                       (ask? kb (list 'unary_predicate y) ctx))))

(defn- admissible-filler?
  "Does at least one **determinate** filler `y`, believed at slot `n` of `pred`'s
  tuples about `x` in `ctx`, satisfy every derived slot constraint in `typings`?
  Named for both bites: a violation means no filler was determinate *and*
  contract-satisfying — absence, a skolem, and a constraint-failing filler all read
  the same from the caller's side.

  `n` is the audited slot — 2 audits `(pred x ?y)`, 1 audits `(pred ?y x)` — the one
  place the position is turned into a goal shape, fed by the same `n`
  `specified-violations` derived the typings with.

  A binding that carries no `?y` is not a filler: the registry answers a goal with
  `[{}]` where a prover proves it without binding anything, and a typing question
  about nil is not a membership question."
  [kb pred x typings n ctx]
  (let [goal    (if (= n 2) (list pred x '?y) (list pred '?y x))
        answers (quasiquote/ask-prepared kb goal ctx)]
    (boolean
     (some (fn [b]
             (let [y (get b '?y)]
               (and (some? y)
                    (not (indeterminate-term? kb y ctx))
                    (every? #(satisfies-typing? kb y % ctx) typings))))
           answers))))

(defn- member-selector
  [kb]
  (let [tax (reasoning/taxonomy kb)
        evidence (memoize #(budget/checked-call (fn [] (defining/definition-evidence kb %))))
        eligible (memoize
                  (fn [source subject]
                    (let [{:keys [contexts skeletal-only?]} (evidence subject)]
                      (cond
                        skeletal-only? #{}
                        (or (empty? contexts) (sx/variable? source)) ::actual-reader
                        :else (into #{}
                                    (mapcat (fn [home]
                                              (budget/checked-seq
                                               (budget/checked-call
                                                #(tax/common-descendants tax [source home])))))
                                    (budget/checked-seq contexts))))))]
    (fn [source reader subject]
      (budget/spend!)
      (let [readers (eligible source subject)]
        (or (= ::actual-reader readers) (contains? readers reader))))))

(defn specified-violations
  "Audit one binary `(predAllSpecified pred indep)` declaration in `ctx` and return a
  result map that always carries a `:status` — `{:status :audited :violations #{x …}}`
  where the audit ran (empty set = the requirement holds), or
  `{:status :gap :gap :missing-slot-typing :pred pred :position n}` where `pred`
  carries no visible denotation-typing at the audited position, a declaration-contract
  gap reported explicitly rather than silently audited unconstrained.  Discriminate on
  `:status`: a gap result carries no `:violations` key on purpose (no violation set
  pretends the audit ran), so a bare `(:violations r)` read nil-puns a gap into a
  clean pass.

  The required filler type is **derived from `pred`'s own argument contract**, never
  restated in the declaration: every visible `(arg pred n t)` requires the filler to be
  a member of `t`, every visible `(genlArg pred n t)` requires it to be a subtype of
  `t`, and multiple constraints compose conjunctively, as the assert-time checker
  composes them.

  `arg-pos` selects the twin: `:second` for `predAllSpecified` (the audited filler sits
  at `pred`'s second position), `:first` for `predSpecifiedAll` (the filler sits first
  and the quantified instance second).  Defaults to `:second`.

  A filler is indeterminate exactly when it is an `indeterminate_term` — a skolem (the
  built-in first member) or an extension declared with `(genl NewKind indeterminate_term)`
  — so an *Exists* placeholder passes and a skolemised witness does not, which is what
  makes this the antagonist of the *Exists* class."
  ([kb pred indep ctx] (specified-violations kb pred indep ctx :second))
  ([kb pred indep ctx arg-pos]
   (let [eligible? (member-selector kb)]
     (specified-violations kb pred indep ctx arg-pos #(eligible? ctx ctx %))))
  ([kb pred indep ctx arg-pos eligible?]
   (let [n       (case arg-pos
                   :second 2
                   :first  1
                   (throw (ex-info (str "arg-pos must be :second or :first, got "
                                        (pr-str arg-pos) " — (predAllSpecified pred indep)"
                                        " is binary; a context symbol arriving here usually"
                                        " means the caller still passes the removed dep"
                                        " parameter (see the CHANGELOG migration note)")
                                   {:type :bad-args :op 'specified-violations
                                    :arg-pos arg-pos})))
         typings (slot-typings kb pred n ctx)]
     (if (empty? typings)
       {:status :gap :gap :missing-slot-typing :pred pred :position n}
       (try
         {:status :audited
          :violations
          (into #{}
                (comp (map #(get % '?x))
                      (remove #(admissible-filler? kb pred % typings n ctx))
                      (filter eligible?))
                (quasiquote/ask-prepared kb (list indep '?x) ctx))}
         (catch clojure.lang.ExceptionInfo e
           (if (= :incomplete-defining-contexts (:type (ex-data e)))
             (merge {:status :gap :gap :incomplete-defining-contexts :pred pred}
                    (select-keys (ex-data e) [:term :handles]))
             (throw e))))))))

(defn- exists-reading
  "`[subjects goal filler-type placeholder]` for the *Exists* declaration `(functor pred a
  b)`: the terms the audit asks of (the members of the universal collection, or the fixed
  term), a fn from a subject to the goal whose `?y` is the filler, the collection the
  filler is a member of, and a fn from a subject to the cell's placeholder application.
  Nil for any other functor."
  [kb [functor pred a b] ctx]
  (let [members #(keep (fn [m] (get m '?x)) (quasiquote/ask-prepared kb (list % '?x) ctx))]
    (case functor
      predAllExists      [(members a) #(list pred % '?y) b #(list 'PredAllExistsFn pred a b %)]
      predExistsAll      [(members b) #(list pred '?y %) a #(list 'PredExistsAllFn pred a b %)]
      predExistsInstance [[b]         #(list pred '?y %) a (constantly (list 'PredExistsInstanceFn pred a b))]
      predInstanceExists [[a]         #(list pred % '?y) b (constantly (list 'PredInstanceExistsFn pred a b))]
      nil)))

(defn exists-violations
  "Audit one *Exists* declaration `(functor pred a b)` in `ctx`, `functor` one of
  `predAllExists`, `predExistsAll`, `predExistsInstance` and `predInstanceExists`, and
  return `{:status :audited :violations #{x …}}`: each member of the universal collection,
  or the fixed term of a pure existential, with no believed tuple of `pred` relating it to
  a member of the filler collection or to the cell's placeholder for it.  Any member
  counts, an indeterminate one (a skolem) included, since the declaration asks for
  existence only.  Throws `:bad-args` for any other functor."
  [kb declaration ctx]
  (if-let [[subjects goal filler-type placeholder]
           (and (sequential? declaration) (= 4 (count declaration))
                (exists-reading kb declaration ctx))]
    {:status :audited
     :violations
     (into #{}
           (remove (fn [x]
                     (some #(let [y (get % '?y)]
                              (and (some? y)
                                   (or (= y (placeholder x)) (ask? kb (list filler-type y) ctx))))
                           (quasiquote/ask-prepared kb (goal x) ctx))))
           subjects)}
    (throw (ex-info (str "not an Exists declaration: " (pr-str declaration))
                    {:type :bad-args :op 'exists-violations}))))

(defn- content-ordered
  "The distinct tuples `xs` in content order, so a sweep cut short keeps the same prefix
  in every arrival order."
  [xs]
  (sort-by #(apply list %) nm/compare-form (distinct xs)))

(defn- declaration-contexts
  "Select declaration tuples through the registry, retaining their stored defining
  contexts. A native-only answer has no source record and retains the supplied `ctx`."
  [kb functor ctx]
  (map (fn [[pred indep]]
         (let [stored (content-ordered
                       (for [[_ _ record] (budget/checked-seq
                                           (res/matches-visible kb (list functor pred indep) ctx))]
                         [pred indep (:context record) (:id record)]))]
           (if (seq stored) stored [[pred indep ctx nil]])))
       (content-ordered
        (for [b (quasiquote/ask-prepared kb (list functor '?pred '?indep) ctx)]
          [(get b '?pred) (get b '?indep)]))))

(defn- merge-specified-results
  "Combine source-context results without changing the public result shape. A missing
  slot contract remains an explicit gap; audited violation sets combine by union."
  [previous result]
  (cond
    (= :gap (:status previous)) previous
    (= :gap (:status result)) result
    :else (update previous :violations into (:violations result))))

(defn- specified-context-audits
  "Emit cumulative results after each eligible reader, retaining completed findings."
  [kb functor arg-pos declarations]
  (let [declarations (budget/checked-seq declarations)
        [pred indep] (first declarations)
        declaration [functor pred indep]
        eligible? (member-selector kb)
        readers (for [[_ _ source handle] declarations
                      reader (budget/checked-seq
                              (if handle
                                (let [descendants
                                      (budget/checked-call
                                       #(tax/common-descendants (reasoning/taxonomy kb) [source]))]
                                  (budget/checked-call
                                   #(sort-by nm/name-key (budget/checked-seq descendants))))
                                [source]))
                      :when (or (nil? handle)
                                (some #(= handle (:id (nth % 2)))
                                      (budget/checked-seq
                                       (budget/checked-call
                                        #(res/matches-visible kb (list functor pred indep) reader)))))]
                  [source reader])]
    (map (fn [result] [declaration result])
         (rest (reductions
                (fn [previous [source reader]]
                  (merge-specified-results
                   previous (specified-violations kb pred indep reader arg-pos
                                                  #(eligible? source reader %))))
                {:status :audited :violations #{}}
                readers)))))

(defn- exists-declarations
  "Read the stored *Exists* declarations `(functor pred a b)` in `ctx` as `[functor pred a
  b]` tuples, in content order."
  [kb functor ctx]
  (content-ordered
   (for [b (quasiquote/ask-prepared kb (list functor '?pred '?a '?b) ctx)]
     [functor (get b '?pred) (get b '?a) (get b '?b)])))

(defn- legacy-ternary-declarations
  "The retired ternary `(functor pred a b)` sentexes stored in a context `ctx` sees, as
  `[pred a b]` tuples in content order, belief unread: each breaks the functor's binary
  shape, so it is inert and no ask answers it.  The bulk import path builds records
  without the assert-time checks, so a pre-migration dump's ternary declarations load
  intact, and an unread one would turn an unmigrated KB into a fake clean sweep."
  [kb functor ctx]
  (let [up   (tax/context-up (reasoning/taxonomy kb) ctx)
        recs (:records kb)]
    (content-ordered
     (for [h  (reads/as-stored-with-functor-in (:index kb) functor up)
           :let [s (:sentence (p/get-sentex recs h))]
           :when (and (seq? s) (= 4 (count s)))]
       (vec (rest s))))))

(defn specified-declaration-audits
  "Every declaration audit as a lazy stream of `[declaration result]` entries.

  A stored Specified declaration audits every known reader seeing that requirement and
  an ordinary defining home of an instance. Each reader uses its own population,
  contracts and fillers. Reader results combine under one canonical key. Native-only registry answers
  retain the supplied context, since their binding maps carry no defining context.

  The open reads are only the unavoidable declaration censuses. Each expensive audit
  after that is focused on one declared predicate and independent collection. Keeping
  the units lazy lets the integrity sweep checkpoint and retain progress between them."
  [kb ctx]
  (concat
   (res/lazy-mapcat
    (fn [[functor arg-pos]]
      (res/lazy-mapcat
       #(specified-context-audits kb functor arg-pos %)
       (declaration-contexts kb functor ctx)))
    [['predAllSpecified :second] ['predSpecifiedAll :first]])
   (res/lazy-mapcat
    (fn [functor]
      (res/lazy-mapcat
       (fn [[pred a b]]
         (list [[functor pred a b]
                {:status :gap :gap :legacy-ternary-declaration
                 :pred pred :sentence (list functor pred a b)}]))
       (legacy-ternary-declarations kb functor ctx)))
    '[predAllSpecified predSpecifiedAll])
   (res/lazy-mapcat
    (fn [functor]
      (res/lazy-mapcat
       (fn [declaration]
         (list [declaration (exists-violations kb (apply list declaration) ctx)]))
       (exists-declarations kb functor ctx)))
    '[predAllExists predExistsAll predExistsInstance predInstanceExists])))

(defn all-specified-violations
  "Audit every `predAllSpecified` and `predSpecifiedAll` declaration visible in `ctx`,
  and every *Exists* declaration (`exists-violations`, keyed `[functor pred a b]`),
  and return `{[functor pred indep] result …}` — each result carrying a `:status`:
  `{:status :audited :violations #{…}}` where the audit ran, or `{:status :gap …}`
  for a diagnostic. Gap kinds include `:missing-slot-typing`
  (the predicate carries no visible slot typing at the audited position) and
  `:legacy-ternary-declaration` (a stored pre-migration ternary sentex, reachable
  through the bulk import path, which the binary audit cannot read).  A legacy gap
  is keyed by its whole stale argument tuple, `[functor pred a b]`, so it collides
  with neither a three-element binary key nor another stale sentex over the same
  predicate: an unmigrated KB carries both spellings at once, and a key off the
  first two arguments alone let the stale one replace the migrated declaration's
  violation set.  Declarations that hold are omitted; a gap never is, so a clean
  sweep is an empty map and a gap cannot pass as one.  This public aggregate and
  `kb-integrity` both fold the same focused per-declaration audit stream; only this
  function returns its complete aggregate map.

  Each stored Specified declaration is checked in every known eligible reader, not only
  maximal readers. A proved skeletal-only instance is exempt; an empty evidence set is
  audited in the actual reader. Unclassified support is :incomplete-defining-contexts.
  Visible definitions with one canonical key combine their violation sets. Native-only registry
  answers without a stored definition retain `ctx`, as do Exists audits."
  [kb ctx]
  (into {}
        (filter (fn [[_ r]] (or (= :gap (:status r)) (seq (:violations r)))))
        (specified-declaration-audits kb ctx)))
