;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.predall
  "The *Specified* half of the predAll / predExists / predInstance / predSpecified matrix
  (docs/predall.md, resources/kb/CxCore.txt).

  Reached from outside through `vaelii.core/specified-violations` and
  `vaelii.core/all-specified-violations`.  This namespace sits **above** `vaelii.core`,
  because auditing is asking and the audit asks through the public read path, so the
  delegation runs back down through `vaelii.impl.wiring`.

  Where the *Instance* relations stamp real inference and the *Exists* relations are
  inert records beside a sanctioned placeholder functor, `predAllSpecified` / `predSpecifiedAll` are an **integrity
  audit**: given a declaration that every instance of a collection ought to have a
  *determinate*, contract-satisfying filler, the reader here reports the instances
  with no admissible one — `{:status :audited :violations #{…}}` — or an explicit
  `{:status :gap …}` declaration-contract diagnostic.  It is not a
  stored rule and concludes nothing — it reads the declaration and the beliefs and hands
  back the violations, the way a solve-time report does.

  **Indeterminate = the `indeterminate_term` category.**  A filler counts as determinate
  unless it is a member of the extensible `indeterminate_term` collection (CxCore.txt).
  Skolem constants are its built-in first member — a reified NAT whose expression is a
  `SkolemFn` application (docs/skolem.md), detected structurally because a skolem's
  membership is never a stored fact — and a further kind is added with
  `(genl NewKind indeterminate_term)`.  Whether a non-skolem NAT is determinate by default
  is punted (Pace): a plain individual, a literal and an *Exists* placeholder alike are
  all treated as determinate here, which is what makes `predAllSpecified` the exact
  antagonist of `predAllExists`."
  (:require [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]))

(defn indeterminate-term?
  "Is `term` an **indeterminate** filler in `ctx` — a member of the extensible
  `indeterminate_term` category (CxCore.txt)?  A skolem constant is the built-in first
  member, read off its `SkolemFn` minting expression because a skolem's membership is
  never a stored fact; a further kind added with `(genl NewKind indeterminate_term)` is
  picked up through ordinary collection membership.

  `vaelii.impl.provers/indeterminate-term?` **is** the implementation, so the audit and
  the `different` prover's UNA identity exemption cannot disagree about a term.  This
  namespace sits above the prover registry, which is what makes the call possible; two
  copies agreeing by inspection did diverge, on a membership one reader derived and the
  other read as stored.

  A non-skolem NAT that is not declared an `indeterminate_term`, a bare individual and a
  literal are all determinate; the blanket non-skolem-NAT determinacy question is punted
  (Pace)."
  [kb term ctx]
  (provers/indeterminate-term? kb term ctx))

(defn- slot-typings
  "The visible slot-`n` typing constraints binding `pred`'s tuples in `ctx`, as a set
  of `{:check :membership|:subtype|:type-position :type t}` entries — one per believed
  `(arg cp n t)` (membership) and `(genlArg cp n t)` (subtype) over **every predicate
  `cp` whose declarations bind a `pred` tuple** (`res/constraining-predicates`: `pred`
  itself plus the super-predicates its `genl` closure reaches, the same union
  `checks/declaration-reader` realizes for the assert-time checker), plus one
  `:type-position` entry when `pred` is a believed `type_relation_predicate` — CxCore's
  note beside `genl`: \"the position is not thereby unconstrained: genl is a
  type_relation_predicate, which says of every one of its positions what genlArg says
  of one.\"

  The per-ancestor reads keep the variable ground where it matters: an open
  `(arg pred n ?t)` is answered by `FactProver` alone (`MetaConstraintProver` is
  ground-goal-only), so a single free-variable ask on the bare predicate would miss
  every inherited declaration — the audit walks the closure itself and asks each
  constraining predicate for its stored declarations, which is how it reads the same
  union the checker reads.

  A set, because the constraints compose as an unordered conjunction and the same
  constraint reached through two ancestors is one question."
  [kb pred n ctx]
  (into #{}
        cat
        [(for [cp (res/constraining-predicates kb 'arg pred ctx)
               b  (v/ask kb (list 'arg cp n '?t) ctx)
               :let [t (get b '?t)]
               :when (some? t)]
           {:check :membership :type t})
         (for [cp (res/constraining-predicates kb 'genlArg pred ctx)
               b  (v/ask kb (list 'genlArg cp n '?t) ctx)
               :let [t (get b '?t)]
               :when (some? t)]
           {:check :subtype :type t})
         (when (v/ask? kb (list 'type_relation_predicate pred) ctx)
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
    :membership    (v/ask? kb (list type y) ctx)
    :subtype       (v/ask? kb (list 'genl y type) ctx)
    :type-position (or (v/ask? kb (list 'genl y type) ctx)
                       (v/ask? kb (list 'unary_predicate y) ctx))))

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
        answers (v/ask kb goal ctx)]
    (boolean
     (some (fn [b]
             (let [y (get b '?y)]
               (and (some? y)
                    (not (indeterminate-term? kb y ctx))
                    (every? #(satisfies-typing? kb y % ctx) typings))))
           answers))))

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
       {:status :audited
        :violations
        (into #{}
              (comp (map #(get % '?x))
                    (remove #(admissible-filler? kb pred % typings n ctx)))
              (v/ask kb (list indep '?x) ctx))}))))

(defn- declaration-args
  "Read the stored binary `(functor pred indep)` declarations in `ctx` as
  `[pred indep]` tuples."
  [kb functor ctx]
  (for [b (v/ask kb (list functor '?pred '?indep) ctx)]
    [(get b '?pred) (get b '?indep)]))

(defn- legacy-ternary-declarations
  "The retired ternary `(functor pred a b)` sentexes still believed in `ctx`, as
  `[pred a b]` tuples.  A fresh assert of the shape is refused (the functors are
  `binary_predicate`s and the arity classes are disjoint), but the bulk import path
  builds records without the assert-time checks, so a pre-migration dump's ternary
  declarations load intact — and, matching neither the binary ask pattern nor any
  audit, would otherwise vanish from the sweep entirely, turning an unmigrated KB
  into a fake clean sweep."
  [kb functor ctx]
  (for [b (v/ask kb (list functor '?pred '?a '?b) ctx)]
    [(get b '?pred) (get b '?a) (get b '?b)]))

(defn all-specified-violations
  "Audit every `predAllSpecified` and `predSpecifiedAll` declaration visible in `ctx`
  and return `{[functor pred indep] result …}` — each result carrying a `:status`:
  `{:status :audited :violations #{…}}` where the audit ran, or `{:status :gap …}`
  for a declaration-contract diagnostic.  Two gap kinds ship: `:missing-slot-typing`
  (the predicate carries no visible slot typing at the audited position) and
  `:legacy-ternary-declaration` (a stored pre-migration ternary sentex, reachable
  through the bulk import path, which the binary audit cannot read — reported per
  stale sentex, keyed `[functor pred indep]` off its first two arguments).
  Declarations that hold are omitted; a gap never is, so a clean sweep is an empty
  map and a gap cannot pass as one.  The one call an integrity sweep makes;
  `specified-violations` is the per-declaration reader it is built from."
  [kb ctx]
  (into {}
        cat
        [(for [[functor arg-pos] [['predAllSpecified :second]
                                  ['predSpecifiedAll :first]]
               [pred indep] (declaration-args kb functor ctx)
               :let [r (specified-violations kb pred indep ctx arg-pos)]
               :when (or (= :gap (:status r)) (seq (:violations r)))]
           [[functor pred indep] r])
         (for [functor '[predAllSpecified predSpecifiedAll]
               [pred a b] (legacy-ternary-declarations kb functor ctx)]
           [[functor pred a]
            {:status :gap :gap :legacy-ternary-declaration
             :pred pred :sentence (list functor pred a b)}])]))
