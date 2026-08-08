;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.checks
  "The definitional checks — argIsa argument types, disjointness, functionality —
  plus ground-ness and the stratification glue over the rule index.

  Second layer of the engine stack (kb <- checks <- special <- integrate <- chain
  <- settle):
  every check reads the KB (taxonomy, index, believed matches) and returns a value
  or throws — nothing here writes.  Both mutation paths consume these: `assert`
  (vaelii.core) throws the value, the derivation path (vaelii.impl.chain) records
  it in the violations ledger."
  (:require [vaelii.impl.config :as config]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.wff :as wff]))

;; ---- invariants: naming + argument type constraints ---------------------

;; The definitional checks below are **value-first**: each returns the first
;; violation as a map `{:type ... :message ...}` (or nil), like the wff arms and
;; `rules/range-problems`.  `constraint-checks` throws by wrapping the value on the
;; assert path; `constraint-violation` records it on the derivation path.  The old
;; shape — throw, then catch-your-own-throw against a whitelist of `:type`s — meant
;; a fourth check added without updating the whitelist would rethrow from inside
;; the chaining fixpoint, the exact abort `violations` exists to forbid.

(defn- checkable-term?
  "Is `x` a term the definitional checks can say anything about — any name the KB
  can hold a type membership for?

  Every non-variable symbol qualifies, whatever role its spelling reads as.  A
  predicate is as much a thing as `Muffet` is: the meta-ontology types predicates
  (`unaryPredicate`, `instanceRelationPredicate`, …), separates those types with
  `disjointMetatype`, and constrains predicate-valued argument positions with
  `argIsa` — so restricting the checks to CapitalCamelCase individuals would leave
  the whole meta-level declared and unenforced.  Numbers, strings and compounds are
  excluded because a type membership cannot be asserted of one (a NAT reifies to its
  constant first, so a reified term is checked under that constant)."
  [x]
  (and (symbol? x) (not (sx/variable? x))))

(def ^:private declaration-queries
  "Per declaration kind, the sentence `declaration-reader` queries: the functor, then the
  argument tail that follows the predicate being asked about.  A table rather than a cond
  chain, because the kinds differ in *arity* as well as in functor — `interArgIsa` names
  two positions and two types — and a chain would put that difference in the caller."
  '{:arity      (arity ?n)
    argIsa      (argIsa ?n ?type)
    argGenl     (argGenl ?n ?type)
    interArgIsa (interArgIsa ?n ?type ?m ?utype)})

(defn- declaration-reader
  "A `kind -> [[handle bindings] …]` reader for one predicate's argument constraints,
  memoized for the life of one caller.

  `args-problem`, `genls-problem` and the entailments all ask the same two questions —
  what does `argIsa` say about this predicate's positions, and what does `argGenl` —
  and `assert` names that read the dominant per-fact cost of a store.  Asking it once
  is what lets the entailment ride along on a walk the check was making anyway instead
  of doubling it.  Realized rather than lazy: a predicate carries a handful of
  declarations, and every caller but the first-violation `for` wants all of them."
  [kb pred context]
  (let [cache (volatile! {})]
    (fn [kind]
      (if-some [ds (get @cache kind)]
        ds
        (let [[f & tail] (declaration-queries kind)
              ds         (when (symbol? pred)
                           (vec (res/matches-visible kb (list* f pred tail) context)))]
          (vswap! cache assoc kind ds)
          ds)))))

(defn- arg-at
  "The argument sitting at one-based `position` of the argument vector `as`, or nil when
  the position is not one the sentence has.  The bounds test the argument constraints all
  need before they can say anything about a position a declaration names."
  [as position]
  (when (and (integer? position) (<= 1 position (count as)))
    (nth as (dec position))))

(defn- in-content-order
  "Declaration matches sorted by the stored declaration's own sentence — the order
  every first-violation walk reads them in.

  `res/matches-visible` promises the answer *set*: `res/*hierarchical-retrieval*` says
  nothing about order, so a `(first (for …))` over the raw matches would let the
  retrieval strategy pick *which* declaration a refusal names when several convict.
  Sorting on content keys the choice on what the KB says rather than on enumeration —
  the rule `handle-naming` states for the handle a clash is reported as.  Existence is
  untouched: every declaration is still read, and a sentence no declaration convicts
  still has no violation."
  [ds]
  (sort-by #(pr-str (:sentence (nth % 2))) ds))

(defn- args-problem
  "First (argIsa pred n type) violation for a sentence, or nil.  Uses genl
  transitivity; only constraints and type memberships visible from `context`
  count.  Open-world: an untyped term can't violate anything.

  `types` is the shared per-assert membership reader (`kb/membership-reader`), `decls`
  the shared declaration reader.  The two questions asked of each constrained
  argument — is it in the hierarchy at all, and does it reach the constraint type —
  are one retrieval and two set lookups, and a second constraint on the same position
  adds no retrieval at all."
  [_kb sentence _context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (symbol? pred)
      (first
       (for [[_ b] (in-content-order (decls 'argIsa))
             :let  [n   (get b '?n)
                    t   (get b '?type)
                    arg (arg-at as n)]
             :when (and arg (checkable-term? arg)
                        (let [m (types arg)]
                          (and (kb/isa-among? (:closures m) 'thing)
                               (not (kb/isa-among? (:closures m) t)))))]
         {:type :arg-type :sentence sentence :arg arg :expected t :position n
          :message (str "arg constraint: " arg " must be a " t
                        " (arg " n " of " pred ")")})))))

(defn- inter-args-problem
  "First `(interArgIsa pred n T m U)` violation for a sentence, or nil.

  The **conditional** argument constraint: if argument `n` is a `T`, argument `m` must be
  a `U`.  `(interArgIsa eats 1 carnivore 2 meat)` says a carnivore eats meat — a claim
  `argIsa` cannot make, since `(argIsa eats 2 meat)` would demand it of every eater.

  Open-world **twice, in opposite directions**, and that is the whole of the reading:

  * The trigger side must be *positively established*.  Silence about argument `n`'s type
    is not evidence that it is a `T`, so an unknown trigger leaves the constraint dormant
    rather than firing it — this is the antecedent of a conditional, and NAF there is a
    reason not to convict.
  * The target side is convicted by *absence*, exactly as `args-problem` is: argument `m`
    must be in the hierarchy at all (or the edges placing it may simply not have arrived)
    and must not reach `U`.  NAF here is a reason to convict.

  One declaration, two readings of the same silence, and getting either backwards inverts
  the constraint: demand the trigger's absence and every untyped argument fires it; excuse
  the target's absence and it never convicts anybody.

  Both sides are context-scoped by construction — `decls` reads only the declarations
  visible from `context` and `types` only the memberships — so a context is convicted
  on evidence it can see, which is the judgement `genls-problem` spells out at length.

  **Behind an O(1) gate, unlike its two unconditional neighbours.**  `args-problem` and
  `genls-problem` run their declaration read unconditionally because `argIsa` is what a
  typed ontology is mostly made of, so the read pays for itself.  Nothing declares
  `interArgIsa` yet, and this check runs on *every* assert — the read `assert` names its
  dominant per-fact cost — so a third retrieval that finds nothing is a tax on every write
  in every KB.  One `count-with-functor` says whether any such declaration is stored at
  all; zero means no scoped read can find one, so there is nothing to look for."
  [kb sentence _context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (and (symbol? pred)
               (pos? (p/count-with-functor (:index kb) 'interArgIsa)))
      (first
       (for [[_ b] (in-content-order (decls 'interArgIsa))
             :let  [n       (get b '?n)
                    t       (get b '?type)
                    m       (get b '?m)
                    u       (get b '?utype)
                    trigger (arg-at as n)
                    target  (arg-at as m)]
             :when (and trigger target
                        (checkable-term? trigger) (checkable-term? target)
                        (symbol? t) (symbol? u)
                        ;; the antecedent, established rather than merely unrefuted
                        (kb/isa-among? (:closures (types trigger)) t)
                        (let [tm (types target)]
                          (and (kb/isa-among? (:closures tm) 'thing)
                               (not (kb/isa-among? (:closures tm) u)))))]
         {:type :inter-arg-type :sentence sentence :arg target :expected u :position m
          :trigger trigger :trigger-type t :trigger-position n
          :message (str "arg constraint: " target " must be a " u " (arg " m " of " pred
                        ", because arg " n " is a " t ")")})))))

(defn- genls-problem
  "First `(argGenl pred n type)` violation for a sentence, or nil.

  `argGenl` is `argIsa` one level up: it constrains the argument to be a **subtype**
  of the named type rather than an instance of it, which is what a type-level relation
  wants — `(argGenl partType 1 physical_object)` says the first argument names a kind
  of physical object, where `(argIsa partOf 1 physical_object)` says it names one.

  Which constraints apply is context-scoped exactly as `argIsa` is, and so is the
  subtype test itself: absence of a *visible* path to the constraint type is what
  convicts, the NAF reading judged from the writer's own vantage.

  Open-world has a floor here that `argIsa` does not have.  An argument outside the
  hierarchy is normally exempt, since the edges placing it may not have arrived yet —
  but an **individual** can never acquire them (`wff/genl-problems` refuses `genl` of
  one), so a type-level position holding one is convicted rather than excused.  The
  test is \"outside the hierarchy *and* individual\", not \"individual\", because a
  reified NAT reads as an individual by spelling and is minted with real `genl` edges from
  its `resultGenl` declarations — one that reaches `thing` is judged like any type.

  **A deliberate global/scoped split inside one `cond`.**  The first floor asks what
  the argument *is* (could it ever be a type?) and stays **global**: a reified NAT's
  minting edges land in `UniverseContext`, which the upper band sits above and
  cannot see, so a scoped floor would convict an imported reified NAT used from
  `MeasureContext` as \"an individual, so never a subtype\" — false.  The second
  floor is the **scoped** open-world excuse: an argument with no *visible* path
  into the hierarchy may simply have its edges out of sight, and a NAF check that
  convicted on invisible evidence would convict harder the less a context sees.
  Only an argument with visible evidence that reaches the wrong place is convicted."
  [kb sentence context decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (:taxonomy kb)]
    (when (symbol? pred)
      (first
       (for [[_ b] (in-content-order (decls 'argGenl))
             :let  [n   (get b '?n)
                    t   (get b '?type)
                    arg (arg-at as n)
                    why (when (and arg (checkable-term? arg) (symbol? t))
                          (cond
                            (not (tax/genl? tax arg 'thing))          ; global: the individual floor
                            (when (nm/individual? arg)
                              (str arg " is an individual, so it can never be a subtype of " t))

                            (not (tax/genl? tax arg 'thing context))  ; scoped: no visible evidence
                            nil                                       ; — open world excuses

                            (not (tax/genl? tax arg t context))       ; scoped: the writer's vantage
                            (str arg " must be a subtype of " t)))]
             :when why]
         {:type :arg-genl :sentence sentence :arg arg :expected t :position n
          :message (str "arg constraint: " why " (arg " n " of " pred ")")})))))

;; ---- the argument constraints, checked against each other ----------------

(def ^:private arg-constraint-kinds
  "The two **unconditional** argument constraints, each mapped to the other: the value is
  the counterpart a declaration is checked against, and membership is what
  `declaration-problem` reads to recognize one.

  `interArgIsa` is not here and has its own arm.  It is written at a different arity and
  names two positions, so it fits neither the pairing nor the `(= 3 (nm/arity …))` test —
  forcing it in would put that difference inside every reader of this map."
  '{argIsa argGenl, argGenl argIsa})

(def predicate-type-arities
  "What each predicate-type membership says the arity is.  The `arity` sentexes and
  these memberships derive each other through the CoreContext rules, so a declared
  predicate normally has both — but a `{:chain? false}` assert or a KB loaded without
  the rules has only what was written, so both spellings are read.

  Public because `settle`'s retroactive arity report triggers on an arriving *arity
  declaration*, and these memberships are the second way to write one — a roster read
  twice is a roster that drifts."
  '{unaryPredicate 1 binaryPredicate 2 ternaryPredicate 3})

(defn- declared-arity
  "The arity `pred` is declared with, visible from `context`, or nil when the KB has
  never said.

  Read from the **taxonomy cache** (`tax/declared-arity`), which `(arity P n)`
  maintains the way `(transitive P)` maintains its prop: this runs on every assertion,
  and answering it from the index meant a retrieval and a filtered walk of every sentex
  holding `pred` as its first argument — 16 candidates per assertion on an OpenCyc
  load, 13.3M over it, nearly all finding nothing.  A declaration is not something to
  re-derive per write.

  The membership spelling is read off the predicate's own types (`types`, the shared
  per-assert reader), so it costs the retrieval `argIsa` already needs for its
  arguments rather than one of its own."
  ([kb pred context types] (declared-arity kb pred context types nil))
  ([kb pred context types _decls]
   (or (let [n (tax/declared-arity (:taxonomy kb) pred context)]
         (when (and (integer? n) (pos? n)) n))
       (let [cs (:closures (types pred))]
         (first (for [[t n] predicate-type-arities
                      :when (kb/isa-among? cs t)]
                  n))))))

(defn- handle-namings
  "The handles of the matches that literally *say* `target`, in content order, else a
  content-ordered choice among the matches that merely entail it.

  `res/matches-visible` is **type-aware**, so a literal comes back alongside everything
  the taxonomy proves implies it: ask for `(animal CI2)` and you also get `(dog CI2)`
  where `dog` is under `animal`.  Every one of them is a true answer to *is this
  believed*, which is all an existence check wants — but a caller naming the handle is
  choosing the sentex a violation is **reported as**, and `ffirst` hands that choice to
  whatever order the retrieval strategy happened to produce.

  Order is not part of that contract, and should not be: `res/*hierarchical-retrieval*`
  promises the answer *set*, and a caller reading whole answers cannot observe more.
  Taking the first match would make it observable — a flag documented as a pure cost
  decision would decide which pair `contradictions` reports and, through arbitration,
  what the KB believes (`clash_oracle_test` under `VAELII_HIER=0`).

  So **both** arms are content-ordered, exact matches first because the direct statement
  is the one the caller asked about.  The order key is the sentence *and its context*:
  `res/matches-visible` fans over the whole `genlContext` cone, so one sentence stated in
  two visible contexts comes back as two exact matches, and a key on the sentence alone
  ties them — leaving the pick to enumeration order in precisely the arm that exists to
  take it away.  Never the handle, which is allocation order: two KBs given one op stream
  must name the same side.

  **Every exact match, not one**, because they are not one sentex.  A term stated to hold
  the same type in a general context and again in one that sees it is two stored
  claims of different provenance and possibly different strength, and each forms its own
  pair with whatever contradicts it — naming only the content-first of them leaves the
  other coexisting with content that denies it.  The entailing arm stays singular: those
  matches are *different* sentences reaching the target through the hierarchy, and each
  already convicts under the type it actually states."
  [matches target]
  (let [sen   (fn [m] (:sentence (nth m 2)))
        order (fn [m] (pr-str [(sen m) (:context (nth m 2))]))]
    (if-let [exact (seq (filter #(= target (sen %)) matches))]
      (map first (sort-by order exact))
      (take 1 (map first (sort-by order matches))))))

(defn- handle-naming
  "The one handle a *refusal* names — the first of `handle-namings`, which is the
  content-first exact match where one is stored.  A refusal needs one reason, and the
  arity arm convicts against a declaration rather than against a pair, so there is
  nothing plural for it to say."
  [matches target]
  (first (handle-namings matches target)))

(defn- arity-declaration-handle
  "The handle of the believed declaration saying `pred` has arity `declared`, visible
  from `context` — the sentex a wrong-arity sentence convicts *against*.

  Two spellings declare it and `declared-arity` reads both, so both are looked for: the
  `(arity P n)` sentex, and failing that the predicate-type membership `(binaryPredicate
  P)` that says the same thing.  Asked only once a clash has been found, so an
  admissible assert never pays for the retrieval."
  [kb pred declared context]
  ;; `handle-naming` for the same reason it exists: both reads are type-aware, so a
  ;; subtype of the declaration's own predicate comes back beside it.  The preference
  ;; between the two *spellings* is this `or`, and stays content-ordered by construction.
  (or (let [target (list 'arity pred declared)]
        (handle-naming (res/matches-visible kb target context) target))
      (first (for [[t n] predicate-type-arities
                   :when (= n declared)
                   :let  [target (list t pred)
                          h (handle-naming (res/matches-visible kb target context) target)]
                   :when h]
               h))))

(defn- arity-problem
  "A sentence used at an arity its predicate is not declared with, or nil.

  The **top literal only**, exactly like `args-problem`: a rule reaches here as its
  `implies` form, whose own arity is 2 and is checked as such, and its antecedents are
  not.  That is the existing line between what `assert` checks and what a rule is
  trusted to contain, and arity does not move it.

  Open-world in the same shape as `argIsa`: a predicate the KB has never declared can
  be used at any arity, since the declaration may simply not have arrived.  A
  `variableArity` predicate is exempt outright — `lessThan` is declared binary *and*
  reads a chain of any length, and the declaration is what says so.

  `:opposing-handle` names the declaration that convicted, so a refusal can say *which*
  one and the retroactive report can point at it.  It does **not** make this arbitrable
  — `arbitrable-kinds` is what decides that, and the comment above it says why arity is
  not on the list even though it names a second sentex."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)]
    (when (symbol? pred)
      ;; `decls` is the shared reader for *this sentence's* functor, so it answers the
      ;; arity question too — the same visibility-scoped retrieval, asked once for the
      ;; whole pass instead of once per check that wants it.
      (when-let [declared (declared-arity kb pred context types decls)]
        (let [actual (nm/arity sentence)]
          (when (and (not= actual declared)
                     (not (kb/isa-among? (:closures (types pred)) 'variableArity)))
            {:type :arity :sentence sentence :predicate pred
             :expected declared :actual actual
             :opposing-handle (arity-declaration-handle kb pred declared context)
             :message (str pred " is declared with " declared " argument"
                           (when (not= 1 declared) "s") " but has " actual)}))))))

(defn- arg-position-problem
  "A declaration constraining a position `pred` does not have — `(argIsa parentOf 5
  animal)` where `parentOf` is declared binary.  The constraint would never fire, so it
  reads as enforced while enforcing nothing.

  Shared by every declaration kind, because `interArgIsa` names **two** positions and both
  are the same mistake.  Open-world: a predicate whose arity the KB has never stated is
  unconstrained."
  [kb f pred n context types]
  (when (and (integer? n) (pos? n))
    (when-let [declared (declared-arity kb pred context types)]
      (when (> n declared)
        {:type :arg-position :predicate pred
         :position n :arity declared
         :message (str f " constrains argument " n " of " pred ", which is"
                       " declared with " declared " argument"
                       (when (not= 1 declared) "s"))}))))

(defn- declaration-problem
  "A problem with an `argIsa` / `argGenl` / `interArgIsa` **declaration** itself, rather
  than with a sentence it constrains — two ways one can contradict what the KB already
  says about the predicate it is about:

  * a position the predicate does not have (`arg-position-problem`).  `interArgIsa` names
    two, and each is checked.
  * a constraint disagreeing with the predicate's own `relationKind` — `argGenl` on
    an `instanceRelationPredicate`, or `argIsa` on a `typeRelationPredicate`.
    `interArgIsa` reads its types as memberships, so it takes `argIsa`'s side of that.

  **Both constraints on one position is not a problem**, and this is the case worth
  naming because the opposite reads plausible: one asks the argument to be an instance
  of a type, the other to be a subtype of a type, and a *type* is routinely both.
  `(argIsa P 2 collection)` with `(argGenl P 2 animal)` says the slot holds a kind of
  animal, and `dog` satisfies it — an instance of `collection`, a subtype of `animal`.
  The two checks are independent and each is open-world on its own, so declaring both
  narrows the slot rather than emptying it.

  Open-world throughout: each arm needs a declaration to contradict, so a predicate
  the KB has said nothing about is unconstrained."
  [kb sentence context types]
  (let [[f pred n _ m] sentence]
    (cond
      (and (= 'interArgIsa f) (= 5 (nm/arity sentence)) (symbol? pred))
      (some-> (or (arg-position-problem kb f pred n context types)
                  (arg-position-problem kb f pred m context types)
                  (when (seq (res/matches-visible kb (list 'typeRelationPredicate pred) context))
                    {:type :arg-constraint-kind :predicate pred
                     :message (str pred " is declared typeRelationPredicate, so its"
                                   " arguments are constrained with argGenl, not " f)}))
              (assoc :sentence sentence))

      (and (contains? arg-constraint-kinds f) (= 3 (nm/arity sentence))
           (symbol? pred) (integer? n) (pos? n))
      (let [other (arg-constraint-kinds f)]
        (or (some-> (arg-position-problem kb f pred n context types)
                    (assoc :sentence sentence))
            (let [clash (if (= f 'argIsa) 'typeRelationPredicate 'instanceRelationPredicate)]
              (when (seq (res/matches-visible kb (list clash pred) context))
                {:type :arg-constraint-kind :sentence sentence :predicate pred
                 :message (str pred " is declared " clash ", so its arguments are"
                               " constrained with " other ", not " f)})))))))

;; ---- the three violations that name an opposing sentex -------------------
;;
;; Disjointness, functionality and asymmetry are not like the argument constraints.
;; Each convicts by pointing at **another believed sentex** that the incoming one
;; cannot coexist with — a pair, which is exactly what a nogood is, and exactly what
;; `settle` already arbitrates for `S` against `(not S)`.  So each carries the
;; opposing handle and that handle's defeat class, and the layers above decide from
;; the class alone whether this is a *refusal* (contradicting the fixed background) or
;; a *nogood* (contradicting a defeasible claim).  See docs/nmtms.md.
;;
;; **Two families do not join them, for two different reasons.**
;;
;; The argument constraints cannot form a pair at all.  `(parentOf Fred Mary)` violating
;; `(argIsa parentOf 1 animal)` is convicted by the *absence* of a path from Fred's types
;; to `animal` — an open-world negation-as-failure judgement, not a stored sentex to weigh
;; against — so there is no second member to make a pair of, and nothing for a defeat
;; class to compare.  Those stay refusals.
;;
;; `arity` **does** name a second sentex — the `(arity P n)` declaration, or the
;; predicate-type membership saying the same thing — and is still not arbitrable, which is
;; the case worth naming because the pair looks so much like the three above it.  The
;; sentex it names is the *vocabulary entry the conviction is read through*: `declared-arity`
;; answers from the taxonomy's arity table, which follows belief, so a nogood that defeated
;; the declaration would destroy its own premise.  Measured, on `(pRelOf A B C)` known-true
;; against a `:default` `(arity pRelOf 2)`: the declaration is defeated in the settle that
;; admits the pair, revived by the next settle's `clear-defeats!` while the table it was
;; uninstalled from is still empty, and with the table empty the clash is not re-derived —
;; so it is never reported again, and while the declaration was out a *fourth*-arity fact
;; of the same predicate was admitted too.  One wrong fact would disable a declaration for
;; every other use of the predicate, and belief would depend on how many settles had run.
;;
;; The other two members of the family defeat a *fact* and leave the vocabulary standing,
;; which is why they are stable.  So arity keeps the door refusal, and the retroactive half
;; is a **report** (`settle/report-arity-reach!`) rather than a decision: it names the facts
;; a declaration arriving late convicts, and moves no belief.  Do not promote it to a
;; nogood without first making the vocabulary read independent of the belief the nogood
;; moves.

(def arbitrable-kinds
  "The definitional violations that name a pair of believed sentexes rather than a
  malformed sentence, so `settle` can arbitrate them like any other contradiction."
  #{:disjoint :functional :asymmetric})

(defn- opposing-class
  "The defeat class of the sentex a violation is *against*, or nil when it names
  none.  Read from the TMS rather than from the record's `:strength`, because a
  derived opposing claim is a premise of nothing and carries its class only on the
  node."
  [kb v]
  (when-let [h (:opposing-handle v)]
    (jtms/defeat-class (:tms kb) h)))

(defn- with-opposing-class
  "Stamp a violation with its opposing sentex's defeat class, so every consumer reads
  the same answer rather than each fetching it again."
  [kb v]
  (if (and v (:opposing-handle v)) (assoc v :opposing-class (opposing-class kb v)) v))

(defn arbitrable?
  "Can `settle` arbitrate this violation instead of the caller refusing it — does it
  name an opposing believed sentex to form a nogood with?"
  [v]
  (boolean (and v (contains? arbitrable-kinds (:type v))
                (integer? (:opposing-handle v)))))

(defn- against-known-true?
  "Is the opposing side known-true — the fixed background a solve reasons *from*?
  Then admitting the newcomer would store something the KB can never believe, and a
  refusal is the honest answer.  A violation naming no opposing sentex answers true:
  what cannot be arbitrated must be refused."
  [v]
  (or (not (arbitrable? v))
      (strength/known-true? (:opposing-class v))))

(def ^:dynamic *arbitrate-constraints?*
  "Does the **assert** path hand a disjointness or functionality clash to `settle` as
  a nogood instead of throwing?

  **Off by default**, which leaves `assert` refusing exactly what it refuses today: a
  disjoint or functional clash at any strength.  On, the three checks read one rule —
  refuse only against `:monotonic` content, arbitrate against a `:default` claim — and
  `(dog Rex)` beside `(cat Rex)` becomes a represented dilemma rather than a throw.

  The derivation path does not consult this and never did: a rule firing has no caller
  to refuse, so an arbitrable violation there is always placed and arbitrated (which is
  what gives the loser a `why-not`).  This var is only about whether a *writer* is told
  no, and that is a policy question rather than an engine one.

  `binding` it is the ordinary way in; `VAELII_ARBITRATE_CONSTRAINTS=1` sets the root
  value, which is what lets the whole suite be run under it.  A KB that names a
  `:constraints` policy of its own overrides both — `kb/constraint-policies` names them
  and `arbitrating?` is the one read of either."
  ;; A var root, so it is read at namespace load and refuses there — `config`'s own
  ;; docstring says why that is the right door for a `def` and the wrong one for a value
  ;; a worker reads.
  (config/arbitrate-constraints?))

(defn arbitrating?
  "Does `kb` arbitrate a definitional clash against defeasible content rather than
  refusing it at the door — and let a declaration reach back over stored content?

  The KB's own `:constraints` policy decides when it has one (`kb/constraint-policies`
  names them); a KB that named none reads the process default, so
  `VAELII_ARBITRATE_CONSTRAINTS=1` still moves a whole suite and a `binding` still moves
  one call."
  [kb]
  (case (:constraints kb)
    :arbitrate true
    :refuse    false
    *arbitrate-constraints?*))

(defn refuses-assert?
  "Does this violation refuse the sentence on the **assert** path?

  `:asymmetric` reads the class either way — that is the line it draws, and the one the
  other two are generalized to.  `:disjoint` and `:functional` refuse unconditionally
  until `kb`'s constraint policy (`arbitrating?`) opts into the same rule.  Everything
  else is a malformed sentence or an open-world judgement and refuses outright."
  [kb v]
  (when v
    (case (:type v)
      :asymmetric             (against-known-true? v)
      (:disjoint :functional) (or (not (arbitrating? kb)) (against-known-true? v))
      true)))

(defn- membership-handles
  "The handles of the believed `(t x)` sentexes visible from `context` — the sentexes a
  disjointness clash is *with*.  Asked only once a clash has been found, so an
  admissible assert never pays for it.

  **The sentex saying `(t x)`, not merely one that entails it.**  `matches-visible` is
  type-aware, so asking it for `(animal CI2)` returns the direct membership *and* every
  subtype membership that implies it — `(dog CI2)` where `dog` is under `animal`.  Both
  are true answers to \"is CI2 an animal\", and either would do if this were an
  existence check; but the handle picked becomes the side a clash is *reported as*, so
  taking `ffirst` let the report read `contradicts (dog CI2) (plant CI2)` or
  `contradicts (animal CI2) (plant CI2)` depending on which the retrieval strategy
  happened to enumerate first.  `res/*hierarchical-retrieval*` promises the answer set
  and says nothing about order — correctly, since order is not a thing a caller reading
  whole answers can observe — so that made a documented cost decision change what the
  KB reported, and through arbitration what it believed.  `clash_oracle_test` catches it
  under `VAELII_HIER=0`.

  So: every exact membership when one is stored, and a content-ordered choice among the
  entailing ones when none is — a purely inherited membership has no direct sentex to
  name.  `handle-namings` is that rule, and says the rest, including why the exact arm
  is plural: one sentence stated in two contexts a reader sees is two sentexes, and each
  forms its own pair."
  [kb t x context]
  (let [target (list t x)]
    (handle-namings (res/matches-visible kb target context) target)))

(defn- disjoint-problems
  "A type membership (T X) where X already holds a type the taxonomy proves
  disjoint from T, as a violation map, or nil.  **Fully scoped to the asserting
  context**: the memberships read, the disjoint declaration, and the genl edges
  the disjointness closes under must all be visible from `context` — a
  context is only ever refused on grounds it can see.

  X is any term, not only an individual, so a `disjointMetatype` over predicate
  types separates the predicates it is declared of — one predicate cannot be both
  an `instanceRelationPredicate` and a `typeRelationPredicate`.

  `:opposing-handle` is the conflicting membership's own handle: the clash is between
  two sentexes, and naming the second is what lets `settle` weigh them.

  **Every** clash, not the first — `disjoint-problem` takes the first for the refusal
  path, where one reason to refuse is as good as another.  A *pair* is not a reason
  though, it is a fact about two sentexes, and a term holding three mutually disjoint
  types forms three pairs.  Stopping at the first would make which of them `settle`
  reports depend on the order the argument root hands the memberships back, which is
  handle order, which is arrival order.

  A pair per opposing **sentex**, not per opposing type, for the same reason one level
  down: the same membership stated in a general context and in one that sees it is
  two claims, of possibly different strength, and a reader below both is contradicted by
  each.  `functional-problems` counts its clashes that way already."
  [kb sentence context types]
  (when (= 1 (nm/arity sentence))
    (let [t (nm/functor sentence)
          x (first (nm/args sentence))]
      (when (checkable-term? x)
        (let [ts (:types (types x))]
          (when (seq ts)
            ;; one question, asked of each type the term holds: `t` and the asserting
            ;; context are fixed across the loop, and they are what most of the answer
            ;; is a function of
            (let [disjoint? (tax/disjointness-test (:taxonomy kb) t context)]
              (for [t' ts
                    :when (disjoint? t')
                    h    (membership-handles kb t' x context)]
                {:type :disjoint :sentence sentence :types [t t']
                 :opposing-handle h
                 :message (str "disjointness violated: " x " cannot be both "
                               t " and " t')}))))))))

(defn- disjoint-problem
  "The first disjointness clash, for the refusal paths."
  [kb sentence context types]
  (first (disjoint-problems kb sentence context types)))

(defn mergeable-values?
  "Could a functional clash between `x` and `y` be *resolved* by concluding they name
  one thing?  Only when both are plain symbols: the equality closure is a partition
  over symbols (`wff` refuses a compound, and a number or a string is not even an
  indexable term), so `(equals 1980 1990)` is not a sentence the KB can hold.

  This is the line between a clash that is knowledge and a clash that is an error.
  Two spellings of a person may denote one woman; 1980 and 1990 are two numbers and
  no merge can make them one, so a numeric functional clash stays the hard rejection
  it has always been."
  [x y]
  (and (symbol? x) (symbol? y) (not (sx/variable? x)) (not (sx/variable? y))))

(defn functional-clashes
  "The believed `[handle value]` pairs that already fill `P`'s functional slot for the
  same first argument with something other than `b` — the clash a `(functional P)`
  declaration turns into either a rejection or an equality."
  [kb sentence context]
  (let [pred (nm/functor sentence)]
    (when (and (= 2 (nm/arity sentence))
               (tax/has-prop? (:taxonomy kb) :functional pred context))
      (let [[a b] (nm/args sentence)]
        (for [[h bnd] (res/matches-visible kb (list pred a '?fv) context)
              :let    [v (get bnd '?fv)]
              :when   (and v (not= v b))]
          [h v])))))

(defn- functional-problems
  "A (P a b) where P is functional and `a` already has a value for P that no
  equality could reconcile with `b` (visible from `context`), as a violation map,
  or nil.

  A clash between two **symbols** is not an error: `(functional motherOf)` plus
  two spellings of Tom's mother is exactly where co-reference shows up, and the KB
  *derives* `(equals V1 V2)` from it (see `special/derive-functional-equalities`)
  instead of refusing the second fact.  Everything else — two numbers, two strings, a
  compound — is still the hard contradiction it was, because no merge can make two
  numbers one thing.  See docs/equality.md.

  Every clash, not the first, for the reason `disjoint-problems` gives: a slot filled
  with three irreconcilable values forms three pairs, and which of them is reported may
  not depend on the order the extent came back in."
  [kb sentence context]
  (let [b (second (nm/args sentence))]
    (for [[h v] (functional-clashes kb sentence context)
          ;; violation iff no merge could reconcile them AND no merge already has
          :when (and (not (mergeable-values? v b))
                     (not (tax/same-class? (:taxonomy kb) v b)))]
      {:type :functional :sentence sentence :existing v :new b :opposing-handle h
       :message (str "functional violation: " (nm/functor sentence) " of "
                     (first (nm/args sentence)) " is already " v ", not " b)})))

(defn- functional-problem
  "The first functional clash, for the refusal paths."
  [kb sentence context]
  (first (functional-problems kb sentence context)))

(defn- asymmetry-problems
  "Every `(asymmetric P)` violation a sentence commits in `context`.

  `(asymmetric largerThan)` says `(P a b)` and `(P b a)` cannot both hold, so a claim
  whose **converse** is known-true is a contradiction rather than an addition.  The
  converse counts whether it was stated directly or reached by argument-position
  preservation — `(largerThan dog cat)` reaches `(largerThan cat maine_coon)` and every
  other pair below it, and a strict claim is exactly as binding there as where it was
  written (`vaelii.impl.inherit`).

  Only a **`:monotonic`** opposing claim refuses.  That is the whole strict/typical
  distinction, and it is read off the claim rather than the vocabulary: known-true
  content is the fixed background, so contradicting it is an error, while a `:default`
  generality is something a more specific statement is *entitled* to override — there
  the inheritance is undercut and never fires, so no clash reaches here at all.

  A **`:default`** opposing claim is still reported, and that is what makes a relation
  declared not to hold both ways stop holding both ways in silence: the violation is
  not a refusal (`refuses-assert?` reads the class), it is the pair `settle` arbitrates
  — at equal class, a represented dilemma in `(contradictions kb)`.

  The **strongest** surviving opposing claim is reported first, ties broken on the
  context name and then on the sentence, for the reason `inherit/strongest-per-tuple`
  gives: taking the first found would key an admission decision on handle iteration
  order, and handles are allocated in assertion order.  The sentence is what settles a
  tie the context name cannot — argument preservation reaches the converse from a
  sub-predicate, so two claims of equal class in one context are ordinary, and a key
  that stops at the context leaves that pair to iteration order.

  **One violation per opposing sentex**, in that order, for the reason
  `disjoint-problems` gives: the converse stated in a general context and again in
  one that sees it is two claims, and each is its own pair with the sentence here.  The
  refusal path takes the first and is therefore deciding against the strongest, which is
  the claim it always decided against; the discovery weighs all of them.  Deduped on the
  handle, since preservation can reach one stored claim by several routes.

  That is why the converse is read **twice**.  `inherit/surviving` answers what is
  *inherited* — one claim per tuple, the strongest — which is the right answer to whether
  the converse is licensed, and drops the duplicates on purpose
  (`inherit/strongest-per-tuple`).  The duplicates are exactly what a pair needs, so the
  sentexes literally stating the converse are read beside it and merged on the handle.
  Nothing is resurrected by that: a claim at the goal's own tuple is the most specific
  there is, so `undercut?` never displaced one.

  Ground binary sentences only; an open or n-ary one has no converse to speak of."
  [kb sentence context]
  (let [pred (nm/functor sentence)
        args (vec (nm/args sentence))]
    (when (and (symbol? pred) (= 2 (count args))
               (every? sx/ground-term? args)
               (tax/has-prop? (:taxonomy kb) :asymmetric pred context))
      (let [converse (list pred (second args) (first args))
            stated   (for [m   (res/matches-visible kb converse context)
                           :let [sxr (nth m 2) h (first m)]
                           :when (= converse (:sentence sxr))]
                       {:polarity :for :handle h :sentence (:sentence sxr)
                        :context (:context sxr)
                        :class (or (jtms/defeat-class (:tms kb) h) :default)})
            opposing (->> (concat (filter #(= :for (:polarity %))
                                          (inherit/surviving kb converse context))
                                  stated)
                          (sort-by (juxt #(- (strength/rank-of (:class %)))
                                         #(str (:context %))
                                         #(pr-str (:sentence %))))
                          (reduce (fn [acc o]
                                    (if (some #(= (:handle %) (:handle o)) acc)
                                      acc
                                      (conj acc o)))
                                  []))]
        (for [o opposing]
          {:type :asymmetric :sentence sentence :pred pred
           :opposing (:sentence o) :opposing-handle (:handle o)
           :message (str "asymmetric: " pred " cannot hold both ways, and "
                         (pr-str (:sentence o))
                         (if (= :monotonic (:class o)) " is known true" " is believed")
                         (when (not= (:sentence o) converse)
                           (str " (which reaches " (pr-str converse)
                                " by argument preservation)")))})))))

(defn- asymmetry-problem
  "The strongest `(asymmetric P)` violation, for the refusal paths."
  [kb sentence context]
  (first (asymmetry-problems kb sentence context)))

(defn- checked-sentence
  "The body the definitional checks see: the double-negation-eliminated positive body,
  so a `(not (not (dog Muffet)))` is still arg/disjoint/functional-checked and a genuine
  negation is not."
  [sentence]
  (or (sx/positive-body sentence) sentence))

(defn- constraint-problem
  "The first definitional violation for `chk` in `context`, as a value, or nil
  when the sentence is admissible.  The checks are stated once, here, and every
  path reads them: `constraint-checks` (assert) throws the value,
  `constraint-violation` (derivation) records it.

  `types` is the shared membership reader (`kb/membership-reader`).  The arms that ask
  what types a term holds ask about the same few terms — the sentence's arguments and
  its predicate — and between them ask several times each: the arity arm reads the
  predicate's memberships for three spellings and again for `variableArity`, `argIsa`
  reads an argument's twice per constraint, and for a unary sentence the disjointness
  arm wants the very memberships `argIsa` just read.

  The answer is stamped with the opposing sentex's defeat class where it names one, so
  the two callers decide refusal-versus-nogood from the value alone rather than each
  reaching back into the TMS for the same reading."
  [kb chk context types decls]
  (with-opposing-class
    kb
    (or (arity-problem kb chk context types decls)
        (args-problem kb chk context types decls)
        (inter-args-problem kb chk context types decls)
        (genls-problem kb chk context decls)
        (declaration-problem kb chk context types)
        (disjoint-problem kb chk context types)
        (asymmetry-problem kb chk context)
        (functional-problem kb chk context))))

;; ---- what the argument constraints *entail* ------------------------------
;; `args-problem` and `genls-problem` read `argIsa` / `argGenl` as constraints to test,
;; and their open-world floor is the same in both: an argument with no visible place in
;; the genl hierarchy cannot violate anything, so it passes and nothing is learned.  But
;; the declaration says what the argument *is*, and a KB told twice over that Fred fills
;; an `animal` slot still cannot answer `(animal Fred)` with a record.
;;
;; So the declarations are read a second way — as entailments.  The pairing is what is
;; entailed: **one entailment per (sentence, applicable declaration) pair**, drawn
;; whenever the declaration speaks for the context and names a type the hierarchy holds.
;;
;; **Nothing narrows that on grounds of redundancy**, and the reason is the invariant
;; rather than taste.  Every candidate narrowing — "the argument already has a type
;; reaching this one", "the type is already stored" — asks about *derived state*, which
;; is a function of what has arrived so far.  Withhold on those grounds and
;; `(dog Fred)` arriving before the declaration suppresses a materialization that the
;; same three sentences in the other order produce; withhold the *justification* on
;; those grounds and a second fact entailing the same type contributes no support, so
;; retracting the first sweeps a type the second still licenses, and which of the two
;; holds it up depends on which arrived first.  Both are belief varying with arrival
;; order, which is the one thing it may not do (docs/nmtms.md).
;;
;; So every applicable pair draws its entailment and `find-or-create-sentex` /
;; `has-justification?` do the deduplication at the point where it is a property of
;; content: one sentex per sentence, one justification per pair, whatever the order.
;; That a subsuming membership would also have reached the type is not a reason to
;; withhold a justified record — being a record is the whole of what this adds.
;;
;; Nothing here writes: the entailment is a **value**, and the sentex that would
;; justify it does not exist yet — the checks run before anything is stored, so a
;; refusal leaves nothing behind.  `special/deduce-arg-types` materializes it in the
;; post-store slot, beside the decontextualization lift, where there is a handle to
;; hang `[source-handle declaration-handle]` on.

(def ^:dynamic *assertive-arg-types?*
  "Do the argument constraints *entail* as well as constrain?

  **Off by default.**  A KB that derives types it cannot retract cleanly is worse than
  one that derives none, and entailing changes what a KB *contains* rather than only
  what it answers — so it is opt-in, and off leaves the constraint reading alone
  (docs/argtypes.md).

  `binding` it is the ordinary way in.  `VAELII_ASSERTIVE_ARG_TYPES=1` sets the root
  value instead, which is what lets the whole suite be run under it — the parity gate
  that says the entailment is additive rather than a different engine."
  (config/assertive-arg-types?))

(def ^:private universal-context
  "The one context every other sees.  A declaration stated there speaks for every
  context, so it entails locally wherever it is visible; `special/universal-context` is
  the same symbol, named there for the lift."
  'UniverseContext)

(defn- mintable-type?
  "Is `t` a type a membership can be minted in — a name the genl hierarchy actually
  holds?

  A **global** read, like `genls-problem`'s individual floor and for the same reason:
  this asks what the name *is*, not what a context can see of it, and an entailment
  drawn in a context that cannot see `thing` would be an entailment about nothing.
  A name the hierarchy does not hold is not a type we invent a membership in — which
  is where a structural constraint (an argument that must be a number, a string) lands
  without needing a list of exemptions to keep in step."
  [tax t]
  (and (symbol? t) (not (sx/variable? t)) (tax/genl? tax t 'thing)))

(defn- declares-locally?
  "Does the declaration stored at `dh` speak **for** `context`, rather than merely
  reaching it?

  A declaration is *inherited* by every descendant of the context it was written in,
  and there it constrains: an ancestor schema enforces its argument types in every
  context below it.  It does not *entail* there — an upper-band schema would
  otherwise spray derived `(T x)` memberships across every context that inherits it,
  claims no author of that context made.  So only a declaration written in the
  context being checked, or in `UniverseContext` (which speaks for every context by
  construction), draws the entailment.

  One record fetch, asked last of the conditions so it is paid only for a declaration
  that would otherwise mint."
  [kb dh context]
  (let [dc (:context (p/get-sentex (:records kb) dh))]
    (or (= dc context) (= dc universal-context))))

(defn- arg-entailments
  "The entailments one argument-constraint kind draws over `sentence`'s arguments in
  `context` — a seq of `{:assert <sentence> :because [decl-handle] :position n
  :kind argIsa|argGenl}`.

  `eligible?` is the kind's reading of \"this argument is the sort of term the
  entailment can be about\", and it is a property of the **term** alone, never of what
  the KB has learned about it so far — which is what keeps the answer a function of
  content.  It doubles as the early-out: no eligible argument means no declaration can
  say anything, and the declaration query is never run."
  [kb sentence context decls kind eligible? mint]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (:taxonomy kb)]
    (when (and (symbol? pred) (some eligible? as))
      (for [[dh b] (decls kind)
            :let  [n   (get b '?n)
                   t   (get b '?type)
                   arg (arg-at as n)]
            :when (and arg (eligible? arg)
                       (mintable-type? tax t)
                       (declares-locally? kb dh context))]
        {:assert (mint arg t) :because [dh] :position n :kind kind}))))

(defn- inter-arg-entailments
  "The entailments `interArgIsa` draws over `sentence`'s arguments in `context`.

  Exactly as strong as `argIsa`'s, and drawn under the same condition the check convicts
  on: the trigger argument must *already* be established as a `T`, so the entailment is
  what the declaration says once its antecedent holds.  A dormant constraint entails
  nothing, which is the same asymmetry `inter-args-problem` reads.

  `types` is therefore needed here where `arg-entailments` needs none — the unconditional
  kinds ask nothing about what the KB has learned, and this one has to.  Behind the same
  O(1) gate `inter-args-problem` is, and for the same reason."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (:taxonomy kb)]
    (when (and (symbol? pred) (some checkable-term? as)
               (pos? (p/count-with-functor (:index kb) 'interArgIsa)))
      (for [[dh b] (decls 'interArgIsa)
            :let  [n       (get b '?n)
                   t       (get b '?type)
                   m       (get b '?m)
                   u       (get b '?utype)
                   trigger (arg-at as n)
                   target  (arg-at as m)]
            :when (and trigger target
                       (checkable-term? trigger) (checkable-term? target)
                       (symbol? t)
                       (kb/isa-among? (:closures (types trigger)) t)
                       (mintable-type? tax u)
                       (declares-locally? kb dh context))]
        {:assert (list u target) :because [dh] :position m :kind 'interArgIsa}))))

(defn constraint-entailments
  "What `sentence`'s visible argument declarations entail about its arguments in
  `context` — a vec of `{:assert <sentence> :because [decl-handle] :position n :kind
  argIsa|argGenl|interArgIsa}`, empty when they entail nothing.

  `(argIsa parentOf 1 animal)` over `(parentOf Fred Mary)` entails `(animal Fred)`;
  `(argGenl partType 1 physical_object)` over `(partType wheel_kind axle_kind)` entails
  `(genl wheel_kind physical_object)`; `(interArgIsa eats 1 carnivore 2 meat)` over
  `(eats Rex Chunk)` entails `(meat Chunk)` — but only once `Rex` is known to be a
  carnivore, which is the condition the declaration is *about*.  An **individual** in an
  `argGenl` position is convicted by `genls-problem` rather than given an edge, so it is
  ineligible here — said at the point it matters rather than relying on the check having
  run first.

  One entry per applicable declaration, with no narrowing for redundancy: see the
  commentary above for why every candidate narrowing would make belief depend on
  arrival order.  Deduplication is the materializer's, where it is keyed on content.

  **Reads only.**  The caller decides whether to store, and the caller is
  `special/deduce-arg-types`, which mints each one as a derived sentex justified by
  `[the triggering fact, the declaration]` — so retracting either takes the type back."
  ([kb sentence context]
   (constraint-entailments kb sentence context
                           (kb/membership-reader kb context)
                           (declaration-reader kb (nm/functor sentence) context)))
  ([kb sentence context types decls]
   (when *assertive-arg-types?*
     (vec (concat (arg-entailments kb sentence context decls 'argIsa
                                   checkable-term?
                                   (fn [arg t] (list t arg)))
                  (arg-entailments kb sentence context decls 'argGenl
                                   #(and (checkable-term? %) (not (nm/individual? %)))
                                   (fn [arg t] (list 'genl arg t)))
                  (inter-arg-entailments kb sentence context types decls))))))

(defn constraint-checks
  "Throw the first definitional violation as typed ex-info — the assert path.

  Not every violation refuses.  One that names an opposing *believed* sentex is a
  nogood, and whether the writer is told no is `refuses-assert?`'s question: against
  known-true content, yes (admitting it would store what the KB can never believe);
  against a defeasible claim, the sentence is admitted and `settle` arbitrates the pair
  it forms.  An admitted clash is **not** reported here — settle discovers it from the
  relabelled region, which is what makes the discovery route-agnostic and the answer
  the same in every arrival order.

  Returns the **entailments** the argument constraints draw over an admissible
  sentence (`constraint-entailments`), for the caller to materialize once the sentex
  it would be justified by exists.  Empty unless `*assertive-arg-types?*`."
  [kb sentence context]
  (let [chk   (checked-sentence sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)
        p     (constraint-problem kb chk context types decls)]
    (if (refuses-assert? kb p)
      (throw (ex-info (:message p) (dissoc p :message)))
      (constraint-entailments kb chk context types decls))))

(defn constraint-admission
  "The derivation path's `constraint-checks`: one pass over the definitional checks,
  answering both halves as values — `{:violation v}` when `sentence` is inadmissible
  in `context`, else `{:entailments [...]}`.

  Forward chaining must not throw — a rule firing mid-fixpoint that aborted the run
  would leave belief half-computed, and the project's stance is that contradictions
  are soft.  So the derivation path asks the question instead of being stopped by
  the answer.  No try/catch: the checks bottom out as values, so there is no thrown
  answer to fish back out (and no whitelist of `:type`s for a new check to miss).

  An **arbitrable** violation is not a violation here at all.  A firing has no caller
  to refuse, so the two answers available are dropping the conclusion — no sentex, no
  justification, and `why-not` reduced to `:not-stored` — or placing it and letting
  `settle` weigh the pair like any other contradiction.  Placing it is what gives the
  loser a reason, so this reports only what genuinely cannot be represented: a
  malformed sentence, or an argument constraint, whose conviction rests on the
  *absence* of a fact rather than on a second one to weigh against."
  [kb sentence context]
  (let [chk   (checked-sentence sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)
        p     (constraint-problem kb chk context types decls)]
    (if (and p (not (arbitrable? p)))
      {:violation {:violation (:type p) :detail (dissoc p :type :sentence)}}
      {:entailments (constraint-entailments kb chk context types decls)})))

(defn constraint-violation
  "The definitional checks as a value alone: nil when `sentence` is admissible in
  `context`, else `{:violation :arity|:arg-type|:arg-genl|:arg-position
  |:arg-constraint-kind|:disjoint|:asymmetric|:functional :detail {...}}`.

  **Every** violation, arbitrable ones included — which is what separates this from
  `constraint-admission`.  The callers are the paths that *mint* content nobody asked
  for and that has somewhere else to be: the decontextualization lift's copy, the
  equality migration's twin, and the gate on what `abduce` may assume.  None of those
  is a rule firing with a conclusion to stand behind — a lift can decline to copy, a
  merge can decline to restate, an abducer can decline to hypothesize — so where a
  firing arbitrates, they refuse, and the refusal is reported rather than thrown."
  [kb sentence context]
  (let [chk   (checked-sentence sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)]
    (when-let [p (constraint-problem kb chk context types decls)]
      {:violation (:type p) :detail (dissoc p :type :sentence)})))

(defn arity-violation
  "The arity violation `sentence` commits in `context`, or nil — that one arm, asked of
  content **already stored**.

  The retroactive report's probe (`settle/report-arity-reach!`).  A declaration arriving
  after the facts it convicts was never seen by the check that runs on the way in, so
  the facts are re-asked here — the same `arity-problem` the door reads, so the two
  cannot drift about what a wrong arity is.

  Nothing else in the arm's family is asked: the sentence is stored, so whatever the
  other checks would say about it was said when it was written, and only the *arity*
  declaration is what just arrived.

  **No `:opposing-class`**, unlike every problem `constraint-problem` hands back.  A class
  is what a caller weighs two sides with, and this caller weighs nothing — stamping one
  would advertise an arbitration that deliberately does not happen."
  [kb sentence context]
  (let [chk   (checked-sentence sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)]
    (arity-problem kb chk context types decls)))

(defn arbitrable-violations
  "**Every** definitional clash `sentence` forms against believed content visible from
  `context` — the nogood half of the checks, read by `settle`'s discovery.  Empty when
  the sentence is admissible outright.

  Asked of a sentence that is itself **stored and believed**, which is what the
  discovery walks: the clashes it reports are with the *other* members of each pair,
  since a sentence never opposes itself (a term's own type is not disjoint from itself,
  its own value is not a second value, and its own converse is a different tuple).

  Plural, and that is the point.  `constraint-problem` stops at the first violation
  because a refusal needs only one reason.  A pair is not a reason — it is a fact about
  two sentexes — and a term holding three mutually disjoint types forms three of them,
  so stopping at the first would report a set of pairs that depended on the order the
  argument root handed the memberships back.  That order is handle order, which is
  arrival order, which is the one thing belief may not depend on.

  Only the three arbitrable arms run.  The argument constraints cannot produce a pair,
  and on this path the sentence is already stored — so whatever they would say about it
  was said when it was written."
  [kb sentence context]
  (let [chk   (checked-sentence sentence)
        types (kb/membership-reader kb context)]
    (->> (concat (disjoint-problems kb chk context types)
                 (functional-problems kb chk context)
                 (asymmetry-problems kb chk context))
         (map #(with-opposing-class kb %))
         (filter arbitrable?))))

(defn check-ground
  "Reject a non-rule sentence that still contains pattern variables.

  A fact asserts something; `(mortal ?x)` asserts nothing — it is an open sentence.
  Stored as a premise it is worse than useless: `unify` matches it against any goal,
  so it silently behaves as a universally quantified fact that nothing ever licensed.
  Universal claims are written as rules, where `check-range-restricted` governs the
  variables.

  Rule-ness is read off the **canonicalized record**, not off the raw input: an
  `implies`, a `set/*Rule` wrapper, and a nested combination of the two all
  canonicalize into `:antecedent`, and pattern-matching the input would have to
  re-derive that (and would miss a spelling).

  A **schematic equation** `(equals (fatherOf (fatherOf ?x)) (grandfatherOf ?x))` is
  the deliberate exception: its variables belong to a term-rewriting schema, not to an
  open fact, so it is stored as an oriented rewrite rule rather than refused
  (docs/equality.md, symbolic equational reasoning).  It is not matched as a fact
  under `unify` — its functor is `equals`, read by the equality machinery, not by the
  fact prover for arbitrary goals."
  [kb sentence context]
  (let [s (res/kb-sentex kb sentence context)]
    (when (and (nil? (:antecedent s)) (not (sx/ground? s))
               (not (rewrite/schematic-equation? sentence)))
      (throw (ex-info (str "not ground: " (pr-str sentence)
                           " contains a variable — a fact must be ground"
                           " (write a universal claim as a rule)")
                      {:type :not-ground :sentence sentence :context context})))))

;; ---- stratification -----------------------------------------------------
;; The rule-set half of well-formedness: a rule whose `exceptWhen` exception closes
;; a cycle through negation is refused, the way a `genl` cycle is.  The graph itself
;; and the search live in `vaelii.impl.wff`; what lives here is reaching the stored
;; rules, which is the rule index's job — `rules-by-consequent` answers "what could
;; conclude P?" whatever a rule's direction, so no scan is needed.
;;
;; **Two things can close a cycle**, because both kinds of edge fan out over the genl
;; **spec** closure: a *rule* arriving, and a *taxonomy edge* arriving underneath
;; rules that are already stored.  An exception on `flightless` is reached by a
;; stored `(penguin Opus)` the moment `(genl penguin flightless)` holds, whichever of
;; the two arrived last.  So the walk runs on both paths:
;;
;;   `check-stratified`        a rule is being asserted   -> throw
;;   `check-edge-stratified`   an edge is being asserted  -> throw
;;   `edge-stratification-violation`   an edge is being *derived* -> report
;;
;; Only *additions* can close a cycle: `specs` grows monotonically with the edge set,
;; so removing an edge only removes graph edges and a retraction needs no check.

(defn- negative-predicates
  "The predicates a rule depends on **negatively**.

  Three things put a predicate here.  An `exceptWhen` exception and an `(unknown S)`
  antecedent, both negation as failure over what the KB derives — the exception at
  rule granularity, the `unknown` per-literal — so asserting a fact can *withdraw* a
  conclusion, and a cycle through either is order-dependent (docs/exceptions.md,
  docs/naf.md).  Both arrive here already collected as `neg-query-preds`.  And a
  `different` antecedent, which is negation as failure over the **equality closure**:
  it holds exactly while nothing has merged its arguments, so asserting an equality
  *withdraws* it, and a rule that concludes an equality from a `different` antecedent
  is a cycle through negation whose settled state would depend on arrival order
  (docs/equality.md, \"Interactions — Stratification\").

  The negative edge from a `different` antecedent runs to the three relations that
  assert a merge, not to `different` itself — nothing ever concludes `different`, so
  an edge keyed on it would reach no rule and find no cycle."
  [antecedent-preds neg-query-preds]
  (concat neg-query-preds
          (when (some #(= 'different %) antecedent-preds) kb/equality-predicates)))

(defn- exception-predicates
  "The predicates the exceptWhen exceptions of stored rule `handle` mention — the
  negative-edge keys the stratification graph reads, gathered from the rule's
  belief-following exceptWhen meta-sentexes (`provers/rule-exceptions`)."
  [kb handle]
  (mapcat #(keep nm/functor %) (provers/rule-exceptions kb handle)))

(defn- rule-graph-node
  "The stratification graph's view of a stored rule: what it depends on, positively
  (its antecedent predicates) and negatively (the predicates its exceptWhen exceptions
  and its `unknown` antecedents mention, plus the equality relations when it reads
  `different`).  The exceptWhen predicates come from the rule's meta-sentexes, so kb is
  needed."
  [kb handle rule-sentex]
  (let [antes (rules/antecedent-predicates (:sentence rule-sentex))]
    {:id               handle
     :label            (str "rule#" handle)
     :antecedent-preds antes
     :exception-preds  (negative-predicates
                        antes (concat (exception-predicates kb handle)
                                      (rules/recheck-predicates rule-sentex)))}))

(defn- stored-rule-node
  "The graph node for a stored rule handle — nil if the handle names something that
  is not a rule, which the rule index should never hand back but which a stale
  posting could."
  [kb handle]
  (when-let [rsx (p/get-sentex (:records kb) handle)]
    (when (rules/rule? rsx) (rule-graph-node kb handle rsx))))

(defn- stratification-concluders
  "Predicate -> the rule nodes concluding it, read off the rule index.

  The one-arity is the graph exactly as **stored**, which is what an edge change is
  checked against.  The two-arity adds `pending`, the rule (or exception) being added,
  under its own consequent by hand: it is not reflected in the graph yet, and without
  it a rule whose exception mentions what it concludes — a one-rule cycle — would look
  stratified."
  ([kb]
   (fn [pred]
     (keep #(stored-rule-node kb %) (p/rules-by-consequent (:index kb) pred))))
  ([kb pending]
   (let [stored (stratification-concluders kb)]
     (fn [pred]
       (cond-> (remove #(= (:id %) (:id pending)) (stored pred))
         (= pred (:consequent-pred pending)) (conj pending))))))

(defn check-stratified
  "Throw unless adding this rule leaves the rule set stratified — see
  docs/exceptions.md.  Runs before anything is stored, so a refused rule leaves no
  partial state behind.

  Fast path: with no exception on the rule being added and none on any stored rule,
  the graph has no negative edge at all and no cycle through negation is possible,
  so the walk is skipped entirely.  That is every rule in an ontology that uses no
  exceptions, which is most of them."
  [kb sentence inner context]
  (let [[_ _ exception] (sx/peel-rule-wrapper sentence)
        antes             (rules/antecedent-predicates inner)
        ;; negatives: the exception's predicates, the `unknown` antecedents' *and* the
        ;; **aggregate** bodies'.  All three read what the KB believes rather than a
        ;; fact the firing names, so a cycle through any of them is unstratified — a
        ;; rule whose count is over a relation the rule itself concludes has no settled
        ;; answer, and which one it lands on would depend on arrival order.
        negatives         (negative-predicates antes (concat (keep nm/functor exception)
                                                             (rules/naf-predicates-of inner)
                                                             (rules/aggregate-predicates-of inner)))]
    ;; The fast path skips the walk when the graph has no negative edge at all — now
    ;; a `different` antecedent counts as one, so a rule that reads the equality
    ;; closure is walked even though it carries no `exceptWhen`.
    (when (or (seq negatives) (seq (p/exception-rules (:index kb))))
      (let [pending {:id               ::pending
                     :label            "the rule being asserted"
                     :antecedent-preds antes
                     :exception-preds  negatives
                     :consequent-pred  (rules/consequent-predicate inner)}]
        (when-let [cycle (wff/negation-cycle (:taxonomy kb)
                                             (stratification-concluders kb pending)
                                             pending)]
          (throw (ex-info (str "not stratified: the rule set would have a cycle through "
                               "negation: " (wff/cycle-description cycle))
                          {:type :not-stratified :sentence inner :context context
                           :cycle cycle})))))))

(defn check-exceptWhen-stratified
  "Throw unless adding an exceptWhen exception mentioning `new-exc-preds` to the stored
  rule `rule-handle` leaves the rule set stratified.

  The exception is a new negative edge from the rule to those predicates, so it can
  close a cycle through negation exactly as a whole rule can (`check-stratified`).  The
  pending node is the rule's stored graph node augmented with the new negative edges;
  `stratification-concluders` swaps it in for the stored rule so the walk sees the edge.
  Runs before the meta-sentex is stored, so a refused exception leaves nothing behind."
  [kb rule-handle new-exc-preds context]
  (when-let [rsx (p/get-sentex (:records kb) rule-handle)]
    (let [base    (rule-graph-node kb rule-handle rsx)
          pending (assoc base
                         :label           (str "rule#" rule-handle " (with the new exception)")
                         :exception-preds (concat (:exception-preds base)
                                                  (negative-predicates (:antecedent-preds base)
                                                                       new-exc-preds))
                         :consequent-pred (rules/consequent-predicate (:sentence rsx)))]
      (when (seq (:exception-preds pending))
        (when-let [cycle (wff/negation-cycle (:taxonomy kb)
                                             (stratification-concluders kb pending)
                                             pending)]
          (throw (ex-info (str "not stratified: the exception would give the rule set a "
                               "cycle through negation: " (wff/cycle-description cycle))
                          {:type :not-stratified :rule rule-handle :context context
                           :exception-preds (vec new-exc-preds) :cycle cycle})))))))

(defn- edge-negation-cycle
  "The cycle through negation that adding this `genl` / `genlContext` sentence would
  create among the **stored** rules, or nil.  Nil for anything that is not one of
  those two edges.

  Every cycle through negation contains at least one negative edge, and negative
  edges leave excepted rules only — so starting the walk at each excepted rule is
  complete, and `exception-rules` is exactly that roster in one lookup.  That is the
  same set (and the same reason) as `recheck-every-exception`'s: an edge change has
  no rule and no fact to narrow by, so it re-walks the excepted rules wholesale.
  They are few, and edge changes are rare.

  **Fast path:** no stored rule carries an exception, so the graph has no negative
  edge and no walk can find one.  That is every rule in the bundled starter, so an
  ordinary `genl` assert pays one set read and stops.

  The edge is added to a **detached copy** of the taxonomy rather than to the real
  one: the check runs before anything is written, and a refused edge must leave the
  cached closures untouched as well as the store."
  [kb sentence]
  (let [f (nm/functor sentence)]
    (when (or (= f 'genl) (= f 'genlContext))
      (let [excepted (p/exception-rules (:index kb))]
        (when (seq excepted)
          (let [[_ a b]    sentence
                probe      (tax/detached-copy (:taxonomy kb))
                _          (if (= f 'genl)
                             (tax/add-genl probe a b ::probe)
                             (tax/add-genlContext probe a b ::probe))
                concluders (stratification-concluders kb)]
            (some #(some->> (stored-rule-node kb %)
                            (wff/negation-cycle probe concluders))
                  excepted)))))))

(defn check-edge-stratified
  "Throw unless adding this taxonomy edge leaves the stored rule set stratified.

  The `genl` assert is the operation at fault, so refusing the *edge* is the
  consistent answer: it is what `wff` already does to an edge that would make the
  taxonomy cyclic, and it keeps the invariant that stored state is always stratified
  — which is what lets `check-stratified` look only for cycles through the rule being
  added.  Runs before the sentex is created and before the taxonomy is touched."
  [kb sentence context]
  (when-let [cycle (edge-negation-cycle kb sentence)]
    (throw (ex-info (str "not stratified: " (pr-str sentence)
                         " would give the rule set a cycle through negation: "
                         (wff/cycle-description cycle))
                    {:type :not-stratified :sentence sentence :context context
                     :cycle cycle}))))

;; (`wff-violation` — structural well-formedness as a value, for derived content —
;; lives in `vaelii.impl.special` now: the per-functor wff dispatch is a column of
;; the special-predicate table, which sits a layer above this namespace.)

(defn edge-stratification-violation
  "The same check as a **value**, for a `genl` / `genlContext` edge a rule *derived*
  rather than one a caller asserted: nil when the edge is admissible, else a
  violation map in the shape `constraint-violation` returns.

  A derived edge reaches the taxonomy through `integrate-transitive`, so a rule
  concluding `(genl a b)` can close a cycle with no caller asserting anything.
  Throwing there is the wrong shape — chaining is a fixpoint and must not abort
  halfway through one — so this joins the definitional constraints on the derivation
  path: the conclusion is dropped and reported in `(core/violations kb)`.  Dropping
  it is what keeps the invariant intact, since an unstratified edge that was merely
  *reported* would still be in the taxonomy."
  [kb sentence]
  (when-let [cycle (edge-negation-cycle kb sentence)]
    {:violation :not-stratified
     :detail    {:cycle   cycle
                 :message (str "not stratified: deriving " (pr-str sentence)
                               " would give the rule set a cycle through negation: "
                               (wff/cycle-description cycle))}}))

;; Negation is *not* a hard check.  `(not S)` and `S` co-existing is a soft,
;; prioritized contradiction resolved at settle time (`vaelii.impl.settle`):
;; the weaker-class belief is defeated, a default/default tie is a represented
;; dilemma, and an irreducible `:monotonic` clash is reported, never thrown.
