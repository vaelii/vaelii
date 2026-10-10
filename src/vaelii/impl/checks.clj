;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.checks
  "The definitional checks — arg argument types, disjointness, functionality —
  plus ground-ness and the stratification glue over the rule index.

  Second layer of the engine stack (kb <- checks <- special <- integrate <- chain
  <- settle):
  every check reads the KB (taxonomy, index, believed matches) and returns a value
  or throws — nothing here writes.  Both mutation paths consume these: `assert`
  (vaelii.core) throws the value, the derivation path (vaelii.impl.chain) records
  it in the violations ledger."
  (:require [clojure.string :as str]
            [taoensso.nippy :as nippy]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.config :as config]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.except :as exc]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.io.thaw :as safe]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]
            [vaelii.impl.wff :as wff]))

;; ---- invariants: naming + argument type declarations --------------------

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
  (`unary_predicate`, `instance_relation_predicate`, …), separates those types with
  `disjoint_metatype`, and constrains predicate-valued argument positions with
  `arg` — so restricting the checks to CapitalCamelCase individuals would leave
  the whole meta-level declared and unenforced.  Numbers, strings and compounds are
  excluded because a type membership cannot be asserted of one (a NAT reifies to its
  constant first, so a reified term is checked under that constant)."
  [x]
  (and (symbol? x) (not (sx/variable? x))))

(def ^:private syntactic-roots
  "The syntactic types a value is classified into — the roots of the kind lattice
  `quotedArg` types against.  A `quotedArg` whose declared type is neither one of these
  nor below one is out of the feature's domain (an imported constraint typing an argument
  as some domain collection), and the check reads it open-world rather than convicting.

  One per leaf kind a sentence can carry, and complete on purpose: a kind with no root
  here is one both argument checks have to wave through, which is a hole rather than a
  policy.  A compound is the exception `value-kind` states."
  '#{string number integer symbol keyword boolean character})

(defn- value-kind
  "The syntactic type of an argument taken as a **term** — its EDN kind, mapped to the
  type the argument checks compare it against: a string is `string`, an integer `integer`
  (a `number` below), any other number `number`, a keyword `keyword`, a boolean
  `boolean`, a character `character`, a non-variable symbol `symbol` (a name, however its
  role spells it).

  `nil` for the two things that are not a leaf with a knowable kind — a **variable**,
  which is not a term yet, and a **compound**, whose kind is not the question: what
  `(QuantityFn 5 Meter)` denotes is its function's business, so no syntactic answer would
  be the right one and both checks read it open-world.

  The syntactic half is the whole of what this declines to answer, and the semantic half
  is answered beside it: `result` / `genlResult` say what an application denotes, and
  `convicting-result-type` reads them.  A **reifiable** application reaches neither — it
  is minted before the checks run and arrives as the constant its result types were
  materialized on, checked like any symbol — so a compound seen here is one that is never
  minted, and its function's declaration is the only thing the KB can know about it.

  A literal value's kind is `provers/literal-value-kind`'s, the table `EvaluableProver`
  answers a value-kind membership from, so the argument checks and the prover read one
  classification.  A symbol is the one kind added here."
  [x]
  (or (provers/literal-value-kind x)
      (when (and (symbol? x) (not (sx/variable? x))) 'symbol)))

(defn- value-kinds
  "The most specific built-in types known from a value.

  Most values have only their EDN kind. Integers additionally carry the sign-refined
  types declared in CxCore. Zero belongs to both non-negative and non-positive; returning
  a set rather than forcing one artificial leaf keeps both argument constraints exact.

  **Read by both argument readings, which is why it is not named for either.**  `arg`
  types what an argument denotes and `quotedArg` the term written there, and for a
  *value* those coincide — a value denotes itself, which is the whole reason the EDN
  kinds sit in the `genl` lattice at all (CxCore, and `vocabulary.clj`'s note on the
  value kinds).  A sign is as decidable from `5` written in a position as from what
  `5` denotes, so a reading that admitted `integer` and refused `positive_integer` would
  not be more conservative, only wrong in one direction: `args-quoted-problem` read
  `value-kind` alone and so convicted **every** integer of failing
  `(quotedArg P n positive_integer)`, the declared type being *below* the kind rather
  than above it (#55).  One reader, both entry points."
  [x]
  (if (integer? x)
    (cond
      (pos? x) '#{positive_integer non_negative_integer}
      (neg? x) '#{negative_integer non_positive_integer}
      :else    '#{non_negative_integer non_positive_integer})
    (if-some [t (value-kind x)] #{t} #{})))

(defn- syntactic-type?
  "Is `t` a type `quotedArg` can judge a value against — a syntactic root or a subtype
  of one?  A declared type outside this lattice leaves the constraint open-world."
  [tax t context]
  (or (contains? syntactic-roots t)
      (some #(tax/genl? tax t % context) syntactic-roots)))

(def ^:private declaration-queries
  "Per declaration kind, the sentence `declaration-reader` queries: the functor, then the
  argument tail that follows the predicate being asked about.  A table rather than a cond
  chain, because the kinds differ in *arity* as well as in functor — `interArg` names
  two positions and two types — and a chain would put that difference in the caller."
  '{arg      (arg ?n ?type)
    genlArg     (genlArg ?n ?type)
    quotedArg   (quotedArg ?n ?type)
    interArg (interArg ?n ?type ?m ?utype)
    args           (args ?type)
    argsGenl        (argsGenl ?type)
    argAndRest      (argAndRest ?start ?type)
    argAndRestGenl  (argAndRestGenl ?start ?type)
    interArgs       (interArgs ?type)
    interArgAndRest (interArgAndRest ?start ?type)})

(def constraint-declaration-functors
  "The argument constraints this namespace reads at the entry point, as a set — `declaration-
  queries`' keys.

  Public because it is one of the rosters that reads the `:argument-constraint` family
  **as a family**, and `predicates/check-facets` holds those to enumerating exactly it.
  A spelling in the family and not here is one the entry point cannot query for and so never
  convicts; a spelling here and not in the family is one nothing declares."
  (set (keys declaration-queries)))

(defn- declaration-reader
  "A `kind -> [[handle bindings sentex] …]` reader for the argument constraints binding
  one predicate's tuples, memoized for the life of one caller.

  `args-problem`, `genls-problem` and the entailments all ask the same two questions —
  what does `arg` say about this predicate's positions, and what does `genlArg` —
  and `assert` names that read the dominant per-fact cost of a store.  Asking it once
  is what lets the entailment ride along on a walk the check was making anyway instead
  of doubling it.  Realized rather than lazy: a predicate carries a handful of
  declarations, and every caller but the first-violation `for` wants all of them.

  **The read is the union over the predicate's `genl` closure**
  (`res/constraining-predicates`), not the bare predicate: a super-predicate's
  declaration binds the sub-predicate's tuples, since a `genl` edge between predicates
  says the sub's tuples *are* the super's.  One site feeds all four consumers, so the
  refusal, both `genls`-level checks and the minting move together.  The union is
  realized for the reason the single read was: `in-content-order` sorts before the
  first-violation walk starts, so there is no early exit for laziness to serve, and the
  sort is what keeps the refusal keyed on what the KB says rather than on which
  super-predicate the closure happened to enumerate first.

  **Two arities.**  `(decls kind)` is the read above.  `(decls ::stored? functor)` is the
  O(1) gate the gated arms stand behind — is any `functor` sentex stored at all
  (`kind-stored?`) — memoized in `counts`, which a reader for a *nested* application
  shares with the reader of the sentence it sits in (`(decls ::counts nil)`), so one check
  pays each gate once however many applications it reads."
  ([kb pred context] (declaration-reader kb pred context (volatile! {})))
  ([kb pred context counts]
   (let [cache (volatile! {})]
     (fn
       ([kind]
        (if-some [ds (get @cache kind)]
          ds
          (let [[f & tail] (declaration-queries kind)
                ds         (when (symbol? pred)
                             (into []
                                   (mapcat #(res/matches-visible kb (list* f % tail) context))
                                   (res/constraining-predicates kb kind pred context)))]
            (vswap! cache assoc kind ds)
            ds)))
       ([op functor]
        (case op
          ::counts  counts
          ::stored? (if-some [b (get @counts functor)]
                      b
                      (let [b (pos? (reads/stored-count-with-functor (:index kb) functor))]
                        (vswap! counts assoc functor b)
                        b))))))))

(defn- kind-stored?
  "Is any `functor` sentex stored — the O(1) gate, asked through `decls` so a check pays it
  once (`declaration-reader`)."
  [decls functor]
  (decls ::stored? functor))

(defn- declared-of
  "The predicate a declaration match is *about* — its first argument, which is `pred`
  itself for a declaration written on the predicate under test and a super-predicate of
  it for one that descends.  Named in a refusal message so an author told a `fatherOf`
  claim is ill-typed can find the `parentOf` declaration that says so."
  [match]
  (second (:sentence (nth match 2))))

(defn- via-clause
  "The refusal's `, declared of P` clause, or the empty string when the declaration is
  the sentence's own predicate's."
  [via pred]
  (if (= via pred) "" (str ", declared of " via)))

(defn arity-binding-clause
  "How a message says what length binds a predicate: **is declared with 2 arguments** for
  one carrying its own declaration, **takes 2 arguments through parentOf** for one whose
  length descends from a super-predicate.

  Public and spelled once: `arg-position-problem` words a declaration naming a position
  the length denies with it, and a caller describing a binding reads the same clause.
  \"is declared with\" is false of a predicate that declared nothing and took its length
  off a super, so the split is a claim about the KB rather than a phrasing."
  [pred via n]
  (str (if (= via pred) "is declared with " "takes ")
       n " argument" (when (not= 1 n) "s")
       (when-not (= via pred) (str " through " via))))

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
  the rule `handle-namings` states for the handle a clash is reported as.  Existence is
  untouched: every declaration is still read, and a sentence no declaration convicts
  still has no violation.

  The key is built once per match and compared as a string (`nm/sort-by-content-key`
  with `compare`) — the same lexicographic order, off the per-comparison rebuild — and a
  run of one, the common case for a `(first (for …))` consumer, sorts nothing.  Printed
  through `nm/print-key`, so no ambient `*print-length*` collapses two declarations to
  one prefix: these sentences are *short*, which exposes them rather than protecting them
  — at `*print-length*` 3, `(arg parentOf 1 person)` and `(arg parentOf 1 animal)` print
  the same."
  [ds]
  (nm/sort-by-content-key #(nm/print-key (:sentence (nth % 2))) compare ds))

;; ---- what both readings of an argument declaration need ------------------
;; The toggle, and the two conditions an entailment is drawn under.  They sit above
;; the constraint arms rather than beside the entailment arms below because
;; `args-problem` reads them too: under the toggle its symbol arm yields to the
;; entailment, and what it yields to is exactly these conditions.

(def ^:dynamic *assertive-arg-types?*
  "Do the argument constraints *entail* as well as constrain?

  **On by default.**  The entailment is additive — it mints the type a declaration
  already constrains, as a justified, retractable sentex — and off leaves the constraint
  reading alone (docs/argtypes.md).

  `binding` it is the ordinary way in.  `VAELII_ASSERTIVE_ARG_TYPES=0` sets the root
  value off instead, which is what lets the whole suite be run under the constraint-only
  reading — the parity gate that says the entailment is additive rather than a different
  engine."
  (config/assertive-arg-types?))

(def ^:dynamic *entry-mints?*
  "Is the sentence being checked one the entry point will reify before storing it?

  True while `vaelii.core/check` reads a fact the way `assert` would store it, and while
  the forward chainer asks whether a conclusion naming an application with no constant
  yet is admissible before it mints one (`chain/reify-conclusion`).  `assert` mints
  every ground application of a reifiable function to a constant before its checks run,
  so an argument that is such an application is read there as that constant; neither
  of the two callers has minted it yet, and under this binding the argument arm reads
  the application as the constant would be read (`minted-application-clash`).  False
  everywhere else, where every reifiable application has already been replaced by its
  constant."
  false)

(defn mintable-type?
  "Is `t` a type a membership can be minted in — a name the genl hierarchy actually
  holds?

  A **global** read, like `genls-problem`'s individual floor and for the same reason:
  this asks what the name *is*, not what a context can see of it, and an entailment
  drawn in a context that cannot see `thing` would be an entailment about nothing.
  A name the hierarchy does not hold is not a type we invent a membership in — which
  is where a structural constraint (an argument that must be a number, a string) lands
  without needing a list of exemptions to keep in step.  The answer is held per `genl`
  generation (`tax/genl?-global-held`): a sweep asks it of one declaration's type once
  per fact."
  [tax t]
  (and (symbol? t) (not (sx/variable? t)) (tax/genl?-global-held tax t 'thing)))

(defn mintable-types
  "`mintable-type?` as a fn of one type, for a caller asking about many types while the
  hierarchy holds still: `thing`'s subtypes are walked once (`tax/specs-of-all`, global
  for `mintable-type?`'s reason) and each answer is a set lookup (docs/exceptions.md)."
  [tax]
  (let [under (tax/specs-of-all tax ['thing])]
    (fn [t] (and (symbol? t) (not (sx/variable? t)) (contains? under t)))))

(defn- visibility-support
  "The `genlCx` edge supporters along one visible path from `context` to the context the
  declaration stored at `dh` is written in, or empty when it is written in `context`.  A
  derivation drawn in `context` through a declaration it inherits rests on that path as it
  rests on the `genl` edges `edge-support` names, so retracting an edge on the path takes
  the derivation back and a surviving route draws it again
  (`special/rederive-descended`)."
  [kb dh context]
  (let [dc (:context (p/get-sentex (:records kb) dh))]
    (if (or (nil? dc) (= dc context))
      []
      (mapv first (tax/reach-support (reasoning/taxonomy kb) :genlCx context dc context)))))

(defn- trigger-supports
  "One support per believed membership `(T' x)` that makes `x` a `t` from `context`: the
  membership's handle, the `genl` edges from `T'` to `t` (`tax/reach-support`), and the
  `genlCx` edges `context` sees the membership through (`visibility-support`).  In content
  order; empty when no membership reaches `t`.  A derivation an `interArg` or a
  homogeneity declaration draws from a trigger names one of these, so retracting the
  membership or an edge on its route takes the derivation back."
  [kb x t context]
  (let [tax (reasoning/taxonomy kb)]
    (into []
          (keep (fn [m]
                  (let [t' (nm/functor (:sentence m))]
                    (when (tax/genl? tax t' t context)
                      (into [(:id m)]
                            (concat (mapv first (tax/reach-support tax :genl t' t context))
                                    (visibility-support kb (:id m) context)))))))
          (sort-by (juxt #(nm/name-key (nm/functor (:sentence %))) #(nm/name-key (:context %)))
                   (kb/type-memberships kb x context)))))

(defn- outside-declared-type?
  "Does `arg` fail the `(arg P n t)` demand, as seen from `context`?

  Two readings, because the KB knows two different amounts about the two kinds of term.

  A **symbol** is typed by what somebody asserted, so the reading is open-world: it
  violates nothing until it holds a membership, and then only if none of them reaches
  `t`.  A **value** is typed by what it *is* — `value-kind` reads its EDN kind, and
  those kinds sit in the `genl` lattice (CxCore) exactly so this comparison can be made.
  No assertion is involved and none is possible, so there is nothing to be open-world
  about: a string is a `string` and a `string` is not a `dog`, and saying so is the
  difference between a declaration that constrains a position and one that constrains
  the half of it somebody happened to spell with a name.

  The openness moves rather than disappearing, and it moves to the **declared type**: a
  `t` outside the hierarchy is one the lattice cannot place the kind against, which is
  the imported-constraint case `args-quoted-problem` exempts for the same reason.

  A **compound** is neither of the two readings and is not answered here.  It holds no
  membership and its kind is not the question; what it denotes is its function's business,
  and `convicting-result-type` beside this is the arm that reads the function.  What it
  is *given* is a separate question, `nested-input-problem`'s."
  [tax types arg t context]
  (if (checkable-term? arg)
    (let [ms (types arg)]
      (and (kb/isa-among? ms 'thing)
           (not (kb/isa-among? ms t))))
    (let [ks (value-kinds arg)]
      (when (seq ks)
        (and (symbol? t)
             (tax/genl? tax t 'thing context)
             (not-any? #(tax/genl? tax % t context) ks))))))

(defn- application-term?
  "Is `x` a function **application** — a compound whose head is a name?

  The one argument shape neither `checkable-term?` nor `value-kind` answers for: a type
  membership cannot be asserted of it, and its EDN kind is not the question its declared
  position asks.  A **vector** fails the head test rather than being excluded by name — a
  vector in a sentence is a list of forms (an `exceptWhen`'s conjuncts, a `thereExists`'s
  binders), so its first element is a form and not a function."
  [x]
  (and (sequential? x)
       (symbol? (first x))
       (not (sx/variable? (first x)))))

(defn- convicting-result-type
  "The declared result type that convicts the application `x` of failing a demand for
  type `t`, seen from `context`, or nil.  `declared` is the reader for the demand's
  reading — `nat/result-types` for `arg`'s instance demand, `nat/genl-result-types`
  for `genlArg`'s subtype one — and the two are never crossed: `arg` asks what the
  application *is*, `genlArg` what it is a *kind of*, and one declaration answers each.

  **A result declaration is a claim about the function, not about the application.**
  `(result QuantityFn measure)` says every `(QuantityFn m u)` denotes a measure; no
  application is typed on its own, and nothing here computes a per-application type —
  there is nothing to compute, a structural application holding no membership and being
  able to hold none.  A **reified** application does not arrive here at all: it is minted
  before the checks run, and its constant carries these very declarations materialized as
  `(T K)` / `(genl K T)`, which the symbol arm reads.  So this is the reading for the
  applications that are never minted, and it and the mint say the same thing about the
  same function.

  **Open-world, one level out from the symbol reading.**  A head that declares no result
  exempts every application of it, exactly as an unclassified symbol exempts itself, and a
  declared result the asking context cannot place in the hierarchy is no evidence either.
  Only a head with a declared result that visibly reaches `thing` and visibly fails to
  reach `t` convicts — `outside-declared-type?`'s floor and its negation as failure, with
  the head's declarations standing where a term's memberships stand.

  Content-least where a head declares several, so which of them a refusal names is keyed
  on what the KB says rather than on the order a retrieval enumerated them.

  **A quoting predicate's argument is a mention and is left alone.** `(termOfUnit K
  (FruitFn AppleTree))` and a compound-argument `(rewriteOf T E)` carry the NAT
  expression as a verbatim payload rather than as a term used in that position
  (`nat/nat-quoting-predicates`, docs/nat.md), so typing it by what the function yields
  would type a quotation by its referent.  It is also the one place a mint would pay for
  this: `mint-nat!` writes a `termOfUnit` per constant, and that write is where a KB
  declaring result types would otherwise buy a scoped retrieval it can never be convicted
  by.  A `quoting_function`'s argument is the same mention one level in, reached when
  `nested-input-problem` reads the quoting function's own declarations.

  Behind `nat/any-result-declarations?` — two O(1) functor counts, reached only for a
  compound sitting at a position some declaration constrains, so a KB that has written no
  result declaration pays nothing for this and one that has pays two integer reads."
  [kb declared pred x t context]
  (when (and (symbol? t) (application-term? x)
             (not (contains? nat/nat-quoting-predicates pred))
             (nat/any-result-declarations? kb))
    (let [tax (reasoning/taxonomy kb)
          rs  (vec (declared kb (first x) context))]
      (when (and (not (tax/quoting-function? tax pred))
                 (not-any? #(tax/genl? tax % t context) rs))
        (nm/min-by-content-key identity (filterv #(tax/genl? tax % 'thing context) rs))))))

(defn- entailment-covers?
  "Does the entailing reading answer for the argument `arg` of an argument constraint?

  Under `*assertive-arg-types?*` an argument constraint only adds support: it derives the
  membership it names over a symbol argument (`constraint-entailments`) and never convicts
  one on the memberships it holds.  That holds for a declaration written in the asking
  context and for one it inherits, and for a declared type the hierarchy does not hold
  yet, which derives nothing until it does.  A membership the declared type does not
  reach is a second membership beside the derived one, and a disjoint pair of them is a
  clash the settle places (docs/argtypes.md).

  Only the symbol arm yields.  A **value** carries its type in its syntax and an
  **application** is typed by its function's `result`; no membership can be derived of
  either, so for both the constraint reading is the only one there is."
  [arg]
  (and *assertive-arg-types?* (checkable-term? arg)))

(defn- minted-application-clash
  "How `assert` reads the argument `x`, a ground application of a reifiable function,
  where the `arg` declaration `d` demands `t` of it: nil when the reading below does not
  apply, `::admitted` when `assert` admits the argument, or the result type the demand
  clashes with.  Asked only under `*entry-mints?*`, the binding `check` reads a sentence
  under.

  `assert` mints such an application before the checks run, and the constant it mints
  holds the function's result types as memberships.  Under `*assertive-arg-types?*`, and
  where the declared type is one the hierarchy holds, the symbol arm then yields: the entailment mints `(t K)` and refuses it
  only where it clashes with a membership the constant holds (`entailment-check`).
  `check` does not mint, so it reads the application here, with the result types standing
  where the constant's memberships would: a result type that reaches `t` admits the
  argument, one the taxonomy separates from `t` is the clash, and any other admits it,
  since the entailment would mint `t` there.  The consequences of minting `(t K)` past that
  one membership are not read.  A quoting predicate's or quoting function's argument is a
  mention, which `convicting-result-type` leaves alone for the same reason, so nil."
  [kb tax pred x t context]
  (when (and *entry-mints?*
             *assertive-arg-types?*
             (not (contains? nat/nat-quoting-predicates pred))
             (not (tax/quoting-function? tax pred))
             (nat/reifiable-ground-nat? kb x)
             (mintable-type? tax t))
    (let [rs (vec (nat/result-types kb (first x)))]
      (if (some #(tax/genl? tax % t context) rs)
        ::admitted
        (let [dj? (tax/disjointness-test tax t context)]
          (or (nm/min-by-content-key identity (filterv dj? rs))
              ::admitted))))))

(defn- args-problem
  "First (arg pred n type) violation for a sentence, or nil.  Uses genl
  transitivity; only constraints and type memberships visible from `context`
  count.  Open-world about a **symbol**: an untyped one can't violate anything.  A
  **value** carries its type in its syntax and is checked against it —
  `outside-declared-type?` has that argument.

  **Genl transitivity in two places, not one.**  The constraint *type* is reached
  through the closure, and so is the constrained *predicate*: `decls` reads every
  declaration on `pred` and on the super-predicates `context` can see
  (`res/constraining-predicates`), because a `genl` edge between predicates says the
  sub-predicate's tuples are the super's, and a tuple set only narrows going down.  So
  `(arg parentOf 1 person)` refuses `(fatherOf TheRock1 Mary)` as surely as it
  refuses the same claim spelled `parentOf` — which it has to, since the stored
  sub-predicate fact answers every super-predicate query through the matcher's fan.

  **An application is typed by its function's `result`**, which is the one thing the
  KB can know about a term no membership can be asserted of: `(result QuantityFn
  measure)` refuses `(needs_dog (QuantityFn 5 Meter))` under `(arg needs_dog 1 dog)` and
  admits it under `(arg needsMeasure 1 measure)`.  `convicting-result-type` has that
  argument, the open-world floor included.  The application's own inputs are not read
  here: they answer to its function's declarations, and `application-input-problem` runs
  this arm again one level in, with the function where `pred` stands.

  **Under `*assertive-arg-types?*` the symbol arm yields** to the entailment that reads
  the same declaration (`entailment-covers?`): where the declaration mints the type, the
  argument cannot fail to have it.  What refuses in its place is the mint the KB cannot
  admit — `entailment-check` walks the whole cascade before anything is stored, so a
  declaration whose consequence clashes with a disjoint membership refuses the assert
  instead of dropping a conclusion after it.  Under `*entry-mints?*`, the binding `check`
  reads under, a ground application of a reifiable function is read the way `assert`
  reads the constant it mints (`minted-application-clash`), so a clash with its result
  type is `:disjoint` in `check` as it is in `assert`.

  `types` is the shared per-assert membership reader (`kb/membership-reader`), `decls`
  the shared declaration reader.  The two questions asked of each constrained
  argument — is it in the hierarchy at all, and does it reach the constraint type —
  are one retrieval and two set lookups, and a second constraint on the same position
  adds no retrieval at all."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (symbol? pred)
      (first
       (for [m     (in-content-order (decls 'arg))
             :let  [b     (nth m 1)
                    n     (get b '?n)
                    t     (get b '?type)
                    arg   (arg-at as n)
                    ;; a reifiable application, read as the constant `assert` mints
                    clash (when arg (minted-application-clash kb tax pred arg t context))
                    ;; the application arm — nil for every argument that is not one
                    r     (when-not clash
                            (convicting-result-type kb nat/result-types pred arg t context))]
             :when (and arg
                        (not= ::admitted clash)
                        (or clash r
                            (and (not (entailment-covers? arg))
                                 (outside-declared-type? tax types arg t context))))]
         (if clash
           (let [minted (list t arg)]
             {:type :disjoint :sentence minted :types [t clash] :entailed-from sentence
              :message (str "arg constraint: " (pr-str sentence) " entails " (pr-str minted)
                            ", which cannot be admitted — disjointness violated: "
                            (pr-str arg) " cannot be both " t " and " clash)})
           {:type :arg-type :sentence sentence :arg arg :expected t :position n
            ;; `pr-str`, so a convicted string reads as one — it prints the same as `str`
            ;; for every term that could already be convicted here
            :message (str "arg constraint: " (pr-str arg) " must be a " t
                          (when r (str " — " (first arg) " results in a " r))
                          " (arg " n " of " pred (via-clause (declared-of m) pred) ")")}))))))

(defn- inter-args-problem
  "First `(interArg pred n T m U)` violation for a sentence, or nil.

  The **conditional** argument constraint: if argument `n` is a `T`, argument `m` must be
  a `U`.  `(interArg eats 1 carnivore 2 meat)` says a carnivore eats meat — a claim
  `arg` cannot make, since `(arg eats 2 meat)` would demand it of every eater.

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
  It descends the predicate hierarchy for `args-problem`'s reason and by riding the
  same reader: a conditional constraint on `parentOf` is a claim about every tuple of
  every predicate beneath it.

  **Behind an O(1) gate, unlike its two unconditional neighbours.**  `args-problem` and
  `genls-problem` run their declaration read unconditionally because `arg` is what a
  typed ontology is mostly made of, so the read pays for itself.  Nothing declares
  `interArg` yet, and this check runs on *every* assert — the read `assert` names its
  dominant per-fact cost — so a third retrieval that finds nothing is a tax on every write
  in every KB.  One `count-with-functor` says whether any such declaration is stored at
  all; zero means no scoped read can find one, so there is nothing to look for.

  **The constraint reading only.**  Under `*assertive-arg-types?*` the declaration
  derives the target's type once the trigger holds (`inter-arg-entailments`) and
  convicts nothing (`entailment-covers?`)."
  [_kb sentence _context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (and (symbol? pred)
               (not *assertive-arg-types?*)
               (kind-stored? decls 'interArg))
      (first
       (for [d       (in-content-order (decls 'interArg))
             :let  [b       (nth d 1)
                    n       (get b '?n)
                    t       (get b '?type)
                    m       (get b '?m)
                    u       (get b '?utype)
                    trigger (arg-at as n)
                    target  (arg-at as m)]
             :when (and trigger target
                        (checkable-term? trigger) (checkable-term? target)
                        (symbol? t) (symbol? u)
                        ;; the antecedent, established rather than merely unrefuted
                        (kb/isa-among? (types trigger) t)
                        (let [tm (types target)]
                          (and (kb/isa-among? tm 'thing)
                               (not (kb/isa-among? tm u)))))]
         {:type :inter-arg-type :sentence sentence :arg target :expected u :position m
          :trigger trigger :trigger-type t :trigger-position n
          :message (str "arg constraint: " target " must be a " u " (arg " m " of " pred
                        (via-clause (declared-of d) pred)
                        ", because arg " n " is a " t ")")})))))

(defn- genls-problem
  "First `(genlArg pred n type)` violation for a sentence, or nil.

  `genlArg` is `arg` one level up: it constrains the argument to be a **subtype**
  of the named type rather than an instance of it, which is what a type-level relation
  wants — `(genlArg partType 1 tangible)` says the first argument names a kind
  of physical object, where `(arg partOf 1 tangible)` says it names one.

  Which constraints apply is context-scoped exactly as `arg` is, and so is the
  subtype test itself: absence of a *visible* path to the constraint type is what
  convicts, the NAF reading judged from the writer's own vantage.  Which constraints
  apply also descends the predicate hierarchy exactly as `arg`'s do, by riding the
  same reader.

  **An application is typed by its function's `genlResult`**, never by its `result`:
  this position wants a kind, and `genlResult` is the declaration saying an application
  names one where `result` says it *is* one.  `convicting-result-type` has that
  argument, and keeps the two readings apart.

  Open-world has a floor here that `arg` does not have.  An argument outside the
  hierarchy is normally exempt, since the edges placing it may not have arrived yet —
  but an **individual** can never acquire them (`wff/genl-problems` refuses `genl` of
  one), so a type-level position holding one is convicted rather than excused.  The
  test is \"outside the hierarchy *and* individual\", not \"individual\", because a
  reified NAT is indistinguishable from an individual by spelling and is minted with real `genl` edges from
  its `genlResult` declarations — one that reaches `thing` is judged like any type.

  **A deliberate global/scoped split inside one `cond`.**  The first floor asks what
  the argument *is* (could it ever be a type?) and stays **global**: a reified NAT's
  minting edges land in `CxUniverse`, which the upper spindle's members sit above and
  cannot see, so a scoped floor would convict an imported reified NAT used from
  `CxMeasure` as \"an individual, so never a subtype\" — false.  The second
  floor is the **scoped** open-world excuse: an argument with no *visible* path
  into the hierarchy may simply have its edges out of sight, and a NAF check that
  convicted on invisible evidence would convict harder the less a context sees.
  Only an argument with visible evidence that reaches the wrong place is convicted, and
  only under the constraint reading: under `*assertive-arg-types?*` the declaration
  derives the `genl` edge (`constraint-entailments`) and the subtype test convicts nothing."
  [kb sentence context decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (symbol? pred)
      (first
       (for [d     (in-content-order (decls 'genlArg))
             :let  [b   (nth d 1)
                    n   (get b '?n)
                    t   (get b '?type)
                    arg (arg-at as n)
                    ;; the application arm — nil for every argument that is not one
                    r   (convicting-result-type kb nat/genl-result-types pred arg t context)
                    why (if r
                          (str (pr-str arg) " must be a subtype of " t " — "
                               (first arg) " results in a subtype of " r)
                          (when (and arg (checkable-term? arg) (symbol? t))
                            (cond
                              (not (tax/genl?-global tax arg 'thing))          ; global: the individual floor
                              (when (nm/individual? arg)
                                (str arg " is an individual, so it can never be a subtype of " t))

                              (not (tax/genl? tax arg 'thing context))  ; scoped: no visible evidence
                              nil                                       ; — open world excuses

                              ;; scoped: the writer's vantage, and the constraint reading
                              ;; only — the entailing one derives the edge instead
                              (and (not *assertive-arg-types?*) (not (tax/genl? tax arg t context)))
                              (str arg " must be a subtype of " t))))]
             :when why]
         {:type :arg-genl :sentence sentence :arg arg :expected t :position n
          :message (str "arg constraint: " why " (arg " n " of " pred
                        (via-clause (declared-of d) pred) ")")})))))

;; ---- the covering argument constraints -----------------------------------
;; `arg` and `genlArg` type one numbered position.  `args` / `argsGenl` type EVERY
;; accepted position, and `argAndRest` / `argAndRestGenl` every position from a start
;; onward — the tail of a variable-arity relation, where naming a largest finite `arg`
;; would make an unbounded relation look finite and leaving the later positions undeclared
;; would drop the contract silently.  Each covering form generalizes its singular twin and
;; reuses its per-argument conviction: `args` asks the instance question `arg` asks,
;; `argsGenl` the subtype question `genlArg` asks.
;;
;; **The walk is over the positions the sentence actually has, not a re-counted tail.**
;; every position the sentence has is walked, including one past a length its relation
;; is bound to: such a tuple is stored, and the settle places it as an arity nogood
;; (`vaelii.impl.decide`).  The covering declarations are read
;; through the same `decls` reader the singular forms use, so a super-predicate's covering
;; declaration binds a sub-predicate's tuples for `args-problem`'s reason.

(defn- covering-declared?
  "Is any covering declaration of one of the `:props` `kinds` marked in the taxonomy?
  A `:props` map lookup per kind, not a predicate-extent read — so a KB with no covering
  declaration adds nothing to the firing read budget, where a per-functor
  `stored-count-with-functor` gate would cost one predicate-extent read per assert for a
  feature the KB does not use.  Over-approximates like `inter-args-problem`'s index gate:
  the mark is global, so a covering constraint on any predicate runs the scoped check for
  every assert, and the scoped `decls` read decides whose tuples it actually binds."
  [kb kinds]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (some #(seq (tax/props tax %)) kinds))))

(defn- covering-triples
  "The covering declarations of the every-position kind `ek` and the tail kind `rk`,
  read through the shared `decls` reader and merged into `[start type kind match]`
  entries in content order — start 1 for `ek`, the declared start for `rk`.  A tail
  declaration whose start is not a positive integer is dropped here rather than convicting
  from an ill-formed position; its own `(arg <rk> 2 positive_integer)` refuses it at the
  entry point, so a stored one is a torn record, not a live constraint.  Sorting keys the
  refusal on what the KB says, exactly as `in-content-order` does for the singular forms."
  [decls ek rk]
  (nm/sort-by-content-key
   #(nm/print-key (:sentence (nth (nth % 3) 2))) compare
   (concat (for [m (decls ek)] [1 (get (nth m 1) '?type) ek m])
           (for [m     (decls rk)
                 :let  [b (nth m 1) s (get b '?start)]
                 :when (and (integer? s) (pos? s))]
             [s (get b '?type) rk m]))))

(defn- suffix-positions
  "The one-based positions from `start` to the last argument of the argument vector `as`
  — the walk every tail constraint makes, the covering forms and the homogeneity forms
  alike.  Bounded by the arguments the sentence has."
  [as start]
  (range start (inc (count as))))

(defn- covering-clause
  "How a covering refusal names the position it convicts: `args, position N` for an
  every-position form, `argAndRest from M, position N` for a tail form."
  [kind start pos]
  (if (#{'args 'argsGenl} kind)
    (str kind ", position " pos)
    (str kind " from " start ", position " pos)))

(defn- covering-args-problem
  "First `(args R T)` / `(argAndRest R n T)` violation for a sentence, or nil.  Types
  every admitted position (or every one from `n` onward) as an **instance** of `T`,
  reusing `args-problem`'s per-argument conviction — `convicting-result-type` for an
  application, `outside-declared-type?` for a symbol or value, and yielding the symbol arm
  to the same entailment under the toggle.  Conjunctive with a singular `(arg R n T)`:
  both are read, neither overrides.

  Behind the O(1) gate `inter-args-problem` is, and for the same reason: nothing declares
  a covering constraint yet and this runs on every assert."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred)
               (covering-declared? kb [:declares-args-isa :declares-arg-and-rest-isa]))
      (first
       (for [[start t kind decl] (covering-triples decls 'args 'argAndRest)
             pos   (suffix-positions as start)
             :let  [arg (arg-at as pos)
                    r   (convicting-result-type kb nat/result-types pred arg t context)]
             :when (and arg (or r (and (not (entailment-covers? arg))
                                       (outside-declared-type? tax types arg t context))))]
         {:type :arg-type :sentence sentence :arg arg :expected t :position pos
          :message (str "arg constraint: " (pr-str arg) " must be a " t
                        (when r (str " — " (first arg) " results in a " r))
                        " (" (covering-clause kind start pos) " of " pred
                        (via-clause (declared-of decl) pred) ")")})))))

(defn- covering-genls-problem
  "First `(argsGenl R T)` / `(argAndRestGenl R n T)` violation for a sentence, or nil.
  The subtype twin of `covering-args-problem`: every admitted position (or every one from
  `n` onward) must name a **subtype** of `T`, reusing `genls-problem`'s per-argument
  reading — `genlResult` for an application, and the global individual floor, the scoped
  open-world excuse and the scoped subtype test for a symbol.  Conjunctive with a singular
  `(genlArg R n T)`.

  **The individual floor is a global read (`tax/genl?-global`), for `genls-problem`'s
  reason (E17_ROSTER).**  The floor asks whether the argument could ever be a type at all;
  a reified NAT's minting `genl` edges land in `CxUniverse`, which a member of the upper
  spindle sits above and cannot see, so a scoped floor would convict an imported reified
  NAT used from a narrow context as \"an individual, so never a subtype\" — false.  The
  subtype test proper stays scoped, the writer's own vantage, and convicts only under the
  constraint reading, as `genls-problem`'s does."
  [kb sentence context decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred)
               (covering-declared? kb [:declares-args-genl :declares-arg-and-rest-genl]))
      (first
       (for [[start t kind decl] (covering-triples decls 'argsGenl 'argAndRestGenl)
             pos   (suffix-positions as start)
             :let  [arg (arg-at as pos)
                    r   (convicting-result-type kb nat/genl-result-types pred arg t context)
                    why (if r
                          (str (pr-str arg) " must be a subtype of " t " — "
                               (first arg) " results in a subtype of " r)
                          (when (and arg (checkable-term? arg) (symbol? t))
                            (cond
                              (not (tax/genl?-global tax arg 'thing))
                              (when (nm/individual? arg)
                                (str arg " is an individual, so it can never be a subtype of " t))

                              (not (tax/genl? tax arg 'thing context)) nil

                              (and (not *assertive-arg-types?*) (not (tax/genl? tax arg t context)))
                              (str arg " must be a subtype of " t))))]
             :when why]
         {:type :arg-genl :sentence sentence :arg arg :expected t :position pos
          :message (str "arg constraint: " why " (" (covering-clause kind start pos)
                        " of " pred (via-clause (declared-of decl) pred) ")")})))))

;; ---- the homogeneity constraints -----------------------------------------
;; `interArg` demands a type at one position once another position holds a type.
;; `interArgs` / `interArgAndRest` demand ONE type of a whole suffix — every position, or
;; every position from a start onward — once any argument in that suffix holds it.  The
;; type is the trigger and the target at once, and the reading of each side is
;; `inter-args-problem`'s: the trigger must be positively established, the target is
;; convicted by absence.  The walk is over the positions the sentence has, for the reason
;; the covering constraints give above.

(defn- homogeneity-declarations
  "The `interArgs` / `interArgAndRest` declarations binding a sentence's tuples, as
  `[start type via]` entries in content order — start 1 for `interArgs`, the declared
  start for `interArgAndRest` — with `via` the predicate the declaration is written of.

  **One entry per constraint, whichever spelling states it.**  CxCore's two forward rules
  derive `(interArgAndRest R 1 T)` from `(interArgs R T)` and `(interArgs R T)` from
  `(interArgAndRest R 1 T)`, so a KB that states either spelling holds both, and a KB
  without those rules holds the one it was told.  The entries are deduplicated on
  `[start type via]` and sorted on a key that spells each of them as `interArgAndRest`, so
  a sentence draws the same refusal whichever spelling arrived, and a stated declaration
  with its derived twin convicts once.  A start that is not a positive integer is dropped,
  as `covering-triples` drops one: `(arg interArgAndRest 2 positive_integer)` refuses it at
  the entry point, so a stored one is a torn record rather than a live constraint."
  [decls]
  (->> (concat (for [m (decls 'interArgs)]
                 [1 (get (nth m 1) '?type) (declared-of m)])
               (for [m     (decls 'interArgAndRest)
                     :let  [b (nth m 1) s (get b '?start)]
                     :when (and (integer? s) (pos? s))]
                 [s (get b '?type) (declared-of m)]))
       distinct
       (nm/sort-by-content-key (fn [[s t via]] (nm/print-key (list 'interArgAndRest via s t)))
                               compare)))

(defn- homogeneity-clause
  "How a homogeneity refusal names the declaration: `interArgs` for start 1, which is
  what both spellings state there, and `interArgAndRest from N` for a later start."
  [start]
  (if (= 1 start) "interArgs" (str "interArgAndRest from " start)))

(defn- inter-args-homogeneity-problem
  "First `(interArgs R T)` / `(interArgAndRest R n T)` violation for a sentence, or nil.

  Per declaration, one pass over the suffix: the first position whose argument is
  positively established as a `T` is the trigger, and the first position whose argument
  is in the hierarchy and does not reach `T` is the target.  A suffix with no trigger is
  unconstrained, so an application whose arguments all lie outside `T` passes, and so
  does one whose other arguments are unknown.  Positions below the start are never read.
  Positions are sentence content, so the first trigger and the first target are chosen
  by content and never by a handle.

  Both sides read `inter-args-problem`'s way, and each for its reason.  A **symbol**
  argument is typed by its memberships (`types`, the shared per-assert reader, so a
  position read as a trigger and as a target costs one retrieval).  A value or a compound
  is neither a trigger nor a target, which is the reading `inter-args-problem` gives
  both of its positions.

  The constraint reading only: under `*assertive-arg-types?*` the declaration derives
  `T` of every other suffix argument once a trigger holds (`homogeneity-entailments`)
  and convicts nothing.  Behind the taxonomy `:props` gate `covering-declared?` is, so a KB that declares no
  homogeneity constraint pays two map lookups per assert and no index read."
  [kb sentence _context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (and (symbol? pred)
               (not *assertive-arg-types?*)
               (covering-declared? kb [:declares-inter-args-isa
                                       :declares-inter-arg-and-rest-isa]))
      (let [holds? (fn [t p] (let [x (arg-at as p)]
                               (and (checkable-term? x)
                                    (kb/isa-among? (types x) t))))
            fails? (fn [t p] (let [x (arg-at as p)]
                               (and (checkable-term? x)
                                    (let [cs (types x)]
                                      (and (kb/isa-among? cs 'thing)
                                           (not (kb/isa-among? cs t)))))))]
        (first
         (for [[start t via] (homogeneity-declarations decls)
               :when (symbol? t)
               :let  [suffix (suffix-positions as start)
                      n      (first (filter #(holds? t %) suffix))]
               :when n
               :let  [m (first (filter #(fails? t %) suffix))]
               :when m
               :let  [target (arg-at as m)]]
           {:type :inter-arg-type :sentence sentence :arg target :expected t :position m
            :trigger (arg-at as n) :trigger-type t :trigger-position n
            :message (str "arg constraint: " target " must be a " t " ("
                          (homogeneity-clause start) ", position " m " of " pred
                          (via-clause via pred)
                          ", because position " n " is a " t ")")}))))))

(defn- args-quoted-problem
  "First `(quotedArg pred n type)` violation for a sentence, or nil.

  The **mention** twin of `args-problem`: where that types what an argument *denotes*,
  this types the argument *as a term* — what is decidable from the value itself
  (`value-kinds`), checked through genl against the declared syntactic type.
  `(quotedArg name_of_guy 1 string)` refuses
  `(name_of_guy 5)` because `5` is a `number`, not a `string`, and admits `(name_of_guy
  \"Bob\")`.  Closed about a decidable value — every leaf kind has a name
  (`syntactic-roots`), a keyword and a character included — and open-world about the one
  shape no kind answers for, a **compound**, which is exempt on the same floor
  `args-problem` gives an argument outside the hierarchy.

  **`value-kinds`, not `value-kind`, and the difference is the sign-refined
  integers.**  `syntactic-type?` admits any type below a syntactic root, so
  `positive_integer` — a part of CxCore's partitions of `integer` — is inside this
  check's domain and always was.  Judged by EDN kind alone the comparison ran the wrong
  way round, asking whether `integer` is below `positive_integer`, and refused every
  integer written in such a position (#55).  The shared reader answers the
  question the declaration actually asks, and the mention and denotation readings agree
  about a value for the reason they always have: a value denotes itself.

  Behind the same O(1) gate as `inter-args-problem`, and for the same reason: nothing
  declares `quotedArg` in a bare KB, and this runs on every assert, so a
  `count-with-functor` says whether any is stored before a scoped read looks."
  [kb sentence context _types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred)
               (kind-stored? decls 'quotedArg))
      (first
       (for [d     (in-content-order (decls 'quotedArg))
             :let  [b   (nth d 1)
                    n   (get b '?n)
                    t   (get b '?type)
                    arg (arg-at as n)
                    lit (value-kind arg)
                    ks  (value-kinds arg)]
             :when (and (some? arg) lit (symbol? t)
                        (not (contains? ks t))
                        (syntactic-type? tax t context)
                        (not-any? #(tax/genl? tax % t context) ks))]
         {:type :quoted-arg-type :sentence sentence :arg arg :expected t :position n
          ;; the value types when the refinement is what failed, the bare EDN kind
          ;; otherwise: "it is a integer" says nothing useful about -5 refused a
          ;; positive_integer, where the kind alone is the whole answer for "Bob"
          ;; refused a number
          :message (str "quoted-arg constraint: " arg " must be a " t " as a term — it is a "
                        (if (= ks #{lit}) (str lit) (str/join " / " (sort ks)))
                        " (arg " n " of " pred (via-clause (declared-of d) pred) ")")})))))

;; ---- the inputs of a function application ---------------------------------
;; The arms above read the declarations of the sentence's own relation, and an
;; application sitting in one of its positions is typed there by its function's
;; `result` — what the application *denotes*.  That says nothing about what is written
;; *inside* it: `(arg InputGapFn 1 integer)` constrains the input of every application
;; of `InputGapFn`, and `(observes (InputGapFn "x"))` violates it whatever the result
;; reading concludes.  So the argument arms run a second time, one level in, with the
;; function standing where the predicate stood.  Both readings run; neither replaces
;; the other.

(defn- mentioned-positions
  "The positions of the relation `decls` reads that a visible `quotedArg` declaration
  types — the positions holding a **mention** of the term written there rather than a
  use of it.  Through `decls` with no count gate of its own: the reader memoizes the
  kind, so `args-quoted-problem`'s read of it over the same relation is the one read."
  [decls]
  (into #{} (map #(get (nth % 1) '?n)) (decls 'quotedArg)))

(def ^:private formula-functors
  "The frames whose arguments are formulas rather than terms — a `(not (P …))` reaches the
  checks whole when the negation is genuine (`checked-sentence`), and its argument is a
  sentence about `P`, not an application of it."
  '#{not and or implies exceptWhen thereExists forAll ist unknown})

(defn- formula-head?
  "Does the compound `x`, written in an argument position, have a head the KB knows as a
  predicate — is it a `predication`, the other half of `non_atomic_expression`
  (CxCore), rather than a function applied to terms?  A formula written as an argument is
  a sentence about its predicate's tuples, which that predicate's declarations do not
  type from here.  A head the KB has not classified is read as a function: its
  declarations are what it has, and a head with none convicts nothing.

  A membership read, so `nested-input-problem` asks it only of an application something
  inside convicted: the common application convicts nothing, and asking first would put
  a read on every assert that carries a compound (`assert_cost_test`'s compound
  workload)."
  [types x]
  (kb/isa-among? (types (first x)) 'predicate))

(defn- nested-input-problem
  "The first violation of a function's own argument declarations by an input written
  inside one of `sentence`'s used arguments, at any depth, or nil.  The violation is the
  arm's own, so its `:sentence` is the innermost application whose input failed.

  **No derivation, and under `*assertive-arg-types?*` no conviction of a symbol.**  A
  declaration arriving derives over the facts already stored, which it finds by
  predicate, and no index finds the applications of a function inside stored facts, so a
  membership derived from a nested input would be drawn in one arrival order and not the
  other.  The arms read here therefore derive nothing, and under the entailing reading
  their symbol arms yield as they do at the top level (`entailment-covers?`): a nested
  symbol is not convicted on its memberships.  A value and an application are convicted
  as at the top level, and a function that declares nothing convicts nothing.

  **Terms, not formulas.**  A connective's argument, and a compound whose head is a known
  predicate, is a formula (`formula-head?`), and nothing found inside one convicts.

  **Mentions are not descended into.**  A position a `quotedArg` declaration types holds
  the term written there, not a use of it, so an application in it is syntax and its
  function's declarations about what its inputs denote do not reach it; the same holds
  for the argument of a quoting predicate (`nat/nat-quoting-predicates`) and of a
  `quoting_function`.  A quoting function's own declarations are still read over its
  application — only what it quotes is left alone.

  One declaration reader per application, built on reaching it, so a sentence with no
  compound argument reads nothing: `application-term?` over its arguments is the whole
  cost."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (nm/args sentence)]
    (when (and (symbol? pred)
               (not (contains? formula-functors pred))
               (some application-term? as)
               (not (contains? nat/nat-quoting-predicates pred))
               (not (tax/quoting-function? (reasoning/taxonomy kb) pred)))
      (let [mentioned (mentioned-positions decls)]
        (first
         (for [[n x] (map-indexed (fn [i a] [(inc i) a]) as)
               :when (and (application-term? x)
                          (not (contains? formula-functors (first x)))
                          (not (contains? mentioned n)))
               :let  [ds (declaration-reader kb (first x) context (decls ::counts nil))
                      p  (or (args-problem kb x context types ds)
                             (inter-args-problem kb x context types ds)
                             (inter-args-homogeneity-problem kb x context types ds)
                             (genls-problem kb x context ds)
                             (covering-args-problem kb x context types ds)
                             (covering-genls-problem kb x context ds)
                             (args-quoted-problem kb x context types ds)
                             (nested-input-problem kb x context types ds))]
               :when (and p (not (formula-head? types x)))]
           p))))))

(defn- application-input-problem
  "First violation of a function's argument declarations inside `sentence`'s arguments,
  or nil — `nested-input-problem` reported against the sentence being checked.

  The arm's `:type`, `:arg`, `:expected` and `:position` are kept, so a caller reads a
  nested `:arg-type` exactly as it reads a top-level one and `conviction-watch` watches
  the convicted input.  `:position` is the position in the application's function, and
  `:application` names that application; the message says where it sits."
  [kb sentence context types decls]
  (when-let [p (nested-input-problem kb sentence context types decls)]
    (assoc p
           :sentence sentence
           :application (:sentence p)
           :message (str (:message p) ", inside " (pr-str (:sentence p))))))

;; ---- the argument constraints, checked against each other ----------------

(def ^:private arg-constraint-kinds
  "The two **unconditional** argument constraints, each mapped to the other: the value is
  the counterpart a declaration is checked against, and membership is what
  `declaration-problem` reads to recognize one.

  `interArg` is not here and has its own arm.  It is written at a different arity and
  names two positions, so it fits neither the pairing nor the `(= 3 (nm/arity …))` test —
  forcing it in would put that difference inside every reader of this map."
  '{arg genlArg, genlArg arg})

(defn- tabled-arity
  "The arity the `(arity P n)` **table** gives `pred` from `context`, or nil.

  Read from the **taxonomy cache** (`tax/declared-arity`), which `(arity P n)`
  maintains the way `(transitive P)` maintains its prop: this runs on every assertion,
  and answering it from the index meant a retrieval and a filtered walk of every sentex
  holding `pred` as its first argument — 16 candidates per assertion on an OpenCyc
  load, 13.3M over it, nearly all finding nothing.  A declaration is not something to
  re-derive per write.  One map read, which is why every arity question asks this one
  first and the membership spelling second."
  [kb pred context]
  (let [n (tax/declared-arity (reasoning/taxonomy kb) pred context)]
    (when (and (integer? n) (pos? n)) n)))

(defn- membered-arity
  "The arity `pred`'s own exact-class membership gives it, or nil — the second
  spelling, read off the predicate's types (`types`, the shared per-assert reader), so it
  costs the retrieval `arg` already needs for its arguments rather than one of its
  own.  A retrieval where `tabled-arity` is a map read, which is the whole of why the two
  are separate functions rather than one `or`: a caller asking about several predicates
  wants the cheap half of the question asked of all of them first.

  `first` over the roster is exact wherever CxCore is loaded: `(disjoint unary binary)`
  and its two peers separate the relation-wide three and the six kind specializations
  inherit that separation through their `genl` edges, so a relation reaches one number
  however many of the nine spellings its closure holds."
  [types pred]
  (let [cs (types pred)]
    (first (for [[t n] tax/exact-arity-classes
                 :when (kb/isa-among? cs t)]
             n))))

(defn- variable-arity?
  "Is `pred` declared `variable_arity`, from the vantage `types` reads with?

  The escape the whole arity family turns on, spelled once so every arm reads it the same
  way: off the predicate's own memberships, so a mark reached through a `genl` edge
  between collections releases exactly as a directly asserted one does."
  [types pred]
  (kb/isa-among? (types pred) 'variable_arity))

(defn- own-arity
  "The arity `pred` **itself** is declared with, visible from `context`, or nil when the
  KB has never said.  Both spellings, the table first because it is a map read."
  [kb pred context types]
  (or (tabled-arity kb pred context)
      (membered-arity types pred)))

(defn- inherited-arity
  "The arity `pred`'s **super-predicates** bind it to, as `[n via]`, or nil: the one
  length every super-predicate visible from `context` that declares one agrees on, both
  spellings read (`own-arity`), with `via` the content-first of them.  Nil when they
  disagree, and when any super is `variable_arity`.  One membership read per super,
  memoized per `types` reader."
  [kb pred context types]
  (let [tax    (reasoning/taxonomy kb)
        supers (sort (disj (tax/genls tax pred context) pred))
        pairs  (into [] (keep (fn [p] (when-let [n (own-arity kb p context types)] [p n])))
                     supers)]
    (when (and (seq pairs)
               (= 1 (count (into #{} (map second) pairs)))
               (not-any? #(variable-arity? types %) supers))
      (let [[p n] (nth pairs 0)] [n p]))))

(defn- declared-arity
  "The arity binding `pred` in `context`, as `[n via]`, or nil when nothing does — its
  own declaration where it has one (`via` is `pred`), else the one its super-predicates
  agree on (`inherited-arity`)."
  [kb pred context types]
  (if-let [n (own-arity kb pred context types)]
    [n pred]
    (inherited-arity kb pred context types)))

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
  `res/matches-visible` fans over the whole `genlCx` ancestor set, so one sentence stated in
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
  already convicts under the type it actually states.

  With `all?`, every match is named, the exact ones first, for a caller whose
  entailing matches convict under no type of their own (`negation-handles`)."
  ([matches target] (handle-namings matches target false))
  ([matches target all?]
   (let [sen   (fn [m] (:sentence (nth m 2)))
         ;; `nm/print-key`, and built once per match rather than once per comparison: the
         ;; second arm names ONE handle out of a `res/matches-visible` answer *set*, so a
         ;; key an ambient `*print-length*` collapsed would decide the refusal on
         ;; enumeration order — which is the handle order this key exists to keep out
         order (fn [m] (nm/print-key [(sen m) (:context (nth m 2))]))
         named (fn [ms] (map first (nm/sort-by-content-key order compare ms)))
         exact (seq (filter #(= target (sen %)) matches))]
     (cond
       all?   (concat (named exact) (named (remove #(= target (sen %)) matches)))
       exact  (named exact)
       :else  (take 1 (named matches))))))

(defn- arg-position-problem
  "A declaration constraining a position `pred` does not have — `(arg parentOf 5
  animal)` where `parentOf` is declared binary.  The constraint would never fire, so it
  reads as enforced while enforcing nothing.

  Shared by every declaration kind, because `interArg` names **two** positions and both
  are the same mistake.  Open-world: a predicate whose arity the KB has never stated is
  unconstrained — and the arity read is `declared-arity`'s, so a predicate that inherits
  its length from a super-predicate has the position it lacks refused on the same
  grounds.

  **`variable_arity` releases it**, as it releases every other arm of the family.  Such a
  predicate reads a tuple of any length from its declared arity upward, so a position past
  that length is one its tuples really do reach and a constraint on it fires — `arg-at`
  bounds-checks per sentence, so the declaration is silent on the short tuples and
  enforced on the long ones.  Refusing it while the same KB admits the very facts it would
  type is the one reading no arrival order makes coherent.

  The release is read off **`pred`'s own memberships and nothing else**, which is
  `variable-arity?`'s definition and is the complete question here.  An inherited length
  reaches this arm only through `inherited-arity`, which already declines to bind when any
  super carries the mark — so a `via` that is not `pred` is a predicate the release was
  asked of and refused, and asking it again would answer a settled question twice.  Asking
  it of `via` *instead* is the reading that loses the case: the mark sits on the sub, which
  is exactly where `inherited-arity` never looks.

  `:via` names the predicate the length was read off.  **Both routes reach
  here** — a predicate held to a number it declared, and one held to a super's — so
  `arity-binding-clause` says which: `parentOf` *is declared with* 2 arguments, `fatherOf`
  *takes* 2 arguments *through* `parentOf`.  Wording the second as a declaration would be
  false of a predicate nobody declared, and would send an author looking for one that does
  not exist."
  [kb f pred n context types]
  (when (and (integer? n) (pos? n))
    (when-let [[declared via] (declared-arity kb pred context types)]
      ;; the position the predicate does not have is the one the shared decision reads as
      ;; certainly-not-admitted — the same function `provers/AdmitsArgnumProver` answers, so
      ;; a position this arm refuses is one `(admitsArgnum pred n)` does not prove
      (when (false? (provers/admits-position? (variable-arity? types pred) declared n))
        {:type :arg-position :predicate pred
         :position n :arity declared :via via
         :message (str f " constrains argument " n " of " pred ", which "
                       (arity-binding-clause pred via declared))}))))

(defn- declaration-problem
  "A problem with an `arg` / `genlArg` / `interArg` **declaration** itself, rather
  than with a sentence it constrains — two ways one can contradict what the KB already
  says about the predicate it is about:

  * a position the predicate does not have (`arg-position-problem`).  `interArg` names
    two, and each is checked.
  * a constraint disagreeing with the predicate's own `relation_kind` — `genlArg` on
    an `instance_relation_predicate`, or `arg` on a `type_relation_predicate`.
    `interArg` reads its types as memberships, so it takes `arg`'s side of that.

  **Both constraints on one position is not a problem**, and this is the case worth
  naming because the opposite reads plausible: one asks the argument to be an instance
  of a type, the other to be a subtype of a type, and a *type* is routinely both.
  `(arg P 2 collection)` with `(genlArg P 2 animal)` says the slot holds a kind of
  animal, and `dog` satisfies it — an instance of `collection`, a subtype of `animal`.
  The two checks are independent and each is open-world on its own, so declaring both
  narrows the slot rather than emptying it.

  `arg1` / `arg2` / `arg3` — the binary projections of `arg` — are held to the same
  two arms at their projected position, so both spellings of one declaration refuse
  identically.  Without this the binary spelling would evade the arms entirely: the
  sentence itself carries no position for the generic machinery to check, the bridge
  rule's ternary conclusion is convicted on the *derivation* path where a conviction
  is dropped and recorded rather than thrown, and the author is left holding a
  believed `arg1`/`arg2`/`arg3` fact whose real declaration the engine rejected — silently inert,
  the exact trap CxCore's `quotedArg` note names.

  Open-world throughout: each arm needs a declaration to contradict, so a predicate
  the KB has said nothing about is unconstrained."
  [kb sentence context types]
  (let [[f pred n _ m] sentence]
    (cond
      (and ('{arg1 1, arg2 2, arg3 3} f) (= 2 (nm/arity sentence)) (symbol? pred))
      (let [pos ('{arg1 1, arg2 2, arg3 3} f)]
        (or (some-> (arg-position-problem kb f pred pos context types)
                    (assoc :sentence sentence))
            (when (seq (res/matches-visible kb (list 'type_relation_predicate pred) context))
              {:type :arg-constraint-kind :sentence sentence :predicate pred
               :message (str pred " is declared type_relation_predicate, so its"
                             " arguments are constrained with genlArg, not " f
                             " (the binary projection of arg)")})))

      (and (= 'interArg f) (= 5 (nm/arity sentence)) (symbol? pred))
      (some-> (or (arg-position-problem kb f pred n context types)
                  (arg-position-problem kb f pred m context types)
                  (when (seq (res/matches-visible kb (list 'type_relation_predicate pred) context))
                    {:type :arg-constraint-kind :predicate pred
                     :message (str pred " is declared type_relation_predicate, so its"
                                   " arguments are constrained with genlArg, not " f)}))
              (assoc :sentence sentence))

      (and (contains? arg-constraint-kinds f) (= 3 (nm/arity sentence))
           (symbol? pred) (integer? n) (pos? n))
      (let [other (arg-constraint-kinds f)]
        (or (some-> (arg-position-problem kb f pred n context types)
                    (assoc :sentence sentence))
            (let [clash (if (= f 'arg) 'type_relation_predicate 'instance_relation_predicate)]
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
;; opposing handle, the entry point stores the sentence, and `settle` decides the nogood
;; from its members' classes.  See docs/nmtms.md.
;;
;; The argument constraints do not join them: `(parentOf Fred Mary)` violating `(arg
;; parentOf 1 animal)` is convicted by the *absence* of a path from Fred's types to
;; `animal`, an open-world negation-as-failure judgement with no second member to weigh,
;; so those stay refusals.  `arity` is not checked here: a tuple whose length breaks its
;; predicate's binding is a nogood the settle places (`vaelii.impl.decide`).

(def arbitrable-kinds
  "The definitional violations that name **other believed sentexes** rather than a
  malformed sentence, so `settle` can arbitrate them like any other contradiction."
  #{:disjoint :functional :asymmetric :anti-transitive :cover})

(defn opposing-handles
  "The believed sentexes a violation is *against*, as a vector of handles — empty when
  it names none.

  Two spellings, one reading.  The pairwise kinds name a single opposing sentex in
  `:opposing-handle` and always did; `:anti-transitive` convicts a two-step chain and the
  direct step **together**, so it names both other members in `:opposing-handles` (the
  nogood is a triple, not a pair — docs/nmtms.md).  Every consumer that weighs a
  violation against what it opposes reads this rather than either key, so a kind naming
  two is weighed exactly as one naming one is, and the published `:opposing-handle` on
  the three older kinds is left where callers already read it."
  [v]
  (cond
    (seq (:opposing-handles v)) (filterv integer? (:opposing-handles v))
    (integer? (:opposing-handle v)) [(:opposing-handle v)]
    :else []))

(defn arbitrable?
  "Can `settle` arbitrate this violation instead of the caller refusing it — does it
  name opposing believed sentexes to form a nogood with?"
  [v]
  (boolean (and v (contains? arbitrable-kinds (:type v))
                (seq (opposing-handles v)))))

(defn refuses-assert?
  "Does violation `v` refuse its sentence at the write entry point?  True unless `v` is
  arbitrable (`arbitrable?`): a clash naming the other believed members of its nogood is
  stored, and `settle` decides it and reports it when every member is `:monotonic`.  A
  malformed sentence, an argument conviction and a clash naming no stored member refuse
  (docs/nmtms.md, \"What a refusal may rest on\")."
  [v]
  (boolean (and v (not (arbitrable? v)))))

(def ^:dynamic *refuse-clashes?*
  "Does the write entry point refuse an arbitrable clash as well?  False by default, where
  `refuses-assert?` decides.  `vaelii.core/try-assert` binds it true, and
  `constraint-checks` then refuses every violation the sentence or one of its
  argument-type mints forms (docs/api.md, \"Refusing a clash\")."
  false)

(defn- entry-refuses?
  "Does violation `v` refuse its sentence at the write entry point under
  `*refuse-clashes?*`?"
  [v]
  (if *refuse-clashes?* (some? v) (refuses-assert? v)))

(defn- membership-handles-led
  "`membership-handles`' small side: lead from `x`'s own argument-1 postings (a handful)
  and test each up via `genl?` (t'' ⊑ t ⟺ t'' ∈ specs(t), see `kb/memberships`),
  rather than `matches-visible` walking `specs(t)` *down* — unbounded for a broad t (with
  t = `thing`, every type in the KB), and the closure walk that dominates a cold rebuild's
  clash pass.  The candidate set, the filters (believed, context-visible, `except`-hidden,
  retired) and `handle-namings` are exactly what `matches-visible` would feed here — it is
  `matches-hierarchical` over `(t x)` then `without-excepted`/`without-retired`, and the
  pred-hierarchy filter `t'' ∈ specs(t)` is the same set as `t'' ⊑ t` — so the
  answer set is identical, retrieved from the small side.  Split out so `res/*lead-side*`
  can force the `matches-visible` reference the two oracles compare it against.

  **The exact postings first.**  `handle-namings` names the matches saying `(t x)` itself
  whenever one survives the filters, and the entailing ones only when none does, so a
  surviving exact match settles the answer and no other posting is walked up.  The
  filters drop matches one at a time, so the exact ones that survive them alone are the
  ones that survive them among the rest.  `disjoint-problems` asks this of the types a
  term is asserted to hold, where an exact posting is the rule, so the exact ones are
  read first by their own trie path under every context, and the term's postings, every
  fact holding it at argument 1, only when none survives."
  [kb t x context]
  (let [recs   (:records kb)
        tms    (reasoning/tms kb)
        tax    (reasoning/taxonomy kb)
        target (list t x)
        up     (when-not (sx/variable? context) (tax/context-up tax context))
        vis?   (if up #(contains? up %) (constantly true))
        cand   (fn [h]
                 (when-let [s (p/get-sentex recs h)]
                   (when (and (jtms/in? tms (:id s)) (vis? (:context s)))
                     (let [sen (:sentence s)]
                       (when (and (= 1 (nm/arity sen))
                                  (= x (first (nm/args sen)))
                                  (not (sx/exceptWhen-meta? sen)))
                         s)))))
        kept   #(->> % (exc/without-excepted kb context) (res/without-retired kb context))
        said   (keep #(when (= target (:sentence %)) [(:id %) nil %]))
        ;; the exact memberships by their own path, then by the postings when none
        ;; survives, which is when the postings are read anyway
        by-path (when (and (symbol? x) (not (sx/variable? x)))
                  (kept (sequence (comp (distinct) (keep cand) said)
                                  (reads/as-stored-at-path (:index kb)
                                                           (sx/path (sx/sentex target '?c))))))
        cands  (delay (into [] (keep cand) (reads/as-stored-with-arg (:index kb) 1 x)))
        exact  (if (seq by-path) by-path (kept (sequence said @cands)))]
    (handle-namings
     (if (seq exact)
       exact
       (kept (keep (fn [s]
                     (let [t'' (nm/functor (:sentence s))]
                       ;; a walk memoized per pass, not the closure: every type `x`
                       ;; holds is tested, and a closure read builds the supertype
                       ;; closure of each; a plain walk repeats per instance sharing t''
                       (when (or (= t'' t) (tax/genl?-per-pass tax t'' t context))
                         [(:id s) nil s])))
                   @cands)))
     target)))

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
  forms its own pair.

  Two ways to reach the same set, gated by `res/*lead-side*`: `:scoped` runs the
  `matches-visible` reference (specs(t) walked down), anything else leads from the term's
  own postings (`membership-handles-led`)."
  [kb t x context]
  (if (= :scoped res/*lead-side*)
    (handle-namings (res/matches-visible kb (list t x) context) (list t x))
    (membership-handles-led kb t x context)))

(defn- disjoint-problems
  "A type membership (T X) where X already holds a type the taxonomy proves
  disjoint from T, as a violation map, or nil.  **Fully scoped to the asserting
  context**: the memberships read, the disjoint declaration, and the genl edges
  the disjointness closes under must all be visible from `context` — a
  context is only ever refused on grounds it can see.

  X is any term, not only an individual, so a `disjoint_metatype` over predicate
  types separates the predicates it is declared of — one predicate cannot be both
  an `instance_relation_predicate` and a `type_relation_predicate`.

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
      ;; one question, asked of each type the term holds: `t` and the asserting context
      ;; are fixed across the loop, and they are what most of the answer is a function
      ;; of.  A `t` no declaration reaches reads none of the term's types.
      (when-let [disjoint? (and (checkable-term? x)
                                (tax/separation-test (reasoning/taxonomy kb) t context))]
        (for [t' (:types (types x))
              :when (disjoint? t')
              h    (membership-handles kb t' x context)]
          {:type :disjoint :sentence sentence :types [t t']
           :opposing-handle h
           :message (str "disjointness violated: " x " cannot be both "
                         t " and " t')})))))

(defn- negation-handles
  "The handles of the believed sentexes visible from `context` that entail `(not (t x))`,
  each a denial of `t` or of a supertype of it, in content order (`handle-namings`).
  `membership-handles` names one entailing match, and `negation-handles` names every one:
  a denial of a supertype rules out the part `t` and convicts under no part of its own,
  so each such denial is a member of its own `covering` nogood, and
  `membership/term-nogoods` forms one nogood per choice of denials."
  [kb t x context]
  (let [target (list 'not (list t x))]
    (handle-namings (res/matches-visible kb target context) target true)))

(defn- cover-refutations
  "A cover every one of whose parts is denied of a term the whole holds, as violation
  maps.

  `(covering W A B)` says that an instance of `W` is an `A` or a `B`. With `(W X)`
  believed and `(not (A X))` and `(not (B X))` believed beside it, the declaration itself
  is refuted — a contradiction among believed sentexes, which is a nogood rather than a
  malformed sentence, so `settle` weighs the membership and the negations and defeats
  the weakest, exactly as it weighs the two memberships of a disjointness clash.

  Asked of the membership `(W X)` or of a negation `(not (A X))`: either one can
  complete the refutation.  `settle` re-asks it of the membership (`reads-clash?`) for a
  nogood a reader found from the term (`membership/term-nogoods`).

  `:opposing-handles` names every other member of the nogood, for the reason
  `:anti-transitive` names both steps of its chain: the contradiction is not a pair, and
  arbitration that could see only one side of it would defeat the one sentex it could
  name whatever the rest were worth.  The declaration is not a member (the comment on
  the map says why).

  Scoped to the asserting context throughout, as `disjoint-problems` is: the declaration,
  the membership and each negation must be visible from `context`, since a context is
  refused only on grounds it can see."
  [kb sentence context]
  (let [tax  (reasoning/taxonomy kb)
        neg? (sx/negation? sentence)
        lit  (if neg? (second sentence) sentence)]
    (when (and (sequential? lit) (= 1 (nm/arity lit)) (symbol? (nm/functor lit)))
      (let [;; `part` is the part this sentence rules out, or nil when the sentence is
            ;; the whole's own membership.  The two shapes are the two arrival orders an
            ;; entry point sees: the last negation completing a refutation, and the
            ;; membership arriving under negations already stored.
            part (when neg? (nm/functor lit))
            x    (first (nm/args lit))]
        (when (checkable-term? x)
          (let [decls (if neg?
                        (mapv (fn [[whole parts _]] [whole parts])
                              (tax/covers-naming-visible tax part context))
                        (tax/covers-over tax (nm/functor lit) context))]
            (for [[whole parts] decls
                  :when (or (nil? part)
                            (provers/conjunction-derivable? kb [(list whole x)] {} context))
                  ;; every part *but this one*: on the refusal path the sentence under
                  ;; assertion is not stored yet and holds by assumption, and on the
                  ;; settle path it is stored and would answer here anyway.
                  ;; A part the membership `(t x)` puts `x` in (`t` or a supertype of
                  ;; it) is denied only by a stored negation.  A closed extent's
                  ;; negation as failure is withdrawn when a member arrives, and the
                  ;; membership under assertion is that member, so reading the denial
                  ;; before it is stored would make the arrival order decide.
                  :when (every? (fn [p]
                                  (or (= p part)
                                      (if (and (nil? part)
                                               (or (= p (nm/functor lit))
                                                   (tax/genl? tax (nm/functor lit) p context)))
                                        (seq (negation-handles kb p x context))
                                        (provers/conjunction-derivable?
                                         kb [(list 'not (list p x))] {} context))))
                                parts)]
              {:type :cover :sentence sentence :types (vec (cons whole parts))
               ;; The membership and the other negations, and **not** the declaration
               ;; the conviction is read through — `disjoint`'s rule, for `disjoint`'s
               ;; reason: a nogood holding the declaration would, on defeating it, read a
               ;; taxonomy without the cover on the next pass, find no violation, revive
               ;; the declaration and oscillate.  The evidence is what a refuted cover
               ;; convicts; the cover is the standing claim it is convicted against.
               :opposing-handles
               (into (if part (vec (membership-handles kb whole x context)) [])
                     (mapcat #(when-not (= % part) (negation-handles kb % x context))
                             parts))
               :message (str "coverage violated: " x " is a " whole
                             ", which every part of the declared cover "
                             (str/join ", " parts) " is now denied of")})))))))

(defn- cover-refutation
  "The first refuted cover, for the refusal paths."
  [kb sentence context]
  (first (cover-refutations kb sentence context)))

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
  no merge can make them one, so a numeric functional clash is a nogood the settle
  decides.  A symbol clash merges only when both members are `:monotonic`
  (docs/reference.md, decision 6)."
  [x y]
  (and (symbol? x) (symbol? y) (not (sx/variable? x)) (not (sx/variable? y))))

(defn- first-per-slot
  "`[handle value via]` triples with the content-first `via` kept per `[handle value]`.

  Several marked predicates in one chain each probe their own slot, and a super's probe
  fans down over its specs — so one stored filler comes back under every mark above it.
  That is one clash, not three: the pair is `[this sentence, that filler]` whichever
  declaration convicts it.  Lazy, because `functional-problem` takes the first and an
  eager dedup would walk a whole functional extent to answer whether one exists.

  The key is `[handle value]` by default and a caller may widen it.  `functional-clashes`
  does, to `[handle value position]`: with `functionalInArg` a predicate may be
  constrained at more than one position at once, and two positions filled by one stored
  sentex are two different slots with two different incoming fillers, so a key that
  ignored the position would drop one of them.  For the arity-2 marks the position is
  always 2 and the widened key dedups identically, which is what keeps today's behaviour
  byte-for-byte."
  ([triples] (first-per-slot triples (fn [t] [(nth t 0) (nth t 1)])))
  ([triples key-fn] (nm/distinct-by key-fn triples)))

(defn functional-clashes
  "The believed `[handle value via]` triples that already fill a functional slot for the
  same first argument with something other than `b` — the clash a `(functional P)`
  declaration turns into either a rejection or an equality.

  `via` is the predicate carrying the mark this clash is against, which is the
  sentence's own where it carries one and a **super-predicate** where the mark descends
  (`tax/props-over`).  Two `fatherOf` mothers for one child are two `parentOf` values,
  so `(functional parentOf)` convicts them; reading the mark off the exact functor made
  that bypassable through the sub-predicate entry point while the *slot probe* already fanned
  down the hierarchy, so which spelling arrived second decided whether the clash
  existed.

  The slot is probed **at the marked predicate**: `(parentOf a ?v)` finds a filler
  written either way through the matcher's fan, where `(fatherOf a ?v)` would miss one
  written at the general spelling.  Empty when nothing above the sentence's predicate is
  marked — one map read on a KB that declares nothing functional, which is every bulk
  load.

  **The quadruple carries the position**, because `functionalInArg` moved it.  A
  `(functional P)` mark always constrains argument 2, so the arity-2 path reads its
  incoming filler as `(second (nm/args sentence))` and nothing had to say so; a
  `(functionalInArg P n)` constrains argument `n`, and which argument the clash is about
  is no longer a constant the caller can assume.  Every consumer reads `b` off the
  quadruple rather than off the sentence.

  Both marks are consulted and their clashes unioned, so a predicate carrying
  `(functional P)` **and** `(functionalInArg P 2)` yields one deduped clash resting on
  both declarations — which is the behaviour `derive-functional-equalities` already
  wants of two `(functional P)` sentexes in different contexts, applied one level up."
  [kb sentence context]
  (let [pred (nm/functor sentence)
        tax  (reasoning/taxonomy kb)
        args (vec (nm/args sentence))
        k    (count args)
        ;; `(q a1 … ?fv … ak)` — the sentence's own arguments with position `n` opened
        ;; up.  At arity 2 with n=2 this is `(q a ?fv)`, the probe the arity-2 path built
        ;; by hand, so the generalization reproduces it rather than replacing it.
        probe (fn [q n] (apply list q (assoc args (dec n) '?fv)))
        ;; `[via position]` pairs constraining this sentence.  The arity-2 mark speaks
        ;; only for arity-2 sentences, exactly as before.  `functionalInArg` speaks
        ;; wherever the declared position is a position this sentence actually has — a
        ;; declaration past the end matches no tuple, which is `arity`'s open-worldness
        ;; and the reason `wff` does not refuse it either.
        marks (into (if (= 2 k)
                      (into #{} (map (fn [q] [q 2]))
                            (tax/props-over tax :functional pred context))
                      #{})
                    (filter (fn [[_ n]] (<= n k)))
                    (tax/functional-in-arg-over tax pred context))]
    (when (seq marks)
      (first-per-slot
       (for [[q n]  (sort marks)
             :let   [b (nth args (dec n))]
             [h bnd] (res/matches-visible kb (probe q n) context)
             :let    [v (get bnd '?fv)]
             :when   (and v (not= v b))]
         [h v q n])
       (fn [t] [(nth t 0) (nth t 1) (nth t 3)])))))

(defn functional-filler
  "The incoming filler a clash quadruple is about — argument `n` of `sentence`.

  The one reader for it, where three call sites would otherwise each spell
  `(second (nm/args sentence))`, so the arg-2 assumption has exactly one place to live
  and it is this function."
  [sentence [_ _ _ n]]
  (nth (vec (nm/args sentence)) (dec n)))

(defn functional-declaration-supporters
  "The handles of every declaration supporting a functional constraint on `via` at
  position `n` — the `(functional via)` sentexes when `n` is 2, and the
  `(functionalInArg via n)` sentexes always, unioned.

  Both genuinely support the merge, so both belong in its antecedents: retracting one
  leaves it standing on the other, which is the rule
  `a-merge-rests-on-every-functional-declaration-not-on-one-of-them` pins for two
  `(functional P)` sentexes and holds for the same reason across the two spellings."
  [tax via n]
  (into (if (= 2 n) (tax/prop-supporters tax :functional via) #{})
        (tax/functional-in-arg-supporters tax via n)))

(defn- functional-problems
  "A (P a b) where P is functional and `a` already has a value for P that no
  equality could reconcile with `b` (visible from `context`), as a violation map,
  or nil.

  A clash between two **symbols** whose members are both `:monotonic` is not an error:
  `(functional motherOf)` plus two known-true spellings of Tom's mother is where
  co-reference shows up, and the KB *derives* `(equals V1 V2)` from it (see
  `special/derive-functional-equalities`).  Everything else — two numbers, two strings,
  a compound — is a nogood, because no merge can make two numbers one thing.  See
  docs/equality.md.

  Every clash, not the first, for the reason `disjoint-problems` gives: a slot filled
  with three irreconcilable values forms three pairs, and which of them is reported may
  not depend on the order the extent came back in.

  The message names the predicate the mark is on, which is the sentence's own unless the
  declaration descended — the slot that is already filled is that predicate's.  It names
  the **position** too once the constraint is not at argument 2, because with
  `functionalInArg` the determinant is every other argument and reporting only the first
  would describe a slot the reader does not have.

  A symbol clash is left out: whether it merges or forms a nogood is read from the
  members' classes, which a reader does (`vaelii.impl.decide`, docs/reference.md,
  decision 6)."
  [kb sentence context]
  (for [[h v via n :as clash] (functional-clashes kb sentence context)
        :let [b (functional-filler sentence clash)]
        :when (not (mergeable-values? v b))]
    {:type :functional :sentence sentence :existing v :new b :opposing-handle h
     :pred via :position n
     :message (if (= 2 n)
                (str "functional violation: " via " of "
                     (first (nm/args sentence)) " is already " v ", not " b)
                (str "functional violation: argument " n " of " via " under "
                     (pr-str (vec (keep-indexed (fn [i a] (when (not= i (dec n)) a))
                                                (nm/args sentence))))
                     " is already " v ", not " b))}))

(defn- functional-problem
  "The first functional clash, for the refusal paths."
  [kb sentence context]
  (first (functional-problems kb sentence context)))

(defn- inherited-opposing
  "`c`, a `:for` claim `inherit/surviving` read for `converse`, as an opposing claim.  A
  claim stated at another tuple reaches `converse` by preservation, and carries the
  reading's handles as `::via` and as `:class` the weakest defeat class of the claim and
  those handles, the reading `discovery/preserving-nogoods` weighs.  With no reading, `c`
  carries no `::via`, so `arbitrable-violations` keeps the pair."
  [kb converse c context]
  (if-let [via (when (not= (:tuple c) (vec (nm/args converse)))
                 (some-> (inherit/claim-reading kb converse c context) vec))]
    (assoc c ::via via
           :class (reduce strength/min (:class c)
                          (map #(or (jtms/defeat-class (reasoning/tms kb) %) :default)
                               via)))
    c))

(defn- asymmetry-problems
  "Every `(asymmetric P)` violation a sentence commits in `context`.

  `(asymmetric largerThan)` says `(P a b)` and `(P b a)` cannot both hold, so a claim
  whose **converse** is known-true is a contradiction rather than an addition.  The
  converse counts whether it was stated directly or reached by argument-position
  preservation — `(largerThan dog cat)` reaches `(largerThan cat maine_coon)` and every
  other pair below it, and a strict claim is exactly as binding there as where it was
  written (`vaelii.impl.inherit`).

  A `:default` generality is something a more specific statement is entitled to
  override: there the inheritance is undercut and never fires, so no clash reaches here.
  A claim reached by preservation opposes at the weakest class of the claim and its
  reading, and names the reading's handles (`inherited-opposing`, docs/inherit.md).

  The violation is the pair `settle` arbitrates: the weaker member loses, a tie at
  `:default` is a dilemma in `(contradictions kb)`, and a tie at `:monotonic` is a hard
  clash in `(conflicts kb)`.

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
  discovery weighs all of them, deduped on the handle, since preservation can reach one
  stored claim by several routes.

  That is why the converse is read **twice**.  `inherit/surviving` answers what is
  *inherited* — one claim per tuple, the strongest — which is the right answer to whether
  the converse is licensed, and drops the duplicates on purpose
  (`inherit/strongest-per-tuple`).  The duplicates are exactly what a pair needs, so the
  sentexes literally stating the converse are read beside it and merged on the handle.
  Nothing is resurrected by that: a claim at the goal's own tuple is the most specific
  there is, so `undercut?` never displaced one.

  **The mark is read up the predicate hierarchy** (`tax/props-over`) where the converse
  probe already fanned *down* it, and the asymmetry between those two directions is what
  the descension closes.  `(asymmetric parentOf)` with `(genl fatherOf parentOf)`
  convicted `(parentOf b a)` against a stored `(fatherOf a b)` — `matches-visible` fans
  the converse over `parentOf`'s specs — and admitted the same pair written the other way
  round, because `fatherOf` carries no mark of its own.  Which spelling arrived second
  decided whether the pair existed.

  The converse is probed **at the marked predicate**, not at the sentence's own: it is
  `(parentOf b a)` that `(asymmetric parentOf)` forbids beside `(parentOf a b)`, and
  probing `(fatherOf b a)` would miss a converse stated at the general spelling while
  probing the general one finds both through the fan.  Several supers may carry the mark;
  each contributes its own converse, and the results merge on the handle exactly as the
  two reads of one converse do.

  **A sentence is not its own opposing claim.**  For a self tuple `(P a a)` the converse
  *is* the sentence, so once one is stored it answers its own probe: asserting `(P a a)`
  a second time convicts it against the copy the first assert left, and content the KB
  already believes refuses rather than deduping to the handle it already has.  Asymmetry
  does not hand you irreflexivity here — `CxCore.txt` says a self tuple is admitted, and
  `docs/taxonomy.md` and `docs/inherit.md` say it twice more — so admitting it once and
  refusing it forever after is neither reading.

  **Sentence and context both**, which is what makes it self-identity rather than a rule
  about self tuples: `(P a a)` in one context and `(P a a)` in another are two claims and
  a real pair — each is the other's converse across the context boundary, and
  `a-self-tuple-in-two-contexts-orders-on-the-context` is the case that reads them.  What
  is excluded is the sentence meeting *itself*, which is a comparison on the canonical
  sentence since the checks run before this one has a handle.  For `a` ≠ `b` the converse
  canonicalizes to a different sentence anyway, and a predicate for which it did not
  would be symmetric rather than asymmetric.

  **The context that decides self is the sentence's own — `home` — and not the asker.**
  The two are the same at the entry point and differ wherever `settle` asks a stored sentex's
  question from a *vantage* that sees more than its own context (`reads-clash?`).  Key
  self on the asker instead and the twin **stored in the vantage** is thrown away as
  though the candidate were it: `(P a a)` written in a general context and again in one
  that sees it is a real pair, and whether it is reported turns on which of the two is
  written last — the specific one arriving second convicts from its own context and finds
  its partner, the general one arriving second is asked from the specific vantage and
  discards it.  That is order-dependence in what the KB believes, which
  `clash_oracle_test`'s streams measure and `docs/nmtms.md` forbids.

  Ground binary sentences only; an open or n-ary one has no converse to speak of."
  ([kb sentence context] (asymmetry-problems kb sentence context context))
  ([kb sentence context home]
   (let [pred (nm/functor sentence)
         args (vec (nm/args sentence))]
     (when (and (symbol? pred) (= 2 (count args))
                (every? sx/ground-term? args)
                ;; no predicate carries the mark on nearly every KB: one roster read
                ;; then, and none of what follows is built
                (seq (tax/props (reasoning/taxonomy kb) :asymmetric)))
       (let [marked   (sort (tax/props-over (reasoning/taxonomy kb) :asymmetric pred context))
             ;; read once the mark is there to convict against, so an unmarked predicate
             ;; pays no canonicalization for it
             self     (when (seq marked) (:sentence (res/kb-sentex kb sentence context)))
             claims   (for [q marked
                            :let [converse (list q (second args) (first args))
                                  ;; compared against the *canonical* spelling: the matcher
                                  ;; probes through `kb-sentex`, so a comparison
                                  ;; predicate's converse is stored folded (`greaterThan B
                                  ;; A` as `lessThan A B`) and the raw form would match no
                                  ;; record — leaving `stated` empty and the duplicate
                                  ;; opposing sentexes this second read exists to supply
                                  ;; unsupplied
                                  stored-c (:sentence (res/kb-sentex kb converse context))
                                  stated   (for [m   (res/matches-visible kb converse context)
                                                 :let [sxr (nth m 2) h (first m)]
                                                 :when (= stored-c (:sentence sxr))]
                                             {:polarity :for :handle h
                                              :sentence (:sentence sxr)
                                              :context (:context sxr)
                                              :class (or (jtms/defeat-class (reasoning/tms kb) h)
                                                         :default)})]
                            o (concat (keep #(when (= :for (:polarity %))
                                               (inherited-opposing kb converse % context))
                                            (inherit/surviving kb converse context))
                                      stated)
                            :when (not (and (= self (:sentence o))
                                            (= home (:context o))))]
                        (assoc o ::mark q ::converse converse))
             opposing (->> claims
                           ;; one `nm/print-key` + two `str` in the key — built once per
                           ;; claim, not per comparison; the `[rank …]` tuple orders under
                           ;; `compare`.  Printed through `print-key` because `claims` is
                           ;; a `for` over `res/matches-visible`, an answer *set*, and
                           ;; `asymmetry-problem` takes the first: an elided sentence would
                           ;; decide a refusal on which claim the retrieval yielded first
                           (nm/sort-by-content-key (juxt #(- (strength/rank-of (:class %)))
                                                         #(str (:context %))
                                                         #(nm/print-key (:sentence %))
                                                         #(str (::mark %)))
                                                   compare)
                           (reduce (fn [acc o]
                                     (if (some #(= (:handle %) (:handle o)) acc)
                                       acc
                                       (conj acc o)))
                                   []))]
         (for [o opposing
               :let [q (::mark o) converse (::converse o)]]
           (cond-> {:type :asymmetric :sentence sentence :pred q
                    :opposing (:sentence o) :opposing-handle (:handle o)
                    :message (str "asymmetric: " q " cannot hold both ways, and "
                                  (pr-str (:sentence o))
                                  (if (= :monotonic (:class o)) " is known true" " is believed")
                                  (when (not= (:sentence o) converse)
                                    (str " (which reaches " (pr-str converse)
                                         " by argument preservation)")))}
             (::via o) (assoc :opposing-handles (into [(:handle o)] (::via o))
                              :via (::via o)))))))))

(defn- asymmetry-problem
  "The strongest `(asymmetric P)` violation, for the refusal paths."
  [kb sentence context]
  (first (asymmetry-problems kb sentence context)))

(defn- chain-steps
  "The believed steps matching `pattern` from `context`, as `[handle sentex binding]`
  triples — `binding` being what `var` bound.

  One `matches-visible` probe, so the predicate's **spec closure** is fanned exactly as
  it is everywhere else a mark descends: a probe at `parentOf` reads a `fatherOf` step,
  and a step written at the general spelling is read by a probe at it.  Belief-filtered
  by the matcher, so a defeated step is no step."
  [kb pattern context var]
  (for [[h b sx] (res/matches-visible kb pattern context)]
    [h sx (get b var)]))

(defn- lead-from-source?
  "For the closing role, is `(q a ?m)` the smaller end to enumerate than `(q ?m b)`?

  Both ends enumerate the **same** set of midpoints — `{m : (q a m) ∧ (q m b)}` — so this
  decides only which side is walked and which is probed per candidate, never the answer.
  The two argument roots are read for their cardinality alone: they span every predicate
  and either polarity, so they bound the walk rather than describing it.  A non-symbol
  has no root and cannot be led from."
  [kb a b]
  (let [idx  (:index kb)
        wide Long/MAX_VALUE
        out  (if (symbol? a) (reads/stored-count-with-arg idx 1 a) wide)
        in   (if (symbol? b) (reads/stored-count-with-arg idx 2 b) wide)]
    (<= out in)))

(defn- chain-triples
  "The forbidden triples `{(q a c), (q a m), (q m c)}` the tuple `(q a b)` is a member of,
  as `[first-step second-step closing]` in **role** order, each element a stored sentex or
  `::self` for the tuple being checked.

  Three roles, and all three are asked, because the settle's discovery walks the sentexes
  a settle *moved* and forms the nogood from whichever member it holds: a triple only two
  of whose members could convict it would be found or missed according to which one
  arrived last (`clash_oracle_test`, \"conviction has to be symmetric\").  The tuple is

  * the **closing** step, over each midpoint `m` with `(q a m)` and `(q m b)` believed;
  * the **first** step, over each `c` with `(q b c)` and the closing `(q a c)` believed;
  * the **second** step, over each `z` with `(q z a)` and the closing `(q z b)` believed.

  The closing role leads from whichever argument root is smaller (`lead-from-source?`)
  and probes the far leg bound; the other two roles have one bound end each and no choice
  to make.  A step reachable **only** by argument preservation is not enumerated — see
  the docstring of `antitransitivity-problems`."
  [kb q a b context]
  (concat
   (if (lead-from-source? kb a b)
     (for [[_ _ m :as s1] (chain-steps kb (list q a '?m) context '?m)
           s2             (chain-steps kb (list q m b) context nil)]
       [s1 s2 ::self])
     (for [[_ _ m :as s2] (chain-steps kb (list q '?m b) context '?m)
           s1             (chain-steps kb (list q a m) context nil)]
       [s1 s2 ::self]))
   (for [[_ _ c :as s2] (chain-steps kb (list q b '?c) context '?c)
         cl             (chain-steps kb (list q a c) context nil)]
     [::self s2 cl])
   (for [[_ _ z :as s1] (chain-steps kb (list q '?z a) context '?z)
         cl             (chain-steps kb (list q z b) context nil)]
     [s1 ::self cl])))

(defn- antitransitivity-problems
  "Every `(anti_transitive P)` violation a sentence commits in `context`.

  `(anti_transitive parentOf)` says a two-step chain forbids the direct step: believing
  `(P a m)` and `(P m c)` makes `(P a c)` contradictory, the dual of `transitive` and the
  reason no predicate is declared both (`(disjoint transitive anti_transitive)`).  So the
  conviction names **two** other believed sentexes rather than one, and the violation
  carries `:opposing-handles` where the pairwise kinds carry `:opposing-handle` —
  `settle` weighs the three together as one nogood (docs/nmtms.md).

  The triple is decided as any nogood is: at equal `:default` class it is a dilemma in
  `(contradictions kb)`, three claims none of which the engine picks between, and at
  equal `:monotonic` class a hard clash in `(conflicts kb)`.

  **The mark is read up the predicate hierarchy** (`tax/props-over`) and the steps are
  probed **at the marked predicate**, exactly as `asymmetry-problems` reads its converse:
  `(anti_transitive parentOf)` with `(genl fatherOf parentOf)` convicts a `fatherOf` chain,
  and a chain written half at each spelling is one chain.  Empty when nothing at or above
  the sentence's predicate is marked — one map read on a KB that declares none, which is
  every bulk load.

  **A sentence is not its own step**, on the rule `asymmetry-problems` states: a stored
  copy of the very claim being checked (same canonical sentence, same `home` context) is
  excluded, so re-asserting a fact does not convict it against itself.  `home` is the
  sentence's own context and not the asker's, for the reason that docstring records at
  length: a twin stored in the *vantage* a stored sentex is asked from is a partner and
  not a self.  What that leaves
  is real and is kept: a triple that collapses to two distinct sentexes — `(P a b)` beside
  `(P b b)` — is a two-member nogood weighed like any pair, and a self tuple `(P a a)`,
  whose whole triple is itself, names no other sentex at all and so convicts nothing.
  `anti_transitive` does not hand you `irreflexive` any more than `asymmetric` does
  (docs/taxonomy.md); a KB that wants the self tuple refused declares the mark that
  refuses it.

  **A step reached only by argument preservation is not enumerated.**
  `asymmetry-problems` reads `inherit/surviving` beside the stored converse; here that
  would make conviction one-sided — preservation reads a goal's arguments upwards, so the
  specific claim asks about the general one and never the reverse (docs/nmtms.md, \"Where
  conviction is one-sided\") — and a triple only one of whose members convicts is a triple
  the incremental discovery finds or misses by arrival order.  A stated absence, not an
  oversight: the spec fan above is what the mark's descension needs, and it is symmetric.

  **Every** violation, not the first, for the reason `disjoint-problems` gives: a hub term
  chains several ways, and which triple is reported may not depend on the order the
  postings came back in.  Deduped on the pair of opposing handles, so one triple reached
  under two marks above the predicate, or from two roles, is one violation — the
  content-first mark kept, as `first-per-slot` keeps its `via`.  Ordered weakest-opposing
  first, so the refusal path (which takes the first) decides against the chain that most
  nearly refuses, and then by content, so nothing rests on iteration order.

  Ground binary sentences only; an open or n-ary one is no step of a chain."
  ([kb sentence context] (antitransitivity-problems kb sentence context context))
  ([kb sentence context home]
   (let [pred (nm/functor sentence)
         args (vec (nm/args sentence))]
     (when (and (symbol? pred) (= 2 (count args))
                (every? sx/ground-term? args)
                ;; no predicate carries the mark on nearly every KB: one roster read
                ;; then, and none of what follows is built
                (seq (tax/props (reasoning/taxonomy kb) :anti-transitive)))
       (let [tms    (reasoning/tms kb)
             [a b]  args
             marked (sort (tax/props-over (reasoning/taxonomy kb) :anti-transitive pred context))
             ;; read once the mark is there to convict against, so an unmarked predicate
             ;; pays no canonicalization for it
             self   (when (seq marked) (:sentence (res/kb-sentex kb sentence context)))
             self?  (fn [s] (and (= self (:sentence s)) (= home (:context s))))
             ;; the triple as sentences, in role order, with the checked sentence in its
             ;; own place — what the message reads and what orders one violation against
             ;; another
             said   (fn [s] (if (= ::self s) self (:sentence (second s))))
             found  (for [q     marked
                          steps (chain-triples kb q a b context)
                          :let  [others (remove #(or (= ::self %) (self? (second %))) steps)]
                          ;; every member is this very claim (a self tuple's whole
                          ;; triple), so there is no second sentex to weigh
                          :when (seq others)
                          :let  [hs    (mapv first others)
                                 chain (mapv said steps)]]
                      {:type :anti-transitive :sentence sentence :pred q
                       :chain chain
                       :opposing-handles hs
                       :weakest (reduce strength/min (map #(jtms/defeat-class tms %) hs))
                       :message (str "anti_transitive: " q " chains " (pr-str (first chain))
                                     " and " (pr-str (second chain))
                                     ", so the direct step " (pr-str (nth chain 2))
                                     " cannot hold too")})]
         (->> found
              ;; `:chain` is three whole sentences — the longest printed value keyed on
              ;; anywhere here, and the first an ambient `*print-length*` truncates — so
              ;; it is printed through `nm/print-key`.  `antitransitivity-problem` takes
              ;; the first of these, and `found` is a `for` over `res/matches-visible`
              (nm/sort-by-content-key
               (juxt #(- (strength/rank-of (:weakest %)))
                     #(nm/print-key (:chain %))
                     #(str (:pred %)))
               compare)
              (reduce (fn [[acc seen] v]
                        (let [k (set (:opposing-handles v))]
                          (if (contains? seen k) [acc seen] [(conj acc v) (conj seen k)])))
                      [[] #{}])
              first
              (mapv #(dissoc % :weakest))))))))

(defn- antitransitivity-problem
  "The violation whose chain most nearly refuses, for the refusal paths."
  [kb sentence context]
  (first (antitransitivity-problems kb sentence context)))

(defn antisymmetric-converses
  "The believed `[handle via]` pairs whose sentence is the converse of `(P a b)` under an
  `(anti_symmetric P)` mark — the facts `(P b a)` that, with the sentence, force
  `(equals a b)`.  Deduped on the converse's handle; `via` is the marked predicate the
  conviction reads through (the sentence's own where it carries the mark, a
  super-predicate where the mark descends), which the equality derivation names in its
  justification.

  The converse is probed **at the marked predicate** and its mark read **up** the
  hierarchy, exactly as `asymmetry-problems` and `functional-clashes` do and for the same
  reason: `(anti_symmetric parentOf)` with `(genl fatherOf parentOf)` must convict a
  `fatherOf` pair whichever spelling arrives last, so reading the mark off the exact
  functor would leave the pair found or missed by arrival order.

  `matches-visible` over the ground converse is the whole probe: it fans **down** to the
  sub-predicate spellings (so `(atOrAbove Alice Bob)` finds a stored `(atOrAboveStrict
  Alice Bob)`) and folds a comparison predicate's converse internally, so no exact-sentence
  filter is wanted here — one would drop exactly the descended pair the up-read exists to
  catch.  Ground binary sentences only."
  [kb sentence context]
  (let [pred (nm/functor sentence)
        args (vec (nm/args sentence))]
    (when (and (symbol? pred) (= 2 (count args))
               (every? sx/ground-term? args))
      (let [[a b]   args
            triples (for [q (sort (tax/props-over (reasoning/taxonomy kb) :anti-symmetric pred context))
                          m (res/matches-visible kb (list q b a) context)]
                      [(first m) nil q])]
        (map (fn [[h _ via]] [h via]) (first-per-slot triples))))))

(defn- matches-pattern-problem
  "A `matchesPattern` literal whose pattern argument is a ground string the regex engine
  cannot compile, or nil.  `EvaluableProver` reads the pattern as a value at query time, so
  an author who mistypes it would otherwise get a goal that silently never matches; this
  reports the compile failure at the assert entry point instead.  Only a ground string
  pattern is judged — a variable pattern is open, like every other undecided argument, and a
  non-string pattern is the `quotedArg` arm's refusal, not this one."
  [sentence]
  (when (= 'matchesPattern (nm/functor sentence))
    (let [pattern (second (nm/args sentence))]
      (when (string? pattern)
        (try (java.util.regex.Pattern/compile pattern) nil
             (catch java.util.regex.PatternSyntaxException e
               {:type :bad-pattern :sentence sentence :pattern pattern
                :message (str "matchesPattern was given a pattern that does not compile: "
                              (.getMessage e))}))))))

(defn- checked-sentence
  "The body the definitional checks see: the double-negation-eliminated positive body,
  so a `(not (not (dog Muffet)))` is still arg/disjoint/functional-checked and a genuine
  negation is not.  A literal whose functor is `symmetric` or declares a commuting group
  is read in the argument order `res/kb-sentex` stores it in, so each argument meets the
  declarations at the position it is stored at, whichever spelling was written."
  [kb sentence]
  (let [body (or (sx/positive-body sentence) sentence)
        f    (when (sequential? body) (first body))
        tax  (when (symbol? f) (reasoning/taxonomy kb))]
    (if (and tax (or (tax/has-prop? tax :symmetric f) (seq (tax/commuting-groups tax f))))
      (:sentence (res/kb-sentex kb body 'default))
      body)))

(defn- constraint-problem
  "The first definitional violation for `chk` in `context` that `keep?` accepts, as a
  value, or nil.  The checks are stated once, here, and every path reads them:
  `constraint-checks` (assert) throws the first that `refuses-assert?`,
  `constraint-admission` (derivation) drops a firing for it, and `constraint-violation`
  reports the first of any kind (`some?`).  The arms run in order and stop at the first
  accepted, so an arbitrable clash an early arm finds does not hide a refusal a later arm
  finds.

  `types` is the shared membership reader (`kb/membership-reader`).  The arms that ask
  what types a term holds ask about the same few terms — the sentence's arguments and
  its predicate — and between them ask several times each: `arg` reads an argument's
  twice per constraint, and for a unary sentence the disjointness arm wants the very
  memberships `arg` just read."
  [kb chk context types decls keep?]
  (some (fn [arm] (let [p (arm)] (when (and p (keep? p)) p)))
        [#(matches-pattern-problem chk)
         #(args-problem kb chk context types decls)
         #(inter-args-problem kb chk context types decls)
         #(inter-args-homogeneity-problem kb chk context types decls)
         #(genls-problem kb chk context decls)
         #(covering-args-problem kb chk context types decls)
         #(covering-genls-problem kb chk context decls)
         #(args-quoted-problem kb chk context types decls)
         #(application-input-problem kb chk context types decls)
         #(declaration-problem kb chk context types)
         #(disjoint-problem kb chk context types)
         #(cover-refutation kb chk context)
         #(asymmetry-problem kb chk context)
         #(functional-problem kb chk context)
         #(antitransitivity-problem kb chk context)]))

;; ---- what the argument constraints *entail* ------------------------------
;; `args-problem` and `genls-problem` read `arg` / `genlArg` as constraints to test,
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

(defn edge-support
  "The handles of the `genl` edge supporters a declaration written of `via` travels down
  to reach `pred` — empty when `via` **is** `pred`, a declaration that rests on no edge.

  Anything **derived** through a super-predicate's declaration rests on three things
  rather than two: the fact, the declaration, and the subsumption that makes the fact
  one of the declaration's tuples.  Naming only the first two would leave the derivation
  standing after the edge was retracted — a derived record supported by content that no
  longer entails it, which is the exact failure justifying a derivation at all is meant
  to prevent.  Both descending derivations read it: the argument-type entailment below,
  and the equality a descended `(functional P)` mints
  (`special/derive-functional-equalities`).

  One supporter per edge on a shortest **visible** path (`tax/reach-support`), which is
  the witness rule everything else depending on a reachability takes: a justification is
  a conjunction of supports, not a proof that no other route exists, so when the named
  route goes what rested on it goes and is re-derived from whatever survives."
  [kb pred via context]
  (if (= pred via)
    []
    (mapv first (tax/reach-support (reasoning/taxonomy kb) :genl pred via context))))

(defn- entailment-support
  "What a derivation through the declaration match `d` rests on besides the sentence it
  is drawn over: the declaration, the `genl` edges it descends through to `pred`
  (`edge-support`), and the `genlCx` edges through which `context` sees it
  (`visibility-support`)."
  [kb pred d context]
  (into [(nth d 0)]
        (concat (edge-support kb pred (declared-of d) context)
                (visibility-support kb (nth d 0) context))))

(defn- arg-entailments
  "The entailments one argument-constraint kind draws over `sentence`'s arguments in
  `context` — a seq of `{:assert <sentence> :because [decl-handle edge-handle …]
  :position n :kind arg|genlArg}`.

  `eligible?` is the kind's reading of \"this argument is the sort of term the
  entailment can be about\", and it is a property of the **term** alone, never of what
  the KB has learned about it so far — which is what keeps the answer a function of
  content.  It doubles as the early-out: no eligible argument means no declaration can
  say anything, and the declaration query is never run.

  `:because` leads with the declaration and carries the `genl` edges it descended
  through and the `genlCx` edges it is seen through (`entailment-support`), so the
  entailment holds only while the subsumption and the sighting that licensed it do.  A
  declaration the context inherits derives as one written there does."
  [kb sentence context decls kind eligible? mint]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred) (some eligible? as))
      (for [d     (decls kind)
            :let  [b   (nth d 1)
                   n   (get b '?n)
                   t   (get b '?type)
                   arg (arg-at as n)]
            :when (and arg (eligible? arg)
                       (mintable-type? tax t)
                       ;; A `genlArg` mints `(genl arg t)`, which is not-well-formed when
                       ;; `arg` is `t`.  A reflexive `genl` edge is never well-formed for
                       ;; any `t`, and `arg`/`t` are literal terms, so this is a structural
                       ;; exclusion like `mintable-type?` above rather than a redundancy
                       ;; narrowing.
                       (not (and (= kind 'genlArg) (= arg t))))]
        {:assert  (mint arg t)
         :because (entailment-support kb pred d context)
         :position n :kind kind}))))

(defn- inter-arg-entailments
  "The entailments `interArg` draws over `sentence`'s arguments in `context`.

  Exactly as strong as `arg`'s, and drawn under the same condition the check convicts
  on: the trigger argument must be established as a `T`, so the entailment is what the
  declaration says once its antecedent holds.  A dormant constraint entails nothing,
  which is the same asymmetry `inter-args-problem` reads.  One entailment per membership
  establishing the trigger, each naming it under `:trigger` and in `:because`
  (`trigger-supports`); `special/triggered-mints` draws them when the membership
  arrives after the fact.

  Behind the same O(1) gate `inter-args-problem` is, and for the same reason."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred) (some checkable-term? as)
               (pos? (reads/stored-count-with-functor (:index kb) 'interArg)))
      (for [d     (decls 'interArg)
            :let  [b       (nth d 1)
                   n       (get b '?n)
                   t       (get b '?type)
                   m       (get b '?m)
                   u       (get b '?utype)
                   trigger (arg-at as n)
                   target  (arg-at as m)]
            :when (and trigger target
                       (checkable-term? trigger) (checkable-term? target)
                       (symbol? t)
                       (kb/isa-among? (types trigger) t)
                       (mintable-type? tax u))
            :let  [because (entailment-support kb pred d context)]
            sup   (trigger-supports kb trigger t context)]
        {:assert  (list u target)
         :because (into because sup)
         :trigger (first sup)
         :position m :kind 'interArg}))))

(defn- covering-entailments
  "The entailments the covering declarations draw over `sentence`'s arguments in
  `context`: `(args R T)` and `(argAndRest R n T)` derive `(T x)` of every symbol
  argument from their start onward, and `(argsGenl R T)` and `(argAndRestGenl R n T)`
  derive `(genl x T)`, as `arg` and `genlArg` derive them of one position.  An
  individual is not given an edge and `(genl T T)` is not drawn, for `arg-entailments`'
  reasons.  Behind the `:props` gate `covering-args-problem` stands behind."
  [kb sentence context decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)
        draw (fn [ek rk props eligible? mint]
               (when (covering-declared? kb props)
                 (for [[start t kind d] (covering-triples decls ek rk)
                       :when (mintable-type? tax t)
                       pos   (suffix-positions as start)
                       :let  [x (arg-at as pos)]
                       :when (and (checkable-term? x) (eligible? x t))]
                   {:assert (mint x t) :because (entailment-support kb pred d context)
                    :position pos :kind kind})))]
    (when (and (symbol? pred) (some checkable-term? as))
      (concat (draw 'args 'argAndRest [:declares-args-isa :declares-arg-and-rest-isa]
                    (fn [_ _] true) (fn [x t] (list t x)))
              (draw 'argsGenl 'argAndRestGenl [:declares-args-genl :declares-arg-and-rest-genl]
                    (fn [x t] (and (not (nm/individual? x)) (not= x t)))
                    (fn [x t] (list 'genl x t)))))))

(defn- homogeneity-entailments
  "The entailments `(interArgs R T)` and `(interArgAndRest R n T)` draw over `sentence`'s
  arguments in `context`: every suffix argument established as a `T` is a trigger, and
  derives `T` of every other symbol argument in the suffix, once per membership
  establishing it (`trigger-supports`, named under `:trigger`).  A suffix with no trigger
  draws nothing, which is `inter-arg-entailments`' reading of the trigger.  Each
  spelling's declaration supports its own derivation, so a stated declaration and its
  CxCore-derived twin both justify the one record."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred) (some checkable-term? as)
               (covering-declared? kb [:declares-inter-args-isa
                                       :declares-inter-arg-and-rest-isa]))
      (for [kind  '[interArgs interArgAndRest]
            d     (decls kind)
            :let  [b     (nth d 1)
                   start (if (= kind 'interArgs) 1 (get b '?start))
                   t     (get b '?type)]
            :when (and (integer? start) (pos? start) (mintable-type? tax t))
            :let  [suffix  (suffix-positions as start)
                   because (delay (entailment-support kb pred d context))]
            n     suffix
            :let  [tx (arg-at as n)]
            :when (and (checkable-term? tx) (kb/isa-among? (types tx) t))
            sup   (trigger-supports kb tx t context)
            pos   suffix
            :let  [x (arg-at as pos)]
            :when (and (checkable-term? x) (not= x tx))]
        {:assert (list t x) :because (into @because sup) :trigger (first sup)
         :position pos :kind kind}))))

(defn- stored-spelling
  "`sentence` as the store keeps it in `context`: a `(symmetric P)` literal's arguments
  sorted, a commuting component arranged (`res/kb-sentex`), anything else as written.

  The entailments a fact meets its declarations with read their positions off this on
  every path, so the assert and derivation paths, which reach them before the sentex
  exists, draw the justifications a later declaration or a reload draws.  An unmarked
  predicate pays two taxonomy reads and no canonicalization."
  [kb sentence context]
  (let [tax (reasoning/taxonomy kb)
        f   (nm/functor sentence)]
    (if (and (symbol? f)
             (or (tax/has-prop? tax :symmetric f) (seq (tax/commuting-groups tax f))))
      (:sentence (res/kb-sentex kb sentence context))
      sentence)))

(defn constraint-entailments
  "What `sentence`'s visible argument declarations entail about its arguments in
  `context` — a vec of `{:assert <sentence> :because [decl-handle edge-handle …]
  :position n :kind <the declaring functor>}`, empty when they entail nothing.  Every
  entailing kind is read: `arg`, `genlArg`, `interArg`, the covering forms and the
  homogeneity forms, from a declaration written in `context` or inherited by it.

  `(arg parentOf 1 animal)` over `(parentOf Fred Mary)` entails `(animal Fred)`;
  `(genlArg partType 1 tangible)` over `(partType wheel_kind axle_kind)` entails
  `(genl wheel_kind tangible)`; `(interArg eats 1 carnivore 2 meat)` over
  `(eats Rex Chunk)` entails `(meat Chunk)` — but only once `Rex` is known to be a
  carnivore, which is the condition the declaration is *about*.  An **individual** in an
  `genlArg` position is convicted by `genls-problem` rather than given an edge, so it is
  ineligible here — said at the point it matters rather than relying on the check having
  run first.

  One entry per applicable declaration, with no narrowing for redundancy: see the
  commentary above for why every candidate narrowing would make belief depend on
  arrival order.  Deduplication is the materializer's, where it is keyed on content.

  Drawn over the spelling the store keeps (`stored-spelling`), not the one written: a
  `(symmetric P)` fact names each argument at both positions, and which declaration a
  mint rests on must not turn on how the fact was spelled.

  **Reads only.**  The caller decides whether to store, and the caller is
  `special/deduce-arg-types`, which mints each one as a derived sentex justified by the
  triggering fact and `:because` — so retracting any of them takes the type back."
  ([kb sentence context]
   (constraint-entailments kb sentence context
                           (kb/membership-reader kb context)
                           (declaration-reader kb (nm/functor sentence) context)))
  ([kb sentence context types decls]
   (when *assertive-arg-types?*
     (let [sentence (stored-spelling kb sentence context)]
       (vec (concat (arg-entailments kb sentence context decls 'arg
                                     checkable-term?
                                     (fn [arg t] (list t arg)))
                    (arg-entailments kb sentence context decls 'genlArg
                                     #(and (checkable-term? %) (not (nm/individual? %)))
                                     (fn [arg t] (list 'genl arg t)))
                    (inter-arg-entailments kb sentence context types decls)
                    (covering-entailments kb sentence context decls)
                    (homogeneity-entailments kb sentence context types decls)))))))

(defn declaration-entailments
  "`constraint-entailments` narrowed to the declaration stored at `dh`: the entries whose
  `:because` leads with `dh`, drawn from that declaration's match alone.  Every arm draws
  one entry per match, so the other declarations on the predicate are not read, and their
  types are not asked `mintable-type?` once per fact of a sweep over `dh`'s extent."
  [kb sentence context dh]
  (let [kind  (nm/functor (:sentence (p/get-sentex (:records kb) dh)))
        decls (declaration-reader kb (nm/functor sentence) context)]
    (constraint-entailments kb sentence context (kb/membership-reader kb context)
                            (fn
                              ([k] (if (= k kind) (filterv #(= dh (nth % 0)) (decls k)) []))
                              ([op functor] (decls op functor))))))

(def ^:dynamic *prune-subsumed-mints?*
  "Does a minted type give way to a more specific one the KB believes?  With this on,
  `(animal Fred)` minted off `(parentOf Fred Mary)` is withheld while `(dog Fred)` is
  believed and comes back when it goes, which takes about a tenth of the records out of a
  shipped load and changes no answer.  On by default (docs/argtypes.md).

  `binding` it is the ordinary way in, and `VAELII_PRUNE_SUBSUMED_MINTS=0` sets the root
  value off — the parity run that says pruning removes records rather than answers."
  (config/prune-subsumed-mints?))

(defn- subsuming-membership
  "The handle of a believed `(T2 x)` that makes a minted `(t x)` in `context`
  redundant, or nil — `T2` a **strict** subtype of `t` through the edges `context`
  sees, stated where `context` can read it.

  The candidate predicates come from the slot roster (`as-stored-predicates-at-arg`,
  one read), so a term claimed under three types costs three subsumption tests rather
  than a walk of `t`'s whole spec subtree, which on a shipped taxonomy is thousands of
  types with no fact between them.

  Belief at `context`, not storage: a `(dog Fred)` `context` takes OUT licenses nothing,
  so the mint it would have made redundant stands.  The visibility test is `sees?` in the direction a read
  takes — a membership stated below `context` is invisible there and subsumes nothing."
  [kb t x context]
  (let [tax (reasoning/taxonomy kb)]
    (first
     (for [p    (reads/as-stored-predicates-at-arg (:index kb) 1 x)
           :when (and (symbol? p) (not= p t) (tax/genl? tax p t context))
           h    (reads/as-stored-with-args (:index kb) p {1 x})
           :let [sx (p/get-sentex (:records kb) h)]
           :when (and sx (= (list p x) (:sentence sx))
                      (tax/sees? tax context (:context sx))
                      (res/believed-at? kb h context))]
       h))))

(defn- subsuming-edge
  "The handle of a believed `(genl x S)` that makes a minted `(genl x t)` in `context`
  redundant, or nil — `S` a strict subtype of `t` reaching it through the edges
  `context` sees, so `x` reaches `t` over a route of two edges or more.

  Reachability is what a redundant edge does not change: removing every edge of a
  directed acyclic graph that has another route leaves the same closure, which is why
  dropping them all at once is stable rather than a cascade that eats the route it was
  reading.  The taxonomy refuses a `genl` cycle (`edge-stratification-violation`), so the
  acyclicity the argument rests on is the store's invariant rather than an assumption."
  [kb x t context]
  (let [tax (reasoning/taxonomy kb)]
    (first
     (for [h    (reads/as-stored-with-args (:index kb) 'genl {1 x})
           :let [sx (p/get-sentex (:records kb) h)
                 s  (when sx (nth (:sentence sx) 2 nil))]
           :when (and sx (= 3 (count (:sentence sx))) (symbol? s)
                      (not= s t) (tax/genl? tax s t context)
                      (tax/sees? tax context (:context sx))
                      (res/believed-at? kb h context))]
       h))))

(defn subsumed-mint
  "The handle of the believed record that already says, more specifically, what the
  minted `sentence` says in `context` — or nil when nothing does.

  The two shapes an argument declaration mints: a membership `(t x)`, subsumed by a
  membership in a subtype of `t`; and a `genl` edge, subsumed by a route of two edges or
  more.  Nil for anything else and nil with the toggle off, so a caller asks without
  testing either first.

  **A read of belief, which is what makes it order-independent.**  Withholding the mint
  while the specific membership is believed and drawing it again when that membership
  leaves is a function of the current state, so the arrival order of the fact, the
  declaration and the specific type cannot decide which records the KB ends up holding —
  the property `every-arrival-order-reaches-the-same-belief` pins.  What the KB *answers*
  is untouched either way: subsumption reaches `t` from the specific type with or without
  a record in between (docs/argtypes.md)."
  [kb sentence context]
  (when *prune-subsumed-mints?*
    (cond
      (and (= 1 (nm/arity sentence)) (symbol? (nm/functor sentence))
           (symbol? (first (nm/args sentence))))
      (subsuming-membership kb (nm/functor sentence) (first (nm/args sentence)) context)

      (and (= 'genl (nm/functor sentence)) (= 3 (count sentence))
           (symbol? (nth sentence 1)) (symbol? (nth sentence 2)))
      (subsuming-edge kb (nth sentence 1) (nth sentence 2) context))))

(defn- entailment-cascade
  "Every sentence the argument declarations would mint over `sentence` in `context`, and
  over those mints in turn — `{:mints [sentence …] :readers {functor reader}}`.

  This is the closure `special/entail-arg-type` walks as it materializes, computed here
  before anything is stored.  A mint draws its own entailments and must — the retroactive
  direction cascades whether or not the forward one does — so a check that looked only one
  level down would pass a sentence whose *second* consequence the KB cannot hold.

  **Terminates on `seen`.**  A mint is a `(t x)` or a `(genl x t)` over names the KB
  already holds, so the sentences reachable are a subset of a finite product and each is
  expanded once.  That is `entail-arg-type`'s termination argument, made over sentences
  here rather than over stored records.

  One declaration reader per **functor**, kept and handed back: the walk asks the same
  functor's declarations again for every mint that shares one, and the admissibility pass
  below asks a third time.  A reader memoizes for the life of one caller, so building one
  per sentence would throw the memo away at each step and pay `res/constraining-predicates`
  again for it.

  A membership the cascade itself would add is **not** threaded into `types`: the reader
  answers what is stored, which is what the materializer will read too for every mint but
  the ones this same cascade produces.  A clash between two mints of one cascade is
  found by `settle` once the materializer has placed both.

  Seeded with the caller's own reader and its **already-computed** first level, so the
  common case — a sentence whose declarations mint nothing further — walks an empty
  frontier and costs no retrieval at all.  Building a second reader for the triggering
  functor here read its declarations twice per assert, which `assert_cost_test` counts."
  [kb sentence context types decls seed]
  (let [level (into [] (comp (map :assert) (distinct)) seed)]
    (loop [frontier level
           readers  {(nm/functor sentence) decls}
           seen     (conj (set level) sentence)
           mints    level]
      (if-let [s (first frontier)]
        (let [f'    (nm/functor s)
              rs    (if (contains? readers f')
                      readers
                      (assoc readers f' (declaration-reader kb f' context)))
              es    (constraint-entailments kb s context types (get rs f'))
              fresh (into [] (comp (map :assert) (remove seen) (distinct)) es)]
          (recur (into (vec (rest frontier)) fresh)
                 rs
                 (into seen fresh)
                 (into mints fresh)))
        {:mints mints :readers readers}))))

(defn- write-clash
  "The first disjointness clash between two memberships of one write — `sentence` and
  the `mints` its cascade draws — as a violation naming the other member in
  `:clashes-with`, or nil.  Neither member is stored when the entry point asks, so no
  stored-content reader finds the pair; `try-assert` asks this (`*refuse-clashes?*`)."
  [kb sentence context mints]
  (let [tax (reasoning/taxonomy kb)
        ms  (filterv #(and (= 1 (nm/arity %)) (symbol? (nm/functor %))
                           (not= 'not (nm/functor %)))
                     (cons sentence mints))]
    (first
     (for [a ms
           :let [disjoint? (tax/separation-test tax (nm/functor a) context)]
           :when disjoint?
           b ms
           :when (and (not= a b) (= (nm/args a) (nm/args b)) (disjoint? (nm/functor b)))]
       {:type :disjoint :sentence b :types [(nm/functor b) (nm/functor a)]
        :entailed-from sentence
        :clashes-with [{:sentence a :context context}]
        :message (str "arg constraint: " (nm/print-key sentence) " entails "
                      (nm/print-key b) ", disjoint from " (nm/print-key a))}))))

(defn- entailment-check
  "The entailment reading's half of the entry point check:
  `{:entailments [{:assert …} …] :refusal v}` — what `sentence`'s argument declarations
  draw over it, and the first consequence of those declarations the KB could not admit.
  Nil with the toggle off, which is `constraint-entailments`' answer there.

  **The refusal sits on the consequence.**  With the entailment on, `args-problem`'s
  symbol arm yields (`entailment-covers?`), so a wrongly-typed symbol argument is not a
  violation: the declaration says what the argument is.  A *consequence* still can be one
  — a minted membership clashing with a disjoint one —
  so the entry point refuses `sentence` exactly when it would refuse what `sentence`
  entails.  The constraint reading's rule, moved one step along the derivation.

  **Asked before the store.**  `special/entail-arg-type` asks the same question of each
  mint as it materializes, and it runs after the triggering sentex exists — so a mint
  whose violation names no opposing sentex is *dropped* and recorded, and the KB is left
  believing a fact whose declared consequence it rejects.  Asked here, the refusal reaches
  the writer and nothing is stored.  A clash with a believed membership, or between two
  mints of one cascade, refuses nothing: the materializer places each mint and `settle`
  decides the nogood the mints form.

  The violation handed back is the **mint's own**, with the sentence that entailed it in
  `:entailed-from`: what could not be held is what a reader is told, rather than a second
  wording of the argument constraint.

  Naming, well-formedness and edge stratification are **not** asked, only the definitional
  checks: those three live above this namespace, where `special/inadmissible` asks all
  four as one question, and a mint they convict is dropped and reported by the
  materializer.

  One walk of the declarations serves both halves.  The first level is what the caller
  materializes and is also the cascade's seed, so asking `constraint-entailments` again
  for the answer already in hand would read the triggering functor's declarations twice
  per assert — a cost `assert_cost_test` counts."
  [kb sentence context types decls]
  (when *assertive-arg-types?*
    (let [seed (constraint-entailments kb sentence context types decls)]
      ;; The common assert draws no entailment (its functor carries no visible
      ;; declaration).  An empty seed makes the cascade's frontier empty, so `mints` is
      ;; exactly the seed and the refusal `keep` over it is nil — computing the cascade
      ;; and the `keep` at all is the same `{:entailments [] :refusal nil}` reached
      ;; without reading anything.
      (if (empty? seed)
        {:entailments seed :refusal nil}
        (let [{:keys [mints readers]} (entailment-cascade kb sentence context types decls seed)]
          {:entailments seed
           :refusal
           (or (first
                (keep (fn [m]
                        (when-let [p (constraint-problem kb m context types
                                                         (get readers (nm/functor m))
                                                         entry-refuses?)]
                          (assoc p :entailed-from sentence
                                 :message (str "arg constraint: " (nm/print-key sentence)
                                               " entails " (nm/print-key m)
                                               ", which cannot be admitted — " (:message p)))))
                      mints))
               (when *refuse-clashes?* (write-clash kb sentence context mints)))})))))

(defn- refusal
  "The ex-info `constraint-checks` throws for violation `v`: `v` under its own `:type`,
  or, for a clash that only `*refuse-clashes?*` refuses, `:definitional-clash` with the
  clash kind in `:violation`, each other member in `:clashes-with`, as `{:handle
  :sentence :context}` when it is stored and without `:handle` when it is part of the
  write (`write-clash`), and the kind's own keys in `:detail`."
  [kb v]
  (if (or (arbitrable? v) (contains? v :clashes-with))
    (ex-info (str "definitional clash: " (:message v))
             {:type          :definitional-clash
              :violation     (:type v)
              :sentence      (:sentence v)
              :entailed-from (:entailed-from v)
              :clashes-with  (into (vec (:clashes-with v))
                                   (map (fn [h]
                                          (let [s (p/get-sentex (:records kb) h)]
                                            {:handle h :sentence (sx/sentence-of s)
                                             :context (:context s)})))
                                   (opposing-handles v))
              :detail        (dissoc v :message :sentence :entailed-from :clashes-with
                                     :opposing-handle :opposing-handles :type)})
    (ex-info (:message v) (dissoc v :message))))

(defn constraint-checks
  "Throw the first definitional violation that `refuses-assert?`, as typed ex-info — the
  assert path.  Under `*refuse-clashes?*`, the first violation of any kind (`refusal`).

  A violation naming the other believed members of its nogood does not refuse: the
  sentence is stored and `settle` decides the nogood, whatever the members' classes.  An
  admitted clash is **not** reported here — settle discovers it from the relabelled
  region, which is what makes the discovery route-agnostic and the answer the same in
  every arrival order.

  Returns the **entailments** the argument constraints draw over an admissible
  sentence (`constraint-entailments`), for the caller to materialize once the sentex
  it would be justified by exists.  Empty unless `*assertive-arg-types?*`.

  **Two questions, not one, once the entailment is on.**  The sentence has to be
  admissible and so does everything it entails (`entailment-check`) — the argument
  declarations are read as definitions there, so admitting `(parentOf Rex Mary)` is
  admitting `(animal Rex)`, and a KB that cannot hold the second may not be left holding
  the first.  Asked second, and only when the sentence itself passed: a sentence already
  refused needs no second reason, and the cascade is the more expensive read of the two."
  [kb sentence context]
  (let [chk   (checked-sentence kb sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)]
    (if-let [p (constraint-problem kb chk context types decls entry-refuses?)]
      (throw (refusal kb p))
      (let [ec (entailment-check kb chk context types decls)]
        (if-let [p (:refusal ec)]
          (throw (refusal kb p))
          (:entailments ec))))))

(defn check-application-inputs
  "Throw the first violation of a function's argument declarations inside `sentence` in
  `context` — `application-input-problem`, asked of a fact **before** the reify pass.

  `assert` mints every ground reifiable application into its constant before
  `constraint-checks` runs, and the constant carries the function's result types, not
  what the application was given: the inputs are gone by the time the arm that reads
  them could look.  So the assert path asks this first, over the sentence as written,
  from the writer's vantage — the same reading `constraint-checks` gives an unreifiable
  application after the pass, and the one `check` gives both, since `check` does not
  mint.  Asked before the mint, a refused sentence leaves no constant behind.

  Nil for a sentence with no compound argument, before any reader is built."
  [kb sentence context]
  ;; the raw sentence's arguments first: a fact with no compound argument has none under
  ;; any `not` either, and asking this before `checked-sentence` keeps the common fact
  ;; off the canonicalization that reads through its negations
  (when (and (sequential? sentence) (some application-term? (rest sentence)))
    (let [chk (checked-sentence kb sentence)]
      (when (and (symbol? (nm/functor chk)) (some application-term? (nm/args chk)))
        (let [p (application-input-problem kb chk context
                                           (kb/membership-reader kb context)
                                           (declaration-reader kb (nm/functor chk) context))]
          (when p
            (throw (ex-info (:message p) (dissoc p :message)))))))))

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
  (let [chk   (checked-sentence kb sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)]
    (if-let [p (constraint-problem kb chk context types decls refuses-assert?)]
      {:violation {:violation (:type p) :detail (dissoc p :type :sentence)}}
      {:entailments (constraint-entailments kb chk context types decls)})))

(defn derivation-violation
  "`constraint-admission`'s violation half alone: nil when `sentence` is admissible in
  `context` or its only violation is arbitrable, else the `{:violation :detail}` map.
  The argument-type mint reads this, so a mint clashing with a believed membership is
  placed and weighed at settle as a rule's conclusion is (docs/argtypes.md)."
  [kb sentence context]
  (let [chk (checked-sentence kb sentence)]
    (when-let [p (constraint-problem kb chk context (kb/membership-reader kb context)
                                     (declaration-reader kb (nm/functor chk) context)
                                     refuses-assert?)]
      {:violation (:type p) :detail (dissoc p :type :sentence)})))

(defn conviction-watch
  "The term whose memberships can lift the argument conviction `v` (a `{:violation
  :detail}` map), as the `{:term}` field a waiting entry carries: the convicted argument,
  which a membership arriving can place inside the declared type.

  Read off the conviction the entry is decided under, every time it is decided.  A
  re-ask that is still convicted can be convicted on a different argument — an
  application with two targets outside the type names the first, and once that one is
  lifted it names the second — and an entry left watching the first would never be
  re-asked when the second is lifted, so the lifting order would decide whether the
  firing is ever placed."
  [v]
  {:term (get-in v [:detail :arg])})

(defn constraint-violation
  "The definitional checks as a value alone: nil when `sentence` is admissible in
  `context`, else `{:violation :arg-type|:arg-genl|:arg-position
  |:arg-constraint-kind|:disjoint|:asymmetric|:functional|:anti-transitive
  :detail {...}}`.

  **Every** violation, arbitrable ones included — which is what separates this from
  `constraint-admission`.  The callers are the gates on content that is never stored
  when it fails: `special/inadmissible`'s default arity, read by what `abduce` may assume
  and by a context-valued function's computed `genlCx` edge.  Content the engine stores
  on its own behalf (a lift's copy, a merge's twin, an argument-type mint) asks
  `derivation-violation` instead, so its arbitrable clash is stored and decided at each
  reader."
  [kb sentence context]
  (let [chk   (checked-sentence kb sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)]
    (when-let [p (constraint-problem kb chk context types decls some?)]
      {:violation (:type p) :detail (dissoc p :type :sentence)})))

(defn arg-position-violation
  "The `:arg-position` violation the **stored declaration** `sentence` commits in
  `context`, or nil — a constraint on a position its predicate does not have.

  It re-asks an entry point check of a stored declaration through the arm the entry point
  reads, so the two cannot drift.  The reader is `vaelii.impl.quality`: a declaration
  stranded by an arity that arrived later constrains nothing, refuses nothing and mints
  nothing, so it is a census question rather than a settle one (docs/taxonomy.md).

  Only the position arm.  `declaration-problem` also convicts a declaration disagreeing
  with its predicate's `relation_kind`, and an arity arriving is not what makes that true,
  so asking it here would report a second finding under the first one's trigger.

  Both of `interArg`'s positions are asked, as at the entry point, and the first that
  convicts is the answer.

  Through `checked-sentence`, like the entry point: a doubly negated
  declaration is a declaration and is read as one, and a genuinely negative sentence keeps
  its `not`, which matches neither arm below.  A caller reading the record store hands in
  a sentence the constructor already stripped to its positive body, so the pass costs it
  nothing — the reason to spell it is that the arm is stated once and both entrances to it
  must be the same entrance."
  ([kb sentence context]
   (arg-position-violation kb sentence context (kb/membership-reader kb context)))
  ([kb sentence context types]
   (let [chk            (checked-sentence kb sentence)
         [f pred n _ m] chk]
     (when (symbol? pred)
       (cond
         (and (= 'interArg f) (= 5 (nm/arity chk)))
         (some-> (or (arg-position-problem kb f pred n context types)
                     (arg-position-problem kb f pred m context types))
                 (assoc :sentence chk))

         (and (contains? arg-constraint-kinds f) (= 3 (nm/arity chk)))
         (some-> (arg-position-problem kb f pred n context types)
                 (assoc :sentence chk)))))))

(defn arbitrable-violations
  "**Every** disjointness and cover clash `sentence` forms against believed content
  visible from `context` — the nogood half of the membership checks, read by `settle`'s
  discovery.  Empty when the sentence forms none.  The tuple marks' nogoods are found
  from a candidate index instead (`vaelii.impl.decide`).

  Asked of a sentence that is itself **stored and believed**, which is what the
  discovery walks: the clashes it reports are with the *other* members of each nogood,
  since a term's own type is not disjoint from itself.

  Plural: a term holding three mutually disjoint types forms three pairs, and stopping at
  the first would report a set of pairs that depended on the order the argument root
  handed the memberships back, which is arrival order.  `context` is the asker; a caller
  asking a stored sentex's question from a vantage passes the vantage."
  [kb sentence context]
  (let [chk   (checked-sentence kb sentence)
        types (kb/membership-reader kb context)]
    (->> (concat (disjoint-problems kb chk context types)
                 (cover-refutations kb chk context))
         (filter arbitrable?))))

(defn check-sentex-ground
  "`check-ground` over `s`, the sentex already built from `sentence` in `context`: throw
  `:not-ground` when `s` is not a rule and has a free variable, unless `sentence` is a
  schematic equation or a `defn*` definition.  A variable inside a `(Quote …)` or bound
  by a quantifier is not free (`sx/closed?`)."
  [s sentence context]
  (when (and (nil? (:antecedent s)) (not (sx/closed? s))
             (not (rewrite/schematic-equation? sentence))
             ;; a `defn*` collection definition carries the member variable `?x` in
             ;; its condition argument, the way a schematic equation carries its schema
             ;; variables — it is stored to retract and belief-follow, and it expands
             ;; into the rules where those variables belong (docs/defns.md)
             (not (sx/defn-sentence? sentence)))
    (throw (ex-info (str "not ground: " (pr-str sentence)
                         " contains a variable — a fact must be ground"
                         " (write a universal claim as a rule)")
                    {:type :not-ground :sentence sentence :context context}))))

(defn check-ground
  "Reject a non-rule sentence that still contains pattern variables.

  A fact asserts something; `(mortal ?x)` asserts nothing — it is an open formula, not
  a sentence.
  Stored as a premise it is worse than useless: `unify` matches it against any goal,
  so it silently behaves as a universally quantified fact that nothing ever licensed.
  Universal claims are written as rules, where `check-range-restricted` governs the
  variables.

  Rule-ness is read off the **canonicalized record**, not off the raw input: an
  `implies`, a `set/*Rule` wrapper, and a nested combination of the two all
  canonicalize into `:antecedent`, and pattern-matching the input would have to
  re-derive that (and would miss a spelling).

  A **schematic equation** `(equals (fatherOf (fatherOf ?x)) (grandfather_of ?x))` is
  the deliberate exception: its variables belong to a term-rewriting schema, not to an
  open fact, so it is stored as an oriented rewrite rule rather than refused
  (docs/equality.md, symbolic equational reasoning).  It is not matched as a fact
  under `unify` — its functor is `equals`, read by the equality machinery, not by the
  fact prover for arbitrary goals.

  `check-sentex-ground` is the same check over a sentex already built, which is what a
  dump import holds."
  [kb sentence context]
  (check-sentex-ground (res/kb-sentex kb sentence context) sentence context))

(defn check-except-target
  "Refuse a visibility `(except (sentexHandle H))` when no sentex is stored under H
  (`:unknown-handle`).  Handles are allocated in assertion order, so every except this
  admits names a handle below its own, and the except graph `assert` builds is acyclic.
  A target retracted after its except leaves the except naming nothing, and a handle is
  never reissued (docs/contexts.md, except)."
  [kb sentence]
  (when-let [h (kb/except-target sentence)]
    (when (nil? (p/get-sentex (:records kb) h))
      (throw (ex-info (str "except names handle " h ", and no sentex is stored under it")
                      {:type :unknown-handle :handle h :sentence sentence})))))

;; ---- the forced-monotonic roster ------------------------------------------

(def uncleared-forcing
  "The roster declarations whose retraction is refused, each with the semantics the
  declared predicate has no unforced reading of: `[declaration-functor predicate]` ->
  missing semantics (docs/nmtms.md, \"The forced-monotonic roster\")."
  (into {['forced_monotonic_between_predicates 'genl] :unforced-predicate-genl
         ['forced_monotonic_predicate 'genlCx]        :unforced-context-edge
         ['forced_monotonic_predicate 'except]        :unforced-except}
        (for [[missing preds]
              {:unforced-relation-mark
               '[irreflexive anti_symmetric asymmetric functional functionalInArg
                 anti_transitive]
               :unforced-definitional-declaration
               '[disjoint covering partition sibling_disjoint orthogonal siblingDisjointException]
               :unforced-arity-binding
               '[arity unary binary ternary unary_predicate binary_predicate
                 ternary_predicate unary_function binary_function ternary_function
                 variable_arity variable_arity_predicate variable_arity_function arityMin]
               :unforced-equality '[rewriteOf sameAs equals]}
              p preds]
          [['forced_monotonic_predicate p] missing])))

(def ^:private roster-kind
  "The taxonomy property each roster declaration functor maintains."
  '{forced_monotonic_predicate          :forced-monotonic
    forced_monotonic_between_predicates :forced-between-predicates})

(defn forced-monotonic?
  "Is `literal` on the forced-monotonic roster (`decide/roster-literal?`, docs/nmtms.md,
  \"The forced-monotonic roster\")."
  [kb literal]
  (decide/roster-literal? (reasoning/taxonomy kb) literal))

(defn inert-denial?
  "Is `sentence` a denial `(not S)` of a `forced-monotonic?` literal `S`.  The labeller
  holds such a denial OUT (the `:out` forced set): it is never believed, forms no nogood
  and fires no rule (docs/nmtms.md, \"The forced-monotonic roster\")."
  [kb sentence]
  (and (sx/negation? sentence) (forced-monotonic? kb (second sentence))))

(defn roster-rule?
  "Is the stored rule `rule-sentex` one whose firings conclude a roster literal as an
  ordinary belief: not `set/defaultRule`, no `unknown` antecedent, and every antecedent a
  `forced-monotonic?` literal.  Its `exceptWhen` exceptions are meta-sentexes, which
  `forced-conclusion-violation` reads at the firing."
  [kb rule-sentex]
  (let [antes (:antecedent rule-sentex)]
    (boolean (and (seq antes) (not (:defeasible rule-sentex))
                  (every? #(and (not (sx/unknown? %)) (forced-monotonic? kb %)) antes)))))

(defn forced-conclusion-violation
  "The `:forced-conclusion` violation of a firing of the rule stored at `rule-handle` that
  concludes the ground sentence `conseq`, or nil when the firing is admitted.  A firing
  concluding a denial of a `forced-monotonic?` literal is convicted, and so is one
  concluding a roster literal unless its rule is a `roster-rule?` with no believed
  `exceptWhen`.  A convicted firing is stored, held void (the `:void` forced set) and
  reported (docs/nmtms.md, \"The forced-monotonic roster\")."
  [kb rule-handle conseq]
  (let [neg? (sx/negation? conseq)
        body (if neg? (second conseq) conseq)]
    (when (and (forced-monotonic? kb body)
               (or neg?
                   (let [rsx (p/get-sentex (:records kb) rule-handle)]
                     (or (nil? rsx) (not (roster-rule? kb rsx))
                         (seq (provers/rule-exception-entries kb rule-handle))))))
      {:violation :forced-conclusion
       :detail    {:message (str (pr-str conseq) " is not concluded: " (nm/functor body)
                                 " is on the forced-monotonic roster, and a rule concludes a"
                                 " roster literal only from roster antecedents, with no"
                                 " unknown, exceptWhen or set/defaultRule")}})))

(defn forced-premise?
  "Does a premise mark on the stored sentex `sx` confer `:monotonic` in the labeller (the
  `:mono` forced set): `sx` is a `genlCx` edge, which caps no firing's class
  (docs/reference.md, decisions 1 and 9).  Every other roster literal keeps the strength
  it was written at and is never a loser (`decide/verdict`)."
  [sx]
  (and (not (rules/rule? sx)) (= 'genlCx (nm/functor (:sentence sx)))))

(defn force-sentex!
  "Write the `:mono` and `:out` memberships of the stored sentex `sx` into the network.
  The assert path calls it before the premise mark, so a forced-out denial is never IN,
  even for one relabel.  A membership already right writes nothing."
  [kb sx]
  (let [tms (reasoning/tms kb)
        h   (:id sx)
        put (fn [kind on?]
              (when (not= on? (jtms/forced? tms kind h))
                (jtms/set-forced tms kind [h] on?)))]
    (put :mono (forced-premise? sx))
    (when-not (rules/rule? sx)
      (put :out (inert-denial? kb (:sentence sx))))))

(defn- rule-sentex
  "The stored rule at `h`, or nil when `h` names no stored rule."
  [kb h]
  (when (integer? h)
    (let [sx (p/get-sentex (:records kb) h)]
      (when (rules/rule? sx) sx))))

(defn- forcing-moves
  "Add to `acc` the forced memberships that move for the stored sentex `sx` and for the
  firings that conclude it or that its rule informs, as `{[kind on?] [id …]}`, and the
  report of each firing newly held void under `[:report]`."
  [kb acc sx]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        h    (:id sx)
        put  (fn [acc kind id on?]
               (let [on? (boolean on?)]
                 (if (= on? (jtms/forced? tms kind id))
                   acc
                   (update acc [kind on?] (fnil conj []) id))))
        void (fn [acc jid rh conclusion]
               (let [v (forced-conclusion-violation kb rh (:sentence conclusion))
                     acc (put acc :void jid v)]
                 (if (and v (not (jtms/forced? tms :void jid)))
                   (update acc [:report] (fnil conj [])
                           (assoc v :sentence (:sentence conclusion)
                                  :context (:context conclusion) :rule rh))
                   acc)))
        acc  (put acc :mono h (forced-premise? sx))]
    (if (rules/rule? sx)
      ;; a firing is read only when its conclusion can be on the roster now, or when it
      ;; is held void now and the roster may have released it
      (let [c       (:consequent sx)
            body    (if (sx/negation? c) (second c) c)
            reach?  (let [f   (nm/functor body)
                          tax (reasoning/taxonomy kb)]
                      (or (sx/variable? f)
                          (and (symbol? f)
                               (or (decide/on-roster? tax :forced-monotonic f)
                                   (decide/on-roster? tax :forced-between-predicates f)))))]
        (reduce (fn [acc jid]
                  (let [j (jtms/justification tms jid)]
                    (if (and (= h (:informant j)) (or reach? (jtms/forced? tms :void jid)))
                      (if-let [conclusion (p/get-sentex recs (:consequence j))]
                        (void acc jid h conclusion)
                        acc)
                      acc)))
                acc (sort (jtms/dependents tms h))))
      (reduce (fn [acc jid]
                (let [rh (:informant (jtms/justification tms jid))]
                  (if (rule-sentex kb rh) (void acc jid rh sx) acc)))
              (put acc :out h (inert-denial? kb (:sentence sx)))
              (sort (jtms/supports tms h))))))

(defn force-sentexes!
  "Rewrite the network's forced memberships for the stored sentexes `sxs` and the
  firings each concludes or informs, from the roster as it stands, and report each firing
  newly held void.  The relabel each set change runs is the whole recompute: nothing
  stored is written or deleted.  Answers whether any membership moved."
  [kb sxs]
  (let [tms   (reasoning/tms kb)
        moves (reduce #(forcing-moves kb %1 %2) {} sxs)]
    (doseq [[[kind on?] ids] (dissoc moves [:report])]
      (jtms/set-forced tms kind ids on?))
    (violations/report kb (get moves [:report]))
    (boolean (seq (dissoc moves [:report])))))

(defn force-reach!
  "Rewrite the forced memberships over what `pred` reaches — every stored sentex
  mentioning it (its literals, their denials, the rules reading or concluding it) and
  their firings — after `pred` joins or leaves the roster (docs/nmtms.md, \"The
  forced-monotonic roster\").  Answers the handles of the rules in that reach, which a
  firing swept while it was held void is restored from by a re-join."
  [kb pred]
  (let [sxs (into [] (kb/find-sentexes kb pred))]
    (force-sentexes! kb sxs)
    (into [] (comp (filter rules/rule?) (map :id)) sxs)))

(defn force-roster!
  "Write every forced membership the stored content takes under the roster:
  `recover`'s pass, run once the taxonomy replay has rebuilt the roster properties.  A
  stored denial of a roster literal with no premise mark and no support is the record an
  older store kept inert, and it takes the `:default` premise mark it was written with
  (docs/nmtms.md, \"The forced-monotonic roster\")."
  [kb]
  (let [tax  (reasoning/taxonomy kb)
        tms  (reasoning/tms kb)
        preds (sort (into #{} (mapcat #(decide/roster tax %)) decide/roster-kinds))
        sxs  (vals (into {} (comp (mapcat #(kb/find-sentexes kb %)) (map (juxt :id identity)))
                         preds))]
    (force-sentexes! kb sxs)
    (doseq [{h :id s :sentence} sxs
            :when (and (inert-denial? kb s) (not (jtms/premise? tms h))
                       (empty? (jtms/supports tms h)))]
      (p/mark-premise (:records kb) h :default)
      (jtms/add-premise tms h :default))))

(defn forcing-retraction-problem
  "The `:uncleared-forcing` refusal of retracting the sentex at `handle`, as a value, or
  nil: the handle states a roster declaration whose predicate has no established unforced
  semantics (`uncleared-forcing`).  The test reads the declaration properties' supporters,
  which are what the sentence alone puts there, and fetches no record.  `where` names the
  entry point."
  [kb handle where]
  (let [tax (reasoning/taxonomy kb)]
    (some (fn [[[functor pred :as decl] missing]]
            (let [kind (roster-kind functor)]
              (when (contains? (tax/prop-supporter-contexts tax kind pred) handle)
                {:type :uncleared-forcing :handle handle :predicate pred :missing missing
                 :operation where
                 :message (str (pr-str (apply list decl)) " is not retracted: " pred
                               " has no unforced semantics yet (" (name missing)
                               "), so its declaration stays")})))
          uncleared-forcing)))

;; ---- storable values ----------------------------------------------------
;; A sentence's leaves must survive the durable log.  Symbols and keywords (the
;; vocabulary), strings/numbers/chars (the values), and booleans/nil — everything a
;; sentence is built from — always do, and are cleared without a freeze so the assert
;; hot path pays one type-check per leaf and no serialization.  Anything else (a
;; function, an atom/ref, an open stream, a Serializable object off nippy's thaw
;; allowlist) is put through the freeze/thaw pair the on-disk backends run, and refused
;; if either throws — so a value stores in every backend or none, rather than in memory
;; and then throwing at write time on the first disk backend.

(defn- storable-scalar?
  "A leaf nippy always round-trips, recognised without a freeze.  Ordered by how often
  a sentence's leaves are each — the vocabulary (symbols, keywords) and values
  (strings, numbers) first, the rarer nil/boolean/char last."
  [v]
  (or (symbol? v) (keyword? v) (string? v) (number? v)
      (nil? v) (boolean? v) (char? v)))

(defonce ^{:private true
           :tag java.util.concurrent.ConcurrentHashMap
           :doc "Storability memoized by class.  Every value that reaches the freeze probe is a leaf
  that is neither a scalar nor a collection, and for those it is a property of the
  *class* — a `Date` always freezes and thaws, a function never does, and nippy's own
  thaw allowlist is class-keyed — so the probe runs once per class, not once per value.
  A bulk load of dated or id-stamped facts then pays one freeze/thaw for the type, not
  one per fact.  Bounded by the distinct non-scalar leaf classes a process ever asserts,
  which is a handful."}
  storable-class-cache
  (java.util.concurrent.ConcurrentHashMap.))

(defn- nippy-storable?
  "Does a value of `v`'s class survive a nippy freeze *and* thaw without throwing — the
  pair the durable log runs on write and read?  Not a `=` round-trip (a byte array and
  other identity-compared values store fine yet would fail it) and not freeze alone (a
  Serializable value off the thaw allowlist freezes and then throws on read); both must
  succeed.  Memoized by class (see `storable-class-cache`): the first value of a class
  runs the probe, the rest read the boolean it cached.

  **The thaw is the one the durable readers run** (`vaelii.impl.io.thaw`), not a bare
  nippy one, so the public entry point and the file readers hold one opinion about what a leaf
  may be.  A class only Java serialization round-trips is refused here rather than
  stored and then refused on the way back off disk — which is the same asymmetry, one
  restart later, that this check exists to close.

  Only an `Exception` is a verdict.  An `Error` — an `OutOfMemoryError` mid-freeze — says
  nothing about the class, so it propagates uncached rather than refusing every later
  value of that class in every KB until the process exits."
  [v]
  (let [c      (class v)
        cached (.get storable-class-cache c)]
    (cond
      (identical? Boolean/TRUE cached)  true
      (identical? Boolean/FALSE cached) false
      :else (let [ok (try (safe/thaw (nippy/freeze v)) true
                          (catch Exception _ false))]
              (.put storable-class-cache c (if ok Boolean/TRUE Boolean/FALSE))
              ok))))

(defn- first-unstorable
  "The first value anywhere in `x` a stored sentence may not carry, as
  `[kind value]` — or nil.  Sequentials are descended; a scalar is cleared without a
  freeze.  Two kinds, and they are two different refusals wearing one `:type`:

  - **`:uncanonical`** — a **map or set** (a record is a map, so it lands here too).
    `sentex/canon` normalizes a sentence's sequentials to `PersistentList` and interns
    its symbols, and it has nothing to do to an unordered collection: two `=` sentences
    differing only in an argument map's implementation or insertion order freeze to
    *different* nippy bytes, which is the hazard `canon` exists to remove
    (docs/canonicalization.md).  `nm/form-rank` has no rank for one either, so
    `compare-form` — every content-keyed tie-break in the engine — has no total order
    over such a sentence, and a tie-break with no order is arrival order.
  - **`:unserializable`** — a leaf whose class does not survive a nippy freeze *and*
    thaw (`nippy-storable?`).

  The uncanonical test comes first because it is the more specific complaint: a map
  full of atoms is refused for being a map, which is the fact that does not go away
  when the atoms do."
  [x]
  (cond
    (storable-scalar? x)   nil
    (or (map? x) (set? x)) [:uncanonical x]
    (sequential? x)        (some first-unstorable x)
    :else                  (when-not (nippy-storable? x) [:unserializable x])))

(defn check-encodable
  "Reject a sentence carrying a value a stored sentence may not carry.

  **Unserializable**: a function, an atom/ref, an open stream — anything nippy cannot
  freeze and thaw — stores in the in-memory backend and then throws at write time on the
  first on-disk backend, so the same assert would succeed or fail by backend.  Refusing
  it here makes the backends agree: a stored sentence's values round-trip.

  **Uncanonical**: a map or a set has no canonical form, so a sentence carrying one has
  neither stable durable bytes nor a content order to tie-break on (`first-unstorable`).
  Refused rather than canonicalized, because there is no ordering of an unordered
  collection that is the *sentence's* — the fix is to write what the KB can order, a
  sequential or a reified term.

  Both throw `:not-encodable`, carrying the offending value under `:value`."
  [sentence]
  (when-let [[kind v] (first-unstorable sentence)]
    (throw (ex-info (if (= :uncanonical kind)
                      (str "value cannot be stored: " (pr-str v) " — a sentence's content"
                           " is EDN scalars and sequentials, and a map or set has no"
                           " canonical form, so it has neither stable durable bytes nor a"
                           " content order to tie-break on (write a sequential — a vector"
                           " of pairs — or reify the structure as a term)")
                      (str "value cannot be stored: " (pr-str v) " of type "
                           (.getName (class v)) " does not round-trip through the durable"
                           " log (nippy) — a sentence's values must be serializable"))
                    {:type :not-encodable :sentence sentence :value v}))))

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

(def ^:private different-negatives
  "The predicates a `different` antecedent depends on negatively: the relations a fact on
  which withdraws it (`negative-predicates`)."
  (into #{'indeterminate_term 'genl} kb/equality-predicates))

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

  The negative edge from a `different` antecedent runs to every relation that can
  *withdraw* it.  Three assert a merge.  The rest make a term an `indeterminate_term`,
  whose members are exempt from the unique-name assumption, so asserting one withdraws a
  `different` the same way an equality does (docs/predall.md, docs/equality.md).

  Two names carry the indeterminacy half.  `indeterminate_term` is the category itself,
  and a subkind of it needs no name here: `wff/negation-walk` steps from a rule concluding
  a `(vague_kind ?x)` declared under the category to the readers of every predicate in its
  `genls-global` closure, so the category's own edge reaches it.  `genl` is the second,
  and it is the over-approximation this check prefers: a rule concluding `genl` mints a
  subkind the taxonomy does not hold yet, which no fan over the current closure can see.
  It costs a refusal where a rule set reads `different` and concludes any `genl` whatever,
  since the consequent's second argument is a variable at check time.  No shipped rule
  reads `different`, so no KB the ontology builds pays for it.  A skolem's membership is
  structural and no rule concludes one, so it needs no edge.

  All of them run to the concluding relation rather than to `different` itself — nothing
  ever concludes `different`, so an edge keyed on it would reach no rule and find no
  cycle.

  Refusing the cycle is half the answer and `rules/rechecked?` is the other.  A rule that
  merely *reads* `different` closes no cycle and is stored, and the fact that withdraws its
  guard can arrive at any time — so such a rule is registered in the re-check index and its
  firing is re-decided when one does (docs/predall.md)."
  [antecedent-preds neg-query-preds]
  (concat neg-query-preds
          (when (some #(= 'different %) antecedent-preds)
            (nm/sort-by-content-key identity different-negatives))))

(defn- negative-edge-rules
  "Handles of every **stored** rule a negative edge leaves — the gate on walking at all:
  with none, the stored graph has no negative edge and no cycle through negation.

  Two rosters, because the re-check index is written when a rule is **indexed**.  Its
  `:rules` holds a rule carrying an `exceptWhen`, an `(unknown S)` antecedent, an
  aggregate, a closed-extent negative or a `different` antecedent — `rules/rechecked?`
  is the gate, and a `different` one is registered there like the rest, since its firing
  is re-decided when a merge or an indeterminacy withdraws the guard.  A rule stored by a
  build that did not register it is still on the antecedent index, in one lookup under
  `different`, which is the key `rules/antecedent-key` files it under.  That second
  roster is what keeps the refusal right over an index written before the registration
  existed and not yet rebuilt by `reindex`.

  Read `different` out and the gate under-approximates the graph — a KB whose only
  negative edge is one rule's `different` would skip the walk, and a cycle through it
  would be stored.  Belief is unread on both halves, over-approximating for the reason
  `stratification-readers` does.

  The antecedent lookup sits behind a membership test on the antecedent keys some stored
  rule reads (`reads/stored-rule-key?`).  So a KB no rule of which mentions `different` —
  every KB the shipped ontology builds — reads no rule posting for this half."
  [kb]
  (let [index (:index kb)]
    (cond-> (set (reads/watched-rules index))
      (reads/stored-rule-key? index 'different)
      (into (reads/as-stored-rules-by-antecedent index 'different)))))

(defn- exception-predicates
  "The predicates the exceptWhen exceptions of stored rule `handle` mention — the
  negative-edge keys the stratification graph reads, gathered from the rule's
  belief-following exceptWhen meta-sentexes (`provers/rule-exceptions`).

  Read through the query frames (`rules/watched-predicates`), because a cycle runs
  through what the exception *reads*: an exception that is itself an `(unknown S)` is a
  negative dependency on `S`'s predicate, and keyed on `unknown` — which nothing
  concludes — the graph would find no cycle to refuse."
  [kb handle]
  (mapcat rules/watched-predicates (provers/rule-exceptions kb handle)))

(defn- rule-graph-node
  "The stratification graph's view of a stored rule: what it depends on, positively
  (its antecedent predicates) and negatively (the predicates its exceptWhen exceptions
  and its `unknown` antecedents mention, the predicate of a negative antecedent a
  `closed_extent_predicate` grant reads as NAF, plus the equality relations when it reads
  `different`).  The exceptWhen predicates come from the rule's meta-sentexes, so kb is
  needed.

  The antecedents are read as **dependency** predicates, not as index keys: an edge
  joins a reader to a rule whose consequent is filed under a spec of what it reads, and
  a conclusion is filed by `consequent-predicate` — which spells a negation `not` where
  the index key spells it `[:not pred]` (`rules/dependency-predicates`).  The consequent
  is `:concludes-any?` for a rule concluding `(?p …)` that chains, which could conclude
  any predicate (`rules/consequent-index-pred`)."
  [kb handle rule-sentex]
  (let [antes   (rules/dependency-predicates (sx/sentence-of rule-sentex))
        ;; an `:inert` rule with a variable consequent keeps the canonical variable, and
        ;; concludes nothing
        conseq  (rules/consequent-index-pred rule-sentex)]
    {:id               handle
     :label            (str "rule#" handle)
     :content          [(sx/sentence-of rule-sentex) (:context rule-sentex)]
     :consequent-pred  (when (symbol? conseq) (when-not (sx/variable? conseq) conseq))
     :concludes-any?   (= p/var-consequent-key conseq)
     :antecedent-preds antes
     :exception-preds  (negative-predicates
                        antes (concat (exception-predicates kb handle)
                                      (rules/recheck-predicates rule-sentex)
                                      (rules/closed-extent-predicates-of
                                       (reasoning/taxonomy kb) (sx/sentence-of rule-sentex))))}))

(defn- stored-rule-node
  "The graph node for a stored rule handle — nil if the handle names something that
  is not a rule, which the rule index should never hand back but which a stale
  posting could."
  [kb handle]
  (when-let [rsx (p/get-sentex (:records kb) handle)]
    (when (rules/rule? rsx) (rule-graph-node kb handle rsx))))

(defn- stratification-readers
  "Predicate -> the rule nodes reading it, positively or negatively, in content order;
  with no argument, every rule node.  `wff/negation-walk` steps from a rule to the readers
  of each predicate at or above its consequent.

  A reader is found through the rule index: the antecedent postings under the predicate
  (every `[:not f]` key for `not`, the dependency spelling of a negated antecedent), the
  re-check postings under it, and the antecedent postings under `different` or `[:not P]`
  where the predicate is one a `different` antecedent or a closed extent makes negative.
  Each candidate's node is read, and kept when its predicates hold the one asked.  Belief
  is unread: refusing a stratified rule set is annoying, accepting an order-dependent one
  is a correctness hole.

  The two-arity adds `pending`, the rule (or exception) being added, under each predicate
  it reads, in place of any stored node with its id: without it a rule whose exception
  mentions what it concludes — a one-rule cycle — would look stratified.

  The returned fn memoizes the node per rule handle and the readers per predicate, for as
  long as the caller holds it.  Every caller builds one per check and drops it when the
  check returns, and a check runs before anything is written, so the store cannot change
  under the memo (docs/exceptions.md, \"The search\")."
  ([kb] (stratification-readers kb nil))
  ([kb pending]
   (let [index   (:index kb)
         tx      (reasoning/taxonomy kb)
         nodes   (java.util.HashMap.)
         node    (fn [h]
                   (if (.containsKey nodes h)
                     (.get nodes h)
                     (let [n (stored-rule-node kb h)] (.put nodes h n) n)))
         reads?  (fn [n g] (or (some #(= g %) (:antecedent-preds n))
                               (some #(= g %) (:exception-preds n))))
         ;; content order, since `wff/negation-walk` returns the first cycle it closes, and a
         ;; set of handles iterates in an order the handles decide
         ordered (fn [handles keep?]
                   (cond-> (nm/sort-by-content-key
                            :content (filter keep? (keep node (disj (set handles) (:id pending)))))
                     (and pending (keep? pending)) (conj pending)))
         by-pred (java.util.HashMap.)
         every   (delay (ordered (concat (reads/as-stored-rules-in index :rule nil)
                                         (reads/watched-rules index))
                                 some?))]
     (fn
       ([] @every)
       ([g]
        (if (.containsKey by-pred g)
          (.get by-pred g)
          (let [ante-keys (if (= sx/not-functor g)
                            (cons g (filter vector? (reads/as-stored-rule-keys index)))
                            [g])
                found     (ordered (concat (mapcat #(reads/as-stored-rules-by-antecedent index %)
                                                   ante-keys)
                                           (reads/watched-rules-on index g)
                                           (when (contains? different-negatives g)
                                             (reads/as-stored-rules-by-antecedent index 'different))
                                           (when (and (symbol? g) (tax/has-prop? tx :closed-extent g))
                                             (reads/as-stored-rules-by-antecedent index [:not g])))
                                   #(reads? % g))]
            (.put by-pred g found)
            found)))))))

(defn check-stratified
  "Throw unless adding this rule leaves the rule set stratified — see
  docs/exceptions.md.  Runs before anything is stored, so a refused rule leaves no
  partial state behind.

  Fast path: with no negative edge on the rule being added and none on any stored rule
  (`negative-edge-rules`), the graph has no negative edge at all and no cycle through
  negation is possible, so the walk is skipped entirely.  That is every rule in an
  ontology that uses no negative dependency — no exception, no `unknown`, no aggregate,
  no closed-extent negative and no `different` — which is most of them."
  [kb sentence inner context]
  (let [[_ _ exception] (sx/peel-rule-wrapper sentence)
        ;; dependency spelling, not the index key: `rule-graph-node` says why
        antes             (rules/dependency-predicates inner)
        ;; negatives: the exception's predicates, the `unknown` antecedents', the
        ;; **aggregate** bodies' *and* the predicate of a negative antecedent a closed
        ;; extent reads as NAF.  All four read what the KB believes rather than a fact the
        ;; firing names, so a cycle through any of them is unstratified — a rule whose
        ;; count is over a relation the rule itself concludes has no settled answer, and
        ;; which one it lands on would depend on arrival order.
        negatives         (negative-predicates antes (concat (rules/watched-predicates exception)
                                                             (rules/naf-predicates-of inner)
                                                             (rules/aggregate-predicates-of inner)
                                                             (rules/closed-extent-predicates-of
                                                              (reasoning/taxonomy kb) inner)))]
    ;; The fast path skips the walk when the graph has no negative edge at all — and a
    ;; `different` antecedent counts as one on both sides, so a rule that reads the
    ;; equality closure is walked, and a *stored* one keeps the walk alive for a rule
    ;; arriving above it that carries no negative edge of its own.
    (when (or (seq negatives) (seq (negative-edge-rules kb)))
      (let [conseq  (rules/consequent-predicate inner)
            pending {:id               ::pending
                     :label            "the rule being asserted"
                     :antecedent-preds antes
                     :exception-preds  negatives
                     :consequent-pred  (when-not (sx/variable? conseq) conseq)
                     :concludes-any?   (sx/variable? conseq)}]
        (when-let [cycle (wff/negation-cycle (reasoning/taxonomy kb)
                                             (stratification-readers kb pending)
                                             pending)]
          (throw (ex-info (str "not stratified: " (pr-str inner) " would close a cycle"
                               " through negation: " (wff/cycle-description cycle)
                               " — a rule set is stratified when no predicate reaches"
                               " itself through a negative edge, so break the cycle at"
                               " one of the rules named, or conclude into a predicate"
                               " off that path")
                          {:type :not-stratified :sentence inner :context context
                           :cycle cycle})))))))

(defn check-no-imperative
  "Refuse a `do/` imperative anywhere inside a rule — antecedent, consequent, or
  `exceptWhen` query.

  A rule is evaluated inside the forward-chaining fixpoint, and an imperative there
  would run a number of times that depends on firing order while mutating the KB the
  fixpoint is still computing over.  Order independence and locality are the two
  invariants the TMS is built on (docs/nmtms.md); a side effect inside the fixpoint
  breaks both at once.  So a `do/` form is legal only at the top level of an `assert`,
  where the caller decided when it happens (docs/labeling.md).

  Walks the whole form rather than the three slots, so a nesting cannot smuggle one
  past — the check is about a fixpoint reaching it, not about where it was written."
  [sentence]
  (when-let [bad (sx/some-form sx/do-form? sentence)]
    (throw (ex-info (str "a do/ imperative cannot appear in a rule: " (pr-str bad)
                         " — a rule is evaluated inside the forward-chaining fixpoint,"
                         " where an imperative runs a number of times that depends on"
                         " firing order.  Assert it on its own, at the top level of an"
                         " assert, where the caller decides when it runs")
                    {:type :not-assertible :form bad :sentence sentence}))))

(defn check-no-defeat
  "Refuse a `defeat` literal anywhere `nm/literals` descends: a fact, a `not`, a rule's
  antecedents and consequent, an `exceptWhen` query.  Throws `:derived-only`.

  The engine derives every `(defeat (sentexHandle H))` (docs/nmtms.md): a placed nogood
  stores one for its unique weakest member.  A defeat written as a premise would remove a
  handle from belief whatever its class, and a rule reading one would fire on a read-time
  verdict.  The check reads the sentence alone, so it refuses the same sentence in every
  KB and every arrival order.  Matching and asking `(defeat ?h)` are reads and pass no
  check."
  [sentence]
  (when-let [[_ lit] (first (filter #(= sx/defeat-functor (nm/functor (second %)))
                                    (nm/literals sentence)))]
    (throw (ex-info (str "defeat is derived by the engine and cannot be asserted: "
                         (pr-str lit) " in " (pr-str sentence)
                         " — a placed nogood stores the defeat of its weakest member")
                    {:type :derived-only :form lit :sentence sentence}))))

;; ---- the argument constraints a rule's variables carry -------------------
;;
;; `args-problem` holds a **ground** argument to what its position declares.  Every
;; argument of a rule is a variable, so that arm passes over all of them vacuously and
;; the rule is stored — and then each fact the rule concludes is convicted one at a
;; time, by a complaint naming the conclusion and never the rule that wrote it.
;;
;; A variable is one term standing in several positions at once, though, so the
;; positions can be held to **each other** before anything fires.  A variable an
;; antecedent binds through `(arg comment 2 string)` and a consequent places
;; into `(genl ?x ?string)` has to be a run of text and a type at the same time, and
;; text and a type are declared disjoint: no term is both, so every firing of that rule
;; would conclude something the entry point refuses.  The rule is the mistake, and this is
;; where it is said.
;;
;; **A type-level position asks for a type, which is a `unary_predicate`.**  That is the
;; second reading this arm needs and the KB already holds it twice over: every type is
;; asserted a `unary_predicate` when the schema loads, and `declaration-problem` refuses
;; an `arg` declaration on a `type_relation_predicate` precisely because *its* arguments
;; name kinds.  So a position is type-level when a `genlArg` names it **or** when its
;; predicate is a `type_relation_predicate` — which is how `genl`'s second argument is
;; constrained at all.  That position carries no declaration of its own, deliberately
;; (see CxCore), and the relation kind is what says what it holds.
;;
;; **Instance constraint against instance constraint, and nothing else.**  `(disjoint T
;; U)` says the two types share no instance, which is exactly what two such constraints
;; on one variable ask of it — the reading `args-problem` gives a ground term, asked of
;; a term that is not there yet.  Two *subtype* constraints are left alone: a type below
;; two disjoint types is empty rather than impossible, and nothing else in the KB
;; refuses an empty type.
;;
;; **Positive literals only.**  A negated antecedent says the variable does not fill
;; that position, so a constraint carried there is one no binding ever has to satisfy;
;; reading it would refuse `(implies (and (dog ?x) (not (plant ?x))) …)` for saying
;; exactly what its author meant.  An existential is skipped for the reason its
;; variables are local: what it binds inside is not the variable the rest shares.
;;
;; **`arg` and `genlArg`, and the other two kinds are not an extension waiting to be
;; made.**  `declaration-queries` reads four; this arm reads two, and the missing pair is
;; a *result* rather than a scope decision — each has a binding both ends accept, so
;; refusing the rule would refuse one that works.
;;
;;   - `quotedArg` × `arg`, and `quotedArg` × `quotedArg`.  Bind a **compound**.  It is
;;     the one thing `value-kind` declines to answer for, so both sides read it
;;     open-world.  Every other leaf kind is named and therefore decided, so a compound
;;     is the whole of the escape — and it is an escape a `result` read at check time
;;     rather than at mint would close for an unreifiable function, which is the one way
;;     these verdicts could still move.  With
;;     `symbol` on the `quotedArg` side there is no tension to begin with: a symbol is
;;     what every term the `arg` side types is written as.
;;   - `quotedArg` × a type-level position.  A string value serves here, `(genl "Bob"
;;     thing)` being admitted — `genls-problem` still exempts a value outright, which
;;     is its own question (a value is never a subtype of anything).
;;   - `interArg`.  Its trigger is a *demand*, not a fact.  `(arg P i T)` does not make
;;     argument `i` a `T` — an unclassified term satisfies it vacuously — so no rule's
;;     own bindings entail the trigger, and a conditional constraint that never provably
;;     fires can convict nothing.
;;   - `arg` × `genlArg` beyond the `unary_predicate` mapping below.  A term may be an
;;     instance of one type and a subtype of another at once; the meta-ontology depends
;;     on it, every type being an instance of `unary_predicate`.
;;
;; Each of those has a witness in `rule_variable_arg_test`, so an extension has to turn
;; one red before it can land.  docs/taxonomy.md carries the same list for a reader.

(def ^:private collection-type
  "The type a **type-level** argument position asks its filler to be an instance of.
  Every type in the KB is asserted a `unary_predicate` as the schema loads, so this is
  what `genlArg`'s \"a subtype of T\" and `type_relation_predicate`'s \"relates kinds\"
  both amount to as a membership — and a membership is what `disjoint` separates."
  'unary_predicate)

(defn- binding-literals
  "The literals of rule `inner` that **bind** its variables: every positive antecedent,
  plus the consequent."
  [inner]
  (conj (into []
              (remove #(or (sx/negation? %) (sx/unknown? %) (sx/there-exists? %)))
              (rules/antecedents inner))
        (rules/consequent inner)))

(defn- literal-variable-constraints
  "The memberships one literal demands of the variables sitting in its arguments, as
  `[[variable {:type T :position n :pred P :via V :level :arg|:genlArg|:kind}] …]`.

  Two sources, and they are the two readings a position can carry.  An `(arg P n T)`
  declaration types the filler directly.  A **type-level** position — one a `genlArg`
  names, or any position of a `type_relation_predicate` — types it as a
  `unary_predicate`, since what stands there is a kind.  `:level` is kept so the refusal
  can say which reading it read, and `:via` so a constraint that descended from a
  super-predicate names the predicate it was written of, exactly as `args-problem` does.

  Walked in `in-content-order`, so which declaration a refusal names is decided by what
  the KB says rather than by how the retrieval happened to enumerate.

  A literal whose **functor is itself a variable** contributes nothing.  `?pred` names no
  predicate, so `declaration-reader` reads it as a match pattern and every `(arg P n T)`
  in the KB comes back — `(arg typeToInstancePred 2 instance_relation_predicate)` beside
  `(arg instantNotEqual 2 time_point)` — and the conjunction of two unrelated predicates' position 2
  is a demand no term meets.  A variable functor is refused `:not-indexable` where it
  stands as a top-level antecedent (`rules.clj`) and is filled by a generator's hole
  otherwise, so the declarations that bind it are the stamped rule's, read when the
  functor is ground."
  [kb lit context]
  (let [pred (nm/functor lit)
        as   (vec (nm/args lit))]
    (when (and (sequential? lit) (symbol? pred) (not (sx/variable? pred))
               (some sx/variable? as))
      (let [decls    (declaration-reader kb pred context)
            type-rel (seq (res/matches-visible kb (list 'type_relation_predicate pred) context))
            of-kind  (fn [kind mk]
                       (for [m     (in-content-order (decls kind))
                             :let  [b (nth m 1)
                                    n (get b '?n)
                                    a (arg-at as n)]
                             :when (and (sx/variable? a) (symbol? (get b '?type)))]
                         [a (mk m b n)]))]
        (concat
         (of-kind 'arg
                  (fn [m b n] {:type (get b '?type) :position n :pred pred
                               :via (declared-of m) :level :arg}))
         (of-kind 'genlArg
                  (fn [m _ n] {:type collection-type :position n :pred pred
                               :via (declared-of m) :level :genlArg}))
         (when type-rel
           (for [[i a] (map-indexed vector as)
                 :when (sx/variable? a)]
             [a {:type collection-type :position (inc i) :pred pred
                 :via pred :level :kind}])))))))

(defn- variable-constraints
  "`variable -> [{…} …]` over `literals`, in literal order — the whole of what a rule's
  own text says its variables have to be."
  [kb literals context]
  (reduce (fn [acc lit]
            (reduce (fn [acc [v c]] (update acc v (fnil conj []) c))
                    acc
                    (literal-variable-constraints kb lit context)))
          {} literals))

(defn- variable-constraint-clause
  "How a refusal names one constraint it found — **a string (arg 2 of
  comment)**, or **a type (arg 2 of genl, a type_relation_predicate)** for a position
  whose demand comes from the relation kind rather than from a declaration.  Carries
  `via-clause` for a constraint that descended from a super-predicate, exactly as
  `args-problem`'s message does."
  [{:keys [type position pred via level]}]
  (str (case level
         :arg     (str "a " type)
         :genlArg "a type"
         :kind    "a type")
       " (arg " position " of " pred
       (case level
         :genlArg (str ", constrained with genlArg" (via-clause via pred))
         :kind    ", a type_relation_predicate"
         (via-clause via pred))
       ")"))

(defn- variable-clash-problem
  "The first pair of constraints on one of rule `inner`'s variables that no term
  satisfies at once, or nil.

  Only two **instance** demands can convict: `disjoint` says two types share no
  instance, and a membership is what each of these constraints asks for — the
  `unary_predicate` a type-level position asks for included.  Variables are taken in
  name order and each one's constraints in literal-then-content order, so a rule
  several of whose variables clash is refused for the same one every time."
  [kb inner context]
  (let [taxo   (reasoning/taxonomy kb)
        by-var (variable-constraints kb (binding-literals inner) context)]
    (first
     ;; `name-key`, not `str`: a rule variable is a symbol, and saying so is what keeps
     ;; the key out of the class an ambient `*print-length*` can collapse
     (for [v     (sort-by nm/name-key (keys by-var))
           :let  [cs (get by-var v)]
           :when (< 1 (count cs))
           [i a] (map-indexed vector cs)
           b     (drop (inc i) cs)
           :when (and (not= (:type a) (:type b))
                      (tax/disjoint? taxo (:type a) (:type b) context))]
       {:type :arg-variable :sentence inner :variable v
        :expected [(:type a) (:type b)]
        :message (str "arg constraint: " v " must be " (variable-constraint-clause a)
                      " and " (variable-constraint-clause b)
                      ", and the two types are disjoint")}))))

(defn- check-variable-constraints!
  "Throw when a variable of rule `inner` carries two argument constraints no term can
  satisfy together.  The value form is `variable-clash-problem`; this is the entry point's.

  Private, unlike the cross-namespace rule checks beside it in `check-rule!`: every
  entry point that stores a rule reaches this through that list, so there is no second caller
  for a public name to serve."
  [kb inner context]
  (when-let [p (variable-clash-problem kb inner context)]
    (throw (ex-info (:message p) (dissoc p :message)))))

;; ---- generators: the refusals a rule concluding a rule owes ---------------
;; A generator is a rule and passes everything a rule passes.  What follows is what it
;; owes *as* a generator, and every one of them is asked of each nesting level, since a
;; stamped rule may stamp one in turn and each level reaches the store as a rule in its
;; own right (docs/generators.md).

(defn- stored-generators
  "Every stored generator, as `[handle sentex]` pairs.

  One index lookup, and the cell it reads is the one that looks like a junk posting:
  `rules/consequent-predicate` reads the functor of what a rule concludes, and what a
  generator concludes is a rule — so every generator in the KB is filed under `implies`
  and nothing else is, at any nesting depth.  Nothing backward-chains through it (a
  generator is forward-only, and no goal's functor is `implies`), which leaves it doing
  exactly this one job.

  **Content-ordered**, because `generator-cycle` names one of these in a refusal
  message — verbatim, by handle.  The index cell is a *set*, so where three generators
  each close the cycle, an unordered walk would blame whichever the set yielded first,
  which is the arrival order that whole check exists to keep out.  One list per KB, and
  a generator roster is a handful of rules.

  **As stored, and a defeated generator is listed** — the entry point is the as-stored one on
  purpose.  What reads this is `generator-cycle`, a stratification refusal, and a cycle is
  a property of what the KB has *written*: a generator whose support is withdrawn is
  retained and revivable, so filtering it out would accept a program today and refuse it
  after a retraction somewhere else revives the rule that closes the loop.  A refusal that
  moves with belief is a refusal nobody can act on."
  [kb]
  (nm/sort-by-content-key
   (fn [[_ s]] [(sx/sentence-of s) (:context s)])
   (into []
         (comp (keep (fn [h] (when-let [s (p/get-sentex (:records kb) h)] [h s])))
               (filter (fn [[_ s]] (rules/generator-sentex? s))))
         (reads/as-stored-rules-by-consequent (:index kb) sx/rule-functor))))

(defn- stamped-predicate
  "The predicate a generator eventually concludes — the **innermost** rule's, through
  however many levels of stamping stand between.  The levels in between conclude rules,
  and nothing reads a sentence under the `implies` key as a fact; what reaches the fact
  store is the innermost conclusion, so that is the predicate a cycle can run through."
  [sentence]
  (rules/consequent-predicate (rules/innermost-rule sentence)))

(defn- generator-reads
  "The predicates whose arrival makes this generator **stamp** — the antecedents of
  every level but the innermost.  The innermost rule's antecedents are excluded on
  purpose: they trigger the rule that was stamped, which concludes a fact, and a fact is
  not what makes the rule set grow."
  [sentence]
  (into #{} (mapcat #(keep nm/functor (:antecedents %)))
        (butlast (rules/nesting sentence))))

(defn generator-cycle
  "A description of the cycle adding this generator would put in the rule set, or nil.

  The graph is generators only, and one hop: an edge runs from a generator to any
  generator that reads — in an antecedent it stamps from — the predicate its stamped
  rule concludes.  A cycle there is a rule set that mints rules that mint rules, and
  unlike ordinary recursion nothing bounds it: each round adds *rules* rather than
  facts, and the next round's rules are the ones the last round wrote.

  Refused outright rather than depth-capped.  A cap would make the KB's contents a
  function of how long the chainer happened to run, and \"how many rules does this KB
  have\" would stop having an answer — the same call stratification makes for a cycle
  through negation (docs/exceptions.md).  It is also why *nesting* is not a cap worth
  having: a nested generator stamps one level further before it stops, and what makes a
  rule set unbounded is the cycle, not the depth.

  **Both directions, because either can be the new edge**: the arriving generator may
  stamp what a stored one reads, or read what a stored one stamps, and a self-loop is
  the case where it does both to itself.  Checking only one direction would let the
  cycle in whenever the two generators were asserted in the other order — which is the
  order dependence every check here exists to keep out."
  [kb inner context]
  (when (rules/generated-rule (rules/consequent inner))
    (let [stamps (stamped-predicate inner)
          reads  (generator-reads inner)
          gens   (stored-generators kb)
          where  (or (when (and stamps (reads stamps)) "itself")
                     (some (fn [[h s]]
                             (when (and stamps (contains? (generator-reads (sx/sentence-of s))
                                                          stamps))
                               (str "the generator at handle " h)))
                           gens)
                     (some (fn [[h s]]
                             (when-let [p (stamped-predicate (sx/sentence-of s))]
                               (when (reads p)
                                 (str "the generator at handle " h ", which stamps "
                                      p))))
                           gens))]
      (when where
        (str "the rule it generates concludes " stamps
             ", and that predicate is read by " where
             (when context (str " (asserting into " context ")")))))))

(defn check-generator!
  "The three refusals that are a **generator**'s alone — a rule whose consequent is a
  rule (docs/generators.md).  Everything else it must satisfy it satisfies as a rule,
  through the list below.

  **Forward-only.** A generator's conclusion is a rule, and there is no backward goal
  whose answer is one — `concluding-rule-handles` reads a goal's predicate, and a
  generator's consequent predicate is `implies`, which names nothing a query asks for.
  A `set/backwardRule` generator would therefore be stored claiming a capability it
  cannot exercise, which is the accepted-and-inert state the indexability refusal
  exists to keep out of the KB.  `:inert` stays legal: it claims nothing.  Asked of
  **every** generator level, since a `set/backwardRule` around a middle level would be
  minted as a backward generator and refused one firing later, in the ledger rather
  than at the sentence.

  **No `exceptWhen` on a stamped rule.** An exception is not a rule field — it is a
  separate meta-sentex keyed by the rule's handle, split off and stored by the assert
  path (`assert-exceptWhen-meta!`), which a firing does not run.  So a stamped
  `exceptWhen` would reach the store as nothing at all: the mint would be a rule whose
  guard had silently evaporated, firing on exactly the bindings its author wrote it not
  to.  A guard that is dropped in silence is worse than one refused, so it is refused.
  An `exceptWhen` on the **outermost** rule is a different and legal thing — it says
  when not to stamp — and the message points there.

  **No generator cycle.** A stamped rule whose conclusion feeds some generator's
  antecedent is a rule set that mints rules that mint rules, with no fixpoint anybody
  has bounded.  Refused outright rather than capped, the same call stratification makes
  for a cycle through negation: the alternative is a KB whose size depends on how long
  the chainer was allowed to run.

  Read by both storage entry points through `check-rule!`, so a generator a *firing* stamps
  owes exactly what one an author wrote owes — which is the whole of what makes nesting
  safe: the middle level is checked twice, once as a pattern and once as the rule it
  became."
  [kb sentence context]
  (let [inner  (rules/inner-rule sentence)
        levels (rules/nesting sentence)
        ;; `peel-rule-wrapper` reports the wrapper it found, and a bare rule has none —
        ;; the record's default is what nil means here, as it does at the constructor.
        ;; Every sentence this runs on is a generator, and a bare generator defaults to
        ;; :forward at the constructor (a backward generator is meaningless), so nil is
        ;; :forward here.  A level's own wrapper rides the consequent of the level above
        ;; it, which is where a stamped rule's direction is written.
        dirs   (cons (or (first (sx/peel-rule-wrapper sentence)) :forward)
                     (map #(or (first (sx/peel-rule-wrapper (:consequent %))) :forward)
                          levels))]
    (doseq [[i level dir] (map vector (range) levels dirs)
            :when         (:generated level)]
      (when (seq (nth (sx/peel-rule-wrapper (:consequent level)) 2))
        (throw (ex-info (str "the rule a generator generates cannot carry an exceptWhen:"
                             " an exception is stored as a meta-sentex against the rule's"
                             " handle, and a firing has no way to split one off, so it"
                             " would be dropped in silence.  Put the condition in the"
                             " generated rule's antecedents as an (unknown …), or put the"
                             " exceptWhen on the outermost rule to say when not to"
                             " generate")
                        {:type :not-well-formed :sentence sentence :context context
                         :nesting-level (inc i)})))
      (when-not (contains? #{:forward :both :inert :forward-only} dir)
        (throw (ex-info (str "a rule generator is forward-only: its conclusion is a rule,"
                             " and no backward goal asks for one.  Drop the"
                             " set/backwardRule wrapper — the wrapper on the innermost"
                             " rule is what sets that rule's direction")
                        {:type :not-indexable :direction dir :sentence sentence
                         :nesting-level (inc i)}))))
    (when-let [cyc (generator-cycle kb inner context)]
      (throw (ex-info (str "a rule generator cannot generate a rule that feeds a"
                           " generator: " cyc
                           " — each round of that loop stamps the rules the next round"
                           " reads, so nothing bounds the rule set.  Assert one of those"
                           " rules directly instead of generating it")
                      {:type :not-stratified :sentence sentence :context context
                       :cycle cyc})))))

(defn check-rule-shape
  "The refusals of `check-rule!` that read nothing from the KB, in its order: a `do/`
  imperative anywhere in the rule, an `or` no expansion removes, a consequent variable no
  antecedent binds, an open NAF literal, and a variable antecedent functor on a rule that
  is not `:inert` (an inert rule runs in neither engine, so the index owes it nothing).
  `check-rule!` runs this first, and a dump import runs it over each rule frame, which
  may not read the KB: a declaration or rule the frame depends on may arrive later in
  the stream (docs/naming.md)."
  [sentence]
  (let [inner       (rules/inner-rule sentence)
        [direction] (sx/peel-rule-wrapper sentence)]
    ;; on the sentence **as written**, not on `inner`: `inner-rule` peels the
    ;; `exceptWhen` wrapper and takes the exception query with it, so guarding the
    ;; inner rule let an imperative through in the one rule slot that is re-evaluated
    ;; most often
    (check-no-imperative sentence)
    (check-no-defeat sentence)
    ;; An `or` the polycanonicalization can expand away is gone by the time `assert` or
    ;; the mint reaches here, since both store the *expansion*.  What is left is the rule
    ;; that could not be expanded: one over `rules/max-alternatives`, or one whose `or`
    ;; sits where nothing expands it.  The assert entry point refuses it at the shape
    ;; guard, before the split; the mint and the import have only this list.
    (rules/check-disjunction! sentence)
    (rules/check-range-restricted (rules/antecedents inner) (rules/consequent inner))
    ;; The NAF-literal checks — closure, quantifier locality, the reduction slot, a
    ;; quantified or empty conjunction.  The sentex constructor runs these too; here
    ;; they run before anything is built, so `core/check`, which constructs no sentex,
    ;; predicts them.
    (sx/check-naf-closed (rules/antecedents inner) (rules/consequent inner) nil)
    (when-not (= :inert direction)
      (rules/check-indexable-functors inner))))

(defn check-rule!
  "Every pre-storage check a rule must pass, as a step that writes nothing.

  **Two entry points store a rule** and this is the list both read.  `core/assert` stores one
  an author wrote; a generator firing stores one the KB derived
  (docs/generators.md).  What a rule has to *be* does not depend on which entry point it came
  through, so a copy per entry point is the drift this exists to prevent — a check added at
  the assert entry point that the mint never learned would let the fixpoint store what the
  API refuses.

  Factored out of the assert path so `assert` can also run it over **all** the
  conjuncts of a polycanonicalized rule before storing *any* of them.
  `(implies A (and C1 C2))` is split into one rule per conjunct and then `mapv`d,
  and a `mapv` is not a transaction: with the checks inline, a refusal on C2 leaves
  C1 already stored, indexed, and chained from, while the caller sees a throw and
  reasonably concludes nothing was asserted.

  One arm here has no counterpart on the fact path at all —
  `check-variable-constraints!`, which holds a rule's shared variables to the argument
  constraints of every position they stand in.  A ground argument is checked by
  `constraint-checks` on the way in; a variable is checked here or nowhere, since the
  term it will hold does not exist yet.

  A **generator** owes three more (`check-generator!`), and they run last so the
  sharper complaint comes first: a rule that is unbound *and* backward-only is refused
  for the unbound variable, which is the one its author can act on."
  [kb sentence context]
  (let [inner (rules/inner-rule sentence)]
    (check-rule-shape sentence)
    (nm/check! (:naming kb) inner context)
    ;; the argument constraints the rule's own variables carry, checked against each
    ;; other — the arm above this file's `binding-literals` explains.  Here rather than
    ;; on the fact path because a variable is not an argument any ground check can see,
    ;; and after naming because it reads declarations off the functors naming just
    ;; passed.
    (check-variable-constraints! kb inner context)
    ;; the rule-set check, before anything is stored: an `exceptWhen` is negation as
    ;; failure, and a cycle through it would make the settled state depend on
    ;; arrival order (docs/exceptions.md)
    (check-stratified kb sentence inner context)
    (when (rules/generator? sentence)
      (check-generator! kb sentence context))))

(defn rule-violation
  "`check-rule!` as a **value** in the form the derivation path files — a
  `{:violation :detail}` map, or nil when the rule stands.

  The mint's form of the same list, and the reason it is a value is the reason every
  check on that path is: a firing runs inside the fixpoint, an exception escaping it
  would leave belief half-computed, and which rule happened to fire first would decide
  what the KB ends up believing.  So a mint that cannot stand is dropped and recorded
  (`violations/report`), never thrown.

  Read through the throwing form rather than restating it, so the two cannot drift —
  the same trick `core/check` plays to predict `assert`."
  [kb sentence context]
  (try (check-rule! kb sentence context) nil
       (catch clojure.lang.ExceptionInfo e
         ;; `:sentence` and `:context` are dropped because the caller re-attaches its
         ;; own — the mint's, which is the rule that was actually refused — and a
         ;; stale copy under the same key would shadow it.  They come off in a step of
         ;; their own, and the type keyword last: the refusal-vocabulary scan reads
         ;; the token *following* a type keyword as a refusal type, so listing them in
         ;; one `dissoc` files whichever argument happened to sit there as caller-visible
         ;; vocabulary (`type_contract_test`).
         (let [d      (ex-data e)
               detail (dissoc d :sentence :context)]
           {:violation (get d :type :not-well-formed)
            :detail    (assoc (dissoc detail :type) :message (.getMessage e))}))))

(defn check-exceptWhen-stratified
  "Throw unless adding an exceptWhen exception mentioning `new-exc-preds` to the stored
  rule `rule-handle` leaves the rule set stratified.

  The exception is a new negative edge from the rule to those predicates, so it can
  close a cycle through negation exactly as a whole rule can (`check-stratified`).  The
  pending node is the rule's stored graph node augmented with the new negative edges;
  `stratification-readers` swaps it in for the stored rule so the walk sees the edge.
  Runs before the meta-sentex is stored, so a refused exception leaves nothing behind."
  [kb rule-handle new-exc-preds context]
  (when-let [rsx (p/get-sentex (:records kb) rule-handle)]
    (let [base    (rule-graph-node kb rule-handle rsx)
          pending (assoc base
                         :label           (str "rule#" rule-handle " (with the new exception)")
                         :exception-preds (concat (:exception-preds base)
                                                  (negative-predicates (:antecedent-preds base)
                                                                       new-exc-preds)))]
      (when (seq (:exception-preds pending))
        (when-let [cycle (wff/negation-cycle (reasoning/taxonomy kb)
                                             (stratification-readers kb pending)
                                             pending)]
          (throw (ex-info (str "not stratified: the exception on rule#" rule-handle
                               " reads " (pr-str (vec new-exc-preds)) " and would close a"
                               " cycle through negation: " (wff/cycle-description cycle)
                               " — a rule set is stratified when no predicate reaches"
                               " itself through a negative edge, so guard the rule with"
                               " an antecedent instead, or write the exception over a"
                               " predicate off that path")
                          {:type :not-stratified :rule rule-handle :context context
                           :exception-preds (vec new-exc-preds) :cycle cycle})))))))

(defn check-closed-extent-stratified
  "Throw unless declaring `(closed_extent_predicate P)` leaves the rule set stratified.

  The grant is what turns a closed `(not (P …))` antecedent from a lookup into negation
  as failure, so it adds a negative edge to every stored rule carrying one — and can close
  a cycle through negation exactly as a `genl` edge arriving underneath stored rules can
  (`check-edge-stratified`).  Nil for anything that is not the declaration.

  Complete without a wholesale walk: the edge it adds leaves precisely the rules with a
  `[:not P]` antecedent, which the antecedent index names in one lookup, so each of those
  is the start node and every cycle the grant could close passes through one of them.
  Walked in content order, so two rules that each close a cycle give one refusal rather
  than whichever was asserted first.

  Runs before anything is written, so a refused grant leaves no mark, no posting and no
  cycle."
  [kb sentence context]
  (when (and (= 'closed_extent_predicate (nm/functor sentence)) (= 2 (count sentence)))
    (let [pred (second sentence)]
      (when-let [[node cycle]
                 (->> (reads/as-stored-rules-by-antecedent (:index kb) [:not pred])
                      (keep (fn [rh]
                              (when-let [rsx (p/get-sentex (:records kb) rh)]
                                (when (and (rules/rule? rsx)
                                           (seq (rules/closed-negative-antecedents
                                                 (:antecedent rsx))))
                                  [rh rsx]))))
                      (nm/sort-by-content-key (fn [[_ rsx]] [(sx/sentence-of rsx) (:context rsx)]))
                      (keep (fn [[rh rsx]]
                              (let [base    (rule-graph-node kb rh rsx)
                                    pending (assoc base
                                                   :label (str "rule#" rh
                                                               " (under the closed extent)")
                                                   :exception-preds
                                                   (concat (:exception-preds base)
                                                           (negative-predicates
                                                            (:antecedent-preds base) [pred])))]
                                (when-let [c (wff/negation-cycle
                                              (reasoning/taxonomy kb)
                                              (stratification-readers kb pending)
                                              pending)]
                                  [pending c]))))
                      first)]
        (throw (ex-info (str "not stratified: " (pr-str sentence)
                             " would close a cycle through negation: "
                             (wff/cycle-description cycle)
                             " — the grant reads every closed (not …) antecedent on that"
                             " path as negation as failure, so leave the predicate open,"
                             " or break the cycle at one of the rules named")
                        {:type :not-stratified :sentence sentence :context context
                         :rule (:id node) :cycle cycle}))))))

(defn- edge-negation-cycle
  "The cycle through negation that adding this `genl` sentence would create among the
  **stored** rules, or nil.  Nil for anything else: a `genlCx` edge moves no edge of the
  graph, which reads the `genl` closure alone.

  `wff/genl-negation-cycle` walks once, from the rules the edge's added graph edges point
  to, so the check reads what the edge reaches and nothing else (docs/exceptions.md, \"A
  taxonomy edge closes a cycle too\").

  **Fast path:** no stored rule carries a negative edge (`negative-edge-rules`), so the
  graph has none and no walk can find a cycle.  That is every rule in the bundled
  starter, so an ordinary `genl` assert pays two set reads and stops.

  The edge is added to a **detached copy** of the taxonomy rather than to the real
  one: the check runs before anything is written, and a refused edge must leave the
  cached closures untouched as well as the store."
  [kb sentence]
  (when (and (= 'genl (nm/functor sentence)) (seq (negative-edge-rules kb)))
    (let [[_ a b] sentence
          probe   (tax/detached-copy (reasoning/taxonomy kb))]
      (tax/add-genl probe a b ::probe)
      (wff/genl-negation-cycle probe (stratification-readers kb) a b))))

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
                         " would close a cycle through negation: "
                         (wff/cycle-description cycle)
                         " — the edge fans each rule's negative dependencies over the"
                         " specs below it, so break the cycle at one of the rules named,"
                         " or place the edge under a type off that path")
                    {:type :not-stratified :sentence sentence :context context
                     :cycle cycle}))))

;; (`wff-violation` — structural well-formedness as a value, for derived content —
;; lives in `vaelii.impl.special` now: the per-functor wff dispatch is a column of
;; the special-predicate table, which sits a layer above this namespace.)

(defn edge-stratification-violation
  "The same check as a **value**, for a `genl` edge a rule *derived*
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

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :K8 :label "Storable classes" :kind :cache :keyed-by :value :reads [] :retired-by {}
  :computed :read :imaged? false :var #'storable-class-cache
  :value (fn [_] storable-class-cache)
  :note "class to whether a value of it can be stored; content-keyed, bounded by the classes seen"})
