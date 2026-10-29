# Assertive argument types: `arg` as an entailment

- **Covers:** how, by default, an argument constraint — `arg`, `argArg`, `genlArg`,
  `interArg`, `interArgEqual`, the covering and the homogeneity forms — derives the type it names as a derived, justified,
  retractable sentex and refuses nothing on a membership; the pass that records those
  derivations over a store loaded without them.
- **Not here:** `arg` / `genlArg` read as a constraint that rejects a wrongly-typed
  argument (the opt-out `VAELII_ASSERTIVE_ARG_TYPES=0` reading) → [taxonomy.md](taxonomy.md); `transitiveInArg`,
  which carries a stated claim rather than a declared type across an argument →
  [inherit.md](inherit.md).
- **Assumes:** sentex, justification, context, `genl` → [glossary.md](glossary.md).

## Relation-wide declarations and the runtime boundary

`arg` (including `arg1` through `arg5`), `genlArg`, `quotedArg`, `interArg`, the
covering forms `args` / `argsGenl` / `argAndRest` / `argAndRestGenl` (below), and the
homogeneity forms `interArgs` / `interArgAndRest` (below) accept a `relation` as their
subject: either a predicate or a function. A function's declarations are enforced on the
inputs of every application of it, at any depth, and two readings run on each
application:

- **Where it sits**, the application is typed by its function's `result` / `genlResult`
  against the declaration of the position it fills — what it denotes
  ([nat.md](nat.md#typing-an-application-that-is-never-minted)).
- **Inside it**, each input is checked against the function's own `arg`, `genlArg`,
  `quotedArg`, `interArg` and covering declarations, with the function standing where the
  predicate stands at the top level. A well-typed input does not rescue an application
  whose result misses, and a result that reaches does not excuse an ill-typed input.

```clojure
(unreifiable_function InputGapFn)
(arg InputGapFn 1 integer)
(result InputGapFn thing)
(arg inputGapObserver 1 thing)

(inputGapObserver (InputGapFn 5))                 ; admitted
(inputGapObserver (InputGapFn "not-an-integer"))  ; refused :arg-type — the string is
                                                  ; arg 1 of InputGapFn, :application names
                                                  ; (InputGapFn "not-an-integer")
```

The refusal carries the arm's own `:type`, `:arg`, `:expected` and `:position` (the
position in the function), plus `:application`, the innermost application whose input
failed. The boundary of the inner reading:

- **No derivation.** No entailment is drawn for a nested input: a declaration arriving
  after the fact derives over the facts it finds by predicate, and nothing finds the
  applications of a function inside stored facts, so a nested derivation would be drawn
  in one arrival order and not the other. A nested input is convicted when it holds a
  type the taxonomy separates from the declared one, and an input with no visible type is
  no evidence. Under the entailing reading `assert` stores a nested symbol so convicted
  and `try-assert` refuses it, as at the top level; a nested value or application is
  convicted under both readings.
- **Terms, not formulas.** A connective's argument (a genuine `(not (P …))`) and a
  compound whose head the KB knows as a predicate are formulas, not applications, and
  are not read as one. A head the KB has not classified is read as a function.
- **A mention is not descended into.** A position a `quotedArg` declaration types holds
  the term written there, so an application in it is syntax, and neither its result nor
  its inputs are read. The same holds for the argument of a quoting predicate
  (`natFormula`, `rewriteOf`) and of a quoting function (`Quote`, `Quasiquote`). A
  quoting function's own declarations are still read over its application; only what it
  quotes is left alone.
  `quotedArg` itself judges a compound argument by its shape kinds
  ([what a quoted form is](#what-a-quoted-form-is)).
- **Reifiable and unreifiable alike.** `assert` mints a ground reifiable application into
  a constant before the checks run, and the constant carries the result types, not the
  inputs, so the inputs are read over the sentence as written, before the mint; a refused
  sentence leaves no constant behind. `check` does not mint, reads the same inputs
  structurally, and reaches the same verdict. A rule's applications are read when a
  firing's conclusion is admitted, on the derivation path, before the firing mints the
  application's constant ([nat.md](nat.md), "Derivation path").
- **Context-scoped.** The function's declarations are read from the asking context's
  vantage, like every definitional check: a context below the one they are written in
  inherits them, a sibling is not refused by them.

### A unary predicate carries no `arg` declaration

A unary predicate's `genl` edges conclude its argument's types, so a unary predicate
declares no argument position, and its argument's type is `thing`.
`(genl instance_relation_predicate binary_predicate)` concludes `(binary_predicate P)` from
`(instance_relation_predicate P)`. An `(arg instance_relation_predicate 1 binary_predicate)`
beside that edge would duplicate the `genl` hierarchy and add a second justification for
each `(binary_predicate P)` the edge concludes. Unary predicates give types; other
predicates require types. The stable-constraints rule of
[no silent side effects](oe-principles.md#no-silent-side-effects) applies to predicates of
arity 2 and up.

`ontology_test/every-position-of-a-shipped-arity-above-one-is-declared` reads every
`resources/kb/*.txt` file and fails on an `arg` declaration of a predicate whose stated
arity is 1.

#### What a unary predicate's argument meets

The `genl` edges place the argument, and the taxonomy's disjointness refuses a wrong kind:

| argument of `instance_relation_predicate` | what happens |
|---|---|
| a term reaching only `thing` | stored; the mark's edges place it under `binary_predicate`, `predicate` and `relation` |
| a relation whose kind is not yet stated | stored, and the mark supplies the kind |
| a `function` F | `try-assert` refuses it `:disjoint`, through the `(disjoint predicate function)` the partition of `relation` derives; `assert` stores it, and the settle weighs it against `(function F)` |

The arity policy reads the same way. With `(variable_arity P)` stored, `(binary_predicate P)`
derives `(fixed_arity P)` through its edges, and `(partition relation fixed_arity
variable_arity)` separates the two, so the two memberships are one contradiction, stored as
a clash in either arrival order.

`arity_vocabulary_test/a-predicate-only-classification-is-order-independent-of-the-arity`
compares the two orders of the arity and the mark on the whole closure rather than on an
acceptance, and `an-arity-alone-leaves-the-relation-kind-open` asserts the rows of the
table.

## The covering constraints: typing a variable-arity tail

`arg` and `genlArg` name one numbered position. A variable-arity relation whose tail
repeats one role has no largest position to name, and `(args R T)` types the whole
admitted tail instead: every accepted position of `R` is an instance of `T`. `(argsGenl R
T)` is the subtype reading — `argsGenl` to `genlArg` what `args` is to `arg`. `(argAndRest
R n T)` and `(argAndRestGenl R n T)` type position `n` and every later one, so a relation
whose head positions carry their own `arg` declarations and whose tail repeats one role is
typed exactly. `(args R T)` states what `(argAndRest R 1 T)` states, and a forward rule
in `core.txt` stores that `argAndRest` beside it.

What a position is declared to hold is read through one chokepoint,
`res/arg-constraints` (the whole list) and `res/arg-constraints-at` (the entries covering
one position). At the instance level it looks up `arg` and `argAndRest` alone: `args`
reaches it through the twin its rule stores, and the `argN` projections through the `arg`
theirs store. The type-level `genlArg`, `argAndRestGenl` and `argsGenl` and the quoted
`quotedArg` come back on the same entries under their own kind. `ArgTypeProver`, the
`predAllSpecified` audit, `kb-integrity`'s `:missing-arg` and `:genl-arg-widening` passes
and the rule-pair quality report read through it. The list is held for one stretch of the
change clock, so a read-only caller asking per fact reads the store once per predicate.
The assert-time checks look up the same two at the instance level: `args` is refused,
and derives memberships, through its stored `argAndRest` twin, whose handle is the support
an entailment names. Retracting the `args` takes the twin, and everything resting on it,
with it. A KB that does not load `core.txt` has no such rule, so there an `args`
declaration types nothing; state `argAndRest` instead.

A valid unbounded tail: a `variable_arity` `herd` with `(arityMin herd 2)` and `(args herd
animal)` accepts `(herd Rex Bossy)` and `(herd Rex Bossy Clarabelle)` and derives
`(animal X)` of every member, at whatever length the tail reaches.

Not every variable-arity relation has a homogeneous tail. `functionCorrespondingPredicate`
relates a function, its corresponding predicate, and an argument count — three positions of
three types — so no covering constraint fits it, and its positions take per-position `arg`
declarations. The covering forms serve the homogeneous case; they do not demand that a tail
be homogeneous, and the engine enforces neither preference.

Three properties hold, each of them `arg`'s:

- **Conjunctive with the singular forms.** A position-specific `(arg R n T)` and a covering
  `(args R U)` both bind position `n`; neither overrides the other, and an argument there is
  held to both `T` and `U`.
- **Descends the predicate hierarchy.** A covering declaration on a super-predicate binds a
  sub-predicate's tuples, read through the same declaration reader `arg` uses
  (`res/constraining-predicates`).
- **Derives, and convicts only a value.** Under the entailment toggle a covering
  constraint derives `(T x)` (or, for the subtype forms, `(genl x T)`) of every symbol in
  the tail, with `arg`'s four arrival directions, and convicts only a value or an
  application whose type misses. Under the constraint-only reading it derives nothing and
  convicts a tail symbol the KB places outside the type, with no retroactive reach.

The walk is over the positions a sentence has, not a re-counted tail. A tuple of a length
its relation's binding denies is stored and held inert in the `:out` forced set
([taxonomy.md](taxonomy.md#arity)); the covering check walks every position such a tuple
has.

## Constraint and entailment readings

`(arg parentOf 1 animal)` says the first argument of `parentOf` is an animal. Assert
`(parentOf Fred Mary)` and the KB checks that claim against what it knows about `Fred` —
and when it knows nothing, **passes and stores nothing**. The declaration is read as a
constraint to test, never as a fact to derive.

This is the other reading: the declaration also *entails* what it constrains, and the
entailment is a derived, justified, retractable sentex under truth maintenance.

```clojure
(v/assert kb '(genl animal thing) 'CxUniverse)   ; the declared type has to be one
                                                      ; the hierarchy holds — see below
(binding [argument/*assertive-arg-types?* true]
  (v/assert kb '(arg parentOf 1 animal) 'CxWorld)
  (v/assert kb '(parentOf Fred Mary) 'CxWorld))

(v/isa? kb 'Fred 'animal 'CxWorld)          ; => true
(v/why kb (v/handle-of kb '(animal Fred) 'CxWorld))
;; {:root 7
;;  :nodes {7 {:premise? false :support [{:informant arg :because [5 6]}]}
;;          5 {:sentence (parentOf Fred Mary) :premise? true}
;;          6 {:sentence (arg parentOf 1 animal) :premise? true}}}
```

**On by default** (`vaelii.impl.decide.argument/*assertive-arg-types?*`; the root value reads
`VAELII_ASSERTIVE_ARG_TYPES`, and `=0` opts out — how the whole suite is run under the
constraint-only reading). Entailing changes what a KB *contains*, not only what it
answers, so the constraint-only reading stays one `binding` away.

**An `arg`-family declaration may type an argument `thing`.** `(arg P n thing)` says that
position `n` holds a term of any kind and that no narrower type is right for it. It
rejects nothing under the constraint-only reading, and the entailing one derives nothing
from it: a membership in `thing`, or a `genl` edge to it, says nothing about the term
(`arity/mintable-type?`). `kb-quality` lists each such declaration under
`:typed-thing` with its predicate's stored extent, the facts a narrower type would type
([quality.md](quality.md)). The second slots of the happening-participant predicates `actor`,
`thingPerceived`, `doneBy`, `input`, `destroyedInput`, `preservedInput` and `output` are
such positions. Their bounds stay explicit on each predicate even where inherited, so a
parent's revision cannot silently change a child's declared constraint. A
`(genlArg P n thing)` declaration says position `n` holds a type, and the constraint-only
reading convicts an individual there. A position that holds a term taken as written
declares an expression type with `quotedArg`, as `(quotedArg comment 1 denotational_term)`
does.

**Both readings prove the same sentences over the shipped ontology.** A membership or
`genl` edge an argument declaration in `resources/kb/` derives is written in a KB file
where the constraint-only reading could not prove it otherwise, so a derivation the
entailment stores is a copy of a sentence a context it sees already holds, or a
membership `provers/ArgTypeProver` answers
(`starter_test/the-constraint-only-reading-proves-every-sentence-the-entailment-derives`).

### The open membership goal

`provers/ArgTypeProver` answers an open `(t ?x)` as well as a ground `(t X)`, and answers
the open goal exactly where the stored memberships do not cover the ground one. A
declaration `(arg P n T')` with `T'` at or below `t` is uncovered under the
constraint-only reading, which mints nothing, and under the entailing reading when
`arity/mintable-type?` refuses `T'`: `thing`, and a type an arity statement binds to
another length ([where it does not mint](#where-it-does-not-mint)). The check reads
`argument/*assertive-arg-types?*` at the call and the same `mintable-type?` the mint path
reads. For each uncovered declaration the prover reads the distinct individuals at
argument `n` of a stored fact of `P` or a predicate below it, stated in a context the
reader sees, and keeps those the ground test types `t`. An open answer therefore carries
the support the ground goal on its binding carries, and a conjunction joining `(t ?a)`
answers the same set in every conjunct order
(`provers_test/an-argument-typed-conjunction-answers-alike-in-every-conjunct-order`). Under
the entailing reading the stored-fact prover answers a mintable type's members, and the
two provers together answer what the ground test accepts
(`provers_test/stored-memberships-and-the-open-arm-answer-what-the-ground-arm-accepts`).

## What this is not

`provers/ArgTypeProver` already answers a ground `(animal Fred)` goal from exactly this
declaration — arg read as an inference is not new. What is new is that the type
becomes a **record**: a handle, a justification naming what it rests on, a place in the
taxonomy that `isa?` / `types-of` and the definitional checks read, and a datum the
agenda fires rules on. A prover's answer is none of those, and it is confined to a
CapitalCamelCase individual; `genlArg` entails a `genl` edge, which no prover can.

## An argument constraint derives; `try-assert` refuses a separated argument

With the toggle on, an argument constraint derives the membership it names, and `assert`
refuses no sentence on the memberships its argument holds (`checks/entailment-covers?`).
A declaration read as an entailment says Fred *is* an animal. The same holds of every kind
that types a symbol: `arg`, `genlArg`, `interArg`, the covering forms and the homogeneity
forms, from a declaration written in the asking context or inherited by it, and for a
declared type no `genl` edge places. When
Fred holds a type the taxonomy separates from `animal`, the derivation is a clash, and
`try-assert` refuses the sentence with `:definitional-clash` (`:violation :arg-type`,
[api.md](api.md#refusing-a-clash)).

A membership the declared type does not reach is a second membership beside the derived
one, not evidence against the sentence. `(achieves Ann Bee)` under `(arg accomplishes 2
tt)` and `(genl achieves accomplishes)` derives `(tt Bee)`; with `(genl tt assoc)` and an
inherited `(arg assoc 1 sub)` it derives `(sub Bee)` from that; and a second fact deriving
`(tt Bee)` adds a second justification. Each arrives as the first did, and re-asserting
the stored `(tt Bee)` stores it again
(`argtype_entail_test/two-facts-deriving-one-membership-are-both-stored-in-either-order`).

Two things still convict, because no membership can be derived of them:

- a **value**, which carries its type in its syntax — `5` is not a `string`;
- a **function application**, typed by its function's declared `result`.

The constraint-only reading (`VAELII_ASSERTIVE_ARG_TYPES=0`) derives nothing and convicts a
symbol holding a type the taxonomy separates from the declared one, as
[taxonomy.md](taxonomy.md) describes. A symbol whose types neither reach nor are separated
from the declared type is admitted: its other type is unknown, and an unknown type stands.

### An argument that fails its declared type is held inert

`assert` stores a fact an argument declaration convicts and holds it in the `:out` forced
set ([nmtms.md](nmtms.md#the-forced-monotonic-set)): the fact is never believed, forms
no nogood and fires no rule. The held convictions are `:arg-type`, `:arg-genl`,
`:inter-arg-type` and `:quoted-arg-type` that the entailing reading does not weigh: a value
under `arg`, an individual in a `genlArg` position, a symbol the constraint-only reading
convicts, and a kind outside a `quotedArg` type. The verdict is read off the stored state,
so the stored set and belief are the same whichever of the declaration, the fact and a
membership arrives first:

```clojure
(v/assert kb '(genl dog thing) 'CxUniverse)
(v/assert kb '(unary_predicate needs) 'CxUniverse)
(v/assert kb '(needs 5) 'CxUniverse)              ; stored and believed
(v/assert kb '(arg needs 1 dog) 'CxUniverse)      ; (needs 5) is held inert
(v/why-not kb '(needs 5) 'CxUniverse)
;; {:reason :inert :conviction {:type :arg-type :arg 5 :expected dog :position 1 …} …}
```

`violations` lists each held fact as `:inert-argument`, with the violation under
`:detail`. Retracting the declaration, or a membership or `genl` edge the conviction read,
releases the fact. `try-assert` refuses the write as `:definitional-clash`
([api.md](api.md#refusing-a-clash)).

A rule's conclusion the same conviction convicts is held the same way: the firing stores
the conclusion with its justification and holds it (`chain/place-fact-conclusion`,
`checks/constraint-admission`'s `:conviction`). A sentence a rule derives and a caller
asserts is one held sentex in either arrival order, and a `recover` decides its hold from
the stored sentex
(`refused_firing_test/a-convicted-firing-is-held-and-released-alike-live-in-place-and-over-a-fresh-open`,
`refused_firing_test/a-sentence-derived-and-asserted-is-held-alike-in-both-arrival-orders`).
A write that moves no hold reads none of the held conclusions (`lein perf --only
assert-beside-held-firings`).

The settle decides the hold again for every stored fact a write can move
(`checks/refresh-argument-holds!`): the tuples under a declaration stored, removed or
relabelled; under the constraint-only reading, the facts naming a term whose membership
moved; under a declaration naming a type a definition stored, removed or relabelled
reaches, the held facts and the convicted tuples; and, after a `genl`, separation or
`genlCx` move, the facts its ends reach, held or not; a held fact the ends do not reach is
not decided again (`lein perf --only genl-write-beside-held-facts`). The declarations
below the moved types with more specializations than the refresh walks (512) are found in
one pass over every declaration, with the types above each declared type walked once for
all of those ends, and a declaration below several ends is read once (`lein perf --only
genl-ends-above-deep-declarations`). The refresh logs progress lines per moved type and per
declaration, and a shutdown can stop an `assert` before each one, with the refresh's
queue left in place (`recovery_test/a-shutdown-stops-a-write-between-the-moved-types-a-holds-refresh-reads`). A
`genlCx` move reads only the tuples of the predicates a declaration constrains, stated at
or below the edge's context, and no other fact stated there (`lein perf --only
mints-under-context-edge`). Each
declaration is read per position it types, a covering form at every position from its
start, and only the atoms there that can be held are tested: under the entailing reading a
value, an individual in a `genlArg` position and a `quotedArg` term. Each test is memoized
per term kind and context for the pass, and per value where a `:monotonic` definition can
decide one, so a declared type's closure is walked once and
not once per atom (`lein perf --only recover-genlarg-types-down-a-chain`). The memo is
keyed by the declared kind and type, so the declarations naming one type share it, and
each predicate position's atoms are read once per pass. A recover
reads every declaration whole (`argtype_entail_test/a-value-argument-under-a-declared-type-is-inert-in-either-order`,
`argtype_entail_test/a-separated-symbol-argument-is-inert-in-every-order-under-the-constraint-reading`,
`quoted_arg_test/a-quotedarg-violation-is-inert-in-either-order`).

Three cases stay outside the hold:

- A declaration arriving after the fact reads the atoms at its position, so a compound
  argument there is decided only at the fact's own write. A `quotedArg` declaration also
  reads the compounds at its position, when its type is separated from some compound kind.
- A function application nested inside an argument is checked against its function's
  declarations at the write (`checks/check-application-inputs`), which refuses it. A
  rule's conclusion convicted the same way is dropped and reported in `violations`.
- A bulk load runs no argument check, so a bulk-loaded fact under a declaration already
  stored is held only when a later write moves its verdict.

**A real conflict is a clash, decided by belief.** A derived membership disjoint from one
the term holds is placed and weighed at settle, as a rule's conclusion is
(`checks/derivation-violation`): the stronger class wins, and an equal `:default` pair both
stay believed and are listed by `contradictions`. With `(disjoint relation collection)` and
`(arg p 1 relation)`, `(collection Foo)` and `(p Foo)` at `:default` leave both memberships
believed and the pair listed in every arrival order, and a `:monotonic` `(collection Foo)`
takes `(relation Foo)` OUT in every order. A declaration arriving over both, including one
a rule derives, derives and is weighed the same way
(`argtype_entail_test/a-minted-membership-clashing-with-a-believed-one-is-weighed-at-settle`).
A clash between two derivations of one cascade — `(p1 Fred)` and the `(p2 Fred)` it
entails — is found by the settle from the stored records in the same way.

A declaration whose type an arity statement binds to another length derives nothing. With
`t` declared binary, `(arg rel 1 t)` and `(rel Rex Mary)` store the fact and no `(t Rex)`,
and the declaration mints once the binding leaves
(`argtype_entail_test/a-type-bound-to-another-length-mints-nothing-and-records-nothing`,
[taxonomy.md](taxonomy.md#arity)).

**What the entry point still asks of the derivations.** `checks/entailment-check` walks the
whole cascade before anything is stored and refuses the sentence when a derivation is one
a definitional check refuses on its own syntax, with the derivation's violation and the
sentence in `:entailed-from`. Naming, well-formedness and edge stratification are asked of
each derivation as it is stored (`special/inadmissible`): a derived `(genl X T)` that closes
a taxonomy cycle is dropped and reported in `(violations kb)`, since the derivation runs
after the triggering sentex is stored and inside a fixpoint, neither of which may abort
halfway.

### A rule whose variable no term can fill is held inert

`assert` stores a rule that `checks/variable-clash-problem` convicts and holds it in the
`:out` forced set, as a fact above is held. A variable of such a rule stands in two
positions whose demands are separated types, so every firing would conclude a fact the
argument checks convict; [taxonomy.md](taxonomy.md#and-against-the-variables-of-a-rule)
states which demands the arm reads. The held rule is never believed, so it fires nothing
forward and answers no goal backward, and a firing it made while believed loses its
support. The verdict is read from the rule's own context off the stored state, so the
stored set and belief are the same in every arrival order of the rule, its declarations
and the separation
(`rule_variable_arg_test/a-rule-a-separation-convicts-is-held-in-every-arrival-order`, all
24 orders). A rule a generator or a `defn*` fact mints is held the same way
(`checks/hold-rule-conviction!`).

```clojure
(v/assert kb '(implies (comment ?x ?string) (genl ?x ?string)) 'CxUniverse)
(v/why-not kb '(implies (comment ?x ?string) (genl ?x ?string)) 'CxUniverse)
;; {:reason :inert :conviction {:type :arg-variable :variable ?string
;;                              :expected [string predicate] …} …}
```

`violations` lists the rule as `:inert-rule`, with the conviction under `:detail`. `check`
reports nothing. `try-assert` refuses the rule as `:definitional-clash` with `:violation
:arg-variable`, and refuses an `arg`, `genlArg` or `quotedArg` declaration that would
convict a stored, believed rule, naming the rule in `:clashes-with`
(`checks/rule-declaration-conflict`). Retracting a declaration or the separation the
conviction read releases the rule, and its firings come back IN.

The drain that decides the facts' holds decides the rules' too
(`checks/refresh-argument-holds!`). It reads the rules on the predicates a write names,
through both rule indexes (`checks/rules-on`):

- a declaration stored, removed or relabelled reads the rules on its predicate and the
  predicates below it;
- a `type_relation_predicate` membership stored or removed reads the rules on its member;
- a `genl` or separation move reads the rules on the predicates at or below an end that a
  declaration constrains, and on the predicates of each declaration naming a type at or
  below an end, with every rule on a `genlArg`-declared predicate or a
  `type_relation_predicate` when an end is at or above `unary_predicate`;
- a `genlCx` move reads the rules stated at or below the edge's context;
- a recover, and a move at a value kind, read the rules on every constrained predicate and
  on every `type_relation_predicate`.

A recover decides the holds in its rebuild settle, before a family reads a label
(`settle/*rebuilding?*`), so no step of it believes a fact or rule the live KB holds OUT
(`recovery_test/a-recover-holds-out-what-the-live-kb-holds-out-before-its-settle-reads-a-label`).

Each predicate's declarations are read once per context for the pass
(`checks/*pass-reads*`). Before a rule is read from its context, the pass reads its
variables' constraints as stored over every context and tests each pair unscoped with no
`siblingDisjointException` (`checks/clash-possible?`); a rule no pair there can separate
is not convicted at any context, and is decided without a scoped read. Two cases stay outside the hold: `try-assert` of a separation
or a `type_relation_predicate` membership that would convict a stored rule does not refuse
it, and a rule an equality merge restates (docs/equality.md) is decided only when a later
write reaches it.

## Where it lives

The **check computes it; the post-store slot materializes it.**

| | |
|---|---|
| `checks/constraint-entailments` | reads the declarations, returns `{:assert :because :position :kind}` maps — **writes nothing** |
| `checks/entailment-check` | walks the cascade of prospective mints at the entry point and refuses the first the KB could not admit — **writes nothing** |
| `special/deduce-arg-types` | materializes them, beside `deduce-lifts`, in `assert-entry/assert-one` and `chain/place-conclusion` |
| `special/deduce-below` | the declarations stated below the fact's context, at the placements of each pair |
| `special/entail-existing` | the retroactive direction: a declaration arriving over facts already stored |
| `special/entail-under-edge`, `special/entail-under-context-edge` | a `genl` or `genlCx` edge arriving over a fact and a declaration already stored |
| `special/triggered-mints` | a trigger membership of `interArg` or a homogeneity form arriving over a fact and a declaration already stored |
| `special/except-move-sweeps` | an `except` of an ingredient arriving or leaving |
| `argtype-pass/run-all`, `argtype-pass/run-pass!` (`v/record-arg-types`, `v/record-arg-types!`) | the pass over a store loaded without the derivations, in one call or stoppable and resumable ([below](#the-pass-over-a-stored-kb)) |

Not because a check may not cause a write — `special/deduce-lifts` is a check-shaped
declaration read that causes a justified write on this very path. The reason is
sequencing. `assert` runs its checks *before anything is written and before the taxonomy
is touched, so a refusal leaves nothing behind*, and at that moment the triggering sentex
does not exist: there is no `source-handle` to hang `[source-handle decl-handle]` on, so
the entailment is not merely inconvenient to mint there, it is inexpressible.

So `checks` gains a third *value* to return. It already had one problem read with two
dispositions — `constraint-checks` throws it, `constraint-violation` records it. The
entailment is a new consumer of the same pass: `constraint-checks` returns it on the
assert path, `constraint-admission` returns it beside the violation on the derivation
path, and one memoized `declaration-reader` serves the checks and the entailments alike,
so turning the feature on does not pay twice for the read `assert` calls its dominant
per-fact cost.

## The entailment, as a justified datum

`special/entail-arg-type` follows `deduce-lift` almost line for line:

* `kb/find-or-create-sentex` for the implied `(T arg)` at each placement of the fact and
  the declaration ([Where a mint is placed](#where-a-mint-is-placed));
* `derived-sentex-added` when it is new, so it reaches the closures and posts its
  exception re-check trigger exactly as a rule conclusion does;
* `jtms/->just` with antecedents **`[source-handle decl-handle & route-edge-handles]`**
  — the `genl` edges the declaration descends through and the `genlCx` edges the
  context sees it through — and the declaring predicate as the informant, guarded by
  `has-justification?`;
* depth one past the deepest of them;
* strength `:monotonic` conferred — the entailment adds no defeasibility of its own, so
  `conferred-class` caps it at the weaker of the fact and the declaration.

That is what makes it retractable. Drop the fact or drop the declaration and the type
goes, through machinery that already exists; defeat the fact and the type goes OUT with
it, because it is an ordinary derived node.

The edge handles are there because a constraint **descends the predicate hierarchy**
([taxonomy.md](taxonomy.md)): `(arg parentOf 1 animal)` entails `(animal Ann)` from
`(fatherOf Ann Mary)` under `(genl fatherOf parentOf)`, and that type is entailed only
while the subsumption is. Naming the fact and the declaration alone would leave it
standing after the edge was retracted — a derived record supported by content that no
longer entails it, which is the whole failure justifying an entailment is meant to
prevent. `checks/edge-support` names one supporter per edge on a shortest visible path,
the same witness rule everything else depending on a reachability takes. A shorter route
arriving after the entailment draws the pair again over itself, and that justification
replaces the one over the longer route (`special/drop-replaced-routes!`), so a pair holds
one justification in every arrival order ([nmtms.md](nmtms.md), "Where the layer stops",
states where replacement stops).

One named path is not the only path. With `pa → pb → pd` and `pa → pc → pd` both stated,
`(arg pd 1 tt)` over `(pa Xone)` names the route through `pb`, and retracting
`(genl pa pb)` deletes that justification while the route through `pc` still entails
`(tt Xone)`. The removal draws the entailment again from the taxonomy it left
(`special/rederive-descended`), for a cover on the route and for a trigger
membership as for a `genl` edge: the retraction path reads the justifications the sweep
deleted before it deletes their records (`special/edge-descended-justifications`), and a
settle that defeats an edge reads the derivations the edge took OUT
(`special/lost-descended-derivations`). Where a route survives, the type comes back resting
on it; where none does, nothing is drawn. The descended `functional` and `anti_symmetric`
equalities ([equality.md](equality.md)) name their routes the same way and are drawn again
by the same two arms.

## Four directions, or belief depends on arrival order

A declaration has to reach back over content already stored, or belief depends on which
of the ingredients arrived first. `decontextualized_predicate` lifts the facts already
present when it arrives, so `arg` has to as well — and with the descension and the
context hierarchy the ingredients are four rather than two, so there are four entry
points:

* **fact meets declaration** — `deduce-arg-types` for the declarations the fact's context
  sees and `deduce-below` for those stated below it, on `assert` *and* on
  `place-conclusion`, because what a declaration says is a claim about the predicate and
  not about how a sentence arrived;
* **declaration meets facts** — `entail-existing`, walking the predicate extents of the
  declared predicate's whole `genl` **spec** subtree, since the declaration binds every
  predicate beneath the one it names;
* **edge meets both** — `entail-under-edge`, walking the same subtree under the arriving
  edge's sub-predicate, and under each part of an arriving `covering`, `separating` or
  `partition`, which installs an edge per part (`tax/installed-edges`). It is the taxonomy
  twin of `entail-existing`, and there for the
  reason `subsumption-seeds` beside it is: the arriving datum is the *edge*, and nothing
  else on the assert path re-examines the facts it just brought under a declaration;
* **context edge meets both** — `entail-under-context-edge`, from the settle's drain of
  the `genlCx` moves ([contexts.md](contexts.md#one-context-move)), re-deriving the facts stored in the arriving
  `(genlCx sub super)` edge's `sub` and every context under it, since the edge makes the
  declarations above `super` visible to them, and the facts and declarations the edge
  gives a new common descendant ([Where a mint is placed](#where-a-mint-is-placed)). It
  reads the smaller of that extent and the extent of the declared predicates, by index
  counts, which `lein perf`'s `genlcx-edge-beside-declared-facts` holds.

Every order of {declaration, fact} reaches the identical KB, and so does every order of
{declaration, fact, edge}. Three regression tests enforce it:
`every-arrival-order-reaches-the-same-belief` runs all six orders of {declaration, fact,
a competing type}, `every-arrival-order-of-the-three-ingredients-mints-the-same-type`
runs all six of {declaration, fact, edge}, and
`every-arrival-order-derives-through-an-inherited-declaration` runs all 120 of {local
declaration, inherited declaration, predicate edge, context edge, fact}, with a sampled
twin at the default selector.

No member of the family refuses on a membership, so the **facts** a KB holds are the same
in every order as well as the derivations. The constraint-only reading holds a convicted
fact inert in every order
([held inert](#an-argument-that-fails-its-declared-type-is-held-inert), [taxonomy.md](taxonomy.md),
"What each constraint does in each arrival order").

**A type is a unary predicate, so a declared type mints by its arity.** `mintable-type?`
reads the declared type's own IN arity bindings, one read with no `genl` closure: a type
mints when no binding gives it a length other than one, no `variable_arity` releases it
and no `arityMin` floors it above one. A
declaration that mints also entails `(unary_predicate T)` of each type it names, justified
by the declaration alone (`special/entail-existing`), so the type's arity is stored beside
its first mints. A length `T` inherits through `genl` is not read.

A declared type an arity statement binds to another length mints nothing, and nothing
records the declaration: the stored declaration is the record. When the arity family's
refresh reports a type whose own bindings moved and whose length now admits one
(`arity/drain!`'s `:bound`), the settle reads the stored declarations naming the type and
runs `entail-existing` for each that has no `declaredType` justification of
`(unary_predicate T)`, which mints over every fact stored meanwhile
(`special/mints-on-lengths`). A `genl` or `genlCx` edge moves no type's own bindings, so it
reads no declaration; `lein perf`'s `mint-release-after-genl-move` bounds the settle after
a `genl` edge per waiting declaration. Until then the declaration reads none of its facts: every arm asks
`mintable-type?` of the declaration's own type before it draws, so the extent would yield
nothing.

An arity statement binding `T` to another length after the declaration has minted
withdraws the entailed `(unary_predicate T)` (`special/withdrawn-type-entailments`, in
the arity family's refresh) and leaves the declaration waiting on `T`, as it waits when
the statement arrived first. The same refresh drops the mint justifications concluding a
membership `(T x)` or an edge `(genl x T)` (`special/withdrawn-type-mints`), so a mint
the argument entailment alone holds up leaves the store, and a record with other support
stays under `T`'s length, inert ([taxonomy.md](taxonomy.md#arity)). Arriving first, the
statement leaves nothing minted, so both orders store the same records
(`absent_type_order_test/a-length-arriving-after-a-mint-removes-it-from-the-store`,
`clash_oracle_test/a-length-arriving-after-a-minting-declaration-reads-as-one-arriving-before-it`).

A type mints only when every IN length admits length one. With `(unary_predicate T)` and
`(binary_predicate T)` both IN, the binary binding gives `T` a length other than one, so a
declaration naming `T` mints nothing, and the binary binding arriving after a mint drops
the mint justifications as above. No order of the two bindings, the declaration and the
fact stores the mint, before or after `recover`
(`absent_type_order_test/a-type-with-two-in-lengths-mints-in-no-order`). The two lengths
stay one `contradicts` ([taxonomy.md](taxonomy.md#arity)).

`entail-existing` puts each stored sentex back through `constraint-entailments` in its
*own* context, narrowed to the arriving declaration (`checks/declaration-entailments`),
rather than re-deciding the conditions. The directions must agree about what a
declaration entails, and the only way to be sure of that is for them to ask the same
function. The narrowing hands the arms the arriving declaration's match alone, so the
other declarations on the predicate are not read per fact; `lein perf`'s
`arg-declaration-over-facts` holds a declaration over n facts to a cost per fact flat in
n beside a declared type whose ancestor set grows with n.

## The rules that govern what is drawn

### A declaration derives wherever it is visible

A declaration is visible in the context it is written in and in every context below it,
and it derives in each of them: a derivation is drawn in the context of the fact it is
drawn over, from every declaration that context sees, and a declaration stated where the
fact's context does not see it derives at the contexts that see both
([Where a mint is placed](#where-a-mint-is-placed)). A declaration the context inherits
rests on the `genlCx` edges through which the context sees it, as a declaration on a
super-predicate rests on the `genl` edges it descends through, so the justification is
`[fact, declaration, genl edges…, genlCx edges…]` (`checks/entailment-support`).
Retracting a `genlCx` edge on that path takes the derivation back, and a second path draws
it again (`special/rederive-descended`), as for a `genl` route.

The starter's `(arg parentOf 1 organism)` lives in CxUniverse (`life.txt`) while the individuals live in
`CxNaturalWorld`, below it, so a `parentOf` fact there derives `(organism X)` in
`CxNaturalWorld`. A toggle-on starter load derives a membership per declared position,
less the ones pruning withholds (the table under [Cost](#cost)). Each argument position
of arity 2 and up in the shipped ontology is declared, except the ones `ontology_test`'s
`undeclared-positions` names: the two `genl` positions and the example predicates' quoted
sentence. `core.txt` says why beside `genl`: `thing`
cannot be a proper subtype of itself, so the constraint the root would fail is the wrong
constraint rather than a missing one.

### Where a mint is placed

A mint is placed at each maximal context that sees every ingredient of its derivation with
no `except` hiding one, as a forward firing and a placed nogood are placed
(`special/pair-placements`). The ingredients are the fact, the declaration, the `genl`
edges of one route from the fact's predicate to the declared one, and for an `interArg` or
homogeneity declaration one trigger membership with its route. Where the fact's context
sees them all, that context is the one placement. Where it does not, the placements are the
maximal common descendants of the ingredients' contexts, taken over each uncovered route
(`tax/general-reach-supports`) and each trigger, keeping the most general, and each mint's
justification names the route and the `genlCx` edges its placement sees the fact through.
While an `except` hides an ingredient somewhere, each placement is the maximal context
past it (`res/exception-aware-placements`).

- With `(P a b)` in CxTop and `(arg P 1 T)` in CxMid below it, `(T a)` is stored in CxMid,
  believed at CxMid and below, and absent at CxTop.
- With the fact in CxL, the declaration in CxR and both under CxTop, a CxJoin under CxL and
  CxR is the placement, one per maximal common descendant.
- With the fact and `(arg Q 1 T)` in CxTop and `(genl P Q)` in CxMid, `(T a)` is stored in
  CxMid; with a second `(genl P Q)` in CxTop, in CxTop alone. A trigger membership stated
  in CxMid places an `interArg` mint the same way.
- With an `except` of the fact at the placement CxMid and an `except` of that `except` in
  CxLow, `(T a)` is stored in CxLow.

Each arrival direction reaches the placement:

- a **fact arriving** reads the declarations of its predicate and the predicate's
  ancestors whose placement is not its own context (`special/deduce-below`): one
  argument-root read per declaring kind and declared ancestor, skipped when no `genlCx`
  edge comes up to the fact's context. A posting whose count holds more declarations
  than the context has descendants is read narrowed to the contexts sharing a descendant
  with it, which `lein perf`'s `fact-beside-distant-declarations` holds;
- a **declaration arriving** places each fact of its extent at the pair's placements
  (`entail-existing`);
- a **`genl` edge or a trigger membership arriving** draws over the facts it reaches
  (`entail-under-edge`, `special/triggered-mints`) at their placements;
- a **`genlCx` edge arriving** draws over the facts stated in the contexts a context under
  its `sub` sees and its `super` does not, and the declarations stated there over the facts
  stated where the edge newly shows `sub` (`entail-under-context-edge`), which `lein
  perf`'s `genlcx-edge-beside-seen-declared-facts` holds. An edge whose newly shown
  contexts store nothing draws nothing, which `genlcx-edge-showing-an-empty-context`
  holds;
- a **`genlCx` edge leaving** takes the mints that named it, and `rederive-descended`
  draws the pair again at the placements that stand. A context under its `sub` can also
  become a maximal common descendant of a pair placed in a context it saw only through the
  edge (the move's effective stratum, `tax/context-move`); the settle's drain reads the mints placed in those contexts, and with
  pruning on the records there that withheld one, and draws each pair again
  (`special/departed-context-edge-mints`), which `lein perf`'s
  `genlcx-edge-leaving-beside-distant-mints` holds;
- an **`except` moving** draws the derivations of its target again
  ([An except of an ingredient](#an-except-of-an-ingredient)).

A placement an arrival leaves below a more general one loses its justification in the
settle: under a `genlCx` edge (`special/surplus-placements`), under a `genl` route or a
trigger membership (`special/descent-surplus-placements`), and under an `except` leaving
(`drop-hidden-mints!`). So every arrival order stores the same mints
(`argtype_entail_test`'s `a-mint-is-placed-at-the-most-general-contexts-that-see-the-fact-and-the-declaration`,
`a-genlCx-edge-leaving-places-the-mint-at-the-common-descendants-it-gives-back`,
`a-route-edge-or-trigger-below-the-placement-places-the-mint-where-it-is-seen` and
`an-except-at-the-placement-places-the-mint-where-the-fact-is-given-back`).

### An except of an ingredient

A derivation is not drawn in a context from which an `except` hides one of its
ingredients: the fact, the declaration, a trigger membership or an edge on the route
(`entail-arg-type` asks `exc/except-hidden-fn`), as a rule firing is not placed there
([contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree)). The
`except` moving reaches the derivations in either direction through the settle
(`special/except-move-sweeps`). An `except` arriving drops each derivation resting on its
target that the derivation's context no longer sees, or whose context is no longer a
placement, so the KB holds what the `except` arriving first leaves. An `except` leaving draws again what its target's arrival draws:
`entail-existing` for a declaration, the fact's own entailments for a fact, and the
trigger arm for a membership or a `genl` edge (`special/trigger-entailments`). A target
that is itself an `except` adds its own target. A `genlCx` edge that moves an `except`
moves it only for the contexts under the edge's `sub`, so there the sweep reads the
derivations stored under `sub` and draws the edge's own sweep (`entail-under-context-edge`)
rather than the target's. `order_independence_test`'s
`a-trigger-derives-in-every-order-and-its-retraction-takes-the-derivation` runs an
`except` of each ingredient in every order, standing and retracted.

### Nothing is withheld for redundancy

Every candidate narrowing — *the argument already has a type reaching this one*, *the
type is already stored*, *the argument has no visible place in the hierarchy so this is
the only thing that could teach it* — asks about **derived state**, which is a function
of what has arrived so far. That is fatal twice over:

* withhold the **materialization** on those grounds and `(dog Fred)` arriving before the
  declaration suppresses a record the same three sentences produce in the other order;
* withhold the **justification** on those grounds and a second fact entailing the same
  type contributes no support — so retracting the first sweeps a type the second still
  licenses, and which of the two holds it up depends on which arrived first.

Both are belief varying with arrival order, which is the one thing it may not do
(docs/nmtms.md). So every applicable (sentence, declaration) pair draws its entailment,
and deduplication happens where it is a property of content: `find-or-create-sentex`
gives one sentex per sentence, `has-justification?` one justification per pair.

The consequence is stated as a test: `(dog Muffet)` under `(genl dog animal)` already
*reaches* `animal` by subsumption, and with pruning off `(animal Muffet)` is minted anyway.
The one narrowing that reads belief rather than arrival is the next section's. That the engine
never materializes a supertype membership for *matching* is a different question —
matching fans the functor over the spec closure and needs no record. Here the declaration
makes the claim, and being a record is the whole of what this adds.

### Pruning what the KB says more specifically — `VAELII_PRUNE_SUBSUMED_MINTS`, on

One narrowing is **not** of that kind, and the engine takes it by default: a mint the KB
already holds more specifically. While `(dog Muffet)` is believed, the minted
`(animal Muffet)` beside it is the same claim one step vaguer, and it is not stored
(`VAELII_PRUNE_SUBSUMED_MINTS=0` stores it). What makes this admissible where the
narrowings above are not is that it reads **current belief**, not arrival: while the
specific membership is believed there is no record, and when it stops being believed the
mint is drawn. The membership, the edge that puts its type under the mint's, the fact and
the declaration in any of their twenty-four orders leave the same KB, which is what
`every-arrival-order-prunes-the-same-way` asks, and
`every-arrival-order-prunes-the-same-way-across-contexts` asks of the `genlCx` edge that
lets the mint's context see the membership. The candidate subtypes are the predicates of
the term's unary predicate set (`reads/as-stored-unary-predicates`), which a derived membership
enters as a stated one does, so a predicate holding the term in a fact of another arity
costs the check nothing.

Both arrival orders reach that state, and neither remembers how it got there:

* the specific membership **first** — `special/entail-arg-type` finds it
  (`checks/subsumed-mint`) and writes no record. It asks before the admission checks, and
  the assert entry point's check skips the mint too, so a withheld mint runs no admission
  check (`lein perf`'s `withheld-mint-beside-covers`);
* the specific membership **last**, or the `genl` or `genlCx` edge that makes it more
  specific or visible — the mint is already stored, so `settle` blocks its justifications
  (`special/subsumed-mint-blocks`) and the sweep that collects an excepted conclusion
  collects it.

A withdrawn `genl` mint can be the witness of rule firings, and the sweep deletes those
firings with the mint. Before the sweep, `special/withdrawn-edge-seeds` collects the
facts and rules of each withdrawn edge that a rule firing names as its witness. After the
sweep, `settle/apply-pass!` re-chains those seeds, so each firing is stored again over the
stated route that made the mint redundant. The order that states the route after the mint
therefore stores the same firings as the order that states the route first, which
`late_route_test/a-stated-route-withdrawing-a-mint-keeps-the-firings-the-mint-carried`
asks. [inference.md](inference.md#a-genl--genlcx-antecedent-reads-the-closure)
describes the re-join beside the re-join a departing edge owes.

The settle finds the stored mints a record it moved can displace in the **mint family**,
an index family ([indexing.md](indexing.md#10-the-mint-family)) that files every record a
stored justification of an argument declaration concludes, by the term it is about and by
its context.  The family is keyed by the justification and not by the sentence: a minted
`(person A)` and an authored `(person A)` in one context are one sentex.

| the record the settle moved | the mints it asks about |
|---|---|
| a membership `(T x)` | the mints about `x`, each tested against `(T x)` alone |
| a `genl` edge `(genl sub super)` | the edges minted out of `sub`, tested against the edge; the mints about each type under `sub` and each member of one, asked `checks/subsumed-mint` |
| a cover, `(covering W P …)` and its two sibling spellings | per part `P`, the mints about each type under `P` and each member of one, asked `checks/subsumed-mint`; a cover is never tested against a mint by itself |
| a `genlCx` edge `(genlCx sub super)` | the mints stated in each context under `sub`, asked `checks/subsumed-mint` |

The types and members under a `genl` edge are gathered once per settle over **all** the
edges it moved (`special/edge-route-candidates`, one `tax/specs-of-all` walk), not once per
edge: a `recover` moves every edge together, and per edge it would walk a subtree as many
times as edges leave it. A `recover`'s settle moves the whole store, and while fewer mints
are stored than sentexes it reads no moved record: it asks each stored mint
`checks/subsumed-mint`, and reads the `genlCx` edges off the index
(`record_fetch_cost_test/a-recover-pages-the-mints-not-the-store`). The loop over the
candidates hints the record store 256 at a time with each mint's record and then the
records `checks/subsumed-mint` can fetch for it (`checks/subsumer-reads`: the term's
memberships in other unary predicates, or the `genl` edges out of it and their
supporters), so a store with a fetch cache in front of a round trip reads them in two
round trips a chunk ([storage.md](storage.md#prefetching--the-optional-hint), `lein
perf`'s `subsumed-mint-pass-over-a-fetch-cache`).

The family holds exactly the records a stored mint justification concludes.
`special/entail-arg-type` files a record as it stores the justification, from the sentence
in hand.  A record leaving the store leaves the family (`special/retire-mint!`), and a
removal that takes a record's last mint justification while the record stays takes it out
(`special/retire-unjustified-mints!`), read off the network's report of what it removed
rather than off the stored justifications.  A filed record can still hold other support,
and `mint-only?` rejects it.  `reindex` rebuilds the family from the stored
justifications; `recover` and a fork read it and rebuild nothing for it
(`mint_candidates_test/the-mint-family-files-the-records-a-stored-mint-justification-concludes`).

Two conditions keep the withdrawal from eating what holds it up: the record has to be the
entailment's own (no premise support, every justification an argument declaration's), and
some subsuming record must not rest on the mint. Every subsumer is asked, so a minted
`(animal Muffet)` that `(awake Muffet)` subsumes while resting on it is withdrawn by
`(dog Muffet)`, as the mint drawn after `(dog Muffet)` is withheld
(`argtype_entail_test/a-subsumer-resting-on-the-mint-does-not-keep-it`).

**Nothing records a withheld mint.** It comes back when the record that displaced it
leaves belief or the store — retracted, defeated or swept — and the settle finds it by
re-deriving the mints that departure can have released (`special/withheld-releases`), as
`deduce-arg-types` derives them for a fact arriving now:

| the record that left | the facts re-derived |
|---|---|
| a membership `(T x)` | the facts naming `x`, for the memberships of `x` in `T` and the types above it |
| a `genl` edge `(genl sub super)` | the facts naming `sub`, each type under it and each member of one, for every mint about each |
| a cover | the same, per part |
| a `genlCx` edge `(genlCx sub super)` | every fact stored in a context under `sub` |

A departure reaches the settle from the network when a record goes OUT, and from
`integrate/sentex-removed!`, which queues each removed record of those four shapes on
`:departed`, one of the `Reasoning` value's two mint queues; a mint the same settle
withdrew is left out, since what subsumed it
subsumes what it did. The release is therefore a function of the store: a KB rebuilt by
`recover` releases what the KB that withheld the mint releases, which
`recovery_test/a-recovered-kb-releases-a-withheld-mint-as-the-live-one-does` asks of each
of the five ways a subsumption ends.

One arrival re-derives too. A record takes the justification of everything that entails
it, so a record a premise or a rule firing holds up coming IN while a believed record
subsumes it — an author's `(animal Fred)` beside `(dog Fred)` — has the facts naming
`Fred` re-derive that one sentence, and each whose mint of it was withheld adds its
justification. The record qualifies whether or not a mint justification already concludes
it: a firing in the same write can mint onto the record before the settle reads it, and
the order that stores the record first draws every mint onto it
(`argtype_entail_test/a-record-a-rule-concludes-takes-the-withheld-mints-in-every-order`).

A settle under `special/*release-withheld?*` false draws neither release. It keeps each
departure and arrival it read on `:owed` in `mint-queues`, which the reasoning image
carries, and `v/owed-releases` counts them; the browser's store card shows the count. The
switch is false in a bulk load, in the settles `recover` runs (an open and `lein cli
upgrade` among them) and in the first settle after a trusted image install. Nothing drains
the queue implicitly. `v/release-withheld!` draws what the owed rows release, chains from
the mints and settles, returning `{:terms n :released n :ms n}`. While a row is owed,
`isa?` and matching miss the membership it would draw. A preview keeps its own releases
owed unless asked otherwise ([preview.md](preview.md#what-a-preview-omits)). The draw matches what a
settle per fact draws at the departure
(`argtype_entail_test/a-departure-under-the-switch-owes-its-mint-until-release-withheld`),
and a close and a reopen keep the queue
(`reasoning_image_test/the-image-carries-the-owed-releases-and-an-image-without-them-installs`).

The KB **answers** the same either way: `isa?`, matching and the definitional checks all
read the taxonomy, which reaches `animal` from `dog` with or without a record in between.
Storage differs — the shipped starter holds 2,568 sentexes against 3,561, `core.txt` 932
against 1,234 — and so does `why`, which shows the subsumption route rather than a minted
record.

## The minted type is ordinary content

It is a **chaining seed**: it joins `seeds` alongside `subsumption-seeds` in
`assert-one`, so a rule with an `(animal ?x)` antecedent fires off a type the entailment
minted *within the same assert*. Without that, the same knowledge would derive different
things in different arrival orders — which is what this feature exists to fix, not to
cause. A minted `genl` edge is seeded as an asserted one is: the facts under its sub-type
go back on the agenda through `special/minted-seeds`, which calls `subsumption-seeds`
for each minted edge, so `(wolf Rex)` stored before `(genl wolf animal)` is minted fires
a rule on `(animal ?x)`. That holds on `assert`, on a rule conclusion, and on the settle
that releases a declaration whose type's other arity has just left.
`argtype_entail_test/a-minted-genl-edge-fires-the-rules-it-connects-in-every-order` runs
all 120 orders.

It is **checked**: `special/inadmissible` runs the same triple `place-conclusion` runs
over a rule conclusion — naming, the definitional constraints, `wff`, and edge
stratification, with the definitional constraints read as `place-conclusion` reads them:
a minted `(T x)` that clashes with a believed disjoint membership is placed and weighed at
settle. A minted `(T x)` at an arity its type denies is stored and read OUT by each
reader that sees the binding, with nothing in the ledger. A minted `(genl X T)` that closes
a taxonomy cycle or a cycle through negation is **reported, not thrown**: this runs after the triggering sentex is stored and inside a
fixpoint, neither of which may abort halfway, so it lands in `(violations kb)` the way
the lift's does.

And it **draws its own entailments**. It has to: the retroactive direction cascades
whether or not the forward one does — a declaration arriving over a stored `(t1 x)`
reaches it through `entail-existing` — so a forward direction that stopped at one level
would make the two orders disagree. The cascade recurses only on a *transition to
believed* — a sentex created, or a fresh justification that brings an out node in — which
bounds it: the condition is content-keyed and monotone within a pass, and the sentences
that can be minted are a subset of the finite `{(type, term)}` product the KB's vocabulary
spans, so each step consumes one element of a finite set that never shrinks. An
already-believed mint target takes the new support without re-querying its own
declarations; the target materialized those entailments when it first became believed.

## Where it does *not* mint

| case | what happens instead |
|---|---|
| an **individual** in an `genlArg` position | `genls-problem` convicts; an individual can never acquire `genl` edges |
| the declared type is `thing` | nothing, in either reading, and no waiting entry: a membership in `thing` says nothing about a term. `kb-quality` lists the declaration under `:typed-thing` |
| an arity statement binds the declared type to another length | nothing until the binding leaves; nothing records the declaration, and the settle reads it when the type's own bindings move |
| a `genlArg` position filled by the declared type itself | nothing — `(genl t t)` is a reflexive edge `wff` refuses, so `arg-entailments` never draws it. A `(genlArg P n thing)` declaration over a sentence whose position `n` holds `thing` would otherwise store a violation |
| a **function application** in the position | `args-problem` / `genls-problem` check it against the function's declared `result` / `genlResult` and refuse where the result misses ([nat.md](nat.md)) — but nothing is minted, a declared result being a claim about the *function* and not about this application, and a compound having no membership to mint |
| a genuine negation, or a rule | not argument-checked, so not entailed from either |
| an **inert** fact (`assert-inert`, or `set/inert` in a text file) | nothing, in every arrival order: the fact, a declaration reaching back over it, a forward chain, and a `genlCx` edge each skip it, since an inert sentex claims nothing (`argtype_entail_test/a-declaration-draws-no-type-from-an-inert-fact`) |
| a `genlCx` edge the structural producer computed: no premise, every support under the `contextArgSubrelation` informant (`nat-read/computed-genlCx-edge?`) | nothing, in every arrival order: the producer places the edge and draws no entailment, and a `genlCx` declaration's sweep (`entail-existing`), asserted or derived again by a rule, skips it. The orphan sweep reads the same edge as the engine's own wiring ([context-nat.md](context-nat.md#orphan-collection-a-context-is-a-place-as-well-as-a-name)), so a mint over it would be one more sentex the order of arrival decides (`context_nat_test/a-re-derived-declaration-draws-no-membership-over-a-computed-edge`) |
| a **query** | nothing, ever. The entailment is on the store path alone |
| a bulk or dump load | skipped: `*bulk-load?*` draws none of the four arrival orders (the fact, the declaration, the `genl` edge, and the `genlCx` edge the settle drains), and a dump import writes records directly. `v/record-arg-types`, run once after the load on the recovered KB, records what the stored facts derive, so the store then holds what a per-fact load holds (`argtype_entail_test/a-bulk-loaded-store-records-its-derivations-once`). The pass holds each mint's admission answer until it writes a mint or brings one IN (`special/*admission-memo*`), so the facts naming one term ask the checks, and their cover arm the provers, once between writes (`argtype_entail_test/a-record-pass-asks-each-terms-admission-once-between-writes`; `argtype_entail_test/a-record-pass-holding-its-checks-stores-and-believes-what-asking-each-afresh-does`). A mint written by every fact asks afresh, and the checks keep that ask cheap: the cover arm proves a part only of a cover that could refuse the mint ([taxonomy.md](taxonomy.md)), and the inheritance prover answers a denial of a part with no stated denial in range without reading the part's extent ([inherit.md](inherit.md#reading-it-back), `lein perf`'s `record-pass-mints-beside-an-inherited-extent`) |

## The pass over a stored KB

`record-arg-types` draws what every stored fact entails in one call. Over a store of
millions of facts that call runs for hours, says nothing while it runs, and a process
stopped part-way starts it again from the first fact. `record-arg-types!` is the same pass
as a run that reports, stops, resumes and sets a slow fact aside:

```clojure
(record-arg-types! kb {:on-progress progress!})          ; resumes what is owed, 2 s a fact
;; => {:drawn n :done n :total n :recorded n :violations n :deferred n
;;     :stopped nil|:requested|:shutdown|:cancelled :complete? bool}
(arg-types-owed kb)                                      ; => nil, or {:facts :total :swept? :deferred}
(record-arg-types! kb {:retry-deferred? true :budget-ms 60000})
(request-stop! kb)                                       ; from another thread
```

**One order.** Both entry points draw the facts of each functor an entailing declaration
reaches, the functors in content order (`declared-functors`) and each functor's facts by
handle, and draw each fact as `deduce-placed` draws one arriving now
(`special/draw-fact`). The handles of every functor are read when a run starts.

**A mint the fact would leave as it is costs no checks.** Over a store whose mints were
drawn once, nearly every entailment a fact draws is already stored with that fact's
justification, and `entail-arg-type` would write nothing for it and cascade nothing. The
pass passes such a mint over before its admission checks, as `rederive-mints` does
(`special/unchanged-mint?`): one stored in that context with a support from the same
declaring predicate over the same antecedents, or one not stored that a believed record
still subsumes, which would be withheld again. The checks are a mint's cost: beside ten covers a fact
costs 25 µs passed over and 1.0 ms asked (`lein perf`'s `record-pass-over-recorded-facts`).
The pass reports no violation of a mint already stored with that support, so a
violation that content stored after the mint makes goes unreported. A removal from the
records of a KB without belief adds no content, so it cannot make one. A mint not stored,
or stored without this support, takes the admission checks, and the pass writes it when
they admit it.

**What it owes is one record.** The functors drawn whole, by name; the handle reached in
the next one; the facts set aside; and whether the sweep over the functors has ended. A KB
with a directory keeps it there as `arg-types-owed.edn`, replaced whole through a temp
file, an fsync and an atomic rename; a KB without one keeps it in memory. It names stored
content and nothing else, so a pass stopped under one engine resumes under another.
`edit-records!` makes the whole pass owed when its batch removes anything, since a removed
membership or edge may have withheld a mint anywhere; `settle-record-edits!` under
`{:arg-types? false}` does when its sweep removed anything and nothing was owed.
`record-arg-types`, a `record-arg-types!` run that ends with nothing set aside, and
`clear!`, which deletes the records the position names, leave nothing owed. A run that
finds nothing owed draws from the first fact.

**A stop lands between two facts.** `:stop?`, `request-stop!`, a shutdown
(`dur/stop-requested?`) and a throw from `:on-progress` — a browser job's cancel — each
end the run at the next fact boundary. The run asks from its second step on, so every run
moves the pass on by one.

**A commit comes before the record moves.** The violations drawn since the last commit
are filed, belief is settled, every registered store is forced to disk, and only then is
the record written: every `:commit-every-ms` (30 s) and at the end of every run, stopped,
cancelled or thrown. A stopped pass leaves a settled KB and a record no further on than
the mints on disk. A process killed between two commits loses no stored mint: once belief
is rebuilt (`recover`, or `settle-record-edits!`), the next run redraws from the last
commit, which adds nothing to what the facts after it already wrote. A record carries a
handle allocated at its commit, and a store that allocates at or below it was restored from
an older copy: the run refuses it (`:owed-record-ahead`), and `{:resume? false}` starts
over.

**A fact over its budget is set aside, not waited on.** `:budget-ms` (2000) bounds the
reads one fact's mints make before they write: the admission checks (`inadmissible`, each
arm of `checks/constraint-problem` naming itself), the withheld test (`subsumed-mint`),
the entailments and the declarations below. Only those reads run under it
(`special/within-fact`, `budget/check-unit!`), and the writes that can draw mints of their
own — a restatement at a merged term, a dropped route — run outside it, so the signal lands
before a mint is stored or after it is justified. A fact past its budget is recorded with
`:phase`, the part of the checks that ran out, and with the mints it brought IN before it
stopped (`:transitions`), and the run moves on. `{:retry-deferred? true}` draws each again
once the sweep has ended: the fact, then each of those mints' own entailments and
restatement, which drawing the fact again would not reach, since the mints are stored and
justified by then.

A fact set aside is drawn after the facts behind it. Where an admission depends on the
order facts arrive in — the cover refuted through denials of a type above, where
`(q_w q_t)` is admitted before the `genl` mint that puts `q_t` under `q_top` and refused
after it (`argtype_entail_test`'s held-checks reading) — the KB then holds what that order
draws. Everywhere else the facts set aside and drawn again end where one pass ends.

**The phases a report names**, each as `{:phase :done :total}` in units fixed before it
starts: `:arg-types`, facts drawn of every fact the declared functors hold; `:releases`,
once the sweep has ended, the withheld mints the settles of an open or a recover left owed
(`release-withheld!`); `:deferred`, facts set aside drawn again; `:settle`; `:done`.
`settle-record-edits!` reports `:reindex`, `:recover` (the recover's seven steps) and
`:sweep` (its six) the same way.

The tests are `argtype_pass_test`: a pass stopped at every first, second, third and
seventh boundary, from the progress report, and by a cancel thrown from it, and one whose
facts are set aside at budgets counted in clock readings and drawn again, each store,
believe and justify what one uninterrupted pass does; the records path settles without
the pass, owes it across a close and a reopen, and resumes it; and a killed run redraws
from each commit it made.

## Cost

2000 binary-fact asserts into one context, in-memory backend, over a starter of 1,571
sentexes — the corpus these readings were taken on:

| | off | on |
|---|---|---|
| no declarations at all | 374–415 ms | 322–364 ms |
| 20 declarations, none matching the facts | 286–316 ms | 294–340 ms |
| every predicate declared (one mint per assert) | 317–336 ms | 609–673 ms, **2× the sentexes** |
| the starter load | 585–638 ms, 1571 sentexes | 865–962 ms, 1793 sentexes |

With the toggle **off** an assert reads one dynamic var and stops. With it **on** — the
default — and nothing to do, on/off straddles parity, which is as precise
as this bench gets; the shared `declaration-reader` is what bought that. Where it mints,
the run stores twice as many sentexes, so the ~1.9× is the minting, not the declaration check.

**With subsumed mints pruned, the default, a membership a settle moves costs one mint-set
lookup**, and nothing on a KB that holds no mint. The records the settle relabelled are
filtered by shape (only a membership, a `genl` edge or a `genlCx` edge can subsume a mint)
and by transition (a record that did not move subsumes what it subsumed before), and an
empty mint set stops the trigger before any record is read. A membership about a term
holding no mint reads no posting however many facts name the term — the one read the
release adds for a membership that is not a mint, `checks/subsumed-mint`, is the term's
slot predicate set — which `lein perf`'s `mint-withdrawal-under-busy-term` holds. A `genl` edge
still reads its subtree's stored extent, the read `entail-under-edge` makes for the same
edge. The release is paid on a departure rather than on a write: a membership leaving
re-derives the facts naming its term, a `genl` edge the facts naming each term under it,
and a `genlCx` edge the facts stored under it, and a settle that moves none of the three
reads nothing about the mints the KB withholds, which `settle-beside-withheld-mints`
holds. The check in front of the release reads the taxonomy's declaring `:props` sets
rather than the index, so `assert_cost_test`'s budgets are the ones the entailment alone sets
whichever way the switch stands. With it off none of that runs.

**`interArg` is read behind an O(1) presence check where the other two are unconditional**, and
the asymmetry is deliberate. `arg` is what a typed ontology is mostly made of, so its
declaration read pays for itself on the facts it constrains. The shipped ontology declares
no `interArg` at all, and the check runs on *every* assert — measured at **~11% per
assert** of a declaration-carrying predicate for a retrieval that found nothing, against a
`count-with-functor` that answers "is one stored at all" for free. Add a fourth
argument-constraint kind the same way: skip it unless something declares it. A ratio-based
perf check cannot catch this class, since a constant added to every write divides out
(`bench/vaelii/bench/perf.clj` says so in its preamble).

## Which runs cover each reading

`lein gate` runs the suite under the entailing reading, the default. The constraint-only
reading is the `assertive-off` sweep (`VAELII_ASSERTIVE_ARG_TYPES=0`): `lein test-sweeps`,
`lein test-matrix` and the `deep` workflow run it on the default backend, and `lein
test-matrix --owed` names it for a change to `checks.clj`, `special.clj` or
`resources/kb/`. Both readings must fail the same set and run the same number of
assertions, as every sweep must ([CONTRIBUTING.md](../CONTRIBUTING.md)), so a test whose
count or answer depends on the reading forces one: `tu/with-entailing` where the entailment
is its subject, `tu/without-entailing` where the constraint is.

On `memory` at `:default` both readings run 5,102 tests, and a per-namespace count
(`VAELII_TEST_NS_COUNTS=1`) puts every namespace at the same assertion count under both.
The sampling oracles `arg-root-retrieval-test` and `matches-hierarchical-test` run the
same count under both readings. `full-kb-test`'s small-KB twin samples derived literals
per context, where the mints sit, so it forces the entailing reading. Subsumed-mint pruning
(`VAELII_PRUNE_SUBSUMED_MINTS`) acts only on mints, so the constraint-only run leaves it
idle; the tests of pruning force the entailment on.

`backend_parity_test` forces the toggle off inside its scripted session. That namespace's
question is whether eight storage backends answer hand-written expectations alike, and
the entailment would change the script itself: `(arg ownerOf 2 animal)` and
`(ownerOf Ann Rex)` both sit in `CxParity`, so Rex would carry a second, independent
`animal` membership and retracting `(dog Rex)` would no longer take his type with it.
That is the feature working, tested where it belongs.

## The conditional form

`(interArg P n T m U)` says that when argument `n` is a `T`, argument `m` must be a
`U` — the claim `arg` cannot make, since `(arg eats 2 meat)` demands meat of every
eater where `(interArg eats 1 carnivore 2 meat)` demands it only of carnivores. It
entails the same way and just as strongly: `(meat Chunk)` from `(eats Rex Chunk)` and the
declaration, justified by both, once `Rex` is known to be a carnivore.

The trigger side must be *positively established* — silence about argument `n`'s type is
not evidence that it is a `T`, so an unknown trigger leaves the declaration dormant. Once
the trigger holds, the target is derived a `U` and is not convicted, whatever else it
holds. Under the constraint-only reading the target is convicted by *absence*, exactly as
`arg`'s is there.

**The trigger is an ingredient.** The derivation names the membership that makes `Rex` a
carnivore, the `genl` edges from its type up to `carnivore` and the `genlCx` edges the
fact's context sees it through (`checks/trigger-supports`), one justification per such
membership. Retracting `(carnivore Rex)`, or an edge on its route, takes `(meat Chunk)`
back unless another membership still makes `Rex` a carnivore. The fact and the
declaration each reach the other (at the entry point, and through
`special/entail-existing`). The trigger arriving after both reaches back through the
settle: a membership that comes IN, or a `genl` edge that makes a held type reach a
trigger type, puts the stored facts naming its terms back through the derivation
(`special/triggered-mints`). It reads the smaller of the term's postings and the extent
of the declared predicates, which `lein perf`'s `trigger-membership-beside-declared-facts`
holds. A trigger defeated when the fact arrived and believed later is the same
transition. `order_independence_test`'s
`a-trigger-derives-in-every-order-and-its-retraction-takes-the-derivation` runs every
order of the three ingredients and each retraction. The homogeneity forms below read the
trigger the same way.

## A type another argument names: `argArg`

`(argArg P n m)` says that argument `n` of every application of `P` is an instance of the
type its argument `m` names. `arg` fixes the type in the declaration; `argArg` reads it off
each sentence, so `(argArg kindOfPet 1 2)` over `(kindOfPet Rex dog)` derives `(dog Rex)`
and over `(kindOfPet Tom cat)` derives `(cat Tom)`. A sentence holding no symbol at `m`
names no type and is not constrained.

`checks/arg-arg-rows` reads each declaration as an `arg` row for the sentence in hand,
with the declaration's handle as the row's support. The conviction (`args-problem`), the
entailment (`constraint-entailments`) and the declaration's sweep over stored facts
(`special/entail-existing`) are therefore `arg`'s own, and a mint's justification names
the fact and the `argArg` declaration. The declaration itself is checked as `interArg`'s
is: both positions must be positions `P` has, and one position named twice is
`:not-well-formed`.

**A named type bound to another length mints once it is mintable.** `arg` names one
type, so a declaration whose type is not mintable is swept again once the type is
mintable. An `argArg` names no type of its own: each fact names one. A fact whose named
type `mintable-type?` refuses draws no mint in it, and once the type is mintable
`special/mints-on-lengths` reads the stored facts naming the type at a position an
`argArg` types and draws their mints through `deduce-placed`, so the binding of `dog`
leaving after `(kindOfPet Rex dog)` mints `(dog Rex)` as it would had it left first.
`argtype_entail_test/every-arrival-order-of-an-arg-arg-reaches-the-same-belief` runs the
six orders of the declaration, the fact and the edge. A fact waits only on declarations
visible from its context or placed below it, the two reads the assert path makes.

**`resultArg` types a reified constant through the same arm.** `(resultArg F n)` types
the value of an application of `F` by the type the application's argument `n` names. Over
a `(natFormula K E)` fact, `E` an application of `F`, `checks/result-arg-rows` reads each
declaration as an `arg` row at position 1. `(resultArg MemberFn 1)` over `(natFormula K
(MemberFn dog))` therefore derives `(dog K)`, justified by the `natFormula` fact and the
declaration. The mint is placed, waits on an unmintable type and is released as an
`argArg` mint is. A type bound to another length mints nothing until the binding leaves,
and retracting the declaration withdraws the mint. A declaration arriving after the
mints reads the stored `natFormula` facts of `F`'s applications
(`special/entail-existing`). The membership is an entailment, so the constraint-only
reading (`VAELII_ASSERTIVE_ARG_TYPES=0`) draws none, and a minted constant there holds its
`result` types alone. `argtype_entail_test/a-result-arg-types-a-minted-constant-in-every-order`
runs the six orders of the declaration, the write and the type edge, each with a recover,
beside a name that is no type and a retracted declaration. An application that is never
minted is typed at check time ([nat.md](nat.md#typing-an-application-that-is-never-minted)).

## A type conditioned on an argument value: `interArgEqual`

`(interArgEqual P n v m U)` says that argument `m` of every application of `P` whose
argument `n` is `v` is a `U`. `interArg` conditions on argument `n`'s type and
`interArgEqual` conditions on its value, compared by `=`: `(interArgEqual grants 2 3 1
admin)` over `(grants Rex 3)` derives `(admin Rex)`, and over `(grants Fido 4)` derives
nothing. A sentence holding another value at `n`, or a variable, is not constrained.

`checks/inter-arg-equal-rows` reads each declaration as an `arg` row for the sentence in
hand, as `argArg`'s rows are read, so the conviction, the entailment and the derivation's
justification (the fact and the declaration) are `arg`'s own. Under the constraint-only
reading a sentence whose argument `m` misses `U` is convicted and held inert. `try-assert`
refuses a provable clash from both arrival orders: the fact after the declaration and a
held separation (`:arg-type`), and the declaration after a stored triggered fact
(`checks/declaration-demand`). A declaration arriving after the facts reads the stored
sentences of `P` and its specs and keeps those holding `v` at `n`
(`special/entail-existing`).

**The value is a number, string, keyword, boolean or character.** `wff` refuses a symbol
at argument 3 (`:not-well-formed`). The equality partition holds symbols only
([equality.md](equality.md)), and a merge moves stored sentences to the representative
without drawing their argument entailments again, so a symbol value would derive in one
arrival order and not in the other. No merge changes a value of the five kinds, so `=` on
one reads the same in every order.

**CxUniverse types a `closedExtentForArg` grant's predicate by the grant's position.** The
rows `(interArgEqual closedExtentForArg 2 2 1 at_least_binary)` through `(… 2 5 1
at_least_quinary)` derive `(at_least_ternary accountOn)` from `(closedExtentForArg
accountOn 3 HostA)`. On a `binary` `accountOn`, the shipped `(disjoint at_least_ternary
binary)` separates the two. Under the entailing reading `try-assert` refuses the grant,
or refuses the arity statement that arrives after it; under the constraint-only reading
it refuses the grant, and a grant stored first is held inert once the arity arrives ([naf.md](naf.md#a-closed-extent-for-one-argument-value)).
`argtype_entail_test/an-inter-arg-equal-types-the-tuples-its-value-triggers-in-every-order`
runs every order of the declaration and two facts, and
`naf_test/a-per-argument-grant-past-its-predicate-s-arity-clashes` both readings and both
orders of the grant and the arity.

## Suffix homogeneity: `interArgs` and `interArgAndRest`

`(interArgs R T)` says that when any argument of an application of `R` is a `T`, every
argument is a `T`. `(interArgAndRest R n T)` says the same of the positions from `n` to the
end of each application and leaves the positions before `n` unconstrained. `(interArgs R
T)` states what `(interArgAndRest R 1 T)` states, and two forward rules in `core.txt` derive
each spelling from the other, the way `arg1` and `(arg R 1 T)` derive each other.

The reading is `interArg`'s with one type in both roles. The trigger is an argument in the
suffix that the KB knows to be a `T`; the target is an argument in the suffix that the KB
places in the hierarchy outside `T`. Under the entailing reading a trigger derives `T` of
every other symbol in the suffix (`checks/homogeneity-entailments`), so `(sameKindAs Rex
Oak)` with `Rex` an animal stores and derives `(animal Oak)` beside `Oak`'s own type. Under
the constraint-only reading an application with a trigger and a target is refused
`:inter-arg-type`, the `interArg` refusal, carrying the trigger's position and the
target's. An application with no trigger is unconstrained in both readings, so a suffix
whose arguments all lie outside `T` stores and derives nothing. An argument with no type is
no trigger. A value or a compound is neither trigger nor target, which is the reading
`interArg` gives both of its positions.

Under the constraint-only reading, with `(interArgs sameKindAs animal)`, `(sameKindAs Rex
Fido)` and `(sameKindAs Oak Elm)` store and `(sameKindAs Rex Oak)` is refused once `Rex` is
an animal and `Oak` a plant. `(interArgAndRest groupedUnder 2 animal)` refuses
`(groupedUnder Farm Rex Oak)` and stores `(groupedUnder Rex Oak Elm)`: position 1 is below
the start, so the animal there triggers nothing.

- **One constraint, read once.** `checks/inter-args-homogeneity-problem` reads both
  spellings through the shared declaration reader and keys each on its start, type and
  declaring predicate, so a stated `interArgs` and its derived `interArgAndRest` twin
  convict once, and the refusal names `interArgs` at start 1 whichever spelling was stated.
- **Descends the predicate hierarchy**, as every argument constraint does: a declaration on
  a super-predicate binds a sub-predicate's tuples.
- **Answered at the stated type.** `MetaConstraintProver` answers a goal from a stored
  declaration on the goal's predicate or on a super-predicate, with the type and the start
  matching exactly. The type is a trigger, which reads down `genl` like `interArg`'s
  position 3, and a target, which reads up like its position 5, so it generalizes in
  neither direction: `(interArgs R animal)` refuses a reptile beside a plant that
  `(interArgs R mammal)` stores, and `(interArgs R mammal)` refuses a mammal beside a
  reptile that `(interArgs R animal)` stores.
- **Behind a presence check.** Both readings sit behind the taxonomy `:props` presence
  check the covering forms use.

**Arrival order.** Under the entailing reading a declaration arriving after the
applications derives over them (`entail-existing`), and a trigger's membership arriving
after them derives through the settle, as `interArg`'s does (above). Under the
constraint-only reading the declaration and both memberships stored before the application
is the covered order, in any of their six orders, which `inter_args_test` runs; a
declaration, a trigger's membership or a target's membership arriving after the
application convicts nothing, and `entry_point_and_report_test` holds the three beside the
family's other cells that read "nothing".

## The quoted twin

`(quotedArg P n T)` types argument `n` **as a term** rather than by what it denotes: its
EDN kind — a `string`, a `number` (with `integer` below it), a `symbol` — checked through
`genl` against a syntactic type. Under `(quotedArg name_of_guy 1 string)`, `(name_of_guy 5)`
is stored and held inert, 5 being a number and not a string, in either arrival order
([held inert](#an-argument-that-fails-its-declared-type-is-held-inert)), and
`(name_of_guy "Bob")` is believed. It is the mention twin
of `arg`: where `arg` reads the referent's type, `quotedArg` reads the argument's own
syntax, which is decidable from the value — so it is **checked, never entailed**, there
being nothing to mint about a term that already is what it is. A compound is judged by the
kinds its spelling decides ([what a quoted form is](#what-a-quoted-form-is)). Open-world
about a declared type outside the syntactic lattice and the expression lattice it sits in,
so an imported constraint on a domain collection never convicts a value it cannot judge.
`(quotedArgAndRest P n T)` is its suffix form, as `argAndRest` is of `arg`: position `n`
and every later one, each taken as written. `checks/args-quoted-problem`, behind the same
O(1) presence check as `interArg`. Why the kind
decides at all, rather than every non-symbol being exempt:
[defenses.md](defenses.md#a-value-is-typed-by-its-kind-and-the-openness-moves-to-the-declared-type).

**Checked and never entailed is not the same as read literally.** Whose declarations speak
for a tuple is one question for all four spellings — `res/constraining-predicates`, the
predicate's own and every super-predicate the asking context can see — so a `quotedArg` on
`pAgeOf` holds a `pInfantAgeOf` tuple inert. `provers/MetaConstraintProver`
answers `quotedArg` along that same closure, position 1 descending the predicate and
position 3 widening up the type, exactly as it answers the other three; the alternative was
one declaration meaning one thing to `assert` and another to `ask`. What stays out is the
*entailment*: answering a goal draws nothing, and there is still nothing to mint.

**One vocabulary, not two.** `string`, `number`, `integer`, `keyword`, `boolean`,
`character` and `symbol` name the EDN kinds a value can carry — one per leaf
kind, deliberately complete — and both declarations read them. Beside them sit the
value-refined integer types `positive_integer`, `negative_integer`,
`non_negative_integer` and `non_positive_integer`, each below `integer` in the `genl`
lattice; zero satisfies both non-positive and non-negative, so a value can
answer to two of them at once and `checks/value-kinds` returns the set rather
than forcing one artificial leaf.

**Both declarations read the refinements, and for the reason they share the kinds.** A
sign is as decidable from the `5` written in a position as from what that `5` denotes,
so `(quotedArg p n positive_integer)` holds `-5` inert and admits `5`, exactly as
`(arg p n positive_integer)` does. Reading the refinements on one side only was tried
and is the trap this page already warns about one paragraph down, arrived at from the
other direction: `positive_integer` is *inside* the syntactic lattice, being below
`integer`, so the open-world escape does not apply to it — the check compared the
value's bare kind upward against the declared type, and refused every integer
written in such a position. One reader, both entry points. A string value denotes itself, so
`(arg comment 2 string)` and `(quotedArg p n string)` ask two questions of one set — what
the argument denotes, and what is written there. A parallel domain spelling would buy
nothing and cost a trap: `quotedArg` reads a type outside the syntactic lattice
open-world, so a second spelling stores clean and convicts nothing, with no report
([why one vocabulary](defenses.md#one-vocabulary-not-two)).

**A type that refines a kind convicts only by separation.** A declared type below the
value's own root and above none of its kinds, such as `ip_address` under `string` or a
subtype of `integer` other than the four above, is one the value may or may not belong
to: the kind does not decide it. Both declarations convict a value there only where the
taxonomy separates the declared type from one of the value's kinds, so `5` under
`negative_integer` is held and `"192.0.2.1"` under `ip_address` is believed
(`checks/value-outside?`,
`argtype_entail_test/a-value-is-held-only-where-the-declared-type-excludes-it`).

**A `:monotonic` definition states the kind a type's values are.** A type with no `genl`
edge to a value kind, such as a `character_string` under `thing` alone, convicts every
value under it. `(defnIff character_string (string ?x))`, `defnSufficient` or
`defnNecessary`, asserted at `:monotonic` over the value-kind predicates or any evaluable
condition, decides the value before the kind does, in both declarations and both readings
(`provers/value-definition`):

- a sufficient condition of the type or of a subtype that is true on the value admits it,
  so `(nameString X "Foo")` under `(arg nameString 2 character_string)` is believed;
- a necessary condition of the type or of a supertype that is false on the value convicts
  it, so `5` there is held, and a subtype of `character_string` holds it too;
- a `:default` definition decides nothing, and with no definition the kind decides.

A condition decides only where every conjunct is evaluable, since a value is open about a
stored predicate. The definitions are read at the write, and the drain reads the
declarations naming a type at, above or below a definition stored, removed or relabelled
(`argtype_entail_test/a-monotonic-definition-decides-a-value-under-the-declared-type`,
`argtype_entail_test/a-value-a-monotonic-definition-admits-owes-no-release-after-a-recover`).
The form and the order the conditions are read in are [defns.md](defns.md#a-definition-decides-a-literal-value-at-the-argument-check).

`symbol` is the exception, and is **mention-only**. A symbol does not denote itself, so
the set of names and the set of things named are not one set — `parentOf` written in a
sentence denotes a predicate, and `(Quote parentOf)` denotes the symbol. `symbol` is below
`linguistic`, which is disjoint from `relation`, so no term is both a symbol and a
predicate.

## What a quoted form is

`(Quote X)` denotes the expression X. The kinds X's spelling decides in `reflection.txt`'s
expression lattice are read off how X is written (`provers/shape-kinds`):

| X | kinds |
|---|---|
| a variable | `variable` |
| a symbol | `symbol` |
| a value | its value kind (`string`, `integer`, …) |
| a compound under a connective or quantifier head (`not`, `and`, `implies`, `forall`, …) | `open_formula`, or `sentence` when no variable is free in it |
| `(sentexHandle N)`, N a positive integer | `sentex_handle_term`, a `non_atomic_term` |
| a compound under any other symbol head | `non_atomic_expression`, beside `open_expression` or `closed_expression` |
| a compound under any other head | `ill_formed_expression`, beside the same |

A variable inside a nested `(Quote …)`, or bound by a quantifier in X, is not free in X
(`sx/unquoted-free-vars`). The expression `?x` is open; the sentence around `(Quote ?x)` is
closed (`sx/closed?`), which is a different expression.

`ExpressionKindProver` answers `(k (F X))` for `k` below `expression` and `F` a quoting
function — `Quote` or `Quasiquote`, which the engine fixes and no statement declares —
true when one of X's kinds reaches `k` through `genl`. A reifiable quoting function's
application arrives minted, and the prover reads the constant's `natFormula` back to the
form; an application never minted names no stored term, so a query over it matches
nothing, as for any NAT ([nat.md](nat.md)). The answer rests on the `natFormula`
statement and one `genl` path, and a forward firing names them. A datum on an
edge-installing functor re-joins the rules over an expression kind, so the lattice
arriving after the rule and the fact fires it. Forward chaining discharges an antecedent
through the prover only for the kinds `provers/expression-kind-predicates` names.
`(sentence (Quote (not (dog Muffet))))` holds by the form's own shape, with no `genl` edge
and no `natFormula` behind it, so its answer carries no handle. It joins beside the stored
fact that bound the form, and that fact supports the firing; a firing whose combined
handles are empty is dropped, so `(implies (sentence (Quote …)) …)` alone concludes nothing
(`kind_antecedent_forward_test`).

A **value kind** antecedent (`string`, `number`, `boolean`, `keyword`, `character`,
`integer`) is computed once another antecedent binds its argument, as `lessThan` is
(`sentex/deferred-predicates`): `(implies (and (valueOf ?a ?x) (string ?x)) …)` fires when
`(valueOf Ann "rex")` arrives, in either order. A value kind of a constant or a function
application reads the stored membership, since either can denote a value of any kind. A
rule in which nothing binds the argument is refused (`:naf-not-closed`).

**What the KB states of the head decides the rest** (`provers/stated-kinds`). The kinds of a
compound `(R a …)` under a symbol head are read from R's stored memberships and length,
never from R's spelling:

| what the KB states of R | `(R a …)` closed | `(R a …)` open |
|---|---|---|
| a member of `predicate`, or of a type below it, and not of `function` | `closed_predication`, so a `literal` and a `sentence` | `open_predication` |
| a member of `function`, or of a type below it, and not of `predicate` | `non_atomic_term`, so a `denotational_term` and a `wff_expression` | no further kind: a `denotational_term` is closed |
| a length the argument count breaks (`arity/broken-binding`) | `ill_formed_sentence` for a predicate, else `ill_formed_expression` | `ill_formed` for a predicate, else `ill_formed_expression` |
| neither, or both | no further kind | no further kind |

An application whose length is broken is neither a predication nor a `non_atomic_term`:
only a `wff_expression` predicates or denotes. The answer rests on the membership and one
`genl` path from its type to `predicate` or `function`, and a broken length rests on the
bindings stating it and the `genl` edges up to them, so a forward firing withdraws when one
of them goes. A membership classifies the form for the contexts that see it; a length is
read the same at every context ([taxonomy.md](taxonomy.md#arity)). A membership `(T R)` of
a type at or below `relation` re-joins the rules over a kind it can move
(`provers/support-answers-reading`) when a stored sentex holds a quoted application headed
by R, and a settle pass that moved R's length re-joins them under the same condition
(`special/recheck-on-lengths`). A rule over `(predication ?q)` therefore fires whether the
head's membership arrives before or after the rule and the quoted fact (`quote_test`).

Only the head is read. An ill-formed operand inside `(R a …)` leaves the form at the head's
kinds, and `(not (R a))` stays at `sentence` or `open_formula`. No kind answers
`wff_expression` for a formula, nor `wff` or `wff_sentence`: the positive half of
well-formedness needs every operator's length in X, which no reader collects.

**`quotedArg` judges a compound by the kinds its spelling decides.** A compound in a `quotedArg` position is
held inert where one of its kinds is separated from the declared type
(`checks/compound-kind-against`, `tax/disjointness-test`). A kind that merely fails to reach
the type convicts nothing, since the spelling leaves `(R a)` at `non_atomic_expression`,
which reaches neither `non_atomic_term` nor `formula`. Under `(quotedArg P 1 string)`,
`(P (MsrFn 5))` is held, a `non_atomic_expression` being separated from `string`; under
`(quotedArg P 1 non_atomic_term)` it is believed, and `(P (not (dog Fido)))` is held,
`reflection.txt` separating `formula` from `non_atomic_term`. The verdict is the same in
either arrival order of the declaration and the fact
(`quoted_arg_test/a-compound-is-held-only-where-one-of-its-kinds-is-separated-from-the-type`).
A declared kind of `expression` decides a value or a symbol too, every value kind and
`symbol` sitting in the lattice (`checks/syntactic-type?`): `(quotedArg except 1
sentex_handle_term)` convicts `(except 212)`, and `(quotedArg comment 1 denotational_term)`
admits a symbol or a value.

## Scope

**In:** `arg`, `genlArg`, `interArg`, the covering forms and the homogeneity forms, in
all four directions, justified and retractable, from a declaration written in a context or
inherited by it; `record-arg-types` over a store loaded without them; the toggle; and the
closure reading of the four singular spellings on the query surface, which is neither
direction of the entailment.

**Out:** entailing `quotedArg`, which is checked and never entailed (above), there being
nothing to mint about a term that already is what it is — it is *answered* along the `genl`
closure with the other three, which is a different question; `(ListOfType T)` element typing, which stays
disjoint-check-only so a `(ListOfType thing)` slot refuses nothing and sprays nothing;
making `checks` write, for the sequencing reason above; a dry-run mode, since
`preview` has its own machinery and the two are not wired together; and judging a rule
variable against a `quotedArg` demand at a kind other than `string`, `number` or a type
below one, or against a second `quotedArg` demand: the rule-variable arm stores and
believes a rule no term can satisfy at both ends of such a pair
(`rule_variable_arg_test/a-quoted-symbol-demand-is-not-judged-by-the-rule-arm`,
`rule_variable_arg_test/two-quoted-demands-are-not-judged-by-the-rule-arm`,
[taxonomy.md](taxonomy.md#and-against-the-variables-of-a-rule)).

**On by default.** The constraint-only reading stays available under
`VAELII_ASSERTIVE_ARG_TYPES=0`, and the tests that assert it force it there
(`tu/without-entailing`).
