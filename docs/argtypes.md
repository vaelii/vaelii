# Assertive argument types: `arg` as an entailment

- **Covers:** how, by default, an argument constraint — `arg`, `genlArg`, `interArg`, the
  covering and the homogeneity forms — derives the type it names as a derived, justified,
  retractable sentex and refuses nothing on a membership; the pass that records those
  derivations over a store loaded without them.
- **Not here:** `arg` / `genlArg` read as a constraint that rejects a wrongly-typed
  argument (the opt-out `VAELII_ASSERTIVE_ARG_TYPES=0` reading) → [taxonomy.md](taxonomy.md); `transitiveInArg`,
  which carries a stated claim rather than a declared type across an argument →
  [inherit.md](inherit.md).
- **Assumes:** sentex, justification, context, `genl` → [glossary.md](glossary.md).

## Relation-wide declarations and the runtime boundary

`arg` (including `arg1` / `arg2` / `arg3`), `genlArg`, `quotedArg`, `interArg`, the
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

- **No derivation, and a symbol convicted only under the constraint-only reading.** No
  entailment is drawn for a nested input: a declaration arriving after the fact derives
  over the facts it finds by predicate, and nothing finds the applications of a function
  inside stored facts, so a nested derivation would be drawn in one arrival order and not
  the other. Under the entailing reading a nested symbol is therefore neither derived nor
  convicted, as at the top level; a nested value or application is convicted. Under the
  constraint-only reading a nested input is convicted when its visible types reach
  `thing` and miss the declared type, and an input with no visible type is no evidence.
- **Terms, not formulas.** A connective's argument (a genuine `(not (P …))`) and a
  compound whose head the KB knows as a predicate are formulas, not applications, and
  are not read as one. A head the KB has not classified is read as a function.
- **A mention is not descended into.** A position a `quotedArg` declaration types holds
  the term written there, so an application in it is syntax, and neither its result nor
  its inputs are read. The same holds for the argument of a quoting predicate
  (`termOfUnit`, `rewriteOf`) and of a `quoting_function`. A quoting function's own
  declarations are still read over its application; only what it quotes is left alone.
  `quotedArg` itself stays open-world about a compound argument's kind: no shape
  classifier exists, so a compound in a `(quotedArg P n string)` position is neither a
  string nor convicted of not being one.
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

### A unary predicate declares a position only when its `genl` parent does not imply it

An `arg` declaration on a unary predicate and a `genl` edge above it can say the same
thing, and which of the two is right turns on where the parent sits relative to the type
the declaration names.

`fixed_arity` carries `(arg fixed_arity 1 relation)`, and the `(genl fixed_arity relation)`
edge that `(partition relation fixed_arity variable_arity)` installs names that same type. The edge concludes `(relation 5)` from `(fixed_arity 5)` and
nothing is disjoint from `relation` for a number, so the declaration's value conviction
is the only refusal there is; drop it and `(fixed_arity 5)` is accepted. `variable_arity`
and the function marks are in the same position and keep theirs.

`instance_relation_predicate` is the other case. Its parent is `binary_predicate`, which
sits **below** `predicate`, so `(arg instance_relation_predicate 1 predicate)` would
restate in a weaker form what the edge already concludes, and under the constraint-only
reading it would turn that conclusion into a precondition: `(instance_relation_predicate
pairOf)` after `(arity pairOf 2)`, which places `pairOf` under `relation` and not under
`predicate`, would be refused for a kind the sentence itself states. So the six marks whose
own `genl` parent supplies the declared type declare no position:
`instance_relation_predicate`, `type_relation_predicate`, `equivalence_relation`,
`injection`, `surjection` and `bijection`.

| argument | what happens |
|---|---|
| a number | `:arg-type`, through the `(arg fixed_arity 1 relation)` floor the mark inherits |
| a term reaching only `thing` | stored; the floor derives `relation` and the mark's edges place it under `predicate` |
| a `function` | stored, with `instance_relation_predicate` and `function` a placed clash |
| a relation whose kind is not yet stated | stored, and the mark supplies the kind |

`arity_vocabulary_test/a-predicate-only-classification-is-order-independent-of-the-arity`
compares the two orders on the whole closure rather than on an acceptance, and
`an-arity-alone-leaves-the-relation-kind-open` asserts the rows of the table.

### The policy classes declare one position and their specializations declare none

`fixed_arity` and `variable_arity` each carry `(arg C 1 relation)`. Nothing below them
carries one. The parent's declaration descends the predicate hierarchy, so
`(fixed_arity_predicate Fred)` with `Fred` a person derives `(relation Fred)`, a clash
with `person`, while a narrower `(arg fixed_arity_predicate 1 predicate)` would derive the
wrong thing: a relation whose only stated type is `variable_arity` would be derived a
`predicate`, so `(binary_predicate P)` written after `(variable_arity P)` would carry a
second derived type where the contradiction is the arity policy. The two are one
contradiction and are stored as a clash in either order. A relation classified into the
wrong kind is caught by `(disjoint predicate function)` through the `genl` edges, a
disjointness derived from `(partition relation function truth_valued_relation)` rather
than stated.

## The covering constraints: typing a variable-arity tail

`arg` and `genlArg` name one numbered position. A variable-arity relation whose tail
repeats one role has no largest position to name, and `(args R T)` types the whole
admitted tail instead: every accepted position of `R` is an instance of `T`. `(argsGenl R
T)` is the subtype reading — `argsGenl` to `genlArg` what `args` is to `arg`. `(argAndRest
R n T)` and `(argAndRestGenl R n T)` type position `n` and every later one, so a relation
whose head positions carry their own `arg` declarations and whose tail repeats one role is
typed exactly. `(args R T)` states what `(argAndRest R 1 T)` states.

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
its relation's binding denies is stored and placed as an arity nogood
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
(binding [checks/*assertive-arg-types?* true]
  (v/assert kb '(arg parentOf 1 animal) 'CxWorld)
  (v/assert kb '(parentOf Fred Mary) 'CxWorld))

(v/isa? kb 'Fred 'animal 'CxWorld)          ; => true
(v/why kb (v/handle-of kb '(animal Fred) 'CxWorld))
;; {:premise? false
;;  :support [{:informant arg
;;             :because [{:sentence (parentOf Fred Mary) :premise? true}
;;                       {:sentence (arg parentOf 1 animal) :premise? true}]}]}
```

**On by default** (`vaelii.impl.checks/*assertive-arg-types?*`; the root value reads
`VAELII_ASSERTIVE_ARG_TYPES`, and `=0` opts out — how the whole suite is run under the
constraint-only reading). Entailing changes what a KB *contains*, not only what it
answers, so the constraint-only reading stays one `binding` away.

**No shipped `arg`-family declaration types an argument `thing`.** Such a declaration
rejects nothing under the constraint-only reading, and under the entailing one it derives
only `(thing X)` (`starter_test/no-shipped-declaration-makes-an-argument-a-thing`). A
`(genlArg P n thing)` declaration says position `n` holds a type, and the constraint-only
reading convicts an individual there.

**Both readings prove the same sentences over the shipped ontology.** A membership or
`genl` edge an argument declaration in `resources/kb/` derives is written in a KB file
where the constraint-only reading could not prove it otherwise, so a derivation the
entailment stores is a copy of a sentence a context it sees already holds, or a
membership `provers/ArgTypeProver` answers
(`starter_test/the-constraint-only-reading-proves-every-sentence-the-entailment-derives`).

## What this is not

`provers/ArgTypeProver` already answers a ground `(animal Fred)` goal from exactly this
declaration — arg read as an inference is not new. What is new is that the type
becomes a **record**: a handle, a justification naming what it rests on, a place in the
taxonomy that `isa?` / `types-of` and the definitional checks read, and a datum the
agenda fires rules on. A prover's answer is none of those, and it is confined to a
CapitalCamelCase individual; `genlArg` entails a `genl` edge, which no prover can.

## An argument constraint only adds support

With the toggle on, an argument constraint derives the membership it names and never
refuses a sentence on the memberships its argument holds (`checks/entailment-covers?`).
A declaration read as an entailment says Fred *is* an animal, so there is no state of the
KB in which Fred fills the slot and fails it. The same holds of every kind that types a
symbol: `arg`, `genlArg`, `interArg`, the covering forms and the homogeneity forms, from a
declaration written in the asking context or inherited by it, and for a declared type the
hierarchy does not hold yet, which derives nothing until it does.

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
symbol whose memberships reach `thing` and miss the declared type, as
[taxonomy.md](taxonomy.md) describes.

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

A derivation at an arity its type denies is stored too. With `t` declared binary, `(arg rel
1 t)` and `(rel Rex Mary)` store the fact and `(t Rex)`, and a reader that sees the binding
reads `(t Rex)` OUT as an arity nogood
(`argtype_entail_test/an-entailment-of-a-length-its-type-denies-is-read-out`,
[taxonomy.md](taxonomy.md#arity)).

**What the entry point still asks of the derivations.** `checks/entailment-check` walks the
whole cascade before anything is stored and refuses the sentence when a derivation is one
a definitional check refuses on its own syntax, with the derivation's violation and the
sentence in `:entailed-from`. Naming, well-formedness and edge stratification are asked of
each derivation as it is stored (`special/inadmissible`): a derived `(genl X T)` that closes
a taxonomy cycle is dropped and reported in `(violations kb)`, since the derivation runs
after the triggering sentex is stored and inside a fixpoint, neither of which may abort
halfway.

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
| `special/record-arg-types` (`v/record-arg-types`) | the pass over a store loaded without the derivations |

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
(`special/rederive-descended`): the retraction path reads the justifications the sweep
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
  edge's sub-predicate. It is the taxonomy twin of `entail-existing`, and there for the
  reason `subsumption-seeds` beside it is: the arriving datum is the *edge*, and nothing
  else on the assert path re-examines the facts it just brought under a declaration;
* **context edge meets both** — `entail-under-context-edge`, from
  `special/reconcile-context-edge`, re-deriving the facts stored in the arriving
  `(genlCx sub super)` edge's `sub` and every context under it, since the edge makes the
  declarations above `super` visible to them, and the facts and declarations the edge
  gives a new common descendant ([Where a mint is placed](#where-a-mint-is-placed)). It
  reads the smaller of that extent and the extent of the declared predicates, by index
  counts, which `lein perf`'s `genlcx-edge-beside-declared-facts` holds.

Every order of {declaration, fact} reaches the identical KB, and so does every order of
{declaration, fact, edge}. That is the gate:
`every-arrival-order-reaches-the-same-belief` runs all six orders of {declaration, fact,
a competing type}, `every-arrival-order-of-the-three-ingredients-mints-the-same-type`
runs all six of {declaration, fact, edge}, and
`every-arrival-order-derives-through-an-inherited-declaration` runs all 120 of {local
declaration, inherited declaration, predicate edge, context edge, fact}, with a sampled
twin at the default selector.

No member of the family refuses on a membership under the entailing reading, so the
**facts** a KB holds are the same in every order as well as the derivations. The
constraint-only reading keeps a refusal half with no such reach: it convicts on an
absence, so a KB given the ingredients in different orders under
`VAELII_ASSERTIVE_ARG_TYPES=0` can hold different facts ([taxonomy.md](taxonomy.md),
"What each constraint does in each arrival order").

**A declared type the hierarchy does not hold yet mints nothing, and then everything.**
`mintable-type?` asks whether the type reaches `thing`, and it reads the hierarchy as it
stands, so a declaration and its facts stored before that edge minted nothing. The
declaration is kept in the refusal record, and the settle that sees a `genl` generation
move re-asks it; once the type is mintable, `entail-existing` runs for it again and mints
over every fact stored meanwhile ([exceptions.md](exceptions.md), "A refused firing is
remembered as bindings"). Until then the declaration reads none of its facts: every arm
asks `mintable-type?` of the declaration's own type before it draws, so the extent would
yield nothing. The answer is held per `genl` generation (`tax/genl?-global-held`), so a
sweep over n facts walks the type's ancestors once rather than n times.

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

The starter's `(arg parentOf 1 organism)` lives in `CxLife` while the individuals live in
`CxNaturalWorld`, below it, so a `parentOf` fact there derives `(organism X)` in
`CxNaturalWorld`. Every argument position in the shipped ontology is declared, so a
toggle-on starter load derives a membership per declared position, less the ones
pruning withholds (the table under [Cost](#cost)). The root's own `genl` supertype
position is the single undeclared one, and `CxCore` says why beside it: `thing` cannot be
a proper subtype of itself, so the constraint the root would fail is the wrong constraint
rather than a missing one.

### Where a mint is placed

A mint is placed at each maximal context that sees both the fact and the declaration, as a
forward firing and a placed nogood are placed (`special/pair-placements`). Where the
fact's context sees the declaration, that context is the one placement. Where it does
not, the placements are the maximal common descendants of the two contexts, and each
mint's justification also names the `genlCx` edges its placement sees the fact through.
With `(P a b)` in CxTop and `(arg P 1 T)` in CxMid below it, `(T a)` is stored in CxMid,
believed at CxMid and below, and absent at CxTop. With the fact in CxL, the declaration in
CxR and both under CxTop, a CxJoin under CxL and CxR is the placement, one per maximal
common descendant.

Each arrival direction reaches the placement:

- a **fact arriving** reads the declarations of its predicate and the predicate's
  ancestors that its context does not see and shares a descendant with
  (`special/deduce-below`): one argument-root read per declaring kind and declared
  ancestor, skipped when no `genlCx` edge comes up to the fact's context;
- a **declaration arriving** places each fact of its extent at the pair's placements
  (`entail-existing`);
- a **`genlCx` edge arriving** draws over the facts and declarations stated in the
  contexts a context under its `sub` sees and its `super` does not, against the facts and
  declarations `super` sees (`entail-under-context-edge`). A placement the edge leaves below
  a more general one loses its justification in the settle (`special/surplus-placements`),
  so every arrival order stores the same mints
  (`argtype_entail_test/a-mint-is-placed-at-the-most-general-contexts-that-see-the-fact-and-the-declaration`);
- a **`genlCx` edge leaving** takes the mints that named it, and `rederive-descended`
  draws the pair again at the placements that stand. A context under its `sub` can also
  become a maximal common descendant of a pair placed in a context it saw only through the
  edge; the settle reads the mints placed in those contexts, and with pruning on the
  records there that withheld one, and draws each pair again
  (`special/departed-context-edge-mints`). `lein perf`'s
  `genlcx-edge-leaving-beside-distant-mints` holds the cost flat in the mints stored
  elsewhere
  (`argtype_entail_test/a-genlCx-edge-leaving-places-the-mint-at-the-common-descendants-it-gives-back`).

Two cases are not placed this way. A `genl` route edge or a trigger membership is read
from the placement, so one stated below the placement draws no mint there. An `except`
that hides an ingredient at a placement drops the mint there and places none below it,
as at the fact's own context.

### An except of an ingredient

A derivation is not drawn in a context from which an `except` hides one of its
ingredients: the fact, the declaration, a trigger membership or an edge on the route
(`entail-arg-type` asks `exc/except-hidden-fn`), as a rule firing is not placed there
([contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree)). The
`except` moving reaches the derivations in either direction through the settle
(`special/except-move-sweeps`). An `except` arriving drops each derivation resting on its
target that the derivation's context no longer sees, so the KB holds what the `except`
arriving first leaves. An `except` leaving draws again what its target's arrival draws:
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
lets the mint's context see the membership.

Both arrival orders reach that state, and neither remembers how it got there:

* the specific membership **first** — `special/entail-arg-type` finds it
  (`checks/subsumed-mint`) and writes no record;
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
times as edges leave it.

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
the subsuming membership must not itself rest on the mint.

**Nothing records a withheld mint.** It comes back when the record that displaced it
leaves belief or the store — retracted, defeated or swept — and the settle finds it by
re-deriving the mints that departure can have released (`special/withheld-releases`), as
`deduce-arg-types` derives them for a fact arriving now:

| the record that left | the facts re-derived |
|---|---|
| a membership `(T x)` | the facts naming `x`, for the mints about `x` |
| a `genl` edge `(genl sub super)` | the same, for `sub`, each type under it and each member of one |
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
it, so a record that is not a mint coming IN while a believed record subsumes it — an
author's `(animal Fred)` beside `(dog Fred)` — has the facts naming `Fred` re-derive that
one sentence, and each whose mint of it was withheld adds its justification.

The KB **answers** the same either way: `isa?`, matching and the definitional checks all
read the taxonomy, which reaches `animal` from `dog` with or without a record in between.
Storage differs — the shipped starter holds 2,568 sentexes against 3,561, CxCore 932
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
that releases a declaration whose type has just reached `thing`.
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
| the declared type is not one the hierarchy holds | nothing, and no conviction either — a name that does not reach `thing` is not a type we invent a membership in. This is where a structural constraint lands without needing a list of exemptions to keep in step |
| a `genlArg` position filled by the declared type itself | nothing — `(genl t t)` is a reflexive edge `wff` refuses, so `arg-entailments` never draws it. A `(genlArg P n thing)` declaration over a sentence whose position `n` holds `thing` would otherwise store a violation |
| a **function application** in the position | `args-problem` / `genls-problem` check it against the function's declared `result` / `genlResult` and refuse where the result misses ([nat.md](nat.md)) — but nothing is minted, a declared result being a claim about the *function* and not about this application, and a compound having no membership to mint |
| a genuine negation, or a rule | not argument-checked, so not entailed from either |
| a **query** | nothing, ever. The entailment is on the store path alone |
| a bulk or dump load | skipped: the fact-direction derivations ride on the checks `*bulk-load?*` skips, and a dump import writes records directly. `v/record-arg-types`, run once after the load on the recovered KB, records what the stored facts derive, so the store then holds what a per-fact load holds (`argtype_entail_test/a-bulk-loaded-store-records-its-derivations-once`) |

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
the run stores twice as many sentexes, so the ~1.9× is the minting, not the gate.

**With subsumed mints pruned, the default, a membership a settle moves costs one mint-roster
lookup**, and nothing on a KB that holds no mint. The records the settle relabelled are
filtered by shape (only a membership, a `genl` edge or a `genlCx` edge can subsume a mint)
and by transition (a record that did not move subsumes what it subsumed before), and an
empty roster stops the trigger before any record is read. A membership about a term
holding no mint reads no posting however many facts name the term — the one read the
release adds for a membership that is not a mint, `checks/subsumed-mint`, is the term's
slot roster — which `lein perf`'s `mint-withdrawal-under-busy-term` holds. A `genl` edge
still reads its subtree's stored extent, the read `entail-under-edge` makes for the same
edge. The release is paid on a departure rather than on a write: a membership leaving
re-derives the facts naming its term, a `genl` edge the facts naming each term under it,
and a `genlCx` edge the facts stored under it, and a settle that moves none of the three
reads nothing about the mints the KB withholds, which `settle-beside-withheld-mints`
holds. The gate in front of the release reads the taxonomy's declaration roster rather
than the index, so `assert_cost_test`'s budgets are the ones the entailment alone sets
whichever way the switch stands. With it off none of that runs.

**`interArg` is read behind an O(1) gate where the other two are unconditional**, and
the asymmetry is deliberate. `arg` is what a typed ontology is mostly made of, so its
declaration read pays for itself on the facts it constrains. The shipped ontology declares
no `interArg` at all, and the check runs on *every* assert — measured at **~11% per
assert** of a declaration-carrying predicate for a retrieval that found nothing, against a
`count-with-functor` that answers "is one stored at all" for free. Add a fourth
argument-constraint kind the same way: gate it until something declares it. A ratio-based
perf check cannot catch this class, since a constant added to every write divides out
(`bench/vaelii/bench/perf.clj` says so in its preamble).

## The gates

`lein gate` runs the suite under the entailing reading, the default. The constraint-only
reading is the `assertive-off` sweep (`VAELII_ASSERTIVE_ARG_TYPES=0`): `lein test-sweeps`,
`lein test-matrix` and the `deep` workflow run it on the default backend, and `lein
test-matrix --owed` names it for a change to `checks.clj`, `special.clj` or
`resources/kb/`. Both readings must fail the same set and run the same number of
assertions, as every sweep must ([CONTRIBUTING.md](../CONTRIBUTING.md)), so a test whose
count or answer depends on the reading pins one: `tu/with-entailing` where the entailment
is its subject, `tu/without-entailing` where the constraint is.

On `memory` at `:default` both readings run 5,102 tests, and a per-namespace count
(`VAELII_TEST_NS_COUNTS=1`) puts every namespace at the same assertion count under both.
The sampling oracles `arg-root-retrieval-test` and `matches-hierarchical-test` run the
same count under both readings. `full-kb-test`'s small-KB twin samples derived literals
per context, where the mints sit, so it pins the entailing reading. Subsumed-mint pruning
(`VAELII_PRUNE_SUBSUMED_MINTS`) acts only on mints, so the constraint-only run leaves it
idle; the tests of pruning pin the entailment on.

`backend_parity_test` pins the toggle off inside its scripted session. That namespace's
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

## Suffix homogeneity: `interArgs` and `interArgAndRest`

`(interArgs R T)` says that when any argument of an application of `R` is a `T`, every
argument is a `T`. `(interArgAndRest R n T)` says the same of the positions from `n` to the
end of each application and leaves the positions before `n` unconstrained. `(interArgs R
T)` states what `(interArgAndRest R 1 T)` states, and two forward rules in CxCore derive
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
- **Behind a gate.** Both readings sit behind the taxonomy `:props` gate the covering
  forms use.

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
`genl` against a syntactic type. `(quotedArg name_of_guy 1 string)` refuses `(name_of_guy 5)`,
5 being a number and not a string, and admits `(name_of_guy "Bob")`. It is the mention twin
of `arg`: where `arg` reads the referent's type, `quotedArg` reads the argument's own
syntax, which is decidable from the value — so it is **checked, never entailed**, there
being nothing to mint about a term that already is what it is. Open-world about a kind it
does not type (a compound) and about a declared type outside the syntactic lattice, so an
imported constraint on a domain collection never convicts a value it cannot judge.
`checks/args-quoted-problem`, behind the same O(1) gate as `interArg`. Why the kind
decides at all, rather than every non-symbol being exempt:
[defenses.md](defenses.md#a-value-is-typed-by-its-kind-and-the-openness-moves-to-the-declared-type).

**Checked and never entailed is not the same as read literally.** Whose declarations speak
for a tuple is one question for all four spellings — `res/constraining-predicates`, the
predicate's own and every super-predicate the asking context can see — so a `quotedArg` on
`pAgeOf` refuses a `pInfantAgeOf` tuple at the entry point. `provers/MetaConstraintProver`
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
so `(quotedArg p n positive_integer)` refuses `-5` and admits `5`, exactly as
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

`symbol` is the exception, and is **mention-only**. A symbol does not denote itself, so
the set of names and the set of things named are not one set — `parentOf` written in a
sentence denotes a predicate, and `(Quote parentOf)` denotes the symbol. `symbol` is below
`linguistic`, which is disjoint from `relation`, so no term is both a symbol and a
predicate.

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
making `checks` write, for the sequencing reason above; and a dry-run mode, since
`preview` has its own machinery and the two are not wired together.

**On by default.** The constraint-only reading stays available under
`VAELII_ASSERTIVE_ARG_TYPES=0`, and the tests that assert it pin it there
(`tu/without-entailing`).
