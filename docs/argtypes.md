# Assertive argument types: `arg` as an entailment

- **Covers:** how, by default, an `arg` / `genlArg` / `interArg`
  declaration also mints the type it constrains as a derived, justified, retractable sentex.
- **Not here:** `arg` / `genlArg` read as a constraint that rejects a wrongly-typed
  argument (the opt-out `VAELII_ASSERTIVE_ARG_TYPES=0` reading) → [taxonomy.md](taxonomy.md); `transitiveInArg`,
  which carries a stated claim rather than a declared type across an argument →
  [inherit.md](inherit.md).
- **Assumes:** sentex, justification, context, `genl` → [glossary.md](glossary.md).

## Relation-wide declarations and the runtime boundary

`arg` (including `arg1` / `arg2` / `arg3`), `genlArg`, `quotedArg`, `interArg`, and the
covering forms `args` / `argsGenl` / `argAndRest` / `argAndRestGenl` (below)
accept a `relation` as their subject: either a predicate or a function. Accepting and
storing a function's declaration does **not** yet guarantee recursive enforcement of
its input constraints inside a nested function application. The current checks read
the asserted sentence's argument declarations. For `arg` / `genlArg`, a function
application filling a constrained slot is checked through its `result` / `genlResult`,
not by recursively checking every input against that function's declarations.
`quotedArg` instead exempts compound arguments from its value-kind check.
Recursive function-input enforcement is follow-up runtime work, not supplied by the
vocabulary generalization.

### A unary predicate declares a position only when its `genl` parent does not imply it

An `arg` declaration on a unary predicate and a `genl` edge above it can say the same
thing, and which of the two is right turns on where the parent sits relative to the type
the declaration names.

`fixed_arity` carries `(arg fixed_arity 1 relation)` and `(genl fixed_arity relation)`
names that same type. The edge concludes `(relation 5)` from `(fixed_arity 5)` and
nothing is disjoint from `relation` for a number, so the declaration is the only refusal
there is; drop it and `(fixed_arity 5)` is accepted. `variable_arity` and the function
marks are in the same position and keep theirs.

`instance_relation_predicate` is the other case. Its parent is `binary_predicate`, which
sits **below** `predicate`, so `(arg instance_relation_predicate 1 predicate)` restated
in a weaker form what the edge already concludes, and turned that conclusion into a
precondition — the declaration demanded of the argument the very type the assertion
supplies:

```clojure
(assert kb '(arity pairOf 2) 'CxUniverse)
(assert kb '(instance_relation_predicate pairOf) 'CxUniverse)  ; was :arg-type
```

`(arity R 2)` derives `fixed_arity` and the relation-wide `binary`, so `R` is a
`relation`; it says nothing about predicate or function, two arguments being a shape
either kind has. `outside-declared-type?` convicts an argument whose closure reaches
`thing` and does not reach the declared type, so the classification was refused for a
kind it had not yet stated — while the same pair written in the other order was accepted.

That asymmetry is not by itself the argument for dropping the row. The refusal half is
order-sensitive wherever a declaration narrows a type the argument already holds, by the
design stated below under "Three directions": it convicts on an absence, so a KB given
`(arg ownsGadget 1 gadget)`, `(artifact Widget)` and `(ownsGadget Widget Widget)` in
different orders holds different facts, and no change here alters that. What these six
marks had on top of it is a declared type their own `genl` parent already supplies — the
declaration demanded its own conclusion — so the six declare no position:
`instance_relation_predicate`, `type_relation_predicate`, `equivalence_relation`,
`injection`, `surjection` and `bijection`.

Both refusals the rows carried survive the drop, and one of them sharpens:

| argument | with the row | without it |
|---|---|---|
| a term reaching only `thing`, or a number | `:arg-type` | `:arg-type`, through the `(arg fixed_arity 1 relation)` floor the mark inherits |
| a `function` | `:arg-type: must be a predicate` | `:disjoint: cannot be both instance_relation_predicate and function` |
| a relation whose kind is not yet stated | `:arg-type` | accepted, and the mark supplies the kind |

`arity_vocabulary_test/a-predicate-only-classification-is-order-independent-of-the-arity`
compares the two orders on the whole closure rather than on an acceptance, and
`an-arity-alone-leaves-the-relation-kind-open` asserts the two refusals that remain.

### The policy classes declare one position and their specializations declare none

`fixed_arity` and `variable_arity` each carry `(arg C 1 relation)`. Nothing below them
carries one. The parent's declaration descends the predicate hierarchy, so
`(fixed_arity_predicate Fred)` with `Fred` a person is refused `:arg-type` all the same,
while a narrower `(arg fixed_arity_predicate 1 predicate)` would refuse the wrong thing:
a relation whose only stated type is `variable_arity` reaches `relation` and not
`predicate`, so `(binary_predicate P)` written after `(variable_arity P)` would report the
argument's type where the contradiction is the arity policy. The two are one
contradiction and report `:disjoint` in either order. A relation classified into the
wrong kind is caught by `(disjoint predicate function)` through the `genl` edges.

## The covering constraints: typing a variable-arity tail

`arg` and `genlArg` name one numbered position. A variable-arity relation whose tail
repeats one role has no largest position to name, and `(args R T)` types the whole
admitted tail instead: every accepted position of `R` is an instance of `T`. `(argsGenl R
T)` is the subtype reading — `argsGenl` to `genlArg` what `args` is to `arg`. `(argAndRest
R n T)` and `(argAndRestGenl R n T)` type position `n` and every later one, so a relation
whose head positions carry their own `arg` declarations and whose tail repeats one role is
typed exactly. `(args R T)` states what `(argAndRest R 1 T)` states.

A valid unbounded tail: a `variable_arity` `herd` with `(arityMin herd 2)` and `(args herd
animal)` accepts `(herd Rex Bossy)` and `(herd Rex Bossy Clarabelle)` while refusing a
member the KB places outside `animal`, at whatever length the tail reaches.

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
- **Convict-only, and open-world.** A covering constraint convicts a tail value it places
  outside the type; an unknown argument is no evidence and passes. It mints nothing and
  stops short of the retroactive reach `arg` runs under the entailment toggle, so a covering
  declaration arriving after the facts convicts none of them — the same open-world
  stop-short `arityMin` records, and order-sensitive in the way every constraint's refusal
  half is.

The walk is over the positions a sentence has, not a re-counted tail. `arity-problem`
refuses a length the relation does not admit before the covering check runs, so the arity
reader and the covering check never hold two answers about where the tail ends.

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

## What this is not

`prover-types/ArgTypeProver` already answers a ground `(animal Fred)` goal from exactly this
declaration — arg read as an inference is not new. What is new is that the type
becomes a **record**: a handle, a justification naming what it rests on, a place in the
taxonomy that `isa?` / `types-of` and the definitional checks read, and a datum the
agenda fires rules on. A prover's answer is none of those, and it is confined to a
CapitalCamelCase individual; `genlArg` entails a `genl` edge, which no prover can.

## One reading, not two

With the toggle on, `args-problem`'s **symbol arm yields** to the entailment
(`checks/entailment-covers?`). A declaration read as an entailment says Fred *is* an
animal, so there is no state of the KB in which Fred fills the slot and fails it: the
conviction and the entailment are two readings of one declaration, and only the second
one holds. The condition is `arg-entailments`' condition term for term — an eligible
argument, a type the hierarchy holds, a declaration that speaks for this context — so
the two arms cannot disagree about which declarations mint.

Three things still convict, because no mint can answer them:

- a **value**, which carries its type in its syntax — `5` is not a `string`, and no
  membership can be asserted of it;
- a **function application**, typed by its function's declared `result`;
- an **inherited** declaration, which constrains a descendant context without minting
  there (`declares-locally?`) — so in that context the constraint reading is the only
  reading there is.

Running both readings at once stops the cascade, which is the reason only one of them
holds. A minted `(t1 Fred)` re-enters the check; a conviction arm reading `t1`'s own
declaration convicts it for Fred not yet being a `t2`, and the conclusion `(t2 Fred)` is
drawn from is dropped. Such a cascade closes only for an argument holding **no** type at
all, since one unrelated membership — or a unary triggering sentence, which types its own
argument — convicts every mint after the first.

## The entry point refuses what the sentence entails

The refusal did not disappear with the symbol arm; it moved one step along the
derivation. `checks/entailment-check` walks the whole cascade of prospective mints before
anything is stored and reports the first the KB could not admit, so **the entry point
refuses a sentence exactly when it would refuse what the sentence entails**:

```clojure
(v/assert kb '(rock Bert) 'CxWorld)
(v/assert kb '(disjoint animal rock) 'CxWorld)
(v/assert kb '(arg parentOf 1 animal) 'CxWorld)
(v/assert kb '(parentOf Bert Mary) 'CxWorld)
;; throws :disjoint — "arg constraint: (parentOf Bert Mary) entails (animal Bert),
;; which cannot be admitted — disjointness violated: Bert cannot be both animal and rock"
```

The violation is the **mint's own**, so its `:type` is what `refuses-assert?` weighs: a
disjointness clash refuses under the `:refuse` policy and is arbitrated under
`:arbitrate`, exactly as a direct assertion of that membership would be
([exceptions.md](exceptions.md)).

Asked before the store, which is the whole point of asking here.
`special/entail-arg-type` asks the same question of each mint as it materializes, but it
runs *after* the triggering sentex exists — so a mint it cannot admit is dropped and
recorded, leaving the KB believing a fact whose declared consequence it rejects. Asked at
the entry point, the refusal reaches the writer and nothing is stored.

**Two arms, because a clash has two shapes.** `disjoint-problems` names an opposing
*handle*, so it reads clashes against **stored** memberships. A pair the cascade supplies
both sides of has no second record — `(p1 Fred)` and the `(p2 Fred)` it entails — and
`checks/cascade-clash` reads those as content instead. Without it the same clash would
refuse when the opposing type arrived earlier and pass when the cascade produced it.

**The derivation path still reports.** A rule firing has no caller to refuse and may not
throw mid-fixpoint, so `constraint-admission` leaves the conclusion standing and the mint
is recorded in the violations ledger as before. That is the split every other check
already draws.

Three convictions are **not** asked at the entry point — naming, well-formedness and edge
stratification. Those three live above `checks` (`special/inadmissible` is where the four
are one question), and a mint they convict is still dropped and reported by the
materializer.

## Where it lives

The **check computes it; the post-store slot materializes it.**

| | |
|---|---|
| `checks/constraint-entailments` | reads the declarations, returns `{:assert :because :position :kind}` maps — **writes nothing** |
| `checks/entailment-check` | walks the cascade of prospective mints at the entry point and refuses the first the KB could not admit — **writes nothing** |
| `special/deduce-arg-types` | materializes them, beside `deduce-lifts`, in `core/assert-one` and `chain/place-conclusion` |
| `special/entail-existing` | the retroactive direction: a declaration arriving over facts already stored |

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

* `kb/find-or-create-sentex` for the implied `(T arg)` in the asserting context;
* `derived-sentex-added` when it is new, so it reaches the closures and posts its
  exception re-check trigger exactly as a rule conclusion does;
* `jtms/->just` with antecedents **`[source-handle decl-handle & genl-edge-handles]`**
  and the declaring predicate as the informant, guarded by `has-justification?`;
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
the same witness rule everything else depending on a reachability takes.

## Three directions, or belief depends on arrival order

A declaration has to reach back over content already stored, or belief depends on which
of the ingredients arrived first. `decontextualized_predicate` lifts the facts already
present when it arrives, so `arg` has to as well — and with the descension the
ingredients are three rather than two, so there are three entry points:

* **fact meets declaration** — `deduce-arg-types`, on `assert` *and* on
  `place-conclusion`, because what a declaration says is a claim about the predicate and
  not about how a sentence arrived;
* **declaration meets facts** — `entail-existing`, walking the functor roots of the
  declared predicate's whole `genl` **spec** subtree, since the declaration binds every
  predicate beneath the one it names;
* **edge meets both** — `entail-under-edge`, walking the same subtree under the arriving
  edge's sub-predicate. It is the taxonomy twin of `entail-existing`, and there for the
  reason `subsumption-seeds` beside it is: the arriving datum is the *edge*, and nothing
  else on the assert path re-examines the facts it just brought under a declaration.

Every order of {declaration, fact} reaches the identical KB, and so does every order of
{declaration, fact, edge}. That is the gate:
`every-arrival-order-reaches-the-same-belief` runs all six orders of {declaration, fact,
a competing type}, and `every-arrival-order-of-the-three-ingredients-mints-the-same-type`
runs all six of {declaration, fact, edge}.

The *refusal* half has no such reach and is not meant to: it convicts on an absence, so
there is no second sentex to weigh and no pair to arbitrate ([taxonomy.md](taxonomy.md),
"What each constraint does in each arrival order"). A KB given the three ingredients in
different orders can therefore hold different **facts** and must hold the same
**entailments**.

`entail-existing` puts each stored sentex back through `constraint-entailments` in its
*own* context and narrows the answers to the arriving declaration, rather than
re-deciding the conditions. The two directions must agree about what a declaration
entails, and the only way to be sure of that is for them to ask the same function — it
buys the local/inherited rule below for free.

## The two rules that govern what is drawn

### Local declares, inherited only constrains

A declaration is *inherited* by every descendant of the context it was written in, and
there it constrains: an ancestor schema enforces its argument types in every context
below it. It does not **entail** there. An upper-band schema would otherwise spray
derived `(T x)` memberships across every context that inherits it — claims no author of
that context made.

So only a declaration written in the context being checked, or in `CxUniverse`
(which speaks for every context by construction), draws the entailment. Pure can express
this because every supporter records the context it asserts from.

This is also what keeps the **cast** quiet: the starter's `(arg parentOf 1 animal)`
lives in `CxLife` while the individuals live in `CxNaturalWorld`, so nothing is
minted over them however the toggle is set. The schema's own contexts are the other case
and mint freely, because there a declaration and the facts it constrains are written side
by side — `(genl animal thing)` sits in `CxCore` beside `(genlArg genl 1 thing)`.
Every argument position in the shipped ontology is declared, so a toggle-on starter load
mints a membership per declared position (the table under [Cost](#cost)). The root's own
`genl` supertype position is the single undeclared one, and `CxCore` says why beside
it: `thing` cannot be a proper subtype of itself, so the constraint the root would fail is
the wrong constraint rather than a missing one.

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
*reaches* `animal` by subsumption, and `(animal Muffet)` is minted anyway. That the engine
never materializes a supertype membership for *matching* is a different question —
matching fans the functor over the spec closure and needs no record. Here the declaration
makes the claim, and being a record is the whole of what this adds.

## The minted type is ordinary content

It is a **chaining seed**: it joins `seeds` alongside `subsumption-seeds` in
`assert-one`, so a rule with an `(animal ?x)` antecedent fires off a type the entailment
minted *within the same assert*. Without that, the same knowledge would derive different
things in different arrival orders — which is what this feature exists to fix, not to
cause.

It is **checked**: `special/inadmissible` runs the same triple `place-conclusion` runs
over a rule conclusion — naming, the definitional constraints, `wff`, and edge
stratification. A minted `(T x)` can clash with a disjoint membership, and a minted
`(genl X T)` can close a taxonomy cycle or a cycle through negation. A failure is
**reported, not thrown**: this runs after the triggering sentex is stored and inside a
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
| the argument is disjoint with the declared type | `entailment-check` refuses the assert with the mint's own `:disjoint` violation — no type is minted on the way to it |
| an **individual** in an `genlArg` position | `genls-problem` convicts; an individual can never acquire `genl` edges |
| the declared type is not one the hierarchy holds | nothing — a name that does not reach `thing` is not a type we invent a membership in. This is where a structural constraint lands without needing a list of exemptions to keep in step |
| a `genlArg` position filled by the declared type itself | nothing — `(genl t t)` is a reflexive edge `wff` refuses, so `arg-entailments` never draws it. This is what keeps `(genlArg arg 3 thing)` / `(genlArg genlArg 3 thing)` from minting `(genl thing thing)` over every `(arg P n thing)` the ontology carries — a violation per genl edge naming `thing`, otherwise, on the shipped load |
| a **function application** in the position | `args-problem` / `genls-problem` check it against the function's declared `result` / `genlResult` and refuse where the result misses ([nat.md](nat.md)) — but nothing is minted, a declared result being a claim about the *function* and not about this application, and a compound having no membership to mint |
| a genuine negation, or a rule | not argument-checked, so not entailed from either |
| a **query** | nothing, ever. The entailment is on the store path alone |
| bulk load | skipped with the rest of the checks (`*bulk-load?*`) |

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

The suite runs green on all eight backends `scripts/test-backends.sh` covers (the seven
legal record×index pairings plus the overlay decorator), **both ways** — the routine run
is the on-path default, and `VAELII_ASSERTIVE_ARG_TYPES=0` runs the constraint-only
reading. Same failing set (empty) in all sixteen runs. The disk arms matter here beyond
storage parity: a minted type is a real record with a real justification, so they are what
says `recover` rebuilds the same belief over it from the durable store.

The toggle-on run reports **6 fewer assertions** over the whole suite, and the small
number hides larger movements that nearly cancel. The sampling oracles fall:
`arg-root-retrieval-test` by 24 and `matches-hierarchical-test` by 132. Both draw a
fixed-size sample of stored facts and generate one probe per blanked argument position,
and with the entailment on the test world holds minted *unary* type facts, which displace
binary facts from the sample and yield fewer probes each. The rest of the suite gains the
balance back, for the same reason read the other way: a KB with more in it gives the
namespaces that count what they find more to find. Same sample size, same contract,
different composition — and the retrieval paths agree on both samples. It is not a test
doing less; it is evidence the feature is putting content in the KB.

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

It reads open-world **twice, in opposite directions**, and that is the whole of it. The
trigger side must be *positively established* — silence about argument `n`'s type is not
evidence that it is a `T`, so an unknown trigger leaves the constraint dormant rather than
firing it. The target side is convicted by *absence*, exactly as `arg`'s is. Getting
either backwards inverts the constraint: demand the trigger's absence and every untyped
argument fires it, excuse the target's absence and it never convicts anybody.

**One arrival order is not covered, and it is the family's, not this constraint's.** The
fact and the declaration each reach the other (at the entry point, and through
`special/entail-existing`), but the *trigger's type* arriving third does not reach back:
`(eats Rex Chunk)` and the declaration both stored, then `(carnivore Rex)`, and the
entailment is not drawn — nor is the violation reported, had `Chunk` been a `grass`.
`arg` has the same gap from the other side (an argument that acquires its first type
after the fact was admitted), and it is the same open-world non-reach
[taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order) records for the
whole family: a retroactive pass over it would have to decide whether pre-existing silence
about a type is a violation, which is the policy question nobody has answered.

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
`pAgeOf` refuses a `pInfantAgeOf` tuple at the entry point. `prover-types/MetaConstraintProver`
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
the set of names and the set of things named are not one set — `parentOf` is written as a
symbol and denotes a predicate. It therefore gets no placement in the domain lattice and
no disjointness: a use-level claim about it would be false of every predicate name.

## Scope

**In:** `arg`, `genlArg` and `interArg`, both directions, justified and retractable;
the local/inherited rule; the toggle; and the closure reading of all four spellings on the
query surface, which is neither direction of the entailment.

**Out:** entailing `quotedArg`, which is checked and never entailed (above), there being
nothing to mint about a term that already is what it is — it is *answered* along the `genl`
closure with the other three, which is a different question; `(ListOfType T)` element typing, which stays
disjoint-check-only so a `(ListOfType thing)` slot refuses nothing and sprays nothing;
making `checks` write, for the sequencing reason above; and a dry-run mode, since
`preview` has its own machinery and the two are not wired together.

**On by default,** and what changed to allow it: the shipped ontology loads under the
entailment without a `(genl thing thing)` violation, because `arg-entailments` refuses the
reflexive `genl` mint (the table under "Where it does not mint") the `(genlArg arg 3
thing)` / `(genlArg genlArg 3 thing)` meta-declarations would otherwise draw from every
`(arg P n thing)` the ontology carries. The constraint-only reading stays available under
`VAELII_ASSERTIVE_ARG_TYPES=0`, and the tests that assert it pin it there
(`tu/without-entailing`).
