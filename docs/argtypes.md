# Assertive argument types: `argIsa` as an entailment

- **Covers:** how, with the opt-in toggle on, an `argIsa` / `argGenl` / `interArgIsa`
  declaration also mints the type it constrains as a derived, justified, retractable sentex.
- **Not here:** `argIsa` / `argGenl` read as a constraint that rejects a wrongly-typed
  argument (the default, toggle-off reading) → [taxonomy.md](taxonomy.md); `argPreserving`,
  which carries a stated claim rather than a declared type across an argument →
  [inherit.md](inherit.md).
- **Assumes:** sentex, justification, context, `genl` → [glossary.md](glossary.md).

`(argIsa parentOf 1 animal)` says the first argument of `parentOf` is an animal. Assert
`(parentOf Fred Mary)` and the KB checks that claim against what it knows about `Fred` —
and when it knows nothing, **passes and stores nothing**. The declaration is read as a
constraint to test, never as a fact to derive.

This is the other reading: the declaration also *entails* what it constrains, and the
entailment is a derived, justified, retractable sentex under truth maintenance.

```clojure
(v/assert kb '(genl animal thing) 'UniverseContext)   ; the declared type has to be one
                                                      ; the hierarchy holds — see below
(binding [checks/*assertive-arg-types?* true]
  (v/assert kb '(argIsa parentOf 1 animal) 'WorldContext)
  (v/assert kb '(parentOf Fred Mary) 'WorldContext))

(v/isa? kb 'Fred 'animal 'WorldContext)          ; => true
(v/why kb (v/handle-of kb '(animal Fred) 'WorldContext))
;; {:premise? false
;;  :support [{:informant argIsa
;;             :because [{:sentence (parentOf Fred Mary) :premise? true}
;;                       {:sentence (argIsa parentOf 1 animal) :premise? true}]}]}
```

**Off by default** (`vaelii.impl.checks/*assertive-arg-types?*`; the root value reads
`VAELII_ASSERTIVE_ARG_TYPES=1`, which is how the whole suite is run under it). Entailing
changes what a KB *contains*, not only what it answers, so it is opt-in.

## What this is not

`provers/ArgTypeProver` already answers a ground `(animal Fred)` goal from exactly this
declaration — argIsa read as an inference is not new. What is new is that the type
becomes a **record**: a handle, a justification naming what it rests on, a place in the
taxonomy that `isa?` / `types-of` and the definitional checks read, and a datum the
agenda fires rules on. A prover's answer is none of those, and it is confined to a
CapitalCamelCase individual; `argGenl` entails a `genl` edge, which no prover can.

## Where it lives

The **check computes it; the post-store slot materializes it.**

| | |
|---|---|
| `checks/constraint-entailments` | reads the declarations, returns `{:assert :because :position :kind}` maps — **writes nothing** |
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
* `jtms/->just` with antecedents **`[source-handle decl-handle]`** and the declaring
  predicate as the informant, guarded by `has-justification?`;
* depth one past the deeper of the two;
* strength `:monotonic` conferred — the entailment adds no defeasibility of its own, so
  `conferred-class` caps it at the weaker of the fact and the declaration.

That is what makes it retractable. Drop the fact or drop the declaration and the type
goes, through machinery that already exists; defeat the fact and the type goes OUT with
it, because it is an ordinary derived node.

## Both directions, or belief depends on arrival order

A declaration has to reach back over content already stored, or belief depends on which
of the two arrived first. `decontextualizedPredicate` lifts the facts already present
when it arrives, so `argIsa` has to as well. Hence two entry points, mirroring
`deduce-lifts` / `lift-existing`:

* **fact meets declaration** — `deduce-arg-types`, on `assert` *and* on
  `place-conclusion`, because what a declaration says is a claim about the predicate and
  not about how a sentence arrived;
* **declaration meets facts** — `entail-existing`, walking the predicate's functor root.

Assert-then-declare and declare-then-assert reach the identical KB. That is the gate, and
`every-arrival-order-reaches-the-same-belief` runs all six orders of {declaration, fact,
a competing type}.

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

So only a declaration written in the context being checked, or in `UniverseContext`
(which speaks for every context by construction), draws the entailment. Pure can express
this because every supporter records the context it asserts from.

This is also what keeps the shipped ontology quiet: the starter's `(argIsa parentOf 1
animal)` lives in `LifeContext` while the cast lives in `NaturalWorldContext`, so nothing
is minted there however the toggle is set.

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
would make the two orders disagree. The cascade recurses only on *progress* (a sentex
created, or a justification added), which bounds it: both are content-keyed and monotone
within a pass, and the sentences that can be minted are a subset of the finite
`{(type, term)}` product the KB's vocabulary spans, so each step consumes one element of
a finite set that never shrinks.

## Where it does *not* mint

| case | what happens instead |
|---|---|
| the argument is disjoint with the declared type | the existing `:arg-type` refusal — no type is minted on the way to it |
| an **individual** in an `argGenl` position | `genls-problem` convicts; an individual can never acquire `genl` edges |
| the declared type is not one the hierarchy holds | nothing — a name that does not reach `thing` is not a type we invent a membership in. This is where a structural constraint lands without needing a list of exemptions to keep in step |
| a genuine negation, or a rule | not argument-checked, so not entailed from either |
| a **query** | nothing, ever. The entailment is on the store path alone |
| bulk load | skipped with the rest of the checks (`*bulk-load?*`) |

## Cost

2000 binary-fact asserts into one context, in-memory backend:

| | off | on |
|---|---|---|
| no declarations at all | 374–415 ms | 322–364 ms |
| 20 declarations, none matching the facts | 286–316 ms | 294–340 ms |
| every predicate declared (one mint per assert) | 317–336 ms | 609–673 ms, **2× the sentexes** |
| the starter load | 257–299 ms, 749 sentexes | 187–233 ms, 802 sentexes |

With the toggle **off** an assert reads one dynamic var and stops — the default path is
untouched. With it **on** and nothing to do, on/off straddles parity, which is as precise
as this bench gets; the shared `declaration-reader` is what bought that. Where it mints,
the run stores twice as many sentexes, so the ~1.9× is the minting, not the gate.

**`interArgIsa` is read behind an O(1) gate where the other two are unconditional**, and
the asymmetry is deliberate. `argIsa` is what a typed ontology is mostly made of, so its
declaration read pays for itself on the facts it constrains. The shipped ontology declares
no `interArgIsa` at all, and the check runs on *every* assert — measured at **~11% per
assert** of a declaration-carrying predicate for a retrieval that found nothing, against a
`count-with-functor` that answers "is one stored at all" for free. Add a fourth
argument-constraint kind the same way: gate it until something declares it. A ratio-based
perf check cannot catch this class, since a constant added to every write divides out
(`bench/vaelii/bench/perf.clj` says so in its preamble).

## The gates

The suite runs green on all eight backends `scripts/test-backends.sh` covers (the seven
legal record×index pairings plus the overlay decorator), **both ways** —
`VAELII_ASSERTIVE_ARG_TYPES=1` is what makes the second half possible. Same
failing set (empty) in all sixteen runs. The disk arms matter here beyond storage
parity: a minted type is a real record with a real justification, so they are what says
`recover` rebuilds the same belief over it from the durable store.

The toggle-on runs report **79 fewer assertions**, all of them in two oracles —
`arg-root-retrieval-test` (49) and `matches-hierarchical-test` (30). Both draw a
fixed-size sample of stored facts and generate one probe per blanked argument position.
With the entailment on, the test world holds minted *unary* type facts, which displace
binary facts from the sample and yield fewer probes each. Same sample size, same
contract, different composition — and the two retrieval paths agree on both samples. It
is not a test doing less; it is evidence the feature is putting content in the KB.

`backend_parity_test` pins the toggle off inside its scripted session. That namespace's
question is whether eight storage backends answer hand-written expectations alike, and
the entailment would change the script itself: `(argIsa ownerOf 2 animal)` and
`(ownerOf Ann Rex)` both sit in `ParityContext`, so Rex would carry a second, independent
`animal` membership and retracting `(dog Rex)` would no longer take his type with it.
That is the feature working, tested where it belongs.

## The conditional form

`(interArgIsa P n T m U)` says that when argument `n` is a `T`, argument `m` must be a
`U` — the claim `argIsa` cannot make, since `(argIsa eats 2 meat)` demands meat of every
eater where `(interArgIsa eats 1 carnivore 2 meat)` demands it only of carnivores. It
entails the same way and just as strongly: `(meat Chunk)` from `(eats Rex Chunk)` and the
declaration, justified by both, once `Rex` is known to be a carnivore.

It reads open-world **twice, in opposite directions**, and that is the whole of it. The
trigger side must be *positively established* — silence about argument `n`'s type is not
evidence that it is a `T`, so an unknown trigger leaves the constraint dormant rather than
firing it. The target side is convicted by *absence*, exactly as `argIsa`'s is. Getting
either backwards inverts the constraint: demand the trigger's absence and every untyped
argument fires it, excuse the target's absence and it never convicts anybody.

**One arrival order is not covered, and it is the family's, not this constraint's.** The
fact and the declaration each reach the other (at the door, and through
`special/entail-existing`), but the *trigger's type* arriving third does not reach back:
`(eats Rex Chunk)` and the declaration both stored, then `(carnivore Rex)`, and the
entailment is not drawn — nor is the violation reported, had `Chunk` been a `grass`.
`argIsa` has the same gap from the other side (an argument that acquires its first type
after the fact was admitted), and it is the same open-world non-reach
[taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order) records for the
whole family: a retroactive pass over it would have to decide whether pre-existing silence
about a type is a violation, which is the policy question nobody has answered.

## Scope

**In:** `argIsa`, `argGenl` and `interArgIsa`, both directions, justified and retractable;
the local/inherited rule; the toggle.

**Out:** `argQuoted` / `argOneOf` (pure does not have the constraints, and adding them is
separate work from entailing them); `(ListOfType T)` element typing, which stays
disjoint-check-only so a `(ListOfType thing)` slot refuses nothing and sprays nothing;
making `checks` write, for the sequencing reason above; and a dry-run mode, since
`preview` has its own machinery and the two are not wired together.

**Off by default,** and what that rests on: the gate measures free and every invariant
above has a test, but the feature changes what a KB *contains*, and no shipped or
imported corpus has been loaded under it end to end.
