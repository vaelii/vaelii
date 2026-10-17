# Ontological Engineering Principles

- **Covers:** the working rules for adding vocabulary and knowledge to a KB, each with an audit step to run on a vocab PR.
- **Not here:** why a particular piece of the shipped ontology is shaped as it is → [oe-defenses.md](oe-defenses.md). The vocabulary itself → [taxonomy.md](taxonomy.md).
- **Assumes:** you know the KB's metatypes (`genl`, `disjoint`, `partition`, `arg`) from [taxonomy.md](taxonomy.md).

Working rules for adding vocabulary and knowledge to a vaelii KB, collected from Pace Heart's ontology reviews. Each principle has a short handle, used to cite it, with its full name below; `genlPrinciple` and `specPrinciple` relate a special case to the principle it specializes. Most end with an audit step to run on a vocab PR before it ships.

## strongest form
*State knowledge in its strongest form*
**specPrinciple:** tightest parent, partition over disjoint, classify before you constrain
If you're about to assert P, but Q is also true and Q implies P, assert Q instead. The weaker fact stays derivable, so nothing is lost, and the stronger one carries more.

This applies to instance facts, argument types and disjointness alike:
- **Instances:** if a more specific true type exists, use it. If it doesn't exist yet, mint it (with its genl) rather than settling for the general one.
- **Argument types:** type each argument as tightly as the truth allows. If only one kind of thing can fill a position, the arg should name that kind.
- **Disjointness:** state it at the highest level that is true. If `(disjoint A B)` holds and A′ ⊂ A, don't also state `(disjoint A′ B)`.

**Audit:** for every line, ask whether a more specific true fact entails it.

## look before you mint
*Search everywhere before minting a term*
**genlPrinciple:** DRY
Before declaring a term new, search every place a definition can live: the starter KB, every overlay and knowledge directory, setup and migration code, test fixtures (they show intent), all branches, the live KB, and the discussion history where vocabulary gets proposed. A term "not found" in one place is often defined in another.

## tightest parent
*Parent types: the tightest true one*
**genlPrinciple:** strongest form · **specPrinciple:** walk down, broad under thing
Choose the closest existing parent, not a broad one that happens to be true. If you settle on a broad parent because nothing closer exists, say so in a comment and mark it provisional.

## factor out commonalities
*Name recurring meta-type combinations once*
**genlPrinciple:** DRY
If facts keep stating `(A P)` plus `(B P)` for the same P, and neither A nor B is a genl of the other, mint the intersection of A and B and use that. Stating a combination once beats repeating two facts everywhere.

**Check first:** if one type is a genl of the other, stating both is a case of **strongest form**: drop the weaker fact. Example: `core.txt` has `(genl instance_relation_predicate binary_predicate)`, so `(binary_predicate P)` next to `(instance_relation_predicate P)` is redundant, not a reason to mint an intersection.

## nesting values aren't individuals
*If values want a hierarchy, they aren't individuals*
Individuals take no genl. When an enumeration of individuals (`ReadAccess`, `WriteAccess`, …) starts wanting "write implies read", it was the wrong representation: make the distinctions predicates (`hasWriteAccess` genl `hasReadAccess`) or collections.

**Example:** with access kinds as individuals (`ShellAccess`, `WriteAccess`, `AdminAccess`), "admin implies write" has nowhere to live. As predicates, or as denotational functions with their corresponding predicates (see **don't skip the predicate**), it is a `genl` edge.

## different-type genl
*Beware predicate genls between differently typed args*
`(genl P Q)` where P's args are typed more broadly than Q's can silently widen types: every P fact mints memberships Q's arg types require. Prefer a guarded rule:
```
(implies (and (P ?x ?y) (T1 ?x) (T2 ?y)) (Q ?x ?y))
```
T1 and T2 are named separately because Q's two arguments can have different types.

**Example:** `(genl parentOf Q)`, where `parentOf` takes any animal and Q takes persons, makes every dog's parent a `person`. The guarded rule concludes Q only where both arguments are persons.

## meaning, not name
*Comments state the meaning, not the term again*
**specPrinciple:** references in seeAlso
A comment that restates the term's name adds nothing. Say what membership or the relation *means*, with examples, including the hard ones.

## classify before you constrain
*Classify before you constrain*
**genlPrinciple:** strongest form
When you're about to assert a constraint (especially `disjoint`), first check whether the types are classified as tightly as the truth allows. If a missing true genl would make the constraint derive, add the genl and drop the constraint.
- One genl does the work of many disjoints, and keeps working as the KB grows.
- It says *why* the separation holds.

**Example:** a type X with only a social genl needs a hand-written `(disjoint X Y)`. If X also has a true physical genl P, and `(disjoint P Y)` holds upstream, the disjointness derives and the hand-written line is redundant. The gap is the missing genl, not the missing constraint.

**Audit:** for every `disjoint`, `arg` or `genlArg`, walk both terms up their genl chains. An explicit constraint that a better classification entails is a smell.

## DRY
*One thing, one representation*
**specPrinciple:** factor out commonalities, look before you mint, state it once
If the same thing is represented two ways at the vocabulary level, merge them when feasible: two encodings drift apart, get queried inconsistently, and contradict silently.

Merging is infeasible when the encodings put some dimension (time, modality, provenance) in structurally different places. Example: a Davidsonian event encoding gets time from an assertion about the event, while an n-ary predicate gets it from the context it's asserted in. Then keep both, bridge them with explicit rules, and say why in a comment.

This is about vocabulary. Instance-level duplication can be fine for a good reason, e.g. two sources asserting the same fact, kept separately for provenance.

## state it once
*Don't state what the KB already derives*
**genlPrinciple:** DRY
If a fact follows from facts already stated (a genl implied by an intersection or a chain of genls, a disjoint implied by a partition or by two types' placements), don't state it. A stated redundancy is a second source for the same knowledge: when the facts it follows from change, it stays behind and asserts something nobody chose.

Two exceptions, each marked with a comment saying which one applies:
- **Implementation:** the engine needs the fact stated, for example because it reads the fact directly and doesn't derive it, or because it must hold in a context that can't see the facts it follows from.
- **Documentation:** stating it makes the KB easier to read or browse, for example the parent edges an intersection implies.

The same holds for comments. A comment doesn't restate a definitional assertion the KB already makes: no "the complement of X", "with Y it partitions Z" or bare member list when a `partition`, `intersection` or `genl` says it. The comment says what membership means, with examples, and leaves the structure to the assertions.

**Audit:** for every new `genl`, `disjoint` or `arg`, ask whether the rest of the KB already entails it. If so, drop it or mark which exception applies. For every comment, delete any clause that a definitional assertion already states.

## don't skip the predicate
*Don't skip the predicate*
Whenever you define a function, also define the predicates that relate each of its arguments to its result, and write rules in terms of those predicates. Skipping them forces a syntactic commitment (terms must be represented as non-atomic terms), and the representation should be semantic and syntax-agnostic. A waiver is a named decision, not a default.

## walk down
*Tighten genls by walking down*
**genlPrinciple:** tightest parent
To find a type's most specific genl, start at its current genl and try each direct spec: is every member of the type really a member of that spec, in the real world? If so, tighten, and recurse. Query the direct specs from the KB rather than recalling them.

Every type is a spec of `thing`.

## broad under thing
*Few direct specs of thing, all broad*
**genlPrinciple:** tightest parent
Very few types should be direct specs of `thing`, and those should be very broad. A narrow type directly under `thing` usually means a missing intermediate genl, and that gap also hides disjointness (see **classify before you constrain**). Tighten it with **walk down**.

## match the siblings
*Keep a type consistent with its siblings*
When ontologizing a type, check its siblings: everything it is `disjoint` with, and its `seeAlso` and `termsRelated` partners. Siblings should be placed at the same level and described in the same terms. An asymmetry between siblings is either a finding or a comment, never an accident.

## partition over disjoint
*Can `disjoint` be a `partition`?*
**genlPrinciple:** strongest form
A special case of **strongest form**. For every `(disjoint A B)`, look for a C whose members are exactly A ∪ B (plus any other pairwise-disjoint siblings). If the parts cover C, state `(partition C A B …)` and drop the disjoints it implies.

## does it have rules?
*Include X in concept Y? Compare what's true of each side*
**genlPrinciple:** no OE calligraphy
For a boundary question ("are prosthetics body parts?"), list the facts and rules true of X-with-Y and of X-without-Y. A side with nothing of its own, or only exceptions, isn't worth representing. Both sides rich usually means two concepts, often a type plus a role relation. A word naming each side is weak supporting evidence, since natural language is imprecise.

## no teleology
*No teleology in a type's definition*
A type says what a thing *is*, not what it's for. A type defined by purpose, capacity for a role, or designer intent ("can serve as", "used for", "made to") sweeps in every idle instance. Most pacemakers are nobody's body part; most are old trash.

**Audit:** if a type's comment defines membership by purpose or role, make it a relation (`bodyPartRoleOf ?thing ?body`), put the role's rules on the relation, and type its args by what the fillers are.

**Verb test:** read the verb that defines membership. A process or agency verb (operates, is used, serves, does work) brings purpose in. A stative verb (contains, has as a part, is made of) defines by structure, and the type it defines is rigid.

**Example:** a candidate `device` defined as "operates when powered" admits a brick warming in sunlight and a one-piece whistle. A `tool` defined as "used to perform work" admits a rock used as a hammer. `electronic_device`, "contains an electronic circuit", admits a dead phone and excludes the whistle. `machine`, "has parts that move relative to each other, driven by an energy source", admits a stopped clock.

**Examples:** a type `necessarily_part_of_something` is purpose in disguise. A broad `body_part` meaning "anything that can do the work of a body part" takes in every prosthetic; the kind plus a role relation keeps the two apart.

## beware entity
*Beware "entity" (a discrete, countable object)*
It looks like a natural kind and is far slipperier. Temporal and spatial slices of a thing ("Einstein while at the patent office", "Einstein minus his left pinky toe") behave almost exactly like the thing. Don't make discreteness a type's differentia; pick one that slices and parts inherit (made, grown, alive, has mass), or say explicitly how they're treated.

**Example:** "discrete objects whose form came from being made" excludes a slice of a made thing. `made`'s differentia, being shaped by an agent's action (found with **differentia from near-misses**), holds of a slice as of the whole.

## differentia from near-misses
*Find a type's differentia from its complement*
**genlPrinciple:** no OE calligraphy
List the members, then the near-misses: things under the same parent that aren't members. A property is the differentia only if every member has it and no near-miss does. If none survives, the type has no differentia and isn't worth reifying. The near-miss list is often a list of sibling types waiting to be named.

**Refinement audit:** before accepting a proposed classifier:
1. State what membership means under its parent, not just a list of familiar members. Fix the intended reading and context where a word has episodic, habitual or modal uses.
2. Give positive controls and close non-members under that parent, with a reason each belongs or does not. Challenge the proposed differentia with cases sharing its arity, argument types or temporal variation; those features need not capture its meaning.
3. Separate essential meaning from accidental association. A relation may be asserted, learned or changed in a happening without that relation itself describing a happening. For a proposed happening classifier, contrast an occurrence with a held state, not merely a changing truth value with a fixed one.
4. Ask what each classification would let the KB conclude or rule out (**does it have rules?**). Examples test a proposed definition; a finite list does not establish its necessity or sufficiency. Revise the definition when a real counterexample defeats it.
5. State the defining facts or rules where possible (**represent the definition**). For two encodings, make their argument/role mapping and context or temporal correspondence explicit; do not substitute an unrelated existential witness or assume a unique occurrence from the same participants.
6. Distinguish the semantic criterion from what the current engine can check (**truth, not provability**). Record which expected conclusions are derivable, which exclusions have explicit support, and which cases remain open. Failure to derive membership is not a negative control's proof of non-membership.

## no naked terms
*Hypothesized vocabulary comes with its definitional assertions*
Every proposed term, even in a thought experiment, ships as a block: its metatype(s), `genl`, every `arg`, its `disjoint`/`separating`/`orthogonal` relations to siblings, and its `comment`. Where they apply, also relation properties (`transitive`, `functional`, …) and `termsRelated`/`seeAlso`. A term without its definitional block can't be evaluated yet.

## ontology over quirk
*Ship the right ontology over an engine quirk*
When the right form (an intersection, a partition, a definitional rule, removing a redundant edge) collides with an engine quirk, test fragility or extra work, ship the right form and fix the engine or the tests. Workarounds that weaken the ontology need an explicit decision. A real engine bug that would corrupt answers is surfaced, not quietly worked around.

## truth, not provability
*Whether a sentence is true doesn't depend on how the engine proves it*
A KB author states true facts in their natural form, without knowing anything about the inference engine. The truth of a sentence doesn't depend on the order its conjuncts are written in, or on the path the engine takes to prove it ([from-prolog.md](from-prolog.md#what-your-habits-will-do-here) covers clause order). Where the natural form costs too much or proves less, the gap is an engine limitation to surface and fix, not a reason to change what the KB says (see **ontology over quirk**). Example: a definition stated as two genl edges instead of an intersection proves that each member of the defined type is a member of both parents, but doesn't prove the converse, that a member of both parents is a member of the defined type. The missing converse is lost entailment, and the fix belongs in the engine. Failure to prove a sentence is not evidence of its negation.

## event arg1
*The Davidsonian convention: the event goes in argument 1*
Any relation of arity 2 or more that takes an event takes it as argument 1.

**Audit:** for every relation with an argument typed `event` (or a spec of it), the event is argument 1.

**Example:** `(output ?event ?thing)`, not `(productOf ?thing ?event)`. `doneBy ?event ?doer` follows the same convention.

## default or enumerate
*Default + exception vs. enumeration*
When choosing between a default rule with exceptions and an explicit list of every known case, ask about a member that isn't listed:
- If something new were discovered, would you expect the default rule to apply?
- If you hypothesized something, would you want the default rule to apply?
- In a fictional or counterfactual context, would you expect the default rule to apply?

These are considerations, not a gate. The more you'd expect or want the default to reach new, hypothesized and fictional members, the better a default with stated exceptions fits. Where it shouldn't reach them, enumerate the known cases and conclude nothing about new ones.

**Example:** `metal_stuff` is a `solid` by default, with mercury as the stated exception. A newly found, hypothesized or fictional metal should come out solid.

## catbus principle
*Monotonic until a real fiction needs the overlap*
**specPrinciple:** default or enumerate
State a separation `:monotonic` in CxUniverse unless an existing fictional work shows a member of both types. One such example is enough: weaken the CxUniverse statement to default strength and restate it `:monotonic` in CxRealWorld, which fiction contexts do not inherit. A hypothetical example is not enough.

**Example:** the Catbus in *My Neighbor Totoro* is both a cat and a bus, so `(disjoint animal vehicle)` is a default in CxUniverse and monotonic in CxRealWorld.

**Audit:** for every default-strength separation that has a monotonic copy in CxRealWorld, name the fictional work and the member that justify it.

## no OE calligraphy
*True and useful, not OE calligraphy*
**specPrinciple:** does it have rules?, differentia from near-misses
The KB exists so an inference engine can conclude useful, true things about the world. When making a modelling choice, weigh what is useful as well as what is true: list what each option lets the engine conclude (new derivations, clash checks, persistence over time) and what it forbids. An option that is true but licenses nothing, or that defines a class almost nothing can belong to, loses to one that is true and does inference work.

## references in seeAlso
*References go in seeAlso/termsRelated, not comment prose*
**genlPrinciple:** meaning, not name
A pointer to another term belongs in `seeAlso` (one-way) or `termsRelated` (a symmetric cluster), not in a comment. The comment says what the term means.

## OE over code over text
*Prefer representation over code over prose*
**specPrinciple:** represent the definition, references in seeAlso
Knowledge stated in the KB beats knowledge enforced only in code, which beats knowledge written only in prose. A representation is the most precise form, and the engine can check it. Code is checked, but the KB cannot read it. Prose is neither checked nor readable by the KB.

**Audit:** for each constraint a PR adds in code or in prose, ask whether the KB could state it.

## represent the definition
*State a new term's definition as rules, not only in its comment*
**genlPrinciple:** OE over code over text
An inferentially inert defining rule is still better than text, because it is more precise. For new vocabulary:
- Consider its `seeAlso` and `termsRelated` partners.
- For every sentence of its comment, state the sentence as a fact or a rule where vaelii can. Use `set/inertRule` for a rule that must not fire. The comment keeps only what cannot be represented.
- Run `kb-integrity` over the new terms.

**Audit:** apply those three steps to every new term.
