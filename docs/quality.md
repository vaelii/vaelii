# Reading the KB rather than the engine

- **Covers:** `kb-quality` — which rules never fire, how skewed the predicate extents
  are, how deep the rule graph's chains reach, how much of the taxonomy is connected,
  which argument declarations constrain nothing, which rules another rule already covers,
  which rule pairs would contradict each other if both fired — what each reading costs,
  and what each one does *not* mean.
- **Not here:** how a run went (iterations, derived conclusions, dropped ones) →
  [api.md](api.md)'s instrumentation block and [inference.md](inference.md); whether the
  engine's own grammar is read by anything → [predicates.md](predicates.md); the naming
  rules a type name obeys → [naming.md](naming.md).
- **Assumes:** sentex, handle, justification, informant, `genl` →
  [glossary.md](glossary.md).

`vaelii.impl.quality`, behind `vaelii.core/kb-quality`. Every other instrument here
reports on a **run**: `settle-stats` counts fixpoint iterations, `chain-stats` counts
derived conclusions, `violations` lists the ones that were dropped. None of them is a
reading about the *knowledge*, so the author of a large KB — who wants to know whether any
of it is any good — had no answer at all.

Seven questions, and the whole of this page is them:

| question | the read that answers it | cost |
|---|---|---|
| which rules never fire | per rule handle, the justifications naming it as informant | O(rules + firings) |
| how skewed are the extents | `count-with-functor` per predicate | O(predicates), each O(1) |
| how deep do chains reach | the rule graph, SCC-condensed | O(V+E) over *functors* |
| how much of the taxonomy is connected | the `genl` closure per type | O(ancestor **pairs**) — each type's whole up-closure is read to find its root, so a chain of V types costs Θ(V²) where it has V−1 edges |
| which argument declarations constrain nothing | the declared arity per stored declaration | O(declarations × super-predicates) |
| which rules another rule already covers | one match per rule pair sharing a consequent functor | O(candidate pairs), each a handful of unifications |
| which rule pairs would contradict each other | one unifier per rule pair the consequent index brings together | O(candidate pairs) |

Plus the term-name set, walked **once** to find the functor names the first four readings
are about — which is the report's one superlinear term and the reason the total below
leads with it — and one record read per rule, which is what the last two need and the
postings cannot give.

**No reading fails a build.** A threshold on somebody's ontology is not a build failure:
`lein perf` checks the engine, and this reports on the content. The report's own cost is
checked: `lein perf`'s `quality-report-scaling` holds it to the vocabulary rather than to
the KB.

## One pass, and nothing new indexed

A `rule -> firings` index would be a second copy of the JTMS adjacency to keep in step,
which is the failure class the taxonomy's one record of its supporters, the index's
supporter families, exists to avoid. So every reading comes off state that is already
there:

- **One walk over the term-name set**, and one is the number. The functor names come off it
  by filter, and the type-shaped names come off *those* rather than off the term-name set a second
  time — every type name is lowercase-initial, so it is already in the first answer.
- **Three O(1) index reads per functor name** — the stored extent off the count-aware trie
  ([indexing.md](indexing.md)), and the rule postings *both* ways. That single pass is
  where the extents come from, where the chain graph comes from, and where the rule handles
  come from.
- **The firing census reads each rule's own `:consequences` adjacency** — the candidate set
  `restrength-informant*` already uses, filtered to the justifications whose *informant* is
  that rule, so a justification that merely uses the rule's handle as an ordinary
  antecedent is not counted. It never scans the justification map; on a store of millions
  of justifications the difference is the report existing or not.
- **The declaration census enumerates the declarations** and asks each what binds its own
  predicate's length, rather than asking every predicate what declares it. That is a map
  read where the predicate carries a length of its own and one read per super-predicate
  where it inherits one — the only term in the total that is not flat, and one bounded by
  the hierarchy *above* a predicate rather than by the spec subtree below it.
- **The record store is read for the rules the report lists** — a handful, capped by
  `:limit`, so a listed rule reads as its author wrote it rather than as a handle — and
  for the argument declarations, which are vocabulary and therefore few: 377 in the whole
  bundled ontology.
- **The two rule-hygiene readings read a record per rule**, and they are the only readings
  that do. A rule's antecedents, its consequent and the four slots deciding whether it can
  stand in for another live on the record and nowhere else, so this is the term nothing
  cheaper answers. It is `O(rules)` and never `O(sentexes)`: the rules are what a KB has
  hundreds of where it has millions of facts.

So the report is
`O(terms + rules + firings + ancestor pairs + declarations × super-predicates
+ candidate pairs)` and never
`O(sentexes)` — the **vocabulary and the rule set**, which is what the perf check's claim
says and what it measures: 8x the stored facts over 2.8x the vocabulary costs 1.5x, and 8x
the vocabulary costs 8x. A KB of a million facts about a hundred individuals has a
hundred-odd names in it, and that is the number the report answers to.

Rules are enumerated from the **rule index**, which means one absence worth knowing: a
rule the index cannot key by any predicate — an `:inert` one written with a variable
functor throughout, which is what the shipped ontology's own documentation rule is — is
outside the census. It is also a rule that runs in neither engine, so it could not
have fired.

## Which rules never fire, and the two categories beside it

Three outcomes, and four situations produce them:

| the situation | where it lands |
|---|---|
| the rule fired and a conclusion is believed | `:fired`; every recorded firing counts in `:firings` |
| nothing ever matched its antecedent | `:never` |
| it fired, and every conclusion is defeated | `:all-defeated` |
| it fired, and the support was later retracted | `:never` |

The last row is the one to read twice. **A firing is a *currently supported* one.** The
census reads live justifications, so a rule whose conclusion has been withdrawn has none
left and gives the impression that it had never fired. Firings-ever is a different question and
nothing here answers it — a KB does not keep a history of what it once believed.

`:all-defeated` is separated out because it is the more interesting finding: such a rule
runs, contributes nothing to belief, and would read as working from a firing count alone.

The counts are the headline and the lists are capped (`:limit`, 25 by default) with
`:truncated?` saying so. A listed rule carries `{:handle :sentence :context}`, and the
sentence is the one that was *written* — a rule is stored canonically numbered
([canonicalization.md](canonicalization.md)), which reads as gibberish.

## Extent skew: buckets to read, a Gini to record

Order-of-magnitude buckets are what an author reads (`10^0` holds the predicates with a
single fact); the Gini coefficient is the single number that goes in a baseline — 0.0 when
every predicate holds the same count, `(n-1)/n` when one holds everything, so a small
vocabulary cannot reach 1.0 and the figure must not be give the impression that it could.

Both are over **stored** counts, and that is not a default anybody should change: a
believed extent is O(n) per predicate ([api.md](api.md), "Stored vs believed"), which
would turn an O(predicates) report into an O(sentexes) one. The stored/believed
distinction is exactly what an author wants to see rather than have chosen for them.

The measured shape on one conversion of OpenCyc 4.0 — the corpus [kbs.md](kbs.md) is the
route to, read here at roughly 1.1M sentexes rather than at that page's own load, so the
denominator below is this run's and not that one's: Gini **about 0.96**, over ~7,600
predicates with an extent, of which about two-thirds hold exactly one fact and a handful
hold over 100,000.

## Chain depth, and the reason it is condensed

The rule graph runs consequent functor → antecedent functors. A KB's is **cyclic in the
ordinary case**: `(genl ?a ?b) & (genl ?b ?c) => (genl ?a ?c)` is a self-loop on `genl`,
and a transitive predicate is the commonest rule there is. So the depth pass condenses
strongly-connected components and computes over the condensation, which is a DAG.

Two mistakes are avoided by construction here, and both are cheap to make:

- **Memoizing the path rather than the node.** Memoizing only acyclic results makes a
  densely cyclic graph re-explore its whole reachable subgraph along every path — not slow
  but *exponential*, with no termination and only a JVM restart to clear it. Memoize the
  component.
- **Keying the condensation by the component itself.** Two node sets compare equal in
  O(nodes), and the condensation runs one such comparison per edge, which turns O(V+E)
  into O(V·E) — the same mistake wearing a quieter hat. Components are keyed by an integer
  id: measured on a 4,000-functor cycle, a run of over a second became tens of
  milliseconds.

Depth is reported **per rule** — the depth of the component its consequent functor lands
in — as a histogram plus `:at-least`, the fraction of rules in a chain at least that deep.
The distribution is the reading and a single number is not: most rules can sit at depth 1
while one outlier reaches 7, and an average hides both.

`:cyclic` counts a self-loop as the cycle it is. Counting only multi-node components would
report the commonest cycle in any KB as acyclic.

## Taxonomy coverage is two numbers

`:edged` is how many type names carry a `genl` edge at all. `:rooted` is how many reach
the root, reflexively, so the root counts itself. **The gap between them is the finding**:
a type with an edge into a disconnected island is counted by the first and not the second,
and `:islands` is exactly that difference.

The root is **found, not assumed**. `thing` is this engine's root and a converted corpus
brings its own, so whatever type the most others reach is the one reported against, and
the reading means the same on a corpus that never heard of `thing`.

The denominator (`:names`) is every type-shaped name in the vocabulary, and by
[naming.md](naming.md) that includes a bare lowercase word: `likes` is a legal predicate
*and* a legal type name. A name `relation?` answers true for, by a stored arity of two
or more or a `variable_arity` membership, is excluded from both names and edges, so a
sub-relation edge such as `core.txt`'s `(genl partition covering)` is not an island. A name
with no stored arity remains a candidate, so an untyped root or disconnected unary
island is not silently dropped.
This is why the gap is the finding rather than either fraction on its own.

The measured shape on the same OpenCyc conversion as the Gini above, and all three
counts are that one run's own denominator: of roughly 124k types, about 71% carry a
`genl` edge and about 64% reach the root — and the ~29% with no edge at all is a bigger
finding than either. A percentage taken from one reading over a denominator from another
would be a number nobody measured, which is why the type count here is this run's rather
than [kbs.md](kbs.md)'s.

## Argument constraints that constrain nothing

`(arg parentOf 3 person)` is admitted while `parentOf` has no declared length, because
the highest position a declaration names is a lower bound on the arity rather than a claim
about it. When a length does arrive — declared of the predicate, or inherited through a
`genl` edge from a super-predicate — the declaration is left constraining a position the
predicate provably does not have, and the entry point refuses the identical sentence one line
later. `:declarations` is what names those, and without it a declaration that is enforced
and one that enforces nothing look exactly alike.

It is the **entry point's own arm, re-asked** of content already stored, so what the census lists
and what an `assert` refuses cannot drift apart: whatever binds a predicate's length for
the entry point binds it here, and a predicate the KB has bound to no length strands nothing.
`interArg` names two positions and each is asked, since both are the same mistake.

A **`variable_arity`** predicate strands nothing either, however high the position: it reads
a tuple of any length from its declared arity upward, so a position past that length is one
its tuples really do reach, and the constraint fires on the tuples long enough to have it.
`lessThan`, `greaterThan` and `functionCorrespondingPredicate` are the shipped ontology's.

Belief-filtered, unlike the extent counts: a stored declaration nobody believes constrains
nothing for a reason that has nothing to do with the position it names, and listing it here
would report the wrong defect.

An entry is `{:handle :sentence :context :predicate :position :arity :via :message}`.
`:via` is the predicate the length was read off — the declaration's own where it carries
one, the super it inherits from otherwise, so an author is not sent looking for a
declaration nobody wrote. `:message` is the sentence the check itself wrote, carried rather
than re-derived, so this map and `check`'s answer say it in the same words. `:total` counts
the declarations walked, `:stranded-count` the ones convicted, and the list is capped by
`:limit` with `:truncated?` saying so.

`:typed-thing` lists the believed declarations that type a position `thing`, each as
`{:handle :sentence :context :facts}`, under the same `:limit`, and `:typed-thing-count`
counts them. Such a declaration mints nothing ([argtypes.md](argtypes.md#where-it-does-not-mint)),
and `:facts` is the number of facts of its predicate stored, the ones a narrower type
would type.

**A finding rather than an error**, and the reason it is a census question and not a
`violations` one: a stranded declaration constrains nothing, refuses nothing and mints
nothing, so there is no *newly* for a settle to report and it reads the same an hour later.
[taxonomy.md](taxonomy.md) has that argument in full, against the wrong-length **fact**,
which is a ledger entry.

## Rules another rule already covers

A stored rule **R2** is covered by a stored rule **R1** when one substitution σ over R1's
variables makes `ante(R1)σ` a subset of `ante(R2)` and `conseq(R1)σ` R2's conclusion. R1
then fires wherever R2 does and concludes at least as much, so R2 adds nothing the KB
would not have had.

Both halves are **predicate-genl aware, and in opposite directions** — the same asymmetry
[inference.md](inference.md)'s "Predicate subsumption in matching" describes, read once
forwards and once backwards:

- An antecedent of R1 on `P` is covered by an antecedent of R2 on a **spec** of `P`.
  Whatever satisfies `dog` satisfies `animal`, so a rule keyed on `animal` fires wherever
  one keyed on `dog` does.
- A consequent of R1 on a **spec** of R2's covers it. Concluding `(dog X)` answers every
  goal `(animal ?x)` would; concluding `(animal X)` answers nothing about dogs, so a
  consequent on a *super* does not cover. This is the half a reader expects to be
  symmetric and is not.

R1 must also be **at least as available**, and three slots decide that. Its `engines`
must include R2's — forward + backward covers forward-only and backward, every other set
covers only itself, and an inert rule (`#{}`) is covered by an inert rule alone, because
it chains in neither engine. **A default cannot stand in for a strict rule**: a
defeasible conclusion is defeated exactly where the strict one stands. The `effect` must
match, since a choice or constraint rule does not chain at all ([solving.md](solving.md)). And R1 must carry no `exceptWhen` R2
lacks — an exception is a binding R1 declines to conclude for and R2 concludes for, which
is exactly not covering it. What is *not* read is the rule sentex's own strength, which
says how the rule is defeated rather than where it runs.

Scoped from **R2's context**, which is the vantage the claim is made from: a rule covered
by one it cannot see is not covered.

**Every hit is a redundancy or a deliberate specialization, and the reading cannot tell
them apart.** An exact duplicate cannot be here at all — two rules alike up to variable
names, antecedent order or a symmetric argument order are one handle
([canonicalization.md](canonicalization.md)) — so what is left is a rule written for the
narrow case beside the general one, and whether that was the point lives in what the
author meant rather than in what the KB holds. The reading names the pair, the
substitution and the context, and leaves the judgement.

An entry is `{:subsumed h2 :by h1 :substitution σ :context C :sentence :by-sentence}`, and
σ is written in the two authors' own variable names rather than in the `?var0` numbering
both rules are stored under. `:total` counts the rules compared, `:subsumed-count` the
pairs found, and the list is capped by `:limit` with `:truncated?` saying so.

Pruned by consequent functor — the pairs are drawn from a grouping of the rules by what
each concludes, fanned over the genl closure of the covered rule's own predicate — and by
antecedent count. **The count prune is the one thing the reading
under-reports**: σ may collapse two of R1's antecedents onto one of R2's, so a rule with
more antecedents than the one it covers is missed. A missing hit is the safe direction for
a report that names redundancies.

## Contradictions in waiting

Rule pairs whose consequents would clash if both fired, and whose antecedents could hold
at once. Four kinds, asked of a pair in this order so one answering to two lands under one
of them:

| kind | the clash |
|---|---|
| `:negation` | one concludes `S` and the other `(not T)` where `S` entails `T` — `(dog X)` against `(not (animal X))`, and never `(animal X)` against `(not (dog X))` |
| `:disjoint` | two unary type conclusions about one term whose types a `disjoint`, `sibling_disjoint` or `disjoint_metatype` declaration separates ([taxonomy.md](taxonomy.md)) |
| `:functional` | two conclusions filling one `functional` slot for one subject with values that are not the same term. Both spellings of the mark count — `(functionalInArg P 2)` says the same thing about the same slot as `(functional P)`, and at position 2 only, this reading being arity-2 |
| `:asymmetric` | one tuple concluded both ways round under a predicate declared `asymmetric`. A self tuple `(P a a)` is not one — the ontology admits it |

The two property marks are read **up** the predicate hierarchy, as every constraint is
convicted against them: two `fatherOf` conclusions clash against `(functional parentOf)`.
A mark's reach is asked at three points — whether the KB declares any, which group a
conclusion joins, and whether two conclusions share one — and all three go through one
reader, so a spelling reaches the detector through every read or through none.

"Jointly satisfiable" is **shallow**, and five things rule it out: a literal appearing
under σ together with its own negation or with the negation of a predicate its own is a
spec of — `(properPartOf ?x ?y)` beside `(not (partOf ?x ?y))`, a spec's tuple being the
predicate's — one term claimed to be of two separated types, one
functional slot filled two ways no single filler meets, one term whose minimum length is
bounded above the exact arity it is claimed to have — `(arityMin ?p ?n)` with
`(greaterThan ?n 2)` beside `(symmetric ?p)` —
and one term an `arg` declaration demands be of a type disjoint from one the two rules
place it in — `arg` read with its covering forms, `(args P T)` and `(argAndRest P n T)`
typing every position they reach, `(genl a P)` typing `a` by `P`'s arity, and an
application written at any depth typed by its function's `result` and typing its own
arguments by its function's `arg` declarations. Each of the five is a **declaration read**: **no inference is run and no fact is
consulted.** This is what the rules say about each other, so a pair here is a clash that
*could* form rather than one that has — a clash already formed is in
`(contradictions kb)`, which is the other question and the other reader.

A **functional slot** is position *n* of a tuple under a `(functionalInArg P n)` mark,
read up the predicate hierarchy, and it holds one filler for each value of the rest of the
tuple. Two literals agreeing on the rest under σ fill it two ways no filler meets when they
put two distinct numbers, strings or other non-symbol atoms there, or a number beside a
variable the antecedents bound away from it with `lessThan` or `greaterThan`, or two
variables whose bounds leave nothing between them; two distinct symbols may name one
thing and stay a candidate. The reading names no predicate: it reads the KB's
`functionalInArg` marks, and `(functional P)` reaches it as the `(functionalInArg P 2)`
core.txt's forward rule concludes. The arity table is the shipped case, through
`(functional arity)`: `(arity ?p 1)` beside `(arity ?p 2)`, `(arity ?p 1)` beside
`(equivalence_relation ?p)`, which claims 2 by reaching `binary_predicate` up `genl` and
is read as `(arity ?p 2)`, and `(arity ?p ?n)` with `(greaterThan ?n 2)` beside
`(symmetric ?p)` each admit no `?p`, where `(arity ?p 2)` beside `(lessThan 1 ?n)` on the
same slot stays a candidate. A KB that does not mark a slot functional pairs its fillers
as two facts that can both hold.

The fifth rule-out reads the two consequents beside the antecedents, because the type an
`arg` declaration demands of one rule's variable is disjoint from the type the **other**
rule *concludes* about the unified term. `(arity ?r ?a) => (fixed_arity ?r)` demands `?r`
be a `relation` through `(arg arity 1 relation)`, and CxCriedWolf's
`(lied_before ?x) => (liar ?x)` places the unified term under `person`. No ground term is
both a relation and a person, so the two rules never both fire for one term and the pair is
dropped. The demand is read where a membership cannot state it, on either side: the test
world declares `(arg lied_before 1 person)`, so the same reading drops the pairs whose other
rule concludes a type no person has, such as a signed refinement of `integer`. A declared
domain the other conclusion does not exclude, and an undeclared one, both stay candidates
— two stated types clashing is the clash the pair reports, so at least one side of the
disjoint pair must be a declared arg type.

`genl` declares no type on its first position, and a spec of `P` has `P`'s length, so
`(genl ?r P)` demands `?r` the relation-wide exact-arity class of `(relation-arity kb P)`:
`binary` for a binary `P`, `unary` for a type. A rule over the specs of a binary predicate
then pairs with no rule concluding a type disjoint from `binary`, such as `person`, and
still pairs with one concluding a class of binary relations.

The unifier can bind one rule's variable to an application in the other:
`(metal_stuff ?x) => (solid ?x)` against a rule `(uninterrupted ?y) => (uninterrupted_time
(TimeOfFn ?y))` binds `?x` to `(TimeOfFn ?y)`. `(result TimeOfFn time)` types every
application of `TimeOfFn` a `time`, which is `acausal` where `solid` is `causal`, so the
pair is dropped; `(arg TimeOfFn 1 temporal)` types `?y` a `temporal` in the same way. A compound
whose head is a connective or a `predicate` is a formula and is not read. An argument of
a quoting predicate or quoting function, or at a position a `quotedArg` declaration types,
is a mention and is not descended into, as in the argument checks
([argtypes.md](argtypes.md)). `genlArg` and `genlResult` are not read:
each bounds a subtype, one level above the memberships `disjoint` is asked of.

Scoped to a context that can see **both** rules. That is a common descendant of the two
contexts and not a `sees?` between them, for [nmtms.md](nmtms.md)'s reason: asking only
whether one sees the other exempts every sibling pair, while two incomparable contexts can
share a descendant from which both halves are visible. A pair no context sees together is
not reported, and the reported `:context` is where the nogood could form — which is
frequently neither rule's own.

**A pair whose antecedents cannot both hold is dropped, not flagged**, and the difference
from `:excepted` below is the whole reason. Such a pair is not a clash anybody has to sort:
the two rules cannot both fire for one term, so nothing is in wait and a flag would be a
finding with no reader. An `:excepted` pair is the opposite — both rules fire, the clash
does form, and what handles it is the `exceptWhen`, which is a thing the author wrote and
may have written wrong, so it is listed and flagged. Unreachable is the engine's answer;
handled is the author's.

The shipped ontology's own case is the **arity cycle**, and it is dropped from both
directions. `(unary_predicate ?p) => (arity ?p 1)` beside `(binary_predicate ?p) =>
(arity ?p 2)` would be a `:functional` clash on the `arity` table, and the antecedents are
two types `core.txt` declares `disjoint` ([taxonomy.md](taxonomy.md)), so the pair never enters
the reading. Read the other way round, `(arity ?p 1) => (unary_predicate ?p)` beside
`(arity ?p 2) => (binary_predicate ?p)` is a `:disjoint` clash on the *conclusions*, and
what drops it is the functional `arity` slot above: one `?p` bound to two arities. The same rule-out
drops the pairs against `(equivalence_relation ?p) => (symmetric ?p)` and its two siblings,
whose conclusions are `binary_predicate` specializations and so separated from the unary and
ternary classes.

**A pair one of the two already states as an exception is reported, marked `:excepted`.**
"Birds fly, unless penguins" beside "penguins do not fly" is the intended shape, not a
defect: one rule's `exceptWhen` names a predicate the other rule is about, and the clash is
handled. Hiding it would tell an author there was nothing to see, where what there is to
see is that the pair is handled — so it is listed with the flag and the reader sorts them.

An entry is
`{:rules [h1 h2] :kind :negation|:disjoint|:functional|:asymmetric :unifier σ :context C
:excepted b :sentences [s1 s2]}`. In σ the **second** rule's variables carry a trailing
`'`, because both authors are free to write `?x` and a map holding two of them says
nothing. `:total` counts the rules paired, `:pair-count` the pairs found, and the list is
capped by `:limit`.

A rule is never paired with itself: the reading is about two rules disagreeing.

## Reading it

`kb-quality` answers data; `quality-report` renders that same map as Markdown and reads
nothing else, so it cannot print a figure the data does not hold — and refuses a map that is
not one of its answers (`:not-a-report`), because a page of zeros and dashes is a report a
caller who passed the wrong map cannot tell from a report of an empty KB. `:on-progress` is
called as each phase begins, in the order they run — `:extents`, `:rules`, `:chains`,
`:taxonomy`, `:declarations`, `:subsumption`, `:clashes` — and may **throw to cancel**,
the reading being of current
state, so a half-finished one is discarded rather than repaired. A phase reports itself
before its loop, so one with nothing in it is still announced: "skipped because empty" and
"not reached" must not read the same to a caller watching for where a long report is.

Read **without a snapshot**, like every other reader here: a write landing mid-report can
leave a count and a list disagreeing by one, since a rule enumerated and then retracted is
dropped from the listed set and stays in the total. A reading of a moving KB, not a
transaction over a still one.

`:firings` is every recorded firing in the KB, the defeated ones included — not the live
rules' share of them, which is why the rendered sentence states it as a total.

The two rule-hygiene readings are **as-stored about the rules** and **belief-following
about the declarations they consult**. A rule the KB currently disbelieves is still a rule
somebody wrote, and a redundancy in the text does not stop being one while its support is
defeated; a `disjoint` or `functional` declaration nobody believes, on the other hand,
separates and constrains nothing, so it convicts nothing here either.

    lein cli quality --dir /path/to/kb        # the report, as a document

That is the only consumer in the tree, and it is what keeps the pair exercised.
