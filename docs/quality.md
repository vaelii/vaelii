# Reading the KB rather than the engine

- **Covers:** `kb-quality` — which rules never fire, how skewed the predicate extents
  are, how deep the rule graph's chains reach, how much of the taxonomy is connected,
  which argument declarations constrain nothing, which rules another rule already covers,
  which rule pairs would contradict each other if both fired — what each reading costs,
  and what each one does *not* mean.
- **Not here:** how the taxonomy-coverage, stranded-declaration and rule-clash checks
  decide, which are `kb-integrity` categories this census counts →
  [integrity.md](integrity.md); how a run went (iterations, derived conclusions, dropped ones) →
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

Three readings count findings a check owns elsewhere. Taxonomy coverage, the stranded
declarations and the rule clashes are `kb-integrity` categories (`:taxonomy-island`,
`:stranded-declaration`, `:rule-clash` with `:rule-clash-review`), implemented once in
`vaelii.impl.integrity`; this census calls that code over the whole KB and reports what it
finds as counts and capped lists. `:stranded-declaration` and `:rule-clash` run in
`kb-integrity`'s default sweep, which is where a caller wanting a verdict reads them.

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

The check is `kb-integrity`'s review-only `:taxonomy-island` category
([integrity.md](integrity.md#what-a-taxonomy-island-finding-means)), which lists each
island as `{:term :root}` and says how the root is found and which names are type nodes.
This reading is `vaelii.impl.integrity/taxonomy-coverage` over every context: the same
nodes, the same root, counted rather than listed.

The denominator (`:names`) is every type-shaped name in the vocabulary, and by
[naming.md](naming.md) that includes a bare lowercase word: `likes` is a legal predicate
*and* a legal type name. A name `relation?` answers true for is excluded from both names
and edges, as it is from the category. This is why the gap is the finding rather than
either fraction on its own.

The measured shape on the same OpenCyc conversion as the Gini above, and all three
counts are that one run's own denominator: of roughly 124k types, about 71% carry a
`genl` edge and about 64% reach the root — and the ~29% with no edge at all is a bigger
finding than either. A percentage taken from one reading over a denominator from another
would be a number nobody measured, which is why the type count here is this run's rather
than [kbs.md](kbs.md)'s.

## Argument constraints that constrain nothing

`(arg parentOf 3 person)` is admitted while `parentOf` has no declared length; when a
length arrives, the declaration is left constraining a position the predicate provably
does not have. `:declarations` counts those.

The check is `kb-integrity`'s `:stranded-declaration` category
([integrity.md](integrity.md#what-a-stranded-declaration-finding-means)), which says what
strands a declaration, why a `variable_arity` predicate strands nothing, and why it is a
sweep finding rather than a `violations` entry. This reading is
`vaelii.impl.integrity/stranded-declarations` over every stored declaration, in every
context, where the category reads the ones its audit context sees.

An entry is `{:handle :sentence :context :predicate :position :arity :via :message}`, the
category's finding. `:total` counts the declarations walked, `:stranded-count` the ones
convicted, and the list is capped by `:limit` with `:truncated?` saying so.

`:typed-thing` lists the believed declarations that type a position `thing`, each as
`{:handle :sentence :context :facts}`, under the same `:limit`, and `:typed-thing-count`
counts them. Such a declaration mints nothing ([argtypes.md](argtypes.md#where-it-does-not-mint)),
and `:facts` is the number of facts of its predicate stored, the ones a narrower type
would type.

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
at once. The check is `kb-integrity`'s rule-clash pairing
([integrity.md](integrity.md#what-a-rule-clash-finding-means)), which says what the four
clash kinds are, what the five shallow rule-outs drop, and where a pair's nogood could
form. `kb-integrity` splits it by who acts on a pair: a live pair no exception handles is
a `:rule-clash` violation, and a pair with a `set/inertRule` or a stated exception is a
review-only `:rule-clash-review` suggestion.

This reading is the same pairing, `vaelii.impl.integrity/clash-pairs`, over every rule the
census enumerated and unsplit: an entry is
`{:rules [h1 h2] :kind :negation|:disjoint|:functional|:asymmetric :unifier σ :context C
:excepted b :sentences [s1 s2]}`, the category's finding without `:inert`. `:total`
counts the rules paired, `:pair-count` the pairs found, and the list is capped by
`:limit`.

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
