# Bounded KB integrity

- **Covers:** `kb-integrity` — one read-only checkpoint report for the complete visible
  `predAllSpecified` / `predSpecifiedAll` and *Exists* declaration population, every
  visible `typeAllSpecified` classification requirement, the
  `functionCorrespondingPredicate` pairs whose two sides are of different rigidity kinds,
  query-only definition clashes over a caller-owned finite set of ground candidate terms,
  the predicate `genl` edges that widen a declared argument type, the candidate types with
  no `genl`
  path to `thing`, the `genl` edges a cover forces on a candidate type that the
  closure does not hold, the exact-arity class a candidate predicate or function's kind
  and arity force that it is not an instance of, the orthogonal declarations (`orthogonal` and
  `siblingDisjointException`) over a pair a stated separation divides, the stored rules a
  declaration the engine implements states, the `genl` nodes with no declared arity, the
  functions a held rule applies with no single correspondence, the argument declarations
  that name a position their predicate does not have, the rule pairs whose conclusions
  would contradict each other if both fired, and for review: three ontology-engineering
  smells (sibling types with one direct `genl` set, stated edges that derive without
  themselves, and `disjoint` pairs a known cover exhausts), every declared argument
  position no declaration types, the edged types that miss the taxonomy's root, the
  rule clashes an inert rule, a stated exception or an acknowledgment accounts for, and
  the acknowledged rule-macro suggestions.
- **Not here:** repairing findings, enumerating a domain, vocabulary completeness,
  generic constraint auditing, or the represented settled dilemmas returned by
  `contradictions`; how definitions infer membership → [defns.md](defns.md); what a
  specified declaration requires → [predall.md](predall.md); how an `arg` declaration
  descends a predicate `genl` edge → [argtypes.md](argtypes.md); what a cover
  declares → [taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it); what an
  `siblingDisjointException` exempts → [taxonomy.md](taxonomy.md#disjointness); what
  `transitiveInArg` licenses → [inherit.md](inherit.md); a rule another rule already
  covers, the census counts over these findings, and the other knowledge-quality
  readings → [quality.md](quality.md).
- **Assumes:** sentex, context, ground term, `genl` → [glossary.md](glossary.md).

## The call

```clojure
(v/kb-integrity kb #{-212 0 212} 'CxUniverse)
;; => {:status :audited :candidate-count 3 :work 41 :elapsed-ms 2.3}

(v/kb-integrity kb candidates 'CxUniverse
                {:max-work 10000 :max-ms 1000 :max-results 100})
;; => {:status :truncated :reason :max-work :pass :definition-inconsistencies
;;     :candidate-count 500 :work 10000 :elapsed-ms 37.2 ...partial finding categories...}
```

The candidate argument must be a set, and every member must be ground. This is the cost
and meaning boundary: a caller names the known terms worth checking; the query engine
never turns the audit into an open term enumerator. Collections need not be repeated.
The sweep derives its finite collection population from visible `defnSufficient`
declarations and their `genl` ancestors, exactly the population the positive definition
prover can reach.

The optional budget has three independent bounds. `:max-work` meters direct audit rows,
prover dispatches, and prover results, so a one-term candidate set cannot hide the cost
of an aggregate condition over a large KB extent. `:max-ms` is a cooperative wall clock,
checked at the same boundaries and inside the argument-preservation prover's claim walk
([anytime.md](anytime.md)). `:max-results` caps findings. A `nil` bound is no bound.
Reaching any bound returns `:status :truncated` with a reason and never labels a partial
sweep `:audited`. `:pass` names the category whose pass was running when the bound ran
out, and `:work` the units spent up to that point; a pass that did not finish has no
total to report. An answer that completes carries `:work` and `:elapsed-ms` too, the
units and milliseconds the whole sweep spent, so an operator reads a ceiling off an
unbounded run. The examples below omit both keys. The daemon fills all three when the
map is absent, clamps callers to its ceilings, and refuses an over-ceiling request by type before acquiring the
operation's work.

Work and time are cooperative, not preemptive hard ceilings. The sweep checks immediately
before and after every prover selection/dispatch callback and every result-stream pull.
An opaque callback—or a chunked lazy stream that computes several answers in one pull—may
overrun until it returns; the following checkpoint then truncates before another callback
or pull begins. The `Prover` protocol does not require a prover to yield one answer per
pull. `:max-results` is different: it is an absolute bound on findings returned,
including snapshots truncated for work or time.

The definition pass performs one unavoidable open census of visible `defnSufficient`
declarations because callers intentionally supply terms, not collection names. It then
validates one collection and one ground candidate at a time. The specified pass likewise
uses small declaration censuses only to identify its finite worklist, then audits each
declared predicate independently, and the type-specified pass does the same for each
`typeAllSpecified` declaration. The rigidity-correspondence pass reads one census of the
visible `functionCorrespondingPredicate` pairs, then one pair at a time. The widening pass does the same: one census of visible
`arg` declarations, then one direct `genl` edge at a time. The `thing` pass reads no
census: it checks one candidate term at a time. The implicit-`genl` pass reads none
either: one candidate term, then one visible cover over it, at a time. The
implicit-arity-class pass reads one census of the visible `predicateTypeByArity` and
`functionTypeByArity` facts, then one candidate term at a time. The
`orthogonal` pass reads one census of visible orthogonal declarations, then one
declaration at a time. The rule-macro pass reads one census of the stored rules, then
one rule at a time. The undeclared-arity pass reads one census of the visible `genl`
edges, then one node at a time. The uncorresponded-function pass reads one census of the
stored rules, then one rule at a time. The stranded-declaration pass reads one census of the
argument declarations, then one declaration at a time. The two rule-clash passes read one
census of the stored rules, then one candidate pair at a time. The taxonomy-island pass
reads the visible `genl` nodes, then one node's closure at a time. The three ontology-engineering passes read the taxonomy's types
once, or one census of stated `genl` and `disjoint` declarations, then one type or one
declaration at a time. These focused units are where
cooperative checkpoints and partial-result preservation sit.

`:categories`, a set of category keys, runs the passes of those categories alone and
reads nothing for the others. Without `:categories`, the sweep runs every pass except
the seven review-only ones: `:twin-genls`, `:derivable-stated-edge`,
`:disjoint-could-be-partition`, `:missing-arg`, `:taxonomy-island`,
`:rule-clash-review` and `:rule-macro-review`. A caller names a review-only category
in `:categories` to run its pass, so a review finding never makes a default sweep `:gap`. On a large KB the census passes (the specified and widening
categories) can spend the daemon's `:max-work` ceiling before a candidate pass starts; a
caller names the candidate categories to reach them, or the operator raises or lifts
the ceiling with `VAELII_INTEGRITY_MAX_WORK` ([operations.md](operations.md#operator)).
The default sweep over the starter ontology and 85 candidate terms spends about 2.4
million units, nearly all of them in the definition pass, against the default ceiling
of 10000.

An explicit `nil` options value means the same thing as omitting the options arity,
in-process and through the generated daemon clients. The daemon still supplies its own
ceilings before dispatching either spelling.

A finding changes the top-level status and adds only the populated categories:

```clojure
{:status :gap
 :candidate-count 1
 :definition-inconsistencies
 [{:collection widget
   :term 7
   :passing-sufficient
   [{:defined-collection widget :condition (qualifies ?x)}]
   :failing-necessary
   [{:defined-collection widget :condition (required ?x)}]}]
 :all-specified-violations
 {[predAllSpecified hasPet person]
  {:status :audited :violations #{Bob}}}}
```

`:status :audited` means every pass the sweep ran completed and none found a gap. `:status :gap` cannot
be confused with that clean shape even when only one sparse category is present. The
specified category is exactly `all-specified-violations`, including its typed declaration
gaps; it is composed, not reimplemented.

Stored Specified obligations use each visible declaration's defining context, as
described in [predall.md](predall.md). The result cap counts canonical declaration keys,
not defining contexts. Completed source-context findings remain available if a later
source-context audit exhausts the work or time limit. A native-only registry declaration
has no stored defining context and retains the querying-context audit.

## What a definition finding means

The definition prover treats a passing own-or-spec `defnSufficient` as a positive
membership witness. A failing own `defnNecessary` is simultaneously a negative witness.
When no strict-genl necessary fast-fails the positive path, the collection can therefore
answer both `(Coll term)` and `(not (Coll term))`. The report preserves every passing and
failing declaration as evidence, including the collection on which an inherited
sufficient was declared.

A definition finding is not one `contradictions` reports. `contradictions` reports
settled, represented default dilemmas already present in the truth-maintenance state. A computed
definition condition is evaluated only when queried, so its latent clash has no stored
pair for `contradictions` to enumerate. `kb-integrity` asks the bounded definition
question without changing the meaning or cost of the existing reader.

The sweep stores and files nothing. Aggregate diagnostics raised only because a
definition condition was evaluated are redirected to an audit-local sink, preserving
the condition's truth without changing the live violations ledger or logs. It identifies
gaps; remediation remains a separate, explicit write.

## What a type-specified finding means

`(typeAllSpecified ?classifier ?indep)` is an integrity requirement on what the KB knows:
every instance of `?indep` must have a believed membership in some member of the
metatype `?classifier`. It is `predAllSpecified`'s counterpart for a classification
rather than a filler ([predall.md](predall.md#specified-an-integrity-audit-a-caller-runs)).
core.txt states one:

```clojure
;; (partition relation time_invariant_relation time_agnostic_relation time_varying_relation)
;; (rigidity_kind time_invariant_relation) … (rigidity_kind time_varying_relation)
;; (typeAllSpecified rigidity_kind relation)
;; (binary_predicate ownsPet)
;; (time_varying_relation ownsPet)
;; (binary_predicate admiresPet)
{:status :gap
 :candidate-count 0
 :type-specified-violations
 {[typeAllSpecified rigidity_kind relation]
  {:status :audited :violations #{admiresPet …}}}}
```

`ownsPet` is classified and `admiresPet` is not, so `admiresPet` is reported. A partition
of `?indep` into the classifier's members does not satisfy the requirement. The partition
constrains the world: every relation *is* of one rigidity kind. The requirement constrains
the KB: it must *believe* which. So the partition above leaves every relation nobody
classified in the violation set.

A membership counts when `ask` answers it, so one reached through `genl` or through
argument preservation counts as a stored one does. A time-varying type's specs, which
`(transitiveInArgInverse time_varying_relation 1 genl)` classifies, are not reported.
A finding has the specified pass's shape, keyed by `[typeAllSpecified classifier indep]`:
`{:status :audited :violations #{…}}`, or `{:status :gap :gap :empty-classifier
:classifier c}` when the classifier has no visible member, so no violation set pretends
the audit ran. A declaration that holds is omitted.

The pass has these limits:

- **Declaration census, not candidate terms.** Like the specified pass, it reads every
  visible `typeAllSpecified` declaration once, then audits each one: the instances of
  `?indep`, against the members of `?classifier`. The caller's candidate set does not bound
  it.
- **Members of the classifier only.** A membership in a union of members, such as
  `possibly_time_invariant_relation`, does not classify: the requirement names the
  classifier, and the union is not one of its members.
- **Visible from the audit context.** A declaration, classifier member or membership the
  audit context cannot see contributes nothing.

Each instance and membership question is metered as the specified pass's are, and each
declaration with a finding counts once against `:max-results`, after the specified
category.

## What a rigidity-correspondence finding means

`(functionCorrespondingPredicate ?function ?predicate ?position)` says the function and the predicate
state one relationship, so an instance could lose the one exactly when it could lose the
other. Each pair must therefore share a rigidity kind (`time_invariant_relation`,
`time_agnostic_relation` or `time_varying_relation`, the members of `rigidity_kind`):

```clojure
;; (functionCorrespondingBinaryPredicate HiveQueenFn hiveQueenOf)
;; (time_invariant_relation HiveQueenFn)
;; (time_varying_relation hiveQueenOf)
{:status :gap
 :candidate-count 0
 :rigidity-correspondence
 [{:function HiveQueenFn :predicate hiveQueenOf
   :function-kinds #{time_invariant_relation}
   :predicate-kinds #{time_varying_relation}}]}
```

A pair is reported when both sides are believed of at least one kind and the two sets of
kinds differ. A pair with an unclassified side is not reported: `(typeAllSpecified
rigidity_kind relation)` already reports the unclassified relation in the
`:type-specified-violations` category, and a second finding about it would say nothing
new. Once that side is classified, a mismatch is reported here.

The pass reads both shapes of the declaration, with the value position stated and
without. A membership counts when `ask` answers it, so a kind inherited through `genl`
counts as a stated one does. A pair, a kind or a membership the audit context cannot see
contributes nothing. The pass reads nothing when `rigidity_kind` has no visible member.
Each census, membership question and pair spends one work unit, and each finding counts
against `:max-results` after the type-specified category.

## What a widening finding means

`(genl P Q)` between predicates says every `P` tuple is a `Q` tuple, so `Q`'s `arg`
declarations constrain `P`'s tuples too ([argtypes.md](argtypes.md)). When `P` declares
its own type at a position and `Q` demands one that type is not subsumed by, the edge
does not say what its author meant: `(arg parentOf 1 animal)` under
`(genl parentOf originatorOf)` with `(arg originatorOf 1 person)` makes every animal
parentage an `originatorOf` tuple, which only persons may fill.

Nothing on the write path reports this as a defect of the edge. Depending on the
contexts the declarations sit in and on arrival order, `(parentOf Fido Rex)` over two
dogs is refused `:arg-type`, or is admitted with `(person Fido)` minted onto it. Neither
outcome files a violation or a contradiction naming the edge. So the sweep reads the
declarations instead of any fact:

```clojure
{:status :gap
 :candidate-count 0
 :genl-arg-widening
 [{:spec parentOf :genl originatorOf :arg 1 :spec-type animal :genl-type person}
  {:spec parentOf :genl originatorOf :arg 2 :spec-type animal :genl-type person}]}
```

One finding is reported for each spec type at each position that no demanded type
subsumes. Subsumption is the reflexive `genl` closure read from the audit context. A
spec type that *is* subsumed (`fatherOf` declares `person` under `parentOf`'s `animal`)
is compatible, and so is an identical type. A spec position that holds several declared
types is their intersection, so it is compatible as soon as one of them is subsumed.
`:genl-type-declared-on` is present when the demanded type is declared above `Q`, on a
super-predicate the constraint inherits through `res/constraining-predicates`, the same
closure `assert`'s argument check reads.

The pass has these limits:

- **Declaration census, not candidate terms.** A widening is a fact about two
  predicates' declarations, not about any individual, so the caller's candidate set does
  not bound it. The pass reads every visible `arg` declaration once to find the
  predicates that declare their own types (a few hundred on the shipped load), then each
  such predicate's direct visible `genl` edges. Edges out of a predicate that declares
  nothing of its own are skipped, because such a predicate has no declared domain for an
  edge to widen. A multi-step chain is still covered: the demanded types come from the
  whole closure above the direct genl.
- **`arg` only.** `genlArg` bounds a position one level up (a subtype, not a member),
  `quotedArg` types a mention, and `interArg` and the covering forms (`args`,
  `argAndRest`, …) relate positions rather than typing one. Comparing any of them
  against an `arg` type would compare different levels, so none is read here.
- **`genl` only.** `genlInverse` and other relation-to-relation forms are not read.
- **Visible from the audit context.** An edge or declaration asserted in a context the
  audit context cannot see contributes nothing, as for every other read.

Each declaration row, edge and position comparison spends one work unit, and
`:max-results` counts these findings after the definition, specified, type-specified and
rigidity-correspondence categories, in that order.

## What a not-under-thing finding means

Every type is a specialization of `thing`. Nothing on the write path reports a term
declared `(unary_predicate X)` with no `genl` path to `thing`: no violation or
contradiction names the term. So the sweep reads the declaration and the taxonomy for
each candidate:

```clojure
{:status :gap
 :candidate-count 1
 :not-under-thing
 [{:term orphan_kind}]}
```

One finding is reported for each candidate term, in print order. The path is the
transitive `genl` closure read from the audit context, so `(genl nested_kind placed_kind)`
with `(genl placed_kind thing)` places `nested_kind` under `thing`.

The pass has these limits:

- **Candidate terms, not a census.** The caller's candidate set bounds the pass, as it
  bounds the definition pass. A type declared `unary_predicate` but absent from the set
  is not read, so the pass never enumerates the KB's types. A candidate that is not a
  ground symbol (a number, a string, a compound) cannot be a type and is skipped.
- **`unary_predicate` only.** A binary or wider predicate is not a type, so a predicate
  `genl` edge between two binary predicates is not a finding however its chain ends.
- **`thing` is the root.** `thing` itself is never a finding.
- **Visible from the audit context.** A `unary_predicate` declaration or a `genl` edge
  asserted in a context the audit context cannot see contributes nothing, so a type whose
  only edge to `thing` is asserted below the audit context is a finding there.

Reading the declaration and testing the `genl` path each spend one work unit, and
`:max-results` counts these findings last, after the widening category.

## What an implicit-genl finding means

A cover places individuals: an instance of the whole denied every part but one is an
instance of the remaining part
([taxonomy.md](taxonomy.md#the-coverage-inference-is-conditional-on-explicit-negation)). The
same argument holds of a type, and nothing on the write path applies it there. A type
under the whole that is disjoint from every part but one has all its instances in that
part, so `(genl X P)` is true, but no sentence states it and the `genl` closure does not
derive it. The sweep suggests each such edge, with the cover that forces it and, for each
other part, the declarations that separate the type from it:

```clojure
;; (partition thing tangible intangible)
;; (partition thing temporal atemporal)
;; (genl tangible temporal)
;; (genl abstract_kind atemporal)
{:status :gap
 :candidate-count 1
 :implicit-genl
 [{:term abstract_kind
   :genl intangible
   :cover [(partition thing intangible tangible)]
   :disjoint-from [{:part tangible
                    :grounds [(partition thing atemporal temporal)]}]}]}
```

`abstract_kind` is separated from `tangible` by the second partition, which holds a
supertype of each, so every `abstract_kind` is `intangible`. The finding is a
suggestion: the sweep asserts nothing, and the edge is the author's to state. Every predicate and function the starter ships states its
exact-arity class, so the shipped starter has no finding, in CxUniverse or in any middle
context.

One finding is reported for each candidate term and cover that force an edge, in print
order of the term and then of the cover. The separation is `disjoint?`, so an explicit
`disjoint` pair, a shared `disjoint_metatype`, a `sibling_disjoint` parent and a
separating cover all count, each inherited down the `genl` closure; `:grounds` names the
believed declarations it rests on.

The pass has these limits:

- **Candidate terms, not a census.** The caller's candidate set bounds the pass, as it
  bounds the `thing` pass. A candidate is read as a type when `kb/relation?` does not read
  it as a relation and it is declared with arity one or is the subtype of a visible `genl`
  edge; an individual and a relation of two or more places are skipped.
- **Covers over a supertype or over `thing`.** Every visible `covering` or `partition`
  over a supertype of the term is read, and every one over `thing` even when the term
  has no `genl` path to `thing` yet. A `separating` declaration claims no coverage and forces
  nothing, though it may separate the term from a part.
- **Exactly one part left.** A term separated from every part is empty and is forced
  under none; a term left two parts or more is forced under none. A part, or the whole
  itself, is never a finding.
- **Only edges the closure misses.** A `genl` already stated, or derived through the
  closure, is not a finding.
- **Visible from the audit context.** The cover, the separating declarations and the
  `genl` edges are those the audit context sees.

Reading the term's arity and edges, each cover and each part's disjointness test spend
one work unit, and `:max-results` counts these findings last, after the `thing` category.

## What an implicit-arity-class finding means

`(predicateTypeByArity binary_predicate 2)` says that a predicate of two arguments is a
`binary_predicate`, and `functionTypeByArity` says the same of functions. Each mapping
fact generates that classification as a rule, and the rule is `set/inertRule`: believed and
browsable, run on no write and no query. Run backward, the predicate rule reached
`(binary ?r)` through the `genl` edge from `binary_predicate` to `binary` while the
converse proves `(arity ?r 2)` from `(binary ?r)`, and every `(binary ?r)` and `(arity ?p
?n)` query paid for the cycle ([taxonomy.md](taxonomy.md#arity)). The sweep applies the
rule instead: it reports the class a predicate's or a function's arity forces that the
relation is not an instance of, and an author states it:

```clojure
;; (predicateTypeByArity binary_predicate 2)
;; (predicate pairOf)
;; (arity pairOf 2)
{:status :gap
 :candidate-count 1
 :implicit-arity-class
 [{:term pairOf
   :kind predicate
   :arity 2
   :class binary_predicate
   :mapping (predicateTypeByArity binary_predicate 2)}]}
```

The finding is a suggestion: the sweep asserts nothing, and `(binary_predicate pairOf)`
is the author's to state.

One finding is reported for each candidate term and class, in print order of the term,
then of the kind (predicate before function), then of the class. The length is
`arity/relation-length`'s exact one, read the same at every context: an `(arity R n)`
declaration, a membership in an exact-arity class, or the one exact length the bound
predicates above `R` agree on ([taxonomy.md](taxonomy.md#arity)). The kind and the class
are memberships read through the `genl` closure, so a relation stated `binary_predicate`,
or an instance of a type under it, is not a finding.

The pass has these limits:

- **Candidate terms, not a census of relations.** The caller's candidate set bounds the
  pass, as it bounds the `thing` pass. A candidate that is not a ground symbol is skipped,
  and so is one with no exact length: a variable-arity relation has no exact-arity class.
- **Only the shipped mappings.** The pass reads `predicateTypeByArity` and
  `functionTypeByArity`. An arity no visible mapping fact names forces nothing, so
  `(arity InstantFn 6)` is not a finding.
- **A kind, not the relation-wide class.** `relationTypeByArity`'s rule is forward and
  stores `(binary R)` from `(arity R 2)`, so the relation-wide class is never missing. A
  relation that is neither a predicate nor a function is suggested no class.
- **Visible from the audit context.** The mapping facts and the memberships are those the
  audit context sees.

Reading the mapping facts, each term's length, its kind and each class it lacks spend one
work unit each, and `:max-results` counts these findings after the implicit-`genl`
category.

## What an orthogonal-over-separation finding means

The pass reads every visible orthogonal declaration: an `(orthogonal a b)`, or a fact
whose functor the `genl` closure places under `orthogonal`, which a
`(siblingDisjointException a b)` is. A `siblingDisjointException` exempts the pair from the
separation marks: a `partition` or `separating` declaration naming both, a `sibling_disjoint`
parent and a shared `disjoint_metatype`, read over `a` and `b` or over a separated
supertype of each ([taxonomy.md](taxonomy.md#disjointness)). The exemption is what the
exception is for, and it is also why nothing on the read path can show the conflict when
the separation was meant: `disjoint?` reads the pair apart, `conflicts` sees nothing to
report, and one exception silently undoes, say, a partition of `thing`. So the sweep reads
every visible orthogonal declaration against the separations stated over its pair with no
exemption applied:

```clojure
;; (partition thing tangible intangible)
;; (siblingDisjointException tangible intangible)
{:status :gap
 :candidate-count 0
 :orthogonal-over-separation
 [{:orthogonal   {:handle 2 :sentence (siblingDisjointException intangible tangible)
                  :context CxUniverse}
   :separated-by [{:handle 1 :sentence (partition thing intangible tangible)
                   :context CxUniverse}]}]}
```

Both sides are named by handle, sentence and context, the shape `conflicts` names a
clash's grounds in, so the author can drop whichever is wrong: the declaration when the
separation was meant, the separating declaration when the overlap is. The sweep asserts
and retracts nothing.

One finding is reported for each visible, believed orthogonal declaration over two ground
symbols that some stated separation divides, in content order of the declaration.
`:separated-by` holds every believed declaration the audit context sees that separates
the pair, as `disjoint?` would read it with no exception stated: for a
`disjoint_metatype`, the mark and the two memberships.

The pass has these limits:

- **Declaration census, not candidate terms.** A finding is a fact about two
  declarations, not about any individual, so the caller's candidate set does not bound
  it. The pass reads every visible orthogonal declaration once (they are few), then each
  one's separations.
- **Stated separations only.** The separations read are the four declaration forms
  `disjoint?` reads; nothing else divides a pair for this pass.
- **Every separation, lifted or not.** The separations are read with no exemption at all,
  so a separation an exception lifts still counts. A stated `(orthogonal a b)` exempts
  nothing, so every separation it is reported with is also a clash of the declaration
  that `conflicts` reports; the sweep names it here as well, beside the ones no reader can
  see.
- **Visible from the audit context.** The declaration and the separating declarations
  are those the audit context sees, so a separation asserted below the audit context is
  not a finding there.

Each orthogonal declaration's row and each pair's separation read spend one work unit, and
`:max-results` counts these findings last, after the implicit-`genl` category.

## What a rule-macro finding means

Several declarations the engine implements state exactly what a hand-written rule
states. `(transitiveInArgInverse empty 1 genl)` concludes `(empty d)` from `(empty c)` and
`(genl d c)`, so a rule written as
`(implies (and (empty ?c) (genl ?d ?c)) (empty ?d))` repeats the declaration in a longer
form. The sweep reads each stored rule and reports every declaration whose rule shape
the rule matches:

```clojure
;; (set/forwardRule (implies (and (empty ?c) (genl ?d ?c)) (empty ?d)))
{:status :gap
 :candidate-count 0
 :rule-macro
 [{:rule 812
   :sentence (implies (and (empty ?c) (genl ?d ?c)) (empty ?d))
   :context CxUniverse
   :macro transitiveInArgInverse
   :declaration (transitiveInArgInverse empty 1 genl)}]}
```

`:rule` is the rule's handle and `:sentence` the rule as stored. `:declaration` is the
suggested declaration, to be asserted in the rule's `:context`. `:stated true` is
present when that context already sees the declaration, so the rule repeats it. An
`inverse` finding carries `:converse`, the handle, sentence and context of the rule
that states the other direction. `:default-shaped true` marks a `set/defaultRule` whose
shape is a monotonic declaration (below). The finding is a suggestion: the sweep asserts and
retracts nothing.

The match is structural. The rule's variables are renamed apart, and each shape is
unified against the rule's consequent and, one to one, against its antecedents in any
order. Each argument the shape leaves free must take a distinct variable of the rule,
so a rule that fixes a constant there or repeats a variable is not the shape. The
shapes, with `?o…` standing for the free arguments of a predicate of arity `n`:

| Declaration | Rule shape | Further condition |
|---|---|---|
| `(transitiveInArg P i R)` | `(P … ?w …)`, `(R ?w ?o)` ⇒ `(P … ?o …)`, `?w` and `?o` at position `i` | `R` is `genl`, `genlCx` or declared `transitive` from the rule's context, and `R` is not `P` |
| `(transitiveInArgInverse P i R)` | `(P … ?w …)`, `(R ?o ?w)` ⇒ `(P … ?o …)` | as `transitiveInArg` |
| `(symmetric P)` | `(P ?a ?b)` ⇒ `(P ?b ?a)` | `P` declared with arity 2; the rule is visible from CxUniverse |
| `(transitive P)` | `(P ?a ?w)`, `(P ?w ?b)` ⇒ `(P ?a ?b)` | as `symmetric` |
| `(commutativeInArgs P i j)` | `(P ?o1 … ?on)` ⇒ the same with positions `i` and `j` exchanged, `n` ≥ 3 | `P` declared with arity `n`; the rule is visible from CxUniverse |
| `(inverse P Q)` | `(P ?a ?b)` ⇒ `(Q ?b ?a)`, and a second rule `(Q ?a ?b)` ⇒ `(P ?b ?a)` | `P` and `Q` declared with arity 2; both rules are visible from CxUniverse |
| `(genl P Q)` | `(P ?o1 … ?on)` ⇒ `(Q ?o1 … ?on)` | `Q` is not a term the engine interprets; neither `P` nor `Q` is declared with another arity or with variable arity |
| `(arg P i C)` | `(P ?o1 … ?on)` ⇒ `(C ?oi)` | `P` declared with arity `n ≥ 2` (a unary `P` gives a type, so `(P ?x)` ⇒ `(C ?x)` is the `genl` row); `C` is not a term the engine interprets; the rule is visible from CxUniverse |
| `(predAllInstance P C K)` | `(C ?x)` ⇒ `(P ?x K)`, `K` ground | the rule is a `set/defaultRule`, and `P` is not declared with another arity |
| `(predInstanceAll P K C)` | `(C ?y)` ⇒ `(P K ?y)`, `K` ground | as `predAllInstance` |

The two generators generate a `set/defaultRule`, so a monotonic rule of their shape is not
reported as one. Every other declaration concludes at the class of its weakest premise,
as a bare rule does, so a `set/defaultRule` of their shape is not the declaration. Such
a rule is either a default its author meant, or a rule written as a default by accident,
and the KB states no marker that tells the two apart. The sweep reads one sign instead:

- A `set/defaultRule` with an `exceptWhen` is a default with a stated exception. Like
  every rule with an `exceptWhen`, it is not read.
- A `set/defaultRule` is **excused** when the KB holds a claim the default yields to: a
  believed `(not (Q …))`, in a context that sees the rule's, or a believed rule
  concluding `(not (Q …))`, in a context that sees the rule's or that the rule's context
  sees, for `Q` the rule's consequent predicate or a `genl` of it. An excused default
  is not reported.
- Any other `set/defaultRule` of a monotonic shape is reported with
  `:default-shaped true`, as a default nothing yet overrides, which may be a default by
  accident.

The heuristic is a sign, not a proof. A default may be deliberate before anything
overrides it, and a contrary claim may override a default that was written by accident.

A reviewer records a decision on any suggestion with an
[acknowledgment](#acknowledged-findings) over the suggested declaration, or with
`declined_rule_macro`, `core.txt` sugar for one that carries no reason:

```clojure
;; (set/defaultRule (set/forwardRule (implies (livesIn ?a ?p) (locatedIn ?a ?p))))
(acknowledgedFinding :rule-macro (genl livesIn locatedIn) "livesIn is meant as a default")
(declined_rule_macro (genl livesIn locatedIn))
```

A suggestion the rule's context sees acknowledged moves from `:rule-macro` to the
review-only `:rule-macro-review`, marked with the reason as `:acknowledged`. A forward
rule in `core.txt` concludes `(acknowledgedFinding :rule-macro D "Acknowledged via
declined_rule_macro; no reason supplied.")` from a `(declined_rule_macro D)` record, and
the pass reads only the acknowledgment. The record quotes the suggestion rather than
naming the rule by `(sentexHandle H)`: a handle belongs
to one store, and `export-text!` skips a sentence that names one, so a handle-based record
would not survive a reload. The suggestion is a function of the rule's sentence, so the
record names the rule, and an edit to the rule that changes its shape changes the
suggestion and brings the finding back. Retracting the record brings the finding back too.

The further conditions are where a declaration reads differently from a rule:

- **A relation mark is read from every context.** `symmetric`, `transitive`,
  `commutativeInArgs`, `inverse` and `arg` are lifted into CxUniverse
  ([contexts.md](contexts.md#where-a-relation-property-is-read-from)), so a rule one
  theory states is not the mark, and is reported only when CxUniverse sees it. `genl` and
  the two preservation declarations are read where they are stated, in the rule's own
  context.
- **The preservation reach needs a transitive relation.** `assert` refuses
  `(transitiveInArg P i R)` over an `R` nobody declared transitive
  ([inherit.md](inherit.md#the-transitivity-has-to-have-been-declared)), so the rule over
  such an `R` is not reported.
- **A rule that concludes a term the engine interprets materializes it.** A stored
  `(symmetric P)` sets the property the canonical argument order reads, and a membership
  `genl` inherits does not, as the `equivalence_relation` comment in `core.txt` records. A
  rule shaped as `genl` or `arg` whose consequent predicate is in the engine's grammar
  (`vaelii.impl.predicates`) is therefore not reported.
- **A mark fixes an arity.** `symmetric` and `transitive` classify their predicate as a
  `binary_predicate`, and a rule covers one arity only, so the predicate's arity must
  be the rule's; `commutativeInArgs` and `arg` read the same way, against `P`'s own
  arity, the rule's antecedent. A `genl` edge holds at every arity a predicate takes, so a
  variable-arity predicate is not reported under it.
- **One direction of an inverse is not `inverse`.** A single swapping rule states one
  direction, which is `genlInverse` rather than `inverse`, and the pass suggests no
  `genlInverse`, so such a rule is not reported.

Three differences remain between a reported rule and its declaration, and the finding
does not weigh them. `transitiveInArg` answers a ground goal only and leaves an open one
to the fact and rule provers ([inherit.md](inherit.md#reading-it-back)), where a
forward rule stores each conclusion and answers an open goal from the store. A more
specific contrary claim undercuts a `:default` claim the declaration carries
([inherit.md](inherit.md#specificity-undercuts-and-does-not-arbitrate)), where the
rule's conclusion and the contrary claim form a nogood. A `genl` edge also places `P`
under `Q` in the taxonomy, so `disjoint`, `arg` and the preservation declarations
along `genl` read the edge; the rule's universal reading entails the same subsumption,
and the engine draws none of it from the rule.

The pass has these limits:

- **Rule census, not candidate terms.** A rule is a fact about the KB rather than about
  an individual, so the caller's candidate set does not bound the pass. The pass reads
  every rule off the rule index once (80 on the shipped load), then each of the rule's
  shapes.
- **Premises only.** A rule a generator generated is a conclusion of the generator, so it
  is not reported, and the generator is.
- **Rules a chainer runs.** An inert rule, a choice or constraint rule, and a rule with
  an `exceptWhen`, `unknown`, aggregate or `different` condition are not read.
- **Visible from the audit context.** A rule the audit context cannot see is not read, so
  a rule a domain theory states is reported from that theory or below it.

Reading each rule and unifying each shape spend one work unit, and so do the arity, the
relation and the stated-declaration reads. `:max-results` counts these findings
after the orthogonal-over-separation category.

## What an undeclared-arity finding means

Every type is a unary predicate, and a predicate `genl` edge relates two predicates of
one arity. A term at either end of a `genl` edge that no length binds is a type or a
predicate nobody declared. A rule guarded on `(unary ?t)` or `(unary_predicate ?t)`
reads such a term as no type and skips it, and nothing on the write path reports the
missing declaration. So the sweep reads each node of the visible `genl` edges:

```clojure
;; (unary_predicate placed_kind)
;; (genl below_kind placed_kind)
;; (genl stray_kind loose_kind)
{:status :gap
 :candidate-count 0
 :undeclared-arity
 [{:term loose_kind} {:term stray_kind}]}
```

One finding is reported for each node, in print order. A node has an arity when
`arity/relation-length` binds it to an exact length or a `variable_arity` membership
releases it (`arity/released?`), read the same at every context
([taxonomy.md](taxonomy.md#arity)): an `(arity P n)` declaration, a membership in an
exact-arity class (`unary_predicate`, `binary_predicate`, `unary_function`, and the
others of `sx/exact-arity-classes`), a `:monotonic` membership in a type that reaches one
through `:monotonic` `genl` edges, or a `variable_arity`, `variable_arity_predicate` or
`variable_arity_function` membership, each stated in any context, or the one exact length
the bound predicates above the node agree on. A node below a bound predicate is therefore
not a finding.

`core.txt` declares an arity for every type it places under `thing`. The starter loader
(`vaelii.host.starter/load-into`) asserts `(unary_predicate X)` in CxUniverse for every subtype `X` of `thing` after the KB files load,
which declares the 87 types of the upper and middle files that state no arity of their
own, so the shipped starter has no finding either.

The pass has these limits:

- **Edge census, not candidate terms.** A missing arity is a fact about the KB's
  vocabulary rather than about an individual, so the caller's candidate set does not
  bound the pass. The pass reads every visible `genl` edge once, then each distinct node.
- **`genl` nodes only.** A type that appears in no `genl` edge, and a predicate used only
  in facts, is not read.
- **Visible from the audit context.** An edge or an arity declaration asserted in a
  context the audit context cannot see contributes nothing, so a type declared only
  below the audit context is a finding there.

Reading each edge and each node's two arity reads spend one work unit, and
`:max-results` counts these findings after the rule-macro category.

## What an uncorresponded-function finding means

A rule reads an application `(F a…)` of a `reifiable_function` in its antecedents through
`F`'s corresponding predicate, and a rule whose antecedents name a function its context sees
no `functionCorrespondingPredicate` for is held inert ([nat.md](nat.md#the-corresponding-predicate)).
Nothing on the write path refuses the rule, so the sweep reports each such function with
the held rules that name it:

```clojure
;; (reifiable_function FruitFn)
;; (implies (tagged (FruitFn ?t)) (ripe ?t))
{:status :gap
 :candidate-count 0
 :uncorresponded-function
 [{:function FruitFn :rules [4711]}]}
```

One finding is reported for each function, in print order, with the rules in handle
order.

The pass has these limits:

- **Rule census, not candidate terms.** The pass reads every stored rule, and the
  caller's candidate set does not bound it.
- **Functions without a correspondence only.** A rule held for an application inside an
  `unknown`, `thereExists`, aggregate or `ist` condition names a function that has one,
  and is not reported. A rule held for a variable-functor application names no function,
  and is not reported.
- **Visible from the audit context.** A rule the audit context cannot see is not read.

Reading each rule spends one work unit, and `:max-results` counts these findings after
the undeclared-arity category.

## What a stranded-declaration finding means

`assert` stores `(arg parentOf 3 person)` whatever binds `parentOf`'s length. Once a
length is bound — declared of the predicate, or inherited through a `genl` edge from a
super-predicate — the declaration constrains a position the predicate does not have,
whichever arrived first, and `try-assert` refuses the identical sentence
([taxonomy.md](taxonomy.md#the-declarations-are-checked-against-each-other)). A
declaration that is enforced and one that enforces nothing look exactly alike, so the
sweep names the second:

```clojure
;; (arg parentOf 3 person), then (binary_predicate parentOf)
{:status :gap
 :candidate-count 0
 :stranded-declaration
 [{:handle 914 :sentence (arg parentOf 3 person) :context CxUniverse
   :predicate parentOf :position 3 :arity 2 :via parentOf
   :message "..."}]}
```

It is the **entry point's own arm, re-asked** of content already stored
(`checks/arg-position-violation`), so what the sweep lists and what a `try-assert`
refuses cannot drift apart: whatever binds a predicate's length for the entry point binds it
here, and a predicate the KB has bound to no length strands nothing. `interArg` names two
positions and each is asked. `:via` is the predicate the length was read off — the
declaration's own where it carries one, the super it inherits from otherwise. `:message`
is the sentence the check itself wrote, carried rather than re-derived.

A **`variable_arity`** predicate strands nothing, however high the position: it reads a
tuple of any length from its declared arity upward, so a position past that length is one
its tuples really do reach.

A stranded declaration constrains nothing, refuses nothing and mints nothing, so there is
no *newly* for a settle to report and it reads the same an hour later; that is why it is
a sweep finding and not a `violations` entry ([taxonomy.md](taxonomy.md) has the argument
against the wrong-length **fact**, which is a ledger entry). The fix is to correct the
position, to declare the arity the author meant, or to mark the predicate `variable_arity`
where its tuples really do reach that far.

The pass has these limits:

- **Declaration census, not candidate terms.** The pass reads every stored `arg`,
  `genlArg`, `interArg` and `interArgEqual` declaration once (377 in the bundled
  ontology), then asks each about its own predicate: a map read where the predicate
  carries a length and one read per super-predicate where it inherits one.
- **Believed declarations only.** A stored declaration nobody believes constrains nothing
  for a reason that has nothing to do with the position it names.
- **Visible from the audit context.** A declaration asserted in a context the audit
  context cannot see is not read; the length is read as the entry point reads it in the
  declaration's own context.

Each declaration spends one work unit, and `:max-results` counts these findings after the
uncorresponded-function category.

## What a rule-clash finding means

A rule pair whose consequents would clash if both fired, and whose antecedents could hold
at once, is a contradiction in waiting: nothing is wrong yet, and the first content that
satisfies both antecedents forms a nogood. Four kinds, asked of a pair in this order so one
answering to two lands under one of them:

| kind | the clash |
|---|---|
| `:negation` | one concludes `S` and the other `(not T)` where `S` entails `T` — `(dog X)` against `(not (animal X))`, and never `(animal X)` against `(not (dog X))` |
| `:disjoint` | two unary type conclusions about one term whose types a `disjoint`, `sibling_disjoint` or `disjoint_metatype` declaration separates ([taxonomy.md](taxonomy.md)) |
| `:functional` | two conclusions filling one `functional` slot for one subject with values that are not the same term. Both spellings of the mark count — `(functionalInArg P 2)` says the same thing about the same slot as `(functional P)` — and both positions of a binary tuple, `(functionalInArg P 1)` read in the mirror |
| `:asymmetric` | one tuple concluded both ways round under a predicate declared `asymmetric`. A self tuple `(P a a)` is not one — the ontology admits it |

```clojure
;; (set/forwardRule (implies (bird ?x) (flies ?x)))
;; (set/forwardRule (implies (penguin ?x) (not (flies ?x))))
{:status :gap
 :candidate-count 0
 :rule-clash
 [{:rules [812 813] :kind :negation :unifier {?x ?x'} :context CxUniverse
   :sentences [(implies (bird ?x) (flies ?x)) (implies (penguin ?x) (not (flies ?x)))]
   :excepted false}]}
```

In `:unifier` the **second** rule's variables carry a trailing `'`, because both authors
are free to write `?x` and a map holding two of them says nothing. `:context` is the
context the pair was judged in, below.

**Two categories, by who acts on the pair.** `:rule-clash` holds the live pairs: both
rules chain, no `exceptWhen` handles the clash, and no acknowledgment names the pair.
`:rule-clash-review` is review-only, and holds the rest:

- **A pair with a `set/inertRule`**, marked `:inert true`. An inert rule chains in neither
  engine, so the clash forms only if the rule is switched on: a suggestion about the rule
  as written, not a violation of the KB as it runs.
- **A pair one rule already states as an exception**, marked `:excepted true`. "Birds
  fly, unless penguins" beside "penguins do not fly" is the intended shape: one rule's
  `exceptWhen` names a predicate the other rule is about, and the clash is handled.
  Hiding it would tell an author there was nothing to see, where what there is to see is
  that the pair is handled — which is a thing the author wrote and may have written wrong.
- **A pair an [acknowledgment](#acknowledged-findings) names**, marked with its reason as
  `:acknowledged`. The subject names the pair as `(RulePairFn (Quote R1) (Quote R2))`, in
  either order and under any variable names, and the record is read from the audit
  context. The shipped ontology acknowledges two pairs
  in `abstract.txt`: the root denial `(properPartOf ?part ?whole) → (not (partOf ?whole
  ?part))` against the definitions `properCounterpart` generates for the tangible and the
  situation proper readings, both strict, which fire together only where the facts
  already contradict the root rule.

The two property marks are read **up** the predicate hierarchy, as every constraint is
convicted against them: two `fatherOf` conclusions clash against `(functional parentOf)`.
A mark's reach is asked at three points — whether the KB declares any, which group a
conclusion joins, and whether two conclusions share one — and all three go through one
reader, so a spelling reaches the detector through every read or through none.

"Could hold at once" is **shallow**, and five things rule it out: a literal appearing
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
arguments by its function's `arg` declarations. Each of the five is a **declaration read**: **no inference is run and no fact
is consulted.** A pair here is a clash that *could* form rather than one that has — a
clash already formed is in `(contradictions kb)`, which is the other question and the
other reader.

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
be a `relation` through `(arg arity 1 relation)`, and a rule `(lied_before ?x) => (liar
?x)` places the unified term under `person`. No ground term is both a relation and a
person, so the two rules never both fire for one term and the pair is dropped. A declared
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

**A pair whose antecedents cannot both hold is dropped, not flagged**, and the difference
from `:excepted` is the whole reason. Such a pair is not a clash anybody has to sort: the
two rules cannot both fire for one term, so nothing is in wait. Unreachable is the
engine's answer; handled is the author's. The shipped ontology's own case is the **arity
cycle**: `(unary_predicate ?p) => (arity ?p 1)` beside `(binary_predicate ?p) => (arity ?p
2)` would be a `:functional` clash on the `arity` table, and the antecedents are two types
`core.txt` declares `disjoint`; read the other way round, `(arity ?p 1) =>
(unary_predicate ?p)` beside `(arity ?p 2) => (binary_predicate ?p)` is a `:disjoint`
clash on the conclusions, and the functional `arity` slot drops it: one `?p` bound to two
arities.

A rule is never paired with itself, a pair is taken once, and the findings are in content
order of the first rule and then the second.

The pass has these limits:

- **Rule census, not candidate terms.** The pass reads every stored rule off the rule
  extent once, then pairs only the rules the consequent index brings together: a negated
  conclusion with the conclusions on its predicate's specs, two unary conclusions a
  separation divides, two binary conclusions under one shared mark. A pair is one
  unification and the five shallow rule-outs.
- **As stored.** A rule the KB currently disbelieves is still a rule somebody wrote. The
  declarations the pairing consults — `genl`, `disjoint`, `functional`, `asymmetric`,
  `genlCx` — follow belief, because a separation nobody believes separates nothing.
- **Visible from the audit context.** A rule the audit context cannot see is not paired,
  so a clash between two theories' rules is reported from a context that sees both. Two
  rules are a clash only where some context sees both halves, a common descendant of the
  two rules' contexts, and not where one sees the other, for [nmtms.md](nmtms.md)'s
  reason: asking only whether one sees the other exempts every sibling pair. The audit
  context sees both rules of every pair it pairs, so it is such a descendant, and each
  pair is judged there: the declarations the clash and the rule-outs read, and the
  acknowledgment, are those the audit context sees, and `:context` is the audit context.
  A separation or an acknowledgment stated in a context the audit context does not see
  changes nothing in its answer.
- **A variable consequent functor is not paired.** Such a rule concludes whatever binds,
  so it would clash with every other rule.

Each rule read and each candidate pair spend one work unit. `:max-results` counts
`:rule-clash` findings after the stranded-declaration category.

`kb-quality`'s `:clashes` reading is this pairing over every stored rule, without the
split ([quality.md](quality.md#contradictions-in-waiting)). It has no audit context, so
it judges a pair in each maximal common descendant of the two rules' contexts and reports
one entry per context the pair clashes in, in print order of the context. A pair
separated in one such descendant and clashing in another is reported at the second.

## The ontology-engineering smells

Three census passes flag how the `genl` and `disjoint` declarations arrange the taxonomy's
types, where no single declaration is a defect. Each finding is a candidate for an author to review, never a refusal, and the
sweep asserts and retracts nothing. A sweep without `:categories` skips all three passes,
and `:categories` names a pass to run it.

- **`:twin-genls`**: two or more types whose direct `genl` sets are identical and name at
  least two types besides `thing`, as `{:types [...] :genls [...]}`, which suggests a
  missing common parent.
- **`:derivable-stated-edge`**: a stated `genl` or `disjoint` that still holds with that
  one statement removed, as `{:stated r :path [a … b]}`, `{:stated r :also-stated-by [r
  ...]}` or `{:stated r :separated-by [r ...]}`, where each `r` is `{:handle :sentence
  :context}`.
- **`:disjoint-could-be-partition`**: a stated `(disjoint a b)` whose pair a known cover
  exhausts, as `{:disjoint r :suggest (partition c ...) :basis :covering|:sole-specs}`,
  where `:covering` adds the `:cover` sentences.

How each pass decides, and its limits:

- **Twin genls read direct edges.** A type's direct `genl` set is every visible edge one
  step up: a stated `genl`, a `covering`, `separating` or `partition` declaration installing its
  part under its whole, or a
  rule-derived edge such as an `intersection`'s. Every node of the `genl` relation is
  read once and grouped by that set, so the pass costs one unit per node. A type is
  read as the implicit-`genl` pass reads one, so a relation of two places or more is
  never grouped. Sharing the set is the whole test: an existing type below every shared
  genl, such as an `intersection` over them, is not looked for, and so it appears as a
  member of the group rather than suppressing it.
- **Derivable edges are structural, not a re-proof.** The engine has no query that asks
  whether a goal derives with one premise set aside, so the pass reads the taxonomy. A
  stated `(genl a b)` is redundant when the edge has another believed visible supporter
  (the same edge stated again, a whole-and-parts declaration installing it, a rule deriving
  it), or when a
  breadth-first walk over the visible direct edges reaches `b` from `a` without the edge
  `a`→`b`; the walk runs only after a cheaper test finds a direct parent of `a` other
  than `b` under `b`. A stated `(disjoint a b)` is redundant when the pair has another
  believed visible supporter, or when `separating-keys` names any other separation of
  `a`, or a supertype of it, from `b`, or a supertype of it: a `disjoint` over two
  supertypes, a `partition` or `separating` declaration, a `sibling_disjoint` parent or a
  `disjoint_metatype`. Only premises are read as stated, so a rule's conclusion is never a
  finding of its own. A supporter derived through the statement itself still counts as
  another supporter, and a statement reached only through a backward rule is not seen.
- **Partition candidates.** A `covering` declaration, which claims its parts exhaust the
  whole, is the KB's coverage knowledge: a `covering` naming both `a` and `b` whose parts
  `disjoint?` reads pairwise apart is basis `:covering`, and the suggested `partition` is
  then entailed. With no such cover, a common direct parent whose only direct specs are
  `a` and `b` is basis `:sole-specs`. Coverage is then a guess for the author to confirm,
  since the parent may have instances in neither. A parent a visible `partition` already
  divides into the pair is never suggested.

All three read from the audit context, so a declaration or edge it cannot see contributes
nothing, and an edge stated for a narrower reader that cannot see the other path is
still reported from a context that sees both. Their findings count against `:max-results`
in the order above, after the rule-clash category.

## What a missing-arg finding means

Every argument position of a predicate should say what fills it. `:missing-arg` reads every
predicate the audit context sees declared an arity, through an `(arity P n)`, an
exact-arity class such as `binary_predicate`, or `variable_arity_predicate`, and reports
`{:predicate P :arity n|:variable :missing [k ... :rest]}` for the positions no declaration
types:

- **What types a position.** An `arg`, `genlArg` or `quotedArg` at that position, an
  `argAndRest`, `argAndRestGenl` or `quotedArgAndRest` from that position or an earlier one, or an `args` or
  `argsGenl`, each read on `P` and on every super-predicate
  `res/constraining-predicates` reads, plus the `arg1` through `arg5` projections stated on
  `P` itself. For a unary predicate, a visible `genl` edge out of it types its one position,
  since `(genl P T)` says of P's members what `(arg P 1 T)` would. `interArg` and the
  `type_relation_predicate` mark relate or classify positions and do not count.
- **Variable arity.** Positions 1 to the least visible `arityMin` (1 when none) are
  checked one by one, and `:rest` is reported when no rest form and no `args` form types
  the tail beyond them.
- **Arity conflicts.** A predicate told two different arities is skipped, as
  `kb/relation-arity` reads it.
- **Declarations below the audit context.** An arity mark can be visible where the
  declarations typing the positions are not: the engine places an exact-arity class in
  CxUniverse (`chain/place-arity-class!`), and the starter's unary batch writes
  `unary_predicate` there for every type. So the pass also reads the declarations from each
  context that sees the audit context and stores an `arg`-family declaration on `P` or a
  `genl` edge out of it, and reports a position only if one of those contexts leaves it
  untyped too. With no such context, the audit context's reading is the answer. A context
  that does not see the audit context is not read, so from CxWell a relation declared only
  in CxTra is still reported.

The shipped contexts declare `thing` at each position that holds a term of any kind
([argtypes.md](argtypes.md#constraint-and-entailment-readings)). `:missing-arg` reports
the positions the starter leaves undeclared, and `ontology_test`'s `undeclared-positions`
gives the reason for each fixed-arity one.

`:missing-arg` is review-only: a sweep without `:categories` skips it, and `:categories`
names it to run it. The pass reads one census of arity declarations, then each
predicate's declarations in print order. It counts against `:max-results` after `:disjoint-could-be-partition`.

## What a taxonomy-island finding means

A type with a `genl` edge into a disconnected island answers nothing the closure reads
from the rest of the taxonomy: it is a type in spelling only. `:taxonomy-island` is
review-only, and reports each type node that does not reach the root:

```clojure
;; (genl stray_kind loose_kind)
{:status :gap
 :candidate-count 0
 :taxonomy-island
 [{:term loose_kind :root thing} {:term stray_kind :root thing}]}
```

The root is **found, not assumed**. `thing` is this engine's root and a converted corpus
brings its own, so whatever type the most nodes reach is the root reported against, ties
broken by print order, and the reading means the same on a corpus that never heard of
`thing`. Reachability is reflexive, as `genls` is, so the root is never a finding.

A name `relation?` answers true for, by a stored arity of two or more or a `variable_arity`
membership, is not a type node, so a sub-relation edge such as `core.txt`'s `(genl
partition covering)` is not an island. A name with no stored arity remains a candidate, so
an untyped root or a disconnected unary island is not silently dropped.

`:not-under-thing` reads a different population for a related defect: the caller's
candidate terms declared `unary_predicate`, against `thing` by name, whether or not they
carry any edge. A type with no `genl` edge is never an island, and an island the caller
did not name is never a `:not-under-thing` finding, so neither pass answers for the
other.

The pass has these limits:

- **Edge census, not candidate terms.** The pass reads the type nodes of every visible
  `genl` edge and each node's whole up-closure to find the root, so a chain of V types
  costs Θ(V²) where it has V−1 edges.
- **Review-only.** The root is found, so on a KB under construction an island may be a
  fragment awaiting its placement; a sweep without `:categories` skips the pass.
- **Visible from the audit context.** The nodes and the closures are those of the edges
  the audit context sees, and the arity and `variable_arity` declarations that make a
  name a relation rather than a node are those the audit context sees.

Each node's closure and reach test spend one work unit, and `:max-results` counts these
findings after `:missing-arg`. `kb-quality`'s `:taxonomy`
reading counts the same nodes over every context ([quality.md](quality.md#taxonomy-coverage-is-two-numbers)).

`:rule-clash-review`, described under the rule-clash finding above, counts against
`:max-results` after `:taxonomy-island`, and `:rule-macro-review`, described under the
rule-macro finding, last.

## Acknowledged findings

`(acknowledgedFinding category subject "reason")`, a `core.txt` predicate, records that a
check flagged a finding, someone looked, and why it stays. The sweep moves an
acknowledged finding to its category's review-only bucket instead of dropping it, so it
stays visible with the reason beside it and no longer makes a default sweep `:gap`:

| category | subject | review bucket | read from |
|---|---|---|---|
| `:rule-macro` | the suggested declaration, `(genl livesIn locatedIn)` | `:rule-macro-review` | the rule's context |
| `:rule-clash` | the pair, `(RulePairFn (Quote R1) (Quote R2))` | `:rule-clash-review` | the audit context |

Each rule is quoted on its own. A quoted term is opaque, so no inference or
canonicalization reaches inside either one, and what the pair needs inferred — that
`(RulePairFn R1 R2)` and `(RulePairFn R2 R1)` name the same pair — belongs to
`RulePairFn`, outside both quotes. `core.txt` states `(commutative RulePairFn)`, so the
store holds both orders as one sentex, sorted as a ground compound since a quoted form is
a constant ([canonicalization.md](canonicalization.md#compounds-below-the-literal-sorted)).

```clojure
;; (acknowledgedFinding :rule-clash
;;   (RulePairFn (Quote (implies (penguin ?x) (not (flies ?x))))
;;               (Quote (implies (bird ?x) (flies ?x))))
;;   "penguins are birds that do not fly")
{:status :gap
 :candidate-count 0
 :rule-clash-review
 [{:rules [812 813] :kind :negation :unifier {?x ?x'} :context CxUniverse
   :sentences [(implies (bird ?x) (flies ?x)) (implies (penguin ?x) (not (flies ?x)))]
   :excepted false :acknowledged "penguins are birds that do not fly"}]}
```

The subject names the finding by content, as `declined_rule_macro` always has, so the
record survives a text export, and an edit that changes the finding's content brings the
finding back. A rule pair is matched by each rule's canonical sentence, so the spelling of
its variables and the order of its antecedents do not matter. The sweep compares the two
canonical sentences as a bag, since they may sort differently from the quoted spellings the
store ordered the pair by. That comparison is the sweep's own, and nothing canonicalizes
inside a stored quote. Where several records
acknowledge one finding, the first in print order supplies the reason. The sweep reads
`acknowledgedFinding` and nothing else: other spellings of an acknowledgment, such as
`declined_rule_macro`, are rules in the KB concluding one. Every other category ignores
the record.
