# Sentex canonicalization (`vaelii.impl.sentex`)

- **Covers:** how a sentence's variable names, antecedent order, symmetric and commuting
  arguments at any depth, a declared function's nested, repeated and absorbed arguments,
  and comparison direction fold to one stored handle, and how a conjunctive
  consequent or a disjunctive antecedent unfolds into several.
- **Not here:** which spellings are legal for a predicate, individual, type or context →
  [naming.md](naming.md); how the canonical form becomes the trie key →
  [indexing.md](indexing.md).
- **Assumes:** sentex, rule, antecedent, consequent → [glossary.md](glossary.md).

Beyond the connectives, a sentence is put into a canonical form so logically
identical knowledge is stored once.

## Canonical variables

A rule's variables are renamed `?var0`, `?var1`, … by first occurrence in
canonical order. **`:varmap`** maps them back to what the author wrote
(`{?var0 ?x}`), and `sentex/originalize` restores the original names for display.
Facts carry no varmap.

## Canonical literal order

A rule's antecedents are sorted **structurally** — rank, arity/shape, then value.
Ordering runs *before* numbering with a variable-**blind** comparator, so it can
never depend on the author's variable names. Literals that tie under it (a
same-predicate self-join) are resolved by an **exact prefix minimization** — the
order is built one literal at a time, keeping only the minimal extensions — which
returns the smallest canonically-numbered form without enumerating the tie group's
permutations.

The comparison runs over the **whole rule** — antecedents, then consequent, then
exception — because two orders can render identical antecedents and differ only in
what the consequent says about them. Comparing antecedents alone leaves that decided
by traversal order, and breaks dedup at tie groups as small as **two**. A lexical
comparison of constant symbols is the last resort.

Cost is O(k²) numberings for any tie group whose literals are distinguishable at
all. The hard shape is genuine **automorphism** — k antecedents of one predicate
sharing no variables, a joinless cross product — where every ordering renders the
identical antecedents and only the consequent (then the exception) separates them.
The exact search would keep all k! orderings and pick the minimal consequent at the
end; `prune-by-tail` instead folds the consequent into the search. Such a group is
**joinless** (so every ordering renders the same antecedents) and **tail-isolated**
(its variables touch no other antecedent, so its ordering changes nothing but its own
consequent), which makes the consequent the whole tiebreak — a never-reordered form,
so projecting it is content-, not order-dependent. Projecting it under each survivor's
partial numbering (an unnumbered variable → a sentinel that sorts last) and keeping
only the minimal-so-far survivors each round collapses the automorphic case to O(k²)
too, with no cap. It is exact, not a heuristic: numbering is monotonic across rounds,
so an unnumbered variable can only be given a larger number later — a survivor whose
projected tail is strictly larger can never be the whole-rule minimum. The tie is
broken **per origin** (the incoming survivor a candidate descends from), so it never
decides between orderings that differ on an earlier group's antecedents, which outrank
the tail. The result is identical to the exhaustive search; only the cost changes.

Two kinds of literal are **held back** in the author's order, because their
position is operational rather than logical:

- **Deferred (evaluable)** literals — which consume bindings rather than produce them.
  `sentex/deferred-predicates` names twenty-two: `evaluate`, `lessThan`, `greaterThan`,
  `matchesPattern`, `different`, `unknown`, the six value kinds (`integer`, `string`,
  `number`, `boolean`, `keyword`, `character`), the five quantity comparisons, and the
  five aggregation operators.
- The **recursive** literal of a recursive rule. Reordering it could turn a
  right-recursive rule left-recursive, which the backward chainers cannot execute.

Two spellings of a rule that differ only in the order of their held-back literals are two
rules. The planner runs the held-back literals whose inputs are bound in the stored order
(`plan/ready`), so the order decides which test short-circuits the others.

## A NAF conjunction's conjuncts sorted

`(unknown (and A B))` and `(unknown (and B A))` are one rule. The conjuncts are
independent ground existence checks — closure leaves every variable bound before the
query runs — so their written order, and a repeat, are not their identity. Sorted with
the variable-blind comparator, since this runs on the surface literal, where the
author's variable names are still what they wrote. Every conjunction in the query is
sorted: the `unknown`'s own, a `thereExists` body's, and that of an `unknown` or
`thereExists` conjunct at any depth. A `forall` desugars to that shape, its body into
the `thereExists` conjunction and its head into a nested `unknown`. An exceptWhen
exception's top-level conjuncts are sorted once the query is aligned to the rule's
varmap (`sentex/canonical-exception`), and the conjunctions inside each conjunct are
ordered as an `unknown` antecedent's are, by the sort and the tie-break below, with one
difference: a deferred literal inside an exception's conjunction is held back after the
generators in its written order. The forward join runs a deferred literal whose inputs
are unbound in that order, and an exception's aggregate can bind what a later test
reads, which an `unknown` query refuses (`:naf-not-closed`).

Conjuncts the blind sort leaves tied (`(likes ?x ?c)` beside `(likes ?c ?x)`) are
ordered when the rule is numbered, by the antecedents' prefix minimization run from the
numbering the rule has reached at that literal (`sentex/naf-numberings`): the outer
variables already hold their canonical numbers, and the binder's variables take the
next ones by first occurrence. The comparison is over the whole rule, as it is for the
antecedents. A conjunction with no tie is numbered straight through, so its stored form
is the one the blind sort alone gives.

A `thereExists` or `forall` binder is a set. Its variables are reserved the block of
numbers after the ones the rule has reached, take them by first occurrence in the body,
and are stored in number order, so `(thereExists (?c ?d) …)` and `(thereExists (?d ?c)
…)` are one rule. A one-variable binder is stored bare: `(?c)` is `?c`.

## Symmetric arguments sorted — ground literals only

A *ground* `(siblingOf Bob Ann)` and `(siblingOf Ann Bob)` store as one sentex. A
literal holding a variable is a **pattern** (a query, or an antecedent about to be
matched) and is never reordered: variables sort last, so sorting one would move its
ground argument into slot 1 and miss the stored fact.

Order-insensitive *lookup* is handled at match time instead — `res/raw-match` and
`core/sentexes-matching` probe **both argument orders** for a symmetric predicate, which is
how a query answers a pair whichever way round it was asked. Sorting needs the taxonomy,
so every store/lookup builds its sentex through `res/kb-sentex` (which supplies
`:symmetric?`).

The definitional checks read a literal in the stored order too (`checks/checked-sentence`,
for a symmetric or commuting functor), so each argument meets the `arg` and `genlArg`
declarations of the position it is stored at. The two spellings of one fact draw the same
derivations, and `record-arg-types` adds none to either
(`argtype_entail_test/a-symmetric-fact-derives-at-its-stored-positions-in-either-spelling`).

### A mark arriving after the facts migrates them

The sort is what the *entry point* does, so a `(symmetric P)` declaration arriving after `P`'s
facts leaves the store holding spellings no later assertion will ever produce — and if
both spellings of one pair were written, two records for one proposition, each retractable
without the other. Match-time probing does not close that: it makes both records answer,
which reports the fact twice rather than once.

So the declaration migrates what is stored (`integrate/commute-existing`), which is the
one retroactive arm that writes records rather than deriving content. A row with no mirror
stored is **re-spelled where it lies** — same handle, same TMS node, same premise mark,
same justifications (`kb/respell-sentex!`, the store's third mutation beside
`create-sentex` and `integrate/sentex-removed!`). A mirrored pair **folds into one row**:
the redundant one hands over its premise mark, the justifications that conclude it, the
justifications drawn through it and its handle-naming metas, and then leaves through the
ordinary teardown.

Which of a pair survives is decided from what supports it and only then from the handle.
The row standing on nothing but its own premise is the one that goes, because
`jtms/retract!` is exactly the sweep that takes it. A row a rule concluded leaves through
`integrate/fold-supports!`, which copies the justifications naming it as their consequence
onto the survivor. `integrate/take-out!` then drops the originals and retracts the row, so
the row leaves the network with its record and no justification names a handle with no
record. Between two rows the fold has no other reason to separate — both bare premises,
or both a rule's conclusion — the **lower handle** survives: it is the row the KB would be
holding had the declaration come first, which is the claim being restored.

The argument-type mints a moved row triggers are the one thing resting on it that reads its
spelling: each mint names the declaration of the position its argument held. So once the
row is at its new spelling, `integrate/move-row!` draws the entailments that spelling
meets and drops each mint justification the row triggers that the spelling does not draw
(`special/redraw-mints`), and the justification a fold copied from the other spelling goes
the same way. The KB then holds the mints of the order that stated the mark first
(`argtype_entail_test/a-symmetric-mark-arriving-after-its-facts-leaves-the-mints-of-the-mark-arriving-first`).

The migration is a **write**, so it leaves the records themselves canonical and `recover`
reads a store that needs no reconciling (`recover_independence_test`). The alternative — an
alias recording that two records mean one — would have to be rebuilt on every `recover`
from records that still spell the fact two ways, and consulted for ever after by matching,
retraction, the TMS and every handle entry point.

### A mark leaving hands the spellings back

The kept spelling is a belief. After `(symmetric bRel)`, `(bRel Zed Amy)` and the mark's
retraction, a store left holding `(bRel Amy Zed)` answers `false` to the fact as the caller
wrote it and `true` to its mirror, which a KB never told the mark answers the other way
round. The same holds for a row the late mark re-spelled, and a folded pair is worse: one
row stands where that KB holds two, each asserted at its own class and each retractable
alone.

So each row records the spellings its pieces were written in, under the provenance entry
`integrate/spellings-key`: `{:premise {written strength} :derived {jid written}}`.

- **Premises:** one entry per premise assertion, at the class it was asserted at.
- **Rule firings:** one entry per firing whose conclusion the sort moved.
- **Only what differs is written.** A predicate nothing permutes writes no record. The
  premise map is the one exception: once it exists it lists the stored spelling's
  assertions too, because one premise class on one row cannot say which spelling brought
  it.
- **Written at four points:**
  - the assert entry point (`note-premise-spelling!`);
  - a rule placing a conclusion (`chain/place-fact-conclusion`);
  - a late mark re-spelling a row, which writes out what the row's own spelling had held
    implicitly;
  - a fold, which hands the doomed row's pieces to the survivor.
- **Why provenance:** it is the per-handle record every store already keeps durably, so a
  restart reads the spellings back with no new store method. `core/provenance` does not
  return the entry, and `add-provenance` cannot overwrite it.

A mark stops holding when its last statement is retracted or goes OUT. A placed `defeat`
or an `except` moves no label and is the next section's case. Both reach the
taxonomy at one of two choke points, the removal arm and the belief refresh, and each
queues the predicate whose permuting marks moved. The settle that follows drains the queue
through `chain/reconcile-spellings!`. That call puts every piece at the row its spelling
canonicalizes to now:

- a premise assertion is re-asserted there at its own class;
- a firing is re-placed there with its own antecedents and bindings, and dropped from the
  old row (`jtms/drop-justification!`).

A row no piece stays on is swept, with what was drawn from it: those conclusions read a
spelling nobody wrote. A mark that starts holding again by a relabel has no declaration
arriving to fold what it covers, so the same call folds it (`integrate/commute-predicate`).
Both directions are checked per permuting mark, shape and arrival order against a KB never
told the mark (`order_independence_test`), and across a restart
(`recover_independence_test`).

A handle the caller holds keeps naming its row while the mark holds. Once the mark leaves,
a spelling that moved answers at a new handle, as it would in a KB that stored it apart
from the start.

`core/preview` does not show the split. It runs its settle with the sweep off and must hand
the KB back at the same handles, so a preview of retracting a mark reads the rows as still
folded.

### A mark a reader does not believe

A mark is read from every context, so a mark leaving every reader at once is the case
above. A placed `defeat` or an `except` of a mark's statement takes it away from the
readers that see the defeat and from no other reader, and those readers read a fact on the
predicate as written. The four permuting marks stay visible from every context ([A
context outside the topology](contexts.md#a-context-outside-the-topology)), so whether a
reader believes one is read from the defeats and excepts it sees
(`res/supporter-believed?`).

The store holds the spellings the readers of each fact read
(`res/spelling-planner`). The readers are the fact's context and the contexts where it
meets a context stating a `defeat` or an `except` that reaches a statement of the mark
(`res/spelling-readers`, over `tax/meet-closure`), kept where they see the fact's
context:

| the readers of `(P Bea Ada)` written in `Cf` | stored |
|---|---|
| every one believes the mark (nothing defeats it, or the defeat is placed where no reader of `Cf` sees it) | `(P Ada Bea)` alone, holding the premise and the spelling record, as above |
| none believes it (the defeat is placed at `Cf` or above it) | `(P Bea Ada)` alone, as written |
| some do and some do not (the defeat is placed below `Cf`) | `(P Bea Ada)` holding the premise, and `(P Ada Bea)` in `Cf` justified by `[(P Bea Ada) mark]` under informant `respell` |

- **Store keys.** Each row is keyed by its own spelling: the as-written row by the
  spelling written, the `respell` row by the sort under the marks its readers believe.
  Dedup reads the key the spelling has, so a second assertion of `(P Bea Ada)` finds the
  as-written row, and one of `(P Ada Bea)` finds the sorted row. `res/*spelled-by*` tells
  `res/kb-sentex` which marks spell the literal for the store and for a lookup.
- **What a reader reads.** The read walk hides a `respell` row from a reader that does
  not believe the mark, since the row rests on it. A read hides the as-written row from a
  reader that believes the mark, and drops a match read in an argument order the marks
  the reader believes do not license (`res/without-unbelieved-spellings`, beside
  `res/without-retired`). A ground goal is probed at its written spelling as well as at
  the sorted one (`res/raw-match`, `matches-hierarchical`). `has-prop?` of `:symmetric` or
  `:commutative` with a context answers whether that context believes a statement, so the
  symmetric prover reads the mirror only where the mark is believed. `handle-of` looks a
  sentence up under the marks its context believes.
- **Several commuting groups.** A reader that believes some of a predicate's groups reads
  a fact sorted by those groups alone. More than one spelling read puts the premise at the
  spelling written, and each other spelling read is a `respell` row.
- **Class.** A `respell` justification confers the as-written row's class
  (`jtms/class-antecedents`). The marks it rests on decide whether it is valid and cap
  nothing, as a premise rule informant caps nothing. A reader that believes the mark
  therefore reads the sorted row, and every firing over it, at the class a KB with no
  defeat reads, so a defeat below a context moves no class there
  ([nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage)). A reader that does not believe
  the mark reads neither the row nor what rests on it alone. Its verdicts read the classes
  the members' support carries with the mark's defeats in force there forced OUT
  (`exc/mark-defeated`, [nmtms.md](nmtms.md#why-a-read-runs-no-rounds)).
- **When it runs.** A `defeat` or an `except` stored, removed or moved in force queues the
  predicates whose mark statements rest on its target (`special/note-mark-reach!`), and a
  write storing a fact on such a predicate queues its row (`integrate/note-premise-spelling!`).
  A `genlCx` edge stored or removed while a `defeat` or an `except` is stored queues every
  predicate whose readers disagree (`special/note-split-marks!`), since the edge moves which
  readers see the defeat.
  The settle draining `:respell` brings the rows to the spellings their readers read
  (`chain/respell-rows!`), at a cost linear in the rows of the moved predicate. A KB where
  every reader believes every mark queues nothing.

`order_independence_test`'s `a-permuting-mark-defeated-below-the-facts-is-read-per-reader`
asserts both readers over sampled arrival orders, and
`a-defeated-permuting-mark-leaves-each-spelling-as-written` the case where no reader
believes the mark. `a-defeat-below-a-split-fact-moves-no-class-above-it` and
`a-firing-over-a-split-fact-takes-its-class-per-reader` assert the class each reader reads,
with a `^:slow` twin of each walking every arrival order.

## Commuting arguments sorted — the same sort at any arity

`symmetric` commutes the two arguments of a binary predicate. Three marks state the same
licence over any set of positions at any arity, and `(covering Engine Piston Rod Valve)`
stores as one sentex however the parts are ordered:

| Declaration | What permutes |
|---|---|
| `(commutative P)` | every argument, at each arity `P` is applied at |
| `(commutativeInArgs P p1 p2 …)` | exactly the named positions; every other stays put |
| `(commutativeInArgAndRest P f)` | position `f` through the application's own end |

All three install a group directly, at their own arm in the special-predicate table, and
`(commutative P)` installs the group `[:rest 1]` beside the `:commutative` prop it is
queried by. So no spelling is derived from another: the canonicalizer reads one table
whichever one was written.

The equivalence between `(commutative P)` and `(commutativeInArgAndRest P 1)` stays in
`core.txt` as `set/inertRule`s — believed, indexed and queryable, run by neither engine —
because the engine has no `iff` to state it with and neither mark has to derive the
other any more. The direction back to `commutative` is two rules, one requiring
`(arity ?p ?n)` and one `(arityMin ?p ?n)` with `(greaterThan ?n 1)`, as the
`at_least_binary` floor rules read a length: `(commutativeInArgAndRest P 1)` holds vacuously
of a unary `P`, and a commutative relation is `at_least_binary`.

`(genl symmetric commutative)` classifies every symmetric predicate, and `(commutative P)`
with `(arity P 2)` concludes `(symmetric P)` — commutativity at two arguments **is**
symmetry, where commutativity at any other arity implies neither symmetry nor arity 2.
That last one is a `set/forwardOnlyRule`, and the three directions around it are what
this vocabulary costs a backward search if they are written any other way.

### A bridge between two marks is a cycle backward

`set/forwardRule` adds forward chaining **without taking the backward use away**
(its engines are `#{:forward :backward}`), so a rule written with it answers goals too. Four
rules here conclude a mark that another of them needs:

- `(commutative ?p)` → `(commutativeInArgAndRest ?p 1)` and back, the two directions of
  one equivalence, the way back written once per length reading.
- `(commutative ?p) ∧ (predicate ?p) ∧ (arity ?p 2)` → `(symmetric ?p)`, whose conclusion
  `(genl symmetric commutative)` makes a **spec** of `commutative` — and
  `provers/candidate-rules` offers a rule concluding a spec as a candidate for the
  supertype goal. So the rule answers the goal its own antecedent poses.

`provers/candidate-rules` carries no ancestor-goal guard, so nothing stops the descent.
The depth bound (`inference/*max-depth*`) does stop it, which turns the cycle into an
exponential frontier inside that depth rather than a refusal, and `(genl commutative
relation)` puts `(commutative ?p)` under every open `(relation ?x)` query — so the cost
reached every caller of the inference engine, not only a caller asking about
commutativity. Forward chaining has no such trouble with any of the three: it derives each
conclusion once and reaches a fixpoint, and an unfounded pair is labelled as one
([nmtms.md](nmtms.md)).

So the equivalence is inert (the marks install directly, and it derives nothing either
way) and the arity bridge is forward-only (it derives, and a backward walk of it is the
cycle). Writing any of the three as `set/forwardRule` returns the stall.

The three written spellings reduce to one runtime descriptor, and
`sentex/commuting-components` turns the descriptors a predicate carries into the position
**components** one literal permutes. Three things that reduction decides:

- **Overlapping groups merge.** `(commutativeInArgs P 1 2)` beside `(commutativeInArgs P 2
  3)` says 1 and 2 interchange and 2 and 3 do, so 1 and 3 interchange through 2. Sorting
  the two groups in sequence would make the stored form depend on which ran first, which
  is an order dependence in the storage key.
- **A `:rest` group is closed by the literal's own arity.** So `(covering W A B)` and
  `(covering W A B C)` are two claims, and no permutation moves an argument between them.
- **A component of one position is dropped.** A mark whose positions fall past the
  literal's arity leaves it alone without a special case. No unary predicate is marked
  `commutative`: `commutative` is below `at_least_binary`, since one position is no
  permutation.

Sorting is the same rule as `symmetric`'s: ground literals only, within each component,
other positions fixed. Repeats keep their multiplicity — commutativity changes order,
never content or arity.

Lookup fans the pattern over its arrangements where the symmetric path probes the mirror,
and the fan is **pruned to what a stored fact can hold**: storage sorts the ground
arguments inside a component, so an arrangement holding them out of order matches nothing
and is not probed. With `v` variables among a component of `g` positions that is
`g!/(g-v)!` probes rather than `g!` — a ground tail probes once however long it is, and
one variable in it probes `g` times. Where the fan really is factorial the *answer set*
is too: `g` distinct variables match one stored fact `g!` ways, each a different binding,
which is `(siblingOf ?a ?b)` matching a stored pair twice, at a longer arity.

The mark is read off the literal's **exact functor**, like `symmetric`'s, and a `genl`
edge below a commutative predicate does not make the sub-predicate commutative. A late
declaration reaches the facts already stored through the same `integrate/commute-existing`
migration described above.

## Compounds below the literal sorted

The symmetric and commuting sorts apply to every compound below the literal as well as to
the literal: a function application in an argument, and a literal inside a sentence
argument. `(holds (PairFn Ann Bob))` and `(holds (PairFn Bob Ann))` store as one sentex
under `(commutative PairFn)`, and `(believes Ann (bordersOn Cid Bob))` and `(believes Ann
(bordersOn Bob Cid))` under `(symmetric bordersOn)`. `sentex/canonical-args` walks the
argument terms and sorts the innermost compound first, so a sort above it compares
canonical subterms. `sentex/permute-args` lists the sorts, and the literal and each
compound read that one list.

- **Ground compounds only.** A compound holding a variable keeps its written order, for
  the reason the literal does. A variable inside a `(Quote …)` does not count, since a
  quoted form is a constant (`sentex/sortable-term?`): `(RulePairFn (Quote R1) (Quote R2))`
  over two quoted rules sorts under `(commutative RulePairFn)`, and neither quote is
  entered. A ground compound inside a pattern is sorted, at the rule
  write by the same walk, and in a goal at the match entry points
  (`res/probe-spelling`), so a goal names it in either order.
- **A pattern below the literal is matched as positioned.** `res/raw-match` fans the
  literal's own arguments over their permitted arrangements and does not fan a compound
  below it. `(holds (PairFn Bob ?x))` therefore matches a stored `(holds (PairFn Ann
  Bob))` only when the store's order puts `Bob` first.
- **Held as written.** The walk stops at a quoting function, so `(holds (Quote (PairFn
  Bob Ann)))` and `(holds (Quote (PairFn Ann Bob)))` are two sentexes. It stops at a
  `natFormula` or `rewriteOf` expression, which is a verbatim NAT payload, and at a
  `reifiable_function` application, whose constant is named by the expression as written
  ([nat.md](nat.md#write-path)). A reified NAT is minted before the sort, so
  `(PairFn Ann Bob)` and `(PairFn Bob Ann)` under a reifiable `PairFn` mint two constants.
- **An `or` in an argument is a term.** The shipped ontology declares no mark on `or`,
  so `(believes Ann (or P Q))` and `(believes Ann (or Q P))` are two sentexes
  ([Where `or` cannot go](#where-or-cannot-go)). A KB stating `(commutative or)` folds
  them.
- **A mark arriving or leaving reaches the nested rows.** `integrate/rows-spelled-by`
  adds the rows the term index keys by the marked functor to the functor's own rows, and
  `commute-existing` and `chain/reconcile-spellings!` walk that set. A firing the leaving
  split moves has its antecedents read again by the agenda, since a fold of two
  conclusions keeps one justification for two bindings.
- **Every reader reads the store's order below the literal.** The per-reader spelling of
  [A mark a reader does not believe](#a-mark-a-reader-does-not-believe) reads the marks of
  the literal's own predicate. A `defeat` or an `except` of a mark on a functor applied
  below the literal moves no reader's spelling of that compound.

A store written before compounds below the literal were sorted holds them as written, and
a ground lookup of such a row by its written spelling misses it. `export-text!` then
`load-text!` re-canonicalizes the store.

## A function's terms reshaped by declaration

Three marks reshape a ground application of a function below the literal, beside the
sorts. `sentex/canonical-term` applies them, in the walk above, to the compound whose
functor carries them:

| mark | the application | example |
|---|---|---|
| `(associative F)` | an argument applying `F` has its arguments spliced in, before the sort | `(F A (F B C))` → `(F A B C)` |
| `(idempotent F)` | an argument equal to its neighbour after the sort is dropped when `F` is also associative; otherwise only an application whose arguments are all one term collapses | `(F A B A)` → `(F A B)` |
| `(meetFunctionOf F R)` | an argument another argument lies below by `R` is dropped; of two arguments below each other, the `cmp-term`-least stays | `(F (DatetimeFn "2000") (DatetimeFn "2000-03"))` → `(DatetimeFn "2000-03")` |

An application of an idempotent or meet function left with one argument is that
argument. Core.txt's forward rules conclude `commutative`, `associative` and `idempotent`
from `meetFunctionOf`, so the one declaration gives all four arms.

- **The order's registered comparator decides absorption.** `res/meet-order` reads
  `datetime/order-comparators`, a pure function of the two terms (`subintervalOf` reads
  the calendar fields, so `(MonthFn 2000 3)` and `(DatetimeFn "2000-03")` lie below each
  other). A stored `(R a b)` fact is never read, so a stored form does not move with
  belief: two named times are not absorbed whatever is stated between them, and an order
  with no registered comparator absorbs nothing.
- **The arms keep the walk's limits.** They read the exact functor, unscoped. They
  touch a ground application only, stop at a quoting function, a NAT payload and a
  `reifiable_function` application, and reach the stored rows through
  `integrate/commute-existing` and `chain/reconcile-spellings!` as a commutativity mark
  does. A pattern holding a variable inside such an application keeps its written shape,
  so `(holds (F ?x (F B C)))` matches no stored `(holds (F A B C))`, and a `defeat` of a
  term mark moves no reader's spelling.

## Comparison siblings folded

`greaterThan` is stored as `lessThan` with reversed arguments
(`sentex/comparison-siblings`), so only the `<` direction is ever stored; a
`greaterThan` *goal* is still answerable.

## Comparison chains collapsed

`lessThan` is **variable arity**, and chains in a rule merge: `(lessThan ?a ?b)` +
`(lessThan ?b ?c)` ⇒ `(lessThan ?a ?b ?c)`. A branch (`?a<?b`, `?a<?c`) is left
alone.

## Rule wrappers become fields

`(set/forwardRule (implies …))` is not data *about* a rule — it is how the rule's
direction is written, so like `not`/`implies` it canonicalizes **into the record**. The
wrappers state two things, and the record holds them as two fields plus `:defeasible`:

- `:engines` — which engines run the rule, a subset of `#{:forward :backward :solve}`.
  `#{:backward}` for a bare `implies` (the tractable default, since forward chaining
  materializes a conclusion per match), `#{:forward :backward}` for `set/forwardRule`,
  `#{:forward}` for `set/forwardOnlyRule` (forward-chains and never backchains), `#{}` for
  `set/inertRule`; `set/solveRule` adds `:solve` to whichever of these the rule has, so a
  solve runs it as a normal rule ([solving.md](solving.md)).
- `:effect` — what the head is: `:derive` for a truth, `:choose` for a
  `set/assumptionRule`'s choice, `:forbid` / `:penalize` for a hard / soft constraint's
  marker ([solving.md](solving.md)). Only a `:derive` rule has a choice of engines; the
  other three hold `#{:solve}`.
- `:defeasible` — from `set/defaultRule`.

Wrappers may nest — a defeasible forward rule — and never reach the stored sentence. The
`:direction` opt on `assert` and `assert-rule` is just the programmatic spelling: it
wraps, and the wrapper becomes the field.

A combination the record cannot hold is refused `:not-well-formed` rather than resolved
(`sentex/wrapper-stack-problems`): two different direction wrappers around one rule,
two different head wrappers (`set/assumptionRule`, `set/hardConstraint`,
`set/softConstraint`), or a head wrapper under a direction wrapper or `set/defaultRule`.
A choice or constraint head is decided by a solve and never chained, so a direction or a
default on one says nothing ([solving.md](solving.md)); a `:direction` opt on one is
refused `:unknown-option` for the same reason. A wrapper repeated says one thing twice
and is accepted.

`:effect` is in the identity key, so a choice or constraint rule and its bare twin are
two sentexes. Neither `:engines` nor `:defeasible` is, so re-asserting with a different
direction or default wrapper resolves to the **one** sentex. Where the two spellings
disagree, the slot is then resolved from **content**: the union of the engines (`#{}` is
the bottom, and a backward-only spelling joined with a forward-only one comes to
`#{:forward :backward}`), and strict over defeasible — a rule somebody also stated without `set/defaultRule` is one
they stated as holding outright. Both resolutions are commutative and idempotent, which is what the pair
has to be: keying the slot on which assertion arrived first would let the same two
assertions in the two orders reach two sets of beliefs, and order independence is
not negotiable ([nmtms.md](nmtms.md)).

A **third** slot resolves the same way, and for the same reason read one step
further. `:strength` — the class the rule itself is held at, `opts :strength` at the
entry point — is not in the identity key either, and it takes the **stronger** of the two
assertions. A re-assert carrying no `:strength` states nothing about the class, so
reading that silence as a downgrade would make `defeat-class` answer differently for
the same two assertions in the two orders. No *belief* moves either way, nothing in
the engine defeating a rule ([nmtms.md](nmtms.md)), which is why this one is about
what a caller reads back rather than about what the KB believes. Narrowing any of
the three is `retract!` and re-assert, never a second spelling.

The **fact** entry point resolves its own `:strength` the same way and by the same argument,
where belief does move: a re-asserted fact keeps the stronger mark, so a bare re-assert
of known-true content cannot retire it ([nmtms.md](nmtms.md)).

## Polycanonicalization: one rule written, several stored

The connectives above canonicalize **into** the record — `implies` and `and` become the
antecedent vector and the consequent, a `set/*Rule` wrapper becomes a field, and a `not`
stays as the sentence's one head, which is the literal's sign. Two of them cannot,
because what they say is not about one
rule: a rule that concludes a **conjunction** makes two claims, and a rule whose
antecedent **disjoins** fires for two reasons. Both are *polycanonicalized* — the one
sentence the author wrote is stored as several rules, and the connective is gone before
anything is canonicalized, keyed or indexed.

**A conjunctive consequent splits per conjunct** (`rules/expand-consequent`):

```clojure
(implies A (and C1 C2))   ⇒   (implies A C1)   and   (implies A C2)
```

Each is keyed by its own consequent predicate, which is what the rule index needs: a
backward goal on `C2` reaches a rule filed under `C2`, and a rule filed under the
compound `and` would be reachable by no goal at all.

**A disjunctive antecedent distributes per alternative** (`rules/expand-antecedent`):

```clojure
(implies (or A B) C)          ⇒   (implies A C)          and   (implies B C)
(implies (and (or A B) D) C)  ⇒   (implies (and A D) C)  and   (implies (and B D) C)
```

The distribution is to **DNF**, so an `or` nested inside an `and` inside an `or` expands
too, and a one-disjunct `(or A)` is just `A`. The reason it is expansion rather than a
record slot is the same reason again, read from the other side: the rule index keys a
rule by its antecedents' predicates and forward chaining triggers it from an arriving
fact, so a stored `or` would have to be a predicate — and it names none. Expanded, each
alternative has concrete antecedent predicates and triggers exactly as a hand-written
rule does.

**The two compose, and the result is the product.** `(implies (or A B) (and C1 C2))` is
four rules, alternatives outermost and conjuncts within — which is the order `assert`
stores them, and therefore the order an `exceptWhen` is re-attached along.

### What the author gets back

`assert` and `assert-rule` return the **vector** of handles whenever the rule expanded
to more than one, and a bare handle when it did not. The vector is the author's record
of the whole rule: retracting one handle retracts that one alternative or that one
conjunct, and retracting the rule means retracting them all. `retract!` refuses the
vector itself (`:bad-handle`), rather than treating `(retract! kb (assert kb rule ctx))`
as a no-op that reads like there was nothing to do ([api.md](api.md)).

Everything downstream sees ordinary rules. Each expansion is canonicalized **on its
own** — its own variable numbering, its own antecedent order — and carries its own
handle, TMS node and justifications. Each **dedups against an individually asserted
twin**: writing `(implies A C)` out after the disjunctive rule finds the stored one and
joins its slots exactly as any re-assert does ([nmtms.md](nmtms.md)). `why` on a
conclusion names the alternative that fired, which is the rule a reader can go and
retract.

`canonical-sentex` is the one reader that stops short of the expansion, and deliberately:
it answers for the sentence **as written**, so a rule that polycanonicalizes has no single
canonical sentex to hand back — the canonical forms are its expansions', one each. Ask it
of each alternative when that is what you want. (This is the same for both causes: a
conjunctive consequent comes back whole too.)

An `exceptWhen` is split off before the expansion runs and re-attached **once per
expansion**, against that expansion's own handle and aligned to its own varmap — the
exception belongs on the rule it excepts, and after the split there are several
([exceptions.md](exceptions.md)). A generator's generated rule keeps its `or` until the
mint substitutes the holes, and `chain/mint-rule` expands what it is about to store, so
the alternatives a generator generates are the alternatives of the rule it generated
([generators.md](generators.md)).

### Two things about the whole rule

**Range restriction is asked per alternative**, and this is the check the expansion
cannot inherit from the flat one. `(implies (or (dog ?p) (cat ?q)) (fed ?p))` has `?p`
somewhere in its antecedents, so a read of the disjunction whole passes — and then one
of the two rules it expands to concludes about a variable nothing binds. So each
alternative is checked on its own, and the **whole** rule is refused
(`:not-range-restricted`) naming the disjunct the bad alternative took. Half a rule is
not what anybody wrote, which is the same reason every conjunct is checked before any is
stored.

**The width is capped at 16 alternatives** (`rules/max-alternatives`), refused
`:disjunction-too-wide` with the count. The cost of a disjunction is paid in handles,
index entries and TMS nodes rather than at query time, and nested disjuncts multiply, so
a rule that reads like one line can cost thousands. The count is arithmetic — a product
over the antecedents — so a rule far over the line is refused without ever being
materialized. Past the cap the alternatives are better named as a **type**: a `genl`
edge per member and one rule on the supertype, which is one handle however many members
it covers.

### Where `or` cannot go

The connective is accepted only where canonicalization removes it, so the positions it
cannot disappear from are refused at the shape entry point — before the KB is read at all,
by `assert`, `assert-inert` and `check` alike, and an `import!` skips the frame:

| position | refused | because, and instead |
|---|---|---|
| a rule **conclusion**, or a standalone sentence | `:not-well-formed` | belief is a label on a sentex, not on a set of them, so a disjunctive head is a *choice* rather than a derivation — offer the alternatives to a solve with `set/assumptionRule` ([solving.md](solving.md)) |
| an `unknown` / `thereExists` / aggregate body | `:not-well-formed` | each is answered as one closed level-6 query and nothing there unions two runs ([naf.md](naf.md), [aggregate.md](aggregate.md)) — `(unknown (or A B))` is "neither A nor B", so write two `unknown` antecedents; a `thereExists` or an aggregate takes one rule per alternative |
| an `exceptWhen` query | `:not-well-formed` | the conjuncts of one exception all have to hold — but a rule's exceptions block if **any** holds, so a disjunctive exception is two exceptions, one `exceptWhen` per alternative against the same handle ([exceptions.md](exceptions.md)) |
| under `not` | `:not-well-formed` | `(not (or A B))` is "neither A nor B", a conjunction of negations, so expanding on it would store the opposite claim — write the two negations as separate antecedents, or assert each as its own fact |
| an empty `(or)` | `:not-well-formed` | it expands to no rules at all |
| a **goal** | `:shape` | a rule is expanded once at the write entry point; a goal would have to be expanded at every read, and a read normalizes to *one* conjunction that the planner orders once and every engine walks as one ([api.md](api.md)). Run the query once per alternative and concatenate, or put the disjunction in a rule — which *is* expanded — and ask for its conclusion |

An `or` in an **argument** slot is not a connective frame at all and is left where it
stands, exactly as a compound argument is everywhere else: `(likes Tom (or A B))` is one
literal whose second argument happens to be a list. The refusals above read the literal
positions `nm/applied-literals` descends, so the argument stays a term in every rule
position as well: `(likes ?x (or A B))` is accepted under `not` or `unknown` in an
antecedent, and as a conclusion.

## What the shape checks cost

The constructor asks a sentence several questions of the form *does any form in here look
like X* — and for almost every sentence the answer is no. Seven such readings share two
walks, `sentex/some-form` and `forms-where`, which short-circuit on the first hit, and
`check-naf-closed` counts variable occurrences only once something consumes bindings.
Against a `tree-seq` that builds a seq of every form before answering, that is 8–26× on
the individual readings, 13× on a plain one-antecedent rule assert and 25× on a six —
same answers, same depth-first pre-order.

## Result

So rules identical up to **variable names, antecedent order, symmetric or commuting argument
order, and comparison direction** all dedup to one handle — with one carve-out the
hold-back above states: a *deferred* literal and the *recursive* literal keep the
author's relative order, since their position is operational, so two spellings that
differ only in where those sit are two handles by design.

And the folding has an unfolding beside it: a rule whose consequent conjoins or whose
antecedent disjoins is stored as **several** handles, one per conjunct times one per
alternative, each of them canonicalized on its own and each of them deduping against a
twin somebody writes out by hand.

## See also

- [docs/indexing.md](indexing.md) — how the canonical form reaches the trie key.
- [docs/storage.md](storage.md) — the `LiteralSentex` / `RuleSentex` record shapes.
