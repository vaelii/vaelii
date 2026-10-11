# Naming invariants

- **Covers:** the lexical conventions that mark a symbol as predicate, individual, type,
  sense, context or lexeme, and what `assert` refuses for a badly-shaped name; and the
  reserved words — the prose vocabulary the docs and docstrings are held to.
- **Not here:** how a well-formed sentence's structure normalizes to one stored handle →
  [canonicalization.md](canonicalization.md); whether an argument's type (not its
  spelling) is correct → [argtypes.md](argtypes.md).
- **Assumes:** predicate, type, context, sentex → [glossary.md](glossary.md).

`vaelii.impl.naming`. The KB relies on lexical conventions to tell the role of a symbol.

| Role | Convention | Regex (on the symbol name) | Examples |
|------|-----------|----------------------------|----------|
| predicate | camelCase, lowercase-initial, no `_`, **arity 2+** | `[a-z][a-zA-Z0-9]*` | `parentOf`, `genlCx`, `arg` |
| individual | CapitalCamelCase | `[A-Z][A-Za-z0-9]*` (not a context) | `Muffet`, `Tom` |
| type | snake_case, a **unary** predicate | `[a-z][a-z0-9_]*` | `dog`, `physical_object` |
| **sense** | a type, plus the disambiguator saying *which* sense | `[a-z._][…]*-[a-z0-9][…]*` | `abrasive-grit`, `abandonment-romantic` |
| context | `Cx` prefix, then CapitalCamelCase | `Cx[A-Z][A-Za-z0-9]*` | `CxUniverse`, `CxCore` |
| **lexeme** | the `lex` **namespace**; the name is not ours to spell | `(namespace x)` = `"lex"` | `lex/fool's_gold` |

## Notes

- **Types are unary predicates.** Write `(dog Muffet)`, not `(isa Muffet Dog)`.
  `thing` is the root of the `genl` hierarchy.
- **A sense is a type**, and on a KB built by reading text it is the *usual* type: a
  word alone does not say which of its meanings is meant, and `abandonment-romantic`
  and `abandonment-dual` have to be two terms or the hierarchy conflates them. The
  disambiguator follows the **last** dash, because the word may hold one of its own —
  and may *end* in one, which is the case that forces the rule. `a-` is a word (A, then
  the minus), so its sense is `a--musical_note`: the word is `a-`, the disambiguator is
  `musical_note`, and the boundary is the second dash rather than the first. Nothing
  parses that boundary: `sense` and `disambiguation` facts record it, so the shape is
  all a check has to recognise.
- **The word half is snake_case by convention, and nothing enforces it**, because the
  shape that admits `a--musical_note` admits `has-black-feathers` too. There is no
  single-dash rule: the split is the last dash and the word keeps the rest, so a whole
  kebab-case phrase is a well-formed sense. Only the first character of the symbol is
  constrained (`[a-z._]`, since the reader dispatches on it) and the disambiguator,
  which starts alphanumeric and carries no dash and no capital — `a-B`, `foo-` and
  `-foo` are refused, `a-b-c-d` is not.

  **So `physical-object` and `physical_object` are two terms**, and the hierarchy
  holds them apart like any other pair. Nothing unifies them: `genl` relates what it
  is told to relate, and no check compares a sense's word half against the types
  already stored. Write types snake_case and mint a sense only where a word needs
  disambiguating, and the two spellings never meet. This is the same limit stated
  under [What this does not check](#what-this-does-not-check), one step sharper —
  there the two names at least *read* differently, and here they read the same.

  Kebab-case is the spelling a Clojure hand types without thinking, and it is the one
  to unlearn here. Relations still catch it, since a type is unary and
  `(lives-in ?x cold_place)` is refused at arity 2 exactly as `lives_in` is; a *unary*
  `(has-black-feathers Tweety)` is what passes.
- **A lexeme is a surface form**: exactly what a model or a person wrote, before
  anything decided what it means. It is marked by a *namespace* rather than by a
  spelling because its text is unconstrained — apostrophes, dots, dashes, digits — so
  any marker written into the name would collide with the word it marks.
  `fool's_gold` carries an apostrophe of its own. `(namespace x)` cannot collide.
  `lex` is the only namespace that decides a role; `agg/count` and `set/forwardRule`
  are read by their name half exactly as before.
- **The one fence around a lexeme: it names no relation.** A lexeme applied to
  arguments is refused (`:lexeme-functor`). As an *argument* it is ordinary, which is
  what lets `(sense lex/fools_gold fools_gold-mineral)` say what it means — and lets
  `(genl abrasive-grit lex/abrasive_tool)` stand as an unsensified edge until a sense
  is crafted to replace it.
- **A name the reader would not read back is refused.** A leading digit parses as a
  malformed number (`134a-gas`), and a leading `'` is the quote macro, so
  `'centaur'-mythical` parses as a list rather than a term. Both are escaped with a
  leading underscore when minted — `_134a-gas` — which parses and shows the escape.
- **Overlap is expected.** A plain lowercase word (`dog`, `genl`, `likes`)
  satisfies both `predicate?` and `type-symbol?`. Role is disambiguated by
  position and arity, not the symbol alone — `genl` is a predicate in
  `(genl dog animal)`, `dog` is a type in `(dog Muffet)`.
- **Accessors.** `functor`, `args`, `arity` destructure a sentence.

## Enforcement: every literal, and the arity biconditional

`assert` calls `nm/check!` and `check` (docs/api.md, "Validating without writing") calls
`nm/blocking-problems`; both read the KB's policy, and both are `nm/problems` underneath.
It reports, in order: the context's own name, then **every literal's** functor, then
every literal's atomic symbol **arguments**, then any `ist` context slot, then a dotted
rest marker where one cannot appear. That argument step is lexical — is this spelling an
individual, a type or a predicate at all — and not a type check; whether the argument is
of the *right* type is `arg`'s job.

### Literals, wrappers, and arguments

A naming invariant is about a **literal** — a predicate applied to arguments. A
sentence is built from literals plus *wrappers*, and `nm/literals` descends the wrappers
to reach the literals:

| Wrapper | Descends to |
|---------|-------------|
| `(not X)` | `X` |
| `(and X …)` | each conjunct |
| `(or X …)` | nothing, and it never arrives: a disjunctive antecedent is polycanonicalized into one rule per alternative before naming runs, so what this walk sees is the expansion ([canonicalization.md](canonicalization.md)) |
| `(implies A C)` | each antecedent (`:antecedent`), then `C` (`:consequent`) |
| `set/forwardRule` · `backwardRule` · `forwardOnlyRule` · `inertRule` · `defaultRule` · `solveRule` · `assumptionRule` · `hardConstraint` · `softConstraint` | the rule inside, wrappers nesting in any order |
| `(exceptWhen Q R)` | `Q`'s conjuncts (`:exception`), then `R` |
| `(ist Ctx S)` | `S` (and `Ctx` is checked as a context name) |
| `(unknown S)` · `(thereExists ?v S)` · `(exists ?v C)` | the query / consequent wrapped |
| `(bravely S)` · `(cautiously S)` | `S` — a read of the current dilemmas, answered by the `:brave-cautious` prover ([labeling.md](labeling.md)) |
| `(agg/count ?n ?v B)` and its four siblings | `B` — an aggregate's body is a goal, not an argument ([aggregate.md](aggregate.md)) |
| `(sentexHandle N)` | nothing — it names a stored sentex by id |
| `(do/labeling Ctx)` and the rest of `do/` | nothing — an imperative instructs the engine rather than stating that something is true, so it names no relation: it is dispatched at the top level of `assert` and refused anywhere inside a rule ([labeling.md](labeling.md)) |

Two positions are deliberately **not** literals. **Arguments** are never walked: a
compound in argument position is a *term*, and its head names a function or is plain
data — an arithmetic expression `(evaluate ?s (+ 1 2))`, a structural NAT `(QuantityFn 5
Meter)`, a quoted connective `(comment not "…")`. And a **variable in functor
position** is a pattern that names no predicate, so the dotted rest form
`(?pred . ?args)` and a bare `(?p ?x)` pass. A firing binds that variable, and no check
has read the functor it forms, so a rule consequent with a variable functor is checked
again as each conclusion is placed: under `:strict` a conclusion the naming invariants
refuse is dropped and reported as a `:naming` violation (`core/violations`), and under
`:warn` and `:off` it is stored. A **bare variable** in a literal position is a term
where a formula belongs, and `assert` refuses it `:not-well-formed` in every rule role,
the consequent included: `(implies (holds ?x ?s) ?s)` is written `(implies (holds ?x
(?pred . ?args)) (?pred . ?args))`, which binds the functor and the arguments in the
antecedent.

Descending the wrappers is what makes the check reach a rule. A rule's outermost functor
is `implies`, which is engine vocabulary, so a check that stopped there would examine
nothing an author wrote: `(implies (penguin ?x) (lives_in ?x cold_place))` is refused
for its consequent, and a consequent is exactly where derived and generated content
lands.

### The spelling is a biconditional on arity

A functor carrying an underscore satisfies `type-symbol?` and not `predicate?`, so it
names a **type**, and a type is used as a unary predicate. It is therefore legal at
arity 1 and nowhere else. And the converse holds: a camelCase functor — one carrying an
interior capital, which `type-symbol?` refuses — is legal at arity 2 and above and
nowhere else.

```clojure
(physical_object Rock1)              ; fine — a type membership
(warm_blooded Muffet)                ; fine — a unary predicate, spelled like one
(lives_in penguin cold_place)        ; refused — a type name doing a relation's job
(warmBlooded Muffet)                 ; refused — a property wearing a relation's spelling
(livesIn Tweety Antarctica)          ; fine — camelCase at arity 2
```

**Why both directions.** A one-place predicate is not a relation: its extension is a
*set*, not a set of tuples, and a set is what `genl` orders — which is why the taxonomy
exists at all and why its closure is cached rather than derived by a rule. Every
ontology language that reads a role off a name marks that split (OWL's classes against
its properties, Cyc's collections against its predicates); what none of them can do is
mark it in one direction only, because a rule that half-holds is a rule an author
cannot use to *read*. `(warmBlooded Muffet)` under a one-way rule is legal, unremarkable
and wrong, and the KB shipped thirteen of them before this was closed.

**Where the rule stops.** A bare lowercase word (`dog`, `likes`, `alive`) satisfies both
conventions, so arity decides and nothing is refused. That is not a gap to be closed
later: the marker lives on the *interior* of a name, so a name of one word has nowhere
to carry it. Roughly three quarters of the shipped type names are single words and
always will be — the invariant marks multi-word names, and says so.

**The one exemption.** `sentexHandle` stands at arity 1 and is not a predicate: it names
a stored sentex by its id, a term constructor wearing a literal's shape. It states
nothing, so there is no relation to spell either way. `nm/unary-spelling-exempt` is the
roster, and a name earns a place on it only by naming no relation.

### What a rejection says

The `ex-info` `:type` is `:naming`. A repair loop is handed the message verbatim, so
each one names the literal, the wrapper it sits in, and the spelling to use instead:

```
functor lives_in in rule consequent (lives_in ?x cold_place) is snake_case, which
names a unary predicate — a kind or a property — and is legal only at arity 1, but has
2 arguments — write it camelCase as livesIn, or as (lives_in <one argument>)
```

A rejection is **data before it is prose**. `nm/problems*` yields one
`{:class :role :symbol :literal}` map per violation — `:class` one of
`:context-name` `:functor` `:lexeme-functor` `:functor-arity` `:functor-unary` `:argument`
`:ist-context` `:dot-marker` — and `nm/message` renders one; `problems` is the two
composed. `assert` wants the sentence it refused spelled out, but anything *counting*
violations wants to group, and a message embeds the literal, so it is unique per record
and counting messages counts records.

**The throw is a reporting path, so it does not pay for a stack trace nobody prints.** A
checked import counts what the public entry point refuses, which makes the refusal a
hundred
thousand calls in a load rather than an exceptional one — and most of what `ex-info`
costs is materializing the trace so it can elide its own two stack frames, which is a cost
that grows with the depth of the stack it is thrown from where a bare constructor's does
not. `check!` builds the `ExceptionInfo` directly. Same class, same message, same
`:type :naming` ex-data.

### Whose invariants: the two policies

How hard these are enforced is the **KB's** to say, not the build's. `open-kb`'s
`:naming` selects the policy:

| | |
|---|---|
| `:strict` | the default — refuse the assertion, `ex-info` `:type` `:naming` |
| `:warn` | log each one and store anyway (a corpus being cleaned up) |
| `:off` | store in silence (a corpus with spelling conventions of its own) |

It lives on the KB as a plain value, settled when the KB is opened: a store whose policy
moved under it would hold two vocabularies with nothing recording which sentence arrived
under which. So a lenient loader and a strict editor can hold the *same store* at once,
and neither has to win.

No setting moves the role **reading**. `predicate?` and its three siblings answer the
same way under every policy, so `:off` stores a name nothing can classify: `term-role`
returns nil and a `(Type Individual)` goal takes the general path rather than the
shortcut. It never stores a name classified differently. That is the entire cost of
relaxing the policy, and the reason to leave the check on wherever the content is
hand-written.

A **bulk** path is not on that list because it does not consult it: an import builds
records directly through `res/kb-sentex` and never asks, which is what makes a corpus
beyond what the checks accept loadable at all. The checked and bulk paths are reconciled
by a **count** instead. Both import paths fold `nm/tally` as the frames go past — the one cheap moment,
with each record already decoded — and a non-zero result is logged and returned in the
summary as `{:checked n :refused n :by-class {…}}`, one line naming the fraction and the
classes it splits into:

```
this corpus and `assert` disagree: <n> of <total> records (<pct>) hold names `assert`
would refuse: context-name <n>, argument <n>, functor <n>, functor-arity <n>,
dot-marker <n> — they are stored, findable and countable, but re-asserting one throws
under :naming :strict
```

A foreign dialect can disagree at every record — a naming convention the whole corpus was
written under is one the checks refuse uniformly, not occasionally — so the fraction is as
likely to be 100% as it is to be small. The operator who chose the bulk path learns it
then, rather than from a re-assertion that throws a year later. `lein bench-survey naming`
is the same question asked exhaustively: every record, grouped by class, by frame and by
*distinct spelling*, with candidate widenings priced against the corpus.

**The adjacent check answers the same way.** A name is checked *outside* the constructor,
so a record with a refused name still gets built and stored. The **structural** checks —
NAF closure, quantifier locality, the aggregate reduction slots — run *inside* it, so
when one of those fires there is no record at all. An import counts those in `:refused`
(`{:checked n :skipped n :by-type {…}}`), skips the frame, and carries on:

```
<n> of <total> frames (<pct>) hold sentences this build will not construct:
naf-not-closed <n> — they are not stored, and anything resting on one is dropped with it
```

A dump is not a program being written. A rule an older build stored, or another engine's,
can be one a since-widened check refuses, and there is nothing the reading side can do
about it — so the choice is between skipping that frame and abandoning a finished
multi-hour pass over every good frame beside it. Skipping is not repair — the
justifications and meta-sentexes naming a skipped frame fail to resolve and drop with it,
as they already do for any dangling reference — and the summary says what went with it;
what the count buys is that the operator reads the number off a load that finished.

`assert` refuses more than the constructor does, and seven of those refusals would store
a record that answers wrongly. An open literal (`:not-ground`) matches every goal of
its shape. A rule `checks/check-rule-shape` refuses concludes an open literal
(`:not-range-restricted`), runs a `do/` imperative inside the fixpoint
(`:not-assertible`), stores an `or` no expansion removed as one literal
(`:not-well-formed`), or, with a variable antecedent functor (`:not-indexable`), fires
over whatever is stored when a concrete antecedent arrives. A malformed connective frame
(`:not-well-formed`, `sx/connective-problem`, the check `assert` runs) stores a rule whose
`(ist Ctx S)` or bare-variable antecedent matches nothing, a rule whose consequent is a
bare variable, or a `(not A B)` whose record
and index disagree about what it says. A sentex in a query context, or in a context that
is not a symbol (`:shape`), is in no context a read reaches. An import skips each of these
and counts it in `:refused` under that `:type`, the policy the
structural checks take. The rule checks that read the KB (the variable argument
constraints, stratification, a generator's own three) do not run on an import: a
declaration or rule a frame depends on can arrive later in the stream, so the verdict would
depend on frame order. A name stays on the naming policy, stored and counted, because
the record means what it says and a live KB under `:naming :warn` stores it too. An
`exceptWhen` meta-sentex keeps the rule's variables in its query and is exempt from the
ground check. An `(ist Ctx S)` frame is stored as S in Ctx, which is what `assert` stores,
so it is neither skipped nor counted.

The `{:belief? false}` path stores one record per frame. It keeps no `[sentence context]
-> handle` map, since that map would hold every canonical sentence of the corpus in the
heap, so two frames with one canonical form land there as two records. The belief path
(`true` and `:stored`) keeps that map: it lands the second frame on the first one's
handle, keeps the stronger of the two strengths, and counts the frame in `:collapsed`. A
dump `export!` wrote holds no two frames with one canonical form, because the store it
read keeps one record per canonical form. Such a pair reaches an import only from a
hand-edited dump, a dump another dialect or another build wrote, or an `(ist Ctx S)` frame
beside S in Ctx.

A rule frame whose `or` antecedent or `and` consequent `assert` expands
(`rules/expand-rule`) is the exception to one record per frame, on every path: the import
stores it as the rules `assert` stores, one record per form, and counts it in `:expanded`
as `{:frames n :records n}`. A later `assert` of the same rule therefore dedups against
the imported records.

Two edges of the count. Only an `ex-info` carrying a `:type` is counted; an unlabelled
one is **rethrown**, since tolerating an exception nobody chose to raise is how a bug
becomes a statistic. And `check-frame-count!` reads the records-only path's **`:frames`**
— what the stream yielded — rather than its stored count, or a skipped frame would read
as a torn dump.

### What this does not check

This is a check on the **shape** of a name, never on whether the name is worth having.
A *unary* snake_case functor is a well-formed type name, so

```clojure
(implies (penguin ?x) (has_black_and_white_feathers ?x))
```

passes — as would `capable_of_swimming` or
`thermoregulates_via_blubber_and_feathers`. Nothing about a symbol distinguishes a
type the ontology wants from a one-off coined for a single sentence; judging that needs
the KB's existing vocabulary, which is a different question and not one this check asks.
Reading this check as a guard against vocabulary fragmentation is wrong in the expensive
direction.

### Advice: the sentence that breaks no invariant and still means nothing

A shape can be well-formed and still be a mistake, and `assert` says so where it can
name the repair. `(isa Muffet Dog)` breaks nothing — `isa` is a well-formed predicate
and both arguments well-formed individuals — so it stores a two-place relation nothing
reads, and `(isa? kb 'Muffet 'Dog)` then answers false with nothing to search for.
`nm/advice` reads *intent* where `problems` reads the invariants: it recognizes the
shape, and `advise!` logs a `:warn` once per process spelling the rewrite that was
meant. Advice never refuses and never throws — a naming policy of `:off` silences it,
and an argument that is not a symbol yields no advice rather than an exception, since
advice that crashes the `assert` it exists to help is worse than none.

What it proposes:

| Written | Proposed |
|---|---|
| `(isa Muffet Dog)` | `(dog Muffet)` |
| `(isa Muffet WarmBlooded)` | `(warm_blooded Muffet)` — snake_case, not `warmblooded` |
| `(isa Muffet <non-symbol>)` | the generic `(<type> <individual>)` form |

**The table holds one entry.** The bar for adding a second is in `advice`'s own
docstring:
a shape somebody might legitimately mean stays out, because a warning on legitimate
content is a warning an author learns to ignore.

## Reserved words

The lexical rules above are about a **symbol**. These are about a **word**: the prose
vocabulary the docs, the docstrings and the KB comments are held to.

> **One word, one stratum, one field.** Where that is impossible, the glossary carries
> *every* sense as its own entry — and a word with two senses and one entry is a bug.

Four strata, and every noun in the tree names something at exactly one of them. A word
carrying two senses at the same stratum is a defect; one carrying two senses at strata a
reader cannot confuse is a *declared collision*, and the row below is the declaration.

| Stratum | What lives there |
|---------|------------------|
| **term** | expressions that *denote* a thing |
| **formula** | expressions that *assert* something |
| **knowledge** | what the KB *holds* and believes |
| **machine** | how it is *stored and found* |

The formula stratum runs on the standard ladder, and the docs use it exactly:
a **predication** is a predicate applied to terms; a **closed predication** has no free
variable and an **open predication** has one; a **literal** is a predication or its
negation; a **formula** is a predication, a logical operator applied to formulas, or a
quantifier binding variables in one; a **sentence** is a closed formula. So `(P ?x)` is
an open predication and a positive literal and *not* a sentence, while `(P Alice)` is a
closed predication and a positive literal. A possibly-open goal is a **pattern**, never a
sentence. A **wff** is a well-formed formula, one whose every operator has as many
arguments as its arity allows; an **ill-formed** formula is one that is not. A variable is
free unless a quantifier binds it or it sits inside a `(Quote …)`. CxReflection names each
rung as a collection: `predication`, `closed_predication`, `open_predication`, `literal`,
`wff`, `ill_formed`; CxCore names `formula` and `sentence`.

A **qualified compound is a different word.** *Stack frame*, *binding frame*, *keyword
literal*, *string literal*, *character literal* and *regex literal* are ordinary
programming vocabulary, and the qualifier is what tells them from the bare reserved word.
The rule governs `literal` and `frame` standing alone; it does not reach into a compound
that names something else and says so.

`scripts/lint-glossary.sh`'s check 6 reads the table below: every entry it names must
exist in [glossary.md](glossary.md), and the count must match. Adding a second sense of a
word means adding its row here and its entry there, in the same commit.

| Word | Stratum | Senses | Glossary entries |
|------|---------|--------|------------------|
| arm | machine | 1 | Arm |
| asserted | knowledge | 1 | Asserted |
| atomic | term, machine | 2 | Atomic (term); Atomic (storage) |
| belief | knowledge | 2 | Belief; Belief (an agent's) |
| closed predication | formula | 1 | Closed predication |
| constraint | formula, knowledge | 2 | Constraint (rule slot); Constraint network |
| context | knowledge | 4 | Context; Query context; Placement context; context (ontology type) |
| denotational term | term | 1 | Denotational term |
| derived | knowledge | 1 | Derived |
| entry point | machine | 1 | Entry point |
| extent | machine | 1 | Extent |
| formula | formula | 2 | Formula; formula (ontology type) |
| frame | machine | 1 | Frame |
| ground | term | 1 | Ground |
| ill-formed | formula | 1 | ill_formed (ontology type) |
| inert | knowledge | 1 | Inert |
| kind | term | 1 | Kind |
| label | knowledge | 1 | Labeling |
| lane | machine | 1 | Lane |
| literal | formula | 1 | Literal |
| open predication | formula | 1 | Open predication |
| pattern | formula | 1 | Pattern |
| polarity | formula | 1 | Polarity |
| predication | formula | 1 | Predication |
| reasoning | machine | 1 | Reasoning state |
| record | machine | 1 | Record |
| refusal | machine | 1 | Refusal |
| region | knowledge, term | 2 | Region (relabel scope); Region (spatial) |
| roster | machine | 2 | Roster; Term roster |
| sentence | formula | 1 | Sentence |
| sentex | knowledge | 1 | Sentex |
| strength | knowledge | 1 | Strength |
| term | machine | 1 | Term |
| value | term | 1 | Value |
| variable | term | 1 | Variable |
| wff | formula, machine | 2 | wff (ontology type); WFF (well-formedness) |
| wrapper | formula | 1 | Wrapper |

What the check cannot do is notice a *third* sense arriving in prose. That is the
reviewer's job, and the table is where the question gets asked: a word not in it is
free, and a word in it means what its entries say and nothing else.

## Temporaries in tests

`vaelii.test-util/with-terms` infers a temporary's role from the symbol's own shape and
embeds it in the generated name. A `:type` temp keeps the base's spelling: a base
already carrying an underscore (`physical_object`) becomes snake_case
(`tmp_physical_object_17`) and is therefore unary-only, while a bare lowercase word
(`dog`, `likes`) becomes another bare lowercase word (`tmpdog17`) and stays usable at
any arity — as ambiguous as the word the test wrote. Writing the base with an
underscore is how a test says "a type, and only a type".

A `:predicate` temp is **bare lowercase** for the same reason read the other way. Now
that the rule is a biconditional, a camelCase temp would commit to being a relation
exactly as an underscored one commits to being a kind, and a test that wrote
`parentOf` as a base made neither commitment — so the base's capitals are folded out
(`parentOf` ⇒ `tmpparentof17`). A test that wants the arity-1 commitment writes the
base with an underscore and takes a `:type` temp; one that wants arity 2 and above
writes the literal rather than a temp.
