# Naming invariants

- **Covers:** the lexical conventions that mark a symbol as predicate, individual, type,
  sense, context or lexeme, and what `assert` refuses for a badly-shaped name; and the
  reserved words — the prose vocabulary the docs and docstrings are held to.
- **Not here:** how a well-formed sentence's structure normalizes to one stored handle →
  [canonicalization.md](canonicalization.md); whether an argument's type (not its
  spelling) is correct → [argtypes.md](argtypes.md).
- **Assumes:** predicate, type, context, sentex → [glossary.md](glossary.md).

`vaelii.impl.naming` reads a symbol's role off its spelling alone. No role predicate
consults belief, the stored content or the KB's naming policy.

| Role | Convention | Regex (on the symbol name) | Examples |
|------|-----------|----------------------------|----------|
| predicate | camelCase, lowercase-initial, no `_`, **arity 2+** | `[a-z][a-zA-Z0-9]*` | `parentOf`, `genlCx`, `arg` |
| individual | CapitalCamelCase | `[A-Z][A-Za-z0-9]*` (not a context) | `Muffet`, `Tom` |
| function | an individual's spelling ending in `Fn` | `[A-Z][A-Za-z0-9]*Fn` (not a context) | `FatherFn`, `QuantityFn` |
| type | snake_case, a **unary** predicate | `[a-z][a-z0-9_]*` | `dog`, `physical_object` |
| **sense** | a type, plus the disambiguator saying *which* sense | `[a-z._][…]*-[a-z0-9][…]*` | `abrasive-grit`, `abandonment-romantic` |
| context | `Cx` prefix, then CapitalCamelCase; or the `cx` **namespace** | `Cx[A-Z][A-Za-z0-9]*`, or `(namespace x)` = `"cx"` | `CxUniverse`, `CxWell`, a reified context ([context-nat.md](context-nat.md)) |
| **lexeme** | the `lex` **namespace**; the name is not ours to spell | `(namespace x)` = `"lex"` | `lex/fool's_gold` |

## Notes

- **Types are unary predicates.** Write `(dog Muffet)`, not `(isa Muffet Dog)`.
  `thing` is the root of the `genl` hierarchy.
- **A sense is a type**, and on a KB built by reading text it is the usual type: a word
  alone does not say which of its meanings is meant, so `abandonment-romantic` and
  `abandonment-dual` are two terms. The disambiguator follows the **last** dash, because
  the word may hold a dash of its own and may end in one: `a-` is a word, so its sense is
  `a--musical_note`, with the word `a-` and the disambiguator `musical_note`. No check
  parses that boundary; `sense` and `disambiguation` facts record it, and the check
  recognizes the shape only.
- **The word half is snake_case by convention, and no check enforces it.** The split is
  the last dash and the word keeps the rest, so a whole kebab-case phrase is a well-formed
  sense. The first character of the symbol is `[a-z._]`, because the reader dispatches on
  it; the word half admits no capital; the disambiguator starts alphanumeric and carries
  no dash and no capital. `a-B`, `fooBar-baz`, `foo-` and `-foo` are refused, and
  `a-b-c-d` is not.

  **So `physical-object` and `physical_object` are two terms**, and the hierarchy holds
  them apart like any other pair. No check compares a sense's word half against the types
  already stored ([What this does not check](#what-this-does-not-check)). Write types
  snake_case and mint a sense only where a word needs disambiguating, and the two
  spellings never meet. A relation spelled kebab-case is refused at arity 2,
  `(lives-in ?x cold_place)` exactly as `lives_in`; a unary `(has-black-feathers Tweety)`
  passes.
- **A lexeme is a surface form**: what a model or a person wrote, before anything decided
  what it means. Its text is unconstrained (apostrophes, dots, dashes, digits), so a
  namespace marks it: a marker written into the name would collide with the word, as
  `fool's_gold` carries an apostrophe of its own. `lex` and `cx` are the two namespaces
  that decide a role; `agg/count` and `set/forwardRule` are read by their name half.
- **A lexeme names no relation.** A lexeme applied to arguments is refused
  (`:lexeme-functor`). As an *argument* it is ordinary, so `(sense lex/fools_gold
  fools_gold-mineral)` states what it means, and `(genl abrasive-grit lex/abrasive_tool)`
  stands as an unsensified edge until a sense replaces it.
- **A name the reader would not read back is refused.** A leading digit parses as a
  malformed number (`134a-gas`), and a leading `'` is the quote macro, so
  `'centaur'-mythical` parses as a list. A mint escapes either with a leading underscore,
  `_134a-gas`, which parses.
- **Overlap is expected.** A plain lowercase word (`dog`, `genl`, `likes`) satisfies both
  `predicate?` and `type-symbol?`, and position and arity decide its role: `genl` is a
  predicate in `(genl dog animal)`, `dog` a type in `(dog Muffet)`.
- **A function is an individual by spelling as well.** `individual?` answers true for
  `FatherFn`, and `function-spelled?` is read only where a position names a relation that
  may be a function, the commutativity marks
  ([taxonomy.md](taxonomy.md#well-formedness-vaeliiimplwff)).
- **Accessors.** `functor`, `args`, `arity` destructure a sentence.

## Enforcement: every literal, and the arity biconditional

`assert` calls `nm/check!` and `check` (docs/api.md, "Validating without writing") calls
`nm/blocking-problems`; both read the KB's policy, and both are `nm/problems` underneath.
It reports, in order: the context's own name, then **every literal's** functor, then
every literal's atomic symbol **arguments**, then any `ist` context slot. A `.` is not
a name: a `.` outside a rest marker is refused as `:shape` before this check runs
([inference.md](inference.md#dotted-rest-patterns)). The argument step is lexical: it asks
whether a spelling is an individual, a type or a predicate at all. Whether the argument is of the
*right* type is `arg`'s job.

### Literals, wrappers, and arguments

A naming invariant is about a **literal**, a predicate applied to arguments. A sentence
is built from literals plus *wrappers*, and `nm/literals` descends the wrappers to reach
the literals:

| Wrapper | Descends to |
|---------|-------------|
| `(not X)` | `X` |
| `(and X …)` | each conjunct |
| `(or X …)` | nothing. A disjunctive antecedent is polycanonicalized into one rule per alternative before naming runs, so the walk sees the expansion. Every other connective `or`, `(not (or …))` included, is refused before naming runs ([canonicalization.md](canonicalization.md#where-or-cannot-go)) |
| `(implies A C)` | each antecedent (`:antecedent`), then `C` (`:consequent`); a rule in consequent position is a generator's generated rule, whose literals read `:generated-antecedent` and `:generated-consequent` at every depth ([generators.md](generators.md)) |
| `set/forwardRule` · `backwardRule` · `forwardOnlyRule` · `lazyForwardRule` · `inertRule` · `defaultRule` · `solveRule` · `assumptionRule` · `hardConstraint` · `softConstraint` | the rule inside, wrappers nesting in any order |
| `(exceptWhen Q R)` | `Q`'s conjuncts (`:exception`), then `R` |
| `(ist Ctx S)` | `S` (and `Ctx` is checked as a context name) |
| `(unknown S)` · `(thereExists ?v S)` · `(exists ?v C)` | the query / consequent wrapped |
| `(forall ?v (implies B H))` | each conjunct of `B`, then `H`, in the role the `forall` holds: the nested query the `forall` desugars to ([naf.md](naf.md)) |
| `(bravely S)` · `(cautiously S)` | `S` — a read of the current dilemmas, answered by the `:brave-cautious` prover ([labeling.md](labeling.md)) |
| `(agg/count ?n ?v B)` and its four siblings | `B` — an aggregate's body is a goal, not an argument ([aggregate.md](aggregate.md)) |
| `(sentexHandle N)` | nothing — it names a stored sentex by id |
| `(do/labeling Ctx)` and the rest of `do/` | nothing — an imperative instructs the engine and names no relation: it is dispatched at the top level of `assert` and refused anywhere inside a rule ([labeling.md](labeling.md)) |

Two positions are **not** literals. **Arguments** are never walked: a compound in
argument position is a *term*, and its head names a function or is plain data, as in an
arithmetic expression `(evaluate ?s (+ 1 2))`, a structural NAT `(QuantityFn 5 Meter)` or
a quoted connective `(comment not "…")`. And a **variable in functor position** is a
pattern that names no predicate, so the dotted rest form `(?pred . ?args)` and a bare
`(?p ?x)` pass. A firing binds that variable, so a rule consequent with a variable functor
is checked again as each conclusion is placed: under `:strict` a conclusion the naming
invariants refuse is dropped and reported as a `:naming` violation (`core/violations`),
and under `:warn` and `:off` it is stored. A **bare variable** in a literal position is a
term where a formula belongs, and `assert` refuses it `:not-well-formed` in every rule
role, the consequent included: `(implies (holds ?x ?s) ?s)` is written `(implies (holds
?x (?pred . ?args)) (?pred . ?args))`, which binds the functor and the arguments in the
antecedent.

A rule's outermost functor is `implies`, which is engine vocabulary, so the descent is
what reaches the author's names: `(implies (penguin ?x) (lives_in ?x cold_place))` is
refused for its consequent, the position where derived and generated content lands.

### The spelling is a biconditional on arity

A functor carrying an underscore satisfies `type-symbol?` and not `predicate?`, so it
names a **type**, and a type is a unary predicate: it is legal at arity 1 and nowhere
else. The converse holds: a camelCase functor, one carrying an interior capital, which
`type-symbol?` refuses, is legal at arity 2 and above and nowhere else.

```clojure
(physical_object Rock1)              ; fine — a type membership
(warm_blooded Muffet)                ; fine — a unary predicate, spelled like one
(lives_in penguin cold_place)        ; refused — a type name doing a relation's job
(warmBlooded Muffet)                 ; refused — a property wearing a relation's spelling
(livesIn Tweety Antarctica)          ; fine — camelCase at arity 2
```

Why both directions: [defenses.md](defenses.md#the-spelling-convention-is-a-biconditional-on-arity-not-a-one-way-rule).

**Where the rule stops.** A bare lowercase word (`dog`, `likes`, `alive`) satisfies both
conventions, so arity decides and nothing is refused. The marker sits in the interior of
a name, so a one-word name has nowhere to carry it, and the invariant marks multi-word
names only.

**The one exemption.** `sentexHandle` stands at arity 1 and is not a predicate: it names
a stored sentex by its id, a term constructor with a literal's shape, and states nothing.
`nm/unary-spelling-exempt` is the list, and a name belongs on it only if it names no
relation.

### A length binding is held to the spelling

A length binding (`arity`, `arityMin`, an exact-arity class membership such as
`binary_predicate`) states the lengths a relation takes, so `assert` holds it to the
same biconditional: it refuses a binding that admits no length the bound term's spelling
allows. `nm/length-class` answers both questions, for a literal's own length and for a
binding's.

```clojure
(binary_predicate warm_blooded)      ; refused — a type bound to two arguments
(arityMin warm_blooded 2)            ; refused — no length of one is left
(arity livesIn 1)                    ; refused — camelCase bound to one argument
(arityMin livesIn 1)                 ; fine — two and more are admitted
(binary_predicate likes)             ; fine — a bare word takes any length
(unary_predicate nat/a0IQuAcmzmTCb)  ; fine — a reified constant states no role
```

A reified constant (`nm/reified-constant?`, a `nat/` or `cx/` symbol) is held to no
length, as a binding or as a literal's functor: the engine mints its name, and a mint
of a function whose `result` is a unary class asserts `(unary_predicate nat/K)`
([nat.md](nat.md)).

The refusal is `:length-against-spelling`, carrying `:relation`, `:class`
(`:functor-arity` or `:functor-unary`) and `:binding` (`{:exact n}` or `{:min m}`). It
follows the `:naming` policy below: `:warn` logs and stores, `:off` stores. An engine
grammar term is held to its `:shape` instead, whatever the policy
([taxonomy.md](taxonomy.md#arity)).

### What a rejection says

The `ex-info` `:type` is `:naming`. A repair loop is handed the message verbatim, so
each one names the literal, the wrapper it sits in, and the spelling to use instead:

```
functor lives_in in rule consequent (lives_in ?x cold_place) is snake_case, which
names a unary predicate — a kind or a property — and is legal only at arity 1, but has
2 arguments — write it camelCase as livesIn, or as (lives_in <one argument>)
```

A rejection is **data before it is prose**. `nm/problems*` yields one
`{:class :role :symbol :literal}` map per violation, with `:class` one of
`:context-name` `:functor` `:lexeme-functor` `:functor-arity` `:functor-unary` `:argument`
`:ist-context`, and `nm/message` renders one; `problems` is the two
composed. `assert` spells out the sentence it refused, and a caller counting violations
groups by class: a message embeds the literal, so it is unique per record.

`check!` builds the `ExceptionInfo` with its constructor rather than `ex-info`, with the
same class, message and `:type :naming` ex-data
([defenses.md](defenses.md#a-naming-refusal-skips-ex-info)).

### Whose invariants: the two policies

The **KB** sets how hard these are enforced, not the build. `open-kb`'s `:naming` selects
the policy:

| | |
|---|---|
| `:strict` | the default — refuse the assertion, `ex-info` `:type` `:naming` |
| `:warn` | log each one and store anyway (a corpus being cleaned up) |
| `:off` | store in silence (a corpus with spelling conventions of its own) |

The policy is a plain value on the KB, fixed when the KB is opened, so the store records
no per-sentence policy. A lenient loader and a strict editor can hold the *same store* at
once.

No setting moves the role **reading**. `predicate?` and its three siblings answer the
same way under every policy, so `:off` stores a name no role predicate accepts:
`term-role` returns nil and a `(Type Individual)` goal takes the general path rather than
the shortcut. `:off` never stores a name classified differently.

A **bulk** path does not consult the policy: an import builds records directly through
`res/kb-sentex`, so a corpus the checks refuse is loadable. A **count** reconciles the
checked and bulk paths instead. Both import paths fold `nm/tally` over the frames as they
are decoded, and a non-zero result is logged and returned in the summary as
`{:checked n :refused n :by-class {…}}`, one line naming the fraction and its classes:

```
this corpus and `assert` disagree: <n> of <total> records (<pct>) hold names `assert`
would refuse: context-name <n>, argument <n>, functor <n>, functor-arity <n>
— they are stored, findable and countable, but re-asserting one throws
under :naming :strict
```

A corpus written under a foreign naming convention can disagree at every record, so the
fraction can be 100%. The operator who chose the bulk path reads it off the load.
`lein bench-survey naming` asks the same question exhaustively: every record, grouped by
class, by frame and by *distinct spelling*, with candidate widenings priced against the
corpus.

**The structural checks answer the same way.** A name is checked *outside* the record
constructor, so a record with a refused name is still built and stored. The **structural**
checks (NAF closure, quantifier locality, the aggregate reduction slots) run *inside* it,
so when one of those fires there is no record at all. An import counts those in
`:refused` (`{:checked n :skipped n :by-type {…}}`), skips the frame, and carries on:

```
<n> of <total> frames (<pct>) hold sentences this build will not construct:
naf-not-closed <n> — they are not stored, and anything resting on one is dropped with it
```

A dump can hold a rule an older build or another engine stored and a since-widened check
refuses, and the reading side cannot repair it. The import skips that frame rather than
abandoning a multi-hour pass over every good frame beside it. The justifications and
meta-sentexes naming a skipped frame fail to resolve and drop with it, as they do for any
dangling reference, and the summary counts what went.

`assert` refuses more than the constructor does, and nine of those refusals would store
a record that answers wrongly. An open literal (`:not-ground`) matches every goal of
its shape. A rule `checks/check-rule-shape` refuses concludes an open literal
(`:not-range-restricted`), runs a `do/` imperative inside the fixpoint
(`:not-assertible`), stores an `or` no expansion removed as one literal
(`:not-well-formed`), or, with a variable antecedent functor (`:not-indexable`), fires
over whatever is stored when a concrete antecedent arrives. A malformed connective form
(`:not-well-formed`, `sx/connective-problem`, the check `assert` runs) stores a rule whose
`(ist Ctx S)` or bare-variable antecedent matches nothing, a rule whose consequent is a
bare variable, a `(not A B)` whose record and index disagree about what it says, or an
`or` or `(not (or …))` fact as one literal whose functor names no predicate. A special
predicate's declaration in a shape its `:wff` arm refuses (`:not-well-formed`,
`special/wff-problems`) puts an individual or a self-loop into the taxonomy, or an `arg`
position that is not an integer into the argument constraints. A non-finite measure
magnitude (`:not-well-formed`, `checks/term-shape-problem`) throws out of every
duration and metric goal in its context, and a `MapFn` term giving one key two values
(the same check) makes `valueAt` answer both. An inline `exceptWhen` over a fact
(`:not-well-formed`, `rules/exceptWhen-not-a-rule`) qualifies nothing a rule concludes. A sentex in a query context, or in a context
that is not a symbol (`:shape`), is in no context a read reaches. An import skips each of
these and counts it in `:refused` under that `:type`, as it does for the structural
checks. The checks that read the KB do not run on an import: the rule checks (the
variable argument constraints, stratification, a generator's own three) and the `:wff`
arms' `genl`, `genlCx`, cover and `rewriteOf` cycle checks and the transitivity a
`transitiveInArg` names. A declaration or rule a frame depends on can arrive later in the
stream, so the verdict would depend on frame order. A name stays on the naming policy,
stored and counted, because the record means what it says and a live KB under
`:naming :warn` stores it too. An `exceptWhen` meta-sentex keeps the rule's variables in
its query and is exempt from the ground check. An `(ist Ctx S)` frame is stored as S in Ctx, which is what
`assert` stores, so it is neither skipped nor counted.

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

The count has two edges. Only an `ex-info` carrying a `:type` is counted; an unlabelled
one is **rethrown**, so an exception nobody chose to raise stops the load. And
`check-frame-count!` reads the records-only path's **`:frames`**, what the stream yielded,
rather than its stored count, or a skipped frame would read as a torn dump.

### What this does not check

This is a check on the **shape** of a name, never on whether the name is worth having.
A *unary* snake_case functor is a well-formed type name, so

```clojure
(implies (penguin ?x) (has_black_and_white_feathers ?x))
```

passes, as would `capable_of_swimming` or `thermoregulates_via_blubber_and_feathers`. No
property of a symbol distinguishes a type the ontology wants from a one-off coined for a
single sentence; judging that needs the KB's existing vocabulary, which this check does
not read. It is no guard against vocabulary fragmentation.

### Advice: the sentence that breaks no invariant and still means nothing

A shape can be well-formed and still be a mistake, and `assert` says so where it can
name the repair. `(isa Muffet Dog)` breaks nothing (`isa` is a well-formed predicate and
both arguments well-formed individuals), so it stores a two-place relation nothing reads,
and `(isa? kb 'Muffet 'Dog)` then answers false with no error to search for. `nm/advice`
recognizes the shape, and `advise!` logs a `:warn` once per process spelling the rewrite
that was meant. Advice never refuses and never throws: a naming policy of `:off` silences
it, and an argument that is not a symbol gets the generic rewrite rather than an
exception.

What it proposes:

| Written | Proposed |
|---|---|
| `(isa Muffet Dog)` | `(dog Muffet)` |
| `(isa Muffet WarmBlooded)` | `(warm_blooded Muffet)` — snake_case, not `warmblooded` |
| `(isa Muffet <non-symbol>)` | the generic `(<type> <individual>)` form |

**The table holds one entry.** The bar for adding a second is in `advice`'s docstring: a
shape somebody might legitimately mean stays out.

## Reserved words

The lexical rules above are about a **symbol**. These are about a **word**: the prose
vocabulary the docs, the docstrings and the KB comments are held to.

Every noun in the tree names something at exactly one of four strata. A word carrying two
senses at the same stratum is a defect. A word carrying two senses at strata a reader
cannot confuse is a *declared collision*: its row below declares it, and the glossary
carries each sense as its own entry.

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
free unless a quantifier binds it or it sits inside a `(Quote …)`. `reflection.txt` names each
rung as a collection: `predication`, `closed_predication`, `open_predication`, `literal`,
`wff`, `ill_formed`; `core.txt` names `formula` and `sentence`.

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
| sentence | formula | 1 | Sentence |
| sentex | knowledge | 1 | Sentex |
| strength | knowledge | 1 | Strength |
| term | machine | 1 | Term |
| value | term | 1 | Value |
| variable | term | 1 | Variable |
| view | knowledge | 1 | View |
| wff | formula, machine | 2 | wff (ontology type); WFF (well-formedness) |
| wrapper | formula | 1 | Wrapper |

The check cannot notice a *third* sense arriving in prose; review catches that. A word
not in the table is free, and a word in it means what its entries say and nothing else.

## Temporaries in tests

`vaelii.test-util/with-terms` infers a temporary's role from the symbol's own shape and
embeds the symbol in the generated name. A `:type` temp keeps the base's spelling: a base
carrying an underscore (`physical_object`) becomes snake_case
(`tmp_physical_object_17`) and is unary-only, while a bare lowercase word (`dog`,
`likes`) becomes another bare lowercase word (`tmpdog17`) and stays usable at any arity.
Writing the base with an underscore is how a test says "a type, and only a type".

A `:predicate` temp is **bare lowercase**, since the biconditional would commit a
camelCase temp to arity 2 and above: the base's capitals are folded out (`parentOf` ⇒
`tmpparentof17`). A test that wants the arity-1 commitment writes the base with an
underscore and takes a `:type` temp; one that wants arity 2 and above writes the literal
rather than a temp.

A `:function` temp keeps the `Fn` ending after the gensym (`PairFn` ⇒ `TmpPair17Fn`), so it
stays `function-spelled?`.
