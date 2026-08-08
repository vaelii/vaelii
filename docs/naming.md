# Naming invariants

- **Covers:** the lexical conventions that mark a symbol as predicate, individual, type,
  sense, context or lexeme, and what `assert` refuses for a badly-shaped name.
- **Not here:** how a well-formed sentence's structure normalizes to one stored handle →
  [canonicalization.md](canonicalization.md); whether an argument's type (not its
  spelling) is correct → [argtypes.md](argtypes.md).
- **Assumes:** predicate, type, context, sentex → [glossary.md](glossary.md).

`vaelii.impl.naming`. The KB relies on lexical conventions to tell the role of a symbol.

| Role | Convention | Regex (on the symbol name) | Examples |
|------|-----------|----------------------------|----------|
| predicate | camelCase, lowercase-initial, no `_` | `[a-z][a-zA-Z0-9]*` | `parentOf`, `genl`, `argIsa` |
| individual | CapitalCamelCase | `[A-Z][A-Za-z0-9]*` (not a context) | `Muffet`, `Tom` |
| type | snake_case, a **unary** predicate | `[a-z][a-z0-9_]*` | `dog`, `physical_object` |
| **sense** | a type, plus the disambiguator saying *which* sense | `[a-z._][…]*-[a-z0-9][…]*` | `abrasive-grit`, `abandonment-romantic` |
| context | CapitalCamelCase ending in `Context` | `[A-Z][A-Za-z0-9]*Context` | `UniverseContext`, `CoreContext` |
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
- **A name the reader would not read back is refused.** A leading digit reads as a
  malformed number (`134a-gas`), and a leading `'` is the quote macro, so
  `'centaur'-mythical` reads as a list rather than a term. Both are escaped with a
  leading underscore when minted — `_134a-gas` — which reads and says it was escaped.
- **Overlap is expected.** A plain lowercase word (`dog`, `genl`, `parentOf`)
  satisfies both `predicate?` and `type-symbol?`. Role is disambiguated by
  position and arity, not the symbol alone — `genl` is a predicate in
  `(genl dog animal)`, `dog` is a type in `(dog Muffet)`.
- **Accessors.** `functor`, `args`, `arity` destructure a sentence.

## Enforcement: every literal, and snake_case is unary

`assert` calls `nm/check!` and `check` (docs/api.md, "Validating without writing") calls
`nm/blocking-problems`; both read the KB's policy, and both are `nm/problems` underneath.
It reports, in order: the context's own name, then **every literal's** functor, then
every literal's atomic symbol **arguments**, then any `ist` context slot, then a dotted
rest marker where one cannot appear. That argument step is lexical — is this spelling an
individual, a type or a predicate at all — and not a type check; whether the argument is
of the *right* type is `argIsa`'s job.

### Literals, frames, and arguments

A naming invariant is about a **literal** — a predicate applied to arguments. A
sentence is built from literals plus *frames*, and `nm/literals` descends the frames
to reach the literals:

| Frame | Descends to |
|-------|-------------|
| `(not X)` | `X` |
| `(and X …)` | each conjunct |
| `(implies A C)` | each antecedent (`:antecedent`), then `C` (`:consequent`) |
| `set/forwardRule` · `backwardRule` · `inertRule` · `defaultRule` · `assumptionRule` · `hardConstraint` · `softConstraint` | the rule inside, wrappers nesting in any order |
| `(exceptWhen Q R)` | `Q`'s conjuncts (`:exception`), then `R` |
| `(ist Ctx S)` | `S` (and `Ctx` is checked as a context name) |
| `(unknown S)` · `(thereExists ?v S)` · `(exists ?v C)` | the query / consequent framed |
| `(agg/count ?n ?v B)` and its four siblings | `B` — an aggregate's body is a goal, not an argument ([aggregate.md](aggregate.md)) |
| `(sentexHandle N)` | nothing — it names a stored sentex by id |

Two positions are deliberately **not** literals. **Arguments** are never walked: a
compound in argument position is a *term*, and its head names a function or is plain
data — an arithmetic expression `(evaluate ?s (+ 1 2))`, a structural NAT `(QuantityFn 5
Meter)`, a quoted connective `(comment not "…")`. And a **variable in functor
position** is a pattern that names no predicate, so the dotted rest form
`(?pred . ?args)` and a bare `(?p ?x)` pass.

Descending the frames is what makes the check reach a rule. A rule's outermost functor
is `implies`, which is engine vocabulary, so a check that stopped there would examine
nothing an author wrote: `(implies (penguin ?x) (lives_in ?x cold_place))` is refused
for its consequent, and a consequent is exactly where derived and generated content
lands.

### snake_case is a type name, hence unary

A functor carrying an underscore satisfies `type-symbol?` and not `predicate?`, so it
names a **type**, and a type is used as a unary predicate. It is therefore legal at
arity 1 and nowhere else:

```clojure
(physical_object Rock1)              ; fine — a type membership
(lives_in penguin cold_place)        ; refused — a type name doing a relation's job
(livesIn Tweety Antarctica)          ; fine — camelCase, unconstrained in arity
```

A bare lowercase word (`dog`, `likes`) is both, so arity decides and nothing is
refused.

### What a rejection says

The `ex-info` `:type` is `:naming`. A repair loop is handed the message verbatim, so
each one names the literal, the frame it sits in, and the spelling to use instead:

```
functor lives_in in rule consequent (lives_in ?x cold_place) is snake_case, which
names a type and is legal only as a unary predicate, but has 2 arguments — write it
camelCase as livesIn, or as (lives_in <one argument>)
```

A rejection is **data before it is prose**. `nm/problems*` yields one
`{:class :role :symbol :literal}` map per violation — `:class` one of
`:context-name` `:functor` `:lexeme-functor` `:functor-arity` `:argument`
`:ist-context` `:dot-marker` — and `nm/message` renders one; `problems` is the two
composed. `assert` wants the sentence it refused spelled out, but anything *counting*
violations wants to group, and a message embeds the literal, so it is unique per record
and counting messages counts records.

### Whose invariants: the two doors

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

`:constraints` is the other door of the same kind, over what a **definitional clash**
does rather than over how a symbol is spelled — `:refuse` or `:arbitrate`, on the KB as a
plain value for the same reason ([nmtms.md](nmtms.md), "Which door the content came through").

What no setting moves is the role **reading**. `predicate?` and its three siblings answer
the same way under every policy, so `:off` stores a name nothing can classify — `term-role`
says nil, a `(Type Individual)` goal takes the general path rather than the shortcut —
never one classified differently. That is the entire cost of opening the door, and it is
why the check is worth keeping on wherever the content is hand-written.

A **bulk** path is not on that list because it does not consult it: an import builds
records directly through `res/kb-sentex` and never asks, which is what makes a corpus
of this size loadable at all. The two doors are reconciled by a **count** instead.
Both import paths fold `nm/tally` as the frames go past — the one cheap moment, with each
record already decoded — and a non-zero result is logged and returned in the summary as
`{:checked n :refused n :by-class {…}}`:

(The figures below are from an 11.3M-record corpus in another engine's dialect — not
the 1.18M-sentex OpenCyc conversion the rest of the docs measure.)

```
this corpus and `assert` disagree: 11,314,049 of 11,314,049 records (100.0%) hold names
`assert` would refuse: context-name 11,314,049, argument 10,059,528, functor 395,259,
functor-arity 58, dot-marker 9 — they are stored, findable and countable, but
re-asserting one throws under :naming :strict
```

The operator who chose the bulk path learns the fraction then, rather than from a
re-assertion that throws a year later. `lein bench-survey naming` is the same question
asked exhaustively — every record, grouped by class, by frame and by *distinct spelling*,
with candidate widenings priced against the corpus.

### What this does not check

This is a check on the **shape** of a name, never on whether the name is worth having.
A *unary* snake_case functor is a well-formed type name, so

```clojure
(implies (penguin ?x) (has_black_and_white_feathers ?x))
```

passes — as would `capable_of_swimming` or
`thermoregulates_via_blubber_and_feathers`. Nothing about a symbol distinguishes a
type the ontology wants from a one-off coined for a single sentence; judging that needs
the KB's existing vocabulary, which is a different question asked in
[llm.md](llm.md#vocabulary-fragmentation-and-the-two-guards-against-it). Reading
this check as a guard against vocabulary fragmentation is wrong in the expensive
direction.

### Advice: the sentence that breaks no invariant and still means nothing

A shape can be well-formed and still be a mistake, and the front door says so where it
can name the repair. `(isa Muffet Dog)` breaks nothing — `isa` is a well-formed predicate
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
| `(isa Muffet PhysicalObject)` | `(physical_object Muffet)` — snake_case, not `physicalobject` |
| `(isa Muffet <non-symbol>)` | the generic `(<type> <individual>)` form |

**One entry, deliberately.** The bar for adding a second is in `advice`'s own docstring:
a shape somebody might legitimately mean stays out, because a warning on legitimate
content is a warning an author learns to ignore.

## Temporaries in tests

`vaelii.test-util/with-terms` infers a temporary's role from the symbol's own shape and
embeds it in the generated name. A `:type` temp keeps the base's spelling: a base
already carrying an underscore (`physical_object`) becomes snake_case
(`tmp_physical_object_17`) and is therefore unary-only, while a bare lowercase word
(`dog`, `likes`) becomes another bare lowercase word (`tmpdog17`) and stays usable at
any arity — as ambiguous as the word the test wrote. Writing the base with an
underscore is how a test says "a type, and only a type".
