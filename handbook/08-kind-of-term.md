# 8. The kind of term

- **Covers:** choosing whether a new term is an individual, a type, a predicate, a
  function or a context; the spelling that states the choice; why a value that wants a
  hierarchy is not an individual; and when a property is a type.
- **Not here:** what distinguishes a type from its siblings → [ch. 9](09-differentia.md);
  functions and their corresponding predicates → [ch. 22](22-functions.md); contexts →
  [ch. 23](23-contexts.md).
- **Assumes:** [ch. 6](06-definitional-block.md).

Every term plays one role, and in vaelii the role is written into the name. `assert` reads
a symbol's role off its spelling and refuses a sentence that uses a symbol against its
role. Choosing the kind of a term is therefore the first decision a block records, and the
spelling makes the decision visible in every sentence that uses the term.

## Spelling is role

**Practice.** Spell each term for its role:

| role | spelling | examples |
|---|---|---|
| individual | CapitalCamelCase | `Muffet`, `Tweety` |
| type (a unary predicate) | snake_case | `dog`, `electronic_device` |
| predicate (arity 2 or more) | camelCase, lowercase first | `parentOf`, `locatedIn` |
| function | CapitalCamelCase ending in `Fn` | `FatherFn`, `StartFn`, `QuantityFn` |
| context | `Cx` then CapitalCamelCase | `CxUniverse`, `CxBiology` |
| sense | a type, a dash, a lowercase disambiguator | `abrasive-grit` |
| lexeme | the `lex/` namespace | `lex/fool's_gold` |

The individuals are the test-world's, and the sense and the lexeme are illustrations from
[naming.md](../docs/naming.md); the other examples are shipped terms.

Write a membership as the type applied to the individual, `(dog Muffet)`. An underscore
names a type and a type takes one argument; an interior capital names a relation and a
relation takes two or more. A bare lowercase word such as `dog`, `alive` or `likes` fits
both conventions, and its arity decides its role.

**Example.** A membership, a fact relating two individuals, and a declaration typing a
relation's value position (the declaration is life.txt's):

```clojure composed
(dog Muffet)
(livesIn Tweety Antarctica)
(arg birthYearOf 2 integer)
```

*In development:* `birthYearOf` as a predicate of its own, and not as a reading of a full
birth date, is in development. The examples in this handbook use the shipped
`birthYearOf`.

**Why.**

- **Logic.** Arity is part of meaning: a one-place predicate classifies a term, and a
  predicate of two or more places relates terms. The spelling records which one a name
  is, so a reader knows the arity from the name alone.
- **Engine.** The naming check reads every literal of a sentence, a rule's antecedents and
  consequent included, and holds each functor to the biconditional: snake_case at arity 1
  only, camelCase at arity 2 and above only. Under the default `:strict` policy a breach is
  refused with `:type :naming`, and the message names the literal and the spelling to use
  instead. A length binding is held to the spelling too, so `(binary_predicate X)` on a
  snake_case `X` is refused `:length-against-spelling`. A shape that breaks no invariant
  and still means nothing, a membership written as a two-place `isa`, is logged once with
  the rewrite that was meant.
- **Maintenance.** A reader of any sentence sees each term's role, and a role mistake is
  refused at the write instead of surfacing as a query that answers nothing.

**Why not the other ways.** A membership written as a binary relation between an
individual and a capitalized kind name stores a two-place fact that no type reads, so
`isa?` answers false and no error says why. A relation spelled with an underscore, or a
property spelled camelCase at arity 1, is refused outright.

**Audit.** The naming check runs on every write, and `check` runs it without writing:
`(v/check kb '(dog Muffet) 'CxUniverse)`. A reviewer reads each new name in the
change against the table.

## Choosing the kind

**Practice.** Pick the role by what the term denotes:

- an **individual** is one particular thing, which has types and fills argument positions
  and has no instances;
- a **type** is a kind or a one-place property, which has instances and takes `genl` edges;
- a **predicate** relates two or more terms;
- a **function** builds a term that denotes a thing from its arguments, such as the father
  of an animal;
- a **context** is a theory, a setting or a vantage that sentences hold in.

**Example.** life.txt names a role as a function so the KB can name a father before it knows
his name, and states the relation the function corresponds to:

```clojure
(reifiable_function FatherFn)
(functionCorrespondingBinaryPredicate FatherFn fatherOf)
(result FatherFn animal)
```

**Why.** Each role takes a different set of sentences. An individual takes memberships and
fills arguments; `wff` refuses an individual in any position that names a type, read off
its spelling, so it can never take a `genl` edge or a `disjoint`. A type takes `genl`,
separations and argument declarations that name it. A function takes `result`, its own
`arg` declarations and a corresponding predicate. Choosing the role chooses which of these
mechanisms the term can join.

**Audit.** For each new term, the change states which role it has and what it denotes, in
the comment's first sentence.

## nesting values aren't individuals

*If values want a hierarchy, they aren't individuals*

**Practice.** Individuals take no `genl`. When an enumeration of individuals starts to want
an entailment between its members, such as "write access implies read access", the
members were the wrong representation. Make the distinctions predicates, with a predicate
`genl` between them, or types, with a type `genl`.

**Example.** The KB states ordered distinctions as predicates under predicates (abstract.txt,
CxBiology.txt):

```clojure
(genl performedBy doneBy)
(genl properPartOf partOf)
(genl livesIn locatedIn)
```

The same form serves an access hierarchy. With two illustrative binary predicates the KB
does not ship, `hasWriteAccess` and `hasReadAccess`, `(genl hasWriteAccess hasReadAccess)`
makes every write-access tuple a read-access tuple. An ability hierarchy takes the type
form, since the abilities are event kinds: `(genl flying travelling)`.

**Why.**

- **Logic.** "Write implies read" is a subsumption between two distinctions. Subsumption
  holds between predicates or between types, and an individual has no extension for it to
  hold over.
- **Engine.** `wff` refuses an individual on either side of `genl`. A predicate `genl`
  edge places every tuple of the narrower predicate under the broader one, so a query for
  `hasReadAccess` answers the write-access tuples, and the edge between two predicates is
  forced-monotonic: it goes OUT only by retraction. Rules over the broader predicate fire
  on the narrower one's facts.
- **Maintenance.** With the distinctions as individuals, each implication has to be a
  rule, and the rules multiply as access kinds are added. With predicates or types, a new
  kind is one `genl` edge.

**Why not the other ways.** An individual per access kind, related to its holder by one
binary predicate, leaves "admin implies write" with nowhere to live except a hand-written
rule per pair. Denotational functions are the other route, and **don't skip the predicate**
([ch. 22](22-functions.md)) gives each function its corresponding predicates, which then
take the `genl` edges.

**Audit.** For each enumeration of individuals in a change, ask whether any member should
entail another. If one should, the change states the distinctions as predicates or types.

## When a property is a type

**Practice.** A one-place property that a thing has or lacks is a type: a unary predicate,
spelled snake_case or as one lowercase word, with a `genl` to the kind of thing it can be
true of. A property that takes a value is a binary predicate whose second argument is
typed by the value's kind.

**Example.** life.txt places each biology property under the kind it can hold of, and
types the value of a measured property:

```clojure
(genl asleep animal)
(genl alive organism)
(arg birthYearOf 2 integer)
```

**Why.**

- **Logic.** Only a living thing can be alive, and only an animal can be asleep, so each
  property entails the kind.
- **Engine.** A type is any unary predicate, and the engine reads a property exactly as it
  reads a kind. The `genl` makes a misapplied property a clash: a membership of
  `asleep` on a term held `formation` is placed as a nogood, because the property's
  parent is separated from `formation`. Without the `genl`, the property's pairs with the
  kinds below `organism` read `:unknown` in the disjointness audit. A value-bearing
  property typed by its value's kind, such as `integer`, is checked by that kind: a value
  carries its type in its syntax, so the declaration derives no membership, and a fact
  with a value of another kind is stored and held inert, never believed, while
  `try-assert` refuses it.
- **Maintenance.** A property with a parent is placed in the hierarchy like any other type,
  so the audits read it. A kind may sit below a property it always has, and
  [ch. 12](12-identity.md) gives the rule for when it may.

**Why not the other ways.** A property kept free of `genl` edges, on the rule that a
property is not a type, lets the property hold of anything and leaves its relations to the
kinds unknown. A value-bearing property written as one type per value turns each value
into a separate predicate with no order between them.

**Audit.** For each new one-place property, the block states the kind it is true of as its
`genl`. `disjointness-audit` after the change reads its pairs with the kinds it excludes as
`:disjoint`.
