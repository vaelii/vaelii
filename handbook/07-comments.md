# 7. Comments

- **Covers:** what a term's `comment` says; where a reference to another term goes; and the
  example annotations, quoted and string, that sit beside a comment.
- **Not here:** stating the comment's sentences as rules → [ch. 2](02-representation.md);
  leaving structure to the assertions → [ch. 4](04-economy.md); the differentia a comment
  states → [ch. 9](09-differentia.md).
- **Assumes:** [ch. 6](06-definitional-block.md).

A `comment` is an ordinary sentex: `(comment ?term ?text)` is stored in a context, queried,
justified and retracted like any fact, so the KB documents itself in its own
representation. Its text is a string, so no inference reads it. A comment is therefore for
the reader, and it has one job: to say what the term means where the assertions cannot.

## meaning, not name

*Comments state the meaning, not the term again*

**specPrinciple:** references in seeAlso

**Practice.** Say what membership in a type, or the relation a predicate names, means.
Give examples, including the hard ones: the case that sits on the boundary, and the case
a reader would get wrong. Write a relation's comment as a signature followed by a
definition in the signature's variables, `(eats ?animal ?food) means that …`. Keep what the
engine does with the term in an `implementationNote`, not in the comment.

**Example.** abstract.txt's `hollow` says what a member is, names the cases that test the
boundary, and says what the type is not about:

```clojure
(comment hollow "Has, at that time, an interior space that other things can occupy. A thing can stop being hollow and still exist: a box crushed flat stops being hollow, and a hand is hollow only while it is cupped. What a thing is shaped like, not what it is for, and a container is made to be hollow. Spatiotemporal rather than tangible, since a cave is a space in rock and is made of nothing.")
(positiveExampleComment hollow "a cupped hand")
(negativeExampleComment hollow "an empty clenched fist")
```

A relation's comment opens with its signature (abstract.txt):

```clojure
(comment input "(input ?happening ?thing) means that ?thing went into ?happening. An instrument the happening used and left unchanged is not an input.")
```

**Why.**

- **Logic.** The comment is the reference a reader uses to decide whether a new case is a
  member. A comment that restates the name decides no case, and a comment that names the
  hard cases decides the ones where readers would disagree.
- **Engine.** The gloss composer reads comments. For a relation, it takes the comment's
  first clause and substitutes the actual arguments for the signature's variables, so
  `(input Smelting1 Ore1)` glosses from the `input` comment with no hand-written pattern,
  and a comment edited to say something else changes the gloss with it. A type's gloss
  states the membership and uses the comment as the apposition after it. A comment that only
  restates the name adds nothing to either gloss, and a term with no comment glosses as its
  bare name. `describe` returns the comment strings under `:comment`.
- **Maintenance.** The hard examples are where the next reviewer would reopen a decision.
  Writing them into the comment records the decision with the term, in the context the
  term is defined in.

**Why not the other ways.**

- **A comment that restates the name.** A comment that repeats the term's name in other
  words tells a reader nothing the symbol did not.
- **A comment that restates the structure.** A clause such as "the complement of X" or
  "with Y it partitions Z" repeats a `partition` or a `genl` the KB already states, and
  goes stale when that assertion changes (**state it once**, [ch. 4](04-economy.md)).
- **A comment that describes the implementation.** core.txt's comment on
  `implementationNote` draws the line: a comment says what a term means, a note says how
  the meaning is carried out, and a note can go stale when the engine changes where a
  comment cannot.

**Audit.** For each new comment, check that each sentence says what membership or the
relation means, gives an example, or names a hard case. Delete each clause an assertion
already states, and move each sentence about the engine into an `implementationNote`.
`(v/ask kb '(comment hollow ?text) 'CxUniverse)` reads a comment back.

## references in seeAlso

*References go in seeAlso/termsRelated, not comment prose*

**genlPrinciple:** meaning, not name

**Practice.** State a pointer from one term to another as `seeAlso`, which is directional,
or `termsRelated`, which groups a symmetric cluster of two or more terms. The comment says
what the term means. A term named in a comment because it is part of the meaning ("a
container is one kind of made hollow thing") stays in the comment.

**Example.** Shipped cross-references (abstract.txt, core.txt):

```clojure
(termsRelated input output)
(termsRelated genl disjoint orthogonal)
(seeAlso sibling_disjoint genl)
(termsRelated positiveExample negativeExample borderlineExample)
```

**Why.**

- **Logic.** A reference is a relation between two terms. Stated as a sentence, it has
  arguments a reader and a query can both use. Written as prose, it is a word inside a
  string.
- **Engine.** `seeAlso` and `termsRelated` are stored and never read for inference: core.txt
  classifies both as documentation, so nothing derives from them. They are still sentexes,
  so `(v/ask kb '(seeAlso ?term genl) 'CxUniverse)` finds every term that points at `genl`,
  and the reference is retracted, scoped to a context and exported like any fact.
  `seeAlso` takes its arguments as written, through `quotedArg … denotational_term`, and it
  is directional on purpose: reading it symmetrically would be an inference, so the reverse
  pointer is a second assertion.
- **Maintenance.** When a referenced term is renamed or retracted, a query finds each
  sentence that names it. A name inside a comment is found only by a text search, and a
  text search also matches every other use of the word. **match the siblings**
  ([ch. 11](11-siblings.md)) reads a type's `seeAlso` and `termsRelated` partners as the
  siblings to compare it with, which it can do only when the partners are stated.

**Why not the other ways.** A "see also X" sentence inside a comment is invisible to every
query, and the term it names has no way to know it is referenced.

**Audit.** For each term name inside a new comment string, decide whether it is part of
the meaning or a pointer. Move each pointer into `seeAlso` or `termsRelated`.

## Example annotations

**Practice.** Annotate a term with examples beside its comment. Use the quoted form,
`(positiveExample term (Quote S))` or `negativeExample`, when the example is a sentence the
KB can state and the KB is meant to prove or not prove it. Use the string form,
`positiveExampleComment`, `negativeExampleComment` or `borderlineExampleComment`, for an
example the KB cannot state or does not prove. Draw the negative examples from the
near-misses ([ch. 9](09-differentia.md)).

**Example.** organism.txt quotes its species examples, and abstract.txt describes its
mechanism examples in strings because no individual for them is in the KB:

```clojure
(positiveExample folk_species (Quote (folk_species cat)))
(positiveExampleComment mechanism "the hind-leg gears of a juvenile Issus planthopper")
(negativeExampleComment mechanism "a cloned sheep")
```

**Why.**

- **Logic.** Examples test a definition and do not establish it: a finite list cannot show
  that a property is necessary or sufficient. A negative example drawn from a near-miss is
  the case that tests whether the definition excludes what it should.
- **Engine.** A quoted example carries an obligation that a test holds.
  `curation_test` asks each shipped `positiveExample`'s sentence in the context the example
  is stated in and requires it to be provable there, and requires a `negativeExample`'s
  sentence not to be provable (unknown is enough). The example names no sentex, so
  retracting what made its sentence provable leaves the example standing and turns the
  test red. The string forms are documentation only: nothing in the engine reads them and
  no test checks their text against the KB.
- **Maintenance.** A quoted example fails when the KB drifts away from it, so it is a
  regression test written in the vocabulary itself. A string example records a decided
  case for the next reviewer.

**Why not the other ways.** Examples kept only inside the comment prose cannot be listed
by a query, and a quoted sentence is better than a string wherever the KB can state it,
because the test reads it.

**Audit.** Each new type has positive examples, including a hard case, and negative
examples from its near-misses. Each quoted example passes `curation_test`'s
`the-shipped-examples-hold-as-stated` once the change lands.
