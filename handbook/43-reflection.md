# 43. Reflection

- **Covers:** talking about sentences, terms and names: use and mention, `(Quote X)`,
  choosing between `Quote` at the use and a `quotedArg` declaration on the position, the
  expression lattice `reflection.txt` declares, `denotes`, `expresses`, `means` and
  `proposition`, when a fact is about a sentence and when it is about the world, the
  quoted example annotations, and `(sentexHandle H)`.
- **Not here:** `quotedArg` as one of the argument declarations →
  [ch. 18](18-argument-types.md); what an example annotation is for and when to write the string form →
  [ch. 7](07-comments.md); what an agent believes → [ch. 36](36-agents-and-hypotheses.md);
  `except` → [ch. 23](23-contexts.md); one thing under two names →
  [ch. 37](37-coreference.md); how the engine answers a kind of a quoted form →
  [argtypes.md](../docs/argtypes.md#what-a-quoted-form-is); the mention exemption from
  congruence → [equality.md](../docs/equality.md); a quoted sentence in a rule →
  [inference.md](../docs/inference.md).
- **Assumes:** [ch. 7](07-comments.md), [ch. 8](08-kind-of-term.md),
  [ch. 18](18-argument-types.md), [ch. 19](19-relation-properties.md) (`functional`).

A sentence uses its terms: `dog` written in `(dog Muffet)` denotes the predicate, and
`Muffet` denotes the dog. A sentence about a term or a sentence mentions it, and in vaelii
the mention is written `(Quote X)`, which denotes the expression X. `reflection.txt` gives
the KB a vocabulary for expressions, so a fact about a written form is an ordinary sentence
that queries, rules and audits read.

## use by default
*Write a term plainly unless the sentence is about the term*

**Practice.** Write a term unquoted when the sentence is about what the term names. Write
`(Quote X)` only when the sentence is about the written form X: its spelling, its kind, who
wrote it, or what it exemplifies. Never state an expression kind of an unquoted term.

**Example.** `core.txt` places the written forms under `linguistic` and separates them from
what they name, and the `Quote` annotation gives the contrast:

```clojure
(set/monotonic (separating nowhere_never logical linguistic quantitative))
(genl symbol linguistic)
(positiveExampleComment Quote "(Quote Muffet), which names the symbol Muffet and not the dog")
```

**Why.**

- *Logical.* A symbol and the thing it names are two things. `dog` written plainly is the
  predicate, which is `logical`; `(Quote dog)` is the symbol, which is `linguistic`. The
  separation makes `symbol` and `predicate` share no instance, so an unquoted
  `(symbol dog)` contradicts what `dog` denotes.
- *Engine.* `Quote` is fixed by the engine and takes no `arg`, `result` or metatype
  declaration; the kind of `(Quote X)` follows from how X is written. A variable inside
  `(Quote …)` is never free in the sentence around it, so a sentence quoting a rule is a
  closed fact.
- *Engine.* A quoted term is held opaque to identity merges. After `(sameAs Muffet
  Fluffet)`, `(different (Quote Muffet) (Quote Fluffet))` still holds. A `rewriteOf`
  spelling rename does reach inside, since a rename retires a name and merges no referents.

**Why not the other ways.** A string `"dog"` names a string, which nothing connects to the
term `dog`: a query for the term does not find it, and a rename of the term leaves the
string unchanged. A quotation added where the sentence is about the referent turns a claim
about the world into a claim about a name, and no rule over the referent fires on it.

**Audit.** Review: for each `(Quote X)` in the change, name what the sentence says of the
form X that it does not say of what X names, and confirm every argument of an expression
kind (`symbol`, `formula`, `sentence`) is quoted.

## Quote or quotedArg

**Practice.** When every filler of a position is a written form, declare
`(quotedArg R n K)` with an expression kind `K`, and write the filler unquoted. When a
position holds things of any kind and one sentence names a form, or when the form must stay
apart from its referent under identity merges and be matched exactly as written, write
`(Quote X)` at the use. Choose `K` from the kinds a spelling decides, and choose two kinds
the KB separates when the position must refuse the other one.

**Example.** `core.txt` declares three positions that hold written forms, and
`reflection.txt` separates formulas from terms:

```clojure
(quotedArg comment 1 closed_expression)
(quotedArg argN 3 formula)
(quotedArg argN 1 expression)
(set/monotonic (disjoint formula non_atomic_term))
```

**Why.**

- *Engine.* `quotedArg` reads the argument as written and is checked, never entailed. A
  compound there is held inert only where one of its kinds is separated from `K`: under
  `(quotedArg P 1 non_atomic_term)`, `(P (not (dog Fido)))` is held, `formula` being
  separated from `non_atomic_term`, and an application of an unclassified head, which
  merely fails to reach `K`, is believed.
- *Engine.* Only a quoting function and a `modal_predicate`'s proposition hold a term
  opaque to `sameAs` and `equals`. A merge rewrites a symbol in a `quotedArg` position.
- *Engine.* Canonicalization stops at a quoting function. `(holds (Quote (PairFn Bob
  Ann)))` and `(holds (Quote (PairFn Ann Bob)))` are two sentexes, and a quoted sentence
  matches only the spelling it was stored under, variable names included. A mark on the
  function holding a quoted form still sorts that application, since a quoted form is a
  constant: `(RulePairFn (Quote R1) (Quote R2))` stores in one order under `core.txt`'s
  `(commutative RulePairFn)`. The one reader that compares quoted rules by canonical
  sentence is `kb-integrity`'s, for an `acknowledgedFinding` subject
  ([ch. 28](28-vocab-pr.md#acknowledged-findings)).

**Why not the other ways.** `(arg R n symbol)` types what the argument denotes, and `symbol`
is mention-only: `parentOf` written there denotes a predicate, so the argument is
convicted, or under the entailing reading the KB derives `(symbol parentOf)`, which the
separation of `logical` from `linguistic` contradicts. A `K` outside the expression
lattice is read open-world and convicts nothing.

**Audit.** For each `quotedArg` in the change, name the kind and one filler the
declaration refuses. Run `check` on that filler's sentence and read `:quoted-arg-type`.

## Classify a form by its kind

**Practice.** In a rule over written forms, test the form's kind with a `reflection.txt`
type: `sentence`, `formula`, `predication`, `literal`, `non_atomic_term`,
`ill_formed_expression` and their open and closed halves. Test `sentence` or
`closed_predication`, not `wff`, `wff_sentence` or `wff_expression`, for a well-formed
formula. Join the kind with a stored fact that binds the form.

**Example.** `reflection.txt` cuts `expression` three ways, and each kind is a partition
member:

```clojure
(partition expression atomic_expression non_atomic_expression)
(partition expression wff_expression ill_formed_expression)
(partition formula open_formula sentence)
(partition literal predication negated_predication)
```

A composed rule over temporaries concludes who stated a closed formula:

```clojure composed
(set/forwardRule (implies (and (tmpSaid ?a ?q) (sentence ?q)) (tmpAsserter ?a)))
(tmpSaid TmpTom (Quote (not (dog Muffet))))
```

**Why.**

- *Engine.* `ExpressionKindProver` answers `(k (Quote X))` from X's spelling, and under a
  symbol head `R` from what the KB states of `R`: a predicate makes a predication, a
  function a `non_atomic_term`, and a length the argument count breaks an ill-formed form.
  A firing that read `R`'s membership fires in every arrival order and withdraws with it.
- *Engine.* No kind answers `wff_expression`, `wff` or `wff_sentence` for a formula, since
  the positive half of well-formedness needs every operator's length inside X. Forward
  chaining also skips `negated_predication` and any type an author adds below `expression`.
- *Engine.* `(sentence (Quote (not (dog Muffet))))` holds by spelling alone and rests on no
  stored sentence, and a firing with no support is dropped. The stored `tmpSaid` fact
  supports the firing above, and retracting the fact withdraws the conclusion.

**Why not the other ways.** A predicate stated per form, such as a hand-written
`(sentence (Quote …))` fact, repeats an answer the prover computes from the spelling, and
the stored copy does not move when the head's arity or membership changes.

**Audit.** For each rule in the change with an expression-kind antecedent, confirm the
kind is in the lattice and a stored antecedent binds the form. Run `why` on one
conclusion and confirm it names the fact.

## denotes, expresses, means

**Practice.** Relate a term to what it names with `(denotes (Quote T) X)`, and a sentence
to what it says with `(expresses (Quote S) P)`, where `P` is an individual of type
`proposition`. Use `means`, the predicate both sit under, only where the form may be either.
State two readings of one form in two contexts that no context sees together.

**Example.** `reflection.txt`:

```clojure
(genl denotes means)
(genl expresses means)
(arg expresses 2 proposition)
(set/monotonic (functional means))
(set/monotonic (separating logical relation proposition context))
```

A composed pair states that an English sentence and a sentence named by a constant express
one proposition:

```clojure composed
(proposition TmpMuffetIsADog)
(wff_sentence TmpMuffetEstUnChien)
(expresses (Quote (dog Muffet)) TmpMuffetIsADog)
(expresses TmpMuffetEstUnChien TmpMuffetIsADog)
```

**Why.**

- *Logical.* A proposition is what a sentence says, apart from the language it is said in.
  Two sentences can express one proposition, and two true sentences can express different
  ones, so a proposition is not a sentence and not a truth value. The separation keeps it
  apart from relations and contexts.
- *Engine.* `functional` on `means` is read up the predicate hierarchy, so it judges
  `denotes` and `expresses` tuples too. Two `:monotonic` `denotes` facts naming two
  symbols for one form derive `(equals X Y)`, and two `:default` facts for one form are a
  nogood wherever a context sees both. An ambiguous word stated with both meanings in one
  context therefore merges the meanings or clashes.
- *Engine.* No engine path reads `denotes` or `expresses` to interpret a sentence. The two
  are facts for rules to reason over, such as a lexicon's.

**Why not the other ways.** `(equals (Quote S1) (Quote S2))` says the two forms are one
form, which is false of two sentences that only say the same thing. A quoted sentence
in the proposition position names a sentence and not what the sentence says.

**Audit.** For each `denotes` or `expresses` fact, name the context it holds in and confirm
no context in the change sees a second meaning of the same form. Read any `equals` the
change derives between two meanings with `why`, which names the two facts and the
`functional` mark.

## About the sentence or about the world

**Practice.** To say that something is the case, assert the sentence in the context it
holds in. To say that an agent holds it, write the sentence unquoted under a modal
predicate ([ch. 36](36-agents-and-hypotheses.md)). Quote a sentence only when the claim is
about the sentence: an example of a term's use, a review record, an attribution of
wording. Quote a closed sentence.

**Example.** `organism.txt` and `CxTra.txt` annotate types with quoted examples, and
`abstract.txt` records a reviewed rule clash by quoting the two rules:

```clojure
(positiveExample folk_species (Quote (folk_species cat)))
(negativeExample ip_address (Quote (ip_address "example.org")))
(acknowledgedFinding :rule-clash
  (RulePairFn
   (Quote (implies (properPartOf ?part ?whole) (not (partOf ?whole ?part))))
   (Quote (implies (and (tangiblePartOf ?x ?y) (not (tangiblePartOf ?y ?x)))
                    (properTangiblePartOf ?x ?y))))
  "Left unexcepted on purpose. A proper reading's definition concludes a proper tangible part, so a part, and the root rule denies one. Both fire for one tuple only where the facts already contradict the root rule: a part whose whole is stated a proper part of it. Both rules are strict definitions, so that clash is the one the facts owe, and an exception would hide it.")
```

**Why.**

- *Logical.* A quoted sentence is a term, so quoting a sentence asserts nothing about the
  world. `(positiveExample folk_species (Quote (folk_species cat)))` does not state that
  cats are a folk species; the separate fact does, and the example records that the fact
  holds.
- *Engine.* `curation_test` asks a positive example's quoted sentence in the example's
  context and requires a proof, and requires a negative example's sentence not to be
  provable. An open quoted sentence is reported, since any one binding would answer it.
  Retracting the quoted sentence leaves the example stored and turns the test red.
- *Engine.* `kb-integrity` moves a `:rule-clash` finding an `acknowledgedFinding` names to
  its review-only category. The quoted rules are syntax, so the record asserts neither.
- *Engine.* No rule matches inside a quotation. `ist` and a modal predicate are not
  quotations: `(ist Ctx S)` asserts `S` in `Ctx`, and a modal proposition is proved in the
  agent's context.

**Why not the other ways.** A sentence quoted to say it is true, under a predicate of the
author's own, is never believed and fires no rule. A state that holds at some times and not
others is a fluent, a term built by a function ([ch. 35](35-change-over-time.md)), not a
quoted sentence. An example kept in the comment prose is read by no test.

**Audit.** For each quoted sentence in the change, say whether the claim is about the
sentence or about the world; the second is asserted or projected instead. Each quoted
example passes `curation_test`'s `the-shipped-examples-hold-as-stated` once the change
lands.

## content, not handle
*Name a sentence by its content in KB text, and a stored sentex by handle only from code*

**Practice.** In a KB file, name a sentence with `(Quote S)`. Write `(sentexHandle H)` only
from code that holds the handle, through `sentex-handle`, for a meta-sentence about one
stored record: an `except`, or a reply to a claim. Declare a predicate whose sentences name
a handle `target_following_predicate` when each sentence must go with its target.

**Example.** `kb/koinii/CxSpeechActs.txt` declares the reply acts target-following. The
starter does not load `kb/koinii/`: koinii, the application those files belong to, loads
them itself. A composed call excepts one stored sentex and lists the sentences naming it:

```clojure
(target_following_predicate answers)
```

```clojure composed
(def h (v/assert kb '(dog TmpRex) 'CxWell))
(v/assert kb (list 'except (v/sentex-handle h)) 'CxWell)
(v/sentexes-naming kb h)
```

**Why.**

- *Engine.* A handle is one store's integer, allocated in assertion order. A text export
  writes an `exceptWhen` back as the wrapper around its rule and drops every other sentence
  naming a handle, since the integer names another sentex, or none, in the reading KB.
- *Engine.* Retracting a target retracts every sentence of a `target_following_predicate`
  that names it. `except` and `exceptWhen` do not carry the mark, so an `except` outlives
  its target.
- *Logical.* `(Quote S)` names the sentence, which holds in any number of contexts; a
  handle names one sentex, one sentence in one context. A claim about wording takes the
  first and a claim about one record takes the second.

**Why not the other ways.** A handle written into a KB file names a record of the store
it was copied from. A quoted sentence where a record is meant, such as hiding one
context's copy, names every copy of the sentence.

**Audit.** `git grep sentexHandle` over the change's KB files and confirm each hit is in a
comment or documentation string. For each code path that writes a meta-sentence, run
`sentexes-naming` on a target before retracting the target, and confirm the predicate is
`target_following_predicate` exactly when the metas must go with the target.
