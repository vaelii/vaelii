# 22. Functions

- **Covers:** declaring a function beside the predicate that states the same relationship;
  `functionCorrespondingPredicate` and `functionCorrespondingBinaryPredicate`; choosing
  `reifiable_function` or `unreifiable_function`; the result type of an application.
- **Not here:** spelling a function and telling it from an individual →
  [ch. 8](08-kind-of-term.md); constants a rule mints for an existential →
  [ch. 33](33-existentials.md); context terms built from a function →
  [context-nat.md](../docs/context-nat.md).
- **Assumes:** [ch. 8](08-kind-of-term.md), [ch. 18](18-argument-types.md),
  [ch. 19](19-relation-properties.md) (`functional`).

A function application `(F a…)` that denotes something is a NAT, a non-atomic term.
`(MotherFn Muffet)` names Muffet's mother whether or not the KB knows her name. A NAT is
useful for naming a thing before it has a name, and a KB that has only the function can
state nothing about the relationship the function computes. This chapter is about keeping
both.

## don't skip the predicate
*Don't skip the predicate*

**Practice.** When you declare a function, also declare the predicate that relates its
arguments to its value, state the correspondence with `functionCorrespondingPredicate`
or, for a binary predicate with the value second, `functionCorrespondingBinaryPredicate`,
and write rules in terms of the predicate. Skipping the predicate is a decision, and the
file says so in a `;;` note when it is made.

**Example.** `life.txt` declares `MotherFn` and `motherOf` together:

```clojure
(reifiable_function MotherFn)
(unary_function MotherFn)
(functionCorrespondingBinaryPredicate MotherFn motherOf)
(result MotherFn animal)
```

```clojure
(set/monotonic (instance_relation_predicate motherOf))
(arg motherOf 1 animal)
(arg motherOf 2 animal)
(set/monotonic (functional motherOf))
```

`functionCorrespondingBinaryPredicate` puts the value at the second argument of
`motherOf`. The `comment` on `fatherOf` gives the reason the child comes first: "The
child comes FIRST and the father second, the shape functionCorrespondingBinaryPredicate
states, which is what lets FatherFn read off it." The kinship rules in `CxKinship.txt` are written over the predicate:

```clojure
(set/forwardRule (implies (and (motherOf ?child ?mother)) (parentOf ?mother ?child)))
```

**Why.**

- *Logical.* `(functionCorrespondingPredicate F P N)` says `(F a…)` is `V` exactly when
  `P` holds of `a…` with `V` at argument `N`, and
  `(functionCorrespondingBinaryPredicate F P)` is
  `(functionCorrespondingPredicate F P 2)`. The function and the predicate state one
  relationship, and the declaration tells the KB so.
- *Engine.* The correspondence is read both ways. A believed `(motherOf Muffet Mary)`
  makes `(MotherFn Muffet)` written in a context that sees the fact resolve to `Mary`, so
  no second name is minted. When no value is known, the mint proceeds and the constant is
  projected back onto the predicate as `(motherOf Muffet K)`, so the placeholder answers
  `motherOf` questions. A value arriving after the mint retires the placeholder by a
  `rewriteOf` in the fact's context. Whichever of the application, the fact and the
  declaration arrives last, the KB ends in the same state.
- *Engine.* The engine does not match a function application inside a rule. A rule whose
  antecedents name an open application of a reifiable function is stored with the
  application replaced by a variable and the corresponding literal added to its
  antecedents. A rule whose antecedents apply a reifiable function its context sees no
  correspondence for is stored as written and held: it is not believed and fires nothing.
  Nothing on the write path refuses the rule.
- *Maintenance.* A KB told one of the two spellings can reason with both. The FatherFn
  `comment` in `life.txt` names the effect: "Corresponding to fatherOf is what keeps it
  from minting a second name for a father the KB already knows."

**Why not the other ways.** A function with no predicate forces every statement about
the relationship to be written with the NAT in it, so the representation depends on how
the term is spelled, and a fact stated with a plain name for the value never meets a rule
written over the application. A predicate with no function gives up naming the value
before it is known; the correspondence costs one sentence and keeps both.

**Audit.** Run `kb-integrity` and read `:uncorresponded-function`. Each finding is
`{:function F :rules [h …]}`, naming a function the held rules apply with no
correspondence visible from the audit context. A rule the audit context cannot see is not
read, so run the audit from the context the change targets. For each new function, name
its corresponding predicate or the `;;` note that records the decision not to have one.

## Reifiable or structural

**Practice.** Mark a function `reifiable_function` when its applications denote objects
and the set of distinct applications is bounded. Mark it `unreifiable_function` when the
arguments range over a continuous or open-ended domain, or when a prover reads the
arguments inside the term.

**Example.** `measure.txt` and `time.txt` mark the measure and calendar constructors
structural, and `time.txt` marks the time of a thing reifiable:

```clojure
(unreifiable_function QuantityFn)
(unreifiable_function DayFn)
(reifiable_function TimeOfFn)
```

The `implementationNote` on `QuantityFn` reads "it stays structural instead of being
minted into an opaque constant, so the magnitude and the unit are still readable inside
the sentence".
The `comment` on `TimeOfFn` reads "A reifiable_function, one value per temporal thing".

**Why.**

- *Engine.* A ground application of a reifiable function becomes an opaque `nat/`
  constant before it reaches the index, recorded by a `(natFormula K E)` fact, and is then
  indexed, retrieved and retracted as any symbol is. The declared `result` types are
  materialized on the constant at the mint. A structural application is never minted; it
  is typed from the declaration at check time, and its arguments stay readable to the
  quantity and calendar provers.
- *Engine.* The two marks are exclusive: `core.txt` states `(partition function
  reifiable_function unreifiable_function)` at `:monotonic`. Neither mark is in the
  forced-monotonic set, so each holds at the strength it is written at, and a function
  whose `reifiable_function` mark one reader believes and another does not is read per
  reader ([nat.md](../docs/nat.md)).
- *Engine.* The correspondence is read only for a reifiable function. `measure.txt` and
  `time.txt` still state one for `QuantityFn` (`measureInUnit`) and `DayFn`
  (`calendarDay`), and the `implementationNote` on each predicate says the prover "reads
  the … term and does not answer this predicate". The predicate then records the relationship
  for a reader and for any other encoding of the same values.
- *Maintenance.* Reifying keeps one constant per distinct application. `nat.md` gives the
  bound: `(FatherFn Muffet)` is one constant per animal, where `(QuantityFn 5 Meter)`,
  `(QuantityFn 5.001 Meter)` and every magnitude between them would be a constant apiece
  with nothing to bound the store.

**Why not the other ways.** A measure function marked reifiable hides the magnitude and
the unit inside an opaque constant, and the quantity provers then have nothing to compare.
An object-denoting function left unmarked is a raw compound the reify pass never visits:
its applications get no constant, no materialized result type and no correspondence.

**Audit.** For each new function, state which mark it takes and why the application space
is bounded or not. Confirm it has a `result` declaration, so its value has a type.

## When the values want an order

**Practice.** When the values of a function, or a set of named individuals, start to need
"this one implies that one", represent the distinctions as predicates or types, and give
the function its corresponding predicates. Chapter 8 states this as **nesting values
aren't individuals** ([ch. 8](08-kind-of-term.md)).

**Example.** `oe-principles.md` gives the case of access kinds named as individuals: "admin
implies write" has no place to be stated, since an individual takes no `genl`. As
predicates the implication is one edge. The two names below are temporaries for the
illustration:

```clojure composed
(genl hasAdminAccess hasWriteAccess)
```

**Why.**

- *Logical.* An implication between two kinds of access is a subsumption, and subsumption
  holds between predicates or types, not between individuals.
- *Engine.* A predicate `genl` is a closure edge: a `hasAdminAccess` fact answers a
  `hasWriteAccess` goal with no rule and no stored copy ([ch. 17](17-predicate-hierarchy.md)).
- *Maintenance.* With individuals, each implication between access kinds becomes a rule
  over a variable access argument, and every rule that reads access has to repeat the
  ordering.

**Why not the other ways.** A rule per pair of individuals restates the hierarchy as rules
and has to be extended for each new kind. A function whose values are individuals keeps
the same problem one level down.

**Audit.** For each enumeration of individuals, ask whether any one of them implies
another. A yes means the enumeration is a set of predicates or types.
