# Non-atomic terms (NATs)

- **Covers:** how a function-application term reifies to an opaque constant before
  the index sees it, or stays structural when it does not.
- **Not here:** minting a deterministic constant for a rule's existential head →
  [skolem.md](skolem.md); comparing two structural measure terms →
  [quantity.md](quantity.md).
- **Assumes:** sentex, context, taxonomy, predicate metadata →
  [glossary.md](glossary.md).

A **NAT** is a function-application term `(F arg…)` that *denotes an entity* —
`(FruitFn AppleTree)`, `(CapitalOf France)`, `(QuantityFn 5 Meter)`. A stored sentence has
no first-class function terms; every stored token is atomic. NATs
are supported by **reification**, and functions split by declaration into two kinds.

- `(reifiable_function F)` — **object-denoting**. A ground `(F a…)` is a **reified NAT**: it
  reifies to an opaque `nat/`-namespaced constant `K` *before it reaches the index*,
  so the reified NAT autoindexes exactly like a hand-minted symbol.
- `(unreifiable_function F)` — **evaluated / interpreted**. The application stays a
  **structural NAT** — `(QuantityFn 5 Meter)` keeps its magnitude and
  unit readable for a downstream prover; it is never minted.

## The strategy: reify before the index

A reifiable NAT is replaced by an atomic constant on the write path, so:

- the trie key is unchanged — `(color K Red)` keys `[color K Red]`, K one token;
- `sentex/index-terms` is unchanged — K is an ordinary symbol subterm;
- the reified NAT autoindexes, is retrieved, and is retracted exactly like any symbol.

Indexing nested compounds structurally is the alternative
([defenses.md](defenses.md#a-nat-is-reified-before-the-index-rather-than-indexed-structurally)).

## The data model — all ordinary stored facts

Nothing here is a KV side table. Every mapping is a normal sentex in
**CxUniverse**, so it rides `put-sentex`, the functor / argument roots, and the
inverted term index like any other fact.

| Fact | Meaning |
|------|---------|
| `(reifiable_function F)` / `(unreifiable_function F)` | F's kind — a **predicate-metadata mark** (`vaelii.impl.taxonomy` `:reifiable` / `:unreifiable` prop), belief-following like `transitive`/`symmetric` |
| `(natFormula K E)` | the constant↔expression map: constant `K` denotes NAT expression `E`. The reverse (`K → E`) index; `E → K` is the inverted term index |
| `(rewriteOf T E)` (compound `E`) | NAT `E` reifies to the existing real term `T` instead of a fresh constant |
| `(result F T)` / `(genlResult F T)` | F's output types — materialized on mint as `(T K)` / `(genl K T)` |
| `(resultArg F n)` | F's output is an instance of the type the application's argument `n` names — derived over each `natFormula` fact as `(a_n K)` ([argtypes.md](argtypes.md#a-type-another-argument-names-argarg)) |
| `(functionCorrespondingPredicate F P N)` | F and P state one relationship: `(F a…) = V` exactly when P holds of `a…` with `V` at argument `N` |
| `(functionCorrespondingBinaryPredicate F P)` | `(functionCorrespondingPredicate F P 2)`: P is binary, the argument first and the value second |

`natFormula` and `rewriteOf` are **quoting predicates** (`nat/nat-quoting-predicates
= #{natFormula rewriteOf}`): their expression argument is a verbatim NAT payload that
must not itself be reified or type-checked as a term.

`(rewriteOf T E)` overloads the equality/deprecation `rewriteOf`, discriminated by
shape: a **symbol** second argument is term equality (the equality partition — see
[equality.md](equality.md)); a **compound** second argument is a NAT reify-to-term
declaration. The equality integrate arm and `wff/equality-problems` both skip the
compound shape, so it is stored as an inert quoting fact, never entering the closure.

## Which mark a function gets

`reifiable_function` and `unreifiable_function` describe two mechanisms — minted into a
constant, or left structural for a prover to compute. The criterion between them is
**boundedness of the application space**.

Reifying stores one opaque constant per distinct application and keeps it, so it is safe
exactly when the applications are bounded: `(FatherFn Muffet)` is one constant per animal,
and an `AdultFn`-shaped function one per individual. A function whose arguments range over
a continuous or open-ended domain is not, and takes `unreifiable_function` instead —
`(QuantityFn 5 Meter)`, `(QuantityFn 5.001 Meter)` and every magnitude between them run
over the reals, so a constant apiece is a store nothing bounds. That is why `QuantityFn`
and `QuantityIntervalFn` are unreifiable, and why a **measure function is never reifiable
however atomic its value reads**: reifying `(QuantityFn 5 Meter)` would also hide the
magnitude and the unit a prover reads.

Both marks classify: `(reifiable_function F)` and `(unreifiable_function F)` each say F is a
`function`, which is what `(disjoint function predicate)` — derived from the partition
of `relation` — reaches, and `(partition function reifiable_function unreifiable_function)`
makes the two marks exclusive: a function is one or the other. The choice changes where a
declared result type is *stored*, not whether it holds — a reifiable application carries
`result` materialized on its constant, an unreifiable one is typed from the declaration at
check time, and the two say the same thing about the same function.

## The reifiable-function presence check

A function's kind is metadata cached in the taxonomy, so the per-sentence presence check —
"does the KB declare any function that reifies?" — is a free **in-memory set read**
(`nat-read/any-reifiable-functions?` ⇒ `seq` of the `:reifiable` props),
belief-following and needing no mtime cache. A KB that declares none pays one set read per assert / query for
the argument reify. The maintenance a minted constant owes (the orphan sweep, the
collision merge, the structural `genlCx` producer) reads `nat/any-reified-constants?`,
which adds one O(1) `natFormula` functor count when the set is empty, since a context
slot mints a `cx/` constant with no declaration ([context-nat.md](context-nat.md)).

## Write path

`assert` runs `maybe-reify-nats` **before `expand-consequent`, WFF and the constraint
checks**:

- every **ground, reifiable** NAT subterm `(F a…)` is replaced by its constant `K`
  (an existing one via dedup, else a fresh mint) — inner args reified first, then the
  outer NAT;
- the walk descends into nested non-NAT literals (rule bodies, conjuncts) but leaves
  the head predicate, every quoting-predicate argument and a `modal_predicate`'s
  proposition opaque. A stored `(believes Ann (likes Tom (FruitFn Apple)))` keeps the
  application, and the read entry points leave it as written in a goal, so the belief
  projection reifies it in the agent's context
  ([belief.md](belief.md#where-the-barrier-sits-and-what-it-covers));
- a **vector** is descended element by element, and every element of it. A vector in a
  sentence is a list of forms rather than a literal — an `exceptWhen`'s conjuncts, a
  `thereExists`'s binders — so it has no head predicate to hold opaque and no element
  to skip. That is what puts an exception's query in the same spelling as the fact it
  is about, and the cost of stopping at one is not a missing answer: an exception that
  cannot be answered does not hold ([exceptions.md](exceptions.md)), so the rule fires
  unguarded and nothing says so;
- **unreifiable NATs are left structural** — never minted.

Reify-**before**-WFF is required. The raw compound `(FruitFn AppleTree)` in an
argument slot is not indexed, and `disjoint-problem` skips it — the term index never
posts the raw NAT's constituents, which would pollute it (`sentex/index-terms` descends
into ground compounds). The minted constant `K` carries the materialized `result`
types, so it is an atomic term every check reads like any symbol.

The **argument** checks do not skip it. `args-problem` and `genls-problem` read a
compound through its function's declared result — see [Typing an application that is
never minted](#typing-an-application-that-is-never-minted) below, which is what makes
one declaration bind both classes of function.

`mint-nat!` allocates the opaque `K`, asserts `(natFormula K E)`, materializes the
result types (`(T K)` per `result`, `(genl K T)` per `genlResult`), and returns
`K`, all at `:monotonic` strength — a reified NAT's identity and result types are structural,
not defeasible. The map is asserted with chaining off unless a `resultArg` of `F` is
declared ([defenses.md](defenses.md#the-mints-natformula-fact-does-not-chain)). `assert`
stores synchronously, so a second occurrence of `E` in the same sentence dedups against
the first; a `(rewriteOf T E)` declaration short-circuits the mint to the real term `T`.

`K` is **named by the content of `E`**: `constant-for` hashes `E` with SHA-256, takes the
first 96 bits, and encodes them base62 behind a one-letter scheme tag — `nat/a<17
base62>` for an object NAT, `cx/a…` for a context one (`nat-scheme-tag`). So the same
expression reifies to the **same** constant in any process and after any rebuild, as the
skolem digest ([skolem.md](skolem.md)) names its witnesses. Two dumps that minted the same
NAT hold the same `(natFormula K E)` fact and merge by deduplication, and a re-mint after
an orphan sweep resolves to the constant it had before. The base62 digits keep `K` within
the argument naming convention (`naming/argument-problem`). The leading letter keeps the
name a readable token, since a digit-leading name is not one, and it versions the scheme:
a later hash or encoding change is `nat/b…`, and old constants keep their names
([defenses.md](defenses.md#a-reified-constant-is-named-by-its-content-in-base62)).

## Derivation path

The forward chainer stores a rule's conclusion itself rather than through `assert`, and it
reifies the same way. `chain/place-conclusion` replaces every ground reifiable NAT in a
fired conclusion with its constant before it stores anything (`reify-conclusion`). A stored
rule's consequent keeps its applications as written ([A rule or a goal that names an
open application](#a-rule-or-a-goal-that-names-an-open-application)), so a firing's
bindings make each one ground and this pass mints it, with or without a correspondence.
A generator's generated rule goes through this pass too, so a ground application in its
antecedent is spelled with the constant the facts it matches are stored under.

- An application that already has a term resolves to it — a `rewriteOf` target, the
  value its corresponding predicate names, or the minted constant — through
  `nat-read/reify-existing`, which mints nothing.
- An application with no term is checked before it is minted. The placement's own checks
  run over the conclusion under `checks/*entry-mints?*`, which reads the application as
  the constant a mint would give it, the reading `check` uses (below). A conclusion those
  checks drop is dropped with nothing minted, so no constant is left behind whose one use
  was never stored. The `equals` and `sameAs` check reads the application as a symbol
  under the same binding (`special/equality-wff-problems`), so
  `(implies (linkedQuad ?a ?b ?c ?d) (equals (PairFn ?a ?b) (PairFn ?c ?d)))` mints both
  applications and stores the equality between the two constants, as `assert` of the
  ground sentence does. An admitted conclusion is minted by `mint-nat!`, and the placement
  then runs its checks again over the reified sentence; that second pass draws the
  argument-type entailments on the constant.
- The mint writes what `assert`'s mint writes: the `natFormula` map and the materialized
  result types, as premises in CxUniverse at `:monotonic`, and the settle places the
  correspondence projection off the map. The constant's name is the expression's content, and its bookkeeping is
  the same whichever path named the application first.
- A mint is a full assert and can refuse. A firing does not throw mid-fixpoint
  ([nmtms.md](nmtms.md#definitional-constraints-on-the-derivation-path)), so a refused
  mint drops the conclusion and is recorded in `core/violations` as `:mint-refused`, with
  the refusal's own type under `:refusal`. A firing has no batch to roll back, so the
  bookkeeping the mint wrote before the refusal stays stored, and no removal names that
  constant for the region sweep to collect. A correspondence projection whose argument
  fails its predicate's `arg` declaration is not a refusal: the projection is stored and
  held, as a convicted firing is
  ([argtypes.md](argtypes.md#an-argument-that-fails-its-declared-type-is-held-inert)),
  and the conclusion stands. The mint
  runs under `*defer-settle?*`, as a skolem witness's mint does ([skolem.md](skolem.md)):
  the fixpoint settles once when it finishes. The seeds the mint's asserts chain from join
  the running fixpoint's agenda, and no run starts inside the firing
  ([inference.md](inference.md#forward-chaining)).

**The derived conclusion is a use of the constant, and the bookkeeping does not rest on
the firing.** The conclusion is justified like every other firing; the map and the result
types are premises. The map is one map: it says what the constant denotes, independent of
which firing named it, so it is stored in `CxUniverse` and belongs to no one derivation.
Which constant an expression resolves to depends on the merges the reader sees (Read path,
below). When the derived use goes — its antecedent retracted, or the settle's sweep
deleting what it solely supported — the removal reaches the orphan sweep through
`integrate/*removed-sink*` like any other removal (Rename and remove, below), and the
constant is collected once nothing but its own bookkeeping names it. An asserted use keeps
it, and a derived use keeps it after the asserted one goes. A re-derivation after a
collection mints the same name, so derive-then-assert, assert-then-derive and a derivation
retracted and restated all store the same sentences.

**A recursive consequent mints to the term-nesting bound.** `(implies (num ?x) (num
(SuccFn ?x)))` from `(num Zero)` mints `(SuccFn Zero)`, then the application of `SuccFn` to
that constant, and so on. A constant's nesting is its expression's, so the n-th constant
nests n deep, and each conclusion nests one level deeper than the fact it rests on. The
write stops at `:max-term-depth` ([inference.md](inference.md#forward-chaining), 8 by
default), having minted 8 constants. With `(result SuccFn num)` each mint stores `(num K)`
as a premise at derivation depth 0, and the bound ends the write at the same 8, because
it reads the terms and not the derivation
(`chaining_contracts_test/a-recursive-mint-ends-at-the-term-nesting-bound`).

**A backward proof mints nothing.** `prove` and `query` store no conclusion. A backward
rule's consequent stays as written, as a forward rule's does, while a goal is respelled
through the correspondence, so the rule answers no goal over the application or its
constant: `(implies (bears ?t ?o) (grownIn (FruitFn ?t) ?o))`, read backward, answers
nothing for `(grownIn K ?o)` or `(grownIn (FruitFn AppleTree) ?o)`, and answers
`(grownIn ?f ?o)` with `?f (FruitFn AppleTree)`, the application as written. Read forward,
the same rule stores `(grownIn K Orchard)`, which both goals find
(`nat_test/an-open-application-reads-through-the-corresponding-predicate-in-every-order`).

## Typing an application that is never minted

A reified application arrives at the definitional checks as its constant, typed by the
`(T K)` / `(genl K T)` the mint materialized. An **unreifiable** function has no mint,
so its application stays a compound all the way to the checks — and a compound holds no
type membership and can hold none, a membership being asserted of a name.

So the argument checks read the *function's* declaration instead. `(arg P n T)` reads
`(result F T')` — what an application of `F` **is** — and `(genlArg P n T)` reads
`(genlResult F T')` — what it is a **kind of**. The two are never crossed.

`(resultArg F n)` adds to what an application **is** the type its own argument `n` names,
so `nat/result-types` takes the application rather than its function: `(resultArg PickFn
1)` types `(PickFn dog)` a `dog` and `(PickFn cat)` a `cat`. A minted constant takes the
same type as a derived `(dog K)`, which the argument entailment draws over its
`natFormula` fact in every arrival order
([argtypes.md](argtypes.md#a-type-another-argument-names-argarg)).

**A term a prover hands back is minted no more than one somebody typed, and is no
orphan.** `(startOf (YearFn 2000) ?i)` binds `?i` to `(InstantFn 2000 1 1 0 0 0)`, an
unreifiable NAT the calendar clock computed from the year's fields
([time.md](time.md)) — and computing it writes nothing: no `natFormula` row, no
materialized result type, no handle, so there is no orphan question to ask about it and no
retraction that could take it back. It is a value in a binding map and lives exactly as
long as the answer does. Asserting a sentence that *contains* one is an ordinary assert,
and `(result InstantFn time_point)` in `time.txt` is what types it there — the same one
declaration binding the computed term and the typed one.

**A goal reads the same declaration.** `provers/ResultTypeProver` answers `(T (F a…))`,
the application ground, when a result type of the application
(`nat-read/visible-result-types`, so a `resultArg` position counts) reaches `T` through
the `genl` edges visible from the asking context. `(time_point (InstantFn 2026 10 6 0 0
0))` holds by `(result InstantFn time_point)`, so a backward rule with a `(time_point ?w)`
antecedent fires for an `InstantFn` term
(`nat_test/a-goal-reads-the-result-type-of-an-application-that-is-never-minted`). The
answer is not complete (50): a function that declares no result is open-world.

```clojure
(v/assert kb '(unreifiable_function QuantityFn) 'CxUniverse)
(v/assert kb '(result QuantityFn measure) 'CxUniverse)
(v/assert kb '(arg needs_dog 1 dog) 'CxUniverse)

(v/assert kb '(needs_dog (QuantityFn 5 Meter)) 'CxUniverse)
;; refused: (QuantityFn 5 Meter) must be a dog — QuantityFn results in a measure
```

Four things fix what that reading is and is not.

- **It is a claim about the function, not about the application.** `(result
  QuantityFn measure)` says every `(QuantityFn m u)` denotes a measure. The term has no
  stored membership and can acquire none, so the check and a goal both read the
  function's declaration.
- **Open-world, one level out from the symbol reading.** A function that declares no
  result exempts every application of it, exactly as an unclassified symbol exempts
  itself, and a declared result the asking context cannot place under `thing` is
  evidence the lattice cannot judge. Only a declared result that visibly reaches `thing`
  and visibly fails to reach the demanded type convicts.
- **Context-scoped, like every definitional check.** The declaration is read from the
  asking context's vantage, so a context that cannot see it is not refused by it. That
  is where the check parts company with the **mint**, which reads globally: a mint
  materializes into `CxUniverse`, where every reader sees the result, and what a term
  denotes is not a thing a reader may vary. `nat/result-types` and
  `genl-result-types` carry both arities for exactly that split.
- **One declaration, one verdict.** Under the constraint reading, `(result F measure)`
  refuses the same sentence whether `F` is reifiable or unreifiable — through the constant
  in the first case and through this reading in the second. On the assert path a
  reifiable function's application never reaches this arm, since it is minted first.

**`check` reads a reifiable application as the constant `assert` would mint.** `check`
writes nothing, so it mints nothing. An application that already has a term
(`nat-read/reify-existing`) is checked as that term. One that has none is read under
`checks/*entry-mints?*`, with its function's result types standing where the minted
constant's memberships would. Under assertive argument types ([argtypes.md](argtypes.md))
the demand then refuses only a result type the taxonomy separates from the demanded type,
with `:disjoint`, which is what the entailment `assert` draws over the constant refuses; any
other result type is admitted, as `assert` admits it and mints the demanded type. The
checks do not read what a rule would conclude of the new constant.

What an application is *given* is a separate reading from what it denotes: each input is
checked against the function's own argument declarations, for a reifiable function before
the mint replaces the application with its constant
([argtypes.md](argtypes.md#relation-wide-declarations-and-the-runtime-boundary)).

A **quoting predicate's** argument is left alone: `(natFormula K (FruitFn AppleTree))`
and a compound-argument `(rewriteOf T E)` carry the expression as a verbatim payload
rather than as a term used in that position, so typing it by what the function yields
would type a quotation by its referent. That is also where the reading would otherwise
cost a mint something — `mint-nat!` writes one `natFormula` per constant.

A **quoting function's** argument is a mention as well. `Quote` and `Quasiquote` are the
quoting functions, fixed by the engine (`sx/quoting-functors`) rather than declared, so
no KB can add one or take one away. The reify pass does not reify a NAT nested in their
argument: `(Quote (FruitFn Apple))` mints against the literal `(FruitFn Apple)`, not
against that NAT's own constant, and a read resolves against the same literal. A
quotation names its syntax, and reifying the nested NAT would collapse two quotations
whose payloads' referents merge onto one mention. The argument is held opaque to an
identity merge in the congruence walk too ([equality.md](equality.md)).

`disjoint-problem` is the check that still skips a compound. Its `:opposing-handle` is
the conflicting *membership's* handle — what `settle` weighs the pair by — and a result
declaration is not a membership of this application: pairing them in a nogood would let
one application's assertion defeat a claim about the whole function.

## Read path

Before matching, a query goal's ground reifiable NATs are reified to their
**existing** constant (dedup, never mint). An unknown (never-minted) NAT resolves to
the reserved `nat-read/no-match` sentinel, which can never be a real constant — so an
unknown-NAT query returns empty without minting. `no-match` names no term: a literal
holding it at a term position, as an argument or inside an application at any depth, is
read by the stored-fact prover alone (`res/names-no-match?`), so `(different (FooFn Xa Xb)
Zed)`, `(different (BarFn (FooFn Xa Xb)) Zed)`, `(equals ?x (FooFn Xa Xb))` and `(genl
(FooFn Xa Xb) ?y)` answer nothing. A sentence position (a construct's argument such as
`unknown`'s, or a `formula` position) holds a literal of its own, which its prover
reads: `(unknown (tagged (FooFn Xa Xb)))` holds. A positive equation goal
(`res/equation?`) reads a never-minted application as written
(`nat-read/reify-existing`), and the equality closure answers it by identity and congruence: `(equals (FooFn Xa Xb) (FooFn
Xa Xb))` holds, and `(equals (FooFn Xa Xb) (FooFn Xc Xd))` holds only in a context that sees
`(equals Xa Xc)` and `(equals Xb Xd)`. A never-minted application of a quoting function
stays as written in every goal, because a mention names its own syntax: under
`(reifiable_function Quote)`, `(different (Quote Bar) (Quote Baz))` holds for two
quotations stored only as a `modal_predicate`'s proposition.

It is wired at every read entry, and the enumeration is the whole of the guarantee:
`sentexes-matching`, `ask`, `prove`, `query`, the anytime `ask-within` /
`prove-within`, and levels 6 and 7 of the lookup stack ([levels.md](levels.md)), which
are the two that claim to be the engine's own dispatch. One shared step
(`quasiquote/prepare-goal-for-read`) does it for all of them, because the failure mode when
an entry omits it is not a wrong answer but an **empty** one — the compound is matched
against a store that holds a symbol, and nothing comes back, which is
indistinguishable from a KB that was never told.

Two paths resolve a NAT the same way — dedup, never mint — without being query reads,
through `nat-read/resolve-for-read`, which answers nil when a NAT was never minted rather
than a sentence carrying the `no-match` sentinel. `handle-of` reads the constant `ist`
stored, so a lookup of the compound finds the stored sentex. `assert-inert` stores the resolved
sentence, so an inert record keys on the constant every read reifies to instead of a
compound no read finds, and refuses a NAT this KB never minted (`:unminted-nat`) — it
never mints, since a `natFormula` is a belief-carrying write this entry point does not do.
`canonical-sentex` resolves before it canonicalizes, so its content identity agrees with
`handle-of`; a NAT with no minted constant has no canonical stored form yet, and the
compound stands.

### A NAT resolves under the reader's merges

A read resolves an expression for the context it reads from, and a write for the context
it stores in (`CxUniverse` for a caller that names none). `nat-read/map-rows` reads the
map from every context, so a reader that does not see `CxUniverse` still finds the constant a mint
stored there. The merges applied to the expression are the ones the reader sees. A
`natFormula` row answers when its expression, normalized under the reader's merges, is the
expression's normal form there, and either the row is stated (a premise, superseded or
not) or the reader sees the row's context. A migration twin is not stated, so it answers
only where its merge is visible. The stated rows are probed once per spelling the reader's
equality classes give each symbol argument (`class-spellings`), one spelling when no
argument has merged. A compound `(rewriteOf T E)` target is read the same way
(`rewrite-target`), except that a stated row answers only where the reader sees its
context: `(rewriteOf Mary (MotherFn Muffet))` in `CxStory` resolves the application in
`CxStory` and below, and not in `CxUniverse` or a sibling of `CxStory`. A use of a
constant `K` minted for the expression before such a reader saw the `rewriteOf` takes
the merge `(rewriteOf T K)`, derived from the `rewriteOf` and the use and placed where
their contexts meet, wherever `T` is the target the placement reads; the equality
migration folds the use onto `T`. `chain/sync-values!` places it as it places a
`:monotonic` value's merge ([below](#the-corresponding-predicate)): the `rewriteOf`'s
arrival, a use of `K` and a `genlCx` move queue `K`
(`nat_test/a-compound-rewriteof-reads-the-same-in-every-order-of-rewrite-use-and-edge`).
A use written while the `rewriteOf` was visible stores `T` and keeps it after the
`rewriteOf` is retracted. With
`(sameAs Apple Pomme)` in `CxUniverse`, a reader that does not see
`CxUniverse` leaves `(FruitFn Pomme)` unresolved; with the merge in the reader's own
context, `(FruitFn Pomme)` resolves to the constant minted for `(FruitFn Apple)`.

## The corresponding predicate

An ontology that reifies `MotherFn` usually also has `motherOf`, and the two are one
claim written twice. `(functionCorrespondingPredicate F P N)` says so: `F` maps
`a₁ … a_M` to `V` exactly when `(P a₁ … a_{N-1} V a_N … a_M)` holds. `N` is 1-based
over `P`'s arguments and always stated, so `(functionCorrespondingPredicate StreetCornerFn
streetCornerOf 1)` makes `(StreetCornerFn Xing North)` the `Lot` of
`(streetCornerOf Lot Xing North)`.

The common case is a binary predicate with the value second, and
`(functionCorrespondingBinaryPredicate MotherFn motherOf)` states it. A `core.txt` rule
concludes `(functionCorrespondingPredicate MotherFn motherOf 2)` from it, and the engine
reads only the ternary. The example is the shipped one: `resources/kb/upper/life.txt`
states `motherOf` and `fatherOf` with `MotherFn` and `FatherFn` beside them, so a KB that
loads the starter can name somebody by their role before it knows their name.

Two `functionalInArg` marks constrain the ternary. A function and predicate pair has one
position (`functionalInArg` at 3), and a predicate and position have one function
(`functionalInArg` at 1). Two positions for one pair are a `:functional` nogood, and
`try-assert` refuses the second
(`nat_test/two-positions-for-one-function-and-predicate-collide`). The declaration is
forced-monotonic, so neither side of the nogood loses and both stay believed. Two
functions for one predicate and position collide the same way
(`nat_test/two-functions-for-one-predicate-and-position-collide`). One function may still
correspond to several predicates, and the rest of this section says how each reader
reads them.

It is read in **both** directions, and that is the point: a KB told only one of the two
spellings can otherwise reason with only that one.

- **value → term.** A believed `:monotonic` `(motherOf Muffet Mary)` reifies
  `(MotherFn Muffet)` to `Mary` for a write or a read in a context that sees the fact. The
  expression names the object the KB already has a name for rather than minting a second
  one beside it, so the correspondence is a *computed* `rewriteOf` target — the same
  protocol, looked up through the predicate instead of declared per expression. It is
  consulted before the dedup probe, because a real term outranks a placeholder. A value
  only `:default` facts name resolves no write (`nat-read/correspondence-value` reads the
  class off each fact's handle): the write mints the placeholder, and the value reaches
  the placeholder's uses as copies (below). A read of an application nothing minted
  resolves to the one value the visible facts name, whatever its class.
- **term → value.** When no value is known, the mint proceeds and the constant is
  **projected** back onto the predicate: `(motherOf Muffet K)`, derived from the
  declaration and `K`'s `natFormula` map under the `functionCorrespondingPredicate`
  informant and placed where CxUniverse and the declaration's context meet
  (`res/exception-aware-placements`), as a firing is placed. So the placeholder answers
  `motherOf`'s questions instead of being a term nothing says anything about. The
  alternative — minting the constant and leaving the predicate unstated — makes the
  placeholder invisible to every question the predicate answers. The projection is
  placed after the mint stores the result types, since the projected literal is
  arg-checked against them; a projection an argument declaration convicts is stored and
  held, as a convicted firing is, and the argument-hold refresh releases it. Each
  declaration that yields one projected sentence adds its own justification to that
  sentence, and two predicates yield two sentences. A projection is dropped with the last
  of its supports.

**The two meet at the merge, and that is what makes the order stop mattering.** Three
things can arrive in any order — the application, the fact naming its value, the
declaration — and each of the three landing last has an arm:

| Last to arrive | What happens |
|---|---|
| the application | reifies to the believed `:monotonic` value, and nothing is minted; beside a `:default` value only, mints `K`, which takes copies as the next row says |
| a `:monotonic` fact | `(rewriteOf V K)`, derived from the fact and the declaration and placed where their contexts meet, retires the placeholder there, and the equality migration folds every use of `K` — its `natFormula` map included — onto `V` |
| a `:default` fact | each fact and each rule naming `K` takes a copy with `V` in `K`'s place, derived from the use, the fact and the declaration and placed where the three contexts meet; nothing is merged, so `K`'s own sentexes stay believed |
| the declaration | each constant already minted for `F` is projected, then merged with or copied onto its value as the two rows above say |
| a use of `K` | takes its copy beside each visible `:default` value, as the `:default` row says |

The copies and the merges are derivations `chain/sync-values!` places
(`nat_test/a-default-value-reads-the-same-in-every-order`). A write that names `K` or a
value fact queues the constants it moves (`nat-read/note-values`, behind
`nat-read/values-reachable?`, two functor counts), and so does a settle, over the handles
whose labels moved, the facts a stored or removed defeat moved with no relabel, and the
facts and uses an `except` that arrived or left hides or shows
(`nat_test/a-default-value-whose-rival-is-defeated-or-excepted-takes-its-copy-in-every-order`,
`nat_test/a-use-whose-except-is-retracted-takes-its-copy-in-every-order`).
Each queued constant is brought to what the stored declarations, facts and uses owe: a
wanted derivation missing is placed and an owned justification no longer wanted is
dropped. A chaining run inside `chain/*rollback-scope*` places the missing derivations
and drops nothing. It queues each constant that owes a drop back for the settle, because a
rollback restores no record below the write's mark
(`chaining_contracts_test/a-stopped-run-that-re-decides-a-value-copy-leaves-the-kb-as-it-found-it`).
The settle chains from what it places, except
under a `{:chain? false}` write, which places the derivations and chains nothing from them.
The cost is linear in the uses of the queued
constant and reads no other constant's uses
(`perf/default-value-beside-uses`). A copy rests on its fact, so a defeat of the fact
takes every copy OUT through ordinary labels
(`nat_test/a-default-value-defeated-takes-every-copy-out`). A copy's strength is capped by
its antecedents as a firing's is. A copy of a forced-monotonic sentence over a `:default`
fact is convicted void, and an equality sentence naming `K` takes no copy. A fact
re-asserted `:monotonic` brings the merge, whose migrated twins dedup onto the copies and
add a justification to each. A re-assert never lowers a class, so the way back is a
retraction and a `:default` assert: the merge leaves with the fact, and the copies are
derived again
(`nat_test/a-default-value-made-monotonic-and-default-again-ends-where-it-started`).

**A value applies where it is visible.** The mint reads the values the corresponding facts
visible from the writing context name, each spelled under that context's merges
(`nat-read/correspondence-value`), and a read does the same from the reading context. A
merge or a copy is placed only where the placement context reads exactly one value beside
the placeholder, through the one correspondence the merge or copy was drawn from
(`chain/sync-values!`), decided over the believed facts that context sees. With
`(motherOf Muffet Mary)` in `CxStory` and a write of `(MotherFn Muffet)` in `CxUniverse`:

| The fact's class | A write in `CxStory` | The placeholder minted in `CxUniverse` | A goal in `CxStory` naming the application or `K` |
|---|---|---|---|
| `:monotonic` | reifies to `Mary` | retired in `CxStory` by `(rewriteOf Mary K)`; `CxUniverse` reads `K` | reads `Mary`, the representative |
| `:default` | mints `K` | stays; each use of `K` has a copy naming `Mary` in `CxStory` | reads both spellings, `K` and `Mary` |

Both hold in every arrival order, a `genlCx` edge included
(`nat_test/a-value-in-a-context-retires-the-placeholder-there-alone-in-every-order`). A
context that does not see the fact reads `K` alone
(`nat_test/a-context-that-does-not-see-a-default-value-reads-the-placeholder-only`). The
goal's second spelling is a second lookup: `res/visible-matches` answers a goal naming a
reified object constant with the matches of the goal spelled with the one value outside
`K`'s class the reading context sees (`res/copied-values`), behind the declaration
functor count. A copy rests on the use, so no copy runs from `V` back to `K`. A merge's
restatement of a corresponding fact is no second value for a context that reads the
original and the restatement as one term. A `genlCx` edge stored, removed or relabelled
queues the constants named by what the contexts of its `:gained-below` set store
(`special/note-moved-values`): a placement the move creates or retires has an ingredient
there, since a set of ingredients in `super`'s ancestor set has its placement at `super`
or above already.

The merge is a `rewriteOf`, so `V` represents the class
([defenses.md](defenses.md#a-placeholder-is-retired-by-rewriteof-not-equals)). A minted
constant is `:opaque` to `wff`'s same-role check — the naming invariants are conventions
over names a person *chose*, and what a reified NAT denotes is settled by its materialized
result types — so merging one into an individual is the intended move, not the import bug
that check catches.

**Several believed declarations for one function decide nothing at the mint.** Two
correspondences are two different claims about what `(F a…)` denotes, and choosing
between them would have to key on a handle, which belief may never do — so neither is
read and the application mints as if none were declared. The mint is projected through
each declaration, which also picks nothing
(`nat_test/two-declarations-for-one-function-decide-nothing`). A rule and a goal read
through every one ([below](#a-rule-or-a-goal-that-names-an-open-application)). The same
for a value: `correspondence-value` answers only when the context reads exactly one, and
a context reading two values beside a placeholder neither merges nor copies it. The same for a `rewriteOf` target:
`rewrite-target` answers nil when the believed `(rewriteOf T E)` declarations name two
targets, and two declarations of one target are one answer.

**A declaration respells where the reader sees it.** A rule's stored row reads the
declarations its own context's `genlCx` ancestor set holds, and a goal reads the ones its
reading context's ancestor set holds. A rule also reads each declaration its context
does not see at the contexts that see both: the spelling is stored at the maximal common
descendants of the rule's context and the declaration's (`res/exception-aware-placements`),
justified `respell` by the rule and the declaration, as a firing is placed. A rule stored
in `CxUniverse` beside a declaration in `CxSide` is held in `CxUniverse` and respelled in
`CxSide`; a goal read in `CxUniverse` answers nothing. A `genlCx` edge stored, removed or
relabelled re-spells the rules that apply a function a declaration in the moved contexts
declares, and, when a moved context stores a rule, the rules of every declared function
(`special/move-families`, `chain/reconcile-corresponded!`): the `:held` rules applying
the function and the rules a correspondence of it respelled, with no read of its facts
or constants
(`nat_test/a-correspondence-respells-a-rule-where-its-context-meets-the-declarations-in-every-order`). A query
context or a variable context reads every declaration through a predicate variable, so
each reader matches the declarations it sees. The value side reads the declarations the
context sees as well: a write or a read reifies an application through the declarations
its context sees (`res/correspondence-of`), and a projection, a merge or a copy is placed
where its declaration is seen.

The declaration is read through the **index**, not a taxonomy cache. It is consulted
once per NAT, where the reify is already probing for a `rewriteOf` target and a dedup,
and a KB declaring none pays one O(1) functor count per assert
(`res/any-corresponding-predicates?`). Nothing to integrate means nothing for `recover`
to rebuild — a correspondence works across a restart because the declaration is a
stored fact and always has been; `recover` holds the rules below again
(`checks/force-stored!`). It bites only for a `reifiable_function`: an undeclared
function's application is a raw compound the reify pass never visits.

### A rule or a goal that names an open application

The engine does not pattern-match a function application in an antecedent or a goal.
`res/kb-sentex`, the constructor every store and lookup builds a sentex through, respells a
rule whose antecedents hold an open application `(F a…)` of a `reifiable_function`
(`res/respell-applications`). The application becomes a variable `?v`, and the literal
the correspondence makes equivalent to it, `(P a… ?v)` with `?v` at the declared position,
joins the antecedents. Inner applications are respelled first, and one application
written twice is one variable. The consequent stays as written, for every rule kind,
except that an application an antecedent names takes that antecedent's variable:

```clojure
(implies (tagged (FruitFn ?t)) (ripe (FruitFn ?t)))
;; is stored as
(implies (and (fruitOf ?t ?fruit) (tagged ?fruit)) (ripe ?fruit))

(implies (bears ?t ?o) (grownIn (FruitFn ?t) ?o))
;; is stored as written
```

An `equals` literal one of whose sides is an open application is the corresponding
literal itself, with the other side at the value position: `(equals ?food (FruitFn ?t))`
is `(fruitOf ?t ?food)`, in a rule and in a goal, and searches no equality.

The variable is named for the function, its `Fn` suffix dropped and its first letter
lowercased, with a hash of the application appended where the rule uses the name already.
Canonicalization renames it with the rule's other variables, so the two spellings store
one handle, and `why` and the browser show the predicate form. The DFS prover, the node
engine and rete read the stored rule, so none of them matches an application. A forward
rule concluding about an application mints it at each firing
([Derivation path](#derivation-path)); with a correspondence, the mint's projection states
the value through the corresponding predicate. A backward rule concluding about an
application answers no goal over it (Derivation path).

A function with several believed correspondences gives the rule one spelling per
correspondence, and a rule applying several such functions one per combination
(`res/rule-respellings`). The row keeps the spelling that reads each function's
content-least correspondence, so both written spellings still store one handle. Each
other spelling is stored beside it, justified `respell` by the rule and the declarations
it reads (`chain/sync-rule-respellings!`), so the rule answers through the union of its
correspondences and a declaration leaving takes its spelling with it. A read picks no
correspondence, so the union is order independent.

A rule whose antecedents apply a function its context sees no correspondence of is stored
as written and held in the `:held` forced set (`nat/held-application?`, written by
`checks/force-sentex!`): it stays IN in the network, so the spellings resting on it at
the meet contexts hold, and it is not believed, so it fires nothing and its application
is never matched as written ([nmtms.md](nmtms.md#the-forced-monotonic-set)).
A rule whose antecedents hold a variable-functor application, `(tagged (?fn ?t))`, is held
the same way ([What reification does not cover](#what-reification-does-not-cover)), except
where the compound sits in a sentence position (`res/formula-position?`). An application
inside an `unknown`, `thereExists`, `forall`, `exists`, `ist` or aggregate antecedent is not
respelled, so a rule holding one is held too. A quoting function's argument and a quoting
predicate's payload are mentions, neither respelled nor held. A generator's consequent
rule is not read: the rule it generates is respelled or held when it is stored.

A `modal_predicate`'s proposition is a mention on every path. An application in it stays
as written in an antecedent, a consequent and a goal, holds no rule, and is minted by no
firing ([Write path](#write-path)); the agent position is read as a term. So
`(implies (believes ?a (likes ?a (FruitFn ?t))) (fanOf ?a ?t))` is stored as written,
needs no correspondence, and matches the stored `(believes Ann (likes Ann (FruitFn
Apple)))`. A rule concluding `(believes Bob (likes Bob (FruitFn ?t)))` from `(tagged
(FruitFn ?t))` stores the application in the conclusion although its antecedent gives
`(FruitFn ?t)` a value, so the derived belief and the asserted one are one sentex
(`nat_test/a-modal-proposition-keeps-its-applications-as-written-on-every-path-in-every-order`).
Projecting the proposition into the agent's context is `BeliefProjectionProver`'s
([belief.md](belief.md#where-the-barrier-sits-and-what-it-covers)). `ist` and every other
sentence position are not mentions. An `ist` sentence holds in its context, so a ground
application in it is reified as one in a sentence stored there, and a rule holding an open
one is held as above. A fixed application in any other sentence position is respelled:
`(holdsIn ?c (tagged (FruitFn ?t)))` under `(arg holdsIn 2 sentence)`.
`kb-integrity` reports each function a held rule applies with no correspondence
([integrity.md](integrity.md#what-an-uncorresponded-function-finding-means)).

The hold does not read a consequent. A variable-functor application in a consequent fires,
and the firing mints the application its bindings make. An application in a consequent's
sentence position, `(believes Ann (grownIn (FruitFn ?t) ?o))`, is stored as written in
the conclusion, as `assert` stores it. An `unknown` consequent fires, and each conclusion
is dropped as `:not-well-formed` and filed in `violations` under the rule's handle, with
or without an application in it.

The rule follows the correspondence in both directions:

| The correspondence | The rule |
|---|---|
| arrives, the first its context sees | is respelled in place, leaves the `:held` set, and the settle joins it |
| arrives beside another | adds its spelling, which the settle joins; the row moves to the content-least spelling |
| leaves, another still believed | takes its spelling away, and the firings it made with it |
| leaves, the last its context sees | returns the row to its written spelling, held again |

`assert` records a respelled rule's written spelling on its row (`integrate/spellings-key`,
the record a permuting mark keeps), and the move back restores it. A row holding premise
assertions in two spellings splits, each assertion returning to its own spelling. The rows
are found as a reifiable mark's are (`chain/reconcile-reified!`), and through the antecedent
index of each predicate a declaration of the function names (`nat/corresponded-rules`).
A declaration arriving runs the move from `nat-maintenance/reconcile-assert`, and one
leaving runs it from `collect-orphans!`, so both arrival orders store the same rule.
A move that changes a rule's antecedents or its hold drops the firings the rule made in
the spelling it left, with the drops it filed in `violations`, and a rule left believed
fires again. A rule whose consequent names an open application is dropped and fired again
at every move, so its conclusions are minted under the marks and correspondences believed
after the move
(`order_independence_test/a-late-reifiable-declaration-re-spells-a-stored-rule-and-re-fires-an-application-head`).
A rule that concluded `(hasCapability ?x (SkillFn ?x))` before `SkillFn` was reifiable
therefore stores the conclusion and the constant the declaration arriving first makes.

The sentence positions a variable-functor rule's hold reads move the rule the same way. An
`arg`, `argN` or `quotedArg` declaration typed `formula` or under it, and a `genl` edge
putting a declared type under `formula`, stored or torn down, re-decide the rules with an
antecedent or a consequent on the declaration's predicate that hold a variable-functor
application (`nat/formula-declared-predicates`, `nat/formula-position-rules`). The move is
the row move above with the hold re-read (`chain/reconcile-formula-positions!`): a rule
left held keeps no firing, a rule left believed fires again, and a rule that also applies
a fixed function moves between its written and respelled spellings. `(implies (holdsIn ?c
(?p Rex)) (heardOf ?c ?p))` is held beside no declaration and believed beside `(arg holdsIn
2 sentence)`, whichever arrives first
(`nat_test/a-formula-declaration-releases-a-held-variable-functor-rule-in-every-order`).

A goal is respelled before it is answered (`res/goal-alternatives`). A function with one
believed correspondence reads its predicate: `prove (grownIn (FruitFn ?t) ?o)` asks
`[(fruitOf ?t ?fruit) (grownIn ?fruit ?o)]`, and its answers bind `?fruit` too. A function
with several reads the declaration and a predicate variable, so the goal answers through
each correspondence and merges the answers:

```clojure
(favoriteFood Ann (FruitFn ?tree))
;; with fruitOf and producesFruit both declared, asks
[(functionCorrespondingPredicate FruitFn ?fruitPredicate 2)
 (?fruitPredicate ?tree ?fruit) (favoriteFood Ann ?fruit)]
```

A variable-functor application reads every function's declarations the same way:
`(favoriteFood Ann (?fn AppleTree))` asks `(functionCorrespondingPredicate ?fn
?fnPredicate 2)`, `(?fnPredicate AppleTree ?fnValue)` and `(favoriteFood Ann ?fnValue)`,
and binds `?fn` to the function. Declarations putting the value at different positions
are different literal shapes, so the goal runs one conjunction per distinct position and
merges their answers, each projected onto the variables every conjunction binds:
`(owns Bob (?fn Xing North))` answers `?fn StreetCornerFn` from
`(functionCorrespondingPredicate StreetCornerFn streetCornerOf 1)`,
`(streetCornerOf Lot Xing North)` and `(owns Bob Lot)`. A variable-functor compound in a
position an `arg`, `argN` or `quotedArg` declaration types as a `formula`
(`res/formula-position?`), or in a construct's argument, is a sentence pattern and is not
expanded: `(believes Ann (?p Rex))` matches `(believes Ann (dog Rex))`. An `and` goal is
read as its conjuncts.

`prove`, `provable?`, `query` and their bounded forms merge the conjunctions. The readers
that report on one search, `query-status`, `abduce`, `search-tree`, `compare-tacticians`
and `prove-within`, refuse a goal that needs more than one with a `:shape` refusal
(`quasiquote/prepare-conjunction-for-read`). A goal applying a function with no
correspondence answers nothing: the application is replaced by `nat-read/no-match`. A
**ground** application in a goal keeps the
[read path](#read-path)'s reify, which resolves it to the constant, value or `rewriteOf`
target the KB holds for it; with a correspondence the respell reaches the same term
through the projection or the value's fact. `ask` reads one sentence and expands no rule,
and a stored fact holds a constant rather than an application, so an open application in
an `ask` goal finds nothing.

## Display / export

`nat/expand-expression` reverses the map, recursively rebuilding a reified constant
back to its functional expression — `(color (FruitFn AppleTree) Red)`, never a raw
`nat/` symbol. Non-reified NAT content is returned unchanged (same identity); only
reified NAT-bearing forms are rebuilt.

**A constant is never what a reader sees.** It is an implementation of term *identity*
— a `nat/`-namespaced hash is not a name anybody wrote — so a display layer resolves
it, and `vaelii.core` carries the pair that lets one: `reified-term?`, a pure test on the
reserved namespace that adds no work on a KB that has minted none, and
`term-expression`, **one hop** of the map. One hop rather than the whole expansion,
because a caller rendering each term individually — linking it, colouring it — recurses
and keeps every level addressable; `expand-expression` is the flat answer for a caller
that wants the form and not the parts. The browser does the former, showing the
expression with **bold parens** and the opening one linking to the constant's own page
([web.md](web.md), "A reified term is never shown as its constant").

## Rename and remove — keeping the 1:1 invariant

**Rename** is an equality assert. `(rewriteOf MalusTree AppleTree)` retires
`AppleTree`; the equality **migration** ([equality.md](equality.md)) restates every
sentex naming it, including `(natFormula K (FruitFn AppleTree))`, whose rewritten twin
is `(natFormula K (FruitFn MalusTree))`. `K` stays **stable** — it is not the term
renamed — so nested NATs referencing `K` need no cascade. A rename can collapse two
NATs onto one expression; `merge-colliding-nats!` (behind the reified-constant presence
check) restores the 1:1 invariant by merging each colliding group's constants into its
lexicographically-smallest survivor via a further equality, which migrates their uses.
A collision holds where a context sees both rows, so the repair runs per context:
`merge-collisions!` visits the contexts holding the rows most general first and states
each equality in the context that reads the collision, skipping a pair a visible equality
already merges. A merge stated in `CxQ` joins `(FruitFn AppleTree)` and
`(FruitFn MalusTree)` in `CxQ` alone, and `CxUniverse` keeps the two constants apart.
Three writes can join a collision, and each reads only the rows it can have joined: an
equality reads the rows naming its terms' classes, a mint's `natFormula` the rows naming
its expression's merged arguments, and a `genlCx` edge the rows its migration restated
below its lower context. A collision an import stored stays until a caller asks
`colliding-constant-groups`
([defenses.md](defenses.md#the-collision-merge-reads-the-merged-class-not-the-whole-map)).
The retired spelling stays a usable *question*: a goal naming the old term
goal-rewrites to the new expression and still resolves to `K`.

The invariant holds **per reify namespace**. An expression written in a context slot maps
to a `cx/` constant beside the `nat/` one its argument-position use maps to, and every
`E → K` read and the collision grouping take the namespace they want
([context-nat.md](context-nat.md#one-constant-per-expression-per-namespace)).

A collision can also run the other way — one constant mapped to two expressions — and
until the repair reaches it, **every reader of the map takes the same one**: the
content-least (`nat/authoritative-expression`, the choice `dedup-constant` makes on the
other side of the map). That is what keeps the orphan sweep coherent: `orphan?` decides
orphanhood against the expression `bookkeeping-handles` then computes the retraction set
from, so no verdict about one expression retracts records belonging to another.

**Remove** is retraction. When the last stored use of a reified NAT goes, its `natFormula` map
and materialized types would dangle a raw `nat/` symbol — so `remove-orphaned-nats!`
(run after `retract!` and `edit!` behind the reified-constant presence check, suppressed
while already removing orphans)
collects every constant whose only remaining **stored** sentexes are its own bookkeeping.
Stored, not believed: a use sitting OUT revives when the defeat above it lifts, and an
inert use (a labeling's choice head) has no TMS node at all — either would dangle if a
sweep counted only belief, and re-reifying the expression would mint a second constant
beside the first. A
**correspondence projection** is bookkeeping for this: like a result type it states what
the constant *is*, and counting it as a use would make every placeholder immortal.

**Bookkeeping is decided by authorship, not by shape.** `K`'s own sentexes are its
`natFormula` map plus exactly what `mint-nat!` wrote about it, and `nat/minted-for`
re-derives that set the way the mint derived it: `(T K)` for each believed `(result F
T)`, `(genl K T)` for each `(genlResult F T)`, `F` being the function of the expression
`K` maps to. A correspondence projection, derived from `K`'s map and a declaration
(`nat/projected-from?`), is `K`'s own too, and a merge `(rewriteOf V K)`, derived from a value fact and
a declaration, counts as a use. A record the argument-type entailment
derives off `K`'s own sentexes alone is `K`'s own as well (`nat/entailed-from?`), and
leaves with them. Two such records are a membership an argument declaration on
`natFormula` or a `resultArg` of `F` derives off the map, and the `(predicate K)` the
declaration on `genl` derives off a materialized `(genl K T)`. The test follows the
source of each justification, so a record entailed off such a record is `K`'s own too;
a record with one justification resting on a use, or a rule's conclusion, is a use.
Everything else naming `K` is somebody's
assertion whatever its arity — `(prime K)` is a claim about `K` exactly as `(noted Author
K)` is, and a sweep reading arity alone would retract the claim along with the constant.
The set is computed behind a **delay**, and the `natFormula` clause is tested first: a
constant a teardown collects has its map and nothing else left, so the common answer is
reached without reading the declarations at all. The one constant this keeps
alive that a shape test would have collected is one whose `result` declaration was
retracted after the mint: the materialized `(T K)` is then a believed sentence no rule
supports and nobody has withdrawn, and holding `K` for it is the direction to err in.

**The answer is realized before the caller acts on it.** `bookkeeping-handles` decides
membership by re-reading `K`'s `natFormula`, and its caller retracts that map. A lazy
answer read after the map's retraction calls every later sentex "not bookkeeping" and
leaves it stored, naming a collected constant, in the term-index orders that yield the
map first. Both the per-constant set and the sweep's per-round orphan list are realized
before the round's first retraction.

**The sweep asks about the region the teardown removed, not about the KB.** A constant
becomes an orphan only when something that referenced it goes, so the candidates are the
constants the departing sentexes named (`orphans-named-by`), and each is settled by one
inverted-term-index read — `orphan?`, since a constant's uses, its map and its
materialized types are all sentexes naming it ([indexing.md](indexing.md)). What a
retraction costs is the size of what it removed, and a KB that has minted a hundred
thousand NATs the retraction is not about adds nothing to it.

**A `cx/` context constant is collected by the same sweep**, with its extent as one more
source of liveness: `orphans-named-by` reads a removed sentex's **context** beside its
sentence, and `orphan?` reads the extent, one O(1) `count-in-context`, before the term
index ([context-nat.md](context-nat.md#orphan-collection-a-context-is-a-place-as-well-as-a-name)).

The removals reach the sweep through `integrate/*removed-sink*`, the record the removal
choke point fills while a teardown runs, because they arrive from three places: the
dependency-directed sweep; the settle that follows it, where an exception that starts
holding blocks a justification and what it solely supported is deleted
([exceptions.md](exceptions.md)); and the orphan sweep's own retractions. The third is
how **the region grows with the fixpoint** — removing an orphan removes the `natFormula`
sentex holding its expression, so a reified NAT nested in that expression is a candidate
on the next round. A cascade is therefore found by the rule that found the first orphan,
and the loop ends on the round that removes nothing.

`preview`'s rollback is the one caller that asks the whole KB instead
(`orphaned-constants`): the batch it undoes runs with the settle sweep off
([preview.md](preview.md)) and reaches the orphan sweep at no point, so the claim it owes
— the KB is as it was found — is about all of it rather than about one teardown's region.

## A reifiable mark moving

The write path spells a sentence by the marks believed when it is written, so a
`(reifiable_function F)` mark that starts or stops holding after sentences naming `F` are
stored changes how those sentences would be written. The settle that follows the move
re-spells them (`chain/reconcile-reified!`), so the store holds what a KB told the same
sentences with the mark already in place holds:

| The mark | What the settle re-spells |
|---|---|
| arrives: asserted, derived, or revived from OUT | each stored ground application of `F` becomes its term, minted as `assert` mints it |
| leaves: retracted, or OUT | each use of a constant minted for `F` names the application again |
| is defeated or excepted at or above a use's context, so no reader of the use believes it | the use is spelled as written, and its constant is collected |
| is defeated or excepted below a use's context, so the use's readers disagree | the use stays as written, and the reified use is stored beside it, justified `respell` by the use and the mark |

The move is noted where the mark changes in the taxonomy (`special/note-permuting-moves!`,
beside the permuting marks), on the `:respell` queue the settle drains. The region is read
off the inverted term index (`nat/respell-region`): every stored sentex holding an
application of `F`, and every use of a constant whose expression holds one, at any
nesting. A constant's own bookkeeping is not a use and does not move. A quoting
predicate's payload is a mention and does not move either. Each row is re-spelled by
expanding its constants and reifying again (`nat/respelled`), which is the write path's
own walk. A rule's antecedents move the same way: a rule whose antecedents hold an open
application of `F` is respelled through `F`'s correspondence or held, and a rule whose
consequent holds one fires again
([A rule or a goal that names an open application](#a-rule-or-a-goal-that-names-an-open-application)).

- **A row moves in place** when no row holds its new spelling, keeping its handle,
  premise mark and justifications (`integrate/move-row!`, the move a late `symmetric`
  mark makes). Otherwise it folds into that row. A re-asserted use therefore dedups to
  the moved row instead of storing a second one.
- **A nested application is re-keyed.** A constant's name hashes its expression, and the
  expression holds its inner applications already reified. A use stored while the inner
  function was undeclared names the constant of the raw inner application. When the inner
  mark arrives, that use moves to the constant of the re-keyed expression, and the first
  constant is left with its bookkeeping alone.
- **The constants the moved rows stop naming are collected** by the orphan rule of
  [Rename and remove](#rename-and-remove--keeping-the-11-invariant), over the spellings
  the rows moved off. A settle has no teardown entry point, so each bookkeeping handle is
  taken out through `integrate/take-out!`.

**A map that leaves while uses still name its constant re-spells those uses.** The region
walk reaches a constant only through its stored `natFormula` map, so a map retracted
before the mark would leave its uses spelled with a constant nothing expands. The teardown
that removes the map reads the expression off its removal record and re-spells each
remaining use, and each use of a constant whose expression names the departed one, with
the departed constant written as that expression (`chain/reconcile-stranded!`, run from
`nat-maintenance/collect-orphans!` before the orphan sweep). Under a believed mark the
use keeps its spelling and the constant is minted again, map included, under a new
handle. With the mark gone the use names the application. The mark and its maps
therefore leave the same store in any retraction order.

A reader that does not believe the mark reads no row naming a constant minted for `F`,
the mint and its result types included, and a reader that believes it reads no row holding
an application of `F` unreified (`res/without-unbelieved-spellings`). A goal is reified
with the marks its reader believes (`nat-read/maybe-reify-for-read` given the reader). The
readers are found as for a permuting mark
([canonicalization.md](canonicalization.md#a-mark-a-reader-does-not-believe)), and a write
naming such an application queues the function for the settle (`nat/queue-split-uses!`).

The settle reaches stored rows, believed or not, so a use sitting OUT is spelled as the KB
spells it when its defeat lifts. A declaration written before any application finds only
its own declarations about `F`, and a KB declaring no reifiable function queues nothing.
A store recovered from rows written before this re-spelling existed keeps them: `recover`
re-spells nothing, and retracting the declaration and asserting it again runs the sweep.

A `(result F T)` or `(genlResult F T)` asserted after constants were minted for `F`
materializes `(T K)` or `(genl K T)` on each of them, as the mint does when the declaration
comes first (`nat/reconcile-nats!`).

## Where it lives

- `vaelii.impl.nat-read` — below `provers`, so `BeliefProjectionProver` calls it: the
  detectors (`reified-nat-symbol?`, `reifiable-function?`, `reifiable-ground-nat?`), the
  `E → K` lookups (`dedup-constant`, `rewrite-target`, `correspondence-value`), the shared reify walk (`reify-in`), the read mode
  (`maybe-reify-for-read`, `reify-existing`, `resolve-for-read`), and `note-values`, which
  queues the constants a write or a relabel moves the values of. Reads through
  `resolution` and `reads`.
- `vaelii.impl.nat` — `held-application?`, the lookups `nat-expression`, `result-types` /
  `genl-result-types` and `corresponded-rules`, `expand-expression`, the write mode
  (`maybe-reify-nats`, `mint-nat!`), and the rename / remove / correspondence maintenance — the orphan questions among it
  (`orphan?` per constant, `orphans-named-by` over a region, `orphaned-constants` over
  the KB, `reified-nats-in` for the candidates) and `reconcile-nats!`, the collision
  merge and the declared result in the order the assert path runs them. Reads the store,
  taxonomy and belief directly, and reaches assertion through `wiring/assert-sentence`.
- `vaelii.impl.resolution` — the correspondence reads (`correspondence-of`,
  `believed-correspondences`, `corresponding-values`), the second spelling a goal naming
  a placeholder reads (`copied-values`), and the respell of a rule's and a goal's open applications
  (`respell-applications`, which `kb-sentex` runs, and `respell-goal-applications`).
- `vaelii.impl.nat-maintenance` — the sequencing the write paths run around that:
  `reconcile-assert` once a sentence is stored (`reconcile-nats!`, the correspondence
  derivations it moves, the rules a correspondence declaration respells, then the
  structural `genlCx` edges the fact entails and the merges those edges license) and
  `collect-orphans!` on the `retract!` and `edit!` sweeps, which respells the rules a
  removed declaration respelled, re-places the derivations the removal moved, and loops
  `remove-orphaned-nats!` to a fixpoint. The teardown entry point is an argument, so the
  engine requires nothing above it.
- `vaelii.core` — the reify call sites: the write-path reify at the head of `assert`,
  the read-path reify at the query entries, and one call into
  `vaelii.impl.nat-maintenance` per maintenance site.
- `vaelii.impl.chain` — `reify-conclusion`, the derivation-path reify `place-conclusion`
  runs on a fired conclusion, with the checks asked before the mint. It runs only when
  `nat/names-reifiable-nat?` holds, a walk that rebuilds nothing. Also `reconcile-reified!`, the
  settle's re-spelling when a reifiable mark or a correspondence moves, and
  `sync-values!`, the projections, merges and copies of the queued constants.
- `vaelii.impl.integrate` — `*removed-sink*`, the removal choke point's record of what a
  teardown took away, which is the region the orphan sweep runs over.
- `vaelii.impl.special` — the two function-kind prop marks, the correspondence's
  wff-only entry, the equality-arm skip for a compound-arg `rewriteOf`, `derive-merge`,
  which a merge is stored through, and `note-moved-values`, the constants a `genlCx` move
  queues.
- `vaelii.impl.checks` — `convicting-result-type`, the arm `args-problem` and
  `genls-problem` read a compound argument through ([argtypes.md](argtypes.md)), and the
  `force-sentex!` arm that writes the `:held` set from `nat/held-application?`.
- `vaelii.impl.quasiquote` — `prepare-conjunction-for-read`, the goal respell.
- `vaelii.impl.wff` — `function-decl-problems`, `correspondence-problems`, the
  `:opaque` role a minted constant carries through the same-role check, and the
  `equality-problems` waiver for a compound-arg `rewriteOf`.
- `resources/kb/upper/core.txt` — the seven NAT predicates, declared and documented.

## What reification does not cover

- **An unreified or open NAT is not structurally indexed.** Reification is what makes a
  NAT findable, so a NAT that cannot be reified is reachable only through the coarser
  keys ([indexing.md](indexing.md)).
- **An existential rule head is not skolemized here** ([skolem.md](skolem.md)).
- **A rule's open application in an antecedent is read only through a correspondence.**
  With no believed `functionCorrespondingPredicate`, a rule whose antecedents apply the
  function is held inert and a goal applying it answers nothing
  ([A rule or a goal that names an open application](#a-rule-or-a-goal-that-names-an-open-application)).
  An application inside an `unknown`, `thereExists`, `forall`, `exists`, `ist` or
  aggregate condition is held with one too. One inside a `modal_predicate`'s proposition
  is matched as written, and only a stored belief spelled the same way answers it.
- **A rule moves between its spellings when a declaration is stored or torn down, or a
  `genlCx` edge moves.** A declaration derived by a rule, or hidden from a reader by an
  `except`, moves no rule. The ternary a `functionCorrespondingBinaryPredicate` concludes
  is derived, so a rule stored before the binary declaration keeps its written spelling
  and fires nothing through it; a rule stored after it is respelled as usual. The
  respell reads the reifiable mark unscoped, so a reader that does not believe the mark
  reads the rule respelled.
- **No rule reads a variable-functor application in an antecedent.** A rule whose
  antecedents hold `(?fn a…)` outside a sentence position is held inert and fires nothing;
  only a goal expands one.
- **A backward rule's consequent does not meet a respelled goal.** A goal over an
  application, or over the constant minted for it, does not reach a backward rule whose
  consequent names that application.
- **A sentence position moves a rule only when its declaration or `genl` edge is stored
  or torn down.** A declaration a rule derives re-decides no rule as it arrives, and one
  hidden from a reader by an `except` re-decides none.
- **A variable-functor goal matches no stored compound.** `(likes ?x (?f Bob))` reads only
  the declared correspondences, so a structural application of an undeclared function
  stored as a compound term does not answer it.
- **An `unreifiable_function`'s application is computed, not reified.** A rule matches it
  as written, and the respell does not read it.
- **A forward rule's type antecedent reads no result type.** `ResultTypeProver` answers
  any type, so it lists no functor for the forward join, and a forward rule with a
  `(time_point ?w)` antecedent does not fire when `?w` binds to an `(InstantFn …)` term.
  A backward rule and a goal read the declaration.
- **A context that does not see `CxUniverse` reads no collision repair.** Its reads
  resolve an expression to the content-least constant it reads (A NAT resolves under the
  reader's merges), and the uses of the other constant do not answer there.
- **A spelling rename nested in a quoted compound reaches a reader only through a twin.**
  `class-spellings` varies the symbol arguments at the top level, so a reader that does
  not see `CxUniverse` does not resolve `(Quote (foo Muffet))` through a rename of
  `Muffet` stated in a context it sees.
- **A placeholder is retired in each context holding a `:monotonic` value, separately.**
  With `(motherOf Muffet Mary)` in `CxA` and `(motherOf Muffet Maria)` in `CxB`, a context
  seeing both reads the placeholder as `Mary` and as `Maria`, so it reads the two as one
  term.
- **A reifiable mark leaving does not re-spell a use whose application resolved to a real
  term.** A `rewriteOf` target, a correspondence value and a placeholder an equality
  retired stand where a KB that never declared the function holds the application.

The **measure-evaluating quantity prover** — measure comparison over a `dimensionOf` /
`conversionFactor` table — reads the structural measures an unreified application keeps. It lives
in [quantity.md](quantity.md).
