# Non-atomic terms (NATs)

- **Covers:** how a function-application term reifies to an opaque constant before
  the index sees it, or stays structural when it does not.
- **Not here:** minting a deterministic constant for a rule's existential head →
  [skolem.md](skolem.md); comparing two structural measure terms →
  [quantity.md](quantity.md).
- **Assumes:** sentex, context, taxonomy, predicate metadata →
  [glossary.md](glossary.md).

A **NAT** is a function-application term `(F arg…)` that *denotes an entity* —
`(FruitFn AppleTree)`, `(CapitalOf France)`, `(QuantityFn 5 Meter)`. Pure has no
first-class function terms in a stored sentence; every stored token is atomic. NATs
are supported by **reification**, and functions split by declaration into two kinds.

- `(reifiableFunction F)` — **object-denoting**. A ground `(F a…)` is a **reified NAT**: it
  reifies to an opaque `nat/`-namespaced constant `K` *before it reaches the index*,
  so the reified NAT autoindexes exactly like a hand-minted symbol.
- `(unreifiableFunction F)` — **evaluated / interpreted**. The application stays a
  **structural NAT** — `(QuantityFn 5 Meter)` keeps its magnitude and
  unit readable for a downstream prover; it is never minted.

`QuantityFn` must **not** be reifiable — reifying it would collapse `5` and `Meter`
into an opaque atom and lose the very structure a unit prover needs.

## The strategy: reify before the index

The invasive way to support function terms is to *structurally index* nested
compounds — change the trie key and `sentex/index-terms` so `(color (FruitFn
AppleTree) Red)` is findable by the nested `FruitFn` occurrence. That reaches further
into the engine than anything else here touches. Reification sidesteps all of it. A reifiable NAT is replaced by an atomic constant on
the write path, so:

- the trie key is unchanged — `(color K Red)` keys `[color K Red]`, K one token;
- `sentex/index-terms` is unchanged — K is an ordinary symbol subterm;
- the reified NAT autoindexes, is retrieved, and is retracted exactly like any symbol.

There is **no structural indexing of unreified or open NATs**: the reifiable path needs
none, because a reified NAT is a symbol by the time the index sees it.

## The data model — all ordinary stored facts

Nothing here is a KV side table. Every mapping is a normal sentex in
**UniverseContext**, so it rides `put-sentex`, the functor / argument roots, and the
inverted term index like any other fact.

| Fact | Meaning |
|------|---------|
| `(reifiableFunction F)` / `(unreifiableFunction F)` | F's kind — a **predicate-metadata mark** (`vaelii.impl.taxonomy` `:reifiable` / `:unreifiable` prop), belief-following like `transitive`/`symmetric` |
| `(termOfUnit K E)` | the constant↔expression map: constant `K` denotes NAT expression `E`. The reverse (`K → E`) index; `E → K` is the inverted term index |
| `(rewriteOf T E)` (compound `E`) | NAT `E` reifies to the existing real term `T` instead of a fresh constant |
| `(resultIsa F T)` / `(resultGenl F T)` | F's output types — materialized on mint as `(T K)` / `(genl K T)` |
| `(functionCorrespondingPredicate F P N)` | F and P state one relationship: `(F a…) = V` exactly when P holds of `a…` with `V` at argument `N` |

`termOfUnit` and `rewriteOf` are **quoting predicates** (`nat/nat-quoting-predicates
= #{termOfUnit rewriteOf}`): their expression argument is a literal NAT payload that
must not itself be reified or type-checked as a term.

`(rewriteOf T E)` overloads the equality/deprecation `rewriteOf`, discriminated by
shape: a **symbol** second argument is term equality (the equality partition — see
[equality.md](equality.md)); a **compound** second argument is a NAT reify-to-term
declaration. The equality integrate arm and `wff/equality-problems` both skip the
compound shape, so it is stored as an inert quoting fact, never entering the closure.

## The reifiable gate

A function's kind is metadata cached in the taxonomy, so the per-sentence gate —
"does the KB declare any reifiableFunction?" — is a free **in-memory set read**
(`nat/any-reifiable-functions?` ⇒ `seq (tax/props tax :reifiable)`), belief-following
and needing no mtime cache. A KB that declares no reifiableFunction pays one set read
per assert / query and nothing else: the whole subsystem is a gated no-op.

## Write path

`assert` runs `maybe-reify-nats` **first — before `expand-consequent`, WFF, and the
constraint checks**:

- every **ground, reifiable** NAT subterm `(F a…)` is replaced by its constant `K`
  (an existing one via dedup, else a fresh mint) — inner args reified first, then the
  outer NAT;
- the walk descends into nested non-NAT literals (rule bodies, conjuncts) but leaves
  the head predicate and every quoting-predicate argument opaque;
- a **vector** is descended element by element, and every element of it. A vector in a
  sentence is a list of forms rather than a literal — an `exceptWhen`'s conjuncts, a
  `thereExists`'s binders — so it has no head predicate to hold opaque and no element
  to skip. That is what puts an exception's query in the same spelling as the fact it
  is about, and the cost of stopping at one is not a missing answer: an exception that
  cannot be answered does not hold ([exceptions.md](exceptions.md)), so the rule fires
  unguarded and nothing says so;
- **unreifiable NATs are left structural** — never minted.

Reify-**before**-WFF is load-bearing. `checks/args-problem` and `disjoint-problem`
read only top-level args and skip compounds, so the raw compound `(FruitFn AppleTree)`
in an argument slot is neither type-checked nor indexed. The minted constant `K`
carries the materialized `resultIsa` types, so it is an atomic term the checks *can*
see — and the term index never posts the raw NAT's constituents, which would pollute
it (`sentex/index-terms` descends into ground compounds).

`mint-nat!` allocates a fresh opaque `K`, asserts `(termOfUnit K E)`, materializes the
result types (`(T K)` per `resultIsa`, `(genl K T)` per `resultGenl`), and returns
`K`, all at `:monotonic` strength — a reified NAT's identity and result types are structural,
not defeasible. `assert` stores synchronously, so a second occurrence of `E` in the
same sentence dedups against the first; a `(rewriteOf T E)` declaration short-circuits
the mint to the real term `T`.

## Read path

Before matching, a query goal's ground reifiable NATs are reified to their
**existing** constant (dedup, never mint). An unknown (never-minted) NAT resolves to
the reserved `nat/no-match` sentinel, which can never be a real constant — so an
unknown-NAT query returns empty without minting.

It is wired at every read entry, and the enumeration is the whole of the guarantee:
`sentexes-matching`, `ask`, `prove`, `query`, the anytime `ask-within` /
`prove-within`, and levels 6 and 7 of the lookup stack ([levels.md](levels.md)), which
are the two that claim to be the engine's own dispatch. One shared step
(`core/prepare-goal-for-read`) does it for all of them, because the failure mode when
an entry omits it is not a wrong answer but an **empty** one — the compound is matched
against a store that holds a symbol, and nothing comes back, which is
indistinguishable from a KB that was never told.

## The corresponding predicate

An ontology that reifies `MotherFn` usually also has `motherOf`, and the two are one
claim written twice. `(functionCorrespondingPredicate F P N)` says so: `F` maps
`a₁ … a_M` to `V` exactly when `(P a₁ … a_{N-1} V a_N … a_M)` holds. `N` is 1-based
over `P`'s arguments; **omit it and the value takes the last position**, which is what
`(functionCorrespondingPredicate MotherFn motherOf)` means and the shape nearly every
correspondence has. A value in any other position needs the explicit form —
`(functionCorrespondingPredicate StreetCornerFn streetCornerOf 1)`, so
`(StreetCornerFn Xing North)` is the `Lot` of `(streetCornerOf Lot Xing North)`.

The example is the shipped one: `resources/kb/upper/LifeContext.txt` states `motherOf` and
`fatherOf` with `MotherFn` and `FatherFn` beside them, so a KB that loads the starter can
name somebody by their role before it knows their name.

It is read in **both** directions, and that is the point: a KB told only one of the two
spellings can otherwise reason with only that one.

- **value → term.** A believed `(motherOf Muffet Mary)` reifies `(MotherFn Muffet)` to
  `Mary`. The expression names the object the KB already has a name for rather than
  minting a second one beside it, so the correspondence is a *computed* `rewriteOf`
  target — the same seam, looked up through the predicate instead of declared per
  expression. It is consulted before the dedup probe, because a real term outranks a
  placeholder.
- **term → value.** When no value is known, the mint proceeds and the constant is
  **projected** back onto the predicate: `(motherOf Muffet K)`, asserted with the rest of
  `K`'s bookkeeping and *after* the result types, since the projected literal is
  argIsa-checked and `K`'s types are what it is checked against. So the placeholder
  answers `motherOf`'s questions instead of being a term nothing says anything about.
  The alternative — minting the constant and leaving the predicate unstated — makes the
  placeholder invisible to every question the predicate answers.

**The two meet at the merge, and that is what makes the order stop mattering.** Three
things can arrive in any order — the application, the fact naming its value, the
declaration — and each of the three landing last has an arm:

| Last to arrive | What happens |
|---|---|
| the application | reifies to the believed value; nothing is minted |
| the fact | `(rewriteOf V K)` retires the placeholder, and the equality migration folds every use of `K` — its `termOfUnit` map included — onto `V` |
| the declaration | each constant already minted for `F` is equated with its value, or projected when it has none |

`rewriteOf` rather than `equals` because the two sides are not interchangeable: `V` is
a name somebody wrote and `K` is a stand-in for not knowing it, so the class needs a
term that wins the election rather than whichever one sorts first. A minted constant is
`:opaque` to `wff`'s same-role check — the naming invariants are conventions over names
a person *chose*, and what a reified NAT denotes is settled by its materialized result types —
so merging one into an individual is the intended move, not the import bug that check
catches.

**Several believed declarations for one function decide nothing.** Two correspondences
are two different claims about what `(F a…)` denotes, and choosing between them would
have to key on a handle, which belief may never do — so neither is read and the
application mints as if none were declared. The same for a value: `correspondence-value`
answers only when exactly one is believed.

The declaration is read through the **index**, not a taxonomy cache. It is consulted
once per NAT, where the reify is already probing for a `rewriteOf` target and a dedup,
and a KB declaring none pays one O(1) functor count per assert
(`nat/any-corresponding-predicates?`). Nothing to integrate means nothing for `recover`
to rebuild — a correspondence works across a restart because the declaration is a
stored fact and always has been. It bites only for a `reifiableFunction`: an undeclared
function's application is a raw compound the reify pass never visits.

## Display / export

`nat/expand-expression` reverses the map, recursively rebuilding a reified constant
back to its functional expression — `(color (FruitFn AppleTree) Red)`, never a raw
`nat/` symbol. Non-reified NAT content is returned unchanged (same identity); only
reified NAT-bearing forms are rebuilt.

**A constant is never what a reader sees.** It is an implementation of term *identity*
— a `nat/`-namespaced gensym is not a name anybody wrote — so a display layer resolves
it, and `vaelii.core` carries the pair that lets one: `reified-term?`, a pure test on the
reserved namespace that costs nothing on a KB that has minted none, and
`term-expression`, **one hop** of the map. One hop rather than the whole expansion,
because a caller rendering each term individually — linking it, colouring it — recurses
and keeps every level addressable; `expand-expression` is the flat answer for a caller
that wants the form and not the parts. The browser does the former, showing the
expression with **bold parens** and the opening one linking to the constant's own page
([web.md](web.md), "A reified term is never shown as its constant").

## Rename and remove — keeping the 1:1 invariant

**Rename** is an equality assert. `(rewriteOf MalusTree AppleTree)` retires
`AppleTree`; the equality **migration** ([equality.md](equality.md)) restates every
sentex naming it, including `(termOfUnit K (FruitFn AppleTree))`, whose rewritten twin
is `(termOfUnit K (FruitFn MalusTree))`. `K` stays **stable** — it is not the term
renamed — so nested NATs referencing `K` need no cascade. A rename can collapse two
NATs onto one expression; `merge-colliding-nats!` (run after an equality assert,
gated) restores the 1:1 invariant by merging each colliding group's constants into its
lexicographically-smallest survivor via a further equality, which migrates their uses.
The retired spelling stays a usable *question*: a goal naming the old term
goal-rewrites to the new expression and still resolves to `K`.

**Remove** is retraction. When the last live use of a reified NAT goes, its `termOfUnit` map
and materialized types would dangle a raw `nat/` symbol — so `remove-orphaned-nats!`
(run after `retract!`, gated, suppressed while already removing orphans) collects
every constant whose only remaining believed sentexes are its own bookkeeping, looping
to a fixpoint since removing a nested reified NAT can orphan another. A **correspondence
projection** is bookkeeping for this: like a result type it states what the constant
*is*, and counting it as a use would make every placeholder immortal.

## Where it lives

- `vaelii.impl.nat` — detectors (`reified-nat-symbol?`, `reifiable-function?`,
  `reifiable-ground-nat?`), lookups (`nat-expression`, `dedup-constant`,
  `rewrite-target`, `result-isa-types` / `result-genl-types`,
  `correspondence-of` / `correspondence-value` / `corresponding-literal`),
  `expand-expression`, the shared reify walk in both modes, `mint-nat!`, and the
  rename / remove / correspondence maintenance. Reads the store, taxonomy and belief
  directly, and reaches assertion through `wiring/assert-sentence`.
- `vaelii.core` — the reify call sites: the write-path reify at the head of `assert`,
  the read-path reify at the query entries, the post-assert maintenance hooks
  (`merge-colliding-nats!`, `reconcile-correspondence!`), and `remove-orphaned-nats!`
  on the `retract!` sweep.
- `vaelii.impl.special` — the two function-kind prop marks, the correspondence's
  wff-only entry, and the equality-arm skip for a compound-arg `rewriteOf`.
- `vaelii.impl.wff` — `function-decl-problems`, `correspondence-problems`, the
  `:opaque` role a minted constant carries through the same-role check, and the
  `equality-problems` waiver for a compound-arg `rewriteOf`.
- `resources/kb/CoreContext.txt` — the seven NAT predicates, declared and documented.

## What reification does not cover

- **An unreified or open NAT is not structurally indexed.** Reification is what makes a
  NAT findable, so a NAT that cannot be reified is reachable only through the coarser
  keys ([indexing.md](indexing.md)).
- **An existential rule head is not skolemized here** ([skolem.md](skolem.md)).

The **measure-evaluating quantity prover** — measure comparison over a `dimensionOf` /
`conversionFactor` table — reads the structural measures this gate preserves. It lives
in [quantity.md](quantity.md).
