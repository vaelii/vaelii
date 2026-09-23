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
**CxUniverse**, so it rides `put-sentex`, the functor / argument roots, and the
inverted term index like any other fact.

| Fact | Meaning |
|------|---------|
| `(reifiable_function F)` / `(unreifiable_function F)` | F's kind — a **predicate-metadata mark** (`vaelii.impl.taxonomy` `:reifiable` / `:unreifiable` prop), belief-following like `transitive`/`symmetric` |
| `(termOfUnit K E)` | the constant↔expression map: constant `K` denotes NAT expression `E`. The reverse (`K → E`) index; `E → K` is the inverted term index |
| `(rewriteOf T E)` (compound `E`) | NAT `E` reifies to the existing real term `T` instead of a fresh constant |
| `(result F T)` / `(genlResult F T)` | F's output types — materialized on mint as `(T K)` / `(genl K T)` |
| `(functionCorrespondingPredicate F P N)` | F and P state one relationship: `(F a…) = V` exactly when P holds of `a…` with `V` at argument `N` |

`termOfUnit` and `rewriteOf` are **quoting predicates** (`nat/nat-quoting-predicates
= #{termOfUnit rewriteOf}`): their expression argument is a verbatim NAT payload that
must not itself be reified or type-checked as a term.

`(rewriteOf T E)` overloads the equality/deprecation `rewriteOf`, discriminated by
shape: a **symbol** second argument is term equality (the equality partition — see
[equality.md](equality.md)); a **compound** second argument is a NAT reify-to-term
declaration. The equality integrate arm and `wff/equality-problems` both skip the
compound shape, so it is stored as an inert quoting fact, never entering the closure.

## Which mark a function gets

`reifiable_function` and `unreifiable_function` describe two mechanisms — minted into a
constant, or left structural for a prover to compute — and the choice between them is not
a matter of taste. The criterion is **boundedness of the application space**.

Reifying stores one opaque constant per distinct application and keeps it, so it is safe
exactly when the applications are bounded: `(FatherFn Muffet)` is one constant per animal,
and an `AdultFn`-shaped function one per individual. A function whose arguments range over
a continuous or open-ended domain is not, and takes `unreifiable_function` instead —
`(QuantityFn 5 Meter)`, `(QuantityFn 5.001 Meter)` and every magnitude between them run
over the reals, so a constant apiece is a store nothing bounds. That is why `QuantityFn`
and `QuantityIntervalFn` are unreifiable, and why a **measure function is never reifiable
however atomic its value reads** — the shape is the trap, since a measure looks like a
thing you would want a name for.

Both marks classify: `(reifiable_function F)` and `(unreifiable_function F)` each say F is a
`function`, which is what `(disjoint function predicate)` reaches. The choice changes
where a declared result type is *stored*, not whether it holds — a reifiable application
carries `result` materialized on its constant, an unreifiable one is typed from the
declaration at check time, and the two say the same thing about the same function.

## The reifiable gate

A function's kind is metadata cached in the taxonomy, so the per-sentence gate —
"does the KB declare any function that reifies?" — is a free **in-memory set read**
(`nat/any-reifiable-functions?` ⇒ `seq` of the `:reifiable` props, else of the
`:context-denoting` ones), belief-following and needing no mtime cache. A KB that
declares neither pays two set reads per assert / query and nothing else: the whole
subsystem is a gated no-op.

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

Reify-**before**-WFF is required. The raw compound `(FruitFn AppleTree)` in an
argument slot is not indexed, and `disjoint-problem` skips it — the term index never
posts the raw NAT's constituents, which would pollute it (`sentex/index-terms` descends
into ground compounds). The minted constant `K` carries the materialized `result`
types, so it is an atomic term every check reads like any symbol.

The **argument** checks do not skip it. `args-problem` and `genls-problem` read a
compound through its function's declared result — see [Typing an application that is
never minted](#typing-an-application-that-is-never-minted) below, which is what makes
one declaration bind both classes of function.

`mint-nat!` allocates the opaque `K`, asserts `(termOfUnit K E)`, materializes the
result types (`(T K)` per `result`, `(genl K T)` per `genlResult`), and returns
`K`, all at `:monotonic` strength — a reified NAT's identity and result types are structural,
not defeasible. `assert` stores synchronously, so a second occurrence of `E` in the
same sentence dedups against the first; a `(rewriteOf T E)` declaration short-circuits
the mint to the real term `T`.

`K` is **named by the content of `E`**, not a process-local gensym: `constant-for`
hashes `E` with SHA-256, takes the first 96 bits, and encodes them base62 behind a
one-letter scheme tag — `nat/a<17 base62>` for an object NAT, `cx/a…` for a context one
(`nat-scheme-tag`). So the same expression reifies to the **same** constant in any
process and after any rebuild, and the skolem digest ([skolem.md](skolem.md)) names its
witnesses the same way and for the same order-independence reason. This pays off in two
places: two dumps that minted the same NAT hold the same `(termOfUnit K E)` fact and merge
by deduplication, and a re-mint after an orphan sweep resolves to the constant it had
before — where a gensym would have minted a second name for one expression and left the
collision for `merge-colliding-nats!` to reconcile. base62 rather than a shorter
base64url because `K` stands in argument position, held to the naming convention
(`naming/argument-problem`), and base64url's `-` and `_` are exactly the characters that
convention forbids; the tag's leading letter keeps the name a readable token (a
digit-leading name is not) and doubles as the version — a later hash or encoding change
is `nat/b…`, old constants keeping their names.

## Typing an application that is never minted

A reified application arrives at the definitional checks as its constant, typed by the
`(T K)` / `(genl K T)` the mint materialized. An **unreifiable** function has no mint,
so its application stays a compound all the way to the checks — and a compound holds no
type membership and can hold none, a membership being asserted of a name.

So the argument checks read the *function's* declaration instead. `(arg P n T)` reads
`(result F T')` — what an application of `F` **is** — and `(genlArg P n T)` reads
`(genlResult F T')` — what it is a **kind of**. The two are never crossed.

**A term a prover hands back is minted no more than one somebody typed, and is no
orphan.** `(startOf (YearFn 2000) ?i)` binds `?i` to `(InstantFn 2000 1 1 0 0 0)`, an
unreifiable NAT the calendar clock computed from the year's fields
([time.md](time.md)) — and computing it writes nothing: no `termOfUnit` row, no
materialized result type, no handle, so there is no orphan question to ask about it and no
retraction that could take it back. It is a value in a binding map and lives exactly as
long as the answer does. Asserting a sentence that *contains* one is an ordinary assert,
and `(result InstantFn time_point)` in `CxTime` is what types it there — the same one
declaration binding the computed term and the typed one.

```clojure
(v/assert kb '(unreifiable_function QuantityFn) 'CxUniverse)
(v/assert kb '(result QuantityFn measure) 'CxUniverse)
(v/assert kb '(arg needs_dog 1 dog) 'CxUniverse)

(v/assert kb '(needs_dog (QuantityFn 5 Meter)) 'CxUniverse)
;; refused: (QuantityFn 5 Meter) must be a dog — QuantityFn results in a measure
```

Four things fix what that reading is and is not.

- **It is a claim about the function, not about the application.** `(result
  QuantityFn measure)` says every `(QuantityFn m u)` denotes a measure. Nothing computes
  a type for one application, because there is nothing to compute: the term has no
  membership and can acquire none.
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
- **One declaration, one verdict.** `(result F measure)` refuses the same sentence
  whether `F` is reifiable or unreifiable — through the constant in the first case and
  through this reading in the second. A reifiable function's application never reaches
  this arm at all.

What an application is *given* is a separate reading from what it denotes: each input is
checked against the function's own argument declarations, for a reifiable function before
the mint replaces the application with its constant
([argtypes.md](argtypes.md#relation-wide-declarations-and-the-runtime-boundary)).

A **quoting predicate's** argument is left alone: `(termOfUnit K (FruitFn AppleTree))`
and a compound-argument `(rewriteOf T E)` carry the expression as a verbatim payload
rather than as a term used in that position, so typing it by what the function yields
would type a quotation by its referent. That is also where the reading would otherwise
cost a mint something — `mint-nat!` writes one `termOfUnit` per constant.

`disjoint-problem` is the check that still skips a compound. Its `:opposing-handle` is
the conflicting *membership's* handle — what `settle` weighs the pair by — and a result
declaration is not a membership of this application: pairing them in a nogood would let
one application's assertion defeat a claim about the whole function.

## Read path

Before matching, a query goal's ground reifiable NATs are reified to their
**existing** constant (dedup, never mint). An unknown (never-minted) NAT resolves to
the reserved `nat/no-match` sentinel, which can never be a real constant — so an
unknown-NAT query returns empty without minting.

It is wired at every read entry, and the enumeration is the whole of the guarantee:
`sentexes-matching`, `ask`, `prove`, `query`, the anytime `ask-within` /
`prove-within`, and levels 6 and 7 of the lookup stack ([levels.md](levels.md)), which
are the two that claim to be the engine's own dispatch. One shared step
(`quasiquote/prepare-goal-for-read`) does it for all of them, because the failure mode when
an entry omits it is not a wrong answer but an **empty** one — the compound is matched
against a store that holds a symbol, and nothing comes back, which is
indistinguishable from a KB that was never told.

Two paths resolve a NAT the same way — dedup, never mint — without being query reads,
through `nat/resolve-for-read`, which answers nil when a NAT was never minted rather than
a sentence carrying the `no-match` sentinel. `handle-of` reads the constant `ist` stored,
so a lookup of the compound finds the stored sentex. `assert-inert` stores the resolved
sentence, so an inert record keys on the constant every read reifies to instead of a
compound no read finds, and refuses a NAT this KB never minted (`:unminted-nat`) — it
never mints, since a `termOfUnit` is a belief-carrying write this entry point does not do.
`canonical-sentex` resolves before it canonicalizes, so its content identity agrees with
`handle-of`; a NAT with no minted constant has no canonical stored form yet, and the
compound stands.

## The corresponding predicate

An ontology that reifies `MotherFn` usually also has `motherOf`, and the two are one
claim written twice. `(functionCorrespondingPredicate F P N)` says so: `F` maps
`a₁ … a_M` to `V` exactly when `(P a₁ … a_{N-1} V a_N … a_M)` holds. `N` is 1-based
over `P`'s arguments; **omit it and the value takes the last position**, which is what
`(functionCorrespondingPredicate MotherFn motherOf)` means and the shape nearly every
correspondence has. A value in any other position needs the explicit form —
`(functionCorrespondingPredicate StreetCornerFn streetCornerOf 1)`, so
`(StreetCornerFn Xing North)` is the `Lot` of `(streetCornerOf Lot Xing North)`.

The example is the shipped one: `resources/kb/upper/CxLife.txt` states `motherOf` and
`fatherOf` with `MotherFn` and `FatherFn` beside them, so a KB that loads the starter can
name somebody by their role before it knows their name.

It is read in **both** directions, and that is the point: a KB told only one of the two
spellings can otherwise reason with only that one.

- **value → term.** A believed `(motherOf Muffet Mary)` reifies `(MotherFn Muffet)` to
  `Mary`. The expression names the object the KB already has a name for rather than
  minting a second one beside it, so the correspondence is a *computed* `rewriteOf`
  target — the same protocol, looked up through the predicate instead of declared per
  expression. It is consulted before the dedup probe, because a real term outranks a
  placeholder.
- **term → value.** When no value is known, the mint proceeds and the constant is
  **projected** back onto the predicate: `(motherOf Muffet K)`, asserted with the rest of
  `K`'s bookkeeping and *after* the result types, since the projected literal is
  arg-checked and `K`'s types are what it is checked against. So the placeholder
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
stored fact and always has been. It bites only for a `reifiable_function`: an undeclared
function's application is a raw compound the reify pass never visits.

## Display / export

`nat/expand-expression` reverses the map, recursively rebuilding a reified constant
back to its functional expression — `(color (FruitFn AppleTree) Red)`, never a raw
`nat/` symbol. Non-reified NAT content is returned unchanged (same identity); only
reified NAT-bearing forms are rebuilt.

**A constant is never what a reader sees.** It is an implementation of term *identity*
— a `nat/`-namespaced gensym is not a name anybody wrote — so a display layer resolves
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
sentex naming it, including `(termOfUnit K (FruitFn AppleTree))`, whose rewritten twin
is `(termOfUnit K (FruitFn MalusTree))`. `K` stays **stable** — it is not the term
renamed — so nested NATs referencing `K` need no cascade. A rename can collapse two
NATs onto one expression; `merge-colliding-nats!` (run after an equality assert,
gated) restores the 1:1 invariant by merging each colliding group's constants into its
lexicographically-smallest survivor via a further equality, which migrates their uses.
The retired spelling stays a usable *question*: a goal naming the old term
goal-rewrites to the new expression and still resolves to `K`.

A collision can also run the other way — one constant mapped to two expressions — and
until the repair reaches it, **every reader of the map takes the same one**: the
content-least (`nat/authoritative-expression`, the choice `dedup-constant` makes on the
other side of the map). That is what keeps the orphan sweep coherent: `orphan?` decides
orphanhood against the expression `bookkeeping-handles` then computes the retraction set
from, so no verdict about one expression retracts records belonging to another.

**Remove** is retraction. When the last stored use of a reified NAT goes, its `termOfUnit` map
and materialized types would dangle a raw `nat/` symbol — so `remove-orphaned-nats!`
(run after `retract!` and `edit!`, gated, suppressed while already removing orphans)
collects every constant whose only remaining **stored** sentexes are its own bookkeeping.
Stored, not believed: a use sitting OUT revives when the defeat above it lifts, and an
inert use (a labeling's choice head) has no TMS node at all — either would dangle if a
sweep counted only belief, and re-reifying the expression would mint a second constant
beside the first. A
**correspondence projection** is bookkeeping for this: like a result type it states what
the constant *is*, and counting it as a use would make every placeholder immortal.

**Bookkeeping is decided by authorship, not by shape.** `K`'s own sentexes are its
`termOfUnit` map plus exactly what `mint-nat!` wrote about it, and `nat/minted-for`
re-derives that set the way the mint derived it: `(T K)` for each believed `(result F
T)`, `(genl K T)` for each `(genlResult F T)`, `F` being the function of the expression
`K` maps to, and the correspondence projection. Everything else naming `K` is somebody's
assertion whatever its arity — `(prime K)` is a claim about `K` exactly as `(noted Author
K)` is, and a sweep reading arity alone would retract the claim along with the constant.
The set is computed behind a **delay**, and the `termOfUnit` clause is what makes that
pay: a constant a teardown collects has its map and nothing else left, so the common
answer is reached without reading the declarations at all. The one constant this keeps
alive that a shape test would have collected is one whose `result` declaration was
retracted after the mint: the materialized `(T K)` is then a believed sentence no rule
supports and nobody has withdrawn, and holding `K` for it is the direction to err in.

**The answer is realized before the caller acts on it**, and the delay is what makes
that a rule rather than a detail. `bookkeeping-handles` is read *for* a retraction and
decides membership by re-reading `K`'s `termOfUnit`, so an answer still being computed
while the caller retracts through it reads a KB the caller has already taken that map
out of — and everything past that point answers "not bookkeeping" and stays stored,
which is the dangling `nat/` symbol the sweep exists to prevent. Which sentex the term
index hands back first decides whether it happens, so a lazy answer here is a bug in
some retrieval orders and not in others. Both the per-constant set and the sweep's own
per-round orphan list are realized before the round's first retraction.

**The sweep asks about the region the teardown removed, not about the KB.** A constant
becomes an orphan only when something that referenced it goes, so the candidates are the
constants the departing sentexes named (`orphans-named-by`), and each is settled by one
inverted-term-index read — `orphan?`, since a constant's uses, its map and its
materialized types are all sentexes naming it ([indexing.md](indexing.md)). What a
retraction costs is the size of what it removed, and a KB that has minted a hundred
thousand NATs the retraction is not about adds nothing to it.

**A `cx/` context constant is collected at the same gate**, by the same rule with one more
source of liveness: a context is somewhere sentexes *are* as well as something sentences
name, so the last fact leaving its slot orphans it as surely as the last sentence dropping
its name. `orphans-named-by` reads a removed sentex's **context** beside its sentence for
that, and `orphan?` asks a context's extent — one O(1) `count-in-context` — before the term
index. Its whole bookkeeping is the `termOfUnit`, the mint writing no result types for a
place; what the structural producer **computed** off that map is not a reference to it, and
holding an ordered pair up on its own edges is the failure that reading would cause.
[context-nat.md](context-nat.md) has the definition, the trigger and the cost.

The removals reach the sweep through `integrate/*removed-sink*`, the record the removal
choke point fills while a teardown runs, because they arrive from three places: the
dependency-directed sweep; the settle that follows it, where an exception that starts
holding blocks a justification and what it solely supported is deleted
([exceptions.md](exceptions.md)); and the orphan sweep's own retractions. The third is
how **the region grows with the fixpoint** — removing an orphan removes the `termOfUnit`
sentex holding its expression, so a reified NAT nested in that expression is a candidate
on the next round. A cascade is therefore found by the rule that found the first orphan,
and the loop ends on the round that removes nothing.

`preview`'s rollback is the one caller that asks the whole KB instead
(`orphaned-constants`): the batch it undoes runs with the settle sweep off
([preview.md](preview.md)) and reaches the orphan sweep at no point, so the claim it owes
— the KB is as it was found — is about all of it rather than about one teardown's region.

## Where it lives

- `vaelii.impl.nat` — detectors (`reified-nat-symbol?`, `reifiable-function?`,
  `reifiable-ground-nat?`), lookups (`nat-expression`, `dedup-constant`,
  `rewrite-target`, `result-types` / `genl-result-types`,
  `correspondence-of` / `correspondence-value` / `corresponding-literal`),
  `expand-expression`, the shared reify walk in both modes, `mint-nat!`, and the
  rename / remove / correspondence maintenance — the orphan questions among it
  (`orphan?` per constant, `orphans-named-by` over a region, `orphaned-constants` over
  the KB, `reified-nats-in` for the candidates) and `reconcile-nats!`, the collision
  merge and the correspondence in the order the assert path runs them. Reads the store,
  taxonomy and belief directly, and reaches assertion through `wiring/assert-sentence`.
- `vaelii.impl.nat-maintenance` — the sequencing the write paths run around that:
  `reconcile-assert` once a sentence is stored (`reconcile-nats!`, then the structural
  `genlCx` edges the fact entails and the merges those edges license) and
  `collect-orphans!` on the `retract!` and `edit!` sweeps, which loops
  `remove-orphaned-nats!` to a fixpoint. The teardown entry point is an argument, so the
  engine requires nothing above it.
- `vaelii.core` — the reify call sites: the write-path reify at the head of `assert`,
  the read-path reify at the query entries, and one call into
  `vaelii.impl.nat-maintenance` per maintenance site.
- `vaelii.impl.integrate` — `*removed-sink*`, the removal choke point's record of what a
  teardown took away, which is the region the orphan sweep runs over.
- `vaelii.impl.special` — the two function-kind prop marks, the correspondence's
  wff-only entry, and the equality-arm skip for a compound-arg `rewriteOf`.
- `vaelii.impl.checks` — `convicting-result-type`, the arm `args-problem` and
  `genls-problem` read a compound argument through ([argtypes.md](argtypes.md)).
- `vaelii.impl.wff` — `function-decl-problems`, `correspondence-problems`, the
  `:opaque` role a minted constant carries through the same-role check, and the
  `equality-problems` waiver for a compound-arg `rewriteOf`.
- `resources/kb/CxCore.txt` — the seven NAT predicates, declared and documented.

## What reification does not cover

- **An unreified or open NAT is not structurally indexed.** Reification is what makes a
  NAT findable, so a NAT that cannot be reified is reachable only through the coarser
  keys ([indexing.md](indexing.md)).
- **An existential rule head is not skolemized here** ([skolem.md](skolem.md)).

The **measure-evaluating quantity prover** — measure comparison over a `dimensionOf` /
`conversionFactor` table — reads the structural measures this gate preserves. It lives
in [quantity.md](quantity.md).
