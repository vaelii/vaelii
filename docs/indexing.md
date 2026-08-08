# Indexing

- **Covers:** the six index families' key shapes — the trie, the secondary roots, the rule
  and exception indexes, the term index, and the term roster — and what each answers.
- **Not here:** the dense/columnar representations these families are packed into →
  [density.md](density.md); the record store and the protocols the index sits beside →
  [storage.md](storage.md).
- **Assumes:** sentex, handle, context, canonical form → [glossary.md](glossary.md).

`vaelii.impl.kv`. Six indexes over the same sentexes, all in the index store: the positional
trie, the secondary roots, the rule index, the exception re-check index, the
inverted term index, and the term roster beside it. `KvIndexStore` holds the logic over a
`KvBackend` substrate (see [storage.md](storage.md#the-index-is-written-once--kvbackend)),
so a backend just says how a key, a counter, and a set live in a store; the one
`IndexStore` that is not a `KvBackend` is `ColumnarIndexStore`, which implements the trie
natively and delegates the flat families to an embedded `KvIndexStore` on the same keys.

Every key is a structured vector and every set member a bare value. On the in-memory
backend (`vaelii.impl.memory`) the vectors are used directly as map keys; on the
on-disk backend (`vaelii.impl.disk.kv`) the same map is held in RAM and durably
logged, nippy-framed so ints and keywords keep their type. The whole layout:

| Key | Value | Answers |
|-----|-------|---------|
| `[:trie :count prefix]` | integer | how many sentexes under this path prefix |
| `[:trie :children prefix]` | set | the next token labels (a node's child edges) |
| `[:trie :handles prefix]` | set | the sentex handles ending exactly at this node |
| `[:context-root ctx]` | set | the extent of a context (its size is the set's own) |
| `[:functor-root pred]` | set | facts by functor, any arity, either polarity |
| `[:argument-root pred pos term]` | set | `pred`'s facts with `term` at argument position `pos` |
| `[:argument-slot pos term]` | set | the predicates present at that slot (names, not handles) |
| `[:rule-index :antecedent pred]` | set | rules with an antecedent on `pred` |
| `[:rule-index :consequent pred]` | set | rules concluding `pred` |
| `[:exception-index pred]` | set | rules whose exception query mentions `pred` |
| `[:exception-index :rules]` | set | every rule carrying an exception |
| `[:term-index term]` | set | sentexes containing `term` anywhere, any nesting |
| `[:term-roster]` | set | every symbol term the term index is keyed by — the vocabulary |

Only the trie keeps explicit counters, because a *prefix* count aggregates the
leaves beneath it. Every other index is a flat set whose cardinality is its own
set size, so a count cannot drift from its extent.

Note what is deliberately **absent**: nothing here records a rule's direction or
defeasibility as a queryable property (beyond the `:default` enumeration). Those are
fields on the sentex record — see §3.

## 1. The count-aware trie

A sentex is indexed by its **path**: its key tokens followed by the context as the
final level. The key drops the `implies` / `and` rule frame (canonicalized into the
record — see [storage.md](storage.md)) and is **α-renamed**: variables become `?0`,
`?1`, … by first occurrence (`sentex/key-tokens`). So the key shape depends on the
sentex's decomposition:

- a **positive fact** — its body **linearized** in preorder (`sentex/key-stream`):
  the functor at the top level, then each argument, with a nested compound expanded
  into an arity marker `[::subterm k]` (k = element count) followed by its elements.
  `(dog Muffet)` in `default` → `[dog Muffet default]` (flat, unchanged), and
  `(mass Obj (QuantityFn 5 Kilogram))` → `[mass Obj [::subterm 3] QuantityFn 5
  Kilogram default]`, so `QuantityFn` and `Kilogram` are their own matchable,
  selective trie levels instead of one opaque token (see *Structural subterms* below);
- a **negative fact** — `[:false <body> <context>]`, the body kept whole so a
  `(not ?s)` pattern — whose body *is* a variable token — still matches it by the
  ordinary child-set fan. The cost of keeping it whole is that a negative matches in
  the trie only **exactly**: `[:false (dog ?0) c]` is a different key from `[:false
  (dog Tom) c]`, and since no part of the body is a level, an *open* negative like
  `(not (dog ?x))` narrows to nothing rather than to less. So the trie is not a
  candidate source for one, and `res/candidate-handles` routes it to the secondary
  roots, which span both polarities. This is correctness, not cost — a trie lookup
  there returns the empty set, not a slow answer;
- a **rule** — `[:rule <antecedents> <consequent> <assumption> <constraint> <context>]`,
  the α-renamed antecedent vector and consequent pattern (no `implies` / `and`; a
  negative literal keeps its `not` there — its *polarity* — so a rule concluding
  `(flies ?x)` and one concluding `(not (flies ?x))` get distinct keys), then the two
  solver slots (see [solving.md](solving.md)).

`:assumption` and `:constraint` are **constant slots**, `nil` for a rule that is
neither, so every rule keys at one depth. That is not cosmetic: a variable in a path
fans out over a node's whole child set, so at a ragged level a wildcard *context* slot
would descend into the deeper rule's extra node and read child labels back as handles.
Being in the key at all is the point — a choice rule and a plain rule with the same
implication are different rules, and so are a hard-constraint rule and a soft one.

A rule's `exceptWhen` exception is **not** in the key. It is a separate meta-sentex
naming the rule's handle, so `bird ⇒ flies` and `bird ⇒ flies exceptWhen penguin` are
the *same* sentex at the same handle: asserting the exception amends the rule in place
rather than creating a second one (see [exceptions.md](exceptions.md)).

A rule's stored sentence is already canonically numbered (`?var0`, `?var1`, … — see
[storage.md](storage.md)), so for rules α-renaming is idempotent. It still matters for
a **query pattern**, whose variables keep the caller's names. Either way α-renaming
builds *only* the key — never a stored `:sentence` or match bindings — so binding
propagation is unchanged.

Because the key is built from the canonical form, **two rules identical up to
variable names, antecedent order, symmetric argument order, or comparison direction
produce the same key and dedup to one handle** (find-or-create resolves the second to
the first). Sorting symmetric arguments needs the taxonomy, so every store/lookup goes
through `res/kb-sentex`; build a sentex another way and an asserted form and a
queried form could key differently.

Every node — identified by its path prefix — is **three** keys:

```
count-key  [:trie :count prefix]  ->  integer: how many sentexes live under this prefix
set-key    [:trie :children prefix]  ->  a SET: the next token labels (the node's child edges)
leaf-key   [:trie :handles prefix]  ->  a SET: the sentex handles ending exactly at this node
```

The count gives selectivity without walking; `lookup` walks a full pattern. A query
variable matches exactly one complete stored form: at an **atom** child it advances
one level (the child-set fan), at a **marker** child it *skips* the whole subterm the
marker's arity spans (see *Structural subterms*). A marker in the pattern is matched
exactly, like any token. **lookup contract:** pass a full path including a context
slot. This answers *positional* pattern queries.

### Structural subterms

A nested compound argument held as one opaque trie token can only be matched by whole-
value equality, so a pattern with a variable inside it — `(mass ?o (QuantityFn ?n
Kilogram))` against a stored `(QuantityFn 5 Kilogram)` — never matches at all. A
positive fact's compound arguments are therefore **linearized into the path in preorder**, each
compound preceded by an arity marker `[::subterm k]`, so every deep position is its
own trie level: `QuantityFn`, `Kilogram`, and the deep variable slot each become
matchable and selective. The marker is a 2-vector, and after linearization no trie
token is ever a vector (arguments are symbols / numbers / strings or nested lists, and
the connective frame is peeled), so a marker never collides with a stored token.

The hard part is the **whole-subterm variable**: `(p ?y b)` binds `?y` to an *entire*
compound `(F (G a))` of arbitrary depth, so the walk must advance past a stored
subterm of unknown length. The arity marker makes that O(1) per level — `lookup`'s
`skip-one` reads the marker, sees the element count, and skips exactly that many
top-level children (`skip-n`, recursing for nested arity), no balanced close-marker
needed. A query variable therefore matches one whole form whether the stored form is
an atom (advance one) or a compound (skip the subterm), which is what keeps `(p ?y b)`
binding a whole compound working now that compounds span several levels.

This is a **pure selectivity change**: the trie is only ever a superset filter and
`res/unify` is the source of truth (it already unifies deep positions), so the
walk may shrink the candidate set but never changes *which* sentexes match — a
markerless (flat) key walks exactly as before. On the retrieval side,
`res/*structural-index*` gates whether `candidate-handles` uses the structural trie
(narrow on the deep positions) or the functor extent (a correct fallback superset).
`find-sentex-handle` and the level-0 raw lookup read `p/lookup` directly, so they are
always structural; `sentexes-matching` and the matching levels go through `candidate-handles`, so
the gate applies to them too — but only to the candidate *source*, never the matches
(`unify` is the source of truth). `structural_index_test` is the oracle: on == off ==
`unify`, over flat facts, top-level / deep-leaf / whole-subterm variables, and nested
compounds.

Only child *sets* (`:s`) are read while walking; handles (`:l`) are read solely at the
terminus, so the skip can never cross into a leaf handle or read a marker as one.

**Handles get their own key because the trie is ragged.** Arity varies, and one
sentex's whole path can be a proper prefix of another's, so a node is leaf and
interior at once: `(rel A B)` in `CeeContext` keys as `[rel A B CeeContext]`, and
`(rel A B CeeContext X)` in `DeeContext` keys as `[rel A B CeeContext X DeeContext]`
— the first path is an interior node of the second. If handles shared the `:s` token
set they would be indistinguishable from tokens (a handle is an integer, and so is
the token `1970`), so `lookup [bornIn Tom]` on a stored `(bornIn Tom 1970)` would
return `1970` as a phantom handle, and `get-sentex 1970` is a real, unrelated sentex.
Neither rejecting a non-leaf terminus nor type-discrimination can fix that — the node
*is* a leaf, and a handle and a token are both integers — so the distinction is
structural: handles live under `[:trie :handles prefix]`, tokens under `[:trie :children prefix]`.
`lookup` reads only the leaf key at its terminus, so it never returns a token as a
handle; `p/children` reads only the child set, so it is correct at such a node and
`plan/prefix-estimate`'s fan-out carries no phantom branches.

The node layout means an index written by another layout answers nothing rather than
answering wrongly (it fails safe), which is why the layout is stamped and gated at open —
section 7 below.

## 2. The secondary roots

The trie is ordered `[pred args… ctx]`, so it narrows only left-to-right: it can
count "predicate P" or "P with arg1 X", but **not** "context C" (context is the
deepest level, never a prefix) and not "X in argument position 2" without fixing
everything to its left. Three single-level roots fill that in, each a set of handles,
plus the slot roster the predicate-agnostic reads union over:

```
[:context-root <context>]    -> #{handles}   every sentex asserted there (rules included)
[:functor-root <pred>]       -> #{handles}   facts whose functor is pred — any arity,
                                     either polarity (a negative fact roots under
                                     its positive body's functor)
[:argument-root <pred> <pos> <term>] -> #{handles}  pred's facts holding term at 1-based pos
[:argument-slot <pos> <term>]        -> #{preds}    the predicates present at that slot —
                                     reference-counted off the postings, so a
                                     predicate-agnostic read is a union over a
                                     handful of scoped keys
```

Cardinality is the set's own size, not a parallel counter, so a count can never
drift from its extent — the trie needs explicit counters only because a *prefix*
count aggregates the leaves beneath it. A rule contributes only its context; its
predicates live in the rule index below.

They are read through `core`: `sentexes-in-context` / `count-in-context`,
`sentexes-with-functor` / `count-with-functor`, `sentexes-with-arg` /
`count-with-arg`. Two places rely on them for speed rather than convenience:
`core/types-of` (the individual's asserted types — the retrieval `isa?` and
`checks/disjoint-problems` are built on, so it runs on every unary assert) goes straight
to the position-1 read (`sentexes-with-arg`, a slot-roster union) instead of scanning
every sentex mentioning `x` anywhere; and
the provers' `est-bindings` cost
model reads `[:functor-root pred]`, which — unlike the trie's `count-at [pred]` — also sees
negative facts (they key under `:false` and would otherwise estimate 0).

### Retrieval from the roots (`res/match-one`)

The trie narrows only left-to-right, so a pattern that binds a *later* argument while
leaving the first a variable — `(parentOf ?x Tom)`, the second half of a grandparent
join — has no selective prefix and the trie fans out over every first-argument value
(one lookup per node). The roots are indexed by argument position and do not care,
so `res/match-one` consults them for exactly that case, gated by
`res/*arg-root-retrieval*` (default on):

- **Argument-root retrieval.** When a ground argument sits after a variable, the
  candidates come from the argument roots instead of the trie. The set returned is a
  **superset** of the trie's hits — the roots don't constrain numeric arguments or
  context — and the existing `unify` filters it to the identical set, so *which*
  sentexes match never changes. The leading-variable `match-pattern` (the backward /
  `ask` / forward-join path) is flat in the extent where the trie fan is O(N) per
  call — `lein perf`'s `arg-root-retrieval` check gates the flatness, and
  `arg_root_retrieval_test` pins the set-equality.
- **Multi-column narrowing (`sentexes-with-args`).** Knowing more than one term should
  narrow on all of them, so *every* ground argument's predicate-scoped root is
  intersected: `(rel ?x B C)` →
  `[:argument-root rel 2 B] ∩ [:argument-root rel 3 C]`. The scoping means a named
  functor needs no functor-root intersection, and a single bound argument is one hash
  lookup with nothing intersected at all. An individual shared at one position
  across K predicates yields a candidate set at the true match count rather than K×
  it **by construction** — the bucket read is the literal's own predicate's. What an
  intersection *costs* is the backend's business: a
  flat-map index folds `clojure.set/intersection` over sets it already holds, and a dense
  one narrows in the postings' own representation so a rare argument pinned on a hot
  predicate costs the rare side ([density.md](density.md)).
- **An open functor is the same shape at level 0.** `(?type Muffet)` — what types does
  Muffet hold, as a *pattern* rather than a `types-of` call — puts the variable at the
  first path token, so every ground argument is stuck behind it and the trie can only
  fan out over its whole root child set, i.e. **every functor in the KB**. That fan is
  linear in the vocabulary, which in a broad ontology is the largest thing there is.
  The predicate-agnostic read spans every functor by construction — a union of the
  scoped roots over `[:argument-slot 1 Muffet]` — so it answers in a read per predicate
  present at that slot (usually one, a handful when several predicates share it),
  with a `nil` functor to intersect: **flat in the vocabulary** where the trie fan is
  linear in it. A pattern with nothing indexable to lead with (`(?type ?x)`,
  `(?p ?x 1970)`) keeps the trie, since there is no root to read.
- **Hierarchical retrieval (`res/matches-hierarchical`).** A context-scoped
  `(p a ?x)@c` is an intersection over three hierarchies — predicate ∈ `specs(p)`,
  context ∈ `context-up(c)`, arguments unify — which `matches-visible` answered by a
  *product* of `|specs| × |context-up|` trie walks. Leading with the bound argument's
  predicate-scoped roots — one bucket per sub-predicate, the predicate filter
  satisfied by which buckets are read — and making the context hierarchy an
  **in-memory membership filter** over the cached closure collapses the product to a
  hash lookup per sub-predicate: **flat in the context hierarchy's depth** where the
  fan-out is O(depth). The buckets are walked **lazily** — each handed back by
  reference, the per-spec fan a `lazy-mapcat`, consumed only as far as the caller
  reads — so an existence check touches one bucket and short-circuits like the
  fan-out; this is the **default** (`res/*hierarchical-retrieval*`), with the var
  bound false giving the reference fan-out `matches_hierarchical_test` proves it
  equal to.

`sentexes-matching` shares this argument-root retrieval — it routes through `res/raw-match` (the
level-2 matcher), so a leading-variable-then-ground-arg `sentexes-matching` (`(parentOf ?x Tom)`)
diverts to the predicate-scoped argument root (`[:argument-root parentOf 2 Tom]`) instead of
paying the full first-argument trie fan. The `lookup` levels reach it wherever they *match*
(level 2 is `raw-match`, level 4 is `matches-visible`); level 0 (`:raw`) stays a bare
`p/lookup` by contract — it reports the handles at an index location, not the believed
matches, so the argument-root superset would be wrong there.

The roots also underwrite the incremental forward-chain matcher's RAM alpha memories
([inference.md](inference.md), "Incremental rule matching").

## 3. The rule index

Rules are sentexes; they are additionally posted by predicate so chaining finds
candidates without scanning: `[:rule-index :antecedent pred] -> #{rule handles}` (by antecedent
predicate) and `[:rule-index :consequent pred] -> #{...}` (by consequent predicate).

**Both sets are complete** — every rule is registered under all of its antecedent
predicates *and* its consequent predicate, whatever its direction — so "what could
conclude P?" is answerable for a forward-only rule too.

What may actually *fire* is **not indexed**. A rule's `:direction` and `:defeasible`
are fields on its own sentex, put there by its `set/*Rule` wrapper (see
[storage.md](storage.md)), and every consumer reads them from the record:
`fire-rules-for` and `process-datum` check `rules/forward-sentex?`, the backward
chainers `rules/backward-sentex?`. The index answers *which rules mention this
predicate*; the record answers *what this rule may do*.

There is **no exception** to that split, and nothing indexes `:defeasible` — do not
add a set that mirrors it. Defaults fire from the same agenda as strict rules, found by
predicate like any other candidate and fired at the strength their own record reports,
so nothing ever needs to enumerate the defeasible ones. An index that could enumerate
them is an index that has to be kept in step with a field the record already carries.
See [inference.md](inference.md).

A rule concluding a **conjunction** is polycanonicalized into one rule per conjunct
before storage (`rules/expand-consequent`), so `(implies A (and C1 C2))` is stored
as two rules `(implies A C1)` and `(implies A C2)`, each keyed by its own consequent
predicate. `assert` / `assert-rule` return the vector of handles in that case.

## 4. The exception re-check index

A rule may carry its own exception (`exceptWhen` — see [exceptions.md](exceptions.md)).
The exception is a query and is **never stored**, so it has to be re-evaluated; this
index exists only to decide *when*:

```
[:exception-index <pred>]  -> #{rule handles whose exception query mentions pred}
[:exception-index :rules]  -> #{every rule handle carrying an exception}
```

A fact on `P` arriving or leaving looks up `[:exception-index P]` and re-checks those rules'
conclusions. An exception can also flip with no matching fact ever arriving — assert
`(genl penguin flightlessBird)` and `(flightlessBird ?b)` starts holding — so any
`genl` / `genlContext` edge change re-checks `[:exception-index :rules]` wholesale. Edge changes
are rare and exception-bearing rules are few, so the coarse trigger is cheaper than
tracking which closures a query touched, and it cannot be subtly wrong.

Granularity is the **rule**, never the firing. A rule handle is already an antecedent
of every justification it licenses, so each conclusion it produced is reachable
through the consequence links that exist anyway; indexing individual derivations
would buy nothing and grow the store with the exceptions that do *not* apply. This is
the rule index's scale — tens of entries, never millions.

It stores **no truth value**. It answers "which rules might need re-checking", never
"does the exception hold" — a hint, never an answer. That is precisely what separates
it from the cached genl closures, which *do* assert something and therefore had to be
made belief-following (see [taxonomy.md](taxonomy.md)); there is nothing here to drift.

The predicates are passed to `index-exception` / `unindex-exception!` as a seq rather
than read off the sentex, so the index does not depend on how a rule spells its
exception. `rules-with-exception-on` and `exception-rules` read the two sets back.

## 5. The inverted term index

**Every sentex is findable by any term it contains.** On `index-sentex` we post the
handle under every indexable subterm of its **connective-free content**
(`sentex/index-terms` over `content-forms` — a rule's antecedents and consequent,
or a fact's positive body, never the `not` / `implies` / `and`) plus its context:

```
[:term-index term] -> #{handles containing term}
```

An *indexable* subterm (`sentex/indexable-term?`) is a non-variable symbol
(predicate, individual, type, context) or a fully-ground compound. **Numbers,
strings, and variables are dropped** — a year like `1970` or a comment string is
not a lookup key, since it only bloats the index; predicates, individuals,
and ground compound subterms still key.

- `find-sentexes kb term` — sentexes containing `term` anywhere, any nesting.
- `find-sentexes-all kb terms` — the intersection.
- It gives the reverse lookups the trie can't: from a term back to the sentexes
  mentioning it, wherever it sits.

### Which compounds are keys, and why a probe does not depend on the answer

Two bounds decide which ground **compounds** get a key of their own — a floor
(`sentex/*min-indexed-depth*`, default 1) and a ceiling (`sentex/max-indexed-compound`,
64 nodes). Neither touches an atom: a symbol is keyed wherever it sits, at every depth,
under every setting.

The floor drops each content literal's key *for itself*. That key is the one thing here
that scales with the corpus rather than with the vocabulary — a fact's body is a subterm
of itself, so it mints a key holding exactly one handle, once per record. Over a
12,070-record corpus of 511 names it is 12,054 of 12,565 distinct tokens; in the shipped
starter, 1,108 of 1,383. At the floor and deeper, the nesting is what a probe is *for* —
`(sentexHandle H)` inside an `exceptWhen` meta, the sentence inside an `(ist Ctx S)` —
so those keys stay, and the reads that depend on them are unchanged.

A compound outside either bound costs a **read** rather than a key. `find-sentexes`
narrows it on the postings of the atoms it contains — every sentex holding the compound
holds all of them — and verifies each candidate against its own record, which is the
fetch the call was going to make anyway. So the answer never depends on which bound was
set: the same sentexes come back, and `lein perf`'s `compound-probe` is the gate saying
the cost tracks the rarest atom rather than the hottest one. What the bounds buy is
[density.md](density.md): with the floor at its default the token dictionary is
vocabulary-bound, measured at exactly 1.00× over a 3× corpus.

Note the division of labour with the argument root: this index answers "*anywhere*,
any nesting", which is what a term page or a general search wants. When the position
is known — `types-of` looking for `(T x)`, i.e. `x` at argument 1 — the position-1
argument roots (`sentexes-with-arg`, a union of the scoped roots over the slot
roster) are the precise, and much smaller, answer.

Term keys are canonicalized (`term-key` runs `sentex/canon`) so a reader-literal
compound query term matches the stored, canon-built subterm.

Cost: a sentex creates one posting per distinct indexable subterm — deliberately,
that's the "findable by any term" guarantee.

## 6. The term roster

The term index answers *"which sentexes mention this term?"*. The roster answers the
question one step earlier — **"which terms are there at all?"** — and it is a separate
key because a `KvBackend` has no key *scan*: get / put / delete / counters / sets /
intersect / batch, and nothing that lists the keys of one family. (`kv-entries` lists
every entry the store holds, for a dump — see below — but that is the whole index,
unordered, so answering "which terms" from it would cost a walk over all of it, and the
on-disk backend has no key ordering to narrow with.) So the vocabulary is maintained the
way the secondary roots are, as one flat set whose cardinality is its own size:

```
[:term-roster] -> #{every symbol term the term index is keyed by}
```

- `terms kb` — the vocabulary, sorted by name.
- `term-count kb` — its cardinality, one O(1) read.
- `find-terms kb q opts` — the names matching `q` (`:match` `:prefix` (default) /
  `:substring` / `:regex`, `:case-sensitive?`, `:limit`), filtered over the roster.

**Membership is derived from the postings, never counted separately.** `index-sentex`
reads each of its terms' postings *before* writing them and enters the names whose
posting is empty; `unindex-sentex!` reads them before removing and retires the names
whose posting is exactly the handle going away. Both decisions are made from the
pre-write state, so each costs one extra read per name and the index write stays a
single batch — and the roster cannot drift from what is indexed, because it is
answering a question about the postings themselves. `reindex` rebuilds it with
everything else, and `clear-index!` wipes it.

Only **symbols** are rostered. A ground compound keys the term index too (so
`find-sentexes` takes one), but it is a sentence fragment rather than a name, and a
vocabulary listing that included it would be answering a different question.

Cost: this is what makes term enumeration O(vocabulary) instead of O(sentexes). The
scan it replaces — walk every sentex, take its indexable subterms, collect the symbols
— measures ~8µs per sentex, so listing every term costs 3ms on the starter, 37ms at
4.4k sentexes, 495ms at 60k, and would cost seconds at a million. The roster reads one
set and sorts it: 0.09ms, 0.20ms, 1.9ms at those same sizes (33×, 185×, 260×), because it
is priced by the *vocabulary* — 120, 305, 2,545 terms — which grows far slower than the
KB. `term-count` is a set-size read and does not move at all.

The write side pays for it: one posting read per name on `index-sentex`, ~7% of the
index write (2.7µs a sentex), which is why the term set is computed once and handed to
the roster rather than rebuilt.

## 7. The index as a value: `index-entries` / `index-load`

Every family above is a `structured-key -> value` pair, and that pair shape is the one
thing the four index backends have in common — the flat map holds it directly, the dense
backend packs the values into int postings, the columnar store holds the trie as a node
graph with interned int edges and its roots as one packed-long map, and the disk backend
keeps a RAM map behind a WAL. So the projection lives on the **protocol**, not on any
backend:

```clojure
(p/index-entries index)          ; lazy [key value] over everything, in the shape above
(p/index-load    index entries)  ; install them into an EMPTY index, in this backend's own shape
```

Two consequences worth stating. An index written by one backend loads into another —
`index_dump_test` builds one KB and asserts all four project the *same set*, which is
also the check that catches a dense backend that has quietly stopped posting a family.
What it deliberately cannot catch is a family a dense backend still holds but holds
*boxed*: the projection is the same either way, so how densely a backend stores a family
is `dense_routing_test`'s question, not this
one's ([density.md](density.md)).
And `index-load` is not `index-sentex`: nothing is fetched, no path is recomputed, no
term re-derived, which is what makes replaying a dumped index cheaper than `reindex`.
The columnar store reads back only the leaf entries — counts and child edges are
functions of the leaves and its `t-insert!` maintains both — so a dumped count can never
disagree with the trie it describes.

`kv/index-layout-version` is the number that says which key shapes a build uses. It
matters because an index in an unrecognized layout reads as **empty** rather than as
wrong: the log replays cleanly and then every lookup whose key shape moved finds no key
and answers nothing — populated-looking counts over queries that answer nothing. Bump it
whenever a key shape changes.

Three places check it, and none of them leaves the repair to a person. A **durable KV
index** is gated at `open-kb` before anything reads it: `disk/files.clj`'s
`index-layout-decision` compares `<dir>/index/layout.edn` against the current version —
an absent stamp over a populated log counts as stale, since that is what an index written
before the sentinel existed looks like — and a `:stale` verdict clears the index,
rebuilds it from the records, then stamps. The stamp lands only *after* the rebuild, so a
crash in between reads as still-stale on the next open rather than as clean, and the
rebuild logs at `:warn` with the record count and how long it took. A **fork's base** is
held to the same sentinel and gets the other answer: a stale base is refused
(`:type :stale-index-layout`) rather than rebuilt, because the repair is a write and a
base is mounted read-only — the message names the one place the rebuild can happen, which
is opening that directory as a KB. The **mapped snapshot** and the **dump format** answer
the same question in their own vocabulary: a snapshot whose stamp does not match is
`{:index :rebuild :reason :layout-changed}` and is rebuilt rather than mapped.
`index-load` itself trusts its caller.

## 8. The index as bytes: the mapped snapshot

`index-entries` is the index's *portable* form — key shapes, one entry at a time, readable
by any backend. The columnar store has a second form that is neither portable nor an
enumeration: its own arrays, written verbatim.
`vaelii.impl.disk.index-snapshot` writes the CSR sections `columnar/compact!` already
produces to `<dir>/index/` as raw little-endian `int` runs, and maps them back on open —
so a `:disk-columnar` KB reads its index rather than rebuilding it, and the fact-scaled
postings live in the OS page cache instead of the heap.

The split is the point and it is not symmetric. The **skeleton** (`fcounts` `foffsets`
`fedge-tok` `fedge-tgt`), the roots' key column and the token dictionary are read into
heap; the **leaf handles** and the roots' handle run are `mmap`ed. The lookup walk reads
the skeleton at every frontier node — the leading-variable fan, measured at 18,512
lookups for one query — and a page fault there would cost a disk seek apiece. The leaves are read once, at
a walk's terminus. A write thaws whatever it lands on, mapped or frozen alike, so an image
is a read-phase structure.

It is a cache of derived state, so validity is the whole design: stamped with the record
store's slot fingerprint, checked on **every** open, discarded to `reindex` on any doubt.
Off by default (`vaelii.index.snapshot`), and refused outright on a platform that cannot
replace a mapped file — the publish is an atomic rename over one (`docs/storage.md`).

## What the structural index does not reach

The structural trie above indexes nested subterms of a positive fact. Three things sit
outside it, and a query that needs one of them falls back to the coarser index rather
than failing:

- **The secondary argument roots** (`[:argument-root pred pos term]`) and rete's alpha
  buckets are keyed by **top-level position and arity**. A term nested inside an
  argument is not a key in either.
- **A `:false` body and a rule literal** are not structurally indexed, including the
  dotted-rest `(?pred . ?args)` shape.
- **The rule index is keyed by predicate**, not by full antecedent shape, so two rules
  whose antecedents differ below the predicate share a bucket.  A predicate is what the
  key *is*, so a rule literal with a variable in functor position — `(?p ?x ?y)` — is
  **refused** at `assert` with `:not-indexable`: canonicalization numbers the functor to
  `?var0`, no arriving fact and no goal can spell that, and the rule would answer
  nothing while reporting as accepted.  An `:inert` rule is exempt, since it runs in
  neither engine; `CoreContext`'s `(implies (?pred . ?args) (ist UniverseContext (?pred
  . ?args)))` is one, stating for a reader what the decontextualized-predicate lift does
  in code.
