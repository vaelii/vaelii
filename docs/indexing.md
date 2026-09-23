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
backend (`vaelii.impl.memory`) the vectors are used directly as map keys, every family
alike, and the backend's resident shape is its portable one. On the on-disk backend
(`vaelii.impl.disk.kv`) the same map is held in RAM and durably logged, nippy-framed so
ints and keywords keep their type. The whole layout:

| Key | Value | Answers |
|-----|-------|---------|
| `[:trie :count prefix]` | integer | how many sentexes under this path prefix |
| `[:trie :children prefix]` | set | the next token labels (a node's child edges), and — through its cardinality alone, never by building it — how many there are |
| `[:trie :handles prefix]` | set | the sentex handles ending exactly at this node |
| `[:context-root ctx]` | set | the extent of a context (its size is the set's own) |
| `[:functor-root pred]` | set | facts by functor, any arity, either polarity |
| `[:argument-root pred pos term]` | set | `pred`'s facts with `term` at argument position `pos` |
| `[:argument-slot pos term]` | set | the predicates present at that slot (names, not handles) |
| `[:unary-slot term]` | set | the predicates `term` is the lone argument of (names, not handles) |
| `[:rule-index :antecedent pred]` | set | rules with an antecedent on `pred` |
| `[:rule-index :consequent pred]` | set | rules concluding `pred` |
| `[:exception-index pred]` | set | rules whose exception query mentions `pred` |
| `[:exception-index :rules]` | set | every rule carrying an exception |
| `[:term-index term]` | set | sentexes containing `term` anywhere, any nesting |
| `[:term-roster]` | set | every symbol term the term index is keyed by — the vocabulary |

Only the trie keeps explicit counters, because a *prefix* count aggregates the
leaves beneath it. Every other index is a flat set whose cardinality is its own
set size, so a count cannot drift from its extent.

**A counter is a cardinality, so `kv-decrement` is floored at zero.** The two folds that
implement it — `kv/apply-op` and the transient twin a bulk load takes — both stop at 0,
and so does every backend that counts for itself, because the disk store replays its WAL
through the same fold and a floor on one side alone would make a reopened index disagree
with the one that wrote it. It adds no work (the fold has the new value in hand) and
changes no decision on the ordinary path, where a retraction reads the reply to find the
nodes that emptied and asks `<= 0`. It removes a negative `[:trie :count prefix]`,
which `plan/prefix-estimate` divides by: not a wrong estimate but a meaningless one.

**The retraction is gated, the assert is not, and the asymmetry is the threat model.**
`unindex-sentex!` decrements without looking and frees a node whose count reaches zero
along with every handle under it, so one stray call — a handle never indexed here, or
already removed — would take live sentexes out of the trie. It costs one membership probe
on the leaf to make that a no-op, and any caller holding a stale handle can provoke it.
`index-sentex` has no matching probe, and its callers are why: `kb/create-sentex` indexes a
handle it has just minted; `reindex` walks each live handle once over an index it has just
cleared; and the importer's inline bulk load (`reindex/index-one!`, the same per-sentex
core `reindex` folds) indexes each record from the copy in hand, at a handle its own sink
just decided. None of the three can index a handle twice, and the probe would be a hash
lookup per assert on the flat store and a **second whole trie walk** per assert on the
columnar one, on the path built for 100M facts.

A gated retraction **logs** rather than passing silently (`::unindex-absent`, `:warn`, on
both index stores). The no-op is safe and is not therefore right: the caller
(`integrate/sentex-removed!`) deletes the record on the next line either way, so a genuine
divergence leaves the trie handing out a handle whose record is gone, and that surfaces as
a corrupt store somewhere else entirely. `reindex` is the repair; the log is what says to
run it.

Note what is deliberately **absent**: nothing here records a rule's direction or
defeasibility as a queryable property at all — there is no default-rule index and nothing
enumerates rules by defeasibility. Both are fields on the sentex record — see §3.

**And nothing here records belief.** Every posting is storage: it holds a defeated default,
a conclusion whose support was withdrawn and a spelling an equality retired, because all
three are revivable and belief lives in the JTMS. That is not an omission to work around —
half the engine wants the stored reading — but it does mean every read of a posting carries
a question, so the reads are not made against `vaelii.impl.protocols` directly. They go
through `vaelii.impl.reads`, whose entry point names say which answer the caller wanted:
`as-stored-…` and `stored-count-…` take the index store, `believed-…` takes the KB.
`lein lint`'s **E16** rosters the implementers — this namespace, `columnar`, the disk
snapshot, `kb` and `resolution`, and the dump — and fails a raw read anywhere else
([nmtms.md](nmtms.md#belief-filtering-is-a-namespace-boundary)).

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
would descend into the deeper rule's extra node and read child tokens back as handles.
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

**`p/leaf-at` is the other read of the same key, and it matches nothing.** It returns
the leaf handles at the node a path names — one read, no walk and no fan — where
`lookup` treats a variable in that path as a wildcard. The two agree exactly on a
ground path and diverge the moment one carries a variable, which every non-ground
sentex's key does (the key is α-renamed). **Dedup** is what wants the leaf and not the
match: a sentex's key is a function of its sentence and context, so anything sharing
them shares this leaf, and anything at another leaf is by construction another
sentence — the extra candidates a match returns could never have been the answer, and
`find-sentex-handle` would read the record of each to say so. Retrieval is the other
question and stays `lookup`'s: there a pattern is asked what it matches, not where it
is stored.

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
markerless (flat) key holds no marker for the skip to read, so it walks one level per
token. On the retrieval side,
`res/*structural-index*` gates whether `candidate-handles` uses the structural trie
(narrow on the deep positions) or the functor extent (a correct fallback superset).
The level-0 raw lookup reads `p/lookup` directly, so it is
always structural; `sentexes-matching` and the matching levels go through `candidate-handles`, so
the gate applies to them too — but only to the candidate *source*, never the matches
(`unify` is the source of truth). `structural_index_test` is the oracle: on == off ==
`unify`, over flat facts, top-level / deep-leaf / whole-subterm variables, and nested
compounds.

Only child *sets* (`[:trie :children …]`) are read while walking; handles
(`[:trie :handles …]`) are read solely at the terminus, so the skip can never cross into
a leaf handle or read a marker as one.

**Handles get their own key because the trie is ragged.** Arity varies, and one
sentex's whole path can be a proper prefix of another's, so a node is leaf and
interior at once: `(rel A B)` in `CxCee` keys as `[rel A B CxCee]`, and
`(rel A B CxCee X)` in `CxDee` keys as `[rel A B CxCee X CxDee]`
— the first path is an interior node of the second. Handles and tokens live under
separate keys rather than sharing one — [why a separate
key](defenses.md#handles-get-a-key-separate-from-tokens): handles under
`[:trie :handles prefix]`, tokens under `[:trie :children prefix]`.
`lookup` reads only the leaf key at its terminus, so it never returns a token as a
handle; `p/children` reads only the child set, so it is correct at such a node and
`plan/prefix-estimate`'s fan-out carries no phantom branches.

**How many children is its own read**, not `(count (children …))`. `p/count-children`
answers the width off a cardinality — the set's own count in the KV family, an edge-array
span or a map's size in the columnar trie — where `children` *materializes* the child set
to answer at all. That is the distinct-value count the query planner's cost model divides
by, and it is asked once per literal per plan (`docs/inference.md`) — [why a separate
read](defenses.md#child-count-is-its-own-read). `lein perf`'s
`plan-scaling` holds it flat.

The O(1) has one exception, and it is the overlay's merge rule rather than this read:
a fork answers a cardinality off the base's own `kv-count` only where the key is
*inherited*, and a prefix the fork has itself written under is counted off the merged
set, since a union minus a removal set has no cardinality shortcut (docs/overlay.md).
A fork inherits almost all of its content and writes a little, so that is a small set
of prefixes — but planning against one of them costs what the width there is.

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
[:unary-slot <term>]                 -> #{preds}    the predicates term is the LONE
                                     argument of — the same roster narrowed to
                                     arity 1, which is what a membership read asks for
```

Cardinality is the set's own size, not a parallel counter, so a count can never
drift from its extent — the trie needs explicit counters only because a *prefix*
count aggregates the leaves beneath it. A rule contributes only its context; its
predicates live in the rule index below.

**The argument roots are the one *hierarchical* family** — `pos → term → pred → handles`
— and the reads a settle leans on ask for a subtree of it: one scoped leaf, the
predicate-agnostic **union** at a `(pos, term)` node, or that node's cardinality.

All of that is `vaelii.impl.kv`'s, and none of it is a backend's. `KvIndexStore` spells
the three keys, reads a scoped leaf with `kv-members`, narrows several with
`kv-intersect`, and answers the two agnostic reads by unioning over the
`[:argument-slot pos term]` roster — the roster is what keeps them answerable without a
second copy of every posting, and it holds one predicate in the common case, a handful
otherwise. `[:argument-root pred pos term]` is the only four-element key, so a probe
builds a four-element vector and pays a vector `equals` on it, the same as every other
family pays on its own key.

A backend may hold the family however it likes underneath: `dense-roots` packs those keys
into a long and answers with one lookup, and the rest keep them as flat entries. Each is a
representation, invisible above the backend, and `kv-entries` re-emits the flat shape
whichever one it is — the shape the key table above describes.

### The unary roster, and why position 1 was not narrow enough

`[:unary-slot term]` is the argument-slot roster restricted to arity 1, and it exists
because a *membership* question is not a position-1 question. `core/types-of` asks what
types a term holds — the retrieval `isa?` and `checks/disjoint-problems` are built on, so
it runs on every unary assert — and the types are the arity-1 facts whose lone argument is
that term. Position 1 does not separate them: `(dog Muffet)` and `(likes Muffet Tom)` both
put `Muffet` at argument 1, share the `[:argument-slot 1 Muffet]` entry, and share the trie
node below it, because the trie's next level is the *second argument* for one and the
*context* for the other. So the read fetched the record behind every fact naming the term
at argument 1 and kept the arity-1 ones: a densely described individual paid its whole
description on every assert of a type for it, to find the handful of types it holds.

The roster's members are predicates, so it is vocabulary-scaled beside the slot roster
rather than a second copy of the postings, and `unary-sentexes-with-arg` reads it exactly
as `sentexes-with-arg` reads the other — one roster read, then the predicate-scoped
postings.

**It is a deliberate superset.** The entry is written by every unary fact rather than
reference-counted on the first, because the count that reference-counts the other rosters
is the one at `[:argument-root pred 1 term]`, which a *binary* fact of the same predicate
about the same term also raises — so a count read off it would skip the unary entry
whenever the binary fact arrived first, and a missing entry there loses a membership.
Retirement is the mirror: a unary fact retires the entry with its position-1 slot and a
fact of any other arity leaves it alone, so a KB of binary facts pays nothing for a roster
it never enters, and the entry outlives the last unary fact wherever a binary one empties
the node. A stale entry costs one posting read and `types-of`'s arity filter drops it;
the asymmetry is the point.

They are read through `core`: `sentexes-in-context` / `count-in-context`,
`sentexes-with-functor` / `count-with-functor`, `sentexes-with-arg` /
`count-with-arg`, `unary-sentexes-with-arg`. Two places rely on them for speed rather than
convenience: `core/types-of` goes straight to the unary roster instead of scanning every
sentex mentioning `x` anywhere, or every one holding it at argument 1; and
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
  equal to. A candidate answers **once** unless the literal has a mirror to probe at all
  — a concrete functor, exactly two arguments, and some sub-predicate declared
  `symmetric`. Without one the handle is the whole dedup key and the walk is a `keep`
  over the candidates. Only where a mirror can bind one stored fact twice — an all-variable
  pattern over a stored `(sibOf Rex Tib)`, which binds both ways round — does the key
  become `[handle bindings]` and a candidate yield a sequence rather than an answer.

`sentexes-matching` shares this argument-root retrieval — it routes through `res/raw-match` (the
level-2 matcher), so a leading-variable-then-ground-arg `sentexes-matching` (`(parentOf ?x Tom)`)
diverts to the predicate-scoped argument root (`[:argument-root parentOf 2 Tom]`) instead of
paying the full first-argument trie fan. The `lookup` levels reach it wherever they *match*
(level 2 is `raw-match`, level 4 is `matches-visible`); level 0 (`:raw`) stays a bare
`p/lookup` by contract — it reports the handles at an index location, not the believed
matches, so the argument-root superset would be wrong there.

The roots also underwrite the incremental forward-chain matcher's RAM alpha memories
([inference.md](inference.md), "Incremental rule matching").

Which of these paths a given KB's traffic actually takes, and which families it reads at
all, is a question about a workload rather than about the index:
[profile.md](profile.md) is the instrument that answers it, and it names each path above
so a tally can count it.

## 3. The rule index

Rules are sentexes; they are additionally posted by predicate so chaining finds
candidates without scanning: `[:rule-index :antecedent pred] -> #{rule handles}` (by antecedent
predicate) and `[:rule-index :consequent pred] -> #{...}` (by consequent predicate).

**Both sets are complete** — every rule is registered under all of its antecedent
predicates *and* its consequent predicate, whatever its direction — so "what could
conclude P?" is answerable whatever a rule's direction, an inert rule the browser reads
included.

A **negated antecedent** `(not (p ?x))` keys under `[:not p]` rather than under `not`
(`rules/antecedent-key`). So a negation reaches the rules with a negated antecedent on a
predicate related to its own, not every rule with a negated antecedent anywhere.

**The fan under a negation runs the other way**, and both halves say so. A positive fact
triggers through its predicate and its **genls**: a fact on a spec satisfies an antecedent
on its genl, which is `match1`'s subsumption. A negative fact is the mirror, because a
`genl` edge carries the other way through a negation — `(not (animal X))` entails
`(not (dog X))` for every **spec** `dog` of `animal` — so `rules/trigger-keys` returns
`[:not q]` for each spec `q` of the arriving body's predicate, and `res/match1` meets a
`(not (dog ?x))` antecedent with a negative fact on a genl of `dog`. The two directions
are exclusive: `(not (dog Muffet))` does not satisfy `(not (animal ?x))`.

The negative fan is **enumerated from the roster of keys some stored rule reads**, not
from the spec closure, and the asymmetry is why: the positive fan walks the *up* set,
which a hierarchy bounds by its depth, while the down set on a broad ontology is most of
it — an arriving `(not (thing X))` would otherwise cost one index probe per type in the
KB. A KB whose rules read no negation pays one map read.

The exception re-check index (§4) keeps its bare-`not` bucket: it is a coarse
*whether-to-look* roster, and both of its sides agree on that spelling.

A rule concluding a **variable** predicate — `(implies (holds ?p ?x ?y) (?p ?x ?y))`,
allowed because range restriction binds `?p` to a concrete antecedent — has no concrete
consequent predicate to key on, so its consequent is filed under one catch-all bucket,
`[:rule-index :consequent :var-pred]` (`protocols/var-consequent-key`). It fires *forward*
through its concrete antecedent like any other rule; for the *backward* read, "what could
conclude P?" is the `P` bucket unioned with that catch-all, since a rule concluding `(?p …)`
could conclude any `P` once `?p` binds. `resolution/concluding-rule-handles` does the union,
and `rules/direct-concluders` does the same stored-graph read for the stratification and
blocked-firing paths. A variable functor in an *antecedent* is a different matter and stays
refused ([the split](defenses.md#a-variable-functor-rule-is-refused-not-silently-accepted)).
An `:inert` rule concludes nothing in either engine, so a variable consequent on one keeps
the canonical `?var0` — a dead key nothing reads — rather than the live catch-all.

The dual question is a **goal** with a variable functor — `(?p Tom ?y)` — which names no
consequent bucket and which any rule may conclude, `subsuming-unify` binding `?p` to the
consequent's functor. `concluding-rule-handles` answers it with every rule, enumerated off
the antecedent roster (`:rule-antecedents`) through the antecedent index — `O(rules)`,
paid only for a variable functor, the same enumeration `chain/rule-firing-report` takes.
So `(prove kb '(?p Tom ?y))` and `(query kb '(?p Tom ?y) ctx {:max-depth 2})` reach a
rule concluding `ancestorOf` exactly as fact matching reaches a stored `parentOf` through
the argument roots ([inference.md](inference.md), "Backward chaining").

What may actually *fire* is **not indexed**. A rule's `:direction` and `:defeasible`
are fields on its own sentex, put there by its `set/*Rule` wrapper (see
[storage.md](storage.md)), and every consumer reads them from the record:
`fire-rules-for` and `process-datum` check `rules/forward-sentex?`, the backward
chainers `rules/backward-sentex?`. The index answers *which rules mention this
predicate*; the record answers *what this rule may do*.

There is **no exception** to that split, and nothing indexes `:defeasible`.
Defaults fire from the same agenda as strict rules, found by
predicate like any other candidate and fired at the strength their own record reports,
so nothing ever needs to enumerate the defeasible ones — [why no defeasibility
index](defenses.md#rule-defeasibility-is-not-indexed). See [inference.md](inference.md).

A rule concluding a **conjunction** is polycanonicalized into one rule per conjunct
before storage (`rules/expand-consequent`), so `(implies A (and C1 C2))` is stored
as two rules `(implies A C1)` and `(implies A C2)`, each keyed by its own consequent
predicate. A rule whose antecedent **disjoins** distributes the same way and for the
mirror reason — the antecedent index keys a rule by its antecedents' predicates and
`or` names none, so `(implies (or A B) C)` is stored as two rules, each keyed by its own
antecedent predicate and each triggered by an arriving fact exactly as a hand-written
rule is (`rules/expand-antecedent`). `assert` / `assert-rule` return the vector of
handles whenever a rule expanded, and the two expansions compose into the product
([canonicalization.md](canonicalization.md)).

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
`(genl penguin flightless_bird)` and `(flightless_bird ?b)` starts holding — and an edge
change is what the `:rules` roster is for. It is read as the **gate**, not as the answer:
both edge triggers ask it first, so a KB that writes no `exceptWhen` pays one set read
per edge and stops, and each then narrows from it. `special/recheck-genl-edge` keys on
the predicate — the roster sliced by `[:exception-index pe]` for each `pe` in
`genls(super)`, the up-closure being exactly where a spec closure moved — and
`special/recheck-genlCx-edge` keys on the context, walking the roster and queueing a rule
only where one of its firings was placed in the ancestor set the edge widened. The roster is
taken **whole** only where nothing can narrow it: `special/recheck-every-exception`, which
`recover` takes because a restart leaves no edge or fact to key on and every exception
must be re-decided from scratch.

Granularity is the **rule**, never the firing. A rule handle is already an antecedent
of every justification it licenses, so each conclusion it produced is reachable
through the consequence links that exist anyway. This is
the rule index's scale — tens of entries, never millions — [why the index stays this
coarse](defenses.md#the-exception-index-stays-coarse).

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
starter, 1,724 of 2,077. At the floor and deeper, the nesting is what a probe is *for* —
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
— measures ~8µs per sentex, so listing every term costs ~3 ms on the starter, ~37 ms at
4.4k sentexes, ~500 ms at 60k, and would cost seconds at a million. The roster reads one
set and sorts it: ~0.09 ms, ~0.2 ms, ~1.9 ms at those same sizes (roughly 30×, 190× and
260×), because it is priced by the *vocabulary* — 120, 305, 2,545 terms — which grows far
slower than the KB. `term-count` is a set-size read and does not move at all.

The write side pays for it: one posting read per name on `index-sentex`, ~7% of the
index write (2.7µs a sentex), which is why the term set is computed once and handed to
the roster rather than rebuilt.

Every family on this page is a tax of that kind, and the tax is **counted rather than
timed**: `test/vaelii/assert_cost_test.clj` pins the exact number of index reads and
`index-sentex` / `unindex-sentex!` batch ops fourteen fixed workloads cost, so a family that
starts writing one more posting fails the suite rather than the stopwatch. That is the gate `lein perf`
cannot be — a constant added to every assert moves both of a ratio's readings and divides
out — and [profile.md](profile.md) has the demonstration.

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

Two consequences follow. An index written by one backend loads into another —
`index_dump_test` builds one KB and asserts all four project the *same set*, which is
also the check that catches a dense backend that has quietly stopped posting a family.
It deliberately cannot catch a family a dense backend still holds but holds
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

Four places check it, and none of them leaves the repair to a person. A **durable KV
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

The split is the point and it is not symmetric. **Resident**: the skeleton (`fcounts`
`foffsets` `fedge-tok` `fedge-tgt`), the roots' key *and offset* columns, the argument
roots' scope table, the token dictionary, and `roots-fallback.nippy`. **Mapped**: the leaf
handles (`fleaf-off` / `fhandles`) and the roots' handle run. The lookup walk reads the
skeleton at every frontier node — the leading-variable fan, measured on a corpus-sized
index at tens of thousands of lookups for one query — and a page fault there would cost a
disk seek apiece. The leaves are read once, at a walk's terminus. A write thaws whatever
it lands on, mapped or frozen alike, so an image is a read-phase structure.

**Every section on the resident side is path- or vocabulary-scaled, and the facts are all
on the mapped one.** That is the property the image exists for, and it holds section by
section rather than on average:

| Resident section | Scales with |
|---|---|
| CSR skeleton (`fcounts` `foffsets` `fedge-tok` `fedge-tgt`) | trie paths |
| roots' key and offset columns | the vocabulary, at the default `*min-indexed-depth*` |
| argument-root scope table | distinct `(predicate, position)` pairs |
| token dictionary | the vocabulary, on the same condition |
| `roots-fallback.nippy` | the term roster and the two slot rosters — names, not handles |

The scope table is what lets the argument roots ride the mapped run with every other
family. Their key carries two names where the rest carry one, so the `(predicate,
position)` half interns to a dense id of its own and rides the 24 bits `dense-roots`'
packed `long` reserves for an argument position (`argfam-id`). The table decodes those
ids, is bounded by predicates × arities rather than by facts, and rides `roots.csr` —
the file whose key column is its only reader, so the two are written in one pass and
discarded as one unit.

The blob's entry count and byte length are stamped and checked like a CSR section's all
the same: the slot roster is what a predicate-agnostic argument read descends through, so
a blob that thawed short would answer `#{}` at every position rather than fail.

It is a cache of derived state, so validity is the whole design: stamped with the record
store's slot fingerprint, checked on **every** open, discarded to `reindex` on any doubt.
Selected by name — `{:backend :disk-snapshot}`, the one pairing there is, since the stamp
is the disk record store's own slot fingerprint — and refused outright on a platform that
cannot replace a mapped file, since the publish is an atomic rename over one
(`docs/storage.md`).

## What the structural index does not reach

The structural trie above indexes nested subterms of a positive fact. Three things sit
outside it, and a query that needs one of them falls back to the coarser index rather
than failing:

- **The secondary argument roots** (`[:argument-root pred pos term]`) and rete's alpha
  buckets are keyed by **top-level position and arity**. A term nested inside an
  argument is not a key in either.
- **A `:false` body and a rule literal** are not structurally indexed, including the
  dotted-rest `(?pred . ?args)` shape. A dotted pattern changes its functor's arity, so
  neither the trie nor the argument roots can key it — it is not a stored-fact shape at
  all, and `res/hierarchical-literal?` excludes it by name, so the set-algebra retrieval
  hands it to `matches-visible`. What `res/candidate-handles` chooses between is six
  named access paths — `:trie`, `:structural`, `:arg-roots`, `:functor-extent`,
  `:negative-roots`, `:negative-fan` — each of which answers a **superset** that `unify`
  then filters exact; there is no seventh for a dotted shape.
- **The rule index is keyed by predicate**, not by full antecedent shape, so two rules
  whose antecedents differ below the predicate share a bucket.  A predicate is what the
  key *is*, so a variable in functor position turns on *where* it sits.  In an
  **antecedent** — `(?p ?x ?y)` as a trigger — it names none, so it is **refused** at
  `assert` with `:not-indexable` — [why refuse rather than accept
  it](defenses.md#a-variable-functor-rule-is-refused-not-silently-accepted).  In the
  **consequent** — `(implies (holds ?p ?x ?y) (?p ?x ?y))` — it is allowed: range
  restriction binds `?p` to a concrete antecedent, so the rule fires forward with the
  predicate ground, and its consequent is filed under the `:var-pred` catch-all (§3) for
  the backward read.  An `:inert` rule is exempt from the antecedent refusal, since it runs
  in neither engine, and its variable consequent keeps the dead `?var0` key rather than
  the live catch-all.

  A **generator's** stamped rule is the other exemption, and it is the one that buys
  something back: a variable functor there is a *hole*, filled with a concrete predicate
  before anything is keyed on it, so one generator ranges over a family of predicates
  while every rule the index sees has a concrete functor.  The generator may itself be
  stamped by one, and then the fill happens a level earlier — but the claim is unchanged
  either way, because it is about what reaches the index rather than about what is
  written: a functor **no enclosing level binds** is refused like any other, and a rule
  nothing encloses has no enclosing level to bind one.  See
  [generators.md](generators.md).
