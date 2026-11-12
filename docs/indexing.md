# Indexing

- **Covers:** the index families' key shapes — the trie, the secondary roots, the rule
  and exception indexes, the term index, the term-name set, the taxonomy's supporter
  families, the mint family, the calendar index and the `natFormula` arguments — what each
  answers, and what a read scoped to the contexts a reader sees costs.
- **Not here:** the dense/columnar representations these families are packed into →
  [density.md](density.md); the record store and the protocols the index sits beside →
  [storage.md](storage.md).
- **Assumes:** sentex, handle, context, canonical form → [glossary.md](glossary.md).

`vaelii.impl.kv`. Seven indexes over the same sentexes, all in the index store: the
positional trie, the secondary roots, the rule index, the exception re-check index, the
inverted term index, the term-name set beside it, and the taxonomy's supporter families.
An eighth, the mint family, indexes the stored justifications of argument declarations.
`KvIndexStore` holds the logic over a `KvBackend` substrate (see
[storage.md](storage.md#the-index-is-written-once--kvbackend)), so a backend just says how a key, a counter, and a set live in a store; the one
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
| `[:predicate-extent :count [pred]]` | integer | how many facts have functor `pred`, any arity, either polarity, in every context |
| `[:predicate-extent :children [pred]]` | set | the contexts that state such a fact |
| `[:predicate-extent :handles [pred ctx]]` | set | the handles of those facts stated in `ctx` |
| `[:argument-root :count [pred pos term]]` | integer | how many of `pred`'s facts hold `term` at argument position `pos`, in every context |
| `[:argument-root :children [pred pos term]]` | set | the contexts that state such a fact |
| `[:argument-root :handles [pred pos term ctx]]` | set | the handles of those facts stated in `ctx` |
| `[:argument-slot pos term]` | set | the predicates present at that slot (names, not handles) |
| `[:unary-slot term]` | set | the predicates `term` is the lone argument of (names, not handles) |
| `[:unary-multi]` | set | every term the unary predicate set lists two or more predicates of (terms, not handles) |
| `[:unary-kept pred]` | set | the terms of `[:unary-multi]` whose unary predicate set lists `pred` (terms, not handles) |
| `[:unary-kept-types]` | set | every predicate whose `[:unary-kept pred]` holds a term (names, not handles) |
| `[:unary-denied pred]` | set | every term a stored `(not (pred term))` names (terms, not handles) |
| `[:unary-denied-types]` | set | every predicate whose `[:unary-denied pred]` holds a term (names, not handles) |
| `[:shape-tuple :count [f n]]` | integer | how many positive facts of functor `f` hold `n` arguments, in every context |
| `[:shape-tuple :children [f n]]` | set | the contexts that state such a fact |
| `[:shape-tuple :handles [f n ctx]]` | set | the handles of those facts stated in `ctx` |
| `[:shape-lengths f]` | set | the argument counts the positive facts of `f` are stored at (numbers, not handles) |
| `[:calendar :count [f frame y m]]` | integer | how many facts of functor `f` name a time with a point in month `m` of year `y`, in frame `:local` or `:utc`, in every context |
| `[:calendar :children [f frame y m]]` | set | the contexts that state such a fact |
| `[:calendar :handles [f frame y m ctx]]` | set | the handles of those facts stated in `ctx` |
| `[:calendar-buckets f]` | set | the `[frame y m]` of every `:calendar` node of `f` (triples, not handles) |
| `[:nat-argument :count [f pos term]]` | integer | how many positive `(natFormula K (f …))` maps hold `term` at argument `pos`, in every context |
| `[:nat-argument :children [f pos term]]` | set | the contexts that state such a map |
| `[:nat-argument :handles [f pos term ctx]]` | set | the handles of those maps stated in `ctx` |
| `[:rule-antecedent :count [key]]` | integer | how many rules take an antecedent on `key` (a predicate, or `[:not pred]`) |
| `[:rule-antecedent :children [key]]` | set | the contexts that state such a rule |
| `[:rule-antecedent :handles [key ctx]]` | set | the handles of those rules stated in `ctx` |
| `[:rule-consequent :count [key]]` | integer | how many rules conclude `key` |
| `[:rule-consequent :children [key]]` | set | the contexts that state such a rule |
| `[:rule-consequent :handles [key ctx]]` | set | the handles of those rules stated in `ctx` |
| `[:rule-antecedent-keys]` | set | every antecedent key some stored rule takes (keys, not handles) |
| `[:rule-extent :count [kind]]` | integer | how many rules of `kind` are stored: `:rule` every rule, `:solve` the rules a solve reads, `:lazy` the lazy-forward rules |
| `[:rule-extent :children [kind]]` | set | the contexts that state such a rule |
| `[:rule-extent :handles [kind ctx]]` | set | the handles of those rules stated in `ctx` |
| `[:opposed :count [body]]` | integer | how many facts of `body`, either polarity, are stored while both polarities are |
| `[:opposed :children [body]]` | set | the contexts that state such a fact |
| `[:opposed :handles [body ctx]]` | set | the handles of those facts stated in `ctx` |
| `[:opposed-bodies]` | set | every body stored in both polarities (bodies, not handles) |
| `[:opposed-between f]` | set | the bodies of `[:opposed-bodies]` of functor `f` whose arguments are all predicate-spelled (`nm/between-predicates?`) |
| `[:opposed-functor f]` | set | the other bodies of `[:opposed-bodies]` of functor `f` |
| `[:self-tuple :count [pred]]` | integer | how many ground positive binary self tuples `(pred a a)` are stored |
| `[:self-tuple :children [pred]]` | set | the contexts that state such a tuple |
| `[:self-tuple :handles [pred ctx]]` | set | the handles of those tuples stated in `ctx` |
| `[:arity-binding :count [pred kind value]]` | integer | how many facts bind `pred`'s length as `kind` (`:exact`, `:min` or `:var`) to `value` (nil for `:var`) |
| `[:arity-binding :children [pred kind value]]` | set | the contexts that state such a fact |
| `[:arity-binding :handles [pred kind value ctx]]` | set | the handles of those facts stated in `ctx` |
| `[:arity-binding-kinds pred]` | set | the `[kind value]` of every `:arity-binding` node of `pred` (pairs, not handles) |
| `[:arity-bound]` | set | every predicate holding a stored length binding (names, not handles) |
| `[:opposed-in ctx]` | set | the handles of the facts stated in `ctx` of every body stored in both polarities |
| `[:tax-support :count k]` | integer | how many handles support taxonomy key `k` (`[:genl a b]`, `[:genlCx a b]` or a flat-cache key) |
| `[:tax-support :children k]` | set | the contexts that state a supporter of `k` |
| `[:tax-support :handles (conj k ctx)]` | set | the handles of those supporters stated in `ctx` |
| `[:tax-installs h]` | set | the taxonomy keys handle `h` installs (keys, not handles) |
| `[:tax-named :count [rel f]]` | integer | how many positive `(f (sentexHandle H))` facts, `f` `except` or `defeat`, are stored whose `H` installs a key of relation `rel` (`:genl`, `:genlCx` or `:flat`) |
| `[:tax-named :children [rel f]]` | set | the contexts that state such a fact |
| `[:tax-named :handles [rel f ctx]]` | set | the handles of those facts stated in `ctx` |
| `[:exception-index pred]` | set | rules whose exception query mentions `pred` |
| `[:exception-index :rules]` | set | every rule carrying an exception |
| `[:term-index term]` | set | sentexes containing `term` anywhere, any nesting |
| `[:term-names]` | set | every symbol term the term index is keyed by — the vocabulary |
| `[:mint :count [term]]` | integer | how many records a stored mint justification concludes about `term`, in every context |
| `[:mint :children [term]]` | set | the contexts holding such a record |
| `[:mint :handles [term ctx]]` | set | the handles of those records in `ctx` |
| `[:mint-terms]` | set | every term some filed mint is about (terms, not handles) |
| `[:mint-in :count []]` | integer | how many records are filed as mints |
| `[:mint-in :children []]` | set | the contexts holding a filed mint |
| `[:mint-in :handles [ctx]]` | set | the handles of the mints filed in `ctx` |
| `[:mint-rules]` | set | the `[kind handle]` of every stored rule of `kv/mint-rules` (pairs, not handles) |

The registry's `:shape` ([below](#the-index-family-registry)) says which families keep
explicit counters: the positional trie and the count tries, because a node's count
aggregates the leaves beneath it. Every other
family is a flat set whose cardinality is its own size, so a count cannot drift from its
extent.

The count tries share one shape. A node is the path above the context — `[pred pos
term]`, `[pred]`, `[key]`, `[kind]`, `[body]`, `[f n]`, `[pred kind value]`, a taxonomy key,
`[term]`, `[]` — and holds three keys: its count, its children (the contexts
that state something under it) and, per child, the leaf of that context's handles. So
"what is stated under this node in the contexts a reader sees" is the node's children
intersected with the reader's ancestor set, then one leaf read per context kept
([By-context reads](#by-context-reads)).

**A counter is a cardinality, so `kv-decrement` is floored at zero.** The two folds that
implement it — `kv/apply-op` and the transient twin a bulk load takes — both stop at 0,
and so does every backend that counts for itself, because the disk store replays its WAL
through the same fold and a floor on one side alone would make a reopened index disagree
with the one that wrote it. It adds no work (the fold has the new value in hand) and
changes no decision on the ordinary path, where a retraction reads the reply to find the
nodes that emptied and asks `<= 0`. It removes a negative `[:trie :count prefix]`,
which `plan/prefix-estimate` returns as a match bound: not a wrong estimate but a meaningless one.

**The retraction is checked, the assert is not, and the asymmetry is the threat model.**
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

A retraction the membership probe refuses **logs** rather than passing silently (`::unindex-absent`, `:warn`, on
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
`lein lint`'s **E16** lists the implementers — this namespace, `columnar`, the disk
snapshot, `kb` and `resolution`, and the dump — and fails a raw read anywhere else
([nmtms.md](nmtms.md#belief-filtering-is-a-namespace-boundary)).

## The index-family registry

`kv/index-families` holds one row per key tag, the first element of every key above, and
three readers decide from it rather than from spelled tags:

| Field | Values | Decides |
|---|---|---|
| `:shape` | `:trie`, `:count-trie`, `:set`, `:counter` | which keys the family writes: a count trie's are `[tag :count\|:children node]` and `[tag :handles (conj node ctx)]` |
| `:leaf` | `:handles`, `:names`, nil | whether a posting holds handles; `dense-kv` packs a `:handles` leaf into int postings ([density.md](density.md)) |
| `:context-last?` | boolean | whether the key's last level is the context |
| `:children?` | boolean | whether a node lists the contexts below it, which a by-context read intersects ([By-context reads](#by-context-reads)); the context root and `[:opposed-in ctx]` list none |
| `:root` | a family tag | the name set one level above the family's nodes (`[:rule-antecedent-keys]`, `[:opposed-bodies]`, `[:mint-terms]`, …), which the key builders read |
| `:canon?` | boolean | whether a key term is `sx/canon`'d: the argument root, the two slot predicate sets, the `natFormula` arguments and the term index |
| `:source` | `:sentex`, `:rule`, `:justification`, `:taxonomy` | which write posts the family; a records-only import skips the `:justification` families (`kv/justification-family-entry?`), since it stores no justification |
| `:class` | `:access-path`, `:scan-recoverable`, `:sole-witness` | what a KB without the family would lose, with `:class-evidence` |

`dense-roots` routes the families it packs from its own table, keyed by family tag; a tag
absent from that table goes to its fallback.

**The class says what a missing family costs.** A missing family does not make a question
slower: the read answers less than the truth and the KB reports it as complete, as an
index in an unrecognized layout does (`kv/index-layout-version` and its checks exist for
that case).

- **`:access-path`**: another path returns the identical answer at a cost bounded by
  something smaller than the KB. `:class-evidence` names the differential oracle
  (`:oracle`) and the families that other path reads (`:via`). The argument root's other
  path is the trie (`arg_root_retrieval_test`, `matches_hierarchical_test`); the predicate
  extent's and the two slot predicate sets' is the term index, filtered by the record
  (`arg_root_retrieval_test/the-families-agree-with-the-term-index`), and so is the
  `natFormula` arguments' (`index_test/the-nat-argument-family-agrees-with-the-term-index`).
- **`:scan-recoverable`**: a scan of the whole store returns the identical answer, at a
  cost linear in the KB. `:class-evidence` names the writes that read the family
  (`:writes`). A write's cost is bounded whatever the content, so only a family no write
  reads could be served by a scan, and only the term-name set is one: `vaelii.core/terms`
  and the vocabulary pass read it. The term index is read on writes (the `sentexHandle`
  meta lookups, the trigger entailments, the transitive seeds).
- **`:sole-witness`**: no other path answers, and without the family an answer changes or
  a belief goes stale: the trie, the rule indexes and the rule extent, the exception
  index, the taxonomy's supporters and the mint family. `:class-evidence` names the
  readers.

Every KB writes every family; no option declines one. `index_test/every-key-the-starter-writes-names-a-registry-row-with-a-class`
fails a key whose tag has no row, a row without a class, and an oracle that does not
resolve.

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

The two solver slots spell the rule's `:effect` — `true` in the first for a choice rule,
`:hard` / `:soft` in the second for a constraint rule — and are **constant slots**, `nil`
for a `:derive` rule, so every rule keys at one depth. That is not cosmetic: a variable in a path
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
slot. This answers *positional* pattern queries. Given a set of contexts, `lookup` keeps
the context slot to that set ("By-context reads" below).

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
`res/*structural-index*` decides whether `candidate-handles` uses the structural trie
(narrow on the deep positions) or the functor extent (a correct fallback superset).
The level-0 raw lookup reads `p/lookup` directly, so it is
always structural; `sentexes-matching` and the matching levels go through `candidate-handles`, so
the switch applies to them too — but only to the candidate *source*, never the matches
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
the planner's distinct-value count (`plan/prefix-summary`) carries no phantom branches.

**How many children is its own read**, not `(count (children …))`. `family-child-count`
(`reads/stored-count-children`)
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
answering wrongly (it fails safe), which is why the layout version is written and checked
at open — section 7 below.

## 2. The secondary roots

The trie is ordered `[pred args… ctx]`, so it narrows only left-to-right: it can
count "predicate P" or "P with arg1 X", but **not** "context C" (context is the
deepest level, never a prefix) and not "X in argument position 2" without fixing
everything to its left. One flat root and two count tries fill that in, plus
the slot predicate set the predicate-agnostic reads union over:

```
[:context-root <context>]    -> #{handles}   every sentex asserted there (rules included)
[:predicate-extent :count    [<pred>]]       -> n          facts whose functor is pred — any
                                     arity, either polarity (a negative fact enters
                                     its positive body's functor), in every context
[:predicate-extent :children [<pred>]]       -> #{ctxs}    the contexts stating one
[:predicate-extent :handles  [<pred> <ctx>]] -> #{handles} those stated in ctx
[:argument-root :count    [<pred> <pos> <term>]]       -> n          pred's facts holding term
                                     at 1-based pos, in every context
[:argument-root :children [<pred> <pos> <term>]]       -> #{ctxs}    the contexts stating one
[:argument-root :handles  [<pred> <pos> <term> <ctx>]] -> #{handles} those stated in ctx
[:argument-slot <pos> <term>]        -> #{preds}    the predicates present at that slot —
                                     entered when the predicate's node is created and
                                     retired when it empties, so a predicate-agnostic
                                     read is a union over a handful of nodes
[:unary-slot <term>]                 -> #{preds}    the predicates term is the LONE
                                     argument of — the same set narrowed to
                                     arity 1, which is what a membership read asks for
```

The context root's cardinality is the set's own size. A rule contributes only its
context; its predicates live in the rule indexes below.

**The predicate extent is a count trie over the path `[pred ctx]`.** Its node `[pred]`
holds the count `count-with-functor` and `plan/est-matches` read, and its children are
the contexts that state a `pred` fact; `sentexes-with-functor` unions every child's leaf,
and a predicate stated in one context hands that leaf back as stored. So
`children [defeat]` is every context a `defeat` is stated in, and "is a `defeat` stated
where reader R sees" is `children [defeat] ∩ context-up(R)`, with no fan over the
defeats' targets (`exc/sees-defeat?`).

**The argument roots are a count trie over the path `[pred pos term ctx]`**, with the
positional trie's three keys per node. A node `[pred pos term]` holds the count (the
number `plan/est-matches` and `count-with-arg` read) and its children, which are the
contexts that state such a fact; the leaf under each child holds that context's
handles. So `children [defeat 1 (sentexHandle H)]` is every context `H` is defeated in.
Only the node and leaf levels are stored: no read asks for `[pred]` or `[pred pos]`.
The reads a settle leans on ask for a node: its handles in the contexts a reader sees,
the predicate-agnostic **union** of the nodes at a `(pos, term)`, or a node's count.

All of that is `vaelii.impl.kv`'s, and none of it is a backend's. `KvIndexStore` spells
the keys, writes a fact's leaf beside its context root and predicate-extent leaf, and adds
its context to each node's children and one to each node's count. A retraction reads the leaf and the
children before its batch: an emptied leaf takes its context out of the children, and an
emptied node loses its count key. The two agnostic reads union over the
`[:argument-slot pos term]` slot predicate set — the set is what keeps them answerable without a
second copy of every posting, and it holds one predicate in the common case, a handful
otherwise.

A backend may hold the family however it likes underneath: `dense-roots` packs a leaf
and a node's children into longs, holds the children as context ids, and answers an
argument node's count from its leaves (density.md); the rest keep flat entries. Each is a
representation, invisible above the backend, and `kv-entries` re-emits the flat shape
whichever one it is — the shape the key table above describes.

### The unary predicate set, and why position 1 was not narrow enough

`[:unary-slot term]` is the slot predicate set restricted to arity 1, and it exists
because a *membership* question is not a position-1 question. `core/types-of` asks what
types a term holds — the retrieval `isa?` and `checks/disjoint-problems` are built on, so
it runs on every unary assert — and the types are the arity-1 facts whose lone argument is
that term. Position 1 does not separate them: `(dog Muffet)` and `(likes Muffet Tom)` both
put `Muffet` at argument 1, share the `[:argument-slot 1 Muffet]` entry, and share the trie
node below it, because the trie's next level is the *second argument* for one and the
*context* for the other. So the read fetched the record behind every fact naming the term
at argument 1 and kept the arity-1 ones: a densely described individual paid its whole
description on every assert of a type for it, to find the handful of types it holds.

The set's members are predicates, so it is vocabulary-scaled beside the slot predicate set
rather than a second copy of the postings, and `reads/as-stored-unary-with-arg-global`
reads it exactly as `reads/as-stored-with-arg-global` reads the other — one name-set read,
then the predicate-scoped postings.

**It is a deliberate superset.** The entry is written by every unary fact rather than
reference-counted on the first, because the node that reference-counts the other name sets
is `[pred 1 term]`, which a *binary* fact of the same predicate about the same term also
creates — so a check read off it would skip the unary entry whenever the binary fact
arrived first, and a missing entry there loses a membership.
Retirement is the mirror: a unary fact retires the entry with its position-1 slot and a
fact of any other arity leaves it alone, so a KB of binary facts pays nothing for a set
it never enters, and the entry outlives the last unary fact wherever a binary one empties
the node. A stale entry costs one posting read and `types-of`'s arity filter drops it;
the asymmetry is the point.

`[:unary-multi]` lists the terms whose unary predicate set holds two or more predicates: a term
joins when an entry is its second predicate and leaves when an entry leaves it one, both
read off the set's size before the write (`kv/slot-adds`, `slot-retires`). The
membership candidates read it at recover for the terms that can hold two memberships of
distinct types (`reads/as-stored-unary-multi-terms`); it inherits the unary predicate set's superset.
`[:unary-kept pred]` lists the same terms under each predicate their unary predicate set lists, and
`[:unary-kept-types]` the predicates listing one. The write that adds a term's second
predicate lists the term under both, a further predicate lists it under that one, and the
write leaving a term one predicate takes it out under both (`kv/kept-adds`,
`kept-retires`). A declaration or a `genl` edge moving reads the kept terms under the
types it moves there (`reads/as-stored-unary-kept-terms`): the members of a type holding
no second type are not read, which `lein perf`'s `membership-declaration-arrival` holds
flat in them. `[:unary-denied pred]` lists each term a stored `(not (pred term))` names, and
`[:unary-denied-types]` the predicates listing one: the first denial of a body lists its
term and the last takes it out, read off the trie's `[:false (pred term)]` count before the
write (`kv/denied-adds`, `denied-retires`). A cover or a `genl` edge moving reads the
terms with a denial under the types whose cover nogoods it moves there
(`reads/as-stored-unary-denied-terms`), so a cover arriving reads none of the denials
under other types.

They are read through `core`: `sentexes-in-context` / `count-in-context`,
`sentexes-with-functor` / `count-with-functor`, `sentexes-with-arg` /
`count-with-arg`, and the unary predicate set through `reads/as-stored-unary-with-arg-global`. Two places rely on them for speed rather than
convenience: `core/types-of` goes straight to the unary predicate set instead of scanning every
sentex mentioning `x` anywhere, or every one holding it at argument 1; and
the provers' `est-bindings` cost
model reads the predicate extent's count, which — unlike the trie's `count-at [pred]` —
also sees negative facts (they key under `:false` and would otherwise estimate 0).

### Retrieval from the roots (`res/match-one`)

The trie narrows only left-to-right, so a pattern that binds a *later* argument while
leaving the first a variable — `(parentOf ?x Tom)`, the second half of a grandparent
join — has no selective prefix and the trie fans out over every first-argument value
(one lookup per node). The roots are indexed by argument position and do not care,
so `res/match-one` consults them for exactly that case, conditional on
`res/*arg-root-retrieval*` (default on):

- **Argument-root retrieval.** When a ground argument sits after a variable, or the
  pattern's context is ground and an argument is open (the trie reaches its context
  level only after fanning over that argument), the candidates come from the argument
  roots instead of the trie, read in the pattern's context when it is ground. The set
  returned is a **superset** of the trie's hits — the roots don't constrain numeric
  arguments — and the existing `unify` filters it to the identical set, so *which*
  sentexes match never changes. A pattern whose arguments are all variables, in a
  ground context, reads the predicate extent's leaf in that context
  (`:context-extent`), where the trie fans over every stored argument first. The leading-variable `match-pattern` (the backward /
  `ask` / forward-join path) is flat in the extent where the trie fan is O(N) per
  call — `lein perf`'s `arg-root-retrieval` check enforces the flatness, and
  `arg_root_retrieval_test` asserts the set-equality.
- **Multi-column narrowing (`sentexes-with-args`).** Knowing more than one term should
  narrow on all of them, so *every* ground argument's predicate-scoped node is
  intersected: `(rel ?x B C)` reads the nodes `[rel 2 B]` and `[rel 3 C]`, takes the
  contexts both list (and the reader sees), and intersects the two leaves in each of
  them. The scoping means a named functor needs no predicate-extent intersection, and a
  single bound argument is one node with nothing intersected at all. An individual shared at one position
  across K predicates yields a candidate set at the true match count rather than K×
  it **by construction** — the bucket read is the literal's own predicate's. What an
  intersection *costs* is the backend's business: a
  flat-map index folds `clojure.set/intersection` over sets it already holds, and a dense
  one narrows in the postings' own representation so a rare argument bound on a hot
  predicate costs the rare side ([density.md](density.md)).
- **An open functor is the same shape at level 0.** `(?type Muffet)` — what types does
  Muffet hold, as a *pattern* rather than a `types-of` call — puts the variable at the
  first path token, so every ground argument is stuck behind it and the trie can only
  fan out over its whole root child set, i.e. **every functor in the KB**. That fan is
  linear in the vocabulary, which in a broad ontology is the largest thing there is.
  The predicate-agnostic read spans every functor by construction — a union of the
  scoped nodes over `[:argument-slot 1 Muffet]` — so it answers in a read per predicate
  present at that slot (usually one, a handful when several predicates share it),
  with a `nil` functor to intersect: **flat in the vocabulary** where the trie fan is
  linear in it. A pattern with nothing indexable to lead with (`(?type ?x)`,
  `(?p ?x 1970)`) keeps the trie, since there is no root to read. A stored `(dog Muffet)`
  answers a positive open functor with `dog` and with every super-predicate of `dog`
  visible from the reader (`res/with-open-functor-supers`), as `(animal ?x)` reaches it
  through `animal`'s spec closure; a functor variable that is also an argument, or one
  under a negation, binds the stored functor alone.
- **Hierarchical retrieval (`res/matches-hierarchical`).** A context-scoped
  `(p a ?x)@c` is an intersection over three hierarchies — predicate ∈ `specs(p)`,
  context ∈ `context-up(c)`, arguments unify — which `matches-visible` answered by a
  *product* of `|specs| × |context-up|` trie walks. Leading with the bound argument's
  predicate-scoped nodes — one per sub-predicate, the predicate filter satisfied by
  which nodes are read — and intersecting each node's contexts with the cached closure
  collapses the product to one node read per sub-predicate: **flat in the context
  hierarchy's depth** where the fan-out is O(depth). Where the term holds no more facts
  at the position than the closure has predicates (`res/*lead-side*`), the slot predicate set
  names the predicates holding it, and only those in `specs(p)` have their node read.
  No source hands the matcher a candidate of another predicate, so no record is fetched
  to test its functor: on the starter KB's load this removed 133 of the 183 fetches the
  slot-led reads made. The buckets are walked **lazily** — each handed back by
  reference, the per-spec fan a `lazy-mapcat`, consumed only as far as the caller
  reads — so an existence check touches one bucket and short-circuits like the
  fan-out; this is the **default** (`res/*hierarchical-retrieval*`), with the var
  bound false giving the reference fan-out `matches_hierarchical_test` proves it
  equal to. A literal whose arguments are ground atoms, two or more of them indexable,
  followed only by variables — `(scoreOf Team Year ?v)` — reads the trie under that
  prefix per sub-predicate instead of intersecting two argument roots: the walk costs
  the stored tuples extending the prefix, and the intersection costs the smaller root,
  which grows with the KB when both terms are widely used (`lein perf`'s
  `tuple-mark-determinant-write`). A candidate answers **once** unless the literal has
  a mirror to probe at all — a concrete functor, exactly two arguments, and some sub-predicate declared
  `symmetric`. Without one the handle is the whole dedup key and the walk is a `keep`
  over the candidates. Only where a mirror can bind one stored fact twice — an all-variable
  pattern over a stored `(sibOf Rex Tib)`, which binds both ways round — does the key
  become `[handle bindings]` and a candidate yield a sequence rather than an answer.
  A literal with `greaterThan` among its sub-predicates takes the reference fan-out:
  `greaterThan` is stored as `lessThan` with its arguments reversed
  ([canonicalization.md](canonicalization.md#comparison-siblings-folded)), and the
  set-algebra path reads a candidate's functor and argument order as the literal writes
  them (`res/folded-spec?`).
- **A scoped read costs the contexts its reader sees, not the matches stored elsewhere.**
  A read with a predicate and a bound argument reads the node's children and keeps those
  in the reader's ancestor set — `matches-hierarchical` passes `context-up`, and the
  level-2 matcher passes the pattern's own ground context — iterating the smaller of the
  two sets, then reads the kept contexts' leaves. No record is fetched for a candidate
  the reader cannot see, so `(psaLikes PSATom ?x)` read from `CxPerf` costs one leaf read
  whether 1,000 or 16,000 other `psaLikes` facts about `PSATom` sit in contexts `CxPerf`
  does not see: `lein perf`'s `scoped-arg-read` reads 0.48 ms and 0.36 ms per twenty
  reads of both retrievals, 0.76×, where the read that fetched every candidate read
  23.2 ms and 326.2 ms, 14.09×. An unscoped
  read unions every child's leaf. With several bound arguments the read intersects per
  context: the contexts every node lists and the reader sees, then one `kv-intersect` of
  the leaves in each. The alternative, unioning each node's visible leaves and
  intersecting the unions, was measured slower in every shape tried — 1.7× to 75× on
  two 2,000-handle columns, sixteen contexts of 200 and 256 contexts of 4, on the flat
  and the dense backend.

**Why the context is the last level of both tries, and what that costs a scoped read.**
The positional trie keys `[pred args… ctx]` so that its `[pred]` prefix counts the
positive facts of `pred` in every context, and so that every rule keys at one depth. The
predicate extent's node `[pred]` counts those facts and the negative facts of `pred` as
well, which the trie keys under `[:false <body> <context>]`; `plan/est-matches` reads both
counts. The argument roots key `[pred pos term ctx]` for the
argument's version of the same reason: the node count is the number the planner reads
for a bound argument, whatever contexts state it. A context-first order
(`[ctx pred pos term]`) would make every read fan over the reader's whole ancestor set
— one probe per ancestor context, though most terms are stated in one or two — which is
the open-functor fan of `(?type Muffet)` moved to another column. With the context last,
a scoped read of one node costs min(|children|, |ancestor set|) membership probes plus
one leaf read per context it keeps. The positional trie's walk reaches its context level
last, and `lookup` given a context set keeps that level to the set the same way, so the
walk under a ground prefix (`:hier-trie-prefix`) reads only the leaves its reader sees.
`lein perf`'s `scoped-trie-prefix-read` reads `(ptpScore PTPTeam PTPYear ?v)` from
`CxPerf` beside 1,000 and 16,000 other matches, sixteen values of `?v` each stated in
n/16 contexts `CxPerf` does not see: 1.26 ms and 0.75 ms per twenty reads, 0.60×, where
the walk that fanned the context level over every child read 28.3 ms and 431.9 ms,
15.26×. The walk still visits every stored value of the trailing variables, in every
context, before it reaches the context level, and the context set does not narrow that
fan. `lead-candidates` therefore leads a ground prefix from the argument roots instead,
intersected per context in the reader's ancestor set, when `res/arg-lead` finds them
smaller. The rule reads counts the index holds: the trie count c under the prefix, and
for each bound argument its facts in the ancestor set, one leaf count per context the
argument node lists and the set holds. The argument roots lead when c exceeds the size
of the ancestor set and some bound argument holds fewer than 4c facts there
(`arg-lead-ratio`). A prefix of no more tuples than the ancestor set has contexts, the
partially bound literal of a join among them, keeps the walk and pays one count read.
Timed as leads alone, with 1,024 or 4,096 tuples
under the prefix and the bound arguments holding more facts in the reader's context, the
intersection costs 0.004 to 0.86 of the walk at up to 4.5 facts per tuple and 1.1 to 4.0
of it at sixteen on the flat backend, which puts the crossover between 5 and 16; on the
dense and columnar backends it costs under 0.14 of the walk at every ratio to sixteen.
So 4 sits below every crossover measured, and a hub shape, one tuple under the prefix
against thousands of facts per argument in the reader's context, stays on the walk.
`lein perf`'s `scoped-trie-prefix-fan-read` spreads the matches over n values in
sixteen contexts `CxPerf` does not see: 0.27 ms and 0.27 ms per twenty reads, 0.98×,
where the walk read 17.8 ms and 405.9 ms, 22.9×.
A variable context has no ancestor set, and the intersection fans over every context its
first argument's node lists. There the rule reads each bound argument's node count n and
its number of contexts k, two count reads, and the argument roots lead when some
argument has n < 4c and k < c. The argument with the fewest contexts leads the
intersection. A prefix of one tuple keeps the walk and pays one count read. Timed as
leads alone with 4 to 1,024 tuples under the prefix, where the tuples outnumber the
argument's contexts, the intersection costs 0.05 to 0.57 of the walk below 4 facts per
tuple on the flat backend, whose crossover lies between 4 and 8, and at most 0.58 of it
at every ratio to sixteen on the dense and columnar backends. Where the tuples do not
outnumber the contexts (4 or 16 tuples, one to a context), it costs 1.0 to 1.6 of the
walk below 4 facts per tuple on all three. `lein perf`'s `variable-context-prefix-read` reads 64 matches beside
n facts that one bound argument rules out, four to a context: 1.68 ms and 1.32 ms per
twenty reads, 0.79×, where the walk read 2.30 ms and 2.15 ms, and an intersection led by
the argument stated in n/4 contexts read 1.97 ms and 10.42 ms, 5.30×.
The functor extent (`:hier-functor-extent`) reads each sub-predicate's predicate
extent in the reader's ancestor set. `lein perf`'s `visibility-reading` times what an
`except` hides, not this.

### By-context reads

The argument roots, the predicate extent, the rule extent, the consequent index and the
positional trie's last level answer one question the same way: what is stated under a node in the contexts
a reader sees. The read takes the reader's ancestor set, intersects it with the node's
children — the children filtered by membership in the set, or the set probed against
the children, whichever is smaller — and reads the leaf of each context it keeps. It costs **min(|children|, |ancestor set|)
membership probes plus one leaf read per kept context**, whatever is stated in the
contexts the reader does not see. A nil set reads every child on the named reads below; a
family method takes `p/every-context` for that instead and refuses nil (see "The family
methods" below).

| Read | Family | Reached from |
|---|---|---|
| `sentexes-with-args pred pos-terms ctxs` | argument roots | `matches-hierarchical`, `candidate-handles` |
| `lookup pattern ctxs` | positional trie, its last level | the `:hier-trie-prefix` lead |
| `sentexes-with-args pred [] ctxs` (`reads/as-stored-with-functor-in`) | predicate extent | the functor-extent leads, `:context-extent`, `exc/visible-exception-index` |
| `family-children :predicate-extent [pred] ctxs` (`reads/stores-in?`) | predicate extent, its children only: no leaf read | `exc/sees-defeat?`, `exc/exempting-at?` |
| `family-handles :rule-extent [:rule] ctxs` (`reads/as-stored-rules-in`) | rule extent | `concluding-rule-handles` for an open functor |
| `family-handles :rule-consequent [pred] ctxs` (`reads/as-stored-rules-by-consequent-in`) | consequent index | `concluding-rule-handles`, from `provers/candidate-rules` |

`lein perf`'s `scoped-defeat-read` asks "is a `defeat` stated where `CxPerf` sees" with
1,000 and 16,000 placed defeats in sixteen contexts `CxPerf` does not see, and
`scoped-rule-read` reads `CxPerf`'s backward candidate rules for a bound and an open
functor with as many rules in those contexts. The defeat question reads 0.028 ms and
0.029 ms per twenty reads, 1.05×, where the scan of every stored defeat by target read
2.85 ms and 43.57 ms, 15.28×; the rule read reads 0.16 ms and 0.12 ms, 0.75×, where the
read that fetched every rule's record read 24.9 ms and 543.9 ms, 21.82×.

`sentexes-matching` shares this argument-root retrieval — it routes through `res/raw-match` (the
level-2 matcher), so a leading-variable-then-ground-arg `sentexes-matching` (`(parentOf ?x Tom)`)
diverts to the predicate-scoped argument root (the node `[parentOf 2 Tom]`, read in the pattern's own context) instead of
paying the full first-argument trie fan. The `lookup` levels reach it wherever they *match*
(level 2 is `raw-match`, level 4 is `matches-visible`); level 0 (`:raw`) stays a bare
`p/lookup` by contract — it reports the handles at an index location, not the believed
matches, so the argument-root superset would be wrong there.

The roots also underwrite the incremental forward-chain matcher's RAM alpha memories
([inference.md](inference.md), "Incremental rule matching").

### The family methods

Every family outside the named reads above is read through `IndexStore`'s `family-*`
methods ([storage.md](storage.md), "The family methods"), and only from a
`vaelii.impl.reads` entry point: lint E16 fails a `p/family-*` read, a `p/count-at` or a
`p/leaf-at` anywhere else under `src/` but the two implementers and the image writer.
The entry point names the family and tallies its `:reads` ([profile.md](profile.md)).

A read over every context passes `p/every-context`, and a family method given nil for its
contexts throws `:bad-args`, so no forgotten ancestor set reads past the reader. The
`reads` entry point that passes the sentinel ends in `-global`
(`as-stored-supporters-global`, `as-stored-rules-in-global`, …), and E16 fails a call to
one from a `(file, top-level def)` pair outside `E16_GLOBAL_ALLOW`, in the style of
E17's taxonomy allowlist. A composite read costs the same backend reads as one: a
supporter read is the node's children and a leaf per child, the functor census
(`as-stored-contexts-with-functor`) a children count and then the children in the set,
and the argument census (`stored-census-with-arg-global`) the node's count and its
children count.

### The bodies stored in both polarities

A body `B` is **opposed** while a `(not B)` and a `B` are both stored, in any contexts, and
its members are the handles of both polarities. The negation family places a nogood over
each pair of a member of each polarity ([nmtms.md](nmtms.md#the-nogood-families)), and
reads three keys:

```
[:opposed :count    [<body>]]       -> n          the body's members, in every context
[:opposed :children [<body>]]       -> #{ctxs}    the contexts stating one
[:opposed :handles  [<body> <ctx>]] -> #{handles} those stated in ctx
[:opposed-bodies]                   -> #{bodies}  every opposed body
[:opposed-between <f>]              -> #{bodies}  those of functor f between predicates
[:opposed-functor <f>]              -> #{bodies}  the rest of functor f
[:opposed-in <ctx>]                 -> #{handles} the members stated in ctx, of every body
```

`index-sentex` and `unindex-sentex!` post the family from the sentence in hand and the
trie's counts before the write (`kv/opposed-adds`, `kv/opposed-retires`), never from a
record read, so a bulk load whose record store buffers its records posts what single
writes post. A positive fact reads the `[:false B]` count and stops when it is 0. The body
joins on the first record of its second polarity, which enters the other polarity's
records with it, and leaves on the last record of either polarity, which takes every member
out; `[:false B]` counts the denials exactly, and the node's count less the denials counts
the positives. `[:opposed-bodies]`'s size answers whether any body is opposed in one read,
which every settle asks before placing a pair (`reads/stores-opposed?`).

`[:opposed-between f]` and `[:opposed-functor f]` split the opposed bodies of a symbol
functor `f` by `nm/between-predicates?`, the test `decide/forced-literal?` applies to a
`:forced-between-predicates` functor. A body joins and leaves its set with
`[:opposed-bodies]`. `exc/yielding-reads?` asks whether a forced-monotonic literal is
opposed with one count of each per `:forced-monotonic` predicate and one of
`[:opposed-between f]` per `:forced-between-predicates` predicate
(`reads/stores-opposed-with-functor?`, `reads/stores-opposed-between?`). A scan of
`[:opposed-bodies]` would grow with the opposed bodies of a forced functor that are not
forced literals, the `genl` edges between types among them; `lein perf`'s
`genl-defeat-beside-defeats-columnar` holds the read flat in 8,192 of those.

`[:opposed-in ctx]` keys the members by context first, beside the trie that ends in the
context, for one read: a moved `genlCx` edge's placement pass reads the members stated in
the contexts the edge exposes (the `:below` of the settle's `genlCx` moves, `special/drain-context-moves!`). Read off the context-last
trie, that is every opposed body's children intersected with the exposed contexts. Measured
at one exposed context stating no member (`:memory`), the context-last read costs 1.40 ms
at 1,000 opposed bodies and 22.18 ms at 16,000, and the context-first read 0.6 µs and
0.2 µs. `lein perf`'s `genl-cx-edge-beside-opposed` holds the edge flat in the opposed
bodies it does not reach, and `negation-opposed-check-denials` holds a settle flat in the denials
with no positive twin.

Which of these paths a given KB's traffic actually takes, and which families it reads at
all, is a question about a workload rather than about the index:
[profile.md](profile.md) is the instrument that answers it, and it names each path above
so a tally can count it.

### The length set

A positive fact of functor `f` holding `n` arguments enters the count trie
`:shape-tuple` under the node `[f n]`, the context last, and `[:shape-lengths f]`, the
trie's root level, holds the argument counts `f`'s positive facts are stored at, so a
length leaves the set with its node's last fact (`kv/shape-adds`, `shape-retires`). The
index write posts both from the sentence in hand. The inert-tuple refresh
(`arity/drain!`) reads a functor's lengths here (`reads/as-stored-shape-lengths`) and a
shape's tuples off its node (`reads/as-stored-shape-tuples-global`), so a shape of one
tuple reads one handle
however many tuples of another length its functor holds; the positional trie cannot
answer it, since a positive fact's path carries no length.

### The arity bindings

A stored fact binding a relation's length (`sx/arity-binding`: `(arity P n)`, an
exact-arity class membership, a `variable_arity` membership or `(arityMin P m)`) enters
the count trie `:arity-binding` under the node `[P kind value]`, the context last. Two
levels sit above the node: `[:arity-binding-kinds P]` lists the `[kind value]` of P's
nodes, and `[:arity-bound]` every predicate holding one. The index write posts all three
from the sentence in hand (`kv/fact-nodes`, `binding-adds`, `binding-retires`): a kind
enters with its node's first handle and leaves with its last, read off the node's count
before the write, and a predicate enters `[:arity-bound]` with its first kind and leaves
with its last. `arity/relation-length` reads a predicate's kinds and its bindings in
every context here (`reads/as-stored-arity-binding-kinds`,
`as-stored-arity-bindings-global`), the arity pairs read the CxUniverse copies
(`as-stored-arity-bindings`), and the lengths stored above a type probe `[:arity-bound]`
once per type they read (`reads/stored-arity-bound?`), so no binding record is read and
recover rebuilds no list of them.

### The calendar index

A fact naming a time the calendar places (`datetime/time-term?`) enters the count trie
`:calendar` under the node `[f frame year month]` of its functor `f` and each point of
that time (`datetime/month-buckets`): an `InstantFn` moment's own, and the start and end
of any other term's extent, in frame `:local` for a time in no zone and `:utc` for one
with an offset or a zone. `[:calendar-buckets f]`, the trie's root level, lists `f`'s
months, so a month leaves it with its node's last fact (`kv/calendar-adds`,
`calendar-retires`). A rule names no node. The index write posts both from the sentence
in hand, so `reindex` and a layout rebuild rebuild them.

The reader is the context-NAT producer's link arm ([context-nat.md](context-nat.md)). It
reads the functors of a context NAT's map and of the facts giving point-order links
(`context-nat/calendar-functors`): each one's months (`reads/as-stored-calendar-buckets`),
and its nodes between two months (`reads/as-stored-calendar-at-global`). A read costs one
name-set read per functor, a scan of those functors' months, and their facts filed in the
months it keeps, whatever the count of facts of other functors (`lein perf`'s
`context-nat-calendar-link-beside-timestamps`).

### The `natFormula` arguments

A positive `(natFormula K (f a1 … an))` map enters the count trie `:nat-argument` under
the node `[f pos a]` of each argument the argument root would key (`kv/arg-slots`): a
symbol or a ground compound, canonical and whole at any size. A number, a string and a
negated map enter no node. The index write posts the nodes from the sentence in hand
(`kv/fact-nodes`), so `reindex` and a layout rebuild rebuild them.

The reader is the context-NAT producer ([context-nat.md](context-nat.md)). It reads the
CxUniverse maps holding a term at a declared position (`reads/as-stored-nat-formulas-at`)
and counts them with one leaf count (`stored-count-nat-formulas-at`). A read costs one
node per position and term, whatever the size of the term's own posting in the term index
(`lein perf`'s `context-nat-read-unwritten-slice-beside-monads`).

## 3. The rule index

Rules are sentexes; they are additionally posted by predicate so chaining finds
candidates without scanning. Each index is a count trie ending in the rule's context,
keyed by each distinct antecedent key or by the consequent's key:

```
[:rule-antecedent :count    [<key>]]       -> n          rules with an antecedent on key
[:rule-antecedent :children [<key>]]       -> #{ctxs}    the contexts stating one
[:rule-antecedent :handles  [<key> <ctx>]] -> #{handles} those stated in ctx
[:rule-consequent …]                       -> the same, by consequent key
[:rule-antecedent-keys]                    -> #{keys}    every key some rule takes
[:rule-extent :count    [<kind>]]          -> n          every rule (:rule), solve rules (:solve), lazy (:lazy)
[:rule-extent :children [<kind>]]          -> #{ctxs}    the contexts stating one
[:rule-extent :handles  [<kind> <ctx>]]    -> #{handles} those stated in ctx
```

`[:rule-antecedent-keys]` is the antecedent trie's root level: a key joins it in the batch
that creates its node and leaves it in the batch that empties the node. It is stored under
its own key because its members are keys rather than contexts. The rule extent is written
by `index-sentex` from the rule's own record, so it answers "which contexts state a rule"
and "the solve rules a reader sees" without an antecedent to start from.

A rule is posted once per key: `rules/index-rule` writes a node only where its leaf does
not already hold the handle, and `rules/unindex-rule!` retires one only where it does, so a rule
registered twice, or one whose antecedents repeat a key, leaves every count right. A
backward read from a context passes the reader's ancestor set (`provers/candidate-rules`),
so it reads no rule the visibility filter after it would drop.

**Both indexes are complete** — every rule is registered under all of its antecedent
keys *and* its consequent key, whatever its direction — so "what could conclude P?" is
answerable whatever a rule's direction, an inert rule the browser reads included.

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

Each fan is the closure intersected with the **rule-key set**, the keys some stored rule
reads, read from the smaller side in one read (`reads/as-stored-rule-keys-meeting`). A
closure no larger than the set's count costs one membership test per term. A larger
one costs one pass over the rule-key set, which the `:dense` and columnar indexes decode into a
set on every read, and `chain/fire-rules-for` asks once per datum. The positive fan walks
the *up* set, which a hierarchy bounds by its depth. The down set on a broad ontology is
most of it, so the spec walk stops at the count (`tax/specs-global-within`), and an
arriving `(not (thing X))` takes the pass instead of one index probe per type in the KB.
A KB with no rule reads the count alone (`trigger-keys-beside-rules` in `lein perf`).

The other readers of the rule-key set read from the smaller side too, each as one read. A
`genl` edge's subsumption seeds test each term of the upper end's upward closure and of
the re-join families for membership (`special/rule-reads-above`), and intersect the
lower end's negated fan as `trigger-keys` does (`special/negative-subsumption-seeds`). A
batch of edges (`special/batch-subsumption-seeds`) makes those reads once for every edge:
the key count, the re-join families and the negated keys (`rules/stored-negated-keys`).
An edge whose spec reach passes the key count, and every edge on a KB declaring a
`genlInverse` edge, intersects its reach with the negated keys from the smaller side. A
datum a `SupportingProver` reads intersects the prover's answers
(`special/rules-taking`). A `genlCx` move reads the key count, and the set only when it
builds the fan (`special/move-seeds`). `lein perf` holds each flat in the key count:
`rule-reads-above-beside-rule-keys`, `negative-seeds-beside-rule-keys`,
`batch-seeds-beside-rule-keys`, `computed-reading-beside-rule-keys` and
`visibility-seeds-beside-rule-keys`. The
stratification graph reads the whole set once per graph for the readers of `not`
(`checks/stratification-readers`), because no family holds the negated keys apart from
the rest.

The exception re-check index (§4) keeps its bare-`not` bucket: it is a coarse
*whether-to-look* set, and both of its sides agree on that spelling.

A rule concluding a **variable** predicate — `(implies (holds ?p ?x ?y) (?p ?x ?y))`,
allowed because range restriction binds `?p` to a concrete antecedent — has no concrete
consequent predicate to key on, so its consequent is filed under one catch-all bucket,
`[:rule-consequent :handles [:var-pred ctx]]` (`protocols/var-consequent-key`). It fires *forward*
through its concrete antecedent like any other rule; for the *backward* read, "what could
conclude P?" is the `P` bucket unioned with that catch-all, since a rule concluding `(?p …)`
could conclude any `P` once `?p` binds. A consequent that is a bare variable,
`(implies (holds ?x ?s) ?s)`, is refused `:not-well-formed`
([naming.md](naming.md#literals-wrappers-and-arguments)); the dotted rest `(implies
(holds ?x (?pred . ?args)) (?pred . ?args))` states it and is filed in this bucket.
`resolution/concluding-rule-handles` does the union,
and `rules/direct-concluders` does the same stored-graph read for the stratification and
blocked-firing paths. A variable functor in an *antecedent* is a different matter and stays
refused ([the split](defenses.md#a-variable-functor-rule-is-refused-not-silently-accepted)).
An `:inert` rule concludes nothing in either engine, so a variable consequent on one keeps
the canonical `?var0` — a dead key nothing reads — rather than the live catch-all.

The dual question is a **goal** with a variable functor — `(?p Tom ?y)` — which names no
consequent bucket and which any rule may conclude, `subsuming-unify` binding `?p` to the
consequent's functor. `concluding-rule-handles` answers it with every rule stated in a
context the reader sees, read off the rule extent (`reads/as-stored-rules-in`) — `O(rules)`,
paid only for a variable functor, the same enumeration `chain/rule-firing-report` takes.
So `(prove kb '(?p Tom ?y))` and `(query kb '(?p Tom ?y) ctx {:max-depth 2})` reach a
rule concluding `ancestorOf` exactly as fact matching reaches a stored `parentOf` through
the argument roots ([inference.md](inference.md), "Backward chaining").

What may actually *fire* is **not indexed**. A rule's `:engines` and `:defeasible`
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
change is what the `:rules` set is for. Both edge triggers read it first to decide whether
to go on, never as the answer, so a KB that writes no `exceptWhen` pays one set read
per edge and stops, and each then narrows from it. `special/recheck-genl-edge` keys on
the predicate — the set sliced by `[:exception-index pe]` for each `pe` in
`genls(super)`, the up-closure being exactly where a spec closure moved — and
`special/recheck-genlCx-edge` keys on the context, walking the set and queueing a rule
only where one of its firings was placed in the ancestor set the edge widened. The set is
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

The predicates are passed to `rules/index-exception` / `rules/unindex-exception!` as a
seq rather than read off the sentex, so the index does not depend on how a rule spells its
exception. `reads/watched-rules-on` and `reads/watched-rules` read the two sets back,
`reads/watched-rule?` probes the watched-rule set, and `reads/watched-rule-count` reads its count.
A write's re-check trigger asks the count, not the members, because a mapped index builds
the members as a set on each read (`release-beside-watched-rules` in `lein perf`).

## 5. The inverted term index

**Every sentex is findable by any term it contains.** On `index-sentex` we post the
handle under every indexable subterm of its **connective-free content**
(`sentex/index-terms` over `content-forms` — a rule's antecedents and consequent,
or a fact's positive body, never the `not` / `implies` / `and`) plus its context. The
head of a compound one of the three heads is skipped at every depth too, as in the rule a
generator's consequent quotes, and the compound's other subterms are keyed;
`sentex/probe-atoms` narrows a compound probe by the same atoms:

```
[:term-index term] -> #{handles containing term}
```

An *indexable* subterm (`sentex/indexable-term?`) is a non-variable symbol
(predicate, individual, type, context) or a fully-ground compound. **Numbers,
strings, and variables are dropped** — a year like `1970` or a comment string is
not a lookup key, since it only bloats the index; predicates, individuals,
and ground compound subterms still key. The `.` of a rest pattern `(?f . ?args)` is
syntax and is dropped too, so `terms` never lists it.

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
set: the same sentexes come back, and `lein perf`'s `compound-probe` is the perf check saying
the cost tracks the rarest atom rather than the hottest one. What the bounds buy is
[density.md](density.md): with the floor at its default the token dictionary is
vocabulary-bound, measured at exactly 1.00× over a 3× corpus.

Note the division of labour with the argument root: this index answers "*anywhere*,
any nesting", which is what a term page or a general search wants. When the position
is known — `types-of` looking for `(T x)`, i.e. `x` at argument 1 — the position-1
argument roots (`reads/as-stored-unary-with-arg-global`, a union of the scoped roots over
the unary predicate set) are the precise, and much smaller, answer.

Term keys are canonicalized (`term-key` runs `sentex/canon`) so a reader-literal
compound query term matches the stored, canon-built subterm.

Cost: a sentex creates one posting per distinct indexable subterm — deliberately,
that's the "findable by any term" guarantee.

## 6. The term-name set

The term index answers *"which sentexes mention this term?"*. The term-name set answers the
question one step earlier — **"which terms are there at all?"** — and it is a separate
key because a `KvBackend` has no key *scan*: get / put / delete / counters / sets /
intersect / batch, and nothing that lists the keys of one family. (`kv-entries` lists
every entry the store holds, for a dump — see below — but that is the whole index,
unordered, so answering "which terms" from it would cost a walk over all of it, and the
on-disk backend has no key ordering to narrow with.) So the vocabulary is maintained the
way the secondary roots are, as one flat set whose cardinality is its own size:

```
[:term-names] -> #{every symbol term the term index is keyed by}
```

- `terms kb` — the vocabulary, sorted by name.
- `term-count kb` — its cardinality, one O(1) read.
- `find-terms kb q opts` — the names matching `q` (`:match` `:prefix` (default) /
  `:substring` / `:regex`, `:case-sensitive?`, `:limit`), filtered over the set.

**Membership is derived from the postings, never counted separately.** `index-sentex`
reads each of its terms' postings *before* writing them and enters the names whose
posting is empty; `unindex-sentex!` reads them before removing and retires the names
whose posting is exactly the handle going away. Both decisions are made from the
pre-write state, so each costs one extra read per name and the index write stays a
single batch — and the set cannot drift from what is indexed, because it is
answering a question about the postings themselves. `reindex` rebuilds it with
everything else, and `clear-index!` wipes it.

Only **symbols** are listed. A ground compound keys the term index too (so
`find-sentexes` takes one), but it is a sentence fragment rather than a name, and a
vocabulary listing that included it would be answering a different question.

Cost: this is what makes term enumeration O(vocabulary) instead of O(sentexes). The
scan it replaces — walk every sentex, take its indexable subterms, collect the symbols
— measures ~8µs per sentex, so listing every term costs ~3 ms on the starter, ~37 ms at
4.4k sentexes, ~500 ms at 60k, and would cost seconds at a million. The term-name set reads one
set and sorts it: ~0.09 ms, ~0.2 ms, ~1.9 ms at those same sizes (roughly 30×, 190× and
260×), because it is priced by the *vocabulary* — 120, 305, 2,545 terms — which grows far
slower than the KB. `term-count` is a set-size read and does not move at all.

The write side pays for it: one posting read per name on `index-sentex`, ~7% of the
index write (2.7µs a sentex), which is why the term set is computed once and handed to
the term-name set rather than rebuilt.

Every family on this page is a tax of that kind, and the tax is **counted rather than
timed**: `test/vaelii/assert_cost_test.clj` asserts the exact number of index reads and
`index-sentex` / `unindex-sentex!` batch ops fourteen fixed workloads cost, so a family that
starts writing one more posting fails the suite rather than the stopwatch. That is the regression test `lein perf`
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
index** is checked at `open-kb` before anything reads it: `disk/files.clj`'s
`index-layout-decision` compares `<dir>/index/layout.edn` against the current version —
an absent sentinel over a populated log counts as stale, since that is what an index
written before the sentinel existed looks like — and a `:stale` verdict clears the index,
rebuilds it from the records, then writes the sentinel. The sentinel lands only *after*
the rebuild, so a crash in between reads as still-stale on the next open rather than as
clean, and the rebuild logs at `:warn` with the record count and how long it took. A
**fork's base** is held to the same sentinel and gets the other answer: a stale base is
refused (`:type :stale-index-layout`) rather than rebuilt, because the repair is a write
and a base is mounted read-only — the message names the one place the rebuild can happen,
which is opening that directory as a KB. The **mapped snapshot** and the **dump format**
answer the same question in their own vocabulary: a snapshot whose layout version does not
match is `{:index :rebuild :reason :layout-changed}` and is rebuilt rather than mapped.
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
| argument-root scope table | distinct `(predicate, position)` pairs, `(predicate, position, context)` triples and one `(context, 0, context)` scope per context |
| token dictionary | the vocabulary, on the same condition |
| `roots-fallback.nippy` | the counters keyed by a predicate, functor, rule key or kind: the predicate-extent, rule-index, self-tuple and shape counts |

The scope table is what lets the count tries ride the mapped run with every other
family. An argument leaf's key carries a predicate, a position and a context beside its
term, and an argument node's children key a predicate and a position, so that scope
interns to a dense id of its own and rides the 24 bits `dense-roots`' packed `long`
reserves for an argument position (`argfam-id`); every other count trie's leaf takes its
context's scope `(context, 0, context)`. A node's run holds context ids, written through
the same remap as the keys. The table decodes the scope ids, is bounded by predicates ×
arities × the contexts each is stated in, plus one entry per context, rather than by
facts, and rides
`roots.csr` — the file whose key column is its only reader, so the two are written in
one pass and discarded as one unit. A node's count in the argument, supporter,
length-binding, opposed and mint tries is no section: `dense-roots` sums its leaves. The
predicate-extent, rule-index, self-tuple and shape counts are in the fallback blob, and
every name set rides the run as token ids.

The blob's entry count and byte length are recorded and checked like a CSR section's all
the same: the predicate extent's count is what the planner prices a scan by, so a blob
that thawed short would price every predicate at 0 rather than fail.

It is a cache of derived state, so validity is the whole design: written with the record
store's slot fingerprint, checked on **every** open, discarded to `reindex` on any doubt.
Selected by name — `{:backend :disk-snapshot}`, the one pairing there is, since the
fingerprint is the disk record store's own slot fingerprint — and refused outright on a
platform that cannot replace a mapped file, since the publish is an atomic rename over one
(`docs/storage.md`).

## 9. The taxonomy's supporter families

The taxonomy's writers (`tax/add-genl`, `tax/add-genlCx` and the flat caches' `add-*` /
`mark-*`, which the `:integrate` / `:disintegrate` arms of `special/entries` call) post
each supporter under the key it installs, before the in-memory write that installs it. A
`genl` fact is posted under `[:genl sub super]`; a `covering`, `separating` or `partition`
declaration under `[:genl part whole]` for each part and under its own `[:cover …]` key,
so the node of an edge lists every declaration that installs it. `[:tax-installs h]` is
the reverse: the keys one handle installs. A post or a retirement writes both in one
`family-apply!` batch: a post skips a handle already under the key, and a retirement
passes `p/any-context`, so the store finds which context's leaf holds the handle and
whether the leaf and the node empty. The equality partition and the
rewrite rules post nothing here (docs/taxonomy.md).

The key a declaration installs is a function of the special-predicate table, and a
member of a disjoint metatype is a supporter only while a mark on the metatype is stored.
So `reindex` posts these families after its per-record pass, by replaying the stored
declarations over a scratch taxonomy (`special/post-taxonomy-supporters!`), and the
importer's inline load does the same once every record is in.

`:tax-named` files each stored positive `except` or `defeat` whose target is a supporter,
under the target's relation (`kv/key-relation`), so `kb/supporter-reaches?`, the check a
scoped read runs first, answers that a supporter rests on an `except` or `defeat` target with one count
read when the target is the supporter itself. Two writes post it, each reading the other
side as stored. The naming fact's index write reads `[:tax-installs H]` of its target
(`kv/flat-family-adds`). The taxonomy's post of a supporter reads the naming facts of the
supporter's handle in the trie, and its retirement retires them once the handle installs
no other key of the relation (`tax/post!`, `tax/retire!`). An `except` outlives a target
retracted before it, and the retirement takes it out of the family then. The family's
other path is the scoped-read check's walk over the targets the stored `except`s and
`defeat`s name
(`index_test/the-named-supporter-family-agrees-with-the-naming-trie`).

## 10. The mint family

A **mint** is a record a stored justification of an argument declaration concludes
(`kb/mint-informant?`), and the mint family files each one whose sentence is a
membership `(T x)` or an edge `(genl x T)`, by `x` and by its context.  The settle's mint
withdrawal reads it ([argtypes.md](argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on)).

```
[:mint :count    [<term>]]          -> n          the mints about term
[:mint :children [<term>]]          -> #{ctxs}    the contexts holding one
[:mint :handles  [<term> <ctx>]]    -> #{handles} those in ctx
[:mint-terms]                       -> #{terms}   every term some mint is about
[:mint-in :count    []]             -> n          every mint
[:mint-in :children []]             -> #{ctxs}    the contexts holding one
[:mint-in :handles  [<ctx>]]        -> #{handles} the mints in ctx
```

**The family indexes justifications, not sentences.**  A minted `(person A)` and an
authored `(person A)` in one context are one sentex, so no key over the sentence tells
them apart.  The family is written from the justification and the sentence in hand: by
`special/entail-arg-type` as it stores a mint justification, and by `reindex` from the
stored justifications, walked before the sentexes so each record is posted from the copy
the sentex walk holds.  A record leaves it when it leaves the store
(`special/retire-mint!`) and when its last mint justification goes while it stays
(`special/retire-unjustified-mints!`), which reads the removed justifications'
consequences and informants off the network's removal report (`:removed-supports`).  A
record respelled in place (a `reifiable_function` mark moving) is filed again under its
new spelling's term and taken out from under the old one, and a fold that copies a
mint justification onto the surviving row files that row (`special/refile-mint!`).  A
records-only import stores no justification, so it replays a dump's index without these
entries (`kv/justification-family-entry?`).

A post or a retirement is one `family-apply!` batch over `:mint` and `:mint-in`. The
`:mint` trie answers by term, and its root level `[:mint-terms]` lists and counts the
terms (`reads/as-stored-mints-about-global`, `reads/as-stored-mint-terms`).  The `:mint-in` trie
holds the same handles keyed by the context alone: its node count answers whether any mint
is stored (`reads/stored-mint-count-global`), and its leaves answer the mints stated in the contexts a `genlCx` edge exposes
(`reads/as-stored-mints-in`).  The context-first leaf departs from context-last keys,
as `[:opposed-in ctx]` does, and the read needs it: through `:mint` alone, the mints in a set of
contexts cost a probe per mint term whatever the set
([defenses.md](defenses.md#the-mints-by-context-read-a-context-first-leaf)).

`[:mint-rules]` holds the `[kind handle]` of each stored rule of `kv/mint-rules`, the
inert rules the mints are justified under.  `index-sentex` posts it from the sentence in
hand (`kv/mint-rule-kind`), and `unindex-sentex!` takes it out, so it rebuilds with the
index at `reindex` and at a layout rebuild.  `kb/mint-rule-table` reads it once
(`reads/as-stored-mint-rules`) and holds the map until a rule of `kv/mint-rules` is
stored or removed or the stores are rewritten (`kb/forget-mint-rules!`).

## What the structural index does not reach

The structural trie above indexes nested subterms of a positive fact. Three things sit
outside it, and a query that needs one of them falls back to the coarser index rather
than failing:

- **The secondary argument roots** (the nodes `[pred pos term]`) and rete's alpha
  buckets are keyed by **top-level position and arity**. A term nested inside an
  argument is not a key in either.
- **A `:false` body and a rule literal** are not structurally indexed, including the
  dotted-rest `(?pred . ?args)` shape. A dotted pattern changes its functor's arity, so
  neither the trie nor the argument roots can key it — it is not a stored-fact shape at
  all, and `res/hierarchical-literal?` excludes it by name, so the set-algebra retrieval
  hands it to `matches-visible`. What `res/candidate-handles` chooses between is seven
  named access paths — `:trie`, `:structural`, `:arg-roots`, `:context-extent`,
  `:functor-extent`, `:negative-roots`, `:negative-fan` — each of which answers a
  **superset** that `unify` then filters exact; there is no eighth for a dotted shape. A
  dotted pattern with a concrete functor, `(p ?c . ?xs)`, reads `:functor-extent`, and
  `unify` binds the rest against each fact of `p` at every length. A dotted pattern under
  a variable functor matches no stored fact, since the trie and the argument roots both
  read its `.` as an argument.
- **The rule indexes are keyed by predicate**, not by full antecedent shape, so two rules
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

  A **generator's** generated rule is the other exemption, and it is the one that buys
  something back: a variable functor there is a *hole*, filled with a concrete predicate
  before anything is keyed on it, so one generator ranges over a family of predicates
  while every rule the index sees has a concrete functor.  The generator may itself be
  generated by one, and then the fill happens a level earlier — but the claim is unchanged
  either way, because it is about what reaches the index rather than about what is
  written: a functor **no enclosing level binds** is refused like any other, and a rule
  nothing encloses has no enclosing level to bind one.  See
  [generators.md](generators.md).
