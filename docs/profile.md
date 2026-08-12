# What shape of question this KB is asked

- **Covers:** the workload instrument — the five tallies (`:goals`, `:reads`, `:fan`,
  `:writes`, `:retracts`), the shape key each goal is counted under, the named access
  paths a shape can take, and what the instrument costs on and off.
- **Not here:** what the index *is*, and why the trie is ordered the way it is →
  [indexing.md](indexing.md); what a posting costs in bytes → [density.md](density.md);
  readings about the *knowledge* rather than the traffic → [quality.md](quality.md);
  how a chaining run went → [inference.md](inference.md).
- **Assumes:** sentex, handle, trie path, secondary root, term index →
  [glossary.md](glossary.md), [indexing.md](indexing.md).

`vaelii.impl.profile`, read out by `lein bench-profile`
(`bench/vaelii/bench/profile.clj`). The index has six families and several access paths
into them, and every family is a write tax on every assert. Which of them earns its keep
is a question about a **workload**, not about the code: a KB whose patterns all lead with
a ground first argument pays for three secondary root families nothing reads, and a KB
asking `(?type Muffet)` a thousand times a second lives on the argument-slot roster. This
is the instrument that answers it from outside.

## Five tallies

| tally | one entry per | the question it answers |
|---|---|---|
| `:goals` | retrieval decision, keyed by shape and access path | what distribution the index is asked to serve |
| `:reads` | `IndexStore` read, keyed by family | which families are read at all |
| `:fan` | trie walk, keyed by the path's first token | what a walk cost in node probes |
| `:writes` | `index-sentex`, keyed by functor | what an assert costs each family |
| `:retracts` | `unindex-sentex!`, keyed by functor | what a retraction costs each family |

`:reads` is the one that answers "does this family earn its keep", and it answers it with
a zero when it does not. The trie counts as **two** families there — `:trie-lookup` for a
retrieval walk and `:trie-counts` for `count-at` / `children` / `count-children` — because
those are the query planner's selectivity probes rather than a fetch, and a run can be
dominated by either. `:fan` is what turns a fan-out from an anecdote into a number: a walk
that narrows visits one node per level, and a walk stuck behind a variable visits that
level's whole child set.

`:retracts` is a tally of its own rather than `:writes` with a sign on it, and `:dead` is
why. Every other quantity in either is decided by the sentex — its arity, its terms, its
indexable arguments — so it reads the same whenever the operation happens. How many trie
nodes a removal *kills* is decided by what else is still stored under the same prefix, so
one fact retracted out of a dense corpus and out of a sparse one costs differently. A
family's assert cost can be quoted as a constant; its retraction cost cannot, and merging
the two would make the constant unreadable.

## The shape key

A goal is counted under `[functor truth binding-pattern path]`. The binding pattern is
one character per argument, in position order, and the alphabet is what the **index**
distinguishes rather than what a reader would:

| | |
|---|---|
| `b` | a ground atom the roots key — an individual, a type, a context |
| `B` | a ground compound, which the argument roots key whole |
| `n` | a ground token that is no key at all — a number, a string |
| `f` | an open atom (a variable) |
| `F` | an open compound, one holding a variable |

So `(parentOf ?x Tom)` counts as `[parentOf :true "fb" :arg-roots]`, and
`(mass ?o (QuantityFn ?n Kilogram))` as `[mass :true "fF" :structural]`. `functor` is
`:open` when the functor is itself a variable, the shape that puts every argument behind
it. Arity is the pattern's length, so the key carries that too.

`n` is its own class and not a kind of `b` because the distinction is the whole reason
`(pred ?x 1970)` keeps the trie while `(pred ?x Tom)` does not: a number is ground and is
still no root key, so there is nothing to divert to.

Three readings the harness derives from the pattern, and the first two are **not** the
same question:

- **A bound argument after an open one** — a `b` or `B` with an `f` or `F` to its left.
  This is the shape with no selective trie prefix, and it is the whole argument for the
  secondary argument roots, which answer it.
- **An open compound after an open one** — an `F` with an `f` or `F` to its left. This
  one is answered by nothing. The trie narrows left to right, so the compound's tokens sit
  behind a fan, and `[:argument-root pred pos term]` keys a *ground* argument whole, so a
  compound holding a variable is not one of its keys either.
- **An open compound at any position** — an `F` anywhere, the same reading with the
  position rule dropped. It exists because a zero on the row above has two causes that
  call for opposite conclusions: the compound never arrives at all, or it arrives
  constantly and always with a ground prefix in front of it, which is what lets the trie
  descend into it. Only this row tells those apart, and the harness follows it by naming
  where the open compounds were asked.

An `F` is open, so it is never the bound half of the first reading and the first two never
double-count. Adding them would report a number meaning neither, since one names a shape
a family serves and the other names a shape nothing does. The third is a superset of the
second by construction and is read as a bound, not added to anything.

## The access paths, named

Two matchers decide where candidates come from, and each names its decision so the tally
can count it. `res/candidate-handles` yields one of seven:

| path | taken when |
|---|---|
| `:trie` | a left prefix, a fully-ground test, or after-a-variable selectivity that is only a `n` token |
| `:arg-roots` | a ground argument sits after an open one — the scoped argument roots, intersected |
| `:structural` | a positive pattern with a compound argument, narrowed on the compound's interior |
| `:functor-extent` | the same shape with `res/*structural-index*` false — the correct looser superset |
| `:negative-roots` | an open negative with a functor or a ground argument pinned |
| `:negative-fan` | an open negative with nothing pinned — the `:false` node's own children |
| `:dotted-extent` | a variable-arity dotted-rest pattern — one concrete functor extent, or the matching-polarity functor roster when open |

`res/matches-hierarchical`, the set-algebra matcher behind the context-scoped levels,
makes its own choice and never consults `candidate-handles`:

| path | taken when |
|---|---|
| `:hier-scoped-roots` | something indexable to lead with, and a spec closure to scope by |
| `:hier-agnostic-roots` | something indexable to lead with and no predicate — a variable functor |
| `:hier-functor-extent` | nothing indexable to lead with, so the sub-predicates' extents |

A tally over these is **retrievals, not questions**: a matcher that fans over a
predicate's spec closure records one entry per sub-predicate, so a total is index traffic
rather than a count of what a caller asked.

## What it costs

The switch and the store are one atom, nil when off, so every seam is a deref and a
`nil?` check — what the observer seam costs the reference chainer
([inference.md](inference.md)). The trie walk carries two long operations per level
whether or not anybody is counting, so `lookup` can report how wide its frontier got.

On, it is one `swap!` per event over a persistent map. That is not free and is not meant
to be: every quantity here is a count, so a run under the instrument answers the same as
a run without it, more slowly.

## What it does not see

- **`:fan` is the one tally that is not index-independent.** It is `KvIndexStore`'s,
  covering every backend the `KvBackend` adapters reach — the flat map, the dense one, the
  on-disk WAL, an overlay. The columnar index walks its own native trie and counts no node
  probes, so a columnar run reports **no fan at all** rather than a fabricated one, and
  `profile_test` asserts that silence rather than standing aside. The other four hold on
  both stores: the columnar index keeps them itself, since it writes and walks the index
  rather than going through `KvIndexStore` to do it.
- A retrieval that reaches the index without going through either matcher has no shape:
  the direct `p/lookup` callers — `find-sentex-handle`, the level-0 raw read, and every
  term read the interactive arm makes — appear in `:fan` and `:reads` and not in
  `:goals`.
- The binding pattern is one character per **top-level** argument, so it cannot say where
  inside a compound a variable sits. `(mass Obj (QuantityFn ?n Kilogram))` reads `bF`, and
  that `Kilogram` sits behind `?n` within the subterm is not a distinction the key
  carries.

## Running it

```
lein bench-profile                            the shipped starter
lein bench-profile generated [facts] [rules]  a Zipf-skewed corpus of known shape
lein bench-profile corpus <dir> [profile]     a converted corpus (:cyc-corpus)
```

A corpus run wants a heap, and the `:bench` profile pins `-Xmx6g`. An environment
`JVM_OPTS` is placed *before* the project's own options and loses to it silently, so the
vector is edited on the way past instead — `with-profile` first, `update-in` second,
which is the order `scripts/run-bench-caches.sh` documents:

```
lein with-profile +bench,+with-foreign update-in :jvm-opts conj '"-Xmx32g"' -- \
  run -m vaelii.bench.profile corpus <dir>
```

Six readings come out, and they answer different questions:

- **The corpus shape** is static and needs no workload: arity, where the nesting sits,
  and how the token dictionary scales against the vocabulary. The nesting row is split by
  *where* the compound sits, because the structural trie linearizes a positive fact's
  arguments and nothing else — a compound inside a `:false` body or a rule literal is
  invisible to it ([indexing.md](indexing.md), "What the structural index does not
  reach").
- **The load and chain arms** are the engine's own traffic. Every antecedent a rule
  matches on is a goal somebody really asked.
- **The ask arm** proves each rule's own consequent two deep. A rule's consequent is the
  question the rule exists to answer, so the set is a workload the KB declared for
  itself.
- **The interactive arm** makes the reads an *application* makes — `terms`,
  `term-count`, `find-terms`, `find-sentexes` — and it is the only arm that does. No
  reasoning calls any of them, so without it the term roster and the term index read zero
  on every corpus, which reads as a family nobody uses and means a family no **reasoner**
  uses. Its read table is the inverse of every other arm's: on the shipped starter it is
  88% `:term-index` and 12% `:term-roster`, and every other family at nothing.
- **The churn arm** retracts a sample of premises and puts each one back, which is the
  only way `unindex-sentex!` runs at all. It is net-neutral by construction and says so
  when it is not: a fact retracted that will not go back is counted and reported, because
  it means the arms already run were over a different KB. Premises only — a derived
  conclusion has no antecedent either, and re-asserting one as a premise is refused by the
  checks the rule was allowed to conclude past.

  Two samples, and the split is the arm's whole reading. A `genl` or `genlCx`
  sentence *is* a taxonomy edge, so churning one moves the cached closures
  ([taxonomy.md](taxonomy.md)) rather than the trie under it — on the OpenCyc conversion
  `genl` is the largest predicate of the 7,550 and the two are a fifth of everything
  stored, and a taxonomy pair costs several times an index-path one at the median. So the
  tallies are the **index sample's**, and the taxonomy edges run after under their own
  budget, reported beside it: the comparison between the two is a reading, where one
  number covering both is an index tax nobody paid.

  Each sample is reported as a **distribution** — median, p95 and max, with the costliest
  pairs named — and never as a mean. What one pair costs is the size of the region its
  removal moves, and that ranges over orders of magnitude inside a single hierarchy: an
  edge between two leaf types moves almost nothing, while the edge holding the root type
  under `thing` disconnects every type from the root, so `isa?` changes for every
  individual and the affected region really is the graph. Both are ordinary edges. A mean
  over a sample holding one of each is that edge divided by the sample size, wearing the
  shape of a typical cost — and a reading off this arm gets cited in design work, so it
  has to be a number somebody can act on. Where a sample is too small for a percentile the
  line says so rather than dressing the largest reading up as one, and the per-pair
  timings are kept so the report can name the sentence at the top of each sample: the
  column that answers *which pair was that* without re-running.

  Bounded three ways, and **per pair** is the one that matters. A budget checked on the
  way round a loop is read once a pair is already over, so a single retraction that does
  not come back is unbounded whatever the arm's deadline says. Each pair therefore runs on
  a worker of its own and is abandoned when it passes its budget (10 s on a corpus, 2 s
  otherwise); the arm then stops on *both* samples, because the abandoned worker is still
  inside the KB and a second writer beside it is a race rather than a measurement. The
  other two bounds are the sample's own clock — 90 s the index sample, 30 s the taxonomy
  one, split rather than shared so the second is never starved by the first — and 90% of
  the maximum heap, which a clock cannot stand in for: a corpus churned against taxonomy
  edges retires a cached closure per pair and rebuilds it on the next read, and a run that
  dies of that dies without a stack trace. The heap is read twice with a collection
  between, so the bound fires on the live set rather than on the collector's backlog.

  Whichever fires prints a `SENTINEL churn arm STOPPED` line naming the pair and how many
  facts were dropped, since a bound that truncates quietly reads afterwards as an arm that
  covered everything. And the arm narrates rather than reporting only on the way out: the
  two sample sizes are printed before the first pair and progress every eighth of a sample,
  flushed — an arm that prints its header and then nothing leaves no record of what it was
  doing when it went.
- **The balanced probe** asks every binding pattern equally often, which no workload
  does, and is labelled synthetic for that reason. Its question is not which shapes
  arrive but what each shape costs when it does. Frequency comes from the arms above;
  cost comes from here.

## The gate built on it

`test/vaelii/assert_cost_test.clj` is the instrument's second consumer, and it *decides*
where `lein bench-profile` reports. It runs ten fixed workloads and pins the **exact**
index-operation counts each costs, every read by family and every `index-sentex` or
`unindex-sentex!` batch op by family. Six of them assert — a plain binary fact, a type
membership, a fact of a declaration-carrying predicate, a negative, a compound, and one
arriving through a forward rule — and four retract: the plain facts, the premises of the
forward rule, and two on a KB holding reified NATs, one whose retractions name none of
them and one whose retractions each orphan one.

It exists because `lein perf` cannot see this class of defect and says so in its own
preamble: **a ratio cannot see a constant.** An unconditional read added to the assert
path moves the reading at both sizes equally and divides out, so every ratio check passes
untouched. The two gates are complements, and neither subsumes the other: `perf.clj` holds
the *shape* of a cost, this holds the *constant*.

The quantity is an integer the engine computes rather than a measurement of the machine,
so there is no warm-up, no tail mean, no noise floor and no tolerance. It is identical
across runs, machines and a loaded box, which is what lets it live in the suite instead
of behind a command somebody has to remember. Its configuration is pinned rather than
inherited — `:backend :memory` because the seams are `KvIndexStore`'s and the columnar
store has none, and the four retrieval switches at their shipped defaults — so it says
the same thing on all eight backend runs of `scripts/test-backends.sh` and all five sweeps
of `scripts/test-sweeps.sh`.

Budgets are **exact**, not ceilings. A ceiling lets a change spend whatever is already
budgeted, and these numbers are not a design target: they are a record of what the engine
does today. So an optimization fails this gate too, which is the intended behaviour — the
commit that re-pins the number carries the improvement as data.

**The worked case is a regression that really shipped.** `inter-args-problem` once ran its
`interArgIsa` declaration retrieval unconditionally, on every assert of every KB, though
nothing declares `interArgIsa`; it cost ~11% per assert and was found by hand against a
worktree at the parent commit ([argtypes.md](argtypes.md)). Restoring it:

| | with the regression |
|---|---|
| `lein perf`, every ratio check | **all pass** |
| assert-cost read budgets | **6 of 6 fail**, `:argument-root` +1 per sentex |
| assert-cost write budgets | 6 of 6 pass |

The third row is the one that sets the gate's scope. A counter over the *write* side alone
would have reported nothing, because the regression was a read; counting per family is
what makes it visible at all, since one extra read is 4.8% of the plain workload's total
and 33% of the family it lands on.

What the gate does not catch is in its own namespace docstring: work that is not an index
operation, a more expensive version of the same operation, a non-`KvIndexStore` index, and
anything that scales. `:dead` is the one budgeted number that is not a per-operation
constant — it is exact for a fixed corpus torn down in a fixed order, which is what a
workload is, and it is not a figure another corpus reproduces.

## The bake-off built on it

`bench/vaelii/bench/index.clj` is the instrument's third consumer. `lein bench-profile`
*reports*, `assert_cost_test` *decides*, and this one **compares**: one corpus, one
workload, several index layouts, and what each costs.

```
lein bench-index [corpus] [workload] [args …]

  corpus    starter | generated [facts] [rules] | corpus <dir> [profile]
  workload  shapes (default) | heads | local | all
```

The corpus arms and the probe construction are `vaelii.bench.profile`'s own, taken by
var rather than copied, so a bake-off reading and a profile reading are over the same
corpus and can be checked against each other.

### The layouts, in two tiers

A **physical** layout is a different index: it builds its own KB, so build time and
resident bytes are its own. A flat-map `KvIndexStore` is the reference; beside it the
dense int-postings backend, the columnar native trie, and the flat map with
`sentex/*min-indexed-depth*` bound to 0, which mints every literal's own whole-compound
term key.

An **access** layout reads the *reference's* index with one retrieval switch withdrawn —
`res/*arg-root-retrieval*`, `res/*structural-index*`, `res/*hierarchical-retrieval*` — so
it has no build time and no bytes of its own, and quoting either would be quoting the
reference's. Sharing the KB is what makes it the sharper experiment: the stored index is
held identical and only the path varies.

### The access-path report comes first, and that is the design

A layout that quietly falls back to a coarser access path answers identically and is
merely slower. Read as a duration that is a fair loss; read as a path it is a
misconfiguration. So the `:goals` tally is printed as a path histogram per layout,
before any duration, and a layout whose histogram differs from the reference's is named.

It is also the one table that spans every layout, because `:goals` is the one tally taken
above the index. The `:reads` table beside it prints **not applicable** rather than `0`
for a layout with no `KvIndexStore` seams, since a zero and an absence are different
readings: a columnar arm scored on `:reads` would look like an index nobody touches.

Answers are gated mechanically alongside it. Every layout answers the identical probe
set, and each probe's answer is fingerprinted as `[count (hash handle-set)]` — content
rather than order, since two layouts may return one set in two orders. A layout whose
fingerprint differs is reported as wrong and its timings are void.

### The quantities, and where the other two live

Retrieval time per goal shape, as a ratio against the reference; build time; jol retained
index bytes and bytes per sentex; index reads by family; and the q-error curve per join
depth, which `vaelii.bench.plan` computes and this harness calls rather than repeats. The
q-error reading that matters is whether it is **flat in the depth** — flat means the
estimates compose — rather than whether it is small, because the trie is the cost model's
substrate and a layout that retrieves faster and estimates worse can be a net loss no
retrieval microbenchmark shows.

Two quantities are absent because they are elsewhere. Write cost per assert, per family
is `assert_cost_test`, above. Allocations per lookup are `vaelii.bench.alloc`, which
drives the same layout table.

### What it cannot see

In the harness's own namespace docstring, at more length. A read-only workload cannot see
a layout that moves cost to the write path; every probe is asked at `?ctx`, so nothing
walks the `genlCx` up-closure; the term index and the term roster are read by
`terms` / `find-terms` / `find-sentexes` and by no reasoning at all, so a layout that
moves them shows up as bytes and as nothing else; the q-error arm's corpus is 1:1, where a
correct estimator scores exactly 1.00, so it fails a layout rather than ranking one; and a
corpus too small for two layouts to differ reports that they do not, which is a reading of
the corpus.

The largest of them is worth stating on its own. Unification, belief filtering, the
taxonomy closures, the record fetch and the frontier a walk rebuilds at every level are
inside every timing, and every one is **common to both arms of every ratio**. A ratio
divides a shared cost out, so a row that reads 1.05x can be a layout twice as expensive at
the part it owns. That is `perf.clj`'s "a baseline large enough to already carry the cost
being measured" arriving as a denominator instead of as a small size. Read a retrieval
ratio as a floor on the layout's contribution; the counts, the paths and the retained
bytes are the quantities the sharing does not dilute.

Wall-clock is the untrusted half throughout, as it is in [density.md](density.md). The
counts, the paths and the retained bytes are the structural half.
