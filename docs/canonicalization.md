# Sentex canonicalization (`vaelii.impl.sentex`)

- **Covers:** how a sentence's variable names, antecedent order, symmetric arguments, and
  comparison direction fold to one stored handle, and how a conjunctive consequent or a
  disjunctive antecedent unfolds into several.
- **Not here:** which spellings are legal for a predicate, individual, type or context →
  [naming.md](naming.md); how the canonical form becomes the trie key →
  [indexing.md](indexing.md).
- **Assumes:** sentex, rule, antecedent, consequent → [glossary.md](glossary.md).

Beyond the connectives, a sentence is put into a canonical form so logically
identical knowledge is stored once.

## Canonical variables

A rule's variables are renamed `?var0`, `?var1`, … by first occurrence in
canonical order. **`:varmap`** maps them back to what the author wrote
(`{?var0 ?x}`), and `sentex/originalize` restores the original names for display.
Facts carry no varmap.

## Canonical literal order

A rule's antecedents are sorted **structurally** — rank, arity/shape, then value.
Ordering runs *before* numbering with a variable-**blind** comparator, so it can
never depend on the author's variable names. Literals that tie under it (a
same-predicate self-join) are resolved by an **exact prefix minimization** — the
order is built one literal at a time, keeping only the minimal extensions — which
returns the smallest canonically-numbered form without enumerating the tie group's
permutations.

The comparison runs over the **whole rule** — antecedents, then consequent, then
exception — because two orders can render identical antecedents and differ only in
what the consequent says about them. Comparing antecedents alone leaves that decided
by traversal order, and breaks dedup at tie groups as small as **two**. A lexical
comparison of constant symbols is the last resort.

Cost is O(k²) numberings for any tie group whose literals are distinguishable at
all. The hard shape is genuine **automorphism** — k antecedents of one predicate
sharing no variables, a joinless cross product — where every ordering renders the
identical antecedents and only the consequent (then the exception) separates them.
The exact search would keep all k! orderings and pick the minimal consequent at the
end; `prune-by-tail` instead folds the consequent into the search. Such a group is
**joinless** (so every ordering renders the same antecedents) and **tail-isolated**
(its variables touch no other antecedent, so its ordering changes nothing but its own
consequent), which makes the consequent the whole tiebreak — a never-reordered form,
so projecting it is content-, not order-dependent. Projecting it under each survivor's
partial numbering (an unnumbered variable → a sentinel that sorts last) and keeping
only the minimal-so-far survivors each round collapses the automorphic case to O(k²)
too, with no cap. It is exact, not a heuristic: numbering is monotonic across rounds,
so an unnumbered variable can only be given a larger number later — a survivor whose
projected tail is strictly larger can never be the whole-rule minimum. The tie is
broken **per origin** (the incoming survivor a candidate descends from), so it never
decides between orderings that differ on an earlier group's antecedents, which outrank
the tail. The result is identical to the exhaustive search; only the cost changes.

Two kinds of literal are **held back** in the author's order, because their
position is operational rather than logical:

- **Deferred (evaluable)** literals — which consume bindings rather than produce them.
  `sentex/deferred-predicates` names fifteen: `evaluate`, `lessThan`, `greaterThan`,
  `different`, `unknown`, the five quantity comparisons, and the five aggregation
  operators.
- The **recursive** literal of a recursive rule. Reordering it could turn a
  right-recursive rule left-recursive, which the backward chainers cannot execute.

## A NAF conjunction's conjuncts sorted

`(unknown (and A B))` and `(unknown (and B A))` are one rule. The conjuncts are
independent ground existence checks — closure leaves every variable bound before the
query runs — so their written order, and a repeat, are not their identity. Sorted with
the variable-blind comparator, since this runs on the surface literal, where the
author's variable names are still what they wrote. The exceptWhen exception gets the
same treatment one layer up (`sentex/sort-conjuncts`, applied in `vaelii.core` once the
query is aligned to the rule's varmap).

## Symmetric arguments sorted — ground literals only

A *ground* `(siblingOf Bob Ann)` and `(siblingOf Ann Bob)` store as one sentex. A
literal holding a variable is a **pattern** (a query, or an antecedent about to be
matched) and is never reordered: variables sort last, so sorting one would move its
ground argument into slot 1 and miss the stored fact.

Order-insensitive *lookup* is handled at match time instead — `res/raw-match`,
`core/sentexes-matching`, and `kb/find-sentex-handle` probe **both argument orders** for a
symmetric predicate. That also keeps a fact asserted *before* its `(symmetric P)`
declaration reachable, and makes re-asserting its mirror resolve to it rather than
duplicate. Sorting needs the taxonomy, so every store/lookup builds its sentex
through `res/kb-sentex` (which supplies `:symmetric?`).

## Comparison siblings folded

`greaterThan` is stored as `lessThan` with reversed arguments
(`sentex/comparison-siblings`), so only the `<` direction is ever stored; a
`greaterThan` *goal* is still answerable.

## Comparison chains collapsed

`lessThan` is **variable arity**, and chains in a rule merge: `(lessThan ?a ?b)` +
`(lessThan ?b ?c)` ⇒ `(lessThan ?a ?b ?c)`. A branch (`?a<?b`, `?a<?c`) is left
alone.

## Rule wrappers become fields

`(set/forwardRule (implies …))` is not data *about* a rule — it is how the rule's
direction is written, so like `not`/`implies` it canonicalizes **into the record**:
`:direction` (`:forward`/`:backward`/`:inert`/`:both`, `:both` for a bare
`implies`) and `:defeasible` (from `set/defaultRule`). Wrappers may nest — a
defeasible forward rule — and never reach the stored sentence. The `:direction`
opt on `assert` and `assert-rule` is just the programmatic spelling: it wraps, and
the wrapper becomes the field.

Neither slot is in the identity key, so re-asserting with a different wrapper
resolves to the **one** sentex. Where the two spellings disagree, the slot is then
resolved from **content**: the least restrictive direction (`:inert` is the bottom,
`:forward` and `:backward` join to `:both`), and strict over defeasible — a rule
somebody also stated without `set/defaultRule` is one they stated as holding
outright. Both resolutions are commutative and idempotent, which is what the pair
has to be: keying the slot on which assertion arrived first would let the same two
assertions in the two orders reach two sets of beliefs, and order independence is
not negotiable ([nmtms.md](nmtms.md)).

A **third** slot resolves the same way, and for the same reason read one step
further. `:strength` — the class the rule itself is held at, `opts :strength` at the
door — is not in the identity key either, and it takes the **stronger** of the two
assertions. A re-assert carrying no `:strength` states nothing about the class, so
reading that silence as a downgrade would make `defeat-class` answer differently for
the same two assertions in the two orders. No *belief* moves either way, nothing in
the engine defeating a rule ([nmtms.md](nmtms.md)), which is why this one is about
what a caller reads back rather than about what the KB believes. Narrowing any of
the three is `retract!` and re-assert, never a second spelling.

The **fact** door resolves its own `:strength` the same way and by the same argument,
where belief does move: a re-asserted fact keeps the stronger mark, so a bare re-assert
of known-true content cannot retire it ([nmtms.md](nmtms.md)).

## Polycanonicalization: one rule written, several stored

The connectives above canonicalize **into** the record — `not` becomes a truth value,
`implies` and `and` become the antecedent vector and the consequent, a `set/*Rule`
wrapper becomes a field. Two of them cannot, because what they say is not about one
rule: a rule that concludes a **conjunction** makes two claims, and a rule whose
antecedent **disjoins** fires for two reasons. Both are *polycanonicalized* — the one
sentence the author wrote is stored as several rules, and the connective is gone before
anything is canonicalized, keyed or indexed.

**A conjunctive consequent splits per conjunct** (`rules/expand-consequent`):

```clojure
(implies A (and C1 C2))   ⇒   (implies A C1)   and   (implies A C2)
```

Each is keyed by its own consequent predicate, which is what the rule index needs: a
backward goal on `C2` reaches a rule filed under `C2`, and a rule filed under the
compound `and` would be reachable by no goal at all.

**A disjunctive antecedent distributes per alternative** (`rules/expand-antecedent`):

```clojure
(implies (or A B) C)          ⇒   (implies A C)          and   (implies B C)
(implies (and (or A B) D) C)  ⇒   (implies (and A D) C)  and   (implies (and B D) C)
```

The distribution is to **DNF**, so an `or` nested inside an `and` inside an `or` expands
too, and a one-disjunct `(or A)` is just `A`. The reason it is expansion rather than a
record slot is the same reason again, read from the other side: the rule index keys a
rule by its antecedents' predicates and forward chaining triggers it from an arriving
fact, so a stored `or` would have to be a predicate — and it names none. Expanded, each
alternative has concrete antecedent predicates and triggers exactly as a hand-written
rule does.

**The two compose, and the result is the product.** `(implies (or A B) (and C1 C2))` is
four rules, alternatives outermost and conjuncts within — which is the order `assert`
stores them, and therefore the order an `exceptWhen` is re-attached along.

### What the author gets back

`assert` and `assert-rule` return the **vector** of handles whenever the rule expanded
to more than one, and a bare handle when it did not. The vector is the author's record
of the whole rule: retracting one handle retracts that one alternative or that one
conjunct, and retracting the rule means retracting them all. `retract!` refuses the
vector itself (`:bad-handle`), rather than treating `(retract! kb (assert kb rule ctx))`
as a no-op that reads like there was nothing to do ([api.md](api.md)).

Everything downstream sees ordinary rules. Each expansion is canonicalized **on its
own** — its own variable numbering, its own antecedent order — and carries its own
handle, TMS node and justifications. Each **dedups against an individually asserted
twin**: writing `(implies A C)` out after the disjunctive rule finds the stored one and
joins its slots exactly as any re-assert does ([nmtms.md](nmtms.md)). `why` on a
conclusion names the alternative that fired, which is the rule a reader can go and
retract.

`canonical-sentex` is the one reader that stops short of the expansion, and deliberately:
it answers for the sentence **as written**, so a rule that polycanonicalizes has no single
canonical sentex to hand back — the canonical forms are its expansions', one each. Ask it
of each alternative when that is what you want. (This is the same for both causes: a
conjunctive consequent comes back whole too.)

An `exceptWhen` is split off before the expansion runs and re-attached **once per
expansion**, against that expansion's own handle and aligned to its own varmap — the
exception belongs on the rule it excepts, and after the split there are several
([exceptions.md](exceptions.md)). A generator's stamped rule keeps its `or` until the
mint substitutes the holes, and `chain/mint-rule` expands what it is about to store, so
the alternatives a generator stamps are the alternatives of the rule it stamped
([generators.md](generators.md)).

### Two things about the whole rule

**Range restriction is asked per alternative**, and this is the check the expansion
cannot inherit from the flat one. `(implies (or (dog ?p) (cat ?q)) (fed ?p))` has `?p`
somewhere in its antecedents, so a read of the disjunction whole passes — and then one
of the two rules it expands to concludes about a variable nothing binds. So each
alternative is checked on its own, and the **whole** rule is refused
(`:not-range-restricted`) naming the disjunct the bad alternative took. Half a rule is
not what anybody wrote, which is the same reason every conjunct is checked before any is
stored.

**The width is capped at 16 alternatives** (`rules/max-alternatives`), refused
`:disjunction-too-wide` with the count. The cost of a disjunction is paid in handles,
index entries and TMS nodes rather than at query time, and nested disjuncts multiply, so
a rule that reads like one line can cost thousands. The count is arithmetic — a product
over the antecedents — so a rule far over the line is refused without ever being
materialized. Past the cap the alternatives are better named as a **type**: a `genl`
edge per member and one rule on the supertype, which is one handle however many members
it covers.

### Where `or` cannot go

The connective earns its place by disappearing, so the positions it cannot disappear
from are refused at the shape door — before the KB is read at all, by `assert`,
`assert-inert` and `check` alike:

| position | refused | because, and instead |
|---|---|---|
| a rule **conclusion**, or a standalone sentence | `:not-well-formed` | belief is a label on a sentex, not on a set of them, so a disjunctive head is a *choice* rather than a derivation — offer the alternatives to a solve with `set/assumptionRule` ([solving.md](solving.md)) |
| an `unknown` / `thereExists` / aggregate body | `:not-well-formed` | each is answered as one closed level-6 query and nothing there unions two runs ([naf.md](naf.md), [aggregate.md](aggregate.md)) — `(unknown (or A B))` is "neither A nor B", so write two `unknown` antecedents; a `thereExists` or an aggregate takes one rule per alternative |
| an `exceptWhen` query | `:not-well-formed` | the conjuncts of one exception all have to hold — but a rule's exceptions block if **any** holds, so a disjunctive exception is two exceptions, one `exceptWhen` per alternative against the same handle ([exceptions.md](exceptions.md)) |
| under `not` | `:not-well-formed` | `(not (or A B))` is "neither A nor B", a conjunction of negations, so expanding on it would store the opposite claim — write the two negations as separate antecedents |
| an empty `(or)` | `:not-well-formed` | it expands to no rules at all |
| a **goal** | `:shape` | a rule is expanded once at the write door; a goal would have to be expanded at every read, and a read normalizes to *one* conjunction that the planner orders once and every engine walks as one ([api.md](api.md)). Run the query once per alternative and concatenate, or put the disjunction in a rule — which *is* expanded — and ask for its conclusion |

An `or` in an **argument** slot is not a connective frame at all and is left where it
stands, exactly as a compound argument is everywhere else: `(likes Tom (or A B))` is one
literal whose second argument happens to be a list.

## What the shape checks cost

The constructor asks a sentence several questions of the form *does any form in here look
like X* — and for almost every sentence the answer is no. Seven such readings share two
walks, `sentex/some-form` and `forms-where`, which short-circuit on the first hit, and
`check-naf-closed` counts variable occurrences only once something consumes bindings.
Against a `tree-seq` that builds a seq of every form before answering, that is 8–26× on
the individual readings, 13× on a plain one-antecedent rule assert and 25× on a six —
same answers, same depth-first pre-order.

## Result

So rules identical up to **variable names, antecedent order, symmetric argument
order, and comparison direction** all dedup to one handle — with one carve-out the
hold-back above states: a *deferred* literal and the *recursive* literal keep the
author's relative order, since their position is operational, so two spellings that
differ only in where those sit are two handles by design.

And the folding has an unfolding beside it: a rule whose consequent conjoins or whose
antecedent disjoins is stored as **several** handles, one per conjunct times one per
alternative, each of them canonicalized on its own and each of them deduping against a
twin somebody writes out by hand.

## See also

- [docs/indexing.md](indexing.md) — how the canonical form reaches the trie key.
- [docs/storage.md](storage.md) — the `LiteralSentex` / `RuleSentex` record shapes.
