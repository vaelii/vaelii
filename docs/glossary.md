# Glossary

- **Covers:** the definition of every term the docs and code use, one entry per term,
  tagged by subsystem.
- **Not here:** the per-subsystem map of which doc covers what → [README.md](README.md); the
  naming rules a spelling is checked against → [naming.md](naming.md).
- **Assumes:** nothing — this is where the vocabulary the other pages assume is defined.
  The shape those terms fit together into is [README.md](README.md)'s one-paragraph model.

Terms used across the vaelii docs and code. When a term has both an English and
a KB-symbol meaning, both are covered.

Each entry is tagged with its subsystem:
![kb](../.github/badges/cat-kb.svg) knowledge representation & ontology ·
![inference](../.github/badges/cat-inference.svg) query & rules ·
![tms](../.github/badges/cat-tms.svg) truth maintenance ·
![asp](../.github/badges/cat-asp.svg) ASP & contradiction solving ·
![qr](../.github/badges/cat-qr.svg) qualitative reasoning ·
![backend](../.github/badges/cat-backend.svg) storage & indexes.

## A

**`abducible_predicate`** ![kb](../.github/badges/cat-kb.svg): The grant that
makes a `(P …)` assumable by `abduce`, and the only thing that does — a
belief-following taxonomy prop like `transitive`, but read from the asking
context's `genlCx` ancestor set rather than universally, because abducibility is a
policy of
the context granting it. See [abduction.md](abduction.md).

**Abduction** ![inference](../.github/badges/cat-inference.svg): `abduce` —
what would have to be true for a goal to be provable. Runs the DFS backward
chainer, observes the subgoals it could neither match nor expand
(`res/*dead-end*`), and mints the gated ones as `:default` premises in a
scratch context hung below the asking context, so an ignored call leaves the
KB as it found it and every answer names its assumptions. See
[abduction.md](abduction.md).

**Aggregation** ![inference](../.github/badges/cat-inference.svg): The five
query operators `agg/count` / `agg/sum` / `agg/min` / `agg/max` / `agg/avg` —
namespaced like `set/*Rule`, the bare words being ordinary vocabulary.
`(agg/count ?n ?v Body)` binds `?n` to a
reduction over the distinct `?v` satisfying `Body`, evaluated at level 6. `?v`
is projected out, one answer or none, nothing stored. A conjunctive `Body` is **joined**,
its conjuncts sharing `?v` — so *how many of Bob's children are
asleep* is one witness satisfying both. In a rule antecedent the
aggregate runs once per binding the generators supply, which is where GROUP BY
comes from. See [aggregate.md](aggregate.md).

**Allen's interval algebra** ![qr](../.github/badges/cat-qr.svg): The calculus
of 13 base relations between two stretches of time — `before`, `meets`,
`overlaps`, `starts`, `during`, `finishes`, `equal` and the six converses.
`vaelii.impl.interval`, registered as `:allen`. See [time.md](time.md).

**`and`** ![kb](../.github/badges/cat-kb.svg): The conjunction connective.
`(and S1 S2 …)` holds when every conjunct holds; in an antecedent it is
canonicalized into the rule's antecedent vector rather than stored as data,
and in a *consequent* it is polycanonicalized into one rule per conjunct. See
[canonicalization.md](canonicalization.md).

**Antecedent** ![kb](../.github/badges/cat-kb.svg): The premise side of a rule
sentex, stored as a vector of literals. Empty for a fact. Canonically ordered
and variable-renamed so rules identical up to antecedent order dedup to one
handle. A written `or` never reaches the vector: the rule is polycanonicalized
into one per alternative first. See [inference.md](inference.md).

**Anytime inference** ![inference](../.github/badges/cat-inference.svg):
Resource-bounded query (`ask-within` / `prove-within` / `resume`): realize a
lazy answer stream under a budget (`:max-ms` / `:max-results` / `:max-cost` /
`:max-depth` / `:max-term-growth`) and report whether it ran to `:complete` or was cut
short. The
unrealized tail is the resumable continuation. See [anytime.md](anytime.md).

**`arg`** ![kb](../.github/badges/cat-kb.svg): An argument-type declaration.
`(arg pred n type)` requires the *n*-th argument of every `pred` fact to have
a type whose genl closure reaches `type`. Open-world and context-scoped. See
[taxonomy.md](taxonomy.md). `interArg` is the **conditional** form —
`(interArg pred n T m U)` requires argument *m* to be a `U` only when argument *n* is
a `T` — and it reads open-world in *both* directions at once: an unestablished trigger
leaves it dormant, an unreachable target convicts. See [argtypes.md](argtypes.md).

**Arity vocabulary** ![kb](../.github/badges/cat-kb.svg): `fixed_arity` and
`variable_arity` classify relation-wide argument policy, each with predicate and
function specializations. `arity` states one exact predicate arity; `arityMin` states a
variable relation's lower bound, and exact arity entails the same minimum.
`at_least_binary_relation` / `at_least_ternary_relation` are derived minimum classes.
`admitsArgnum` names whether one positive position exists; no WFF/query reader currently
consumes it. See [taxonomy.md](taxonomy.md#relations-and-arity-policy).

**Arm** ![kb](../.github/badges/cat-kb.svg): The function a table stores under a functor
and a walk over that table invokes at one fixed point — `special/arms` holds an
`:integrate`, a `:disintegrate`, a `:rebuild` and a `:wff` per interpreted predicate, and
`special/entries` is the ordered join all four walks read. The word is the `case` arm's:
the table *is* a dispatch on the functor, and an entry supplies the branch taken for it.
So a check written by hand and reached from no table is not one, however much semantics it
carries. See [predicates.md](predicates.md).

**`ask`** ![inference](../.github/badges/cat-inference.svg): The pluggable
prover-engine query. It runs the cheapest complete prover alone, else unions the
applicable provers cheapest-first by cost tier. See [inference.md](inference.md).

**ASP** ![asp](../.github/badges/cat-asp.svg): Answer-set programming — the
backend the edge solver renders a contested `Program` into, solved with clingo
(in-process JNA) or clasp (subprocess). Opt-in, with a deterministic stub
fallback. See [asp.md](asp.md).

**ASPIF** ![asp](../.github/badges/cat-asp.svg): The intermediate text format a
`Program` is emitted to before a clingo/clasp solve. Contested assumptions
become choice atoms and nogoods become weak constraints. See [asp.md](asp.md).

**Asserted** ![tms](../.github/badges/cat-tms.svg): A sentex with at least one *active*
direct premise support — held IN by having been written down rather than by resting
on a justification. A sentex may be both asserted and **Derived**; `kb-diff`'s
`:premise?` is what tells the two apart. See [nmtms.md](nmtms.md).

**Atomic (storage)** ![backend](../.github/badges/cat-backend.svg): All-or-nothing, the systems sense —
an atomic rename publishing a new file over the live one, a crash-atomic write, and
`edit!` as the all-or-nothing write. A declared collision with the term sense below,
three strata away and never on the same page. See [storage.md](storage.md), [api.md](api.md).

**Atomic (term)** ![kb](../.github/badges/cat-kb.svg): Not a function application — a symbol, a number, a string, or
a reified constant. What a **NAT** is *non*-atomic with respect to. See [nat.md](nat.md).

**Atomic formula** ![kb](../.github/badges/cat-kb.svg): A predicate applied to terms — `(dog Muffet)`, `(P ?x)`. The
base of the formula ladder, and open or closed alike, since the definition says nothing
about variables. A CxCore collection too, `atomic_formula`. See [naming.md](naming.md).

**Atomic sentence** ![kb](../.github/badges/cat-kb.svg): A closed **Atomic formula** — one with no free variables.
What a stored `LiteralSentex` holds in its `:sentence` slot, since `checks/check-ground`
refuses an open one. A CxCore collection too, `atomic_sentence`. See
[canonicalization.md](canonicalization.md).

## B

**Backward chaining** ![inference](../.github/badges/cat-inference.svg): Proving
a goal by expanding rules whose consequent unifies with it. Two chainers: `prove` (a
`recur` DFS over a goal stack with a per-path `seen` guard, terminating on the data, and
`prove-seq` to drive it a solution at a time) and the node engine (a frontier of whole
conjunctions, terminating on a depth bound). Both are type- and context-aware. Nothing in
the prover registry backchains. See [inference.md](inference.md).

**Bare rule** ![tms](../.github/badges/cat-tms.svg): A plain `implies` rule. It
confers `:monotonic` justification strength — adding no defeasibility of its own —
capped by its weakest antecedent. Contrast a default rule. See
[nmtms.md](nmtms.md).

**Base relation** ![qr](../.github/badges/cat-qr.svg): One of a calculus's
atomic relations. They are jointly exhaustive and pairwise disjoint, so exactly
one holds of any two terms and a *set* of them is the constraint on a pair —
the whole universe meaning "unknown", `#{}` meaning "impossible". See
[qcn.md](qcn.md).

**Belief** ![tms](../.github/badges/cat-tms.svg): Whether a datum is IN or OUT.
A node is IN if it is a premise or has a valid justification, unless it is
defeated (forced OUT). Belief is computed from current state, never accumulated,
so the same knowledge in any order yields the same beliefs. See
[nmtms.md](nmtms.md). Stated over the other two: believed ⟺ (**Asserted**
or **Derived**) and not defeated.

**Belief (an agent's)** ![kb](../.github/badges/cat-kb.svg): A different question
with the same word — `(believes Alice P)` proves `P` in Alice's own context and says
nothing about whether the KB holds it. See [belief.md](belief.md).

**`bijection`** ![kb](../.github/badges/cat-kb.svg): `(bijection P)` — the strongest of
the three **function marks**: `P` is single-valued, one-to-one, total on its declared
domain and onto its declared range. CxCore rules derive `(injection P)` and
`(surjection P)`, and those derive the four marks the engine reads. See
[taxonomy.md](taxonomy.md).

**Brave / cautious** ![asp](../.github/badges/cat-asp.svg): The two readings of
a tie the solver leaves open. A conclusion is *cautious* when it holds in every
optimal answer set and *brave* when it holds in at least one; the committed
labeling holds every cautious one, and a merely brave one is believed exactly when
the answer set that was picked holds it. See
[labeling.md](labeling.md).

**Budget** ![inference](../.github/badges/cat-inference.svg): The consumer-side
bound on a lazy answer stream that makes inference anytime — carrying `:max-ms`,
`:max-results`, `:max-cost`, `:max-depth` and `:max-term-growth`. See
[anytime.md](anytime.md).

## C

**Calculus** ![qr](../.github/badges/cat-qr.svg): A relation algebra plus the
predicates that denote its base relations — `{:name :algebra :denotation}`, what
`qcn-kb` needs to read facts into a network and read entailments back out. Six
ship; `core/calculi` is them as data. See [qcn.md](qcn.md).

**Candidate** ![kb](../.github/badges/cat-kb.svg): A `[sentence context opts]` entry
read **out of English** — the shape `edit!` takes, carrying the span of text it came
from in its provenance, checked by `check-edit` and never asserted. Nothing in the
engine can say a candidate means what the text said, which is why a reviewer sits
between the pipeline and the store. See [reading.md](reading.md).

**Canonical form** ![kb](../.github/badges/cat-kb.svg): The normalized shape a
sentence is stored in so logically identical knowledge stores once — canonical
variables, canonical literal order, symmetric-argument sorting, and comparison
folding. See [canonicalization.md](canonicalization.md).

**`closed_extent_predicate`** ![kb](../.github/badges/cat-kb.svg): The grant that
a predicate's **believed** extent is complete, so nothing answering `(P a)` at
level 6 is what answers `(not (P a))`. Read from the asking context's `genlCx`
ancestor set, so it is a policy of the theory that closes the extent; a closed
`(not (P …))` rule antecedent under it is negation as failure. See
[naf.md](naf.md).

**`comment`** ![kb](../.github/badges/cat-kb.svg): A documentation sentex —
`(comment <term> "…")` — that lets the CxCore vocabulary document itself in
its own representation, read back by `core-context/comment-of`. See
[inference.md](inference.md).

**Composition table** ![qr](../.github/badges/cat-qr.svg): `r1 ∘ r2` → the base
relations still possible between *x* and *z* given `r1`(x,y) and `r2`(y,z). The
one thing a calculus cannot derive from anything else. Three are transcribed and
three computed. See [qcn.md](qcn.md).

**Congruence** ![kb](../.github/badges/cat-kb.svg): Equality's substitutivity:
when two names merge, every occurrence of the retired name at any nesting depth
is rewritten under the representative. Free here because the term index finds the
occurrence and migration rewrites it. See [equality.md](equality.md).

**Consequent** ![kb](../.github/badges/cat-kb.svg): The conclusion side of a rule
sentex. A rule concluding a conjunction is polycanonicalized into one rule per
conjunct; a disjunctive conclusion is refused, being a choice rather than a
derivation. See [inference.md](inference.md).

**Constraint (rule slot)** ![asp](../.github/badges/cat-asp.svg): A rule's
`:hard` / `:soft` slot — `set/hardConstraint` and `set/softConstraint`, whose head is a
contradiction marker and whose body is a conjunctive nogood. ASP's integrity and weak
constraints. Neither the qualitative sense (**Constraint network**) nor an
argument-type **Declaration**. See [solving.md](solving.md).

**Constraint network** ![qr](../.github/badges/cat-qr.svg): `{[a b] → #{base
relations}}` over a set of nodes — a value, not a store, read out of the
believed facts visible from a context. `core/qualitative-network` is the public
reading of one. See [qcn.md](qcn.md).

**Context** ![kb](../.github/badges/cat-kb.svg): The theory a sentex holds
in — every sentex is in exactly one. Contexts form a `genlCx` hierarchy: a
sub-context *sees* its supers. Names start with `Cx`, then CapitalCamelCase. See
[contexts.md](contexts.md).

**Contradiction** ![tms](../.github/badges/cat-tms.svg): A believed `P` and
`(not P)` visible from a common context. A defeasible tie is a *represented
dilemma* — both sides stay believed at `:default` and the pair is reported by
`contradictions`, not arbitrated. See [nmtms.md](nmtms.md).

**CxCore** ![kb](../.github/badges/cat-kb.svg): The vocabulary head — the
most general context, seen by every other. Loaded by `core-context/load-into`:
every special predicate the engine interprets, each documented by a `comment`
sentex. See [contexts.md](contexts.md).

**CxUniverse** ![kb](../.github/badges/cat-kb.svg): The mid anchor of the
context spindle, free for lifted universal facts and the target of
`decontextualized_predicate` justifications. See [contexts.md](contexts.md).

**CxWell** ![kb](../.github/badges/cat-kb.svg): The bottom anchor of the
context spindle, transitively seeing the whole ontology; the test-world's
individuals and fables hang below it. See [contexts.md](contexts.md).

## D

**Declaration** ![kb](../.github/badges/cat-kb.svg): A sentex the engine interprets as a statement about the
*vocabulary* rather than about the world — `(arg parentOf 1 person)`, `(symmetric
marriedTo)`, `(genl dog mammal)`. Stored, believed and retracted like any fact, and acted on
besides. What each term of the engine's own grammar says about itself is written once in
`vaelii.impl.predicates`; what is done about it lives in the layers above. See
[predicates.md](predicates.md).

**`decontextualized_predicate`** ![kb](../.github/badges/cat-kb.svg): Metadata
deducing every `(P …)` — asserted or rule-concluded — into CxUniverse, so the
fact is visible from every context instead of belonging to one. The target is
fixed, not named: the definitional checks are context-scoped and only cover the copy
when the stating context sees where it lands. `forced_decontextualized_predicate` is the
stronger variant that *stores* it there by force. See [contexts.md](contexts.md).

**Default rule** ![tms](../.github/badges/cat-tms.svg): A rule wrapped in
`set/defaultRule`, marking it defeasible. It fires from the same agenda as any
rule but confers `:default` justification strength. See [nmtms.md](nmtms.md).

**Defeasible** ![tms](../.github/badges/cat-tms.svg): Able to be withdrawn when
stronger or contradicting knowledge arrives. Default conclusions are defeasible
at the edges; monotonic content is not. See [nmtms.md](nmtms.md).

**Defeat-class** ![tms](../.github/badges/cat-tms.svg): The strength tier an IN
node sits at — exactly two, `:monotonic` > `:default`. A nogood is resolved by
defeating its strictly weakest member. See [nmtms.md](nmtms.md).

**Deferred literal** ![inference](../.github/badges/cat-inference.svg): A literal
whose position is operational, not logical, so canonicalization holds it in the
author's order: the fifteen `sentex/deferred-predicates` (`evaluate`, `lessThan`,
`greaterThan`, `different`, `unknown`, the five quantity comparisons and the five
aggregation operators) and a recursive rule's recursive literal. See
[canonicalization.md](canonicalization.md).

**`defnNecessary` / `defnSufficient` / `defnIff`** ![kb](../.github/badges/cat-kb.svg):
Tie a collection's membership to a defining condition on the member `?x`, expanded into
ordinary forward rules at assert. `defnNecessary` is member ⇒ condition, `defnSufficient`
condition ⇒ member, `defnIff` both. The companion rule is derived — justified by the
`defn*` fact alone — so retraction and belief follow it. A condition built from computed
predicates, which no stored fact can fire the rule on, is instead evaluated at query time
by `DefnSufficientProver`. Open-world: condition *absence* concludes nothing, though a
necessary that is positively violated proves `(not (Coll a))` at query time. See
[defns.md](defns.md).

**Denotational term** ![kb](../.github/badges/cat-kb.svg): The logic sense of *term* —
an expression that denotes an entity: a symbol, a number, a string, a variable, or a
NAT. Spelled in full wherever the logic sense is meant, because plain **Term** is the
vocabulary sense. A CxCore collection too, `denotational_term`. See [nat.md](nat.md).

**Derived** ![tms](../.github/badges/cat-tms.svg): A sentex with at least one *valid* justification support — held IN by
resting on something rather than by having been written down. The complement
of **Asserted**, and a sentex may be both. See [nmtms.md](nmtms.md).

**`describe`** ![kb](../.github/badges/cat-kb.svg): Everything the KB holds about
one term, in one map, keyed by the term's own `term-role` — arity, the argument
declarations, the relation properties, the closures, the counts and the comment for a
predicate; the disjointness and the admitting predicates for a type; the types and
mention counts for an individual; the two `genlCx` closures for a context. Read from
the asking context's ancestor set, since a declaration and a grant are policies of the
context
that states them, and every list is a window carrying its own `:total` / `:exact?` /
`:sorted?`. The browser's term page renders it. See [api.md](api.md).

**`different`** ![kb](../.github/badges/cat-kb.svg): Provable exactly when no two
arguments share an equivalence class — negation as failure over the equality
closure, keeping the unique-name assumption. Variable-arity, ground-only, and
not assertible. See [equality.md](equality.md).

**Direction** ![kb](../.github/badges/cat-kb.svg): Whether a rule chains
`:forward`, `:backward`, `:inert`, or `:both`. The first three are written with a
`set/*Rule` wrapper — `set/forwardRule` / `set/backwardRule` / `set/inertRule` — that
canonicalizes into the record's `:direction` field; a bare `implies` needs none and
reads `:both`. The chainers read the field. See [inference.md](inference.md).

**`disjoint` / `disjoint_metatype`** ![kb](../.github/badges/cat-kb.svg): Declare
types share no instance, closed under genl. A metatype's members are pairwise
disjoint by being consulted, not by storing the clique. Belief-following. See
[taxonomy.md](taxonomy.md).

## E

**Edge solver** ![asp](../.github/badges/cat-asp.svg): The pluggable `Solver`
that arbitrates only the contested *edges* of a soft contradiction; known-true
content is the fixed background and is never sent. Deterministic stub by default,
ASP backend opt-in. See [solving.md](solving.md).

**Entry point** ![kb](../.github/badges/cat-kb.svg): A public function knowledge
reaches the engine through: `assert` / `assert-rule` / `edit!`, the `check` family that
predicts them without storing, the CLI, and the daemon's op dispatch. Every entry point
runs the same checks, because a sentence one refuses and another stores leaves the KB in
a state no caller asked for, and `check` disagreeing with `assert` makes the prediction
worse than no prediction. See [api.md](api.md), [operations.md](operations.md).

**`equals`** ![kb](../.github/badges/cat-kb.svg): An equality relation feeding
the one equivalence closure, `sameAs` without OWL's individuals restriction. A
`functional` clash derives an `equals`. See [equality.md](equality.md).

**Equational rewriting** ![kb](../.github/badges/cat-kb.svg): An `(equals L R)`
carrying **variables**, oriented into a rewrite `L → R` by a reduction order so
normalization terminates. Stored and queried terms meet at one normal form, so
two spellings of a term reach the same answers without storing both. See
[equational.md](equational.md).

**Equivalence closure** ![kb](../.github/badges/cat-kb.svg): The cached partition
(member → class, class → members and representative) that `rewriteOf`, `sameAs`,
and `equals` all feed. Belief-following, content-keyed representative. See
[equality.md](equality.md).

**Evaluatable predicate** ![inference](../.github/badges/cat-inference.svg): A plain
Clojure fn wrapped as a computed prover by `add-evaluatable` — a *check* (every
argument ground, a truthy return is the predicate holding) or a *result-binding*
function (`:result` names an output slot the value binds), the generic form of the
built-in `lessThan` / `evaluate`. The fn is a value, never `eval` of KB data;
completeness 100 by default and guarded by `sole-prover`. Answers a direct `ask` /
`query` goal and, the node engine's leaf being the registry, joins and discharges a rule
antecedent under a `:max-depth`. See [inference.md](inference.md).

**`evaluate`** ![inference](../.github/badges/cat-inference.svg): Symbolic
evaluation — `(evaluate ?sum (+ 1 2))` binds `?sum` to 3 via a safe whitelist,
not `eval`. A deferred literal. See [inference.md](inference.md).

**`exceptWhen`** ![inference](../.github/badges/cat-inference.svg): A wrapper
letting a rule state its own exception. For a binding the closed level-6 query
holds of, the rule *blocks* — it does not conclude, so there is nothing to
arbitrate. Undercutting defeat. See [exceptions.md](exceptions.md).

**Extent** ![backend](../.github/badges/cat-backend.svg): The set of sentexes at
a secondary root — a context, a functor, or an argument position — each set's
cardinality being its own stored count. See [indexing.md](indexing.md).

## F

**Facet** ![kb](../.github/badges/cat-kb.svg): One of the ten lanes a grammar term takes part in —
`:cached`, `:derived`, `:migrates`, `:arbitrable`, `:reach`, `:query-only`, `:answers`,
`:retriggers`, `:convicts`, `:inert`. A closed vocabulary, so a facet cannot come to mean
whatever its first user assumed, and the term's class is read off it rather than off prose
written beside it. See [predicates.md](predicates.md).

**Feed (change feed)** ![tms](../.github/badges/cat-tms.svg): `watch` — a listener
called with the belief a settle added and took away, in `preview`'s entry shapes,
instead of an application re-asking. One settle is one event, so a batch is one
call; a **standing query** is a filter over the moved region and never a re-run of
its goal. Silent under `preview`, `recover` and `reindex`, and refuses a goal the
region cannot answer. See [feed.md](feed.md).

**Fluent** ![kb](../.github/badges/cat-kb.svg): A state of affairs that holds
over some stretches of time and not others — a cat asleep, a tortoise ahead. A fluent
is a **term** rather than a sentence: a reified NAT like `(AsleepFn Whiskers)`, one
constant per subject, so `holdsAt` stays an ordinary binary predicate over two terms.
An event `initiates` one and `terminates` another. See [time.md](time.md).

**`forall`** ![inference](../.github/badges/cat-inference.svg): The universal, and
sugar rather than a mechanism: `(forall ?y (implies Body Head))` is ¬∃?y (Body ∧ ¬Head),
which in a closed world canonicalizes into the nested NAF
`(unknown (thereExists ?y (and Body (unknown Head))))`. The binder is local to it;
the vacuous case (no `?y` satisfies `Body`) reads true. See [naf.md](naf.md).

**Fork** ![backend](../.github/badges/cat-backend.svg): `core/fork` — a private,
writable KB over another's stores. Reads resolve fork-first and fall through to
the base, writes land only in the fork, and the base is never written, so
several forks share one base and evolve independently. Implemented by the store
decorator in [overlay.md](overlay.md).


**Formula** ![kb](../.github/badges/cat-kb.svg): Recursively — an **Atomic
formula**; a logical operator applied to formulas; or a quantifier binding variables in
a formula. *Open* when it has free variables, *closed* when it does not, and a closed
formula is a **Sentence**. A CxCore collection too, `formula`. See [naming.md](naming.md).

**Forward chaining** ![inference](../.github/badges/cat-inference.svg): The
semi-naive fixpoint over one agenda for bare and defeasible rules alike. A new
fact fires rules keyed by its predicate and supertypes; a new rule joins over
existing facts. Each full match records a justification. See
[inference.md](inference.md).

**Frame** ![backend](../.github/badges/cat-backend.svg): The durable serialization unit — one
record as a positional vector behind a numeric tag, thawed past the LRU. The connective
forms a sentence is built out of are **Wrapper**s, not frames. See [storage.md](storage.md).

**`functional`** ![kb](../.github/badges/cat-kb.svg): `(functional P)` plus two
*symbol* values for one first argument derives `(equals V1 V2)`, justified by
both facts and the declaration. Two non-symbols stay a hard rejection. See
[equality.md](equality.md).

**`functionalInArg`** ![kb](../.github/badges/cat-kb.svg): `(functionalInArg P n)` —
`functional` generalized off its fixed argument 2: every argument of `P` except `n`,
taken together, fixes the filler at `n`. Same merge/refuse rule and same four arrival
directions; what it adds is a **composite determinant**, as in
`(functionalInArg namesObject 3)` for "one namespace and one path name one object".
`(functionalInArg P 2)` on a binary predicate is `(functional P)`. See
[taxonomy.md](taxonomy.md) and [equality.md](equality.md).

**Functor root** ![backend](../.github/badges/cat-backend.svg): The secondary
index root `[:functor-root pred]` — every fact by functor, any arity, either polarity —
read via `sentexes-with-functor` / `count-with-functor`. See
[indexing.md](indexing.md).

## G

**`genl` / `genlCx`** ![kb](../.github/badges/cat-kb.svg): The two
transitively-closed relations — `genl` between unary types and between
predicates, `genlCx` between contexts. Cached as reflexive-transitive up/down closures, recomputed on
edge change, belief-following. See [taxonomy.md](taxonomy.md).

**Ground** ![inference](../.github/badges/cat-inference.svg): Containing no variables. A stored non-rule sentence
must be ground (`checks/check-ground`); a rule's variables are implicitly universal,
which makes it closed without being ground. See [inference.md](inference.md).

## H

**Handle** ![backend](../.github/badges/cat-backend.svg): The integer id a stored
sentex or justification is referenced by, allocated in assertion order. Belief
tie-breaks never key on it, or arrival order would leak in. See
[storage.md](storage.md).

**`holdsAt`** ![kb](../.github/badges/cat-kb.svg): `(holdsAt F T)` — is fluent
`F` the case at instant `T`? Never stated and never stored: it is what inertia
derives from the events a narrative gives, and it is backward-only, since a fluent
holds at every moment between its start and its end. See [time.md](time.md).

## I

**`indeterminate_term`** ![kb](../.github/badges/cat-kb.svg): The extensible
category of terms that stand for some object without pinning down which. A skolem
constant is its built-in first member, read off the `SkolemFn` expression it was minted
from; a further kind joins with `(genl NewKind indeterminate_term)`. A member is not a
determinate filler for a `predAllSpecified` audit, and the unique-name assumption is
suspended for it until a merge pins it. Membership is what the KB holds, not what a
prover infers on demand. See [predall.md](predall.md).

**Index (count-aware trie)** ![backend](../.github/badges/cat-backend.svg): The
trie a sentex is indexed by: its key tokens then context as the final
level, connective-free and α-renamed. Each node carries a count, a child-token
set, and the handles at that node. See [indexing.md](indexing.md).

**Inert** ![kb](../.github/badges/cat-kb.svg): One concept — inferential inertness — with two
applications, differing in whether the KB *believes* what it stores.

- An **inert rule** — `set/inertRule`, or `{:direction :inert}` — is believed,
  indexed and browsable, and chains in neither direction. It is a rule kept as
  **documentation**: the shipped one is CxCore's global lifting rule, written down
  where a reader looks for it while the code is what actually runs it
  ([taxonomy.md](taxonomy.md)).  `genl`'s transitivity is not written this way — its
  cached closure is described in the `comment` on the predicate. Its own `:strength` is an ordinary class —
  there is no `:inert` strength, the two assertable classes being `:default`
  and `:monotonic`.
- An **inert sentex** — `core/assert-inert` — is stored, indexed and durable but
  **never a premise**, so it is never believed by anything: the primitive behind a
  solve's materialized labeling, a recorded truth value rather than a claim
  ([solving.md](solving.md)). It takes atoms and their negations; a **rule** is
  refused (`:not-indexable`): the entry point that indexes a rule is the one that
  creates it.

See [inference.md](inference.md) for the first and [solving.md](solving.md) for
the second.

**Inertia** ![inference](../.github/badges/cat-inference.svg): A state persists
until something ends it. The content of the shipped event calculus (`CxChange`): a
fluent an event `initiates` at one instant still `holdsAt` a later one exactly while
`(unknown (clipped …))` — nothing terminated it in between. Undercutting rather than
defeat, so a terminating event heard of later leaves no conclusion to arbitrate.
See [time.md](time.md).

**`injection`** ![kb](../.github/badges/cat-kb.svg): `(injection P)` — a **function
mark**: `P` is single-valued, one-to-one, and total on its declared domain, with nothing
said about reaching every member of its range. Derives `(functional P)` and
`(functionalInArg P 1)`, both enforced at the write, and `(predAllSpecified P D)` off
the `arg` declarations, audited on demand. See [taxonomy.md](taxonomy.md).

**`ist`** ![kb](../.github/badges/cat-kb.svg): "Is true in" — `(ist Ctx S)`
finds-or-creates `S` in `Ctx` and returns its handle. Not stored as data; in a
rule consequent it places `S` into the named context. See
[contexts.md](contexts.md).

## J

**JTMS** ![tms](../.github/badges/cat-tms.svg): The non-monotonic
justification-based truth maintenance system, governed by order independence and
locality — every relabel scoped to the affected region, tie-breaks keyed on
content. See [nmtms.md](nmtms.md).

**Justification** ![tms](../.github/badges/cat-tms.svg): The stored link from
antecedent handles + informant to a conclusion, carrying the strength it confers
and the bindings of the firing that produced it. A conclusion is IN if it has a
valid justification and is not defeated. The **record store** holds it; the JTMS
holds only the part belief is computed from (`jtms/graph-just`, which drops the
bindings). See [nmtms.md](nmtms.md).

## K

**`kb-diff`** ![kb](../.github/badges/cat-kb.svg): What two KBs disagree about, as
content: `{:added :removed :moved :belief-changed}`, keyed on the canonical sentence,
its context and its strength and never on a handle — so a KB reloaded from its own
text export diffs empty. `:moved` is one sentence in a different context and
`:belief-changed` one stored in both and believed in one, which is what a defeated
default reads as. Premises and derived sentexes alike, told apart by `:premise?`;
justifications, provenance and handles are not compared. See [api.md](api.md).

**Kind** ![kb](../.github/badges/cat-kb.svg): The EDN kind of a **Value** — `string`, `number` with
`integer` below it, `symbol`, `keyword`, `boolean`, `character`. Decidable from the value
itself, which is why the kinds sit in the `genl` lattice and why `quotedArg` is checked
and never entailed. See [argtypes.md](argtypes.md).

## L

**Labeling** ![asp](../.github/badges/cat-asp.svg): Materializing one optimal
answer set as belief — every datum in the settled tie assigned `:true`,
`:supportable` or `:false`, checked against the brave/cautious classification of the
same tie. See [labeling.md](labeling.md).

**Lane** ![kb](../.github/badges/cat-kb.svg): A consumer of a declaration that is wired
per spelling and **fails silently** when a spelling is left out of it — the unit a Facet
names and a Mark family has to agree about. `facet-contract`'s `:lane?` says which facets
are ones: `:retriggers` is not, because a re-check posting is one line inside one Arm
rather than a wiring of its own, and `:query-only` and `:inert` are not, because a
classification of the whole term is nothing a family can differ about. The scale is a
subsystem's whole reading of the declaration — the merge lane, the clash-exposure lane —
and a family joined to one in one spelling and not another is #52 and #54. See
[predicates.md](predicates.md).

**`lessThan` / `greaterThan`** ![inference](../.github/badges/cat-inference.svg):
Evaluable arithmetic comparators, variable-arity — a ground chain
`(lessThan 1 2 3)` is checked end to end. `greaterThan` is stored as reversed
`lessThan`. See [inference.md](inference.md).

**Levels** ![inference](../.github/badges/cat-inference.svg): The lookup-to-query
stack — eight levels (`lookup`), each adding exactly one mechanism to the one
below, from raw index handles to full backchaining. `escalate` finds the
cheapest level that answers. See [levels.md](levels.md).

**Literal** ![kb](../.github/badges/cat-kb.svg): An **Atomic formula** or its
negation. What a `LiteralSentex` holds — the `:sentence` slot carrying the atomic
formula and the polarity slot saying which of the two literals it is. A rule's
antecedent is a vector of literals. Also a CxCore collection, `literal`, in the
expression-kind lattice beside `formula` and `relation_application` — documentary, since
nothing in the engine classifies a compound by its shape. The `LiteralSentex` record is
the machine-stratum representation of a member of it. See
[canonicalization.md](canonicalization.md).

**LiteralSentex** ![kb](../.github/badges/cat-kb.svg): The sentex record for a
literal — a fact or its negation, a metadata declaration, or a query pattern —
holding only `[sentence context id polarity strength]`. Split from `RuleSentex` so a
fact does not carry the rule-only slots. A *literal* is a signed predicate
application (an atomic sentence or its negation); the record admits either polarity
via its `polarity` slot, so the name is `Literal`, not `Atomic`. See
[canonicalization.md](canonicalization.md).

**Locality** ![tms](../.github/badges/cat-tms.svg): The JTMS invariant that no
operation recomputes the whole graph — every relabel is scoped to the affected
region with the rest held fixed as a boundary. A least fixpoint over the region
equals the global one. See [nmtms.md](nmtms.md).

## M

**Mark family** ![kb](../.github/badges/cat-kb.svg): Spellings of one declaration that must move
together because more than one lane acts on them — `functional` and `functionalInArg`,
or the four argument constraints. Named once on each spelling so a third reaches every
lane at once; a family is not a storage roster, its spellings caching differently. See
[predicates.md](predicates.md).

**Metatype** ![kb](../.github/badges/cat-kb.svg): A type of types — its members
are types themselves, reified under the `predicate` meta-ontology. A
`disjoint_metatype`'s members are pairwise disjoint. See [taxonomy.md](taxonomy.md).

**Metric time** ![qr](../.github/badges/cat-qr.svg): Numeric bounds on
durations and distances between instants, closed by all-pairs shortest paths
rather than by a composition table — a simple temporal problem, deliberately not
a relation algebra. `vaelii.impl.stp`, registered as `:metric-time`. See
[stp.md](stp.md).

**Migration** ![kb](../.github/badges/cat-kb.svg): The equality-merge step that
gives every sentex containing a retired term a rewritten twin under the
representative, derived and justified by the original plus the equality, and
re-canonicalized rather than textually substituted. See [equality.md](equality.md).

## N

**Naming invariants** ![kb](../.github/badges/cat-kb.svg): The role conventions —
predicates camelCase, individuals CapitalCamelCase, types snake_case (unary
predicates), contexts `Cx`-prefixed CapitalCamelCase. `assert` rejects a bad name. See
[naming.md](naming.md).

**NAT** ![kb](../.github/badges/cat-kb.svg): A non-atomic term `(F a…)` — a
function application denoting an entity. Two readings, by declaration. Under
`(reifiable_function F)` it denotes an object and is **reified** into an opaque
`nat/`-namespaced constant before it reaches the index. Under
`(unreifiable_function F)` it stays **structural**, a compound to be evaluated. Named
as a CxCore collection by `non_atomic_term`, below `relation_application` and
`denotational_term`. See [nat.md](nat.md).

**Negation as failure (NAF)** ![inference](../.github/badges/cat-inference.svg):
Closed-world negation. `(unknown S)` holds iff `S` is not derivable;
`(thereExists ?x S)` existentially closes and projects. Ground/closed only,
never stored, and a negative stratification edge in a rule body. See
[naf.md](naf.md).

**Nogood** ![tms](../.github/badges/cat-tms.svg): A set of believed sentexes that
cannot all hold — a believed `(not X)` alongside a believed `X` wherever some context
sees both, a definitional clash, or the three claims an `anti_transitive` chain forbids.
Resolved softly by `settle` on defeat-class, the weakest member defeated where one is
weakest, never thrown. See [nmtms.md](nmtms.md).

**`not`** ![kb](../.github/badges/cat-kb.svg): First-class negation. A `(not S)`
becomes `S` stored at `:polarity :negative`, double negation eliminated; a negative
literal keeps its `not` in the index as polarity. See
[canonicalization.md](canonicalization.md).

## O

**`or`** ![kb](../.github/badges/cat-kb.svg): The disjunction connective, legal in a
rule **antecedent** and nowhere else. It never reaches a stored sentence: the
rule is polycanonicalized into one rule per alternative, distributed to DNF and
capped at 16. A disjunctive *conclusion* is a choice rather than a derivation and
is written with `set/assumptionRule` ([solving.md](solving.md)); a disjunctive
*goal* is refused, a read normalizing to one conjunction. See
[canonicalization.md](canonicalization.md).

**Order independence** ![tms](../.github/badges/cat-tms.svg): The JTMS invariant
that the same knowledge asserted in any order yields the same beliefs — belief
is computed from state, and every tie-break keys on content, never on handle id.
See [nmtms.md](nmtms.md).

## P

**Path consistency** ![qr](../.github/badges/cat-qr.svg): The fixpoint that
tightens a constraint network: for every triple, intersect the constraint on a
pair with the composition of the two constraints reaching it through the third,
until nothing narrows. A *greatest* fixpoint, so it removes rather than adds,
and it is order-independent. See [qcn.md](qcn.md).

**Pattern** ![inference](../.github/badges/cat-inference.svg): A **Formula** with `?x`
variables, are read as a *pattern to match* rather than as a claim. Never stored as a non-rule
sentence — `checks/check-ground` refuses that — so a pattern reaches the engine only as a
goal or inside a rule. See [inference.md](inference.md).

**Placement context** ![inference](../.github/badges/cat-inference.svg): Where a
forward-derived sentex lands — the maximal contexts that see the firing rule and
all its antecedent facts (`maximal-common-descendant-contexts`). Possibly
several, possibly none. See [contexts.md](contexts.md).

**Plan (conjunctive query planning)** ![inference](../.github/badges/cat-inference.svg):
Ordering a conjunction's literals cheapest-first, each estimated under the
variables bound by the time it runs (sideways information passing), with the
cartesian factors (those sharing no variable with the rest, and matching more than
once, so they multiply it) held to the back on structure rather than on an
estimate. The cost model is the count-aware trie
itself. See [inference.md](inference.md).

**Polarity** ![kb](../.github/badges/cat-kb.svg): Which of the two literals an
atomic formula makes — positive, or negative under a `not`. Carried by the sentex's
polarity slot and kept in the index. **Not** belief, which is IN/OUT and a separate
question. See [canonicalization.md](canonicalization.md).

**Polycanonicalization** ![kb](../.github/badges/cat-kb.svg): Storing one written
rule as several, so a connective that is not about one rule never reaches a
record. Two causes: a conjunctive consequent splits per conjunct
(`(implies A (and C1 C2))`), and a disjunctive antecedent distributes per
alternative (`(implies (or A B) C)`); together they store the product. `assert`
returns the vector of handles whenever a rule expanded. See
[canonicalization.md](canonicalization.md).

**`positiveExample` / `negativeExample` / `borderlineExample`** ![kb](../.github/badges/cat-kb.svg):
CxCore's example vocabulary. `(positiveExample <term> (sentexHandle H))` names a stored
sentex as an example of a term's usage — a true one, a false one, or one deliberately on
the edge — reusing the `sentexHandle` plus `target_following_predicate` pointing shape, so
retracting the example sentex tears the annotation down with it. The engine reads none of
them; the obligation the first two carry — that the target holds, or holds as its negation
— is held by `curation_test`. See [predicates.md](predicates.md).

**`predAll` family** ![kb](../.github/badges/cat-kb.svg): The eight relations that
quantify one argument position of a binary predicate and fix the other, in three
classes. The *Instance* pair (`predAllInstance` / `predInstanceAll`) is a rule generator
and produces inference. The *Exists* four are inert records beside a sanctioned
placeholder functor. The *Specified* pair (`predAllSpecified` / `predSpecifiedAll`) is an
on-demand integrity audit reporting the instances with no determinate filler — binary,
the filler's required type derived from the predicate's own slot contract rather than
restated, and a predicate with no visible slot typing reported as an explicit
declaration-contract gap. See [predall.md](predall.md).

**Premise** ![tms](../.github/badges/cat-tms.svg): An asserted datum held IN
unconditionally (subject to defeat/supersession), as opposed to a derived
conclusion resting on a justification. Carries an assumption strength. See
[nmtms.md](nmtms.md).

**Provenance** ![backend](../.github/badges/cat-backend.svg): The per-handle open
map kept beside a record — `:creator` / `:created` and any application fields —
so the record shapes stay fixed. Belief never reads it. See
[storage.md](storage.md).

**Prover** ![inference](../.github/badges/cat-inference.svg): A registered
answering strategy declaring `applicable?`, `est-bindings`, a `cost` tier,
`completeness`, and `solve`. Transitivity, disjointness, the predicate metadata and the
evaluables are all provers; `add-prover` extends the set. **None of them expands a
rule** — which is what lets a closed-world reader run the registry from inside a relabel
loop, and what makes `ask`'s cost a property of the goal rather than of the rule graph.
See [inference.md](inference.md).

## Q

**Query** ![inference](../.github/badges/cat-inference.svg): `query` / `query?` — the
public entry point for answering a goal, returning binding maps. One dial: `:max-depth`
says how
far to expand rules, and without one the read answers from what the registry reaches and
expands nothing. There is no default depth, since a bound decides which derivations
exist. Takes a goal — a formula, open or closed — or a **vector** of them (joining on shared
variables) at any depth. The believed-literal *match* is `sentexes-matching`, which is a
different question and returns sentexes. See [api.md](api.md),
[inference.md](inference.md).

**Query context** ![kb](../.github/badges/cat-kb.svg): One of `CxEverything`,
`CxInference` and `CxNothing` — a `Cx…` symbol naming a **way of reading** rather than a
place. Resolved at the read entry point and never reaching the engine; refused at
`assert` and in
the `genlCx` slots, so nothing is stored in one and nothing wires one into the lattice.
`CxEverything` reads the store as spelled, belief ignored; `CxInference` keeps only what
one reader's `genlCx` ancestor set sees over the whole derivation and reports that
reader as
`:context`;
`CxNothing` sees no fact at all, leaving the provers. A **variable** context (`?ctx`, the
default of every short arity, or any name) is the same reading as `CxInference`, the witness
being unified into that variable rather than arriving as `:context`. See
[contexts.md](contexts.md), [from-cyc.md](from-cyc.md).

**`quotedArg`** ![kb](../.github/badges/cat-kb.svg): An argument-type declaration on the
argument **as a term** — its EDN kind (`string`, `number` with `integer` below it,
`symbol`) checked against a syntactic type, the mention twin of `arg`. `(quotedArg
name_of_guy 1 string)` refuses `(name_of_guy 5)`; checked, never entailed. See
[argtypes.md](argtypes.md).

## R

**Range restriction** ![kb](../.github/badges/cat-kb.svg): The rule
well-formedness rule (`rules/check-range-restricted`) that every consequent
variable must also appear in the antecedent, so a conclusion binds nothing free.
A head existential `(exists ?y C)` exempts the variables it marks and nothing
else, so a deliberate `∃` is allowed where a typo is still caught. See
[inference.md](inference.md), [skolem.md](skolem.md).

**RCC-8** ![qr](../.github/badges/cat-qr.svg): The region-connection calculus
of 8 base topological relations between two regions — disconnected, externally
connected, partially overlapping, equal, and the two proper-part relations with
their converses. `vaelii.impl.space`, registered as `:rcc8`. See
[space.md](space.md).

**Record** ![backend](../.github/badges/cat-backend.svg): The stored shape of a sentex — a
`LiteralSentex` or a `RuleSentex` — as distinct from the knowledge it holds. See
[storage.md](storage.md).

**`recover`** ![backend](../.github/badges/cat-backend.svg): Rebuild the taxonomy
and JTMS from the durable stores after a restart, ending in a `settle` so belief
is applied consistently either side of a restart. See [storage.md](storage.md).

**Refusal** ![kb](../.github/badges/cat-kb.svg): An `ex-info` thrown instead of accepting —
at an entry point, or at a namespace load, carrying a `:type` keyword the caller
discriminates on.
The vocabulary is closed by hand: `type_contract_test` pins every one, `refusal_roster_test`
demands each be provoked by a test and looked up in a page, and
[troubleshooting.md](troubleshooting.md) is the index. Distinct from a `violations` entry,
which is filed and moves no belief, and from a Nogood, which is arbitrated rather than
thrown. A new `:type` is caller-visible vocabulary and owes a changelog entry; reusing
`:bad-table-entry` with a fresh `:mismatch` is the cheaper move, and the `:mismatch`
values are a closed vocabulary of their own, pinned beside the `:type` one. See
[troubleshooting.md](troubleshooting.md).

**Region (relabel scope)** ![tms](../.github/badges/cat-tms.svg): The forward consequence closure
of what changed — the scope a relabel is confined to, with everything outside
held fixed as a boundary. See [nmtms.md](nmtms.md).

**Region (spatial)** ![qr](../.github/badges/cat-qr.svg): A region of space — what
RCC-8's eight base relations hold between. A declared collision with the JTMS one, and
nothing else. See [space.md](space.md).

**`reindex`** ![backend](../.github/badges/cat-backend.svg): Rebuild the index store
(the trie, secondary roots, rule index, exception re-check index, and term index)
wholesale from the
records, then recover — the repair for a stale on-disk index layout. See
[indexing.md](indexing.md).

**`relation`** ![kb](../.github/badges/cat-kb.svg): The common parent of
`predicate` and `function` — every head that may be applied to arguments. The two
specializations remain disjoint: a predicate holds or fails; a function denotes or
evaluates to a value. See [taxonomy.md](taxonomy.md#relations-and-arity-policy).

**Relation algebra** ![qr](../.github/badges/cat-qr.svg): `{:universe :identity
:compose :converse}` — the base relations, the diagonal, the composition table
and the converse map. A parameter to one engine rather than a reasoner of its
own, which is why a new calculus is a table and a prover. See [qcn.md](qcn.md).

**`relation_application`** ![kb](../.github/badges/cat-kb.svg): The CxCore collection of
expressions shaped `(R a…)` — a relation applied to arguments — specializing into
`atomic_formula` where `R` is a predicate and `non_atomic_term` where it is a function,
the two disjoint. Documentary: no reader classifies a compound argument by its shape, so
an `arg` or `quotedArg` declaration naming it stores and convicts nothing. See
[argtypes.md](argtypes.md).

**Representative** ![kb](../.github/badges/cat-kb.svg): The elected head of an
equivalence class — the head of the `rewriteOf` chain, else the lexicographically
smallest symbol. Content-keyed, so it cannot depend on arrival order. See
[equality.md](equality.md).

**Rete / TREAT** ![inference](../.github/badges/cat-inference.svg): The opt-in
alpha network that keeps facts in RAM indexed by argument value, answering a
non-trigger antecedent's join by hash lookup instead of a trie rescan. Off by
default behind `chain/*matcher*`. See [inference.md](inference.md).

**`rewriteOf`** ![kb](../.github/badges/cat-kb.svg): A directional equality —
`(rewriteOf P D)` marks `D` deprecated and migrates onto `P`. It names the
representative and, being about spelling, may relate any terms. See
[equality.md](equality.md).

**Roster** ![kb](../.github/badges/cat-kb.svg): An enumeration written out and kept in
step **by hand**, as against a *view*, which is derived from the declaration it projects
and cannot drift from it. The word is used against itself throughout
[predicates.md](predicates.md) — "an open field is a roster again, with the same drift and
none of the checking" — the twenty-odd functor-keyed ones being projections of one fact
that each had to be remembered separately. What is left is named where it stands: a roster
the declaration cannot derive says so on its own docstring. Term roster is the second,
declared sense and carries none of this one's pejorative — it is a set of names the index
keeps, not a list anybody maintains. See [predicates.md](predicates.md).

**Rule index** ![backend](../.github/badges/cat-backend.svg): The predicate index
keying rules by their antecedent *and* consequent predicates — both sets
complete whatever the direction — so "what could conclude P?" is answerable
without a scan. See [indexing.md](indexing.md).

**RuleSentex** ![kb](../.github/badges/cat-kb.svg): The sentex record for a sentence
that is an implication, adding the rule-only slots `[antecedent consequent varmap
direction defeasible assumption constraint]`. Indexed additionally by
antecedent/consequent predicates. See [inference.md](inference.md).

## S

**`sameAs`** ![kb](../.github/badges/cat-kb.svg): The OWL equality over
individuals — reflexive, symmetric, transitive — feeding the one equivalence
closure; neither name is deprecated. See [equality.md](equality.md).

**Scenario** ![qr](../.github/badges/cat-qr.svg): One concrete arrangement
consistent with a network — a single base relation per pair, where the network
holds sets. Found by backtracking search over the tightened network, and a
function of the facts alone, so it is repeatable.
`core/qualitative-scenario` / `qualitative-scenarios`. See
[scenario.md](scenario.md).

**Secondary roots** ![backend](../.github/badges/cat-backend.svg): The three
single-level index roots the trie's left-to-right narrowing cannot supply —
context `[:context-root]`, functor `[:functor-root]`, and argument-position `[:argument-root]` — each a
set whose cardinality is its own count. See [indexing.md](indexing.md).

**`seeAlso`** ![kb](../.github/badges/cat-kb.svg): A curation cross-reference —
`(seeAlso a b)` points a reader from term `a` to term `b`. **Directional**: the reverse is
a separate assertion, never an implied one. Documentation vocabulary beside `comment`,
read by a browser and by no inference path. See [predicates.md](predicates.md).

**Semi-naive** ![inference](../.github/badges/cat-inference.svg): The forward-
chaining evaluation strategy — only newly-derived facts trigger the next round
of rule firings, rather than rejoining the whole KB each pass. See
[inference.md](inference.md).

**Sentence** ![kb](../.github/badges/cat-kb.svg): A closed **Formula** — one with no free variables.
Every stored sentex holds one: a non-rule sentence must be **Ground**
(`checks/check-ground`), and a rule's variables are implicitly universal. A
possibly-open goal is a **Pattern**, not a sentence. The `:sentence` slot keeps the
readable form for display and matching. A CxCore collection too, `sentence`. See
[canonicalization.md](canonicalization.md).

**Sentex** ![kb](../.github/badges/cat-kb.svg): The unit of knowledge — a
*sentence* plus the *context* it holds in. Every sentex is in exactly one
context; a rule is a sentex too. See [contexts.md](contexts.md).

**`settle`** ![tms](../.github/badges/cat-tms.svg): The post-chaining fixpoint
that relabels belief, resolves each nogood on defeat-class, and re-evaluates
queued `exceptWhen` exceptions until the blocked set stops moving. See
[nmtms.md](nmtms.md).

**`sibling_disjoint`** ![kb](../.github/badges/cat-kb.svg): Marks a collection so its
`genl`-specializations share no instance pairwise, unless one is a genl of the other —
the `disjoint_metatype` clique keyed off the genl closure, consulted not stored,
belief-following, and raising contradictions through the same JTMS/ASP path as
`disjoint`. Covering is out of scope. See [taxonomy.md](taxonomy.md).

**`siblingDisjointException`** ![kb](../.github/badges/cat-kb.svg): Exempts the one pair
of types it names from a disjointness a `sibling_disjoint` mark or a `disjoint_metatype`
would otherwise force — pair-local, so it does not disturb either type's disjointness from
the parent's other specializations and does not leak to subtypes. Read over the whole KB,
not the reader's context ancestor set, because an exemption removes a clash. See
[taxonomy.md](taxonomy.md).

**Sideways information passing** ![inference](../.github/badges/cat-inference.svg):
Costing each conjunct under the bindings the already-chosen literals will
produce, so the plan reflects the fan-out a literal actually runs with. See
[inference.md](inference.md).

**Sign** ![qr](../.github/badges/cat-qr.svg): One of the three values
`SignNegative` / `SignZero` / `SignPositive` a quantity takes — jointly
exhaustive and pairwise disjoint over the reals, so a *set* of them is a
constraint and its complement a refutation. `signOf` states one;
`qualitativeSum` / `qualitativeDifference` / `qualitativeProduct` compute with
them, and `greaterInMagnitudeThan` settles the one ambiguous entry in the
addition table. See [sign.md](sign.md).

**Skolemization** ![inference](../.github/badges/cat-inference.svg): Replacing
a rule conclusion's existential variable with a term built from the variables
the antecedent bound, so the same binding names the same witness twice and a
re-derivation does not mint a second one. See [skolem.md](skolem.md).

**Stratification** ![inference](../.github/badges/cat-inference.svg): The
well-formedness rule that a rule set must have no cycle through negation — `wff`
refuses an `exceptWhen` (or a `genl`/`genlCx` edge) that closes one. A
purely positive cycle is ordinary recursion. See [exceptions.md](exceptions.md).

**Strength** ![tms](../.github/badges/cat-tms.svg): The assumption strength of a
premise / the class a justification confers — exactly two, `:monotonic` >
`:default`. It propagates from the antecedents: a conclusion is never stronger
than what it rests on. See [nmtms.md](nmtms.md).

**Subsumption (rules)** ![inference](../.github/badges/cat-inference.svg): One rule
covering another — a substitution σ making the covering rule's antecedents a subset of the
covered rule's and its consequent the covered rule's conclusion, so it fires wherever the
covered rule does and concludes at least as much. Predicate-genl aware in both halves and
in opposite directions: an antecedent is covered by one on a *spec*, a consequent covers
one on a *genl*. A reading (`kb-quality`'s `:subsumption`), never a rewrite — nothing is
retracted. See [quality.md](quality.md); the matching-time relation it is built out of is
[inference.md](inference.md)'s predicate subsumption.

**Superseded** ![tms](../.github/badges/cat-tms.svg): The TMS state an equality
merge puts a stale spelling in — stored but not believed and not matching,
subtracting from reported belief rather than forced OUT, so its justified twin
survives. See [equality.md](equality.md).

**`surjection`** ![kb](../.github/badges/cat-kb.svg): `(surjection P)` — a **function
mark**: `P` is single-valued, total on its declared domain, and onto its declared range,
with nothing said about one-to-one. Derives `(functional P)`, enforced at the write, and
the `(predAllSpecified P D)` and `(predSpecifiedAll P R)` requirements off the `arg`
declarations, audited on demand. See [taxonomy.md](taxonomy.md).

**Symmetric arguments** ![kb](../.github/badges/cat-kb.svg): A ground fact of a
symmetric predicate stores with its arguments sorted, so both orders dedup to one
sentex; a pattern is never reordered, and order-insensitive lookup probes both
orders at match time. See [canonicalization.md](canonicalization.md).

## T

**Taxonomy** ![kb](../.github/badges/cat-kb.svg): The in-memory cache of the
`genl` / `genlCx` closures, the equality partition, the predicate metadata,
and the disjointness caches — all belief-following, reconciled each `settle`. See
[taxonomy.md](taxonomy.md).

**Term** ![backend](../.github/badges/cat-backend.svg): A name in the KB's vocabulary — what
the term index is keyed by and the term roster holds. The logic sense is
spelled **Denotational term**. See [indexing.md](indexing.md).

**Term index** ![backend](../.github/badges/cat-backend.svg): The inverted index
`[:term-index term] -> #{handles}` over every indexable subterm of a sentex's
connective-free content, so any sentex is findable by any term it contains
(`find-sentexes`). Numbers, strings, and variables are dropped. Every *symbol* is a
key at every depth; a ground **compound** is one between `*min-indexed-depth*` and
`max-indexed-compound`, and outside those it costs `find-sentexes` a narrowing on its
atoms plus a verify rather than a key. See [indexing.md](indexing.md).

**Term roster** ![backend](../.github/badges/cat-backend.svg): The set of *names*
the term index is keyed by — the KB's vocabulary — held as one index key beside the
postings, so `terms` / `term-count` / `find-terms` cost the size of the vocabulary
rather than a walk over every record. A name enters with the first sentex to mention
it and leaves with the last. See [indexing.md](indexing.md).

**`termsRelated`** ![kb](../.github/badges/cat-kb.svg): A curation grouping —
`(termsRelated t1 t2 …)`, variable-arity, saying the named terms form one cluster so a
reader meeting one is pointed at the rest. Documentation vocabulary beside `comment` and
`seeAlso`, and inert: nothing in the engine reads it. See [predicates.md](predicates.md).

**`thereExists`** ![inference](../.github/badges/cat-inference.svg): The
existential closer — `(thereExists ?x S)` projects `?x` out, so
`(unknown (thereExists ?x S))` reads "there is no `x` such that S". A conjunctive
`S` is joined, so one witness satisfies all of it. A standalone positive one
desugars to `S`'s conjuncts with `?x` a local matched variable. See
[naf.md](naf.md).

**`thing`** ![kb](../.github/badges/cat-kb.svg): The root of the `genl` type
hierarchy — every type reaches `thing` upward. See [taxonomy.md](taxonomy.md).

**`transitiveInArg`** ![kb](../.github/badges/cat-kb.svg): `(transitiveInArg P n R)`
licenses carrying a claim about `P`'s *n*-th argument across an `R`-related pair
— what makes "the part of a wooden table is wooden" derivable without a rule per
predicate. `transitiveInArgInverse` reads it the other way. See
[inherit.md](inherit.md).

**Transitivity** ![kb](../.github/badges/cat-kb.svg): The lifeblood of common
sense, done by cached closures rather than rules for `genl` / `genlCx`, and
by metadata-driven provers for a `(transitive P)` predicate. See
[taxonomy.md](taxonomy.md).

**Trend** ![qr](../.github/badges/cat-qr.svg): Whether a quantity is falling,
steady or rising — the *sign* of its rate of change, stated as `(trendOf Q S)`.
Not a second theory: `(derivativeOf R Q)` names the rate, and the trend is that
rate's sign read at the other end of the edge, a constraint running both ways.
See [sign.md](sign.md).

## U

**`underlying-body`** ![kb](../.github/badges/cat-kb.svg): The body a sentence's
`not` wrappers enclose, whatever its polarity — the *content* question, where
`positive-body` answers the *constraint* one and is nil for a genuinely negative
sentence. What a belief-reading re-check trigger has to key on, since a defeat
stores and removes nothing. See [aggregate.md](aggregate.md).

**Unification** ![inference](../.github/badges/cat-inference.svg): Matching a
pattern against a sentence, binding variables — `unify` / `substitute`, both
handling a dotted rest pattern `(?pred . ?args)`. Type-aware: a sub-predicate or
subtype fact satisfies the antecedent. See [inference.md](inference.md).

**Unique-name assumption (UNA)** ![kb](../.github/badges/cat-kb.svg): Distinct
symbols denote distinct things until an equality sentex says otherwise —
preserved even under the equality closure and made provable by `different`.
Suspended for an unpinned indeterminate term (skolems and `indeterminate_term`
members) until a `rewriteOf`/merge pins it. See [equality.md](equality.md).

**`unknown`** ![inference](../.github/badges/cat-inference.svg): The negation-as-
failure prover — `(unknown S)` holds iff `S` is not derivable over the level-6
prover list. A conjunctive `S` is **joined**, so its conjuncts may share a
quantifier's variable. Ground/closed only and never stored. See [naf.md](naf.md).

## V

**Value** ![kb](../.github/badges/cat-kb.svg): An EDN scalar written in argument position —
a string, a number, a character, a boolean. It denotes itself, which is why its **Kind**
answers both argument readings. See [argtypes.md](argtypes.md).

**Variable** ![kb](../.github/badges/cat-kb.svg): A `?x` symbol standing for an unknown. Canonically renumbered
(`?var0`, `?var1`, …) in a stored rule, with the author's spelling kept in
the **Varmap**. See [canonicalization.md](canonicalization.md).

**Varmap** ![kb](../.github/badges/cat-kb.svg): A rule's map from its canonical
variables (`?var0`, `?var1`, …) back to what the author wrote, so
`sentex/originalize` can restore the original names for display. Facts carry
none. See [canonicalization.md](canonicalization.md).

**`violations`** ![inference](../.github/badges/cat-inference.svg): The
accumulating ledger of conclusions *dropped* on the derivation path — a failed
arg / disjoint / functional check, a placement-less firing, or a derived
cycle through negation — recorded rather than thrown. Four groups drop nothing
and report: the **cross-context** clashes neither writer could see (`:disjoint`,
`:functional` and `:asymmetric`, each carrying `:visible-from`, and the latter two
under `:refuse` only); the seven that say bounded work did not cover everything —
`:exposure-truncated`, `:arbitration-truncated` and `:arity-truncated`, all three
sweeps cut short; `:constraint-exposure-truncated` and `:arity-report-truncated`,
each a pass finding more than it will file — the first naming whichever bound it met, a
cut walk or the entry cap, the second the cap alone; `:partner-sweep-truncated`, a
vantage the cap kept a pass from consulting at all; and
`:context-edge-exposure-truncated`, the only one filed eagerly from an assert rather than
a settle, over merges a `genlCx` edge's ancestor set did not reach; a retroactive
`:arity` reach beside a `:non-confluent` pair of equations; and the provers' own —
`:aggregate` for an extent that will not reduce, `:qualitative-inconsistency` and the two
`:metric-temporal-*` for a network a context cannot satisfy, and `:sign-inconsistency`
for sign facts that leave a quantity no sign at all. An entry about a term, a pair or
a budget carries no `:sentence` or `:context`, and a network report or a
`:post-join-ambiguous` carries a `:context` with no `:sentence`. The roster of every kind, with the `:detail` keys each carries, is
the set of tables in `core/violations`' docstring, pinned to the sources by
`violation_roster_test`. See [inference.md](inference.md),
[nmtms.md](nmtms.md).

**Visibility (genlCx up-closure)** ![kb](../.github/badges/cat-kb.svg):
Which sentexes a context can use — those asserted in it or in any context it sees
(its `genlCx` up-closure). Constraint checks and matching are visibility-
scoped. See [contexts.md](contexts.md).

## W

**WFF (well-formedness)** ![kb](../.github/badges/cat-kb.svg): The structural
checks `assert` runs before storing — that `genl`/`genlCx`, `disjoint`,
`arg`, and the equality relations are shaped right and acyclic, plus rule
stratification. See [naming.md](naming.md).

**`why` / `why-not`** ![tms](../.github/badges/cat-tms.svg): Introspection.
`why` returns the proof tree of a believed handle down to premises; `why-not`
explains a stored-but-OUT datum (`:defeated` / `:superseded` / `:unsupported`)
or a blocked conclusion. `why-not`'s `{:nearest n}` answers the one case with nothing
stored to explain: it runs a bounded backward search and names the rules that came
closest, with the antecedents each is still missing. See [nmtms.md](nmtms.md),
[api.md](api.md).

**Wrapper** ![kb](../.github/badges/cat-kb.svg): A connective or marker form enclosing a sentence rather than asserting
of it — `not`, `and`, `implies`, the `set/*Rule` family, `exceptWhen`, `ist`.
`nm/literals` descends the wrappers to reach the literals. Storage's serialization unit
is a **Frame**, which is a different thing. See [naming.md](naming.md).
