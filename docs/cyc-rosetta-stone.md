# Cyc ↔ Vaelii Rosetta Stone

## Core Concepts

```
Cyc                 → Vaelii
microtheory (Mt)    → context
genlMt              → genlContext
assertion           → sentex
constant            → symbol (CapitalCamelCase individuals, snake_case types, camelCase preds)
collection          → type as unary predicate: (dog Muffet) not (isa Muffet Dog)
genls               → genl
genlPreds           → genl
don't-care var (??) → head existential: (exists ?y ...) — syntactic, not naming convention
rename              → no equivalent (use sameAs/rewriteOf for merging, but no true rename)
arg1Isa             → no equivalent. Instead of (arg1Isa PRED TYPE), use (argIsa PRED 1 TYPE)
wff?                → v/check. Checks argIsa, disjoint, functional, naming conventions, etc.
```

## Gotchas for Cyclists

**argIsa is entailment, not restriction:** In Cyc, argIsa constraints are gates
at assert time. In vaelii, they are entailment sources — `(argIsa parentOf 1 animal)`
over `(parentOf Fred Mary)` ENTAILS `(animal Fred)`, it doesn't reject the assertion.
Our bridge's `check-guarded` / `assert-guarded` enforces the restriction layer.

**Open-world silent acceptance:** Vaelii silently accepts any assertion with any
predicate — `(fghgwgads 212)` stores without error. No predicate declaration check,
no type check at assert time. Typos are the same bug class as undeclared predicates.

## Negation & Mutual Exclusion

```
Cyc                       → Vaelii
negationPreds (unary)     → (disjoint P Q) — native, since collections ARE preds in V
negationPreds (binary)    → paired implication rules:
                            (implies (P ?x ?y) (not (Q ?x ?y)))
                            (implies (Q ?x ?y) (not (P ?x ?y)))
                            Note: Vaelii permits contradictory sentexes to coexist until
                            JTMS/belief repair, unlike insertion-time integrity
no equivalent             → (contradictions kb)
SymmetricBinaryPredicate  → (symmetric P)
AsymmetricBinaryPredicate → (asymmetric P)
genlInverse               → no native equivalent. use a forward rule:
                            (implies (P ?x ?y) (Q ?y ?x))
                            vaelii's (inverse P Q) is the stronger biconditional
disjoint                  → disjoint — type/predicate mutual exclusion,
                            closed under genl. Works for unary preds because
                            collections ARE predicates in V
unk                       → unknown
assertedMoreSpecifically  → no equivalent
completeExtentEnumerable  → no equivalent
```

## WFF Modes (Cyc → Bridge mapping)

Cyc had three Well-Formed Formula checking modes.

```
Mode       Cyc behavior                     
strict     constraints must be provable     
lenient    constraints must not be disjoint
assertive  constraints must not be disjoint, eagerly conclude tighter isas
```

Vaelii WFF is assertive.

## Privileged Contexts

```
Cyc                          → Vaelii              Notes
LogicalTruthMt               → (no analogue)       logical truths baked into engine

CoreCycLMt                   → CoreContext         spindle head: code-interpreted
                                                   vocabulary

UniversalVocabularyMt/BaseKB → UniverseContext     mid anchor, decontextualization
                                                   target

CurrentWorldDataCollectorMt  → WellContext         "all the usual stuff" — sees
                                                   the full shipped ontology

InferencePSC/EverythingPSC   → ?ctx                not a context — omit the context
                                                   arg or pass a variable to query
                                                   unscoped

## Operations

```
Cyc                 → Vaelii API call
assert              → (v/assert kb sentence context opts) → handle
unassert            → (v/retract! kb handle) → {:removed-sentexes n :removed-justifications n}
find-assertion-cycl → (v/sentexes-matching kb sentence context) — literal only, returns collection
                      (sentex-matching via our bridge utils — singular, nil if ambiguous)
ask (backward)      → (v/query kb goal ctx {:max-depth n}) — bounded backward chaining
ask (unbounded)     → (v/prove kb goal ctx) — DFS backward chaining
ask (boolean)       → (v/provable? kb goal ctx)
ask (no inference)  → (v/ask kb goal ctx) / (v/ask? kb goal ctx) — no rule expansion
fi-ask              → (v/query kb goal ctx {:max-depth n}) — vars bind in goal
wff?                → (v/check kb sentence context opts) → vector of problem maps
rename              → no equivalent
```

## Truth Maintenance (actual API calls)

```
Cyc                → Vaelii API call
TMS assert         → (v/assert kb sentence context {:strength :monotonic|:default})
                     :monotonic = known-true, not defeasible
                     :default = defeasible at edges (most common-sense content)
TMS retract        → (v/retract! kb handle) — cascading teardown of solely-supported conclusions
why (support tree) → (v/why kb handle opts?) — proof tree: support → rule + antecedents
why-not            → (v/why-not kb handle) — :defeated / :superseded / :unsupported / :not-stored
                     (v/why-not kb sentence context) — adds :excepted (exceptWhen blocks it)
no equivalent      → (v/in? kb handle) — is this handle IN (believed)?
                     (v/believed kb handles) — batch: set of handles that are IN
no equivalent      → (v/settle-stats kb) — fixpoint iteration instrumentation
no equivalent      → (v/with-deferred-settle kb & body) — batch, settle once at end
```

## Rules (actual API calls)

```
Cyc                 → Vaelii API call
assert rule         → (v/assert-rule kb [antecedents] consequent context opts)
                      opts: {:direction :forward|:backward|:both|:inert
                             :strength :monotonic|:default
                             :chain? bool :max-depth n}
forwardRule         → {:direction :forward} or (set/forwardRule ...) wrapper
backwardRule        → {:direction :backward} or (set/backwardRule ...) wrapper
both (default)      → {:direction :both}
:code direction     → {:direction :inert} or (set/inertRule ...) wrapper
rule vars           → ?x (same convention, but lowercase)
range-restricted    → yes — every consequent var must appear in antecedent
unbound-pred rule literals → REJECTED (:not-indexable) — must instantiate per predicate
nested implies      → ACCEPTED but INERT — stored as dead sentex, not indexed
                     as live rule (filed as vaelii/vaelii#8)
arity check         → catches too-few args but NOT too-many (vaelii/vaelii#9)
```

## Shared (both Cyc and Vaelii have)

- Anytime inference (budgeted): `ask-within`, `prove-within`, `resume`
- Watch (reactive queries): `(v/watch kb goal context f)` — callback when belief moves
- Abduce: `(v/abduce kb goal context opts)` — hypotheses as :default premises in scratch context
- argIsa / interArgIsa
- Equality partition (rewriteOf / sameAs / equals)
- Defeasible defaults with exceptions
- Polycanonicalization

## Vaelii has, Cyc doesn't

- `fork` (overlay KBs — private writable copy over frozen base)
- ASP solver backend (`set-solver kb :asp`)
- Qualitative constraint reasoning (Allen intervals, RCC8, etc.)
- Export/import dump format
- Web browser for ontology exploration

## Cyc has, Vaelii doesn't

- Rename (no equivalent in Vaelii)
- NL generation
- Rule schemata / createRule (meta-rules that conclude rules)
- schematicRuleFormula
- transitiveViaArg
- negationPreds for binary+ preds (use paired (not S) rules instead)
- completeExtentEnumerable
- notAssertible
- arg1Isa / arg2Isa syntactic sugar
- Strict WFF mode
- irreflexive / antiTransitive / antiSymmetric (filed as vaelii/vaelii#14)
