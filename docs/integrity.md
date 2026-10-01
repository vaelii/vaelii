# Bounded KB integrity

- **Covers:** `kb-integrity` — one read-only checkpoint report for the complete visible
  `predAllSpecified` / `predSpecifiedAll` population, query-only definition clashes
  over a caller-owned finite set of ground candidate terms, and the predicate `genl`
  edges that widen a declared argument type.
- **Not here:** repairing findings, enumerating a domain, vocabulary completeness,
  generic constraint auditing, or the represented settled dilemmas returned by
  `contradictions`; how definitions infer membership → [defns.md](defns.md); what a
  specified declaration requires → [predall.md](predall.md); how an `arg` declaration
  descends a predicate `genl` edge → [argtypes.md](argtypes.md); general
  knowledge-quality census readings → [quality.md](quality.md).
- **Assumes:** sentex, context, ground term, `genl` → [glossary.md](glossary.md).

## The call

```clojure
(v/kb-integrity kb #{-212 0 212} 'CxUniverse)
;; => {:status :audited :candidate-count 3}

(v/kb-integrity kb candidates 'CxUniverse
                {:max-work 10000 :max-ms 1000 :max-results 100})
;; => {:status :truncated :reason :max-work :candidate-count 500
;;     :work 10000 :elapsed-ms 37.2 ...partial finding categories...}
```

The candidate argument must be a set, and every member must be ground. This is the cost
and meaning boundary: a caller names the known terms worth checking; the query engine
never turns the audit into an open term enumerator. Collections need not be repeated.
The sweep derives its finite collection population from visible `defnSufficient`
declarations and their `genl` ancestors, exactly the population the positive definition
prover can reach.

The optional budget has three independent bounds. `:max-work` meters direct audit rows,
prover dispatches, and prover results, so a one-term candidate set cannot hide the cost
of an aggregate condition over a large KB extent. `:max-ms` is a cooperative wall clock,
checked at the same boundaries. `:max-results` caps findings. Reaching any bound returns
`:status :truncated` with a reason and never labels a partial sweep `:audited`. The daemon
fills all three when the map is absent, clamps callers to its ceilings, and refuses an
over-ceiling request by type before acquiring the operation's work.

Work and time are cooperative, not preemptive hard ceilings. The sweep checks immediately
before and after every prover selection/dispatch callback and every result-stream pull.
An opaque callback—or a chunked lazy stream that computes several answers in one pull—may
overrun until it returns; the following checkpoint then truncates before another callback
or pull begins. Changing the public `Prover` SPI to require one-answer yielding is outside
this sweep. `:max-results` is different: it is an absolute bound on findings returned,
including snapshots truncated for work or time.

The definition pass performs one unavoidable open census of visible `defnSufficient`
declarations because callers intentionally supply terms, not collection names. It then
validates one collection and one ground candidate at a time. The specified pass likewise
uses small declaration censuses only to identify its finite worklist, then audits each
declared predicate independently. The widening pass does the same: one census of visible
`arg` declarations, then one direct `genl` edge at a time. These focused units are where
cooperative checkpoints and partial-result preservation sit.

An explicit `nil` options value means the same thing as omitting the options arity,
in-process and through the generated daemon clients. The daemon still supplies its own
ceilings before dispatching either spelling.

A finding changes the top-level status and adds only the populated categories:

```clojure
{:status :gap
 :candidate-count 1
 :definition-inconsistencies
 [{:collection widget
   :term 7
   :passing-sufficient
   [{:defined-collection widget :condition (qualifies ?x)}]
   :failing-necessary
   [{:defined-collection widget :condition (required ?x)}]}]
 :all-specified-violations
 {[predAllSpecified hasPet person]
  {:status :audited :violations #{Bob}}}}
```

`:status :audited` means all three passes ran and none found a gap. `:status :gap` cannot
be confused with that clean shape even when only one sparse category is present. The
specified category is exactly `all-specified-violations`, including its typed declaration
gaps; it is composed, not reimplemented.

## What a definition finding means

The definition prover treats a passing own-or-spec `defnSufficient` as a positive
membership witness. A failing own `defnNecessary` is simultaneously a negative witness.
When no strict-genl necessary fast-fails the positive path, the collection can therefore
answer both `(Coll term)` and `(not (Coll term))`. The report preserves every passing and
failing declaration as evidence, including the collection on which an inherited
sufficient was declared.

This is deliberately narrower than `contradictions`. That reader reports settled,
represented default dilemmas already present in the truth-maintenance state. A computed
definition condition is evaluated only when queried, so its latent clash has no stored
pair for `contradictions` to enumerate. `kb-integrity` asks the bounded definition
question without changing the meaning or cost of the existing reader.

The sweep stores and files nothing. Aggregate diagnostics raised only because a
definition condition was evaluated are redirected to an audit-local sink, preserving
the condition's truth without changing the live violations ledger or logs. It identifies
gaps; remediation remains a separate, explicit write.

## What a widening finding means

`(genl P Q)` between predicates says every `P` tuple is a `Q` tuple, so `Q`'s `arg`
declarations constrain `P`'s tuples too ([argtypes.md](argtypes.md)). When `P` declares
its own type at a position and `Q` demands one that type is not subsumed by, the edge
does not say what its author meant: `(arg parentOf 1 animal)` under
`(genl parentOf originatorOf)` with `(arg originatorOf 1 person)` makes every animal
parentage an `originatorOf` tuple, which only persons may fill.

Nothing on the write path reports this as a defect of the edge. Depending on the
contexts the declarations sit in and on arrival order, `(parentOf Fido Rex)` over two
dogs is refused `:arg-type`, or is admitted with `(person Fido)` minted onto it. Neither
outcome files a violation or a contradiction naming the edge. So the sweep reads the
declarations instead of any fact:

```clojure
{:status :gap
 :candidate-count 0
 :genl-arg-widening
 [{:spec parentOf :genl originatorOf :arg 1 :spec-type animal :genl-type person}
  {:spec parentOf :genl originatorOf :arg 2 :spec-type animal :genl-type person}]}
```

One finding is reported for each spec type at each position that no demanded type
subsumes. Subsumption is the reflexive `genl` closure read from the audit context. A
spec type that *is* subsumed (`fatherOf` declares `person` under `parentOf`'s `animal`)
is compatible, and so is an identical type. A spec position that holds several declared
types is their intersection, so it is compatible as soon as one of them is subsumed.
`:genl-type-declared-on` is present when the demanded type is declared above `Q`, on a
super-predicate the constraint inherits through `res/constraining-predicates`, the same
closure `assert`'s argument check reads.

The scope is deliberate:

- **Declaration census, not candidate terms.** A widening is a fact about two
  predicates' declarations, not about any individual, so the caller's candidate set does
  not bound it. The pass reads every visible `arg` declaration once to find the
  predicates that declare their own types (a few hundred on the shipped load), then each
  such predicate's direct visible `genl` edges. Edges out of a predicate that declares
  nothing of its own are skipped, because such a predicate has no declared domain for an
  edge to widen. A multi-step chain is still covered: the demanded types come from the
  whole closure above the direct genl.
- **`arg` only.** `genlArg` bounds a position one level up (a subtype, not a member),
  `quotedArg` types a mention, and `interArg` and the covering forms (`args`,
  `argAndRest`, …) relate positions rather than typing one. Comparing any of them
  against an `arg` type would compare different levels, so none is read here.
- **`genl` only.** `genlInverse` and other relation-to-relation forms are not read.
- **Visible from the audit context.** An edge or declaration asserted in a context the
  audit context cannot see contributes nothing, as for every other read.

Each declaration row, edge and position comparison spends one work unit, and
`:max-results` counts these findings after the definition and specified categories, in
that order.
