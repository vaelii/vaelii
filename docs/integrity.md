# Bounded KB integrity

- **Covers:** `kb-integrity` — one read-only checkpoint report for the complete visible
  `predAllSpecified` / `predSpecifiedAll` population and query-only definition clashes
  over a caller-owned finite set of ground candidate terms.
- **Not here:** repairing findings, enumerating a domain, vocabulary completeness,
  generic constraint auditing, or the represented settled dilemmas returned by
  `contradictions`; how definitions infer membership → [defns.md](defns.md); what a
  specified declaration requires → [predall.md](predall.md); general knowledge-quality
  census readings → [quality.md](quality.md).
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

`:status :audited` means both passes ran and neither found a gap. `:status :gap` cannot
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
