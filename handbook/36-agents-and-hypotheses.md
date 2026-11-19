# 36. Agents and hypotheses

- **Covers:** what an agent believes, stated in the agent's own context and read with
  `believes`; a further modal predicate granted with `modal_predicate`; the predicates a
  theory lets `abduce` hypothesize; and a rule that compares a count or a sum.
- **Not here:** context topology in general → [ch. 23](23-contexts.md); `unknown` and
  `thereExists`, the family aggregation belongs to → [ch. 32](32-negation.md); a
  skolem witness for an open hypothesis → [ch. 33](33-existentials.md).
- **Assumes:** [ch. 23](23-contexts.md), [ch. 24](24-strength.md),
  [ch. 32](32-negation.md).

## An agent's beliefs live in the agent's context

**Practice.** State what an agent believes as ordinary sentences in the agent's context,
named `CxAgent` followed by the agent's name. Ask about it with `(believes Agent P)` from
any context. Add a `genlCx` edge from the agent context to a shared context only when the
agent holds that context's content too.

**Example.** `core.txt` grants the projection for `believes`:

```clojure
(modal_predicate believes)
```

A composed pair of agents over temporaries, with each sentence asserted in the agent
context named in the comment:

```clojure composed
(able TmpTweety flying)          ; in CxAgentTmpAlice
(not (able TmpTweety flying))    ; in CxAgentTmpBob
```

From CxWell, `(believes TmpAlice (able TmpTweety flying))` and
`(believes TmpBob (not (able TmpTweety flying)))` both answer true, and
`contradictions` stays empty.

**Why.**

- Logical: two agents can believe contradictory things without the KB contradicting
  itself. The agent contexts share no `genlCx` ancestor, so no context sees both a claim
  and its negation, and no nogood forms.
- Engine: `BeliefProjectionProver` answers a `believes` goal whose agent argument is
  ground by proving `P` in the agent's context, never in the asker's. An unbound agent is
  not claimed, because it would mean searching every agent's context. The prover runs at
  completeness 50, so a stored `(believes A P)` fact and a projected answer fold into one.
- Engine: the proposition is a mention, so the asker's equality merges do not rewrite a
  term inside it. The agent's own merges do, because the projection runs in the agent's
  context: the substitution goes through exactly when the agent holds the identity, the
  de dicto reading. The engine does not answer the de re reading.
- Context: an agent context has no `genlCx` edge by default, so an agent who believes a
  falsehood does not contradict the shared knowledge, and nothing true in the shared
  context leaks into the agent's beliefs. An edge to CxUniverse or a middle theory lets
  the agent hold that content and reason with its rules.

**Why not the other ways.** Storing `(believes A P)` facts in a shared context makes `P` an
argument, so no rule reasons inside the agent's beliefs and none of `P`'s consequences is
derived for the agent. Giving each predicate an agent argument makes every relation a new
one and puts both agents' contrary claims in one context, where they clash. Asserting
`(believes A P)` does not store `P` in the agent context; the engine has no write that
routes a belief, so the author asserts `P` there directly.

**Audit.** For each agent context the change creates, list its `genlCx` edges and say
which shared content the agent holds. A forward rule firing over an agent's belief with
nowhere to place its conclusion leaves a no-placement entry in `violations`; read it for
each new agent context.

## A further modal predicate

**Practice.** To read another attitude (`knows`, `desires`, `intends`) as a projection,
grant `(modal_predicate P)` in the context whose readers should project it, or call
`register-modal-predicate`.

**Why.** The grant is read from the asking context's `genlCx` ancestor set, so it is a
policy of the context that states it: one theory may read `knows` modally while another,
seeing the same predicate, reads it as an ordinary relation. Nesting follows from the
same scoping. `(believes A (believes B P))` proves the inner `believes` in A's context,
and the inner one projects only when the grant is visible there. An independent agent
context sees no grant, so a nested belief is false until the agent context gets an edge
that reaches one.

**Why not the other ways.** An ungranted attitude predicate is an ordinary relation, and
`CxSocial.txt` uses `knows` that way, as the predicate `friendOf` and `marriedTo` generalize
to. A grant in CxUniverse would make every context that sees CxUniverse read it modally,
including the ones that state `knows` facts between people.

**Audit.** For each `modal_predicate` grant, name the context that states it, and check
that no context below it states the predicate as an ordinary relation.

## What a theory lets `abduce` assume

**Practice.** Grant `(abducible_predicate P)` in the theory's own context, for the
predicates a failed proof in that theory may assume. Grant few, and state in the
theory's `;;` notes why each is a hypothesis worth making.

**Example.** `CxBiology.txt` grants one:

```clojure
;; Sleep is what this theory is willing to assume. A proof that dead-ends on an animal
;; not acting may hypothesize that it is asleep — the one explanation here inexpensive enough
;; to be worth guessing, since an animal is asleep for part of every day and nothing
;; else follows from it. Nothing else is granted: an abducer that will assume anything
;; explains everything and is worth nothing, so each grant is a policy this context
;; states rather than a capability the engine has.
(abducible_predicate asleep)
```

**Why.**

- Logical: abduction answers what would have to be true for a goal to be provable. An
  abducer allowed every predicate makes every goal answerable, so the grants decide which
  explanations the theory considers.
- Engine: `abduce` runs `prove`, collects the subgoals it could neither match nor expand,
  and mints a hypothesis for each one that passes four checks: a ground positive literal,
  a predicate granted abducible where the question is asked, a sentence `assert` would
  accept, and no visible believed negation. A subgoal that fails a check comes back in
  `:refused`; under `CxBiology`, a goal that needs `(bird …)` returns it there.
- Engine: each hypothesis is a `:default` premise in a fresh scratch context below the
  asking context, so a `:monotonic` contrary defeats it and nothing that existed before
  sees it. Candidates are taken in content order, the minted set is capped, and the
  result is irredundant: dropping any one hypothesis stops the goal from following.
- Context: the grant is a policy of the context that states it, read from the asking
  context's ancestor set, so a sibling theory reading `asleep` assumes nothing.

**Why not the other ways.** A grant in CxUniverse lets every context that sees
CxUniverse assume the predicate. Stating a guessed fact in the theory instead of granting it makes the guess
hold for every member, where a hypothesis holds only in the scratch context of the
question that needed it.

**Audit.** For each grant, run `abduce` on a goal the theory expects to explain, read the
`:hypotheses` and the `:refused` lists, and confirm that each hypothesis is one the
theory's note says it may assume.

## A count or a sum in a rule

**Practice.** Write an aggregate as an antecedent of the form
`(agg/count ?n ?v Body)`, with a generator antecedent that binds the group variable, and
write any comparison on `?n` after the aggregate. When the extent to count is a
disjunction, name it with a rule first and aggregate over that rule's conclusion.

**Example.** A composed rule over `life.txt`'s `parentOf` and a temporary consequent:

```clojure composed
(set/forwardRule
  (implies (and (person ?x)
                (agg/count ?n ?c (parentOf ?x ?c))
                (lessThan 2 ?n))
           (tmp_large_family ?x)))
```

**Why.**

- Logical: a count is a fact about the extent of a relation, not about any one tuple, so
  it is computed from what is believed and never stored as a premise.
- Engine: the aggregate projects out `?v` and binds only `?n`. A variable the rule names
  outside the aggregate is the group and must be bound by a generator first
  (`:naf-not-closed` otherwise); a variable only inside the body is local to the count,
  bound by the body's join. A disjunctive body is refused `:not-well-formed`, because a
  witness that satisfied both alternatives would be counted twice.
- Engine: the aggregate and every literal that reads `?n` run after the join, in the
  placement context and in written order. A comparison written before the aggregate it
  reads is refused `:naf-not-closed`, not reordered. The count is taken where the
  conclusion lands, so the facts that bind the group decide which context's count the
  rule reads.
- Maintenance: a counted fact arriving, leaving or being defeated re-checks every firing
  resting on the count, and a firing licensed at a count of 3 is withdrawn at a count of
  1. A rule joining on a count is re-joined whenever a counted fact arrives.
- Reach: the body runs over the registry, which expands no rule. A forward-derived fact
  and a cached closure are counted; a conclusion of a backward rule is not.
- Stratification: the body's predicates are negative edges in the rule dependency graph,
  so a rule whose conclusion feeds its own count is refused `:not-stratified`.

**Why not the other ways.** A count stated as a fact goes stale when a counted fact changes,
and the engine derives no aggregate as a rule consequent, because truth maintenance has
no invalidation for a computed value. A rule per expected count restates
the comparison per value.

**Audit.** For each aggregate rule, name the generator that binds the group, confirm that
every counted predicate is stored or forward-derived, and check that the comparison
follows the aggregate.
