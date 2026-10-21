# Belief projection: what an agent holds true

- **Covers:** `(believes Agent P)` — answered by proving `P` inside `Agent`'s own
  context rather than in the asker's, so agents may disagree without the KB
  contradicting itself. `modal_predicate` / `register-modal-predicate` open the same
  machinery to `knows`, `desires`, `intends`. The **opacity** of `P`: which party's
  equality merges may rewrite a term inside a belief.
- **Not here:** a modal *logic* — no K/T/4/5 schema, and a nested `(believes A (believes B P))`
  projects only where the marker is visible — nothing by default, since an independent
  agent context cannot see the grant (see below); hypothetical worlds → [abduction.md](abduction.md).
  The de re reading of a belief, and any operator for a *group* of agents. Nor the *other*
  belief this engine has a word for: whether the KB itself holds a stored sentex true is
  the JTMS label, and it is [nmtms.md](nmtms.md). Nothing here moves it — an agent's
  beliefs are ordinary facts in the agent's context, believed on the ordinary terms.
- **Assumes:** context, `genlCx` visibility, the prover registry → [contexts.md](contexts.md),
  [glossary.md](glossary.md); the equality partition → [equality.md](equality.md).

Two agents can believe contradictory things without the KB being inconsistent — that is
what a context lattice is *for*, and the engine already has the lattice. What belief
projection adds is one convention and one prover over it: no new belief primitive, no
change to the JTMS, the taxonomy or the index.

```clojure
;; Alice's beliefs are ordinary facts in Alice's own context.
(v/assert kb '(flies Tweety) 'CxAgentAlice)

(v/ask? kb '(believes Alice (flies Tweety)) 'CxWell)   ; => true
(v/ask? kb '(believes Bob   (flies Tweety)) 'CxWell)   ; => false — not Bob's context
(v/ask? kb '(flies Tweety) 'CxWell)                    ; => false — base believes nothing
```

`(believes Alice (flies Tweety))` is `(flies Tweety)` asked in `CxAgentAlice`. The agent
symbol names the context by a fixed convention — `Alice` ↦ `CxAgentAlice`
(`vaelii.impl.modal`) — and a generated name passes exactly the checks a hand-written
context name does (`naming/context?`), so nothing downstream can tell a minted agent
context from any other. A variable in the proposition binds through the projection:
`(believes Alice (flies ?x))` answers `{?x Tweety}`.

## The prover

`BeliefProjectionProver` (in `vaelii.impl.provers`, in `default-provers`) recognizes a
modal goal and sub-queries the inner sentence in the agent's context. Four decisions:

- **Applicable** to a registered modal predicate, of arity 2, whose **agent argument is
  ground** and yields a legal context name, over a sentence-shaped proposition. An
  unbound agent — `(believes ?who P)` — is *not* claimed: that would mean "search every
  agent's context", a different and far costlier operation, so it is excluded and left to
  whatever else answers it.
- **Cost** `:compute` — a projection is a sub-query through the registry, not a lookup.
- **Completeness** 50 — it *augments*. `(believes A P)` may also be a plain stored fact,
  and `believes` is a real relation you may want to assert; the fact prover stays in play,
  and a stored belief and a projected one fold to one answer rather than double-counting.
- **Solve** proves `P` in the agent's context — the agent's, never the asker's, which is
  what keeps one agent's beliefs out of another's answers.

## The headline property: contradictory agents coexist

```clojure
(v/assert kb '(flies Tweety)       'CxAgentAlice)
(v/assert kb '(not (flies Tweety)) 'CxAgentBob)

(v/ask? kb '(believes Alice (flies Tweety))       'CxWell)  ; => true
(v/ask? kb '(believes Bob   (not (flies Tweety))) 'CxWell)  ; => true
(v/conflicts kb)       ; => []  — the two share no context, so no settle ever sees a clash
(v/contradictions kb)  ; => []
```

Alice's `CxAgentAlice` and Bob's `CxAgentBob` share no `genlCx` ancestor, so no context
sees both the claim and its negation and no contradiction is raised. This is the property
no Datalog / SPARQL / DL rival can field, and it falls out of the lattice by construction
rather than being engineered here.

## Independence, and inheriting base

An agent context has **no `genlCx` edge** by default, so it is independent: the agent
believes exactly what is asserted in its context, and nothing true in base leaks in. That
is the default for modal use — an agent who believes a falsehood should not thereby
contradict base. To let an agent see base too, add the edge yourself:

```clojure
(v/assert kb '(green Grass) 'CxUniverse)                 ; a base fact
(v/ask? kb '(believes Alice (green Grass)) 'CxWell)      ; => false — Alice is independent
(v/assert kb '(genlCx CxAgentBob CxUniverse) 'CxUniverse); Bob opts in
(v/ask? kb '(believes Bob (green Grass)) 'CxWell)        ; => true
```

## Opacity: the proposition is a mention

An attitude is **opaque**. From *Oedipus believes he married Jocasta* and *Jocasta is his
mother* it does not follow that *Oedipus believes he married his mother* — that is the
whole of the tragedy, and it is what makes a belief different from an ordinary two-place
fact. So `P` in `(believes Agent P)` is a **mention**: a sentence named as syntax, not a
sentence the reader may normalize.

```clojure
(v/assert kb '(marriedTo Oedipus Jocasta) 'CxAgentOedipus)   ; what he believes
(v/assert kb '(sameAs Jocasta MotherOfOedipus) 'CxUniverse)  ; what the ASKER knows

(v/ask? kb '(believes Oedipus (marriedTo Oedipus Jocasta))         'CxUniverse) ; => true
(v/ask? kb '(believes Oedipus (marriedTo Oedipus MotherOfOedipus)) 'CxUniverse) ; => false
```

The merge is real and the asker holds it: asked *outside* the quotation, either spelling
normalizes to the class representative and the two are one question, exactly as
[equality.md](equality.md) describes. Inside it, nothing moves — the merges the asker
believes are not the ones the agent does.

**The agent's own merges do license the substitution**, and license it for that agent
alone. The projection runs the proposition in the agent's context, so it is normalized
there — the ordinary rule that the reader is what elects, applied to the reader a
projection actually has:

```clojure
(v/assert kb '(marriedTo Oedipus Jocasta)      'CxAgentOedipus)
(v/assert kb '(sameAs Jocasta MotherOfOedipus) 'CxAgentOedipus)   ; HE holds the identity
(v/assert kb '(marriedTo Creon Jocasta)        'CxAgentCreon)     ; Creon does not

(v/ask? kb '(believes Oedipus (marriedTo Oedipus MotherOfOedipus)) 'CxUniverse) ; => true
(v/ask? kb '(believes Oedipus (marriedTo Oedipus Jocasta))         'CxUniverse) ; => true
(v/ask? kb '(believes Creon   (marriedTo Creon  MotherOfOedipus))  'CxUniverse) ; => false
```

That is the *de dicto* reading: the substitution goes through exactly when the agent holds
the identity. The *de re* reading — "of his mother, Oedipus believes he married her",
true whoever holds the identity — is a different question and the projector does not
answer it.

### Where the barrier sits, and what it covers

Congruence opacity lives in the one walk both migration and query go through
(`res/representative-term`), not at the read entry point. That is what keeps the two in step: a
merge migrates a stored `(believes A P)` no more than it rewrites the question, so the
belief stays retrievable under the spelling it was asserted in rather than under one only
the merge produces. `res/without-retired` reads the same walk, so a quoted spelling is not
retired for a reader who never renamed it.

Three positions stay **transparent**, and each for a reason:

| Position | Rewritten by the asker's merges | Why |
|---|---|---|
| the agent — `(believes Oedipus …)` | **yes** | the asker refers with it; merge `Oedipus` and `KingOfThebes` and it is one agent under two names |
| a non-sentence argument — `(believes A Foo)` | **yes** | it names a term, not a proposition; the projector declines that shape too |
| an ungranted predicate — `(mutters A (…))` | **yes** | opacity is what the `modal_predicate` marker buys; without it this is an ordinary relation |

**The other sentence-holding forms are transparent, and none of them is a quotation.**
`(ist Ctx S)` routes an assertion into `Ctx` — `S` is asserted, so it is used rather than
named ([contexts.md](contexts.md)). An `exceptWhen` conjunct and an `unknown` are queries
the engine runs on the reader's behalf, and they are normalized at the context that runs
them ([exceptions.md](exceptions.md), [naf.md](naf.md)). In each the engine is the one
doing the believing, so the reader's merges are the right ones and congruence applies.
An attitude is the case where somebody else is.

A **`rewriteOf` spelling rename does** reach into the quotation, exactly as it reaches into
a quoting function's (`Quote`, `Quasiquote`) arguments: it retires a *name*, and both the belief and the question
follow it. A `sameAs` / `equals` identity merge does not. That is the same split
[equality.md](equality.md) opens with — three relations, one closure, and only one of them
is about spelling.

The marker is read **globally** here, where the projection reads it scoped. The two
questions differ: whether a belief *projects* is a policy of the context that granted the
marker, while whether an argument is a quotation is a fact about the sentence — and a
reader-scoped answer to the second would migrate a stored belief for one context while
holding it for another, after which neither could retrieve what the other had renamed.

Opacity here is **congruence** opacity. The oriented equational rewriting that runs after
it (the schematic `equals` of [equational.md](equational.md)) walks argument terms without
reading the marker, so a schematic equation normalizes inside a quoted position as it does
outside one.

NAT reification does not read the marker either. A ground reifiable NAT inside the
proposition reifies to its constant before the congruence walk runs, and the constant is
found through the `natFormula` map under the merges `CxUniverse` holds
([nat.md](nat.md#what-reification-does-not-cover)). With `(sameAs Apple Pomme)` in
`CxUniverse` and `(likes Tom (FruitFn Apple))` in `CxAgentAnn`, `(believes Ann (likes Tom
(FruitFn Pomme)))` is true, although `CxAgentAnn` does not see the merge. A stored `(believes
A P)` holds the constant in place of the application, so a merge `CxUniverse` holds folds
the stored belief as well.

## More than one modal predicate

Which predicates project is a KB property, not a hard-coded set. `believes` ships granted
in `CxUniverse`; `knows`, `desires`, `intends` are the same projection under a different
predicate, and one assertion away:

```clojure
(v/register-modal-predicate kb 'knows)   ; grants (modal_predicate knows) in CxUniverse
;; or scope the grant to one theory:
(v/register-modal-predicate kb 'knows 'CxPsychology)
```

`(modal_predicate P)` is read **scoped from the asking context**, exactly as
`abducible_predicate` is — so it is a *policy of the context that grants it*: one theory
may read `knows` modally while another, seeing the same predicate, does not. An
unregistered predicate is never projected, which is why the table is open but closed by
default.

This scoping is also what governs **nested** belief. `(believes A (believes B P))` proves
`(believes B P)` in `A`'s context, and the inner `believes` projects only if the grant is
visible *there*. An independent `CxAgentA` cannot see the `CxUniverse` grant, so by default the
inner `believes` is an ordinary literal and the nested query is simply false — there is no
recursion to speak of. Give `A` a `genlCx` edge that reaches the grant and the nesting
projects through. That is the whole of the nesting story: a consequence of where the marker
is visible, not a modal-logic schema.

## What is out of scope

It is **query-only**: the caller asserts an agent's beliefs into the agent
context directly, and the projector reads them back — consistent with how `unknown` /
`thereExists` are query-only operators. A belief that happens to match a base forward rule
fires it like any other fact; an independent agent context may then have nowhere to place
the conclusion, which surfaces as a harmless no-placement notice in `violations`, not a
contradiction.

Out of scope: assertion routing (asserting `(believes Alice P)` to store `P` in Alice's
context — a write that lands a *different* sentence elsewhere, for which no
retraction-symmetric form exists), agent-context lifecycle (garbage-collecting or merging
agent contexts), and modal logic proper. This is a projector, not a modal calculus.
