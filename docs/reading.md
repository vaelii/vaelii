# Reading English

- **Covers:** how a document's own words resolve against the KB's vocabulary before a
  model is asked anything, and how the result becomes spanned, scored candidate sentexes.
- **Not here:** the other three propose paths and the vocabulary-inventory guard against
  coined predicates → [llm.md](llm.md); the browser panel that renders and applies a
  candidate batch → [web.md](web.md).
- **Assumes:** sentex, context, candidate, canonical form → [glossary.md](glossary.md).

A pipeline that takes a document and answers with **candidate sentexes** — the
`[sentence context opts]` entries `vaelii.core/edit!` already takes, each carrying the span
of text it came from. It never asserts anything: proposing rather than importing is the
whole design.

Everything lives in `vaelii.impl.llm.text` (the prompt, the resolution, the coverage
report), `vaelii.impl.llm.session/propose-text` (the loop), and `vaelii.impl.llm.score`
(the arithmetic against a hand-written gold set). Like `web` / `serve` / the rest of
`llm`, it is an application over the engine and is not in `vaelii.core`.

## Why it proposes rather than imports

[`vaelii.impl.gloss`'s namespace docstring](../src/vaelii/impl/gloss.clj) states the problem in the
other direction: *the read path is the one with no verifier*. Composing English out of the
KB is dangerous because nothing in the engine can say an English sentence describing
`(genl penguin bird)` is wrong.

Reading has exactly the same hole, pointed the other way. Every check the engine has —
naming invariants, groundness, well-formedness, `argIsa`, disjointness, functionality —
reads the **sentence**. Every one of them passes on a fluent, well-formed translation of a
claim the text never made. `(freed LionA MouseA)` is admissible; so is
`(freed MouseA LionA)`; the text says one of them.

So the deliverable is a candidate generator with a reviewer between it and the store. Four
consequences, and they are the design:

- **Nothing here writes.** No `assert`, no `edit!`, no `ist`. A test greps for them, and
  another runs a document through and asserts the KB is byte-identical afterwards.
- **A candidate carries its span**, so an accepted sentence is auditable back to the
  characters that produced it. That is the whole reason to prefer this over a script that
  pastes facts in.
- **A candidate is `:default`** unless it explicitly claims otherwise. A translated guess
  asserted at `:monotonic` would defeat hand-written defaults with something a parser
  inferred, which is the worst outcome available here.
- **What it could not translate is part of the answer.** A pipeline that silently drops the
  third of a document it did not understand reads as one that understood the document.

## Where the boundary is

Reading English is only half in the engine, and the split is deliberate: the engine owns
what it can *check*, and everything that is a judgement about a document sits outside it.

| in the engine | outside it |
|---|---|
| the critic (`check-edit`) | the segmentation, the prompt, the model turn |
| the vocabulary — the taxonomy, the declarations, `context-up` | which words of a document resolve to which term |
| the provenance side map, open and unread by belief | what an application puts in it |
| the equality partition's `representative` | treating a resolved synonym as a synonym |
| `handle-of`, and with it the canonical form | scoring a reading against a gold set |

Nothing on the left is specific to reading — every one of those is engine machinery the
rest of the KB uses too, which is the test the split is drawn by. Inside the `llm`
package, `session/new-assertions` takes an entry-builder so that *is this already stored*
is asked in one place rather than in two.

## The shape

```clojure
(require '[vaelii.impl.llm.session :as llm]
         '[vaelii.impl.llm.ollama :as ollama])

(llm/propose-text kb {:text     "A lion caught a mouse, but he spared it…"
                      :context  'CxLionMouse        ; never the model's to write
                      :source   :aesop-lion-and-mouse    ; what provenance records
                      :provider (ollama/generation-provider)})
;; => {:status   :ok
;;     :batch    {:add [[(lion Lion1) CxLionMouse
;;                       {:provenance {:source :aesop-lion-and-mouse :segment 0
;;                                     :span [0 82] :confidence 0.9}}] …]
;;                :remove []}
;;     :lines    "[(lion Lion1) CxLionMouse {…}]\n…"   ; the editor's textarea content
;;     :repairs  [{:entry […] :problem {:type :not-ground …} :correction {…}}]
;;     :corrections [{:from (believed person) :to (set/defaultRule …) :why "…"}]
;;     :coverage {:segments 4 :covered 3
;;                :uncovered [{:index 1 :span [83 150] :text "Not long afterwards…"
;;                             :reason "no vocabulary for a hunter's net"}]}
;;     :queue    [{:index 6 :entry […] :flagged? true :confidence 0.3 :segment 1} …]
;;     :segments […] :resolved […] :candidates […]
;;     :coined […] :vocabulary {…} :summary {…} :budget {…} :usage {…}}
```

`:lines` is textarea content, `:batch` is what `apply-proposal!` applies, and the result
map is `propose-edit`'s shape plus the seven fields only a document has — `:repairs`,
`:corrections`, `:coverage`, `:queue`, `:candidates`, `:segments`, `:resolved` — so the
existing browser panel handles it and no second write path exists. Applying stays the separate,
explicit `session/apply-proposal!`.

## Resolution is the problem; parsing is not

A pipeline that coins `has_black_and_white_feathers` for every sentence produces
fragmentation rather than knowledge, and [naming.md](naming.md) says in as many words that
no check will ever refuse it: a unary snake_case functor is a legal type name. This is the
same failure [llm.md](llm.md) measures on the page path, and it is worse here, because a
document supplies a hundred phrases that each *could* become a predicate.

So the document's own words are resolved against the KB's vocabulary **before** a model is
asked anything.

### Generate the spellings; don't enumerate the KB

The obvious design — invert every term the KB has into the words it would be written with —
is the one read here that grows with the knowledge base. So it runs the other way. Each run
of up to five consecutive words produces the symbols a KB term could be spelled as:

```
prepared for winter  ->  preparedForWinter   prepared_for_winter
lions                ->  lions  Lions  lion  Lion
```

and the KB is asked which of them it has. Nothing is filtered by plausibility —
`allThroughThe` is generated and the answer is no, at the cost of one set lookup.

The lookup is **one roster read for the whole document**, deliberately the reverse of
`inventory/unknown-terms`. That function probes the index's O(1) secondary roots first
because it is asked about a *proposal*, where nearly every functor is already known; a
document is the opposite case, where hundreds of generated spellings name nothing, so the
roots would be probed hundreds of times to answer no.

Matching is longest-run-first and non-overlapping, so *prepared for winter* wins over
*winter* and a compound predicate is not shredded into the words its name is made of. A
resolved term is its equality-class `representative`, so a word spelled at a retired name
resolves to the term that name was merged into. That is the boundary split above in one
line: a resolved synonym belongs to the equality partition, not to the reader.

### The card is three relevance tiers

`text/document-inventory` builds `inventory`'s own shape, so `inventory/render` writes it
unchanged. What differs is the seeding, and the order matters because it is where a token
cap cuts:

1. **What the document's words resolved to** — the vocabulary the text demonstrably wants.
2. **What an `argIsa` licenses** for a resolved type, so a document about a mouse is offered
   the relations a mouse can stand in.
3. **Everything else the target context declares**, nearest context first.

Tier 3 exists because a document rarely spells a predicate the way the KB does. *…and so
repay the kindness* does not resolve `repaidKindness`; a reader who cannot see that name
coins a synonym for it, and the claim joins nothing. `text/declared-in` reads the
`unaryPredicate` / `binaryPredicate` / `ternaryPredicate` memberships **scoped to the target
context's cone** — which is the right scope on its merits, since a candidate filed in one
context may reuse exactly the vocabulary that context sees — and orders the cone by how much
each context sees, largest first. So a cap drops `CxCore`'s plumbing before it drops
the story's own predicates.

What tier 3 puts on the card is **names and shapes**. A declaration says a predicate exists
and takes two arguments; it says nothing about what is true of anything.

## The span, and what it buys

`text/segments` cuts the document at a run of `.`/`!`/`?` followed by whitespace or the end.
Crude, and deliberately so: an abbreviation splits a segment in two, which costs a narrower
span and no correctness, where a cleverer splitter would need a model on the *reading* side
of the pipeline, with nothing to check it. A semicolon does not cut — a segment may carry
several claims, and which clause a claim came from is not something the span can honestly
say.

The model is shown the document numbered, and every candidate names the sentence it came
from. That number is the whole of how a span survives the round trip: asking for character
offsets instead would be asking a model to count characters.

What lands in provenance is `{:source :segment :span :confidence}`, merged into the
per-handle map on apply. Belief never reads provenance ([storage.md](storage.md)), which is
what makes this safe: `:confidence` is a **rank**, one of three tiers written as 0.9 / 0.6 /
0.3 so a review queue sorts. It is not a probability, and it cannot become a defeat class
even by accident — there are two strength classes and there will not be a third
([nmtms.md](nmtms.md)).

A candidate naming a sentence that does not exist gets `:segment nil` and no span, rather
than a plausible one.

## Coverage: what it could not translate

```clojure
:coverage {:segments 4 :covered 2
           :uncovered [{:index 1 :span [83 150] :text "Not long afterwards…"
                        :reason "no vocabulary for a hunter's net"}
                       {:index 2 :span [151 237] :text "The mouse heard him…"}]}
```

**Computed, not reported.** The output schema has an `untranslated` array and the model is
told to use it, but a segment is uncovered when no candidate names it — whatever the model
listed. A stated reason is attached where there is one; a segment the model called
untranslatable and then answered anyway is covered, and the claim is dropped.

This is part of the default answer rather than something a caller asks for, which is the
point of it.

## Nothing reaches a reviewer that they cannot apply

The other three propose paths fail a whole batch on one bad entry, and that is right for
them: a selection rewrite is one answer about one selection. A document routinely yields
thirty claims of which two are malformed, and failing all thirty on account of two would
make the pipeline useless. So `session/split-admissible` splits the final pass:

- admissible entries become `:batch`, which is therefore **always applicable** — a test
  asserts `check-edit` on it is empty;
- each rejected entry becomes a `:repair` carrying the checker's own verdict, plus
  `:correction` where [`correct.clj`](../src/vaelii/impl/llm/correct.clj) has a shape to
  store instead.

`:status` is `:invalid` only when the critic was shown entries and refused **all** of
them. A document whose every claim the KB already stores read correctly and proposes an
empty batch — that is `:ok`, because `apply-proposal!` refuses anything but `:ok` and
calling it invalid would block an apply that would rightly do nothing.

One refusal is not about the sentence at all. `(ist Ctx S)` is find-or-create *in `Ctx`*,
so a candidate shaped like one stores somewhere other than the context the caller named,
past a check chain with nothing to say about it — the sentence is well-formed and every
name in it is legal. That is the only way this path's "the context is the caller's"
promise can be broken, so `session/placement-problem` refuses it as `:context-escape`, on
every propose path rather than only this one. A rule *consequent* `ist` is left alone:
that form exists to place derived conclusions, and it is visible in the line a reviewer
reads rather than hidden in where the line goes.

Beside that, `:corrections` reports entries that **passed** the critic and are still the
wrong shape — `(believed person)` states a one-place claim of a type symbol where the KB's
idiom quantifies over its instances. Nothing rejects it and nothing will; `correct.clj` is
the only thing that catches it, and this is the second place it earns its keep.

## The review queue

```clojure
:queue [{:index 6 :entry [(sang_all_summer Lion1) …] :flagged? true :confidence 0.9 :segment 1}
        {:index 2 :entry [(spared Lion1 Mouse1) …]   :flagged? false :confidence 0.3 :segment 0}
        …]
```

Flagged first, then least confident, then document order. A flag is a coined functor or a
shape `correct` would rewrite — both are failures the check chain admits *by design* and
only a person can settle, so they sort to the top whatever the candidate claims about
itself. Confidence breaks the tie, which is all a confidence is for here.

## The score

The deliverable. The four fables in `test/vaelii/world_fables.clj` are modelled formally by
hand *and* written out as prose in the same file, so there is a ground truth to score
against. `world-fables/texts` is the input; the hand-written sentexes are the gold.

### How a candidate is matched

**The gold set is read out of a KB, never transcribed.** A second copy in a scoring fixture
would drift from the one the suite loads, and a score against a stale gold set is worse than
no score. So the gold is a set of handles and a candidate matches when
`vaelii.core/handle-of` finds it under one of them — which means the comparison uses the
engine's **own** canonical form: a rule whose variables are named differently, or whose
antecedents arrive in another order, is the same sentence to `handle-of` and therefore the
same sentence here ([canonicalization.md](canonicalization.md)). Nothing about matching is
the scorer's opinion.

Two filters on what counts as gold:

- **Its own context**, not the cone above it. A story context sees the whole upper ontology
  through `genlCx`, and scoring a reader of one fable against the shipped schema would
  measure a recall it was never asked for.
- **Premises only.** `(repaidKindness MouseA LionA)` is forward-chained, and so are the
  eleven conclusions the shipped biology theory draws about the characters. Asking a reader
  to produce them would score the chaining rather than the reading. A candidate that lands
  on one is `:derivable` — not right, not wrong, **out of precision's denominator**, exactly
  as `propose-page` treats an assertion the KB already stores.

### Two scores, because the names are unrecoverable

A fable introduces its characters by kind — *a lion*, *a mouse* — so `LionA` and `MouseA`
are the modeller's names and no reader of the text could produce them. A strict score reads
near zero on a story whose structure was recovered perfectly, which measures the naming
convention rather than the reading. So both are reported, and the pair is the finding:

- **strict** — the candidate matched as written;
- **aligned** — after renaming the candidate's *introduced* individuals onto the gold's, one
  for one, by the types each is asserted to have.

The alignment is by **type overlap**, greedy in descending overlap, each side used once. A
bijection, so no renaming can collapse two characters into one to score better; overlap
rather than equality, so a candidate that also invented a type for its character is still
recognised as having recovered it. It is deliberately narrow — aligning on the relations a
character stands in would start fitting the candidate set to the gold, and a score that
repairs its own input measures the repair.

### Measured

Two models, and the pair says more than either. `gemma3:27b` first, `num_ctx` 16384,
temperature 0, **one provider turn per fable** — every answer parsed on the first attempt,
so no repair turn was spent. The KB is the shipped starter plus the test-world.

| document | gold | cand | prec | rec | strict prec | strict rec |
|---|---|---|---|---|---|---|
| the ant and the grasshopper |  7 |  9 |  67% |  86% |  22% |  29% |
| the boy who cried wolf      | 11 | 11 |  70% |  64% |  18% |  18% |
| the lion and the mouse      |  6 |  6 |  83% |  83% |   0% |   0% |
| the tortoise and the hare   | 13 |  7 |  86% |  46% |   0% |   0% |
| **all four**                | 37 | 33 |**75%**|**65%**| 12% | 11% |

Coverage was 4/4, 5/5, 4/4 and 4/4 sentences — every sentence of every fable produced at
least one candidate. Of 33 candidates, one was refused by the critic and arrived as a
repair, and two functors were coined (`boy`, `slowerThan`) — both flagged, and both
implicated in a confusion below.

The strict column is the one worth staring at. On two of the four fables it reads **zero**
while the aligned column reads 83% and 86%: not one recovered claim named a character the
way the modeller did. The 86% is that fable's *precision*, not its recall — its aligned
recall is 46%, for the reason below — so this is a statement about naming, not about
completeness. That gap is the measurement, and it is why this file reports two numbers.

Wall clock was 44–59 s per fable on a loaded laptop, of which ~30–35 s was prompt
evaluation of a 3,766–3,903-token request (the document plus the target context's
vocabulary) and 13–25 s was generation of 169–318 tokens. Prefill dominates, and it is
the *card* that is being prefilled — the document itself is under 100 tokens.

Reproducible rather than merely repeated: the same run twice gave the same candidates in
the same order (Ollama's temperature defaults to 0), and adding the fifty-token *no `ist`*
paragraph to the system prompt moved the boy who cried wolf from 13 candidates to 11 — a
reminder that these numbers belong to one prompt and one model, not to the pipeline.

### A small model, and what the card cap buys

`phi4:14b`, `num_ctx` **4096**, the vocabulary card capped at 1,400 tokens
(`:prompt-opts {:max-tokens 1400}`), twelve candidates asked for:

| document | gold | cand | prec | rec | strict prec | strict rec |
|---|---|---|---|---|---|---|
| the ant and the grasshopper |  7 |  9 |  78% | 100% |  33% |  43% |
| the boy who cried wolf      | 11 |  6 | 100% |  36% |  33% |  18% |
| the lion and the mouse      |  6 |  6 |  83% |  83% |   0% |   0% |
| the tortoise and the hare   | 13 |  7 |  86% |  46% |   0% |   0% |
| **all four**                | 37 | 28 |**85%**|**59%**| 18% | 14% |

The trade is the one the shape predicts: **higher precision, lower recall**. It wrote 28
candidates where the larger model wrote 33, and almost everything it wrote landed — the
boy who cried wolf scored 100% precision on six candidates and 36% recall, having simply
not attempted most of the story. It also got the ant and the grasshopper's two-antecedent
join right (`(and (survivesWinter ?x) (suffersInWinter ?y))`) where the larger model
produced a free variable and was refused, which is the whole of that fable's 100% recall.

**It is fifteen times faster**, and that is where the card cap shows up. 2.6–4.0 s per
fable against 44–59 s, of which prompt evaluation is **211–375 ms** against 30–35 s. A
2,410–2,544-token request instead of a 3,766–3,903-token one, and prefill is quadratic
enough in practice that cutting a third off the prompt cut prefill by two orders of
magnitude on this hardware.

### The window is the thing to get right

Asking `phi4:14b` for `num_ctx` 16384 — its native maximum — never returned on a busy
host: the model was resident at 4096, a different window forces an evict-and-reload, and
that reload queued behind other work indefinitely while the *same host* answered a trivial
request at the resident 4096 in **0.38 s**. The lesson is not about this host. It is that a
document turn should be sized to the window a model is already serving, and at 4096 the
full card does not fit: 3,800 tokens of prompt plus 832 reserved for the answer is over
budget, and `selection/budget-problem` refuses it with the numbers rather than letting
Ollama silently drop the front of the request.

So the card cap is not a tuning knob, it is what makes a small window usable — and it is
where the three relevance tiers earn their keep, because a cap cuts from the bottom: the
context's least-targeted vocabulary goes first and the words the document actually
spelled stay.

### The confusion cases

Six, and they are more informative than the rates.

**A second modelling layer in the same context.** `CxTortoiseHare` holds the fable
*and* `world-narrative`'s story-understanding schema — `(goal WinRace)`,
`(event TortoiseFinishes)`, `(brings TortoiseA TortoiseFinishes)` and three more. Those are
premises somebody wrote, so they are gold, and the prose says nothing about goals or events.
Six of that fable's thirteen gold items are therefore unreachable, which is the whole of
why its recall is 46% against a precision of 86%. The gold set is deliberately *everything a
person asserted in the context* — narrowing it to "the fable pass" would need a
hand-maintained list, and a hand-maintained gold set drifts.

**A join written as one condition.** For the lion and the mouse the reader wrote
`(implies (spared ?x ?y) (repaidKindness ?y ?x))`; the gold joins two facts,
`(and (spared ?strong ?weak) (freed ?weak ?strong))`. The claim is nearly right and stores
as a different rule, so it costs one precision and one recall. Same shape on the ant and
the grasshopper, where a two-antecedent join came back with a free variable in the
consequent and was refused outright (`:not-range-restricted`) — the critic catching what
the reading got wrong, which is the repair path doing its job.

**A coined type where a broader one exists.** The boy who cried wolf came back as
`(boy Boy1)` where the gold is `(human BoyA)`. `boy` is a legal type name, nothing rejects
it and nothing ever will — and the coining flag put it at the head of the review queue,
which is exactly the division of labour this design claims. `(sheep Sheep1)` on the same
fable is the other half of that: a character the prose mentions and the modeller did not,
so it is spurious against this gold and would be perfectly good knowledge in a KB that had
not already decided the story was about the boy.

**A rule stated at the wrong strength.** The same fable produced
`(implies (liar ?x) (not (believed ?x)))` where the gold joins two conditions,
`(and (liar ?x) (criesWolf ?x))`. It also wrote the joined version — both, from one
sentence — so the pair costs a precision point for the loose one and gains the recall for
the tight one. What it never produced is the *positive* default it is the exception to,
`(implies (criesWolf ?x) (believed ?x))`: the prose says "a cry is believed by default,
except from a liar", and the reader took the exception and dropped the rule.

**A coined argument to rescue a rule.** The tortoise and the hare produced
`(implies (and (raced ?x ?y) (slowerThan ?x ?y) (persevered ?x) (napped ?y)) (wins ?x ?y))`.
`slowerThan` is not in the KB, and the model reached for it because the prose says *the
slower one wins* and nothing on the card carried that. Coining to say something the text
actually said is the defensible kind, and it is still reported.

**An engine form no reader could write.** The gold for the same fable includes
`(exceptWhen (liar ?var0) (sentexHandle 2204))` — a meta-sentex naming the rule it qualifies
by raw handle. It is bookkeeping, it is unrecoverable from prose, and it is one of the
eleven gold items recall is measured against. [llm.md](llm.md) keeps these off the page
path's prompt for the same reason; here it stays in the gold, because hiding it would be
choosing which parts of the modelling to be scored on.

### What the score does not measure

Three things make this an easier task than reading arbitrary prose, and the number means
nothing without them:

- **The narrative predicates are named after the English the fable uses.** `spared`,
  `napped`, `preparedForWinter` — resolution works here partly because the vocabulary was
  written by somebody who had the same sentences in front of them. On a corpus whose author
  did not name the ontology, tier 1 of the card would be much thinner and tier 3 would be
  doing all the work.
- **Each predicate's `comment` is on the card**, clipped to 100 characters, and the shipped
  comments are written as signatures — which is what makes them useful and also what makes
  this a well-documented vocabulary rather than a typical one.
- **The story fits in one context with one cast.** Coreference across a document is the
  thing that would break first at length, and a four-sentence fable barely tests it.

The score is a floor on the formalism — can a candidate generator hit the shape, reuse the
vocabulary, and carry a span? — not a claim about English.

## Offline by default

`lein test` makes no model call. The whole pipeline runs against the scriptable stub
(`stub/candidates-text`, and the `{:candidates [[sentence segment opts] …]}` shorthand), so
the segmentation, the resolution, the coverage report, the repair split, the queue order,
the provenance stamping and the byte-identical-KB guarantee are all tested with no host and
no socket — and those tests are ordinary members of `:default`.

The scoring tier is the exception and is held out by both gates
([llm.md](llm.md), "The stub is the default"): it carries **`^:llm`**, the one mark `:all`
does not select, so `lein test :llm` runs it and nothing else and `lein gate --all` never
reaches it; and it is gated on `tu/live-llm?`, so the selector alone is not enough to make
the call.

Determinism is a test rather than an aspiration: the same text yields the same candidates,
the same queue, the same coverage and the same resolutions, because a review queue that
reshuffles under a reviewer is a bug.

## Tests

`test/vaelii/llm_text_test.clj` — the offline tier, then the live score.

| | |
|---|---|
| the span is the document's own characters | every segment of every fable satisfies `(= text (subs doc start end))` |
| nothing writes | a source scan for `assert` / `edit!` / `retract` / `ist`, and a run that leaves the sentex, index and term counts identical |
| the batch is applicable | `check-batch` **and** `check-edit` on it are both empty; a refused candidate is a repair carrying its verdict |
| a candidate cannot file itself elsewhere | an `(ist Ctx S)` candidate is refused on every path, the message names both contexts, and a rule consequent's `ist` is left alone |
| `:invalid` means refused, not empty | a document whose every claim is already stored is `:ok` with an empty batch, and applying it is a no-op |
| the right claim in the wrong shape | `(believed person)` passes the critic, is reported as a correction, and is flagged in the queue |
| vocabulary | a document restating a stored claim produces no new term; a coined functor is reported with its arity and role |
| coverage | every silent sentence is named, not only the one the model owned up to — and a sentence read into something already stored still counts as read |
| provenance | an applied candidate's span slices the original document back out |
| the queue | a coined functor leads however confident it claims to be |
| the contract has no fallback | bare s-expressions and a bare JSON array both read as `:unparseable`, because neither carries a segment |
| the scorer | the gold is premises only; an alignment is a bijection; a name the gold uses is never renamed onto another character; a derived conclusion costs a reader nothing; a duplicate buys no second match |
