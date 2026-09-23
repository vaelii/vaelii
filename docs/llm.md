# The LLM that proposes edits

- **Covers:** the four paths a model can propose an edit batch through — whole-KB,
  selection, page and document-scoped — and the deterministic critic every one of them
  answers to before a human applies anything.
- **Not here:** resolving a document's own words against the KB's vocabulary, the span a
  candidate carries, and the score against hand-written fables →
  [reading.md](reading.md); the browser panel that renders a proposal and takes the
  accept click → [web.md](web.md).
- **Assumes:** sentex, context, canonical form, justification →
  [glossary.md](glossary.md).

A pluggable language model that reads a KB through its own tools and answers with a
**proposed edit batch**. It never writes. The batch is the exact shape
`vaelii.core/edit!` takes, which is also the form the browser's textarea editor
already produces — so a proposal lands in the existing editor as a reviewable diff,
adding no write path and no trust boundary.

Everything lives under `vaelii.host.llm.*`. Like `web` / `serve` / `cli`, it is an
application over the engine, not part of it; it is not in `vaelii.core`.

```
protocol.clj   the `Provider` protocol: complete / stream, and the neutral request+response
provider.clj   which backend a turn runs against — lazily resolved, stub by default
stub.clj       the default provider — deterministic, offline, scriptable
anthropic.clj  the Messages API backend, raw HTTP over java.net.http + cheshire
ollama.clj     a local Ollama backend — no credential, sized context, JSON-schema decoding
http.clj       what both HTTP backends do that is not a wire format: the read deadline,
               the not-JSON refusal, the bounded excerpt
tools.clj      read tool schemas generated from vaelii.host.serve/ops
prompt.clj     the whole-KB system prompt, generated from the live KB
selection.clj  the selection-scoped prompt: the reader's lines + only their vocabulary
inventory.clj  the KB's own vocabulary, in the prompt — and the flag for coined vocabulary
page.clj       the page-scoped prompt: a term, its vocabulary, and a free-text instruction
text.clj       the document-scoped prompt: English in, candidates out (docs/reading.md)
session.clj    propose -> validate -> repair -> batch, and the explicit apply
correct.clj    the right claim in the wrong shape, rewritten rather than rejected
verdict.clj    the four axes of one proposed line, lined up by entry — for a reviewer
score.clj      candidates against a hand-written gold set — precision, recall, confusions
oracle.clj     the other direction: the KB's conclusions judged by a model (docs/commonsense.md)
```

## Four paths, one critic

|   | whole-KB (`propose`) | selection-scoped (`propose-edit`) | page-scoped (`propose-page`) | document-scoped (`propose-text`) |
|---|---|---|---|---|
| unit of work | the KB | a set of handles | one term's page | a document |
| the turn is | "record this" | "rewrite these lines" | "flesh this out" | "what does this text claim?" |
| how the model reads | 87 generated tool schemas | the selection + its vocabulary | the page + the KB's vocabulary inventory | the numbered text + the vocabulary its own words resolved to |
| how the model answers | a fenced `edn` block | the editor's `[sentence context]` lines | bare sentences under a JSON schema | sentences + the sentence each came from, under a JSON schema |
| the context is | the model's to write | the model's to write | the **caller's**, never written | the **caller's**, never written |
| needs | a tool-capable model | any model that can complete text | a model that writes s-expressions | a model that writes s-expressions |
| fixed cost | grows with the KB | grows with the selection | the vocabulary, bounded by tokens | the document, plus the target context's vocabulary |
| a rejected entry | fails the batch | fails the batch | fails the batch | becomes a **repair**; the rest still apply |

All four end at the same deterministic critic, the same coining flag, and the same
explicit apply. The splits are about what the model has to be able to do, what the prompt
costs, and — between editing and generating — which failure the path has to guard against.

The fourth is the odd one and has [its own file](reading.md): it is the only path whose
input is not already formal, so it is the only one that can be *wrong about what it was
told* rather than merely inadmissible. Everything specific to that — resolving a
document's words against the KB's vocabulary, the span each candidate carries into
provenance, the coverage report for what it could not translate, and the score against the
hand-written fables — lives there.

There is a fifth thing here that is not a path at all, because it proposes nothing:
`oracle.clj` glosses what the KB **concluded** into English and asks a model whether an
ordinary person would agree. The trust runs the other way — nothing a verdict says can
reach the store, and a disagreement is a line in a report. [commonsense.md](commonsense.md)
is the argument for it and the measurement against `phi4:14b`, control group included.

## The four required ideas

### 1. `serve/ops` is already a tool registry

`vaelii.host.serve/ops` is an allowlisted, EDN-typed map of `vaelii.core` calls — the
surface the daemon and the browser reach a KB through. `tools/schemas` derives the
model's tools from its **read subset** rather than transcribing them: parameter names
and arities come from each `vaelii.core` var's own `:arglists`, descriptions from its
docstring. Of its 101 entries twelve are filed with the writes — ten that store, plus
`:preview`, which stores nothing but holds the process's single writer and advances
the handle counter, and `:clear-caches`, which mutates the process's measurement
state — and two more are held back for reasons of their own: `:export` names no
`vaelii.core` var to read a signature off, and `:kb-diff`'s second side is a directory on
the daemon's **host** rather than a value on the wire (`tools/host-path-ops`), so exposing
it would hand a prompt-injected model a path-recon primitive. The model sees 87. A read
added to `serve/ops` becomes a tool with no edit here; a
signature change is picked up on the next build.

Names are munged to the provider's identifier grammar — `:find-sentexes` becomes
`kb_find_sentexes`, `:ask?` becomes `kb_ask_p` (so it stays distinct from `kb_ask`).
JSON carries no symbols, so a sentence / context / term argument is a **string holding
an EDN s-expression** — `"(dog ?x)"` — read back with `clojure.edn/read-string`, never
`read-string`: EDN has no reader-eval, so model output cannot evaluate code.

An op with several genuinely different shapes (`why-not` takes a handle *or* a
sentence and a context) declares all their parameters, requires only the ones every
shape needs, and dispatches on the longest signature the model's input satisfies.

**An argument the chosen shape does not take is refused rather than dropped**, and that
is `opts/check!`'s rule one level out. The nested shapes are where it bites: `query`
takes `(goal)`, `(goal, context)`, `(goal, context, opts)`, so a call giving goal and
`opts` and no context satisfies the *first* — and passing it on would run the read
facts-only with the depth discarded, which is indistinguishable from a goal no rule can
reach. The refusal names the form the input selected and the shapes the op has, so the
next call supplies the argument in between.

**Writes are excluded structurally.** `tools/write-ops` names every mutating op, and
anything resolving to a `!` var is treated as a write whatever the table says, so
`read-ops` cannot leak one. There is no write tool, and `tools/op-of` does not resolve
a write's name at all.

**And a read's bounds are the daemon's, for the same reason the table is.** `:max-depth`
and `:max-ms` are held under the ceilings `vaelii.host.serve` applies *in the op table*
rather than at its HTTP route, so a tool call naming a bound past one is refused
`:over-ceiling` and comes back as the `{:ok false :error …}` a `tool_result` carries
([operations.md](operations.md)). A model reading a KB through a prompt it did not write
is the caller most likely to name an expensive depth, and a ceiling only the wire had
would be the entry point it found first.

### 2. The KB documents itself, so the prompt is generated from it

A hand-written copy of the ontology in a prompt string rots the moment someone drops a
new `Cx<Name>.txt` into `resources/kb/`. Every section of `prompt/system-prompt` is
read back out of the KB it describes:

| section | read from |
|---|---|
| contexts, and what each sees | `contexts`, `context-up` |
| the type hierarchy | `types`, `genls` |
| predicate documentation | the `(comment <term> "…")` sentexes, via `vaelii.host.core-context/comment-of` |
| argument types | the stored `arg` sentexes |
| disjointness | `disjoint` sentexes, `disjoint-metatypes`, `metatype-members` |
| algebraic metadata | `props`, `inverse-of` |
| scale | `term-count`, `contexts` |

The naming invariants are the one static section, because they are mechanical rules
rather than content.

Every section is sorted and nothing carries a clock or a handle, so the prompt is
byte-identical across turns for an unchanged KB. That makes it a **stable cache
prefix**: `anthropic/provider` marks its last system block as a cache breakpoint, and
the volatile part — the user's request — lives in the message turn after it. The
minimum cacheable prefix on the default model is 512 tokens; a shorter prompt simply
will not cache, with no error. `:max-contexts` / `:max-types` / `:max-predicates`
bound the enumerated sections so a large KB does not push its whole vocabulary into
every request.

### 3. The model proposes; a human applies

The final answer is one fenced `edn` block:

```edn
{:add    [[(dog Muffet) CxWell]
          [(parentOf Tom Ann) CxWell {:strength :monotonic}]]
 :remove [4211]}
```

`session/propose` returns that batch and nothing else happens. Writing is
`session/apply-proposal!` — a separate call, with the `!` that marks it, which refuses
a proposal the critic rejected unless `{:force? true}` overrides. So there is exactly
one place storage is reached, it is not on the model's path, and a test can assert
(and does) that proposing leaves the sentex set untouched.

**Applying is all-or-nothing, and `apply-proposal!` reports the refusal rather than
raising it.** The critic cannot rule the refusal out: `check-batch` grades every add
against the KB **as it stands**, so two adds that are each admissible and jointly are not
both pass and the batch is `:ok`. `edit!` then trips the engine's own check on the second
entry and takes the whole batch back ([api.md](api.md)). The result says so:

```clojure
{:result    nil   ; edit!'s own result — nil when the batch was refused
 :applied   0     ; how many of :add the KB stored: all of them, or zero
 :failed-at 3     ; the index in :add the refusal names (nil ⇒ a :remove was refused)
 :error     {:type :disjoint :message "…" :exception #error{…}}
 :violations […] :contradictions […]}
```

So a refused apply leaves a KB nobody has to repair, and `:failed-at` names the entry to
fix. It is reported rather than raised because a proposal loop wants the status; a caller
that wants the throw back has `:error`'s `:exception`.

### 4. The well-formedness checker is the critic

`assert` throws typed `ex-info`. `session/check-batch` re-runs **the same check
chain, in the same order, for its answer rather than its effect** — nothing is stored,
nothing is indexed, the taxonomy is not touched:

| check | source | rejection `:type` |
|---|---|---|
| naming invariants | `vaelii.impl.naming/problems` | `:naming` |
| groundness | `vaelii.impl.checks/check-ground` | `:not-ground` |
| structural well-formedness | `vaelii.impl.special/wff-problems` | `:not-well-formed` |
| edge stratification | `vaelii.impl.checks/check-edge-stratified` | `:not-stratified` |
| arg / disjointness / functionality | `vaelii.impl.checks/constraint-checks` | `:arg-type` `:disjoint` `:functional` |
| **the entry lands where it says it does** | `session/placement-problem` | `:context-escape` |

Batch shape and unknown removal handles add `:shape` and `:unknown-handle`. Calling
the engine's own predicates rather than reimplementing them is deliberate: a
second copy of disjointness or arg logic would drift, and every one of these
returns or throws a value without writing.

`:context-escape` is the one row the chain cannot supply, because it is not a fact about
the sentence. `(ist Ctx S)` is find-or-create **in `Ctx`**, so an entry
`[(ist CxCriedWolf (dog Sneaky)) CxLionMouse]` is well-formed, legally named,
and stores somewhere other than the context column a reviewer read. `assert` would carry
it out correctly; the reviewer is the one who was misled. It is refused on every path —
on the two that promise the context is the caller's (`propose-page`, `propose-text`) it is
the only way that promise can be broken, and on the two where the model writes contexts a
line whose displayed context contradicts where it lands is still a bad line to show
anyone. A rule consequent `ist` is not this row's: the check chain refuses an `ist` in
any rule position as `:not-well-formed`.

That is a **deterministic** critic rather than a model-judged one, which is what lets
the repair loop terminate on a fact. Post-settle, `apply-proposal!` reports the same
signal from the other side: the `violations` the edit added to the ledger, and the
standing `contradictions`.

## Vocabulary fragmentation, and the two guards against it

This is the failure mode of a model writing knowledge, and it is worth its own section
because **the check chain cannot help and never will**.

Asked to write type-level common sense about a term, every local model that produces
usable s-expressions at all folds the claim into the *predicate name*:

```clojure
(implies (penguin ?x) (lives_in_antarctica ?x))
(implies (penguin ?x) (capable_of_swimming ?x))
(implies (penguin ?x) (has_black_and_white_feathers ?x))
(implies (penguin ?x) (thermoregulates_via_blubber_and_feathers ?x))
```

Every one is admissible, novel, and useless. A predicate invented for one sentence can
never join a rule or match another sentence; `(livesIn ?x Antarctica)` is the same claim in
vocabulary the engine can reason with. Swapping models does not fix it — the strongest
model produces the *most* of it, because it produces the most output.

**Naming catches only the misspelled case.** `(lives_in ?x cold_place)` is a snake_case
functor at arity 2 and is rejected, and `(livesInAntarctica ?x)` is camelCase at arity 1
and is rejected too — the arity biconditional catches a name spelled at the wrong arity,
in either direction. `(has_black_and_white_feathers ?x)` is snake_case *and* unary, so it
breaks nothing, and is accepted — correctly, and permanently. A model that learns the
spelling rule writes fragmenting predicates that are perfectly well-formed. Groundness, well-formedness, arg, disjointness and functionality have
nothing to say about it either. A three-line fragmentation case scores 3/3 admissible and
3/3 applied.

So there are exactly two guards, both in `vaelii.host.llm.inventory`.

### Guard 1: the vocabulary inventory in the prompt (prevention)

The KB already knows every predicate it has and what shape each one is, so the prompt
carries it: `inventory/inventory` builds it and `render` writes it as **three blocks**.

- **The domain relations to reuse**, each as a signature —
  `locatedIn/2 : physical_object × physical_object [transitive]` — plus its `comment`. The
  signature is the part that does the work: a model that can see there is somewhere to
  put `Antarctica` puts it there instead of spelling it into a name.
- **The type names**, each with its nearest supertype (`penguin < bird`), so the block *is*
  the hierarchy.
- **A small structural set** — `genl`, `disjoint`, `comment`, `arg` — how a claim about a
  kind is stated. An allowlist, not the whole head: offering a model asked about penguins
  `quantityGreaterThanOrEqual` and `termOfUnit` is irrelevant at best and an invitation to
  misuse something it half-recognizes at worst. A term the vocabulary head documents is
  structural and is kept out of the domain block.

Two things about where it comes from, both measured and both counter-intuitive:

- **Sourced from declarations, not facts.** Enumerating functors that actually appear in
  fact position on the shipped schema yields 20 names, every one an engine
  meta-predicate (`genl`, `arg`, `comment`, `disjoint`, …) and not one a domain relation.
  The schema is schema-only: `bird`, `parentOf` and `flies` appear only as *arguments* of
  declarations and inside rules. So types come from `types` and relations from the
  `unary_predicate` / `binary_predicate` / `ternary_predicate` memberships, which covers 142
  domain relations — and `arg` then supplies argument *types* for 119 of the 120 a page
  renders.
- **Arity is never inferred from `arg`.** `arg` constrains an argument to a *type* and
  is deliberately partial: `hasCapability/2` and `result/2` each constrain only their
  first argument, and `interArg/5` constrains one position of five. Its highest declared
  position disagrees with the declared arity for 7 of the 164 predicates it constrains, so
  an inventory built that way would print `interArg/1` and *cause* the arity errors it
  exists to prevent. Arity comes from the declarations, else from the predicate's own
  facts, else it is not printed. The fallback reads at most 64 of them and answers the
  arity most of them carry, a tie going to the smaller — a functor root is a *set*, so
  the first row it enumerates is the order the facts arrived in, and a count is the
  reading that does not move with it ([defenses.md](defenses.md)).

The card is bounded, not complete. An inventory renders 204 terms — 120 relations, 80 type
names and the four structural ones — and `:dropped` counts all three of its cuts, because a
card that cuts silently is indistinguishable from the whole vocabulary. Both count bounds are stated as a
number left out (`:relations` 22 here, `:types` 1), and `:unscanned` is the third: the stored
**facts** `:max-scan` never read, which the relation block states as *"this card did not
read N further facts about this term; a relation used only there is not listed above."*
That cut is the one that loses rather than demotes. A predicate the KB has *declared* is
offered under a later tier whether or not the scan reached it, but a predicate used with
the term and never declared and never `arg`'d is on the card because the scan found it,
and nothing else looks for it.

Both blocks are vocabulary-sized rather than term-sized, so what differs between two pages
is the order and not the size. With signatures and clipped documentation that is about
8,900 tokens uncapped, against the 4,800 a whole page prompt measures (below) — so on the
shipped schema the **token** cap is the one that does the cutting. There is no retrieval
path and no top-K: relevance ordering (the page term's neighbourhood first, then everything
else declared) exists so that the **token cap cuts the least useful first**.

Measured effect, same model and same instruction, with
`:prompt-opts {:max-relations 0 :max-types 0}` as the control:

| page | | literals reusing KB vocabulary | coined |
|---|---|---|---|
| `penguin` | no inventory | 25 / 48 | 23 — `canTreadOn`, `canWalkOnLand`, `hasStreamlinedBody`, `wingsAre` |
| `penguin` | with inventory | 33 / 47 | 14, every one a relation carrying real arguments |
| `dog` | no inventory | 23 / 46 | 23 |
| `dog` | with inventory | **14 / 14** | **0** |

Prevention is real but partial. On a `bird` page the same model still coined `canFly`,
`hasFeathers`, `isWarmBlooded` and `laysEggs` with `flies` and `mortal` sitting on the card
in front of it. That is precisely why the second guard is not optional.

### Guard 2: the coining flag (detection)

`session/coined` (→ `inventory/coined`) reports every functor in a proposal the KB has
never seen, and rides on every proposal result beside `:rejections`:

```clojure
:coined     [{:predicate lives_in_ice :arity 1 :role :type      :in :add :index 0}
             {:predicate capableOf    :arity 2 :role :predicate :in :add :index 1}]
:vocabulary {:literals 4 :reused 2 :coined 2 :coined-types 1 :coined-relations 1}
```

- **`:arity` and `:role` are the reviewer's first question.** "You invented a new one-place
  property" and "you invented a new relation" are different judgements, and
  `capable_of_swimming` versus `capableOf ?x Swimming` differ in exactly that.
- **`:vocabulary` counts the proposal**, so a reviewer knows before reading a line whether
  it is conservative (all reuse) or inventive (mostly new names).
- **It reports; it never rejects.** Coining a type is how an ontology grows. What is not
  acceptable is coining one *invisibly*.
- The frame (`implies`, `and`, `or`, `not`, `exceptWhen`, `ist`, a `set/*Rule` wrapper) is
  never counted as vocabulary, and a namespaced functor never is either. `:remove` entries cannot
  coin.

"Never seen" is read from what is **stored**: the O(1) secondary roots answer first (a
declared-but-unused predicate still sits at argument 1 of its own declaration), and only
what they cannot resolve falls through to the term roster, read once for the whole
candidate set. So a proposal that reuses vocabulary throughout costs a handful of set-size
reads.

**A known gap, in naming rather than here.** A model asked for a relation's second
argument writes `Baby_Penguin`, `South_Pole`, `Cold_Tolerant` — CapitalCamel with an
underscore, which matches *no* naming role, and naming checks the functor rather than the
arguments, so nothing rejects it. The coining flag is scoped to functors and does not
report it either.

## The loop, and how it terminates

```
propose ──▶ provider turn
              │
              ├─ refusal?       ──▶ :refused        (checked before :content is read)
              ├─ truncated?     ──▶ :truncated      (the host stopped at the token limit)
              ├─ tool_use?      ──▶ run reads, feed results back, next turn
              └─ final text     ──▶ parse batch
                                     ├─ unparseable ──▶ feed the parse error back
                                     └─ check-batch
                                          ├─ clean   ──▶ :ok
                                          └─ rejected ─▶ feed the typed rejections back
```

**Two stop reasons are read before the content, not after.** A refusal is the well-known
one; `max_tokens` is the other, and what it costs depends on how the path reads an answer.
Where the answer is **diffed or carries a `:remove`** (`propose`, `propose-edit`), absence
means intent — on the selection path every line the model never reached comes back as a
proposed retraction — so a cut-off turn is `:status :truncated` and carries no batch, lines
or summary at all. Where the answer is **additive** (`propose-page`, `propose-text`), what
did arrive stands, so the turn keeps its batch and carries `:answer-truncated? true` beside
it: a status there would make `apply-proposal!` refuse a partial generation that is
perfectly applicable. The check runs ahead of the tool-use arm too, since a tool call cut in
half is an argument map nobody finished writing.

Two independent bounds, both reported rather than thrown, and each defaulted per path:

- **`:max-repairs`** caps how many rejected or unparseable batches are fed back — 2 on
  `propose` and `propose-edit`, 1 on `propose-page` and `propose-text`, where an additive
  answer's good entries survive a rejection and a second round costs a whole generation.
  Running out yields `:invalid` (with the batch *and* the rejections, so a human can
  still review it) or `:unparseable`.
- **`:max-turns`** caps total provider turns, tool calls included, so a model that only
  ever calls tools ends in `:exhausted` instead of spinning. 24 on `propose`, the one
  path that spends turns reading; 6 on `propose-edit`, 4 on the two generating paths.

A repair turn hands back the checker's verdict verbatim — entry, `:type`, message —
and tells the model to drop an entry it cannot make well-formed rather than guess.

Every read of a model's output catches **`Throwable`**, not `Exception`: a deeply nested
form overflows the reader's stack, and an unreadable answer is the ordinary outcome these
arms exist to report rather than one that should leave the loop. A parse failure is named
by its exception class where the failure carries no message, since a `StackOverflowError`
carries none and a nil marker is indistinguishable from an empty batch — a crash that looks like a model
proposing nothing.

`:status` is one of `:ok`, `:invalid`, `:unparseable`, `:refused`, `:truncated`,
`:exhausted`.

## What an application calls

```clojure
(require '[vaelii.host.llm.session :as llm]
         '[vaelii.host.llm.anthropic :as anthropic])

(llm/propose kb {:message  "Muffet is a dog and Ann is his owner"
                 :provider (anthropic/provider)          ; omit for the offline stub
                 :on-event (fn [ev] …)})                 ; omit for non-streaming
;; => {:status :ok
;;     :batch  {:add [[(dog Muffet) CxWell] …] :remove []}
;;     :edn    "{:add [[(dog Muffet) CxWell]] :remove []}"
;;     :rejections [] :text "…" :attempts 1 :turns 2 :tool-calls 1
;;     :messages [ … the conversation, for a follow-up turn … ]}

(llm/apply-proposal! kb proposal)
;; => {:result {:added […] :removed {…}} :applied 2 :failed-at nil
;;     :violations […] :contradictions […]}      ; :error too, when one threw
```

`:edn` is the batch ready to drop into the editor. Passing `:on-event` switches the
provider to its streaming path and hands every event — `:block-start`, `:text-delta`,
`:block-stop`, `:done` — to the callback, which is what an SSE endpoint consumes.

Other options: `:system` (override the generated prompt), `:prompt-opts`,
`:tool-opts` (`:only` / `:exclude` a set of ops), `:model`, `:max-tokens`, `:effort`,
`:thinking-display`.

`kb` is an **in-process** KB, not an `vaelii.browser.access` handle: the critic calls the
engine's check predicates directly, and those read the taxonomy and the index rather
than going over a wire. The browser's attach-to-daemon mode would need the loop to run
on the daemon side (where the KB is) and only the proposal to cross the wire.

## Editing a selection

The reader selects sentexes on a page and says what to do with them. That is the unit
of work — not the knowledge base — and it is what makes a local model usable and what
keeps the prompt bounded as the KB grows.

### Why the whole-KB path does not fit a small local model

Measured against the **schema-only starter** (no individuals, no facts): the generated
system prompt is 32,020 characters and the 87 tool schemas another 53,557 as sent — about
**24,000 tokens before the user has said anything**, at `selection/chars-per-token`. On a
16,384-token model that is the whole window and past it, spent on a KB with nothing in it
but its schema, and the real target is millions of sentexes. Both figures grow with the
read surface: the schemas are generated from `serve/ops`, so a read added there is another
six hundred characters in every whole-KB request.

Worse, it is unusable rather than merely expensive on the model this was built for.
`phi4:14b` declares `capabilities: ["completion"]` — no `tools` — so its chat template
has no tools section and it cannot emit a tool call at all.

### What the prompt is instead

`selection/user-turn` builds three things:

1. **The selected lines**, in the editor's own format — `[sentence context]`, or
   `[sentence context {:strength :monotonic}]` for known-true content, with a rule's
   direction and defeasibility spelled back as `set/*Rule` wrappers. The same lines the
   textarea is seeded with, so the reader reviews a diff in the format they were
   already reading.
2. **A vocabulary card computed only from terms the selection mentions.** Each
   predicate or type gets its `arg` constraints, its supertypes, its
   **sub-predicates**, its disjointness, its algebraic metadata and its `comment`; each
   individual its types; each context what it sees. Every read is pinned by a term the
   selection contains — a `comment-of` query, an `arg` query on a fixed predicate, a
   cached genl closure lookup — so the card is **O(selection)** and flat in KB size. A
   test asserts exactly that: add a hundred unrelated sentexes and the card is
   byte-identical.
3. **The reader's instruction**, last, so it is the newest thing in the window.

Sub-predicates are the part that decides it of the card. "State this more specifically" is
unanswerable unless `fatherOf` is visible under `parentOf`.

The system prompt closes with a **worked example** — two selected lines and an
instruction, answered with one line rewritten, one kept, and one invented. It is there
because a small model is good at transforming lines it can see and weak at coining new
ones in a formalism it has only been *told* about: asked to record something new,
`phi4:14b` answers in English prose unless the target shape has been demonstrated. About a
hundred and twenty tokens buys that.

### The contract is the editor's line format

The model answers with one `[sentence context]` (or `[sentence context opts]`) per line
— exactly what `/edit` seeds its textarea with and what the editor already parses. So
the round trip through the editor is the **identity**, there is no envelope to
negotiate, and it works on every model.

Ollama's `format` parameter (a JSON schema constraining the sampler) is **not the
contract**, because it is not portable. Measured on this task:

| model | `format` | on the edit task |
|---|---|---|
| `phi4:14b` | honoured | clean |
| `qwen2.5-coder:32b` | honoured | clean |
| `qwen3.6:27b` | **ignored** | answered in the line format anyway, correctly |
| `nemotron-3-nano:30b` | **ignored** | — |

`qwen3.6:27b` even wrapped its JSON in a markdown fence *while* decoding under a schema
that has no way to express one. So `selection/output-schema` is opt-in
(`propose-edit`'s `:format`) for a model it demonstrably helps, and `parse-lines` is
defensive regardless: it strips a markdown fence, reads a JSON envelope if one arrives,
and otherwise reads the lines.

The line format also wins on merit. Same selections, one local model — `phi4:14b`, the
default and the one the timings below are on — JSON envelope versus lines:

| | JSON envelope | lines |
|---|---|---|
| 3-line rewrite | ~1.7 s, 132 output tokens | **~0.5 s, 31** |
| 60 lines, "change nothing" | ~21 s, **12 lines silently dropped** | **~13 s, 60/60 kept** |

Parsing is deliberately asymmetric about failure. Prose is not an entry — it comes back
as `:notes`, the only commentary channel this format has. But a line that **starts like
an entry and is not one** is an error rather than a silent drop, and an answer with no
entries at all is an error however much prose came with it: dropping a line is a
retraction, so nothing is discarded quietly. `clojure.edn/read-string` does the reading,
never `read-string`, so model output cannot evaluate code.

`opts` rides across a rewrite — a known-true fact silently downgraded to a defeasible
default is a real loss the critic cannot see — and is not part of the diff key, so
restating a line's strength is not counted as a rewrite.

### The answer is a line set; the batch is a diff

The model returns the **complete edited set of lines**. `session/diff-batch` diffs it
against the selection **by content** — exactly what the browser's editor does on Save:

- a line returned unchanged is in both sets, and touches nothing (no handle churn),
- a line rewritten retracts the old handle and asserts the new content,
- a line dropped retracts,
- a line invented asserts.

`session/edit-summary` reports `{:selected :returned :unchanged :removed :added}`
alongside the batch, because **a dropped line is a retraction**: a model deleting a line
it was told to leave alone produces a well-formed batch the critic has no reason to
reject, so the count is surfaced rather than left for a reviewer to notice.

### An oversized selection fails; it never truncates

Ollama silently truncates a prompt longer than `num_ctx`, which would answer about part
of the reader's selection while appearing to answer about all of it — the one failure a
reviewer cannot see. So the request is sized first (`selection/budget`) and refused
before anything is sent:

```
:status :too-large
:text   "the selection does not fit the model's context window: 60 sentexes need about
         6463 tokens (3327 of prompt plus 3136 reserved for the answer) against a
         window of 1024. Select fewer sentexes, or raise :num-ctx."
```

The budget reserves output room too — one line back per line in, plus slack — because a
prompt that fits with no room to answer does not fit. Token counts are estimated at 3.5
characters each, deliberately low so the estimate runs **over**; measured against
Ollama's own `prompt_eval_count` it over-estimates by 6–14% (the table below), which is
the safe direction.
Every response carries the measured count back in `:usage`.

The check runs again **before every repair turn**, because a repair carries the whole
conversation back and the first turn fitting says nothing about the third.

### What it costs, measured

Against the starter KB on `phi4:14b`, `num_ctx` 8192. `prompt_eval_count` is the host's
own count, not an estimate:

| selection | est. prompt | measured prompt | output | wall clock |
|---|---|---|---|---|
| 3 facts | 836 | 736 | 31 | ~0.5 s |
| 5 | 1,241 | 1,145 | 102 | ~5 s |
| 20 | 2,115 | 1,965 | 354 | ~5 s |
| 60 | 3,519 | 3,310 | 964 | ~13 s |

A 60-sentex selection leaves ~1,500 tokens of headroom at 8192, so that is the default:
well under phi4's native 16,384, small enough that prefill is cheap and an oversized
selection surfaces as a refusal rather than a truncation, and large enough for a
selection bigger than anyone drags out by hand.

For contrast, the same three-fact edit on the whole-KB path would start at ~24,000 tokens
of fixed overhead — about seven times the whole 60-sentex selection-scoped request, on
a KB with no facts in it.

### What `phi4:14b` is and is not good at

It is the default, and it is very good at the case this path is for: **transforming
lines it can see**. Told that three selected facts are about male parents, it rewrote
the two `parentOf` lines to `fatherOf`, left the unrelated `(dog Muffet)` alone, and did
it in under half a second. Told to change nothing across 60 lines, it returned all 60
unaltered.

It is measurably weaker at **coining content about vocabulary the selection does not
contain**. Asked to record that Ann is a veterinarian who treats Muffet, it produced
`(veterinarian Ann)` and `(professional Ann)` correctly but wrote `(treats_ann Muffet)` —
folding a binary predicate's first argument into its name. That entry is *well-formed*:
`treats_ann` is a legal predicate name and the result is a legal unary fact, so the critic
has no grounds to reject it and a reviewer is the only thing that catches it. The
vocabulary card cannot help, either, because `treats` was not in the selection and so
was not on it. Without the worked example the same request comes back as English prose,
so the example is doing real work — it just does not reach all the way to arity.

`ollama/default-model`'s docstring names the alternatives with their measured latencies:
`qwen3.6:27b` for better judgement at roughly 12 s a turn, `qwen2.5-coder:32b` for the
most formal reliability at roughly 20 s. Both are per-call `:model` overrides.

### What a browser panel calls

```clojure
(require '[vaelii.host.llm.session :as llm]
         '[vaelii.host.llm.provider :as provider])

(llm/propose-edit kb {:handles  [4211 4212 4213]      ; the drag-selected handles
                      :message  "these are all male parents, be specific"
                      :provider (provider/provider :ollama)
                      :num-ctx  8192})
;; => {:status  :ok
;;     :lines   "[(fatherOf Tom Ann) CxWell]\n[(dog Muffet) CxWell]"
;;     :batch   {:add [[(fatherOf Tom Ann) CxWell]] :remove [4211]}
;;     :edn     "{:add [...] :remove [4211]}"
;;     :summary {:selected 3 :returned 3 :unchanged 2 :removed 1 :added 1}
;;     :coined     []                     ; vocabulary the proposal invents
;;     :vocabulary {:literals 4 :reused 4 :coined 0 :coined-types 0 :coined-relations 0}
;;     :notes   "replaced parentOf with fatherOf for Tom, who is male"
;;     :budget  {:prompt 656 :reserved 400 :total 1056 :num-ctx 8192 :headroom 7136}
;;     :usage   {:input-tokens 580 :output-tokens 132 :eval-ms 1548 …}
;;     :elapsed-ms 1676 :rejections [] :attempts 1 :turns 1
;;     :selection [{:handle 4211 :line "[(parentOf Tom Ann) CxWell]"} …]}
```

**`:lines` is the whole wiring.** It is the textarea content the editor already
understands, so the panel drops it into the open editor and the reader reviews it and
hits Save — which goes through the existing `/edit` POST, the existing content diff, and
the existing single settle. The LLM adds no write path: it rewrites a textarea.

`:status` is `:ok`, `:invalid`, `:unparseable`, `:refused`, `:exhausted`, `:truncated`
(the host stopped at the token limit — no batch, because a prefix diffed against the
selection is a set of retractions nobody asked for), `:too-large` (with the numbers,
nothing sent) or `:empty-selection` (no handle still names a stored sentex). Applying stays
the separate explicit `apply-proposal!`.

## Fleshing out a page

The reader is looking at `/term?q=penguin` and types something open-ended — *"flesh out the
capabilities of this"*. That is not an edit of anything: there is no selection, and the
answer is knowledge the KB does not have yet. `session/propose-page` is that turn.

```clojure
(require '[vaelii.host.llm.session :as llm]
         '[vaelii.host.llm.ollama :as ollama])

(ollama/warm)                                    ; when the page opens

(llm/propose-page kb {:term     'penguin
                      :context  'CxOrganism          ; optional — see below
                      :message  "flesh out the capabilities of this"
                      :provider (ollama/generation-provider)
                      :on-event (fn [ev] …)})             ; optional, per assertion
;; => {:status  :ok
;;     :batch   {:add [[(implies (penguin ?x) (livesIn ?x Antarctica)) CxOrganism] …]
;;               :remove []}
;;     :lines   "[(implies (penguin ?x) (livesIn ?x Antarctica)) CxOrganism]\n…"
;;     :summary {:proposed 24 :new 22 :known 2 :duplicate 0 :monotonic 0}
;;     :coined     [{:predicate livesIn :arity 2 :role :predicate :in :add :index 3} …]
;;     :vocabulary {:literals 47 :reused 37 :coined 10 :coined-types 0 :coined-relations 10}
;;     :term penguin :context CxOrganism
;;     :page [{:handle 12 :line "(genl penguin bird)"} …]
;;     :page-found 6 :page-truncated? false :answer-truncated? false
;;     :first-assertion-ms 470 :elapsed-ms 3590
;;     :rejections [] :problems [] :notes nil :attempts 1 :turns 1
;;     :budget {…} :usage {…} :messages […]}
```

The result shape is `propose-edit`'s, so **one panel handles both**: `:lines` is textarea
content, `:batch` is what `apply-proposal!` applies, `:rejections` and `:coined` are what a
reviewer reads. Generation never removes, so `:remove` is always empty and `:summary`
counts what is new instead of what was diffed. `:status` adds `:no-term` — a page turn
asked for something that is not a term symbol, reported with nothing sent — and drops
`:truncated`, which on an additive path is the `:answer-truncated?` flag beside a batch
that is short rather than wrong. `:page-found` and `:page-truncated?` say whether `:page`
is the whole of what is stored about the term or a sample of it.

### Three things the page path does differently

**The context is the caller's.** A page is already about one context, so the model writes
**bare sentences** and the caller supplies the context — one whole class of answer the
model cannot get wrong, and a shorter line every time. Without `:context`, the default is
the context most of the term's own sentexes are in, ties broken by name; the vocabulary
head is never chosen, because a term carries derived bookkeeping there (`(arity penguin 1)`,
`(unary_predicate penguin)`) that can outnumber its definitions. The choice comes back as
`:context`, since where knowledge lands is a decision a reviewer must see.

**Decoding is constrained, and that is the contract here.** `page/output-schema` is sent as
Ollama's `format` by default. This is the opposite of the edit path, and both are measured:
on generation the schema *rescues* models that otherwise answer with a markdown essay (the
strongest coder model went from nothing usable to a full answer), while on the edit path
the same parameter silently drops lines. The two contracts are deliberately different and
are not unified. `session/parse-assertions` stays defensive regardless — it strips a fence,
reads the envelope, and falls back to bare lines.

**What it asks for is type-level.** Common sense about a *kind* is a `genl` edge or a rule,
not a fact about an individual, so the prompt states the three shapes and shows a worked
example of the failure beside its fix. Two lines earn their tokens by removing a whole
repair round each: *`?x` is the only variable you may use* (a model handed `parentOf` on the
card writes `(implies (penguin ?x) (parentOf ?x ?y))`, which the range-restriction check
rejects) and *a card predicate under a new name is still a coined predicate*.

### The page shows what the page shows — minus the bookkeeping

`page/stored-lines` renders the term's own sentexes as bare sentences, **sorted by content
before `:max-lines` (40) cuts**, over a walk bounded separately by `:max-scan` (4,000
mentions). The two bounds mean different things and the split is the whole of it:

- **Below the scan bound the page is a function of the knowledge alone** — the same
  sentences loaded in any order give the same 40 lines, because the sort spans everything
  the cut chooses between.
- **At the bound it is a sample of the term's earliest mentions.** No bounded scan can make
  that cut content-keyed: ranking sentences by content means fetching all of them, which is
  the cost `:max-scan` exists to refuse. What it *can* be is nameable and stable, so the
  handles are sorted before they are fetched — the term index answers with a set, and a
  scan that took whatever it enumerated first would sample by hash of handle, differently
  per backend.

Either way the answer says which it is: the heading over the block reads `40`, `40 of 137`,
or `40 of more than 137` where the scan bound bit, and `propose-page` lifts the same two
out as `:page-found` and `:page-truncated?` so the reviewer reading those 40 lines is told
what the model was told. The prompt asks the model not to repeat anything already stored,
and that instruction is only defensible if a sample says it is one.

Two things are deliberately not sent:

- an `exceptWhen` **meta-sentex**, which names the rule it qualifies by raw handle
  (`(exceptWhen (penguin ?var0) (sentexHandle 463))`) — meaningless to a model, unusable,
  and worst of all *imitable*;
- the **canonical variable numbering**: rules go out originalized, `?x` rather than `?var0`,
  which is the idiom the model was trained on and stops `?var0` coming back as if it were a
  variable name.

### Streaming, per assertion

The page turn always streams. `session/scan` is an incremental s-expression scanner fed the
text deltas: the moment a closing paren balances, the sentence is read, checked, and handed
to `:on-event` as

```clojure
{:type :assertion :index 0 :sentence (genl penguin aquatic_bird)
 :entry [(genl penguin aquatic_bird) CxOrganism]
 :problem nil          ; the critic's verdict on this one line
 :stored? false}       ; already in the KB, so not news
```

so a panel fills in as the model writes. The scanner is shape-blind — it counts parentheses
and skips escapes — so it reads sentences out of the JSON envelope (where each is a string
value) and out of a bare-line answer with the same code. The finished text is parsed
normally afterwards, so the scanner can only ever cost a progress event, never correctness.
`:first-assertion-ms` reports what the reader actually waited for.

### Latency: one request, and a warm model

One run against a starter-loaded KB, `qwen3-coder:30b` on a LAN Ollama, `num_ctx` 8192,
24 assertions asked for. Timings are that host and that model, not a guarantee — what is
stable is the *shape*: prompt construction is negligible, model residency dominates, and
one warm turn lands inside the budget. A term page's prompt on the shipped starter
measures around 4,800 tokens, and `propose-page` reports its own `:budget` per call rather
than relying on a figure written here.

| | |
|---|---|
| prompt built (KB reads, the whole inventory) | 5–15 ms |
| prefill | 22–32 ms |
| **time to first assertion** | **0.38–0.50 s** |
| generation, to the last assertion | 2.6–3.7 s |
| **total, one turn** | **2.8–3.9 s** |
| a turn that needed one repair | ~7 s |

**One request, not several.** The cost is model *load*, not generation: three identical
calls measured ~11 s, then ~0.4 s, then ~0.3 s. So the fix is residency, not splitting —
every request sends `keep_alive` (30 minutes by default) and `ollama/warm` pays the
one-off cost up front. Warming matters more than it looks: with the weights already
resident, the first *generating* turn still took several seconds to its first assertion
while every turn after it took ~0.4 s, so `warm` sends a realistically-sized prefill and
generates one token, which moves that wait out of the reader's way. Splitting the request
would multiply the fixed costs and buy nothing, since a single warm turn already lands
well inside the 5 s budget.

**Editing and generating want different models**, so the two paths default differently:
`phi4:14b` for `propose-edit` (correct and fastest, under two seconds) and
`qwen3-coder:30b` for `propose-page` (20/20 admissible on the flesh-out task, about as
fast warm). `phi4:14b` produced nothing usable for generation under either output
contract, and the generation model is
reached through `ollama/generation-provider` so the pairing has a name.
`provider/generation-provider` is the backend-agnostic spelling of that: it builds a
backend's generation constructor where it has one and its ordinary one where it does not,
so a caller picks the *job* rather than the vendor.

### Where the page path is wired

The browser's term page carries it: `POST /propose` runs one turn and renders the lines
it proposed, and `-main` calls `provider/warm` on a daemon thread at start so the first
reader's question is not the one that pays for loading the weights. Every turn the panel
sends carries a **token cap** — the runaway guard, since two of eight models measured go
runaway and a wall-clock timeout does not stop a host that is still generating. The cap
is sized per backend: a writing budget for a local turn, and the API default for a turn
that reasons against the same ceiling first.

The panel is where the **explicit apply** actually happens. Each line comes back with the
shapes `correct` would accept, numbered, the rewrite leading; the reader picks one (which
re-derives it from `apply-correction` and re-checks it), accepts what they want, and the
accepted set goes through `vaelii.core/edit!` in one settle. So `apply-proposal!`'s
contract holds all the way to the screen: a model's output reaches storage only where a
person put it there, one line at a time. See [docs/web.md](web.md), "Proposing knowledge".

## Providers

### Choosing one

`vaelii.host.llm.provider` stands where `vaelii.impl.asp.solver` stands: a keyword names
a backend, the backend is **lazily resolved** so choosing one is what loads it, and an
unreachable backend falls back to the stub rather than throwing.

```clojure
(provider/provider)             ; the configured backend, or the stub
(provider/provider :ollama)     ; demand one — still falls back
(provider/available? :ollama)   ; ask first if you must know
(provider/active-kind)          ; what (provider) will hand back right now
```

`:stub` · `:ollama` · `:anthropic`, selected with `VAELII_LLM_PROVIDER` or
`-Dvaelii.llm.provider`, default `:stub`. Laziness matters beyond load time:
`anthropic/available?` may shell out to the `ant` CLI and `ollama/available?` opens a
socket, and neither should happen because a namespace was required.

### The stub is the default

`vaelii.host.llm.stub/provider` stands where `vaelii.impl.solve/local-solver` stands:
the deterministic default that makes the LLM provider usable before, and without, a real
backend. `lein test` runs the whole pipeline against it — no API key, no socket, **no
model call** — and a deployment with no credential degrades to a provider that proposes
nothing rather than to an exception.

That is the whole suite, not most of it. The six live tests — three in
`llm_selection_test`, one in `llm_page_test`, one in `llm_text_test`, one in
`llm_oracle_test` — are held out by **two independent gates**, and neither is much use
without the other:

| | what it decides | how to move it |
|---|---|---|
| **`^:llm`** | which tests *run* — the one mark `:all` does not select | `lein test :llm` runs exactly those and nothing else |
| **`tu/live-llm?`** | whether a call may be *made* | `VAELII_LLM_LIVE=1` |

So `lein test :llm` without the variable prints a skip per test rather than dialling out:
a selector is a request, consent is a separate thing, and a reachable Ollama on the
machine is not consent. A test whose assertions depend on what a model happened to say is
neither hermetic nor reproducible, which is why an ordinary run — and `lein gate`, and
`lein gate --all` — never reaches one.

`llm_test/a-test-that-can-reach-a-model-carries-the-llm-mark` scans the test sources and
holds the two in agreement **both ways**: a test that consults the live gate must carry
the mark (or it would run in `:default`), and a marked test must consult the gate (or a
selector alone would be enough to call a host). Consulting it means a **path** to
`live-llm?` — the call in the test's own body, or a call to a helper whose source reaches
it, in the same file or hoisted into `test_util.clj` — so what proves consent is the gate
and never a helper's name. A second test names the six outright, so adding a live test is
a visible change rather than a quiet one.

Agreement is not the whole claim, and the same scan reads a third thing: **what a test
calls**. A test carrying *neither* decoration satisfies both directions above and dials
out under a plain `lein test`, so a host probe — `ollama/version` and everything over it —
or a real backend built and then handed to a turn is itself reaching, and a reaching test
must carry the mark or must pin the var it reaches through. It reads calls, so it does not
follow indirection: a web route that resolves its own provider is invisible to it, which is
why `web_propose_test` pins `provider/configured` rather than relying on the scan.

It is scriptable, so a test drives the loop exactly. `:script` is the turns to hand
back, one per call; each is a full response map or a shorthand:

```clojure
(stub/provider {:script [{:tool "kb_types_of" :input {"x" "Muffet"}}
                         {:batch {:add [[(dog Muffet) CxWell]] :remove []}}
                         {:lines [[(fatherOf Tom Ann) CxWell]]}   ; the selection path
                         "plain prose"]})
```

`stub/requests` and `stub/last-user-text` read back what the loop actually sent.

On the selection path an **unscripted** stub reads as `:unparseable`, which is the safe
outcome: the only line set meaning "change nothing" is the reader's own selection, and a
provider that never saw it cannot write one. Script `{:lines …}` to drive that path.

### The real backend

`vaelii.host.llm.anthropic/provider` speaks the Messages API over raw HTTP. There is
no official Anthropic SDK for Clojure, and the repo already carries both halves —
`cheshire` for JSON, and JDK `java.net.http`, which `vaelii.host.client` already uses
to reach the vaelii daemon — so this adds **no dependency**. It mirrors that
namespace's style: an explicit connection handle, no global state.

Request details that are required:

- Default model `claude-opus-5`.
- `temperature` / `top_p` / `top_k` are rejected by this model family and are never
  sent; steering happens in the prompt.
- Thinking is on by default and takes no token budget. Depth is
  `output_config.effort`; `:thinking-display "summarized"` opts into readable
  reasoning (the default omits the text).
- A **refusal is HTTP 200** with `stop_reason: "refusal"` and empty or partial
  content, so nothing fabricates a text block and the loop branches on `:stop-reason`
  first.
- `fallbacks: "default"` is sent by default (with its beta header) so a policy decline
  is re-served rather than returned as a dead turn. Pass `{:fallbacks nil}` in the
  request to drop both if the organization has not enabled that beta.
- Streaming parses the SSE frames and reassembles whole blocks, so `stream` returns
  the same response map `complete` would.

Assistant content is echoed back through `:raw`, the block's original JSON — the API
rejects an edited thinking block, and a vendor block type this namespace does not
model still round-trips.

### The local backend

`vaelii.host.llm.ollama/provider` speaks Ollama's chat API over the same raw HTTP, and
adds no dependency either. What differs is everything the transport does:

- **No credential.** `available?` is a reachability probe, not a credential lookup — so
  unlike the Anthropic backend this one *can* be tested end to end against a real model,
  which is what the opt-in live tier does under `VAELII_LLM_LIVE=1`.
- **The window is the caller's to set**, per request, as `options.num_ctx`. Nothing here
  truncates; the caller sizes the prompt first.
- **`format` carries a JSON schema** the sampler is constrained to, which is what lets a
  model with no `tools` capability answer in an exact shape.
- **`temperature` defaults to 0**, so a proposal is reproducible.
- **Streaming is newline-delimited JSON**, not SSE: one object per chunk carrying the
  delta, the last carrying `done: true` and the run's counts. `stream` reassembles it
  into the same response map `complete` returns.
- **Counts come back on every response** — `prompt_eval_count`, `eval_count`, and the
  durations — so `:usage` reports what the host actually measured.
- **`keep_alive` is always sent** (30 minutes by default), because model load is the whole
  latency of a local turn and a host left to its own 5-minute default evicts the model
  between one reader's question and the next.

```clojure
(ollama/available?)                    ; is a host reachable?
(ollama/capabilities "phi4:14b")       ; => #{:completion}
(ollama/supports-tools? "phi4:14b")    ; => false
(ollama/context-length "phi4:14b")     ; => 16384
(ollama/warm)                          ; make the generation model answer fast, now
(ollama/generation-provider)           ; a provider on the page-generation model
```

`warm` is what a panel calls when a page opens. It sends a realistically-sized prefill and
generates one token, because loading the weights is only half the cost: with the model
already resident the *first* real turn still took several seconds to its first assertion
and every turn after it took a fraction of one. Bare, not `warm!` — it destroys nothing.

`capabilities` is worth reading before choosing a path: a model without `:tools` cannot
tool-call, and sending it 87 schemas spends the window on something it will never emit.
`supports-tools?` answers false for an unreachable host too — the conservative direction,
since the cost of guessing yes is a wasted context window.

**Host resolution.** `VAELII_OLLAMA_HOST`, else `OLLAMA_HOST`, else `localhost:11434`.
The rest is sized by `VAELII_OLLAMA_MODEL` (default `phi4:14b`),
`VAELII_OLLAMA_GENERATION_MODEL` (default `qwen3-coder:30b`, the model `propose-page`
runs), `VAELII_OLLAMA_NUM_CTX` (default 8192) and `VAELII_OLLAMA_KEEP_ALIVE` (default
`30m`, how long the host holds the weights resident after a turn). `OLLAMA_HOST` is
overloaded — `ollama serve` reads it as the address to **bind**, so a machine running
its own Ollama commonly has it set to `0.0.0.0:11434`. A wildcard is not somewhere to
connect to, and is not read as one.

### What both HTTP backends share

`vaelii.host.llm.http` holds the part of a transport that is not a wire format, because a
deadline policy living in two places is one that gets fixed in one. Each backend passes an
**endpoint** descriptor, `{:label :slug}` — how the far end is named in a message and in a
thread title — and that pair is the whole of the difference between the two copies.

**The failing body is data, never the message.** A response can be megabytes, and what
answered is often not the API — a proxy in front of it answers HTML. So every refusal that
carries body text bounds what it puts in the message to `http/excerpt`'s opening 200
characters and hands the whole text over in the ex-data: `:excerpt` for a 200 that would not
parse (`:llm-bad-response`), `:body` for a non-200 (`:llm-api-error`). Unbounded, that
megabyte is in every log line the failure reaches, and the first line is what says why
anyway.

**The body read carries its own deadline.** A request's `.timeout` bounds the response
*arriving*, and a streamed turn is almost entirely what comes after that — the lines are
pulled off the socket once `send` has returned. `http/under-read-deadline` runs a daemon
watchdog that closes the body once the deadline passes, which is what makes a blocked read
fail, and rewrites the failure that follows as `:llm-timeout` with the original as its cause.
It catches `Throwable`, not `Exception`: what the read does is parse bytes a far end chose, so
a hostile body can overflow the stack or exhaust the heap, and an `Error` escaping the rewrite
would reach a caller's `:llm-timeout` handler as a parser bug instead. With the deadline
unspent the original propagates unchanged; the watchdog is cancelled either way.

**The connect deadline is not the turn's.** `http/connect-timeout-ms` is a fixed five
seconds and every client is built on it, whatever `:timeout-ms` a caller allowed. The two
bound different things: a turn may legitimately run for minutes — a cold 14B load, a
high-effort answer — while a connection either completes in well under a second or is not
going to. Handed the turn's budget, `connectTimeout` makes a host that never answers the
SYN cost five minutes on Ollama and ten on the Messages API, which is the structure of a hang
rather than of a refusal. A probe that wants to fail faster still can: the request's own
`.timeout` bounds the exchange, connection included, so `ollama/version` keeps its
two-second gate.

**One client for the probes.** A JDK `HttpClient` owns a connection pool and a selector
thread. `ollama/probe-client` is one held client that `version`, `show` and `warm` all
send on — and so `available?` and `capabilities` above them, which matters because
`available?` runs on every `/propose` the browser posts. Nothing varies per probe: the
host rides on the request URI and the deadline on the request. A provider keeps its **own**
client, since a turn is long-lived and streams and its connections are not a probe's to
share.

**There is no retry and no backoff.** A 429 or a 529 surfaces as `:llm-api-error` with the
status in its ex-data, exactly like any other non-200, and the turn ends there. Nothing
here sleeps, re-sends, or reads a `retry-after` header; a caller that wants to try again
calls again.

### Credentials

`anthropic/credentials` resolves the way the official SDKs do: `ANTHROPIC_API_KEY`,
then `ANTHROPIC_AUTH_TOKEN`, then an `ant auth login` profile via
`ant auth print-credentials --access-token`. **An unset `ANTHROPIC_API_KEY` does not
mean there is no credential** — an active OAuth profile is enough, and it
authenticates with `Authorization: Bearer` plus the OAuth beta header rather than
`x-api-key`.

The value is a secret: it is returned for the caller to hand straight to a header, and
is never logged, printed, or put in an exception message. Nothing here reads or writes
a credential file. `anthropic/available?` is the gate for choosing between this
backend and the stub.
