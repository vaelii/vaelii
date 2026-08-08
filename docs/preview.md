# Consequence preview

- **Covers:** what a batch of adds and removes would do to belief, computed then
  rolled back at the same handles.
- **Not here:** how belief itself is computed and revised on a real write →
  [nmtms.md](nmtms.md); whether a batch would be admitted at all →
  [api.md](api.md).
- **Assumes:** sentex, context, justification, settle → [glossary.md](glossary.md).

`core/preview` — what a batch would do to the KB, without leaving it done.

```clojure
(preview kb {:add [[sentence context opts?] …] :remove [handle …]} opts?)
;; => {:believed-added   [{:sentence S :context C :handle h|nil :premise? bool
;;                         :justification {:informant i :rule S :antecedents [S …]}} …]
;;     :believed-removed [{:sentence S :context C :handle h :reason kw :detail {…}} …]
;;     :refused          [ …check-edit shape… ]
;;     :violations       [ …violations shape… ]
;;     :contradictions   [ …contradictions shape… ]
;;     :bounded?         bool}
```

`check` ([api.md](api.md), "Validating without writing") answers whether a batch would
be **admitted**. This answers what it would **mean**. They are different questions and
an editor needs both: a line can be perfectly well-formed and still turn off half the
KB's beliefs, and that is not a thing any check can see.

The literature is unusually clear here. Showing which entailments an edit adds and
removes measured a 42% improvement in verification correctness (Inference Inspector,
Matentzoglu et al.), and studies of real authoring find people doing it by hand —
running the reasoner after every axiom, because the tool will not say what they just
did.

## The mechanism, and why it is not `edit!` then `retract!`

Apply the batch, settle, read the belief diff, undo. The undo is the whole problem: a
`retract!` **sweeps**, and what a sweep deletes can only be put back by *deriving it
again*, which lands it on a fresh handle. A preview that moved a handle would be a
preview that broke every reference the caller was holding.

So `preview` writes nothing it cannot take back at the same handles. Three arrangements
make that true:

**An `:add` is really asserted**, and rolled back through the premise marks it made. The
dynamic `*premise-audit*` records each datum's prior premise state as `assert` marks it,
so the rollback knows the three cases apart: a handle that did not exist is retracted
outright, one that existed as a derived datum is un-marked, and one that was already a
premise gets its original strength back. Everything the batch derived hangs off one of
those premises — a derived datum whose rule and antecedents all pre-existed would have
pre-existed too — so retracting them collects the lot through the ordinary
dependency-directed sweep.

That third case is the leak a rollback-by-handle misses. Assert a sentence the KB
already derives and `assert` finds the existing sentex and marks it a premise; retract
only what you *created* and you have quietly turned a conclusion into an assumption.

**A `:remove` is not retracted.** It is `jtms/suspend-premise` — a retraction's effect
on belief with the deletion left out. That is sound because the sweep never moves a
label: it collects datums that are already OUT and ungroundable, so dropping them
changes nothing anyone can observe about belief, which is the whole of what a preview is
asked about. A suspended premise goes straight back with `add-premise` at the strength
it had. The suspension queues the same `exceptWhen` re-check a real removal queues from
the removal choke point — without it, an exception the datum was the only evidence for
would never be re-asked, and the rule it blocks would never fire again.

**`settle`'s own sweep is off for the duration** (`settle/*sweep?*`). An added
`exceptWhen` — or a fact that triggers one — blocks a justification, and the ordinary
settle deletes what it was supporting. Under a preview it blocks without deleting: the
conclusion goes OUT and is reported, and its record and justification stay where they
were.

The **rollback** settles with the sweep back **on**, which is what collects a conclusion
the preview's own *removals* brought into being. Removing a blocker releases an
exception, `rechain-exception-rules` derives the conclusion again at a fresh handle, and
restoring the premise blocks it again — at which point it is newly blocked, and the
sweep takes it. Both directions therefore land back at baseline, and neither leaves the
sweep able to reach anything that was there before.

## The answer

`:believed-added` and `:believed-removed` are the two halves of the belief diff, in
handle order (handles, so the order is a fact about the KB and not about the batch).

The **removed** half is the interesting one, and the one a naive implementation misses.
It is where defeat, supersession and the dependency-directed sweep show up, and its
`:reason` is `why-not`'s: `:defeated` (a stronger claim arrived), `:superseded` (an
equality merge restated it), `:unsupported` (its last witness went). A batch that only
adds can still empty this half or fill it.

`:handle` is **nil** for content the batch created. After the rollback there is no such
sentex, and a number naming nothing is worse than nothing — after enough churn it names
something else. Content that was already stored keeps its handle either way, so a
defeated default and a blocked conclusion are both still addressable, which is what a
UI wants to link to.

`:justification` is one level, not `why`'s tree: the informant, the rule it names when
that informant is a stored rule, and the antecedent sentences. A preview reports a whole
batch's consequences, and a proof tree apiece would be a proof search apiece.

`:refused` is `check-edit`'s verdict plus anything that threw on the way in. `check` is
a fair account of `assert`'s refusals, not a proof of one: a batch whose second line is
inadmissible *only because the first landed* passes the pre-flight and throws during
application. A refused entry is skipped and the rest of the batch is previewed without
it — an admissible batch minus its bad line is what the caller is about to ask for
anyway.

`:violations` is what the **derivation path** dropped: the definitional constraints
(argIsa, disjointness, functionality) that hold of derived content as much as of
asserted content, and that chaining reports rather than throws
([inference.md](inference.md)). The KB's own ledger is restored, so a preview never
shows up in `(violations kb)`.

`:contradictions` is the dilemmas the batch would **open**, and it is here because
otherwise the most obvious thing a reviewer can do would report nothing at all. Asserting
the negation of a believed default withdraws nothing: a defeasible tie is *represented*,
not arbitrated ([nmtms.md](nmtms.md)), so both sides stay believed and both halves of the
diff are silent about a clash the batch just created. Standing dilemmas are subtracted, so
what is listed is what the batch is answerable for.

## What moves anyway

The KB is left byte-identical — same live sentexes, same justifications, at the same
handles. The derived state a batch can *write* is restored with them: the violations
ledger, the program, and the **refusal record**, which a firing the batch's own content
refused would otherwise leave holding handles the rollback took away
([exceptions.md](exceptions.md), "A refused firing is remembered as bindings"). The
entries a batch *consumes* need no snapshot — the rollback's own re-chain re-records
whatever the baseline refuses.

Two things are not restored, and neither can be:

- **the handle counter**. A preview mints handles and they are not reissued. Handles are
  longs and this is one per created sentex; the alternative is reissuing a number a
  caller might still be holding.
- **the `chain-stats` / `settle-stats` counters**, which record work that genuinely ran.

On the `:disk` backend the record log is append-only, so a preview writes frames and
then deletes what they held: the live record set is back at baseline and the log is
longer, which is exactly what an ordinary `assert`-then-`retract!` does there and what
compaction is for ([storage.md](storage.md)).

A preview is a write followed by its undo, so it holds the single writer for its
duration ([storage.md](storage.md), "The single-writer contract"). It is not a read.

That is also why it is filed with the writes in `serve/ops` and `vaelii.impl.access`,
though it stores nothing: a remote client gets the same answer over the daemon
([operations.md](operations.md)), because the daemon *is* the single writer.

An **inert** sentex (`assert-inert`) in `:remove` reports nothing, because removing one
moves no belief — it was never a TMS datum. That is the same answer `edit!` gives, in
belief terms; what `edit!` additionally does is delete the record.

## Cost

The batch's own cost — one settle over the affected region, exactly as `edit!` — plus the
rollback, which is a second one. Nothing scans the KB: every relabel is region-local
([nmtms.md](nmtms.md)), the rollback walks the premises the batch marked, and **the diff
is taken over the relabelled region rather than over the believed set**.

That last one is the whole difference between a usable preview and a toy. A set
difference of the believed set before and after is the obvious implementation and it is
O(KB): 4.4 ms at 2.7k sentexes, 41.6 ms at 23k, 401 ms at 224k — dead linear, and hopeless
at the scale this engine is built for. The region is already computed and already
discarded: `settle` accumulates the datums whose region it relabelled (to skip taxonomy
caches no moved supporter touches) and clears them at the end. `settle/*touched-sink*`
takes a copy first, and that set is a superset of every handle whose belief moved. The
one belief change with no relabel behind it — a supersession flip — is folded in by hand,
for the same reason `settle` folds it into its own reconcile.

Belief **before** is then read *after* the rollback, on a KB that is back at baseline, so
the two readings need no snapshot between them: a candidate believed then was believed
all along, and a handle the rollback took away reads as not believed, which is exactly
right since it did not exist.

Measured over generated corpora (`vaelii.impl.io.generate`, 40 predicates / 200 types,
one hand-added rule, a batch of one fact that fires it; median of fifteen after a
warm-up):

| facts | stored sentexes | `preview` | `edit!` + `retract!` |
|---|---|---|---|
| 2 000 | 2 761 | 0.72 ms | 0.68 ms |
| 20 000 | 23 404 | 0.65 ms | 0.47 ms |
| 200 000 | 223 559 | 0.63 ms | 0.46 ms |

Flat in KB size, at 1.06–1.4× the destructive round trip — which is the second settle.

A batch whose conclusions **cascade** is expensive because the cascade is, and that is
exactly the answer being asked for; bound it with `:max-derivations` when that matters.
The region also bounds the *reporting*: an entry is built for every datum in it, and
`:max-results` caps the answer rather than the walk.

`opts` bounds the run: `:max-depth` / `:max-derivations` reach chaining, `:max-results`
caps each half of the diff. `:bounded?` says one of them bit, so a partial answer never
reads as a complete one.

## The other direction: what a write *did* mean

`preview` answers before. **`edit-with-consequences!`** answers after — the same two halves,
about a batch that landed:

```clojure
(edit-with-consequences! kb {:add [['(dog Muffet) 'StoryContext]]})
;; => {:added [4] :removed {…}
;;     :believed-added   [{:sentence (dog Muffet)    :premise? true  :handle 4 …}
;;                        {:sentence (mortal Muffet) :premise? false :handle 5
;;                         :justification {:rule (implies (dog ?x) (mortal ?x))
;;                                         :antecedents [(dog Muffet)] :informant 3}}]
;;     :believed-removed []
;;     :bounded?         false}
```

It exists because `edit!` reports the handles it stored, which is what the caller already
said, and nothing about what followed. `:premise?` separates the two: a derived conclusion
is not a premise, so `(remove :premise? …)` is exactly "what the writer did not say".

**Where the diff comes from.** Not the rollback trick above — there is no rollback to read
belief-before off. Instead the labels are captured on the way through: alongside the
relabelled region (`jtms/touched`), every relabel records which of that region was
**already believed** when it first touched it (`jtms/touched-in`), first-reading-wins so a
datum relabelled twice keeps the earlier answer. The window runs from the end of the last
settle, which for a batch covers the whole deferred phase *and* its one settle. Region,
plus before-labels, plus belief now, is the delta — and it is proportional to what the
batch moved, never to what is stored. A supersession flip, which changes reported belief
without moving a label, is folded into the before-labels by hand for the same reason
`preview` folds it into the region.

`settle/*touched-in-sink*` is the seam, the companion of `*touched-sink*`. Both TMS
representations implement `touched-in`, and since `jtms/snapshot` carries it, the
randomized dense-vs-reference oracle (`jtms_dense_oracle_test`) compares it at every step
of every run.

**What the removed half cannot say.** A datum the dependency-directed sweep *deleted* has
no record left to describe, so it is omitted rather than guessed at: what is listed is
belief that went away and is **still stored** — defeated, superseded, unsupported. A
`:remove` sweeps, so ask `preview` what a removal would take with it; it suspends instead
of retracting and can still name every casualty. An add-only batch has no such gap, which
is the case the browser's commit paths are.

There is a second gap, and it is the one place `preview` and this answer differently on
the same batch. An **equality merge** supersedes the displaced spelling on the *assert*
path, and the before-labels hand-off covers only what a `settle` supersedes — so
`(sameAs Pref Dep)` over a stored `(dog Pref)` reports `(dog Dep)` added and nothing
removed here, where `preview` reports `(dog Pref)` as `:superseded`. `preview` reads
belief-before off the restored KB and so needs no hand-off; this one has only what was
captured on the way through. Closing it means the equality path posting the displaced
handle where a settle can see it. `feed_test` pins the current answer, because the change
feed shares this diff and the two must not drift apart by accident.

Measured the same way as the table above (one fact firing one rule, 300 iterations after a
200-iteration warm-up): 0.31 ms at 2 003 stored sentexes, 0.31 ms at 4 005, 0.28 ms at
23 430 — against a plain `edit!` at 0.34 / 0.30 / 0.26 ms. The overhead is inside the noise
and, more to the point, does not grow with the KB: what it tracks is the region.

## The third caller: the same diff, continuously

`core/watch` asks that same question of *every* settle rather than of one batch — a change
feed an application drives instead of polling ([feed.md](feed.md)). The three share
`core/moved-handles`, which is the one place region + before-labels + belief-now becomes a
delta, so a promise, its outcome and a feed cannot disagree about what a batch meant; a
test compares the last two on the same batch. `settle-finish` decides the region once and
hands it to the caller's two sinks and the feed's accumulator together.

A preview is the one caller the feed must **not** hear from: it stores, reads and takes
every write back, so a listener would be sent a change and then its exact reverse.
`feed/*enabled?*` is off for the whole preview, rollback included.

## Tests

`test/vaelii/preview_test.clj`, and `test/vaelii/derived_callout_test.clj` for the *after*
half — which checks the two against each other on the same batch. They share the entry
shapes and nothing else, so agreement is evidence rather than tautology, and a
disagreement would mean one of them is wrong about what a commit does.

Every preview test pairs an assertion about the answer with a
before/after comparison of the live sentex and justification sets, because a test that
relied on the neutral fixture would pass on a preview that stored everything and let the
teardown clean up.

Five of them are the **oracle**: run the preview, then really run the batch with `edit!`,
and compare the two belief diffs — derive, defeat, block a conclusion, remove a premise,
release an exception. By sentence and not by handle, because content that a batch
creates, and content that a released exception re-derives, lands on a fresh handle
either way. That is the only test that asks the question the function is named after.

`web_propose_test.clj` covers the panel over it (`POST /propose/preview`,
[web.md](web.md)) — a rule firing, a withdrawal, a dilemma opened, two lines refused only
together — each also asserting the KB did not move, because a panel that recomputes on
every change of the accepted set has to be free to be wrong about.

`suspend-premise` is covered where the rest of the network is: `jtms_dense_oracle_test`
applies it in the randomized op streams and pins it by name, so the two representations
are proved to agree about it op by op. The suite's two gates cover the rest —
`VAELII_TEST_TMS=dense` runs these tests against the dense network and
`VAELII_TEST_BACKEND=disk` against the durable store.
