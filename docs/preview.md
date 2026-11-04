# Consequence preview

- **Covers:** what a batch of adds and removes would do to belief, computed then
  rolled back at the same handles; the same diff after a batch lands
  (`edit-with-consequences!`).
- **Not here:** how belief itself is computed and revised on a real write →
  [nmtms.md](nmtms.md); whether a batch would be admitted at all →
  [api.md](api.md); the same diff delivered after every settle → [feed.md](feed.md).
- **Assumes:** sentex, context, justification, settle → [glossary.md](glossary.md).

`core/preview` — what a batch would do to the KB, without leaving it done.

```clojure
(preview kb {:add [[sentence context opts?] …] :remove [handle …]} opts?)
;; => {:believed-added   [{:sentence S :context C :handle h|nil :premise? bool
;;                         :justification {:informant i :strength k :rule S
;;                                         :antecedents [S …]}} …]
;;     :believed-removed [{:sentence S :context C :handle h :reason kw :detail {…}} …]
;;     :refused          [ …check-edit shape… ]
;;     :violations       [ …violations shape… ]
;;     :contradictions   [ …contradictions shape… ]
;;     :bounded?         bool
;;     :owed-releases    n
;;     :release-path     :deferred | :swept}
```

`check` ([api.md](api.md), "Validating without writing") answers whether a batch would
be **admitted**. `preview` answers what the batch would **mean**: a well-formed line can
still take half the KB's beliefs OUT, and no check reports that. Showing an author which
entailments an edit adds and removes measured a 42% improvement in verification
correctness (Inference Inspector, Matentzoglu et al.).

## The mechanism

`preview` applies the batch, settles, reads the belief diff, and undoes the batch at the
handles it wrote. `edit!` followed by `retract!` cannot do this: a `retract!` sweeps, and a
swept datum comes back only by re-derivation, at a fresh handle, which breaks every handle
a caller holds. Three arrangements keep every write undoable in place.

**An `:add` is asserted**, under a premise audit (`entry/*premise-audit*`) that records
each datum's premise state before `assert` first marks it. The rollback reads the audit
three ways: a handle that did not exist is retracted, one that existed as a derived datum
is un-marked, and one that was already a premise gets its original strength back.
Everything the batch derived rests on one of those premises, so retracting them collects
it through the ordinary dependency-directed sweep. The un-mark arm exists because
`assert` of a sentence the KB already derives marks the stored sentex a premise; a
rollback that retracted only what it created would leave that conclusion standing as a
premise.

**A `:remove` is not retracted.** It is `jtms/suspend-premise`, a retraction's effect on
belief without the sweep ([nmtms.md](nmtms.md) states why that is the whole effect on
belief). The rollback puts the premise back with `add-premise`, then applies the audit to
it as to any add: a handle the batch both adds and removes is suspended at the class the
add raised, and only the audit holds the class the batch found. A real removal queues the
`exceptWhen` re-check at the removal choke point, and for an `except` the re-join of the
firings it refused (`special/recheck-except`). A suspension queues both by hand, and the
rollback queues them again when the premise returns.

**`settle`'s own sweep is off for the duration** (`settle/*sweep?*`). An added
`exceptWhen`, or a fact that triggers one, blocks a justification without deleting what
it supported: the conclusion goes OUT and is reported, and its record and justification
stay. A guard defeat's justification the apply drops stays too (`chain/place-guard-defeats!`
with its drop off), and the preview's answer reads it through the read walk, which takes a
guard out of force wherever a blocker of it is OUT or excepted, as the drop does
(`exc/verdict-reader`'s `:guard`). `preview_test`'s random stream holds the two answers
alike over a rule with a `:default` blocker and excepts of that blocker
(`a-preview-predicts-the-edit-over-a-random-stream`).

The **rollback** settles with the sweep back on. That settle collects a conclusion the
preview's own removals brought into being: removing a blocker releases an exception,
`rechain-exception-rules` derives the conclusion at a fresh handle, and restoring the
premise blocks it again, so the sweep takes it.

## The answer

`:believed-added` and `:believed-removed` are the two halves of the belief diff, each in
**content** order — by sentence, then by context — so the same batch against the same
knowledge reads the same on any load order. `:max-results` caps both halves after that
sort, so the order decides which entries a caller is shown
([defenses.md](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle)).

The removed half carries defeat, supersession and the dependency-directed sweep, and its
`:reason` is `why-not`'s: `:defeated` (a stronger claim arrived), `:superseded` (an
equality merge restated it), `:unsupported` (its last witness went). A batch that only
adds can still fill it.

`:handle` is **nil** for content the batch created: after the rollback no such sentex
exists, and the number would later name another one. Content that was already stored
keeps its handle, so a defeated default and a blocked conclusion stay addressable.

`:justification` is one level, not `why`'s graph: the informant, the strength it confers,
the rule it names when that informant is a stored rule, and the antecedent sentences. A
tree apiece would be a proof search per entry. A datum several derivations support names
the **content-least** justification (`supporting-justifications`), never whichever
derivation landed first.

`:rule` is present only where the informant is a **handle**. The engine's symbol
informants — `rewriteOf`, `except`, `functional`, `decontextualized_predicate`, `arg` — name no
stored rule, so the key is absent rather than nil.

**`:antecedents` is every sentex the firing rests on**, including one witness per
reachability the placement used: the `genl` edges the match subsumed through, and the
`genlCx` edges the placement saw each ingredient context over
([contexts.md](contexts.md), [nmtms.md](nmtms.md)). A rule in `CxLow` firing on a fact in
`CxMid` reports the edges that let it see across:

```clojure
(preview kb {:add [['(puppy Muffet) 'CxMid]]})
;; :believed-added
;;   {:sentence (mortal Muffet) :context CxLow :handle nil :premise? false
;;    :justification {:informant 4 :strength :monotonic
;;                    :rule (implies (dog ?x) (mortal ?x))
;;                    :antecedents [(genl puppy dog)
;;                                  (genlCx CxLow CxMid)
;;                                  (genlCx CxMid CxUniverse)
;;                                  (puppy Muffet)]}}
```

Belief reads the vector as a conjunction, so a preview of a `:remove` of the
`(genlCx CxMid CxUniverse)` edge reports `(mortal Muffet)` gone, `:unsupported`, with
that handle in the `:missing` list. The rule is the justification's informant, not an
antecedent, and is reported as `:rule`. The order is the stored one, which is content
(`kb/antecedent-order`).

`:refused` is `check-edit`'s verdict plus each `ex-info` an add threw. A batch whose second
line is inadmissible only because the first landed passes `check-edit` and throws during
application. A refused entry is skipped and the rest of the batch is previewed without
it. A throw that is not an `ex-info` propagates after the rollback.

`:violations` is what the **derivation path** dropped: the definitional constraints
(arg, disjointness, functionality) that chaining reports rather than throws
([inference.md](inference.md)). The KB's own ledger is restored, so a preview never
shows up in `(violations kb)`. `:violations` lists no `:forced-conclusion` entry, since
`violations` reads that entry off the stored firings and files nothing in the ledger
([nmtms.md](nmtms.md#the-forced-monotonic-set)).

`:contradictions` is the dilemmas the batch would **open**, with the standing ones
subtracted. Asserting the negation of a believed default withdraws nothing — a defeasible
tie is represented, not arbitrated ([nmtms.md](nmtms.md)) — so both halves of the diff are
silent about that clash, and this key is where it shows.

`preview` refuses an **unrecovered** KB where `edit!` does (`:unrecovered-kb`);
[storage.md](storage.md#and-until-it-is-rebuilt-the-kb-does-not-accept-writes) states why
a dry run must refuse with it.

## What a preview omits

A preview's settle keeps the withheld-mint releases owed, as an open's settles do
([argtypes.md](argtypes.md#pruning-what-the-kb-says-more-specifically--vaelii_prune_subsumed_mints-on)).
A batch that removes the membership withholding a mint therefore previews without the
general membership the apply draws, and without any contradiction that membership enters:
with `(disjoint animal plant)` and `(plant Fred)` beside `(dog Fred)`, removing `(dog
Fred)` draws `(animal Fred)` into a clash with `(plant Fred)` on the apply, while the
preview reports none. `:owed-releases` counts the departures and arrivals the preview kept
owed, and `:release-path` is `:deferred`. A preview whose `:owed-releases` is above 0 can
omit mints and contradictions alike. The rollback discards the debt, so `owed-releases`
reads the same before and after.

`{:release-withheld? true}` runs the release sweep inside the preview: `:release-path` is
`:swept`, `:owed-releases` is 0, and the diff and `:contradictions` report what the apply
draws (`preview_test/a-deferred-preview-omits-the-clash-a-released-mint-enters`).

## What the rollback restores, and what it does not

The KB is left with the same live sentexes and justifications at the same handles, and the
same premise classes. The derived state a batch can write is restored with them: the
violations ledger, the program, and the **refusal record**, which a firing the batch's
own content refused would otherwise leave holding handles the rollback took away
([exceptions.md](exceptions.md), "A refused firing is remembered as bindings"). An entry
the batch consumed comes back through the rollback's own re-chain.

The calculi's report markers (`observe/newly-seen?`) go back with the ledger
(`observe/restore-seen!`). A calculus files an unsatisfiable network once per KB and
context, and the marker records that it did, so a marker the batch left would keep the next
write that makes the same network from filing its entry
(`qcn_chain_test/an-assert-after-a-refused-try-assert-or-a-preview-of-it-files-the-unsatisfiable-entry`).
The markers go back whole, a reader thread's included, so a network a reader reported while
the batch ran can be reported a second time.

A constraint entry records the `genl` and `genlCx` generations it was decided under, and
`settle` re-asks an entry whose generations moved. A declaration waiting on a type bound
to another length is read only when that type's own bindings move, which no edge does, so
a previewed edge reads none
(`preview_test/a-rolled-back-preview-reads-no-declaration-waiting-on-a-length`).

The violations ledger keeps an entry filed on **another thread** while the batch ran. The
qualitative, metric and sign calculi file an inconsistency from inside a read, so a
`query` on a reader thread can file one during a preview. The batch records each entry
its own thread files (`vaelii.impl.violations/*batch-entries*`), and both `:violations`
and the rollback read that set.

Not restored:

- **the handle counter**. A preview mints handles and they are not reissued, so a
  number a caller holds never names a second sentex.
- **the `chain-stats` / `settle-stats` counters**, which record work that ran.

On the `:disk` backend the record log is append-only, so a preview writes frames and then
deletes what they held: the live record set is back at baseline and the log is longer, as
after any `assert`-then-`retract!` ([storage.md](storage.md)).

## The rollback is one implementation

`edit!` is all-or-nothing ([api.md](api.md)), and a refused batch is put back by the same
`rollback-batch!`: the audit, its three arms, the settle with the sweep on, and the
restored ledgers are one code path with two callers (three, counting a single `assert`
that throws after writing). The two entry points differ in **when** they roll back:

| | `preview` | `edit!` |
|---|---|---|
| rolls back | always | only when the batch throws, the caller's `:max-ms` or `:stop?` ending its adds included ([inference.md](inference.md#stopping-a-run)) |
| an `:add` | asserted, undone through the audit | the same |
| a `:remove` | `jtms/suspend-premise`, restored | a real teardown, never reached by a rollback |
| `settle`'s sweep | off for the batch | on, as for any write |
| the change feed | off for the whole preview | off for the rollback; the batch's own event is never delivered |

A swept record comes back only as new content at a new handle, so `edit!` asks every
removal for its refusal (`teardown-refusal`, the function `retract!` throws from) before
the first one runs, and past that point the batch is committed.

A preview is a write followed by its undo, so it holds the single writer for its duration
([storage.md](storage.md), "The single-writer contract"). For that reason `serve/ops`
and `vaelii.browser.access` file it with the writes, and a remote client gets it through
the daemon ([operations.md](operations.md)).

An **inert** sentex (`assert-inert`) in `:remove` reports nothing, because it was never a
TMS datum and removing it moves no belief. `edit!` deletes its record.

## Cost

`preview` costs the batch's settle plus the rollback's, and scans nothing KB-wide: every
relabel is region-local ([nmtms.md](nmtms.md)), the rollback walks the premises the batch
marked, and the diff is taken over the **relabelled region**. `settle` hands a copy of
that region to `settle/*touched-sink*`, a superset of every handle whose belief moved;
diffing the believed set instead is O(KB)
([defenses.md](defenses.md#the-touched-set-is-a-superset-not-the-flip-set)). The one
belief change with no relabel behind it, a supersession flip, is folded into the region
([nmtms.md](nmtms.md)).

Belief **before** is read *after* the rollback, on the restored KB, so the two readings
need no snapshot: a candidate believed now was believed before, and a handle the rollback
took away reads as not believed.

`:contradictions` is read off the touched set. With the batch in force,
`clashes/opened` takes the placed `(contradicts …)` sentexes among the handles the batch
relabelled, stored or suspended, and reads the report of each of their nogoods over every
placement of its sentence (`clashes/placements-of`, at the sentence's own index path under
every context), as `contradictions` reads it. After the rollback,
`clashes/standing-removed` reads the same sentences' placements again and subtracts the
reports standing then. A batch that places, removes or relabels no `contradicts` reads no
nogood, and an empty batch has nothing in its touched set
(`preview_test/a-preview-reads-no-placed-nogood-outside-its-touched-set`). The placements
are read once per nogood, however many nogoods share a member
(`preview_test/a-preview-reads-each-placement-once-however-many-nogoods-share-a-member`).
`perf`'s `preview-beside-standing-dilemmas` holds a preview of a fact no nogood reads, and
of an empty batch, flat in the dilemmas standing in its context, and
`preview_test/a-preview-opens-the-dilemmas-the-full-read-opens-over-a-random-stream`
compares the answer with the reading over every stored `contradicts`.

The operation log records a preview as a write, because the handles it allocates stay
allocated. `oplog/replay!` runs the logged preview's writes and rollback, and takes none
of its reads: no reading before the batch, no touched set, no diff and no dilemma report
(`oplog_seal_test/a-restore-replays-a-preview-s-writes-and-rollback-and-none-of-its-reads`).

A batch whose conclusions cascade costs what the cascade costs; `:max-depth` and
`:max-derivations` bound the chaining, and `:max-results` caps each half of the answer but
not the walk, since every datum in the region gets an entry. `:bounded?` is true when any
of the three cut the answer.

## The other direction: what a write did mean

`preview` answers before. **`edit-with-consequences!`** answers after — the same two
halves, about a batch that landed:

```clojure
(edit-with-consequences! kb {:add [['(dog Muffet) 'CxStory]]})
;; => {:added [4] :removed {…}
;;     :believed-added   [{:sentence (dog Muffet)    :premise? true  :handle 4 …}
;;                        {:sentence (mortal Muffet) :premise? false :handle 5
;;                         :justification {:rule (implies (dog ?x) (mortal ?x))
;;                                         :antecedents [(dog Muffet)] :informant 3
;;                                         :strength :monotonic}}]
;;     :believed-removed []
;;     :bounded?         false}
```

The rule, the fact and the conclusion share one context there, so the placement names no
edge and `:antecedents` is the fact alone. `edit!` reports only the handles it stored;
`:premise?` separates those from what followed, so `(remove :premise? …)` is what the
writer did not say.

**Where the diff comes from.** There is no rollback to read belief-before off, so the
labels are captured on the way through. Alongside the relabelled region (`jtms/touched`),
every relabel records which of the region was **already believed** when it first touched
it (`jtms/touched-in`, first reading wins). The touched set accumulates from the end of the last
settle, so for a batch it covers the whole deferred phase and its one settle.
`settle/*touched-in-sink*` receives that set beside `*touched-sink*`, and
`core/moved-handles` turns region, before-labels and belief now into the delta. A
supersession flip is folded into the before-labels for the reason `preview` folds it into
the region.

**What the removed half cannot say.** A datum the dependency-directed sweep deleted has no
record left to describe, so it is omitted: the half lists belief that went away and is
**still stored**. Ask `preview` what a removal would take with it; it suspends instead of
retracting. An add-only batch, which is what the browser's commit paths send, loses
nothing this way.

**An equality merge** supersedes the displaced spelling on the *assert* path, with no
relabel to record it. The settle publishes the supersession moves since the last settle,
each with its entry before (`special/take-supersession-moves!`), so `(sameAs Pref Dep)`
over a stored `(dog Pref)` reports `(dog Dep)` added and `(dog Pref)` removed here, and
`preview` reports `(dog Pref)` as `:superseded`. `feed_test` asserts that the change feed
agrees.

## The third caller: the change feed

`core/watch` asks the same question of every settle ([feed.md](feed.md)).
`edit-with-consequences!` and the feed share `core/moved-handles`, and all three share the
entry builders, so a promise, its outcome and a feed event cannot disagree about what a
batch meant.
`feed/*enabled?*` is off for the whole preview, rollback included
([feed.md](feed.md#what-does-not-arrive)).

## Tests

`test/vaelii/preview_test.clj`, and `test/vaelii/derived_callout_test.clj` for the *after*
half, which checks the two against each other on the same batch. They share the entry
shapes and nothing else, so agreement is evidence that both describe the commit.

A preview test that stores or derives pairs its assertion about the answer with a
before/after comparison of the live sentex and justification sets: a test that relied on
the neutral fixture would pass on a preview that stored everything and let the teardown
clean up.

Five of them are the **oracle**: run the preview, then run the batch with `edit!`, and
compare the two belief diffs — derive, defeat, block a conclusion, remove a premise,
release an exception. They compare by sentence, because content a batch creates, and
content a released exception re-derives, lands on a fresh handle either way.

`web_test.clj` covers the editor's lookahead over it (`POST /edit/preview`,
[web.md](web.md)).

`jtms_dense_oracle_test` applies `suspend-premise` in its randomized op streams and asserts
it by name, so the two TMS representations agree about it op by op.
`VAELII_TEST_TMS=reference` runs these tests against the persistent-map network and
`VAELII_TEST_BACKEND=disk-log` against the durable store.
