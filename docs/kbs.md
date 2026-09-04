# Getting a KB in front of you

- **Covers:** which of the four loadable knowledge bases to pick, and the exact commands to
  load each — from the shipped starter through a durable OpenCyc store.
- **Not here:** the loading mechanism itself (sources, search path, progress, cancellation) →
  [catalog.md](catalog.md); the foreign-reader plugin seam → [foreign.md](foreign.md).
- **Assumes:** sentex, context, `recover` → [glossary.md](glossary.md).

Four knowledge bases you can load, and the route to each is a different length: two ship
in this repo, one ships in the plugin, and one you supply. A fifth source is the
**generator**, which synthesizes a KB at whatever shape you ask for rather than reading
one ([catalog.md](catalog.md)) — and a sixth is **text you exported yourself**, below.

The *mechanism* is elsewhere and not repeated here — [catalog.md](catalog.md) for what a
source is, how one loads and what holding it costs, [foreign.md](foreign.md) for why no
OpenCyc reader is in this repo. This page is the **sequence**, and what each step buys.

| KB | comes from | to first load | once loaded |
|---|---|---|---|
| Starter ontology | the classpath | seconds | ~1,879 sentexes |
| Core vocabulary | the classpath | seconds | ~535 sentexes |
| cyc-tiny | a test fixture in the plugin | one dependency, then seconds | 8,181 sentexes |
| OpenCyc 4.0 | a distribution you supply | a conversion, then ~10 minutes | ~1.2M sentexes |

## The shipped pair needs nothing

```sh
lein run -m vaelii.web        # starter-loaded, http://localhost:3000
```

That is the whole route. `lein browser` gives you the same browser with a REPL and a
reload channel into it; `lein cli repl --starter` gives you the KB and no browser.

Neither KB is a one-shot. **Core vocabulary**, **Starter ontology** and the **generator**
are the three sources always offered on the `/kbs` page, so you can load any of them again
— or a second copy at a different shape — without a restart.

## Both OpenCyc routes start with the reader on the classpath

In a released tree, `+with-foreign` names the released reader, which Clojars carries,
so prefixing a command with it resolves the reader and there is nothing to install:

```sh
lein with-profile +with-foreign run -m vaelii.web
```

Two other routes exist and are worth knowing apart.

**In the development tree**, `+with-foreign` names a snapshot version, which
Clojars does not carry, so it comes out of `~/.m2` and you put it there yourself:

```sh
cd ../vaelii-foreign && lein install
```

Re-run that after any change to the plugin. The profile resolves the **installed** jar,
so a stale snapshot does not fail loudly — it silently lacks whatever namespaces were
added since.

**`scripts/link-checkouts.sh`** is the way out of that entirely: `checkouts/vaelii-foreign`
resolves the readers from live source and needs no install at all. The cost is that a
checkout is on every command's classpath, so the build stops matching a shipped one;
[foreign.md](foreign.md) has the trade in full.

## cyc-tiny, which is the small honest example

The plugin vendors 804 KB of real CFASL as a test fixture — 717 constants, 8,899
assertions, taken from Cycorp's OpenCyc 4.0 distribution; the terms it travels under are
stated in [vaelii-foreign](https://github.com/vaelii/vaelii-foreign), which is where the
fixture and its reader live. It is a raw dump and not a KB: there is no `meta.edn`, so `classify` finds no marker, the catalog does not offer it,
and it has to be converted first.

```sh
cd vaelii-foreign
lein convert convert cyc test/resources/cyc-tiny ~/.vaelii/kbs/cyc-tiny
```

About a second: 8,899 assertions become 8,248 sentences in 16 contexts, 740 dropped with
a reason apiece. Then, back in the engine:

```sh
cd ../vaelii
lein with-profile +with-foreign browser
```

`/kbs` → the **cyc-tiny** card → Load, at the default `ontology` profile. Ready in a few
seconds: 8,181 sentexes, 765 terms, 364 types, 17 contexts, and 128 sentences the engine's
own definitional checks refused.

## OpenCyc 4.0, which you supply

Not shipped here and not ours to ship — it is Cycorp's distribution. The conversion reads
the distribution's own binary unit files directly, needing no Cyc image and no external
tool, so the input is a directory inside it (`5022` on the 4.0 release):

```sh
cd vaelii-foreign
lein convert convert cyc <opencyc>/server/cyc/run/units/5022 ~/.vaelii/kbs/opencyc-4.0
```

`convert` is vaelii-foreign's alias, not this repo's, so both commands on this page run
from that checkout; the engine has no such task and answers "not a task".

**The plugin's own OpenCyc page owns these figures**, states them as one run's rather
than as a guarantee, and is where the conversion runs and where the drops are accounted
for. It states roughly **1.9M assertions read in seconds** and converted to about
**1.85M sentences over ~5.4k contexts** — contexts that actually hold a sentence, where
the vocabulary names ~13.3k of them. The **~214k named terms** come out as about
**114k types**, **~19.6k predicates**, tens of thousands of individuals and those context
terms. The `lein convert` alias carries a heap that can hold a corpus; a plain `lein run`
does not.

From there, two ways in, and they are a genuine trade rather than a better and a worse.

**Through the browser**, exactly as with tiny. One load of the `units/5022` conversion
above, on the JVM's default heap: the plugin's page puts the `:ontology` profile at
about **650 s** to ready, over **~1.16M sentexes**, of which the engine's own definitional
checks refuse well under one percent — and it peaks around **5 GB**. It is browsable from
its first thousand sentexes rather than at the end, and the card's derivation cap is what
bounds chaining if you ask for it. Name a `:dir` on the card for a durable KB when RAM is
the constraint.

**This page is where this repo's OpenCyc figures live**, and a page needing one cites it
here rather than quoting a count of its own — and these are approximate on purpose. The
exact numbers move with the import profile and the plugin version, so two pages taking
their own readings disagree about a corpus neither of them names, and a figure precise to
the sentex is one nothing in this tree can reproduce.

**Or once, offline, into a store:**

```sh
cd vaelii-foreign
lein convert load ~/.vaelii/kbs/opencyc-4.0 /var/lib/vaelii/opencyc --profile ontology
```

That leaves a `records/` + `index/` pair, which this repo classifies as a `:store` and
opens **in place, in seconds, with no plugin on the classpath at all** — nothing foreign
is being read any more. Pay the load once and every session after it is instant. Two
things to know: the CLI's `--profile` defaults to `full` where the browser's card defaults
to `ontology`, and `load` finishes with an *uncapped* `forward-chain` where the card
offers a bound.

Then tick **Recover belief and the taxonomy** when you open it. Skipped, the KB is
findable by term and countable and has no type hierarchy at all — catalog.md's *What it
costs to hold* says why that is one switch and not two, and why it is the failure that
looks like success.

Heap is the other thing this corpus is sensitive to, and the numbers sit close together:
6 GB is not enough for the checked `:ontology` load, and the JVM default on a large
machine is. Neither `lein browser` nor `lein run -m vaelii.web` sets `-Xmx`, so both
get that default; a profile that pins a smaller heap wants the `:dir` instead.

## Text you exported yourself

The shipped ontology is text — one `Cx<Name>.txt` per context under `resources/kb/` — and
`export-text!` writes that same format, so a KB in a store can go back to being files an
author edits:

```sh
lein cli export /tmp/mykb --format text --starter   # premises out, one file per context
$EDITOR /tmp/mykb/CxKinship.txt                     # ordinary sentences, ordinary comments
lein cli load /tmp/mykb --dir /tmp/store            # and back in, through assert
```

In process it is `(v/export-text! kb dir)` and `(v/load-text! kb dir)`; `{:context C}` or
`{:cone C}` narrows the export to one file or to one context and everything it sees
([api.md](api.md)).

**Two wrappers say how a sentence was asserted rather than what it says.**
`(set/monotonic S)` is the known-true class: a strength is an option on the assertion, so
there is nowhere in an s-expression for it to go, and a text KB that could not say it
would round-trip every known-true premise down to a default. And because an `exceptWhen`
asserts *two* things — the rule, and the exception qualifying it — a wrapper on the
**query**, `(exceptWhen (set/monotonic Q) R)`, states the exception's own class where it
differs from the rule's. Both are peeled before anything is stored, so neither reaches a
sentence as a functor ([exceptions.md](exceptions.md)).

**This is a round trip through content, not through state.** What is written is the
*premises* — what somebody asserted — and a reload derives the rest again, so the KB that
comes back has the same beliefs at different handles. Where handle identity is what you
need (a backup, a move between stores, a corpus too big to re-derive), the pair is
`export!` / `import!` instead.

## Where a KB has to sit to be found

`~/.vaelii/kbs/<name>` needs no configuration at all: that and `./kbs` are the default
search path, and a path entry holding several KBs is probed one level down. Anywhere else
takes `VAELII_KB_PATH` or an entry in the catalog file, which is the only place a
machine's own paths live. Either way, dropping a corpus into a searched directory makes it
appear on the next page load with no restart — `sources` is recomputed per call.

## What goes wrong

Four failures, each of which reads as something other than its cause:

* **No `+with-foreign`.** The load fails with `:no-foreign-reader`, naming the kind. The
  KB is still *offered*, because "I cannot read this" is a load that says so rather than a
  KB that quietly stops being listed.
* **A stale plugin jar**, which only a snapshot build can be. The same shape of
  failure, or a namespace that is simply not there. `lein install` in the plugin again.
* **The catalog pointed at an unconverted dump.** It is not offered at all, and nothing
  says why: `classify` recognises a corpus `meta.edn`, a dump's `:format-version` and a
  `records/` + `index/` pair, and a directory with none of them is not a KB. Convert
  first.
* **A store opened without recover.** Its load finishes `:done` and stays that way, with
  0 types. This is the one to watch for, because it is the case that looks finished.

## Further

* [catalog.md](catalog.md) — sources, the search path, load progress and cancellation,
  what a loaded KB costs to hold, and switching which one the pages read.
* [foreign.md](foreign.md) — the plugin seam: one edn manifest, resolved on use, and what
  this repo promises about carrying no reader.
* [operations.md](operations.md) — the same KBs from the CLI and the daemon instead.
* [vaelii-foreign](https://github.com/vaelii/vaelii-foreign) — the plugin, and
  [its OpenCyc notes](https://github.com/vaelii/vaelii-foreign/blob/main/docs/opencyc.md)
  for the conversion pipeline: what the profiles keep, what a translation drops and why,
  and what the engine refuses that the translation did not.
