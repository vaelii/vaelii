# 26. File layout

- **Covers:** where a KB file goes, the header comment every file opens with, the
  term-centric block order inside a file, the two strength spellings a file uses, and the
  `;;` note that names which **state it once** exception a redundant sentence takes.
- **Not here:** what a term's block contains → [ch. 6](06-definitional-block.md); the
  exceptions themselves → [ch. 4](04-economy.md); which context a theory belongs in →
  [ch. 23](23-contexts.md); the review a file change goes through →
  [ch. 28](28-vocab-pr.md).
- **Assumes:** [ch. 4](04-economy.md), [ch. 6](06-definitional-block.md),
  [ch. 23](23-contexts.md).

A KB file is plain text: one s-expression per sentence, with `;;` line comments and blank
lines between them. The loader reads it with `clojure.edn`, so a file is data and runs no
code. Two directories hold the shipped files. `resources/kb/upper/` holds the upper
ontology, and every file there loads into CxUniverse. `resources/kb/middle/` holds the
theories, and each file there is one context, named by its file name.

## Where a file goes

**Practice.** Put a domain's definitional vocabulary in an upper file named for the
domain, and put a theory (rules, defaults, claims about kinds) in a middle file named
`Cx<Name>.txt`, one context per file. Put your own vocabulary in a context of your own,
not in CxUniverse. Put individuals and contingent facts in a context below CxWell, never in
a shipped file.

**Example.** `CxKinship.txt` opens with the two edges that place its context:

```clojure
(genlCx CxKinship CxUniverse)
(genlCx CxWell CxKinship)
```

The first edge lets the theory read the upper ontology. The second edge lets every
context below CxWell read the theory.

**Why.**

- Logical: a sentence holds in exactly one context, and a reader sees its own context
  plus that context's `genlCx` ancestor set. A file named for its context makes the
  context of every sentence in it a fact a reader can see from the file name.
- Engine: the loader discovers every `.txt` file in each layer on the classpath, so a new
  file needs no code change. `vaelii.host.sync/sync!` makes the premises of CxUniverse
  and of each shipped middle context about the engine's own terms exactly what the
  shipped files produce. A premise an author adds to one of those contexts that names only
  shipped terms is retracted at the next sync. A context of the author's own is outside
  what sync reads, so its content stays.
- Maintenance: a theory in its own file can be opted into by one context and left out of
  another, as
  `CxNormalPhysicalConditions` is: CxWell does not see it, so a story set on Mars reads no
  room-temperature states of matter.

**Why not the other ways.** Appending a theory to an upper file puts its rules in
CxUniverse, where every context that sees CxUniverse reads them and none can opt out. Writing
contingent facts into a shipped file makes the shipped schema assert things about
particular individuals, which every KB built from the schema then holds.

**Audit.** For each new file, confirm the layer from its content: definitional
vocabulary in `upper/`, a theory in `middle/` with its `genlCx` edges in the file. Run
`git grep -n '^(genlCx' resources/kb/middle/<file>` and check each edge names the file's
own context.

## The header comment

**Practice.** Open every file with a `;;` block that names the file, says what it holds,
and says where it loads: into CxUniverse for an upper file, or which contexts the theory
sees and which see it for a middle file. Where the file makes a choice a reader would not
expect, the header states the choice and its reason.

**Example.** `CxNormalPhysicalConditions.txt` opens:

```clojure
;; CxNormalPhysicalConditions — the states of matter of stuff at ordinary room temperature
;; and pressure, in the real world. Sees CxRealWorld, so it inherits the whole shared
;; ontology and excludes every fiction. CxWell does not see it, so the everyday contexts
;; below CxWell assume no temperature and serve a story set on Mars as well as one set in
;; a kitchen. A context opts in by placing itself under this one, and a context under
;; both CxWell and this one reads the everyday theories at room temperature.
```

**Why.** The engine reads none of the header, so the header carries nothing the KB
needs. The header serves the reviewer: the context topology of a middle file decides what
every rule in it can reach, and a reviewer who reads the topology first reads each rule
with the right ancestor set in mind. A header that states the file's scope also tells the
next author whether a new term belongs in the file.

**Why not the other ways.** A file with no header leaves the reviewer to reconstruct the
context's position from its `genlCx` sentences, and leaves the reason for an opt-in
position (such as CxNormalPhysicalConditions sitting outside CxWell) unstated anywhere.

**Audit.** Each file's first lines name the file, its content and its context position.
Read `head -8` of every changed file.

## Term-centric blocks

**Practice.** Group every sentence about one term into one block: its `comment`, its
example comments, its metatype or arity class, its `genl` edges, each `arg`, its
separations and overlaps, its relation properties, and its cross-references. Run the
blocks in natural sort order by term. In a middle file, put the `genlCx` edges first.

**Example.** `life.txt` holds `motherOf`'s block together:

```clojure
(comment motherOf
         "(motherOf ?child ?mother) means ?mother is a mother of ?child, by blood or by choice. The child is the first argument. One child may have more than one mother.")
(set/monotonic (instance_relation_predicate motherOf))
(arg motherOf 1 causal)
(arg motherOf 2 causal)
(generic_kinship_predicate motherOf)
```

**Why.**

- Engine: the loader (`text/load-entries!`) is order-insensitive. A sentence refused
  because content further down the list has not arrived yet is retried, and retry rounds
  run while each round makes progress. The loader moves every `genlCx` sentence to the
  front, because a firing with no placement context is dropped rather than refused and
  retrying cannot recover a dropped firing. File order therefore changes nothing the KB
  believes, which is what lets a file be ordered for its reader.
- Review: **no naked terms** asks whether a term has its whole definitional block, and
  **match the siblings** compares a term with its neighbours. With one block per term,
  each check reads one place in the file. A missing `arg` shows as a gap in a block of
  six lines.
- Maintenance: removing or renaming a term edits one block, and the diff of a vocabulary
  change shows each term's block whole.

**Why not the other ways.** Grouping by sentence kind (every `genl` together, then every
`arg`) spreads one term's block over the whole file, so a term with no `arg` at one
position is visible only to a reader who collects the block by hand. Ordering by
dependency (each sentence after the sentences it rests on) is unnecessary because the
loader retries, and it scatters a term's block across the file as well.

**Audit.** For each new or changed term, `git grep -n '<term>' <file>` returns one
contiguous run of lines, apart from mentions inside other terms' blocks.

## The two strength and storage spellings

**Practice.** Write a known-true sentence as `(set/monotonic S)`. Write a sentence that
is stored and never believed as `(set/inert S)`. Leave a default sentence bare.

**Example.** `CxRealWorld.txt` restates a separation at the monotonic strength:

```clojure
(set/monotonic (disjoint animal vehicle))
```

**Why.** The two wrappers are the text format's spelling of the assert options:
`(set/monotonic S)` asserts `S` with `{:strength :monotonic}`, and `(set/inert S)` stores
`S` through `assert-inert`. The format has no other place to write an option, so the
wrapper is how a file states the strength chapter 24 asks for.

**Why not the other ways.** Leaving a known-true sentence bare stores it at `:default`,
and a default loses a clash to any monotonic contrary. `set/inert` and `set/inertRule`
are different things: `set/inertRule` stores a believed rule that never fires, while
`(set/inert S)` stores a sentex nothing believes.

**Audit.** For every bare sentence in a changed block, decide its strength by
[ch. 24](24-strength.md); a definitional sentence that no fiction contradicts carries
`set/monotonic`.

## A note that names the exception

*The file-level form of **state it once***

**Practice.** When a block states a sentence the KB already derives, put a `;;` note on
the line above it that names which **state it once** exception applies, implementation or
documentation, and gives the reason in one sentence. When the note records a limit of how
the engine carries out a term's meaning, state it as an `implementationNote` fact in the
term's block instead of a `;;` line.

**Example.** `core.txt` states two edges a declaration elsewhere installs, and its note
says why the sentences exist:

```clojure
;; A separating declaration installs its parts' taxonomy edges and stores no genl sentence, so
;; the two edges below are stated beside (separating biological organism body_part) in
;; abstract.txt and (separating organism animal plant) in organism.txt.
(genl organism biological)
(genl animal organism)
```

An implementation limit stated as a fact, from `abstract.txt`:

```clojure
(implementationNote subSituationOf "No rule concludes the temporal containment of a part in its whole. The upper ontology has no relation for one time falling within another that covers an intermittent time.")
```

**Why.**

- Logical: a stated sentence that the KB also derives is a second source for one claim.
  When the facts it follows from change, the stated copy stays and asserts something no
  author chose. The note tells the next author that the copy is intended and which
  condition keeps it.
- Engine: the engine reads neither the `;;` note nor an `implementationNote`; nothing in
  the engine reads an `implementationNote` and it draws no inference. An
  `implementationNote` is still a sentex, so it is queried and retracted like any fact,
  and a `;;` line is neither.
- Review: `kb-integrity`'s `:derivable-stated-edge` category reports a stated `genl` or
  `disjoint` that still holds with that statement removed. A reviewer reads each finding
  against the note above the sentence. A finding with a note naming its exception is
  settled; a finding with no note is a redundancy to drop.

**Why not the other ways.** A redundant sentence with no note reads to the next reviewer
as an oversight, and dropping it may remove the one sentence an engine path reads. A note
that says the sentence is redundant without naming the exception leaves the reviewer
unable to tell whether the reason still holds after an engine change.

**Audit.** Run `kb-integrity` over the new terms with `:categories
#{:derivable-stated-edge}`. Every finding either goes, or has a `;;` note above it naming
the implementation or the documentation exception.
