# vaelii-top

The checkout in a btop-style terminal UI: what the repository is right now
above, the git history with one column per check below it — which revision
`lint`, the suite, `perf` and the two matrix selectors last ran at, and what
each of them said — then every JVM running on the machine with the run it
belongs to, and at the bottom the checks running right now, one part to a
braille column.

```
vaelii-top                 # the UI
vaelii-top --once          # the same five verdicts as lines, then exit
vaelii-top --theme gruvbox_dark   # any installed btop theme
```

## What it reads

Nothing is computed by running anything: the tool reads `git`, `ps` and two
files it never writes.

- **`logs/runs.tsv`** — the run ledger, one row per check run, written by
  `scripts/lib/runlog.sh` as each runner exits. `lein lint`, `lein
  test-parallel` (so `lein gate` too), `lein perf` and `lein test-matrix` each
  append one row naming the revision they started at, the wall clock, their own
  closing figures and the verdict.
- **`logs/test-matrix/run-*/summary.tsv`** — the per-configuration detail a
  matrix already writes, read back for the detail view rather than copied into
  the ledger.

A checkout whose ledger is empty is not one that has never been checked: it is
one whose runs pre-date the ledger. `bash scripts/runlog-backfill.sh` reads the
gate and matrix artifacts already on disk and appends the rows nothing wrote at
the time. It is idempotent, so a second pass adds nothing.

## The screen

The **`¹repo` panel** carries the version, the branch, the revision and its
subject, how much is uncommitted (dirt under `src/` or `test/` called out on
its own, because that is the dirt a verdict is taken over), the distance from
the upstream, the tree's counts, and a braille graph of commits per HOUR over
whatever the history window spans, with three clock marks under it. Per hour
rather than per day because a day is one bar and a session is the unit of work
here: an afternoon of six commits and a week of six draw the same daily bar.
Two hours to a braille cell, since a cell is two dot columns wide, so a
126-column terminal holds about ten days.

The **`²runs` panel** is the last run of each check, one row apiece: the
verdict, a bar whose LENGTH is how fresh the run is and whose COLOUR is how
stale, the revision it was taken at, how far back that now sits, the run's own
figures, its wall clock and its age. Its own tile rather than a block above the
history, because "is this tree checked" is a question read on its own — and
because the rows in a tile of their own never scroll away.

**The bar counts the commits that moved THIS CHECK**, not the commits since.
The two numbers are `12 back · 3 it reads`: twelve commits stand between the
verdict and HEAD, and three of them touched something the check reads. A row
whose second number is zero says `12 back · reads HEAD` and fills its bar green,
because the tree that check sees has not moved and the verdict still answers for
it. Counting every commit reported a green `test` taken at HEAD as five commits
stale after five `tools/` commits, which is a claim about a tree the suite never
opens. The roster of what each check reads is the one the history's inferred
cells use, below.

Beside the revision, a **`±`** marks a run taken over uncommitted work under
`src/` or `test/`. It has a column of its own because it is a fact about which
TREE the verdict is about rather than about the verdict: a green over a dirty
tree answers for no commit at all. The column is there whether or not the mark
is, so everything after it lines up down the tile.

A run made of parts carries **one braille dot per part**, packed eight to a
cell — `lint`'s twelve checks, a matrix's fifteen configurations. Green for the
ones that passed, red for the ones that failed, grey for the ones that did not
run: a `--owed` matrix over three of fifteen leaves twelve grey dots. Each
colour starts its own cell, since a cell takes one colour and a mixed one would
have to lie about a dot.

Fifteen dots are two cells, so the strip sits beside the run's sentence rather
than replacing it: the strip says the shape, the sentence says the figures. The
dots are counted out of the run's own artifacts — `summary.tsv` for a matrix,
the check rows of the log for `lint` — so they carry what those wrote rather
than a second roster kept in step with nothing.

`perf` draws a mark and no strip. Its forty-eight checks are each a ratio
against a budget and the run gates on all of them together, so what the row
answers is whether the engine came in under budget: `▶` while it runs, then `✓`
or `✗`. A lint over six of twelve checks and a matrix over three of fifteen
configurations are partial answers no mark can state, which is why those two
count in dots.

**A run under way takes over its row**, with blue dots for the parts running
right now: a lint six checks in reads six green, one blue, four grey, and the
blue moves. The ledger is written by a runner as it exits, so a run in progress
is in none of it — what it does leave is its log. How far in comes out of
whatever that runner streams: `lint` writes a row per check as each finishes,
`perf` a `perf-progress` marker per check with its verdicts held to the end (so
its bar fills while its mark stays `▶`), a matrix one log per configuration, and
a sharded suite one log per shard ending in its exit marker.
The bar fills with the parts FINISHED, since a matrix that has opened all
fifteen logs and answered for none of them is at the beginning.

A run is under way when it has a part unfinished, and then either the pid that
owns its log still exists or it has written recently. The pid is a **positive**
signal and never a negative one: `lint`, `perf` and a selector run each name
their log after their own pid, so those are settled without guessing, while a
matrix's directory is named after a shell that is gone by the time its
configurations run — asking the kernel about that one reports a live run as
dead. Where no live owner is found, silence for three minutes makes a run
**stalled**: the row turns amber and says how long it has been quiet, which is
what a matrix whose shells are alive and whose JVMs have died looks like from
the outside. Half an hour of silence and it goes, so a killed run cannot keep
the last real verdict off its row. (`lein test :fuzz` writes almost nothing for
ten minutes and is working the whole time, which is why a live owner outranks
the clock.) The `²runs` edge counts the two apart. A live run holds the row only
while it is the newest thing that check has: a recorded run that STARTED later
takes the row back, so a lint that died at noon does not keep the row from the
lint that passed at half past.

`lein test-matrix` and `lein test-parallel` each write a one-line plan into their
run directory as they start — the selector, the roster, how many configurations
or shards. A run that has started otherwise says nothing about itself until it
ends, so a `--owed` matrix of three could not be told from a `full` run whose
other twelve had not started, and it showed in the wrong column until it
finished.

The **`³history` panel** is what has landed since: one row per commit, one cell
per check. A commit that touched neither `src/` nor `test/` is drawn quieter,
because it cannot have moved a verdict — and the checks it could not have moved
show their verdict anyway, inferred, which is the section below.

A cell is the same packed strip the runs tile draws, so a matrix that failed
four of fifteen reads as `⣿⠇⡇` — four red dots, then eleven green — without
opening anything. Columns are as wide as the rows on screen need and no wider,
so they shift as you scroll.

**The heading is a row too, and it is where the selection starts.** It carries
no commit, so `enter` and `o` have nothing to open there — which is the point:
the tool opens with the table to read rather than with HEAD picked out that
nobody asked for. `up` from the newest commit returns to it, `home` goes
straight there, and it is the one row that never scrolls away, so a selection
parked on it cannot go off screen while you read something else. The selection
bar is a neutral tint rather than a colour, red on this screen being a failed
verdict rather than a cursor.

A **`±`** after a cell marks a run taken over uncommitted work under `src/` or
`test/`, the same mark the `²runs` tile gives a column of its own. The history
has no column to spare, so the mark rides the cell — and it has to be there,
because that verdict is about a tree no commit holds and nothing else in the row
says so. Such a run is also refused as the source of an inferred cell, so
without the mark a reader sees a green at one commit, none at the next, and
nothing that explains the gap.

**Two vocabularies, and the screen keeps them apart.** A dot COUNTS: one dot is
one part, and a cell is eight of them. A run with nothing to count draws a MARK
instead — `✓` passed, `✗` failed, `○` started and reached no verdict, `▶` under
way, `⋅` never ran here — because a glyph that counts nothing must not be read
as a quantity. `lein test :fuzz` and `lein test :multi-jvm` are one JVM running
one selector, so they have no parts and draw marks, and `perf` draws one
because its forty-eight checks are one budget; `⋅` is the smallest of them
because it is the commonest, and a column of them has to read as background. The `³history` edge carries a legend for each: the marks, and
what one full cell of dots is worth. Neither leans on colour alone, which says
nothing in a screenshot, down a mono terminal, or to a reader who cannot tell
the red from the green.

**A commit with no run of its own can still have an answer.** A check reads part
of the tree and not all of it — `lein test` cannot see a docs page, `lein perf`
runs no test namespace — so where nothing a check reads changed between a commit
and one that did run it, the two trees that check sees are the SAME TREE, and
the verdict is the same verdict. Such a cell draws the glyph the run drew, **in
the never-ran grey** — the shape is the verdict and the colour says no run
happened at this commit. Five `tools/` commits under a green `test` therefore
read as five grey ticks, and the third legend on the `³history` edge names them.

Grey and not a third shade of green, so the screen keeps colour for what was
measured: green, red and amber are verdicts a runner reached, and a cell no
runner reached may not wear one. A `✓` in grey and a `✗` in grey still read
apart, because the glyphs already carry the verdict without leaning on colour.

`runs.CHECKS` holds a roster of path classes per check, and
`repo.classify_path` files a commit's files into those classes:

| | reads |
|---|---|
| `test` `mx:d` `mx:a` `mx:o` `mjvm` `fuzz` | `src/` `test/` `resources/` `scripts/` `project.clj` |
| `perf` | `src/` `resources/` `bench/` `scripts/` `project.clj` |
| `lint` | those, plus `docs/` `tools/` `.clj-kondo/` and the root markdown |

`scripts/` is in every one of them, because `scripts/test-matrix.sh` decides
which configurations a matrix is and `scripts/perf.sh` decides which budgets
perf gates on — a change to either moves what the verdict beside it claims. A
path outside every class, and a merge commit (which lists no names under `git
log --name-only`), is filed as one every check reads, so an unfamiliar change
infers nothing.

Four rules hold the inference down:

- **A recorded verdict is never replaced by an inferred one.** A run under way
  wins, then a run recorded at that commit, then the inference, then `⋅`.
- **A stretch takes its newest run**, the same rule one commit's cell follows:
  a stretch re-run after a fix arrived at the second verdict.
- **A run taken over uncommitted work is never a source.** It answers for no
  commit, so it cannot answer for a second one either; it stays in its own cell.
- **A stretch of one infers nothing**, and neither does one with no run in it.

The inference runs backwards over the history once per check, cutting the
history at each commit that check reads, and costs 1.4ms over two hundred
commits and eight columns. It is recomputed when the checkout is re-read or when
the ledger's rows move, not per frame.

`enter` on a commit names the source: a line per inferred column with the
verdict, the revision that ran it and how long ago. The `²runs` tile and
`--once` are untouched by any of this — both answer where a check last RAN, and
a cell nothing ran in is not an answer to that question.

The `test` column answers **when the suite last passed**, not which command was
typed, so it takes the newest of every way the suite gets run: `lein
test-parallel`, `lein gate` (which runs it), and a matrix, where each
configuration is the suite again. A row filled by a matrix says so. A matrix at
`:all` ran `:default` too, so it counts for that column as well. A plain `lein
test` writes no log of its own and so cannot be recorded — `lein test-parallel
--jobs 1` is the recorded single-JVM run.

`mjvm` and `fuzz` are the two selectors NO gate reaches: `:multi-jvm` forks a
second JVM and `:fuzz` names its own four backends, so neither `lein test`,
`lein test :all`, `lein gate` nor a matrix row runs either. They are run by name
(`lein test-multi-jvm`, `lein test-fuzz`) or not at all, which is why a column
for each is worth having.

`mx:o` is a matrix over fewer configurations than the routine roster — what
`lein test-matrix --owed` runs, and what a hand-named list of configurations
runs. It has a column of its own because it is a weaker claim than `mx:d`
beside it: filed together, a cheap subset would keep hiding when the whole
roster last went green, which is the question the row exists to answer. Which
one a run was is decided on what it RAN, so an `--owed` run that owed
everything is filed as the matrix it was.

The **`⁴jvms` panel** is every java process on the machine: the pid, what it is
running, the run it belongs to, a bar for CPU and one for memory, and how long
it has been up. A row is one JVM and not one invocation, because `lein` is two
of them — a launcher that holds 130 MB doing nothing and the JVM it trampolines
into — and a matrix runs fifteen pairs.

What a JVM is DOING is not on its own command line: the work runs with a
classpath and a temporary `form-init` file for arguments, and the task name is
two processes up. So the tool reads the process table once for the parent links
and again for the command lines of the java processes and their ancestors, and
takes the first answer of: the `lein` task above it, the script above that
(`scripts/lint.sh`, a sibling repo's `run-vaelii.sh`), or the profile it
compiles into.

Which RUN a JVM belongs to is matched both ways round, against the pid each
live run's log is named after. `lein lint` runs `scripts/lint.sh`, so the shell
that owns the log is a child of the launcher JVM and no walk up from the JVM
reaches it; the process group holds the whole invocation either way.

Which PART of that run is a second question, and for a matrix it is the one
worth answering: thirteen JVMs all belong to `matrix :default`, and a column
repeating the run's progress on every row of them says nothing about any row.
Nothing on a command line answers it — a configuration is chosen by the
environment variables `scripts/test-matrix.sh` passes its subshell, and an
environment never reaches a command line. So the script writes
`configs.tsv` into its run directory as each configuration launches, naming the
process group its subshell was put in; `set -m` gives each configuration a group
of its own, and the launcher JVM and the project JVM it trampolines into both
carry it, so one lookup names both. A row then reads `matrix :default —
disk-log`. A run from before the file was written, or one whose parts are not
separate processes, falls back to the run and its progress.

A JVM started from this checkout is drawn at full weight. One that only has
`src/` on its classpath — a sibling repo's bench run, which resolves this
engine through its live source — says `reads this checkout` and is dimmed:
those are not your runs, and they are on the same ten cores. The CPU bar is a
share of the whole machine while the figure beside it is percent of one core,
so a shard JVM at 380% draws under half a bar on ten cores and still says 380.
The memory bar is against `-Xmx` where the command line gives one and against
physical memory where it does not. The tile's edge carries what the JVMs cost
together and the machine's load average, because eight JVMs at 40% apiece under
a load of 18 says the box is carrying something none of the rows is.

The **`⁵live` panel** is the checks running RIGHT NOW, and the only tile whose
content changes between one repaint and the next. A part gets a whole COLUMN
here — two stacked braille cells, eight dot rows, filled from the bottom —
against the eighth of a cell it gets in the history, so a run you are waiting on
takes eight times the width and twice the height of a commit from last week:

```
  mx:d  matrix :default   ⣿⣿⣿⣿⣶⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀   4 of 15 done
        22d8b30e          ⣿⣿⣿⣿⣿⣤⣀⣀⣀⣀⣀⣀⣀⣀⣀   12m04s
```

A full column is a part with a verdict, green or red. The baseline row is a part
not started, which holds the column's width and marks the slot. A column between
the two is a part in flight, drawn moving: a part under way has no progress to
report — a matrix configuration says nothing at all between its first line and
its last — so the column says "in flight" rather than a fraction it does not
know, and the offset per column makes the block of running parts read as one
movement across.

One part to a column also keeps the ORDER the run finished its parts in, which
the packed strip gives up: a braille cell takes one colour, so a packed strip
has to group the passes and the failures apart, while a column is one part and
can be that part's own colour wherever the part sits.

A run under way starts at HEAD or near it, so these bars are generally the top
rows of the `³history` being filled in — the same parts and the same colours, at
a size you can read from across the room. The heading on the left is the history
column the run will land in, and the revision under it is the one the run
started at, so the correspondence is on the row. A run with nothing to count
(`lein test :fuzz`, `lein test :multi-jvm`) draws its mark instead, because a
bar chart of one column states a quantity that is not there.

**`enter`, or a click on the row**, opens every run taken at the selected
commit: its figures, its log tail, and for a matrix the per-configuration rows
`summary.tsv` holds. The tail is shown for a passing run too — a green over a
roster that quietly went short is the case a verdict cannot show you, and the
log is what says which checks ran. `o` hands the newest log at that commit to
`$PAGER`, for when a tail is not enough. `r` re-reads. `q` quits, and so does
`Ctrl-C` — from any screen, however many times it is pressed.

Each tile hides on its own number — `1` repo, `2` runs, `3` history, `4` jvms,
`5` live — and the lowest one still showing takes the room the hidden ones left.
Hide all five and the screen carries a menu of the tiles and their numbers instead,
because a binding that hid the last tile is otherwise one nothing on the screen
can tell you about.

`--once` prints the five verdicts as lines and exits non-zero unless every one
of them is a pass, at HEAD, over a clean tree — so a script can gate on it.

## Installing

Python 3.9 or newer, and [textual](https://textual.textualize.io/).

```
cd tools/vaelii-top
python3 -m venv .venv
.venv/bin/pip install -e .
.venv/bin/vaelii-top
```

`pipx install ./tools/vaelii-top` works too, and puts `vaelii-top` on PATH. The
tool finds its checkout by walking up from the working directory to the nearest
`project.clj` that names this project; `--repo <path>` names one instead.

There is no `lein` alias for it on purpose: `lein shell` pipes the task's
stdout, and a UI that repaints needs a terminal on the other end.

## Where it came from

The drawing — the rounded panels, the `┐segment┌` edge labels, the meters and
the braille graphs — is jstacks' `theme.py` (`src/jstacks/theme.py` in that
project), kept close enough to diff against it. A fix to an edge or a meter belongs in
both. The colours that carry meaning are this tool's own (`colors.py`): green
is a pass and red a failure whatever btop theme is loaded.

The DEFAULT palette has one value jstacks does not. `selected_bg` is a neutral
tint here rather than jstacks' `#6a2f2f`, because red on this screen is a failed
verdict: a red selection bar drew a red band across a row of green cells and
said nothing about any of them. A btop theme that defines its own `selected_bg`
still wins, the way every other palette value does.
