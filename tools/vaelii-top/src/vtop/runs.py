"""The run ledger: `logs/runs.tsv`, one row per check run.

`scripts/lib/runlog.sh` writes it and this reads it. The file is append-only
TSV with a header row, and the header is what a row's fields are keyed on — not
the column order — so a column added there does not need this file changed on
the same day.

Nothing here judges a run. A row says what a runner said about a revision; the
only thing this module adds is which row is the LAST one of its kind, and how
far back in the history that revision now sits.
"""

from __future__ import annotations

import re
import time
from dataclasses import dataclass
from pathlib import Path

from vtop.repo import UNCLASSIFIED

_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")


def strip_ansi(text: str) -> str:
    """A log line as text. Every runner here writes colour into its log — `lein
    lint` and `lein perf` both key colour off TERM, which survives the redirect
    into a file — so a log read back carries escapes."""
    return _ANSI_RE.sub("", text)

LEDGER = "logs/runs.tsv"


@dataclass(frozen=True)
class Check:
    """One column of the history table, and one chip in the status panel.

    `kind` and `variant` together address a row: a `:default` suite and an
    `:all` suite are separate verdicts, and so are a `:default` matrix and an
    `:all` one. A check is in this roster because it has a column; a run whose
    kind is not here is still read, and still shows in a commit's detail.
    """

    key: str
    kind: str
    variant: str
    title: str
    column: str  # the table's heading, kept short enough to fit five of them
    # The path classes (repo.classify_path) whose change can move this check's
    # answer. A commit that touched none of them leaves the check's last verdict
    # standing, which is what `inferred_runs` fills the history's blank cells
    # from. UNCLASSIFIED is added by `reads`, so a path this tool has no class
    # for moves every column.
    inputs: frozenset = frozenset()
    # Other rows that are also a run of this check, newest wins. The suite is
    # run three ways — `lein test-parallel`, `lein gate`, and once per
    # configuration inside a matrix — and the column answers "when did the suite
    # last pass", not "which command was typed". A matrix at `:all` ran
    # `:default` too, so it counts for that column as well.
    also: tuple = ()

    @property
    def keys(self) -> tuple:
        """Every `kind:variant` this column reads, most specific first."""
        return (f"{self.kind}:{self.variant}",) + self.also

    @property
    def reads(self) -> frozenset:
        """`inputs`, plus the class a path outside every known one is filed
        under. Unioned here rather than written into each roster entry, so the
        rule that an unclassified path moves every column is stated once."""
        return self.inputs | {UNCLASSIFIED}


# What each kind of check reads, as path classes. Named per kind and not once
# for all of them, because the checks do not read the same tree: `lein test`
# cannot see a docs page, `lein perf` runs no test namespace, and `lein lint`
# reads all three of docs, scripts and tools on top of the source.
#
# `scripts` is in every one of them. scripts/test-matrix.sh decides which
# configurations a matrix is, scripts/perf.sh decides which budgets perf gates
# on, and a change to either moves what the verdict beside it claims.
SUITE_READS = frozenset({"src", "test", "resources", "scripts", "project"})
PERF_READS = frozenset({"src", "resources", "bench", "scripts", "project"})
LINT_READS = frozenset(
    {
        "src", "test", "bench", "resources", "scripts",
        "docs", "tools", "prose", "lint-config", "project",
    }
)


# The five the table has columns for. Extend it here — the table, the chips and
# the legend all size themselves off this tuple, so adding a sixth is one edit.
CHECKS = (
    Check("lint", "lint", "-", "lint", "lint", inputs=LINT_READS),
    Check(
        "test", "test", ":default", "test :default", "test",
        inputs=SUITE_READS,
        also=(
            "matrix::default",
            "matrix::default owed",
            "matrix::all",
            "matrix::all owed",
        ),
    ),
    Check("perf", "perf", "-", "perf", "perf", inputs=PERF_READS),
    Check("matrix", "matrix", ":default", "matrix :default", "mx:d", inputs=SUITE_READS),
    Check("matrix-all", "matrix", ":all", "matrix :all", "mx:a", inputs=SUITE_READS),
    # A matrix over fewer configurations than the routine roster — what `lein
    # test-matrix --owed` runs, and what a hand-named list of configurations
    # runs. Its own column, because it is a weaker claim than the one beside
    # it: filed together, a cheap subset would keep hiding when the whole
    # roster last went green (scripts/test-matrix.sh decides which a run is).
    Check(
        "matrix-owed", "matrix", ":default owed", "matrix :default --owed", "mx:o",
        inputs=SUITE_READS,
    ),
    # The two selectors NO gate reaches. `:multi-jvm` forks a second JVM and
    # `:fuzz` names its own four backends, so neither `lein test`, `lein test
    # :all`, the gate nor a matrix row runs either — they are run by name or not
    # at all, which is exactly why a column for each is worth having. A change
    # to the single-writer lock, disk open/close, recovery, the daemon or the
    # CLI's `--dir` owes the first; a change to a durable file format, its
    # framing or its recovery owes the second.
    Check("multi-jvm", "test", ":multi-jvm", "test :multi-jvm", "mjvm", inputs=SUITE_READS),
    Check("fuzz", "test", ":fuzz", "test :fuzz", "fuzz", inputs=SUITE_READS),
)

# Kinds drawn as ONE MARK, never as a strip of dots. `perf` is the one: its
# forty-eight checks are each a ratio against a budget and the run gates on all
# of them together, so what the row answers is whether the engine came in under
# budget — a play, a tick or a cross. `lint` and a matrix are the other way
# round, since a lint over six of eleven checks and a matrix over three of
# fifteen configurations are partial answers a mark cannot state.
MARKED_KINDS = frozenset({"perf"})


@dataclass(frozen=True)
class Run:
    """One ledger row."""

    started: str
    epoch: float
    seconds: int
    kind: str
    variant: str
    state: str
    revision: str
    dirty: int
    subject: str
    summary: str
    log: str

    @property
    def key(self) -> str:
        return f"{self.kind}:{self.variant}"

    @property
    def title(self) -> str:
        """`lint`, or `test :default` — the variant only where there is one."""
        if self.variant in ("-", ""):
            return self.kind
        return f"{self.kind} {self.variant}"

    @property
    def over_dirt(self) -> bool:
        """The run compiled uncommitted work, so it answers for no commit.

        Worth its own flag rather than a note in the summary: a green row taken
        over a dirty tree is the one case where the verdict and the revision on
        the same row are about different trees.
        """
        return self.dirty > 0


def _to_int(value: str, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _to_float(value: str, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def parse_ledger(text: str) -> list:
    """The rows of a ledger, oldest first, skipping anything malformed.

    A short or unparseable line is dropped rather than raised on: the ledger is
    appended to by several runners at once, and a torn write is a line to
    ignore, not a reason for the screen to go away.
    """
    lines = text.splitlines()
    if not lines:
        return []
    header = lines[0].split("\t")
    if "kind" not in header:
        return []
    runs = []
    for line in lines[1:]:
        if not line.strip():
            continue
        cells = line.split("\t")
        if len(cells) < len(header):
            continue
        row = dict(zip(header, cells))
        runs.append(
            Run(
                started=row.get("started", ""),
                epoch=_to_float(row.get("epoch", "0")),
                seconds=_to_int(row.get("seconds", "0")),
                kind=row.get("kind", "?"),
                variant=row.get("variant", "-") or "-",
                state=row.get("state", "?"),
                revision=row.get("revision", ""),
                dirty=_to_int(row.get("dirty", "0")),
                subject=row.get("subject", ""),
                summary=row.get("summary", ""),
                log=row.get("log", ""),
            )
        )
    return runs


class Ledger:
    """The ledger, reloaded when the file's mtime moves.

    Reloaded rather than tailed: the file is a few hundred bytes a row and a
    repaint is seconds apart, so a whole read is a few hundred microseconds and
    cannot get out of step with a row that was rewritten. `load()` is a no-op when the
    mtime has not changed, so the common repaint touches the disk once to stat.
    """

    def __init__(self, root: Path, relative: str = LEDGER) -> None:
        self.path = root / relative
        self.runs: list = []
        self._mtime: float = -1.0
        self._by_revision: dict = {}
        self._latest: dict = {}

    def load(self) -> bool:
        """Read the ledger if it moved. True when the rows changed."""
        try:
            mtime = self.path.stat().st_mtime
        except OSError:
            if self.runs:
                self.runs, self._by_revision, self._latest = [], {}, {}
                self._mtime = -1.0
                return True
            return False
        if mtime == self._mtime:
            return False
        try:
            text = self.path.read_text(errors="replace")
        except OSError:
            return False
        self._mtime = mtime
        self.runs = parse_ledger(text)
        self._index()
        return True

    def _index(self) -> None:
        self._by_revision = {}
        self._latest = {}
        for run in self.runs:
            self._by_revision.setdefault(run.revision, []).append(run)
            # Latest by the run's OWN clock, not by where its row sits.  Append
            # order is not time order: `scripts/runlog-backfill.sh` appends rows
            # for runs from last week, and two runners appending at once
            # interleave. A `latest` that trusted the file's order would call a
            # backfilled row from Monday the newest verdict.
            seen = self._latest.get(run.key)
            if seen is None or run.epoch >= seen.epoch:
                self._latest[run.key] = run

    def latest(self, check: Check):
        """The newest run this column reads, across every kind that is one."""
        best = None
        for key in check.keys:
            run = self._latest.get(key)
            if run is not None and (best is None or run.epoch > best.epoch):
                best = run
        return best

    def at(self, revision: str) -> list:
        """Every run taken at a revision, oldest first by its own clock."""
        return sorted(self._by_revision.get(revision, ()), key=lambda run: run.epoch)

    def at_check(self, revision: str, check: Check):
        """The last run of `check` at `revision`, or None.

        The LAST and not the first: re-running a red check at the same revision
        after a fix is how it goes green, and the cell has to show the answer
        the checkout arrived at.
        """
        found = None
        keys = set(check.keys)
        for run in self._by_revision.get(revision, ()):
            if run.key not in keys:
                continue
            if found is None or run.epoch >= found.epoch:
                found = run
        return found

    def durations(self, check: Check, limit: int = 60) -> list:
        """How long the last `limit` runs of one check took, oldest first."""
        keys = set(check.keys)
        matching = sorted(
            (run for run in self.runs if run.key in keys),
            key=lambda run: run.epoch,
        )
        return [float(run.seconds) for run in matching][-limit:]

    def state_of(self, check: Check) -> str:
        run = self.latest(check)
        return run.state if run is not None else "missing"


def commit_distance(commits: list, revision: str):
    """How many commits back from HEAD a revision sits, or None when the
    history read does not reach it.

    None is a real answer and not a zero: a verdict taken before the window
    this tool reads is old, and how old is a question the window cannot answer.
    Abbreviated hashes compare by prefix in both directions, because git's
    short hash grows with the repository and a ledger row keeps whatever length
    it was written at.
    """
    if not revision:
        return None
    for index, commit in enumerate(commits):
        if commit.sha == revision or commit.sha.startswith(revision) or revision.startswith(commit.sha):
            return index
    return None


def moving_commits_since(commits: list, distance, check: Check) -> int:
    """Of the commits between a verdict and HEAD, how many moved `check`.

    The number that decides whether a stale green still means something. `src/`
    is the wrong roster for every column: a `docs/` commit leaves the suite's
    green standing and reds nothing but `lint`, and a `bench/` commit moves
    `perf` alone. Counted against what the check reads, so a verdict at HEAD
    minus five `tools/` commits reports zero rather than five.
    """
    if distance is None:
        return 0
    return sum(1 for commit in commits[:distance] if moves(commit, check))


def moves(commit, check: Check) -> bool:
    """Whether `commit` could have changed what `check` answers.

    True where the commit touched a class the check reads. A `tools/` commit
    moves `lint` and no suite; a `src/` commit moves every column.
    """
    return bool(commit.touched & check.reads)


def inferred_runs(commits: list, ledger, check: Check) -> dict:
    """The run each commit with no run of its own takes its verdict from.

    Between two commits that `check` reads, the tree `check` reads does not
    change, so one run of it answers for every commit in that stretch. The
    stretch is cut at each commit `moves` returns True for, and the run the
    whole stretch takes is the NEWEST one recorded at any commit in it — the
    same rule `at_check` follows inside one commit, for the same reason: a
    stretch re-run after a fix arrived at the second verdict.

    Keyed on the sha, and holding only the commits that ran nothing themselves.
    A commit with its own run of `check` is not in the map, because a recorded
    verdict is never replaced by an inferred one.

    The returned run's `revision` says which commit did the running, so a caller
    that wants to name the source has it without a second lookup.
    """
    if not commits:
        return {}
    inferred = {}
    stretch = []  # indexes into `commits`, oldest first
    # `commits` is newest first, so the walk runs backwards over it: a stretch
    # opens at the commit that moved the check and closes at the next one.
    for index in range(len(commits) - 1, -1, -1):
        if stretch and moves(commits[index], check):
            _fill(inferred, commits, ledger, check, stretch)
            stretch = []
        stretch.append(index)
    _fill(inferred, commits, ledger, check, stretch)
    return inferred


def _fill(inferred: dict, commits: list, ledger, check: Check, stretch: list) -> None:
    """One stretch's blank cells, filled from the newest run inside it."""
    if len(stretch) < 2:
        return  # one commit alone has nothing to take a verdict from
    runs = [ledger.at_check(commits[index].sha, check) for index in stretch]
    best = None
    for run in runs:
        # A run taken over uncommitted work answers for no commit, so it cannot
        # answer for a second one either. It stays in its own cell, where the
        # dirt mark is beside it, and is never the source of an inferred cell.
        if run is None or run.over_dirt:
            continue
        if best is None or run.epoch >= best.epoch:
            best = run
    if best is None:
        return
    for index, run in zip(stretch, runs):
        if run is None:
            inferred[commits[index].sha] = best


def inferred_by_check(commits: list, ledger) -> dict:
    """`inferred_runs` for every column of the history, keyed on the check.

    Computed once per reload rather than per repaint: the history draws eight
    columns over as many rows as fit, and re-deriving the stretches on every
    frame would read the ledger a thousand times a second.
    """
    return {check.key: inferred_runs(commits, ledger, check) for check in CHECKS}


def ago(epoch: float, now: float | None = None) -> str:
    """A compact "how long since", in the largest unit that still reads."""
    if not epoch:
        return "—"
    delta = max(0.0, (now if now is not None else time.time()) - epoch)
    if delta < 90:
        return f"{int(delta)}s"
    if delta < 5400:
        return f"{int(delta / 60)}m"
    if delta < 172800:
        return f"{int(delta / 3600)}h"
    return f"{int(delta / 86400)}d"


def hms(seconds: float) -> str:
    """A duration as the console scripts print one: 41s, 8m12s, 1h04m."""
    seconds = int(max(0, seconds))
    if seconds < 60:
        return f"{seconds}s"
    if seconds < 3600:
        return f"{seconds // 60}m{seconds % 60:02d}s"
    return f"{seconds // 3600}h{(seconds % 3600) // 60:02d}m"


@dataclass(frozen=True)
class Component:
    """One part of a run: a lint check, a perf check, a matrix configuration.

    `group` is what a strip of them is divided on — the matrix's `backend` and
    `sweep` halves. Empty where a run has one kind of part.
    """

    name: str
    state: str
    group: str = ""


# `  <label>   ✓ <summary>` / `  <label>   ✗ FAILED` — scripts/lint.sh indents a
# check row by two and nothing else it prints, which is the contract gate.sh
# reads its roster back on. Keyed on the indentation rather than on the wording,
# so a rewritten summary line does not move it.
_LINT_ROW = re.compile(r"^  ([a-z][a-z0-9-]*) +([\u2713\u2717])")

# Parsed components by (path, mtime). The history table asks for a run's parts
# once per visible commit per check, which is a hundred and more reads a
# repaint; a log does not change after the run that wrote it finished, so the
# mtime is the whole of the invalidation.
_COMPONENT_CACHE: dict = {}
_COMPONENT_CACHE_MAX = 400


def _cached(path: Path, build):
    try:
        key = (str(path), path.stat().st_mtime)
    except OSError:
        return []
    hit = _COMPONENT_CACHE.get(key)
    if hit is not None:
        return hit
    parts = build()
    if len(_COMPONENT_CACHE) >= _COMPONENT_CACHE_MAX:
        _COMPONENT_CACHE.clear()
    _COMPONENT_CACHE[key] = parts
    return parts


def _log_components(root: Path, log: str, pattern, states: dict) -> list:
    """The component rows of a run's log, in the order the run printed them.

    Read back out of the log rather than recorded into the ledger: the runner
    already prints one row per check, and a second copy in the row would be a
    roster to keep in step with no one comparing the two. The order is the
    runner's, which makes a strip positionally stable — the same check is the
    same cell in every run of it.
    """
    if not log:
        return []
    path = root / log
    if not path.is_file():
        return []

    def build():
        try:
            text = path.read_text(errors="replace")
        except OSError:
            return []
        out = []
        for line in strip_ansi(text).splitlines():
            match = pattern.match(line)
            if match is not None:
                out.append(
                    Component(match.group(1), states.get(match.group(2), "missing"))
                )
        return out

    return _cached(path, build)


# `15 of 15 configurations, roster full, 0 failed, 0 skipped` —
# scripts/test-matrix.sh's own summary line. The second number is the roster the
# run was a subset of, which is what says how many configurations did NOT run.
# A backfilled row has no such number, and then there is nothing to grey out.
_MATRIX_OF = re.compile(r"(\d+) of (\d+) configurations")


def roster_size(run) -> int:
    """How many parts the run COULD have had, where the run says so.

    Only a matrix says: `--owed` runs three configurations of fifteen, and the
    twelve that sat out are a fact about the verdict — a green over three is not
    a green over fifteen. Zero where the run states no roster, which is every
    kind but the matrix and every backfilled row.
    """
    match = _MATRIX_OF.search(run.summary or "")
    return int(match.group(2)) if match else 0


def run_components(root: Path, run) -> list:
    """What a run was made of, or [] where it was made of one thing.

    A verdict is one mark over as many as forty-eight checks, and "48 check(s)
    ok" says how many without saying which. The components say it in the row.
    """
    if run.kind == "matrix":
        configs = read_matrix_summary(root, run.log)
        parts = [
            Component(
                config.get("config", "?"),
                # A configuration that was skipped under `--fail-fast`, or never
                # started, is neither a pass nor a failure.
                config.get("state", "")
                if config.get("state") in ("passed", "failed")
                else "missing",
                config.get("kind", ""),
            )
            for config in configs
        ]
        # Grouped and sorted rather than left in finish order, which is longest
        # first and therefore a function of how loaded the box was. Backends
        # then sweeps, each alphabetical, so a configuration holds the same cell
        # in every matrix and two rows can be read against each other.
        return sorted(parts, key=lambda c: (c.group != "backend", c.name))
    if run.kind == "lint":
        return _log_components(
            root, run.log, _LINT_ROW, {"\u2713": "passed", "\u2717": "failed"}
        )
    # `perf` is in MARKED_KINDS and draws a mark, so its check rows are never
    # read: a run of it is one verdict about one budget.
    return []


def read_matrix_summary(root: Path, log: str) -> list:
    """The per-configuration rows of a matrix run, for the detail view.

    A matrix row in the ledger names the run's DIRECTORY, and
    `scripts/test-matrix.sh` already writes `summary.tsv` in it with one row per
    configuration. Read back rather than duplicated into the ledger: fifteen
    rows per matrix in a file that holds one row per run would make the ledger
    something to parse rather than something to read.
    """
    if not log:
        return []
    path = root / log / "summary.tsv"

    def build():
        try:
            text = path.read_text(errors="replace")
        except OSError:
            return []
        lines = [line for line in text.splitlines() if line.strip()]
        if len(lines) < 2:
            return []
        header = lines[0].split("\t")
        return [dict(zip(header, line.split("\t"))) for line in lines[1:]]

    return _cached(path, build)
