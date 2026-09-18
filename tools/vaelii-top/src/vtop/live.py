"""Runs that have not finished: what is going on right now, and how far in.

The ledger is written by a runner as it EXITS, so a run under way is in none of
it. What a live run does leave is its log — `scripts/lib/runlog.sh`'s writers all
open theirs at the start — and the log carries the parts that have finished so
far. So a log with no ledger row, written by a process still alive, is a run in
progress, and reading it says which of its parts are done, which one is in
flight, and how many are still to come.

Nothing here writes, waits or signals. `os.kill(pid, 0)` asks the kernel whether
a pid exists and sends nothing; a log whose pid has gone is a run that died
without finishing, and reads as neither live nor recorded.

Each kind is read from what its runner happens to stream, so they do not all say
the same amount:

  lint    one row per check, as each finishes — verdicts and all
  perf    a `perf-progress k/total` marker per check, verdicts held to the end,
          so a check that has run is under way rather than judged
  matrix  one log per configuration, each carrying clojure.test's own totals
          when that configuration is done
  test    one log per shard, each ending in the `SHARD-EXIT:<code>` marker
          `scripts/test-parallel.sh` reads its verdict from
"""

from __future__ import annotations

import os
import re
import time
from dataclasses import dataclass, field
from pathlib import Path

from vtop.runs import Component, strip_ansi

# How much of a live log to read. A shard log runs to a megabyte on a red run
# and the interesting lines are at the end, so the tail is what gets parsed —
# and it is a tail rather than a line count because the parse is by regex over
# whole lines either way.
TAIL_BYTES = 256 * 1024

# A run with something unfinished and no write for this long is one that died:
# killed, crashed, or its terminal closed. Generous, because the quietest thing
# here is a matrix configuration, which can spend minutes inside one namespace
# without a line — and a run dropped off the tile mid-suite is worse than a dead
# one lingering for three minutes.
ACTIVE_SECONDS = 180

# A run with something unfinished and no write for longer than ACTIVE_SECONDS is
# STALLED, and is shown as that rather than dropped: a matrix whose shells are
# alive and whose JVMs are gone has told you nothing for twenty minutes, which
# is the thing you most want to know and the thing hiding it takes away. Past
# this second bound it goes, because a run that was killed an hour ago must not
# keep the last real verdict off the row.
STALLED_SECONDS = 30 * 60

_RUN_PID = re.compile(r"run-(\d+)")
# `# <name> at <rev> — <state> — <date>`, scripts/lib/revision.sh's stamp, which
# every one of these logs opens with.
_STAMP_REV = re.compile(r"^# \S+.* at ([0-9a-f]{6,}) ")
_STAMP_DATE = re.compile(r"(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})")
_STAMP_DIRTY = re.compile(r"tree DIRTY: (\d+) uncommitted")
_RAN = re.compile(r"^Ran \d+ tests containing \d+ assertions")
_COUNTS = re.compile(r"^(\d+) failures, (\d+) errors")
_SHARD_EXIT = re.compile(r"^SHARD-EXIT:(\d+)")
# `scripts/test-matrix.sh` appends this to each configuration's log as that
# configuration's shell exits, and reads it back at line 613 to file the row.
# The live tile reads the same marker, so a configuration is done here exactly
# when it is done there.
_MATRIX_EXIT = re.compile(r"^MATRIX-EXIT:(\d+)")
_PERF_PROGRESS = re.compile(r"^perf-progress (\d+)/(\d+)")
_LINT_ROW = re.compile(r"^  ([a-z][a-z0-9-]*) +([✓✗])")
_LINT_DONE = re.compile(r"^lint: \d+/\d+")
_SELECTOR = re.compile(r"lein test (:[a-z]+)$")
_NS_SELECTOR = re.compile(r"namespaces at (:[a-z]+)")


@dataclass
class LiveRun:
    """A run under way, and how far in it is."""

    kind: str
    variant: str
    log: str
    started: float
    revision: str = ""
    dirty: int = 0  # uncommitted files under src/ or test/ when it started
    last_write: float = 0.0
    owner_alive: bool = False  # the pid in the name exists, where there is one
    done: list = field(default_factory=list)  # Components with a verdict
    running: int = 0  # parts in flight, drawn blue
    expected: int = 0  # parts in all, where the checkout knows
    # Which PART of this run a process group is: the process group a runner put
    # one part in, to the part's name. Empty for a run whose parts are not
    # separate processes, and for one from before its runner wrote the file.
    parts_by_group: dict = field(default_factory=dict)

    @property
    def key(self) -> str:
        return f"{self.kind}:{self.variant}"

    @property
    def title(self) -> str:
        """`lint`, or `test :default` — the variant only where there is one,
        the way a finished run's row spells it."""
        if self.variant in ("-", ""):
            return self.kind
        return f"{self.kind} {self.variant}"

    @property
    def elapsed(self) -> float:
        return max(0.0, time.time() - self.started)

    @property
    def quiet(self) -> float:
        """Seconds since anything under this run was written."""
        return max(0.0, time.time() - self.last_write) if self.last_write else 0.0

    @property
    def stalled(self) -> bool:
        """Under way by its parts, and silent for long enough to doubt it.

        Never stalled while the process that owns the log is alive: `lein test
        :fuzz` writes almost nothing for ten minutes and is working the whole
        time, and calling that stalled says the opposite of what is true.
        """
        return not self.owner_alive and self.quiet >= ACTIVE_SECONDS

    @property
    def pending(self) -> int:
        """Parts not started yet — the grey tail of the strip."""
        return max(0, self.expected - len(self.done) - self.running)


def owner_pid(name: str) -> int | None:
    """The pid a run's log is named after, or None where the name has none.

    Public because the process table reads it too: a JVM whose ancestry reaches
    this pid is part of that run, and the naming convention it depends on is
    `scripts/lib/runlog.sh`'s, stated here once.
    """
    match = _RUN_PID.search(name)
    if match is None:
        return None
    try:
        return int(match.group(1))
    except ValueError:
        return None


def _owner_alive(path: Path) -> bool:
    """Does the pid in this run's name still exist?

    A POSITIVE signal only. `scripts/lint.sh`, `scripts/perf.sh` and
    `scripts/test-selector.sh` each name their log after their own pid, which is
    alive for exactly as long as the run — so this settles those without
    guessing from the clock. A matrix's directory is named after a shell that is
    gone by the time its configurations are running, so a `False` here means
    "ask the clock", never "dead".
    """
    pid = owner_pid(path.name)
    if pid is None:
        return False
    try:
        os.kill(pid, 0)
        return True
    except PermissionError:
        return True  # alive, and somebody else's
    except (OSError, ValueError):
        return False


def _newest_write(path: Path) -> float:
    """When anything under this run was last written.

    A directory's own mtime moves when an entry is added and not when a file
    inside it is appended to, so a matrix that has opened all its configuration
    logs stops touching it — which read as a run that had stopped.
    """
    try:
        if path.is_dir():
            return max(
                (f.stat().st_mtime for f in path.glob("*") if f.is_file()),
                default=path.stat().st_mtime,
            )
        return path.stat().st_mtime
    except OSError:
        return 0.0


def _going(path: Path, run: LiveRun) -> bool:
    """Is this run still going?

    A part unfinished, and then either the pid that owns the log still exists or
    the run has written recently. The pid is a positive signal and never a
    negative one: a matrix's directory is named after a shell that is gone by
    the time its configurations run, so asking the kernel about that one reports
    a live run as dead. Where there is no live owner, silence past
    ACTIVE_SECONDS makes a run stalled and silence past STALLED_SECONDS makes it
    gone.
    """
    run.last_write = _newest_write(path)
    run.owner_alive = _owner_alive(path)
    if run.running <= 0:
        return False
    return run.owner_alive or run.quiet < STALLED_SECONDS


def _head(path: Path) -> str:
    """The run's stamp line, which every one of these logs opens with."""
    try:
        with path.open("r", errors="replace") as handle:
            return handle.readline()
    except OSError:
        return ""


def _head_revision(path: Path) -> str:
    """The revision the run stamped at its top, so the history can place it."""
    match = _STAMP_REV.match(_head(path))
    return match.group(1) if match is not None else ""


def _head_dirty(path: Path) -> int:
    """Files under src/ or test/ that were uncommitted when the run started.

    The same stamp line carries it (scripts/lib/revision.sh), so a run under way
    fills the dirt column the way a finished one does rather than leaving a hole
    in it.
    """
    match = _STAMP_DIRTY.search(_head(path))
    return int(match.group(1)) if match is not None else 0


def _tail(path: Path) -> str:
    try:
        size = path.stat().st_size
        with path.open("rb") as handle:
            if size > TAIL_BYTES:
                handle.seek(size - TAIL_BYTES)
            return strip_ansi(handle.read().decode("utf-8", errors="replace"))
    except OSError:
        return ""


def _started(path: Path) -> float:
    """When the run began, off its own stamp line.

    Not a timestamp on the file: macOS moves `st_ctime` on every write, so a log
    being appended to reports a start that keeps catching up with now — the
    elapsed clock went backwards between two reads. The stamp is written once,
    at the start, and says what it means.
    """
    match = _STAMP_DATE.search(_head(path))
    if match is not None:
        try:
            return time.mktime(time.strptime(match.group(1), "%Y-%m-%d %H:%M:%S"))
        except (ValueError, OverflowError):
            pass
    try:
        return path.stat().st_mtime
    except OSError:
        return time.time()


def _suite_state(text: str):
    """A clojure.test run's verdict from its output, or None while it goes.

    Matched LINE BY LINE. `_RAN` is anchored with `^`, and `re.search` over a
    whole tail anchors that to the start of the tail rather than to the start of
    a line — so a blob search only ever matched a log whose first line was the
    `Ran` line, which none of them is. A live run therefore never reached a
    verdict here and sat at "running" until its silence aged it out.
    """
    lines = text.splitlines()
    if not any(_RAN.match(line) for line in lines):
        return None
    for line in reversed(lines):
        counts = _COUNTS.match(line)
        if counts is not None:
            return (
                "passed"
                if counts.group(1) == "0" and counts.group(2) == "0"
                else "failed"
            )
    return None


def _exit_state(text: str, pattern):
    """A part's verdict from the exit marker its runner appends, or None where
    the marker has not landed yet. The LAST one, the way the runner's own reader
    takes it."""
    code = None
    for line in text.splitlines():
        match = pattern.match(line)
        if match is not None:
            code = match.group(1)
    if code is None:
        return None
    return "passed" if code == "0" else "failed"


def _lint(path: Path) -> LiveRun:
    text = _tail(path)
    run = LiveRun("lint", "-", "", _started(path), _head_revision(path),
                  _head_dirty(path))
    lines = text.splitlines()
    for line in lines:
        match = _LINT_ROW.match(line)
        if match is not None:
            run.done.append(
                Component(
                    match.group(1),
                    "passed" if match.group(2) == "✓" else "failed",
                )
            )
    # One check at a time, and the run is not over until its verdict line lands.
    run.running = 0 if any(_LINT_DONE.match(line) for line in lines) else 1
    return run


def _perf(path: Path) -> LiveRun:
    text = _tail(path)
    run = LiveRun("perf", "-", "", _started(path), _head_revision(path),
                  _head_dirty(path))
    done = total = 0
    for line in text.splitlines():
        match = _PERF_PROGRESS.match(line)
        if match is not None:
            done, total = int(match.group(1)), int(match.group(2))
    # `vaelii.bench.perf` reports every verdict together at the end, so a check
    # that has finished here has still said nothing. Under way, not judged.
    run.running = min(total, done + 1) if total else done + 1
    run.expected = total
    return run


def _selector_of(text: str, default: str = ":default") -> str:
    for pattern in (_NS_SELECTOR, _SELECTOR):
        match = pattern.search(text)
        if match is not None:
            return match.group(1)
    return default


def _shards(directory: Path) -> LiveRun:
    """A sharded suite: one part per shard, from the shard logs in one directory.

    Keyed on the shard logs rather than on `test.log`, which only `gate.sh`
    writes — a bare `lein test-parallel` puts its shard logs straight into
    `target/gate` and writes no `test.log` at all, so a scan for one missed
    every run outside the gate.
    """
    shards = sorted(directory.glob("test.shard-*.log"))
    plan = _plan(directory / "test.plan")
    first = min(shards, key=_started) if shards else None
    run = LiveRun(
        "test",
        plan.get("selector") or _selector_of(_tail(directory / "test.log")),
        "",
        _started(first) if first is not None else time.time(),
        _head_revision(first) if first is not None else "",
        _head_dirty(first) if first is not None else 0,
    )
    for shard in shards:
        state = _exit_state(_tail(shard), _SHARD_EXIT)
        if state is None:
            run.running += 1
        else:
            run.done.append(Component(shard.stem, state))
    run.expected = int(plan.get("shards") or 0) or len(shards)
    return run


def _selector_run(path: Path) -> LiveRun:
    """`lein test :multi-jvm` / `:fuzz` — one JVM running one selector.

    It has no parts. `running` is 1 because something IS going and `_going`
    reads that, but `expected` stays 0 and nothing is appended to `done`: a
    strip built from one invented part would be a dot that counts nothing, and
    a mark is what a run with nothing to count draws.
    """
    text = _tail(path)
    selector = ":" + path.name.split("-run-")[0]
    run = LiveRun(
        "test", selector, "", _started(path), _head_revision(path), _head_dirty(path)
    )
    run.running = 1 if _suite_state(text) is None else 0
    return run


def _groups(path: Path) -> dict:
    """Which part of a run each process group is running, by process group id.

    `scripts/test-matrix.sh` appends a row to `configs.tsv` as each
    configuration launches, naming the process group its subshell was put in;
    every JVM under that group is that configuration. Nothing else says so: a
    configuration is chosen by environment variables passed to the subshell, and
    an environment never reaches a command line, so a process table alone can
    tell thirteen matrix JVMs apart by pid and by nothing else.

    Read rather than waited for, the way every other file here is: a run older
    than the file, a torn append and a run that never writes one each give a row
    back that names the run and not the part, which is where the tile was.
    """
    groups = {}
    try:
        lines = path.read_text(errors="replace").splitlines()
    except OSError:
        return groups
    if not lines:
        return groups
    header = lines[0].split("\t")
    if "config" not in header or "pgid" not in header:
        return groups
    name_at, group_at = header.index("config"), header.index("pgid")
    for line in lines[1:]:
        cells = line.split("\t")
        if len(cells) <= max(name_at, group_at):
            continue
        try:
            groups[int(cells[group_at])] = cells[name_at]
        except ValueError:
            continue
    return groups


def _plan(path: Path) -> dict:
    """A runner's `<name>.plan`: what it set out to do, stated once at the start.

    Empty for a run older than the plan files, and every reader of one falls
    back to what the logs alone say.
    """
    fields = {}
    try:
        for line in path.read_text(errors="replace").splitlines():
            key, _, value = line.partition("\t")
            if key and value:
                fields[key] = value
    except OSError:
        pass
    return fields


def _matrix(directory: Path) -> LiveRun:
    """A matrix: one part per configuration, from each configuration's own log.

    The plan says the selector, the roster and how many configurations this run
    means to run — so a `--owed` run shows in the column its finished row will
    land in, and the grey tail is the configurations that have not started.
    Without a plan (a run from before they were written) the selector comes off
    a configuration log and the strip is only what has started.
    """
    logs = sorted(p for p in directory.glob("*.log") if p.is_file())
    # The directory carries no stamp, so the run's clock and revision come from
    # the configuration that started first.
    first = min(logs, key=_started) if logs else None
    run = LiveRun(
        "matrix", ":default", "",
        _started(first) if first is not None else time.time(),
        _head_revision(first) if first is not None else "",
        _head_dirty(first) if first is not None else 0,
    )
    selector = ":default"
    for log in logs:
        text = _tail(log)
        selector = _selector_of(text, selector)
        # The exit marker and not clojure.test's totals, the way `_shards` reads
        # a shard: `scripts/test-matrix.sh` files the finished row on the
        # configuration's exit CODE, and a JVM that printed "0 failures" and
        # then died is a configuration that failed.
        state = _exit_state(text, _MATRIX_EXIT)
        if state is None:
            run.running += 1
        else:
            run.done.append(Component(log.stem, state))

    run.parts_by_group = _groups(directory / "configs.tsv")
    plan = _plan(directory / "matrix.plan")
    selector = plan.get("selector", selector)
    # `scripts/test-matrix.sh` files a run short of the routine roster under its
    # own variant; the plan's roster word is that decision, made at the start.
    run.variant = f"{selector} owed" if plan.get("roster") == "owed" else selector
    run.expected = int(plan.get("configs") or 0) or len(logs)
    return run


def live_runs(root: Path, ledger) -> dict:
    """Every run under way, by `kind:variant`.

    A log the ledger already names is a run that finished, whatever else is true
    of it — except where the path repeats, which `target/gate` does for every
    bare `lein test-parallel`. So the ledger is a shortcut and `_going` is the
    answer: a run with a part still unfinished and a write in the last few
    minutes.
    """
    recorded = {run.log for run in ledger.runs}
    found: dict = {}

    def offer(run: LiveRun, path: Path) -> None:
        if not _going(path, run):
            return
        run.log = str(path.relative_to(root))
        # Newest wins where two are somehow under way for one check.
        seen = found.get(run.key)
        if seen is None or run.started >= seen.started:
            found[run.key] = run

    def scan(pattern: str, build, is_dir: bool = False, skip_recorded: bool = True):
        for path in sorted(root.glob(pattern)):
            if is_dir != path.is_dir():
                continue
            if skip_recorded and str(path.relative_to(root)) in recorded:
                continue
            try:
                offer(build(path), path)
            except OSError:
                continue

    scan("logs/lint/run-*.log", _lint)
    scan("logs/perf/run-*.log", _perf)
    scan("logs/test/*-run-*.log", _selector_run)
    scan("logs/test-matrix/run-*", _matrix, is_dir=True)
    # Every directory a sharded suite can put its shards in: the gate's own
    # per-run one, and `target/gate` itself, which is where a bare `lein
    # test-parallel` writes. The second repeats across runs, so the ledger
    # cannot rule it out and `_going` has to.
    for directory in (root / "target/gate", *sorted((root / "target/gate").glob("run-*"))):
        if not directory.is_dir() or not any(directory.glob("test.shard-*.log")):
            continue
        try:
            offer(_shards(directory), directory)
        except OSError:
            continue

    # The expected part count, where neither a plan nor the logs carry one: the
    # last finished run of the same check measured it, which is a reading of this
    # checkout rather than a roster stated twice.
    from vtop.runs import CHECKS, run_components

    for key, run in found.items():
        if run.expected:
            continue
        check = next((c for c in CHECKS if f"{c.kind}:{c.variant}" == key), None)
        last = ledger.latest(check) if check is not None else None
        if last is not None:
            run.expected = len(run_components(root, last))
    return found
