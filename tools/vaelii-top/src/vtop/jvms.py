"""The JVMs running right now: which run each one belongs to, and what it costs.

A verdict tile says what the last run answered; this says what is burning the
machine while you read it. The two questions are different often enough to want
both on one screen — a matrix that has written nothing for four minutes is
either working or gone, and the process table is what settles it.

Everything comes from two `ps` calls and no signals: the first names every
process on the box (cheap, `comm` only) and supplies the parent links, the
second reads the full command line of the java ones alone. A JVM's classpath
runs to a quarter of a megabyte, so reading all of them every tick would cost
more than the panel is worth.

What a JVM is DOING is not on its own command line. `lein` runs the work in a
child JVM whose arguments are a classpath and a temporary `form-init` file, so
the task name lives two processes up — hence the ancestor walk, which is also
what ties a JVM to the run under way that spawned it.
"""

from __future__ import annotations

import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

# The pid a runner's log is named after (`scripts/lib/runlog.sh`'s writers).
from vtop.live import owner_pid

# Lifted straight out of the command line.
_XMX = re.compile(r"-Xmx(\d+)([kmgKMG])")
_COMPILE_PATH = re.compile(r"-Dclojure\.compile\.path=\S*/target/([^/]+)/classes")
_LEIN_PWD = re.compile(r"-Dleiningen\.original\.pwd=(\S+)")
_ETIME = re.compile(r"^(?:(\d+)-)?(?:(\d+):)?(\d+):(\d+)$")

# `lein`'s own entry point. Everything after it on the command line is the task
# as it was typed, which is the one place the task name appears in full.
_LEIN_MAIN = "leiningen.core.main"

_UNITS = {"k": 1024, "m": 1024**2, "g": 1024**3}


@dataclass
class Jvm:
    """One java process: what it is, what it belongs to, what it is using."""

    pid: int
    ppid: int
    pgid: int
    cpu: float  # percent of ONE core, so a parallel run reads over 100
    rss: int  # bytes resident
    elapsed: float  # seconds since it started
    task: str = ""  # the lein task, `-m` namespace, main class, or script
    role: str = ""  # "lein" launcher, "worker", or "" for anything else
    profile: str = ""  # the target/<profile>/classes this JVM compiles into
    heap: int = 0  # -Xmx in bytes, 0 where the command line does not say
    mine: bool = False  # started from the checkout being watched
    reads: bool = False  # holds that checkout's src/ on its classpath
    run: str = ""  # the key of the live run this JVM is part of, if any
    # WHICH PART of that run: the matrix configuration this JVM is running. A
    # run whose parts are separate processes has one name per JVM here; every
    # other run leaves it empty and the row names the run instead.
    part: str = ""

    @property
    def label(self) -> str:
        """What to call the process in one column."""
        return self.task or "java"


def _to_bytes(size: str, unit: str) -> int:
    return int(size) * _UNITS.get(unit.lower(), 1)


def _etime_seconds(text: str) -> float:
    match = _ETIME.match(text.strip())
    if match is None:
        return 0.0
    days, hours, minutes, seconds = match.groups()
    return (
        int(days or 0) * 86400
        + int(hours or 0) * 3600
        + int(minutes) * 60
        + int(seconds)
    )


def _ps(args: list) -> str:
    """`ps` output, or "" if it failed in any way.

    `-ww` because BSD `ps` truncates to a terminal width otherwise, and a
    classpath cut off at eighty columns takes the main class with it.
    """
    try:
        out = subprocess.run(
            ["ps", "-ww", *args],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=5.0,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    if out.returncode != 0:
        return ""
    return out.stdout.decode("utf-8", errors="replace")


def _table() -> tuple:
    """(rows by pid, parent by pid) over every process on the machine.

    A row is (ppid, pgid, cpu, rss, elapsed, executable). The parent map is
    built for ALL processes and not only the java ones, because the chain from
    a worker JVM up to the script that started it runs through two shells.
    """
    rows = {}
    parent = {}
    for line in _ps(["-Ao", "pid=,ppid=,pgid=,%cpu=,rss=,etime=,comm="]).splitlines():
        parts = line.split(None, 6)
        if len(parts) != 7:
            continue
        try:
            pid, ppid, pgid = int(parts[0]), int(parts[1]), int(parts[2])
            cpu, rss = float(parts[3]), int(parts[4]) * 1024
        except ValueError:
            continue
        rows[pid] = (ppid, pgid, cpu, rss, _etime_seconds(parts[5]), parts[6])
        parent[pid] = ppid
    return rows, parent


def _commands(pids: list) -> dict:
    """The full command line of each of `pids`, keyed by pid."""
    if not pids:
        return {}
    text = _ps(["-o", "pid=,command=", "-p", ",".join(str(p) for p in pids)])
    out = {}
    for line in text.splitlines():
        parts = line.split(None, 1)
        if len(parts) != 2:
            continue
        try:
            out[int(parts[0])] = parts[1]
        except ValueError:
            continue
    return out


def _script_of(command: str) -> str:
    """What a shell ancestor is running, where the JVM itself does not say.

    A worker JVM's arguments are a classpath and a temporary file, and its
    ancestors are two `bash` processes — but those two carry the script path,
    which is the name of the work: `lein test :fuzz`, `scripts/lint.sh`,
    `run-vaelii.sh w1.chain.10m.vaelii.genl`. Read from the nearest ancestor
    outwards, so the innermost script wins over the wrapper that called it.
    """
    tokens = command.split()
    for index, token in enumerate(tokens):
        name = os.path.basename(token)
        if name == "lein" or token.endswith(".sh") or token.endswith(".py"):
            rest = [t for t in tokens[index + 1 :] if not t.startswith("-")]
            return " ".join([name, *rest[:2]]).strip()
    return ""


def _task_of(command: str) -> tuple:
    """(role, task) read off one command line.

    Three shapes, in the order they are recognised:

      `… clojure.main -m leiningen.core.main test :fuzz`   the lein launcher,
          and the only process that carries the task as it was typed
      `… clojure.main -m vaelii.serve 57107`               a JVM started at a
          namespace, which names itself
      `… clojure.main -i /tmp/form-init….clj`              the work, whose
          arguments say nothing at all — the caller walks up for the task
    """
    tokens = command.split()
    if _LEIN_MAIN in tokens:
        rest = tokens[tokens.index(_LEIN_MAIN) + 1 :]
        return ("lein", " ".join(rest))
    if "clojure.main" in tokens:
        rest = tokens[tokens.index("clojure.main") + 1 :]
        if rest[:1] == ["-m"]:
            return ("worker", " ".join(rest[1:]))
        return ("worker", "")
    # Not a Clojure process: the main class is the last argument that is neither
    # a flag nor the value of one.
    for token in reversed(tokens):
        if not token.startswith("-") and "/" not in token and "." in token:
            return ("", token)
    return ("", "")


def _ancestors(pid: int, parent: dict, limit: int = 12) -> list:
    """The pids above `pid`, nearest first. Bounded, because a corrupt parent
    map with a cycle in it would otherwise hang the repaint."""
    out = []
    seen = set()
    current = parent.get(pid, 0)
    while current and current > 1 and current not in seen and len(out) < limit:
        out.append(current)
        seen.add(current)
        current = parent.get(current, 0)
    return out


def read_jvms(root: Path, live: dict | None = None) -> list:
    """Every java process on the machine, newest work first.

    `live` is the live-run table, and a JVM whose ancestry reaches a run's
    owning pid is tagged with that run — which is how a bare shard JVM ends up
    labelled `test :default` rather than `clojure.main -i /tmp/form-init.clj`.
    """
    rows, parent = _table()
    java = [pid for pid, row in rows.items() if os.path.basename(row[5]) == "java"]
    chains = {pid: _ancestors(pid, parent) for pid in java}
    # The ancestors' command lines as well as the JVMs' own: a worker JVM is
    # named by the script two processes above it, and that is a bounded handful
    # of pids rather than the whole machine.
    wanted = set(java)
    for chain in chains.values():
        wanted.update(chain)
    commands = _commands(sorted(wanted))

    # Which run a JVM is part of, by the pid its log is named after — matched
    # BOTH ways round. `lein lint` runs `scripts/lint.sh`, so the shell that
    # owns the log is a CHILD of the launcher JVM and no ancestor walk from the
    # JVM will ever reach it; the process group holds the whole invocation
    # either way.
    owners = {}
    owner_groups = {}
    for key, run in (live or {}).items():
        pid = owner_pid(Path(run.log).name)
        if pid is None:
            continue
        owners[pid] = key
        row = rows.get(pid)
        if row is not None:
            owner_groups.setdefault(row[1], key)

    root_text = str(root)
    out = []
    by_pid = {}
    for pid in java:
        ppid, pgid, cpu, rss, elapsed, _ = rows[pid]
        command = commands.get(pid, "")
        role, task = _task_of(command)
        jvm = Jvm(
            pid=pid,
            ppid=ppid,
            pgid=pgid,
            cpu=cpu,
            rss=rss,
            elapsed=elapsed,
            task=task,
            role=role,
        )
        heap = _XMX.search(command)
        if heap is not None:
            jvm.heap = _to_bytes(heap.group(1), heap.group(2))
        profile = _COMPILE_PATH.search(command)
        if profile is not None:
            jvm.profile = profile.group(1)
        pwd = _LEIN_PWD.search(command)
        jvm.mine = pwd is not None and pwd.group(1) == root_text
        # Reading the checkout is a different fact from being started in it: a
        # bench run in a sibling repo resolves this engine through its live
        # source, so it compiles what you are editing without being one of your
        # runs — and it is on the same ten cores either way.
        jvm.reads = f"{root_text}/src" in command
        out.append(jvm)
        by_pid[pid] = jvm

    for jvm in out:
        chain = chains.get(jvm.pid, [])
        # The task from the nearest ancestor that has one, then from the nearest
        # ancestor script. A worker JVM's own arguments are a classpath and a
        # temporary file, and say nothing about what it was asked to do.
        if not jvm.task:
            for up in chain:
                above = by_pid.get(up)
                if above is not None and above.task:
                    jvm.task = above.task
                    break
        if not jvm.task:
            for up in chain:
                script = _script_of(commands.get(up, ""))
                if script:
                    jvm.task = script
                    break
        for up in chain:
            if up in owners:
                jvm.run = owners[up]
                break
        if not jvm.run:
            jvm.run = owner_groups.get(jvm.pgid, "")
        # The part comes off the process group and not off the ancestor chain:
        # `set -m` puts each configuration's subshell in a group of its own, and
        # the launcher JVM and the project JVM it trampolines into both carry
        # that group — so one lookup names both, whichever way the chain runs.
        going = (live or {}).get(jvm.run)
        if going is not None:
            jvm.part = going.parts_by_group.get(jvm.pgid, "")
        if not jvm.mine and any(by_pid.get(up, jvm).mine for up in chain):
            jvm.mine = True
        if jvm.mine:
            jvm.reads = True

    # This checkout's own runs first, then whatever else is reading it, then
    # the biggest resident set: the row that matters is the one doing the work,
    # and the work is what has the memory.
    out.sort(key=lambda j: (not j.mine, not j.reads, -j.rss))
    return out


def totals(jvms: list) -> tuple:
    """(processes, resident bytes, percent of one core) over the whole list."""
    return (len(jvms), sum(j.rss for j in jvms), sum(j.cpu for j in jvms))


def machine_memory() -> int:
    """Physical memory in bytes, or 0 where the sysctl is not there."""
    try:
        out = subprocess.run(
            ["sysctl", "-n", "hw.memsize"],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=2.0,
        )
    except (OSError, subprocess.SubprocessError):
        return 0
    text = out.stdout.decode(errors="replace").strip()
    return int(text) if text.isdigit() else 0


def human_bytes(count: int) -> str:
    """A size in the two significant figures a column has room for."""
    if count <= 0:
        return "—"
    if count < 1024**2:
        return f"{count // 1024}K"
    if count < 1024**3:
        return f"{count / 1024**2:.0f}M"
    return f"{count / 1024**3:.1f}G"
