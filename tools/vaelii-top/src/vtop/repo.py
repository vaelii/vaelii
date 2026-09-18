"""What the vaelii checkout is right now: version, branch, revision, dirt,
how far it is from its upstream, the recent history, and the tree's counts.

Every fact here comes from `git` or from reading a file, never from a build.
The screen repaints on a timer, so nothing in this module may be slow or may
touch the repository: a status panel that compiled something would make
watching the repo change the repo.

Each reader returns a value or a blank — never raises. A checkout without an
upstream, without a tag, or read while a rebase holds the index is a state to
display, not an error to crash on.
"""

from __future__ import annotations

import re
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path


def _run(args: list[str], cwd: Path, timeout: float = 5.0) -> str:
    """A command's stdout, stripped, or "" if it failed in any way. Timeout
    included: a `git` call under a filesystem that has gone away hangs, and a
    hung repaint is indistinguishable from a crashed one."""
    try:
        out = subprocess.run(
            args,
            cwd=str(cwd),
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=timeout,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    if out.returncode != 0:
        return ""
    return out.stdout.decode("utf-8", errors="replace").strip()


# The class each path in a commit is filed under, by the directory it is in.
# A check reads some of these classes and not others, so the classes are what
# `runs.CHECKS` names when it says what a column's verdict depends on.
_PATH_DIRS = (
    ("src/", "src"),
    ("test/", "test"),
    ("bench/", "bench"),
    ("resources/", "resources"),
    ("scripts/", "scripts"),
    ("docs/", "docs"),
    ("tools/", "tools"),
    (".clj-kondo/", "lint-config"),
    (".github/", "ci"),
    ("legal/", "legal"),
    ("licenses/", "legal"),
)

# Files at the root of the checkout, which have no directory to be filed by.
_PATH_FILES = {
    "project.clj": "project",
    "README.md": "prose",
    "CONTRIBUTING.md": "prose",
    "CHANGELOG.md": "prose",
    "CONTRIBUTORS.md": "legal",
    "LICENSE": "legal",
    "DCO": "legal",
    "Dockerfile": "ci",
    "docker-compose.yml": "ci",
    ".dockerignore": "ci",
    ".gitignore": "ci",
}

# A path none of the above names, and the class every check reads. A new
# top-level directory is one this tool has not been told the shape of, and
# filing it as harmless would let a verdict be inferred across a change nothing
# here has looked at.
UNCLASSIFIED = "other"


def classify_path(path: str) -> str:
    """Which class a path in a commit belongs to."""
    for prefix, name in _PATH_DIRS:
        if path.startswith(prefix):
            return name
    return _PATH_FILES.get(path, UNCLASSIFIED)


@dataclass(frozen=True)
class Commit:
    """One line of history, plus which classes of path it touched.

    `touched` is what decides whether a verdict either side of this commit also
    answers for it: a commit that touched nothing a check reads leaves that
    check's last answer standing, and `runs.inferred_runs` fills the cell in
    from there.

    `touches_code` is the `src/` and `test/` half of that — the same two
    directories `scripts/lib/revision.sh` reports dirt under, kept as its own
    field because the history draws a commit's subject by it.
    """

    sha: str
    subject: str
    author: str
    when: float  # author time, epoch seconds
    touched: frozenset

    @property
    def touches_code(self) -> bool:
        return bool(self.touched & {"src", "test"})


@dataclass
class Status:
    """The whole of the top panel, read in one pass."""

    root: Path
    version: str = ""
    branch: str = ""
    head: str = ""
    head_subject: str = ""
    head_when: float = 0.0
    dirty_all: int = 0
    dirty_code: int = 0
    untracked: int = 0
    ahead: int = 0
    behind: int = 0
    upstream: str = ""
    src_namespaces: int = 0
    test_namespaces: int = 0
    doc_pages: int = 0
    kb_contexts: int = 0
    src_lines: int = 0
    commits_total: int = 0
    commits: list = field(default_factory=list)
    read_at: float = 0.0

    @property
    def clean(self) -> bool:
        return self.dirty_code == 0


_VERSION_RE = re.compile(r'\(defproject\s+\S+\s+"([^"]+)"')

# `git log` in one call, with a separator no commit subject can contain. The
# `%x00` NUL is not usable through a shell pipeline but is fine here — this
# runs `git` directly, without one. The leading record separator is what tells a
# header line apart from the file names `--name-only` prints under it, since a
# path may hold anything a subject may.
_LOG_RECORD = "\x1e"
_LOG_FORMAT = f"{_LOG_RECORD}%h%x00%p%x00%an%x00%at%x00%s"


def read_version(root: Path) -> str:
    try:
        text = (root / "project.clj").read_text(errors="replace")
    except OSError:
        return ""
    match = _VERSION_RE.search(text)
    return match.group(1) if match else ""


def read_commits(root: Path, limit: int = 200) -> list:
    """The last `limit` commits, newest first, each with the classes it touched.

    ONE `git log --name-only` and not a pathspec call per class: the classes
    number a dozen, a pathspec call each is a dozen walks of the same history,
    and the single pass that lists every name costs 54ms over 200 commits
    against 38ms for the one pathspec call it replaces. Timed rather than
    assumed, because a repaint every six seconds is what pays for it.

    A merge commit lists no names under `--name-only`, and a commit whose class
    set were read as empty would have every verdict inferred across it. Its
    parent count is therefore read too, and a merge is filed as UNCLASSIFIED.
    """
    raw = _run(
        ["git", "log", f"-{limit}", f"--format={_LOG_FORMAT}", "--name-only"],
        root,
        timeout=8.0,
    )
    if not raw:
        return []
    commits = []
    for record in raw.split(_LOG_RECORD):
        if not record.strip():
            continue
        lines = record.splitlines()
        parts = lines[0].split("\0")
        if len(parts) != 5:
            continue
        sha, parents, author, when, subject = parts
        try:
            stamp = float(when)
        except ValueError:
            stamp = 0.0
        if len(parents.split()) > 1:
            touched = frozenset({UNCLASSIFIED})
        else:
            touched = frozenset(
                classify_path(name) for name in lines[1:] if name.strip()
            )
        commits.append(
            Commit(
                sha=sha,
                subject=subject,
                author=author,
                when=stamp,
                touched=touched,
            )
        )
    return commits


def _count_files(root: Path, *patterns: str) -> int:
    total = 0
    for pattern in patterns:
        total += sum(1 for _ in root.glob(pattern))
    return total


def _count_lines(root: Path, pattern: str) -> int:
    total = 0
    for path in root.glob(pattern):
        try:
            with path.open("rb") as handle:
                total += sum(1 for _ in handle)
        except OSError:
            continue
    return total


def _porcelain_counts(root: Path) -> tuple:
    """(dirty tracked, untracked) over the whole tree, from one `git status`.

    `--porcelain` because the human format is localized, and a reader that
    parses a translated word reports zero on somebody else's machine.
    """
    raw = _run(["git", "status", "--porcelain"], root)
    if not raw:
        return (0, 0)
    dirty = untracked = 0
    for line in raw.splitlines():
        if line.startswith("??"):
            untracked += 1
        elif line.strip():
            dirty += 1
    return (dirty, untracked)


def _ahead_behind(root: Path) -> tuple:
    """(ahead, behind, upstream name). A branch with no upstream is (0, 0, "")
    rather than an error: this checkout's `main` tracks a private remote and a
    detached HEAD tracks nothing at all, and both are ordinary states."""
    upstream = _run(["git", "rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{upstream}"], root)
    if not upstream:
        return (0, 0, "")
    counts = _run(["git", "rev-list", "--left-right", "--count", f"{upstream}...HEAD"], root)
    parts = counts.split()
    if len(parts) != 2:
        return (0, 0, upstream)
    try:
        behind, ahead = int(parts[0]), int(parts[1])
    except ValueError:
        return (0, 0, upstream)
    return (ahead, behind, upstream)


def read_status(root: Path, commit_limit: int = 200) -> Status:
    """Everything the top panel shows, in one pass over git and the tree."""
    status = Status(root=root, read_at=time.time())
    status.version = read_version(root)
    status.branch = _run(["git", "rev-parse", "--abbrev-ref", "HEAD"], root) or "?"
    status.head = _run(["git", "rev-parse", "--short", "HEAD"], root) or "no-git"
    status.head_subject = _run(["git", "log", "-1", "--format=%s"], root)
    when = _run(["git", "log", "-1", "--format=%at"], root)
    try:
        status.head_when = float(when)
    except ValueError:
        status.head_when = 0.0

    # The same two directories `scripts/lib/revision.sh` reports on, so the
    # panel's "dirty" and a stage log's "tree DIRTY" are one number.
    code = _run(["git", "status", "--porcelain", "--", "src", "test"], root)
    status.dirty_code = len([x for x in code.splitlines() if x.strip()])
    status.dirty_all, status.untracked = _porcelain_counts(root)
    status.ahead, status.behind, status.upstream = _ahead_behind(root)

    total = _run(["git", "rev-list", "--count", "HEAD"], root)
    status.commits_total = int(total) if total.isdigit() else 0
    status.commits = read_commits(root, commit_limit)

    status.src_namespaces = _count_files(root, "src/**/*.clj", "src/**/*.cljc")
    status.test_namespaces = _count_files(root, "test/**/*_test.clj")
    status.doc_pages = _count_files(root, "docs/*.md")
    status.kb_contexts = _count_files(root, "resources/kb/**/*.txt")
    status.src_lines = _count_lines(root, "src/**/*.clj")
    return status


def find_root(start: Path | None = None) -> Path | None:
    """The vaelii checkout to read, walking up from `start`.

    A `project.clj` naming this project is what identifies one, rather than a
    git root alone: `tools/vaelii-top` is inside the checkout it reads, so a
    plain `--show-toplevel` would be right here and wrong from a sibling
    worktree of some other repo.
    """
    here = (start or Path.cwd()).resolve()
    for directory in [here, *here.parents]:
        project = directory / "project.clj"
        if project.is_file():
            try:
                text = project.read_text(errors="replace")
            except OSError:
                continue
            if "defproject com.vaelii/vaelii" in text:
                return directory
    return None
