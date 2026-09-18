"""Command-line entry point for vaelii-top."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from vtop import repo, theme
from vtop.app import VtopApp
from vtop.live import live_runs
from vtop.runs import (
    CHECKS,
    Ledger,
    ago,
    commit_distance,
    hms,
    moving_commits_since,
)
from vtop.theme import ThemeError, available_themes, load_theme


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="vaelii-top",
        description=(
            "The vaelii checkout in a btop-style terminal UI: its status above, "
            "and below it the git history with one column per check — which "
            "revision lint, the suite, perf and the two matrix selectors last "
            "ran at, and what each said."
        ),
    )
    parser.add_argument(
        "--repo",
        default=None,
        help="The checkout to read (default: walk up from the working directory "
        "to the nearest vaelii project.clj).",
    )
    parser.add_argument(
        "--commits",
        type=int,
        default=200,
        dest="commit_limit",
        help="How much history to read (default: 200). A verdict taken before "
        "this window reads as older than the window rather than as a distance.",
    )
    parser.add_argument(
        "--theme",
        default="default",
        help="Colour theme: 'default', the name of an installed btop theme "
        "(see --list-themes), or the path to a .theme file. The verdict "
        "colours do not follow the theme; they carry meaning of their own.",
    )
    parser.add_argument(
        "--list-themes",
        action="store_true",
        help="List the btop themes vaelii-top can find, then exit.",
    )
    parser.add_argument(
        "--once",
        action="store_true",
        help="Print the last run of each check and exit, without the UI. What "
        "a script or a commit message wants, and what to reach for over a "
        "connection the UI would repaint over.",
    )
    return parser


def print_once(root: Path, commit_limit: int) -> int:
    """The last run of each check, as lines.

    The same five rows the UI's block shows, as plain lines for a terminal
    running no UI. The exit status says whether every one of them is a pass at a
    revision this history reaches, so a script can gate on it.
    """
    status = repo.read_status(root, commit_limit)
    ledger = Ledger(root)
    ledger.load()
    print(f"vaelii {status.version}  {status.branch}  {status.head}  "
          f"{'clean' if status.clean else str(status.dirty_code) + ' dirty under src/ or test/'}")
    every_green = True
    for check in CHECKS:
        run = ledger.latest(check)
        if run is None:
            print(f"  {check.title:<22} never run in this checkout")
            every_green = False
            continue
        distance = commit_distance(status.commits, run.revision)
        if distance is None:
            where = "older than this window"
        elif distance == 0:
            where = "at HEAD"
        else:
            behind = moving_commits_since(status.commits, distance, check)
            # The same two numbers the UI's row carries, worded to fit the
            # column: how far back the revision sits, and how many of the
            # commits since touched something this check reads.
            where = (
                f"{distance} commits back, none it reads"
                if behind == 0
                else f"{distance} commits back, {behind} it reads"
            )
        dirt = f"  [over {run.dirty} dirty file(s)]" if run.over_dirt else ""
        print(
            f"  {check.title:<22} {run.state:<12} {run.revision:<10} {where:<34} "
            f"{hms(run.seconds):>8}  {ago(run.epoch):>4} ago  {run.summary}{dirt}"
        )
        if run.state != "passed" or distance != 0 or run.over_dirt:
            every_green = False

    # What is under way, after what has finished: a check whose last row is red
    # may be red because of the run that is fixing it, and a reader deciding
    # whether to wait needs to see that without opening the UI.
    for going in sorted(live_runs(root, ledger).values(), key=lambda r: r.key):
        done = f"{len(going.done)} of {going.expected} done" if going.expected else "under way"
        print(
            f"  {going.title:<22} running      "
            f"{going.revision or '?':<10} {done:<34} {hms(going.elapsed):>8}"
        )
    return 0 if every_green else 1


def main(argv: list | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    if args.list_themes:
        print("default (built in)")
        for name, path in sorted(available_themes().items()):
            print(f"{name}  ({path})")
        return 0

    root = Path(args.repo).expanduser() if args.repo else repo.find_root()
    if root is None:
        print(
            "error: no vaelii checkout found. Run this from inside one, or pass "
            "--repo <path>.",
            file=sys.stderr,
        )
        return 2
    if not (root / "project.clj").is_file():
        print(f"error: {root} has no project.clj in it", file=sys.stderr)
        return 2

    try:
        theme.use(load_theme(args.theme))
    except ThemeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if args.commit_limit < 1:
        print("error: --commits must be at least 1", file=sys.stderr)
        return 1

    if args.once:
        return print_once(root, args.commit_limit)

    VtopApp(root=root, commit_limit=args.commit_limit).run()
    return 0


if __name__ == "__main__":
    sys.exit(main())
