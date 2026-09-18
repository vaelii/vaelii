"""The screen: four btop boxes — ¹repo, ²runs, ³history, ⁴jvms.

The app owns the data — the checkout's status, the run ledger and the process
table — and the widgets read it. Three timers: one repaints, one re-reads the
checkout, one re-reads the JVMs. The ledger reload is a stat when nothing has
been appended, so the repaint tick costs a frame and no git calls.
"""

from __future__ import annotations

import os
import subprocess
import time
from pathlib import Path

from rich.console import Group
from rich.style import Style
from rich.text import Text
from textual.app import App, ComposeResult
from textual.binding import Binding
from textual.containers import VerticalScroll
from textual.css.query import NoMatches
from textual.screen import ModalScreen, Screen
from textual.widget import Widget

from vtop import repo, theme
from vtop.colors import DIRT_MARK, state_color, state_mark
from vtop.jvms import human_bytes, machine_memory, read_jvms, totals
from vtop.live import live_runs
from vtop.runs import (
    CHECKS,
    Ledger,
    ago,
    hms,
    inferred_by_check,
    read_matrix_summary,
    strip_ansi,
)
from vtop.theme import GOOD, Panel, label
from vtop.widgets import (
    BAR_ROWS,
    HEADER_ROW,
    LIVE_ROWS_MAX,
    HistoryPanel,
    JvmPanel,
    LivePanel,
    RunsPanel,
    StatusPanel,
    TileMenu,
    _clock,
    bar_cells,
    faded,
)

# How often the panels repaint, and how often the checkout is re-read. The
# repaint is cheap (a string build); the read shells out to git half a dozen
# times, so it is not on the same tick.
REPAINT_SECONDS = 1.0
RELOAD_SECONDS = 6.0

# How often the process table is re-read. Two `ps` calls, so it is not on the
# repaint tick; often enough that a JVM starting or exiting shows up while you
# are still looking at the row above it.
JVM_SECONDS = 2.0

# The most JVM rows the ⁴jvms tile draws. A matrix runs fifteen configurations
# two JVMs apiece, and a tile that grew to thirty rows would take the history
# off the screen — the list is sorted so the heaviest are the ones kept.
JVM_ROWS_MAX = 8

# Below this the status panel drops its graph and keeps the four text rows.
FULL_STATUS_MIN_HEIGHT = 30

# The tail of a log a detail view shows. Enough to carry a failing check's own
# report, short enough that the view opens as one screen.
LOG_TAIL = 60


class RunDetailScreen(ModalScreen[None]):
    """Every run taken at one revision, with the failing ones' log tails.

    Keyed on the REVISION rather than on a single run, because the question a
    commit raises is what the whole roster said about it — a green suite beside
    a red perf is the interesting answer, and two separate views would hide it.
    """

    BINDINGS = [
        Binding("escape", "dismiss", "Close"),
        Binding("q", "dismiss", "Close"),
        Binding("enter", "dismiss", "Close", show=False),
    ]

    def __init__(self, root: Path, commit, runs: list, inferred: list = ()) -> None:
        super().__init__()
        self.root = root
        self.commit = commit
        self.runs = runs
        # (check, run) for each column whose cell this commit inferred, so the
        # view that explains a row explains its grey cells too. A reader who
        # clicked a grey tick is asking which run it came from, and the answer
        # is a revision this screen would otherwise not name.
        self.inferred = list(inferred)

    def compose(self) -> ComposeResult:
        with Panel(id="detail-panel", color=theme.HISTORY_BOX):
            with VerticalScroll(id="detail-scroll"):
                yield Widget(id="detail-body")

    def on_mount(self) -> None:
        panel = self.query_one("#detail-panel", Panel)
        panel.set_edges(
            top_left=[label(self.commit.sha, bold=True), label(_truncate(self.commit.subject, 60))],
            center=_clock(),
            bottom_left=[label("close", "q")],
            bottom_right=[label("esc", color=theme.DIM)],
        )
        body = self.query_one("#detail-body", Widget)
        body.styles.height = "auto"
        rendered = self._body()
        body.render = lambda: rendered  # type: ignore[assignment]
        body.refresh()

    def _body(self) -> Group:
        rows = []
        head = Text()
        head.append(self.commit.author, Style(color=theme.FG))
        head.append(
            f"   {time.strftime('%Y-%m-%d %H:%M', time.localtime(self.commit.when))}"
            f"   ({ago(self.commit.when)} ago)",
            Style(color=theme.DIM),
        )
        # `src/` or `test/` and not "code": a commit under `tools/` or `scripts/`
        # touches neither, and calling that one "docs only" would put a wrong
        # word on the line a reader uses to decide whether a stale green still
        # means something.
        head.append(
            "   touches src/ or test/"
            if self.commit.touches_code
            else "   touches neither src/ nor test/",
            Style(color=theme.HI if self.commit.touches_code else theme.DIM),
        )
        rows.append(head)
        rows.append(Text(""))

        if not self.runs:
            rows.append(
                Text(
                    "No check has run at this revision.",
                    style=Style(color=theme.DIM),
                )
            )
            rows.extend(self._inferred_rows())
            return Group(*rows)

        for run in self.runs:
            line = Text()
            line.append(f"{state_mark(run.state)} ", Style(color=state_color(run.state), bold=True))
            line.append(f"{run.title:<16}", Style(color=theme.TITLE, bold=True))
            line.append(f"{run.state:<12}", Style(color=state_color(run.state)))
            line.append(f"{hms(run.seconds):>8}  ", Style(color=theme.DIM))
            line.append(run.started, Style(color=theme.DIM))
            rows.append(line)
            rows.append(Text(f"    {run.summary}", style=Style(color=theme.FG)))
            if run.over_dirt:
                rows.append(
                    Text(
                        f"    {DIRT_MARK} {run.dirty} uncommitted file(s) under src/ or "
                        "test/ — this run compiled work no commit holds",
                        style=Style(color=theme.HI),
                    )
                )
            rows.append(Text(f"    {run.log}", style=Style(color=theme.DIM)))

            # A matrix already writes one row per configuration beside its logs,
            # so the detail is read from there rather than copied into the
            # ledger (runs.read_matrix_summary says why).
            for config in read_matrix_summary(self.root, run.log):
                mark = state_mark(config.get("state", "missing"))
                row = Text(f"      {mark} ", style=Style(color=state_color(config.get("state", "missing"))))
                row.append(f"{config.get('config', '?'):<18}", Style(color=theme.FG))
                row.append(f"{config.get('summary', ''):<34}", Style(color=theme.DIM))
                row.append(config.get("counts", ""), Style(color=theme.DIM))
                rows.append(row)

            rows.extend(self._log_tail(run))
            rows.append(Text(""))
        rows.extend(self._inferred_rows())
        return Group(*rows)

    def _inferred_rows(self) -> list:
        """The columns this commit took a verdict from somewhere else, and where
        from. One line per column: the verdict, the check, the revision that ran
        it and when."""
        if not self.inferred:
            return []
        rows = [
            Text(""),
            Text(
                "Inferred — nothing these checks read changed between this "
                "commit and the run named:",
                style=Style(color=theme.DIM),
            ),
        ]
        for check, run in self.inferred:
            line = Text("  ")
            line.append_text(
                faded(
                    Text(
                        state_mark(run.state),
                        Style(color=state_color(run.state), bold=True),
                    )
                )
            )
            line.append(f" {check.title:<24}", Style(color=theme.TITLE))
            line.append(f"{run.state:<12}", Style(color=state_color(run.state)))
            line.append(f"from {run.revision}", Style(color=theme.ACCENT))
            line.append(f", {ago(run.epoch)} ago", Style(color=theme.DIM))
            rows.append(line)
        return rows

    def _log_tail(self, run) -> list:
        """The end of a run's log, as text.

        Every run and not only a failing one: a green lint over a roster that
        quietly went short is the case a verdict cannot show you, and the log is
        what says which checks ran. A matrix's `log` is a directory rather than
        a file, and its configurations are already listed above from
        `summary.tsv`, so there is nothing here to tail.
        """
        path = self.root / run.log
        if not path.is_file():
            return []
        try:
            lines = path.read_text(errors="replace").splitlines()
        except OSError:
            return []
        tail = [strip_ansi(line) for line in lines[-LOG_TAIL:]]
        out = [Text(f"    ── {run.log}, last {len(tail)} line(s)", style=Style(color=theme.DIM))]
        out.extend(Text(f"    {line}", style=Style(color=theme.GRAPH_TEXT)) for line in tail)
        return out


def _truncate(text: str, width: int) -> str:
    return text if len(text) <= width else text[: max(0, width - 1)] + "…"


class TopScreen(Screen):
    """The whole tool: the status panel, the history panel, and the timers."""

    BINDINGS = [
        Binding("up", "select_up", "Select", show=False),
        Binding("k", "select_up", "Select", show=False),
        Binding("down", "select_down", "Select", show=False),
        Binding("j", "select_down", "Select", show=False),
        Binding("pageup", "page_up", "Page", show=False),
        Binding("pagedown", "page_down", "Page", show=False),
        Binding("home", "select_head", "HEAD", show=False),
        Binding("end", "select_oldest", "Oldest", show=False),
        Binding("enter", "detail", "Detail"),
        Binding("o", "open_log", "Open log"),
        Binding("r", "reload", "Reload"),
        Binding("1", "toggle_status", "Show/Hide repo tile"),
        Binding("2", "toggle_runs", "Show/Hide runs tile"),
        Binding("3", "toggle_history", "Show/Hide history tile"),
        Binding("4", "toggle_jvms", "Show/Hide jvms tile"),
        Binding("5", "toggle_live", "Show/Hide live tile"),
        Binding("q", "quit_app", "Quit"),
    ]

    def __init__(self, root: Path, commit_limit: int = 200) -> None:
        super().__init__()
        self.root = root
        self.commit_limit = commit_limit
        self.status = None
        self.ledger = Ledger(root)
        self.last_read = 0.0
        self.show_status = True
        self.show_runs = True
        self.show_history = True
        self.show_jvms = True
        self.show_live = True
        self.live: dict = {}
        # The verdict each commit with no run of its own takes, by check. Held
        # here rather than derived in the panel: the history draws eight columns
        # over as many rows as fit and asks for the same map twice a frame, and
        # the map only moves when the history or the ledger does.
        self.inferred: dict = {}
        self.jvms: list = []
        # Read once: neither the core count nor the physical memory changes
        # while the tool is up, and both are a subprocess apiece.
        self.cores = os.cpu_count() or 1
        self.memory = machine_memory()
        self.note: str = ""

    def tiles(self) -> list:
        """The tiles, their keys, what each carries, and whether it is showing.

        Stated once here because three things read it: the bindings that toggle
        a tile, `_fit` which applies the flags, and `TileMenu` which lists them
        when every one is hidden. A second copy in the menu is the one that
        would go short, and the menu is exactly what a reader reaches for when
        they cannot see anything else.
        """
        return [
            ("1", "repo", "version, branch, revision, dirt, upstream, counts", self.show_status),
            ("2", "runs", "the last run of each check, and where it was taken", self.show_runs),
            ("3", "history", "the git history, one column per check", self.show_history),
            ("4", "jvms", "every JVM running, what it is part of, cpu and memory", self.show_jvms),
            ("5", "live", "the checks running now, one part to a braille column", self.show_live),
        ]

    @property
    def commits(self) -> list:
        return self.status.commits if self.status is not None else []

    def commits_per_hour(self, hours: int = 240) -> list:
        """Commits landed per hour, oldest first, ending in the current hour.

        Per hour rather than per day because a day is one bar and a session is
        the unit of work here: an afternoon of six commits and a week of six
        are the same bar on a daily chart, and a chart that cannot tell them
        apart is not reporting the thing it is asked about.

        Built from the history already read rather than from another `git log`,
        and CLIPPED to what that history spans: `--commits 200` reaches back a
        few days, and padding the rest with zeros would draw a flat line where
        there is no reading at all rather than where nothing landed.
        """
        if not self.commits:
            return []
        hour = 3600.0
        now = int(time.time() // hour)
        oldest = min(int(c.when // hour) for c in self.commits if c.when)
        span = max(1, min(hours, now - oldest + 1))
        counts = [0.0] * span
        for commit in self.commits:
            if not commit.when:
                continue
            index = span - 1 - (now - int(commit.when // hour))
            if 0 <= index < span:
                counts[index] += 1
        return counts

    def compose(self) -> ComposeResult:
        with Panel(id="status-panel", color=theme.STATUS_BOX):
            yield StatusPanel(self, id="status")
        with Panel(id="runs-panel", color=theme.RUNS_BOX):
            yield RunsPanel(self, id="runs")
        with Panel(id="history-panel", color=theme.HISTORY_BOX):
            yield HistoryPanel(self, id="history")
        with Panel(id="jvms-panel", color=theme.ACCENT):
            yield JvmPanel(self, id="jvms")
        with Panel(id="live-panel", color=theme.RUNS_BOX):
            yield LivePanel(self, id="live")
        yield TileMenu(self, id="tile-menu")

    def on_mount(self) -> None:
        self.reload()
        self._fit(self.app.size.height)
        self.set_interval(REPAINT_SECONDS, self.repaint)
        self.set_interval(RELOAD_SECONDS, self.reload)
        self.set_interval(JVM_SECONDS, self.reload_jvms)

    def on_resize(self, event) -> None:
        self._fit(event.size.height)

    def _fit(self, height: int) -> None:
        """The three fixed tiles' heights; the history takes what is left.

        The status tile is text plus a graph, so it keeps the graph on a tall
        terminal and drops to the text rows on a short one rather than
        squeezing both. The runs tile is one row per check and never varies —
        which is the point of it being its own tile: the verdicts do not shrink
        to make room for history. The jvms tile is as tall as there are JVMs,
        capped, so an idle machine spends three rows on saying so.
        """
        try:
            status = self.query_one("#status-panel", Panel)
            runs = self.query_one("#runs-panel", Panel)
            history = self.query_one("#history-panel", Panel)
            jvms = self.query_one("#jvms-panel", Panel)
            live = self.query_one("#live-panel", Panel)
            menu = self.query_one("#tile-menu", TileMenu)
        except NoMatches:
            return
        status.styles.display = "block" if self.show_status else "none"
        status.styles.height = 13 if height >= FULL_STATUS_MIN_HEIGHT else 7
        runs.styles.display = "block" if self.show_runs else "none"
        runs.styles.height = len(CHECKS) + 2
        history.styles.display = "block" if self.show_history else "none"
        history.styles.height = "1fr"
        jvms.styles.display = "block" if self.show_jvms else "none"
        # One heading row, one row per JVM, and the frame — or three rows for
        # the one sentence an idle machine gets, which has no heading over it.
        jvms.styles.height = (
            min(len(self.jvms), JVM_ROWS_MAX) + 3 if self.jvms else 3
        )
        live.styles.display = "block" if self.show_live else "none"
        # TWO rows per run under way, since a part here is a column two cells
        # tall — or three rows for the one sentence an idle checkout gets.
        live.styles.height = (
            2 * min(len(self.live), LIVE_ROWS_MAX) + 3 if self.live else 3
        )

        # The LOWEST showing tile takes what is left over, so hiding the ones
        # under it does not leave a ragged band of background. Only one tile may
        # hold the `1fr`, hence the reset above and the walk from the bottom up.
        if self.show_live and not self.show_history:
            live.styles.height = "1fr"
        elif self.show_jvms and not self.show_history:
            jvms.styles.height = "1fr"
        elif not self.show_history:
            if self.show_runs:
                runs.styles.height = "1fr"
            elif self.show_status:
                status.styles.height = "1fr"

        # The menu takes the screen only when nothing else has it. `1fr` rather
        # than a fixed height: it centres its own box in whatever it is given.
        nothing = not any(showing for _, _, _, showing in self.tiles())
        menu.styles.display = "block" if nothing else "none"

    def reload(self) -> None:
        """Re-read the checkout and the ledger."""
        self.status = repo.read_status(self.root, self.commit_limit)
        self.ledger.load()
        self.live = live_runs(self.root, self.ledger)
        self.inferred = inferred_by_check(self.commits, self.ledger)
        self.last_read = time.time()
        self.reload_jvms()
        self.repaint()

    def reload_jvms(self) -> None:
        """Re-read the process table, and resize the tile if the count moved."""
        before = len(self.jvms)
        self.jvms = read_jvms(self.root, self.live)
        if len(self.jvms) != before:
            self._fit(self.app.size.height)
        try:
            self.query_one(JvmPanel).refresh()
        except NoMatches:
            return
        self.update_edges()

    def repaint(self) -> None:
        try:
            self.query_one(StatusPanel).refresh()
            self.query_one(RunsPanel).refresh()
            self.query_one(HistoryPanel).refresh()
            self.query_one(JvmPanel).refresh()
            self.query_one(TileMenu).refresh()
        except NoMatches:
            return
        # A run finishing between two reads of the checkout moves what the
        # commits either side of it infer, so the map is rebuilt whenever the
        # ledger's rows move — 1.4ms over two hundred commits and eight columns,
        # against a stat that finds nothing on the common frame.
        if self.ledger.load():
            self.inferred = inferred_by_check(self.commits, self.ledger)
        self.live = live_runs(self.root, self.ledger)
        self.update_edges()

    # ---- the panel edges ----------------------------------------------------

    def update_edges(self) -> None:
        try:
            status_panel = self.query_one("#status-panel", Panel)
            runs_panel = self.query_one("#runs-panel", Panel)
            history_panel = self.query_one("#history-panel", Panel)
            jvms_panel = self.query_one("#jvms-panel", Panel)
            live_panel = self.query_one("#live-panel", Panel)
        except NoMatches:
            return
        status = self.status
        version = status.version if status else "?"
        branch = status.branch if status else "?"
        if status is None:
            tree = Text("reading", style=Style(color=theme.DIM))
        elif status.clean:
            tree = Text("● clean", style=Style(color=GOOD, bold=True))
        else:
            tree = Text(
                f"{DIRT_MARK} {status.dirty_code} dirty",
                style=Style(color=theme.HI, bold=True),
            )
        status_panel.set_edges(
            top_left=[
                label("repo", num="¹", bold=True),
                label(f"vaelii {version}"),
                label(branch, color=theme.ACCENT),
                tree,
            ],
            center=_clock(),
            top_right=[label("reload", "r")],
            bottom_left=[
                label("quit", "q"),
                label("repo", "1"),
                label("runs", "2"),
                label("history", "3"),
                label("jvms", "4"),
                label("live", "5"),
            ],
            bottom_right=[label(str(self.root), color=theme.DIM)],
        )

        runs_panel.set_edges(
            top_left=[
                label("runs", num="²", bold=True),
                Text(
                    "the last run of each check, and the revision it was taken at",
                    style=Style(color=theme.DIM),
                ),
            ],
            top_right=[self._live_note()],
            bottom_right=[
                Text(
                    "bar: how much of what this check reads is unchanged  ·  "
                    "cell: one check or configuration  ·  "
                    f"{DIRT_MARK}: taken over uncommitted work",
                    style=Style(color=theme.DIM),
                )
            ],
        )

        history = self.query_one(HistoryPanel)
        total = len(self.commits)
        position = Text(
            f"heading · {total} rows"
            if history.selected == HEADER_ROW
            else f"{min(total, history.selected + 1)}/{total}",
            style=Style(color=theme.DIM),
        )
        history_panel.set_edges(
            top_left=[
                label("history", num="³", bold=True),
                self._roster_legend(),
                self._dot_legend(),
                self._inferred_legend(),
            ],
            top_right=[
                Text(f"{total} commits read", style=Style(color=theme.DIM))
            ],
            bottom_left=[
                label("enter or click for the log", "enter"),
                label("pager", "o"),
            ],
            bottom_right=[Text(self.note, style=Style(color=theme.HI)) if self.note else position],
        )

        count, resident, cpu = totals(self.jvms)
        mine = sum(1 for jvm in self.jvms if jvm.mine)
        jvms_panel.set_edges(
            top_left=[
                label("jvms", num="⁴", bold=True),
                Text(
                    f"{count} java process(es), {mine} from this checkout",
                    style=Style(color=theme.DIM),
                ),
            ],
            top_right=[self._load_note(resident, cpu)],
            bottom_right=[
                Text(
                    "cpu bar: share of the machine, the figure: percent of one "
                    "core  ·  mem bar: against -Xmx where there is one",
                    style=Style(color=theme.DIM),
                )
            ],
        )

        live_panel.set_edges(
            top_left=[
                label("live", num="⁵", bold=True),
                self._live_bar_legend(),
            ],
            top_right=[self._live_note()],
            bottom_right=[
                Text(
                    "one column per part, eight dot rows tall  ·  the same "
                    "parts the ³history packs eight to a cell",
                    style=Style(color=theme.DIM),
                )
            ],
        )

    def _live_bar_legend(self) -> Text:
        """What a column of the ⁵live tile is worth, in its own vocabulary.

        A full column is a part with a verdict, a moving one is a part in
        flight, and the baseline row is a part not started — the three states a
        bar can be in, named because a bar chart of one part per column is not
        the packed strip the other tiles draw.
        """
        out = Text()
        for state, level, word in (
            ("passed", BAR_ROWS, "done"),
            ("running", 5, "in flight"),
            ("missing", 1, "not started"),
        ):
            out.append(bar_cells(level)[1], Style(color=state_color(state)))
            out.append(f" {word}  ", Style(color=theme.DIM))
        return out

    def _load_note(self, resident: int, cpu: float) -> Text:
        """What the JVMs cost, and what the machine is carrying in all.

        The load average is here rather than in the repo tile because the number
        it explains is in this one: eight JVMs at 40% apiece and a load of 18
        says the box is oversubscribed by something none of these rows is.
        """
        note = Text()
        note.append(
            f"{human_bytes(resident)} resident", Style(color=theme.FG, bold=True)
        )
        note.append(
            f"  ·  {cpu / max(1, self.cores):.0f}% of {self.cores} cores",
            Style(color=theme.DIM),
        )
        try:
            one, five, fifteen = os.getloadavg()
        except OSError:
            return note
        colour = theme.HI if one > self.cores else theme.DIM
        note.append(f"  ·  load {one:.2f} {five:.2f} {fifteen:.2f}", Style(color=colour))
        return note

    def _live_note(self) -> Text:
        """How many runs are going, and how many have gone quiet.

        The two are counted apart because they are different news: one says work
        is happening, the other says a run is holding a column and has not
        written a line in minutes.
        """
        if not self.live:
            return Text(
                f"{len(self.ledger.runs)} recorded", style=Style(color=theme.DIM)
            )
        stalled = sum(1 for run in self.live.values() if run.stalled)
        note = Text()
        going = len(self.live) - stalled
        if going:
            note.append(
                f"{going} running", Style(color=state_color("running"), bold=True)
            )
        if stalled:
            if going:
                note.append("  ", Style(color=theme.DIM))
            note.append(
                f"{stalled} stalled",
                Style(color=state_color("interrupted"), bold=True),
            )
        return note

    def _roster_legend(self) -> Text:
        """What a MARK means — the glyph a run with nothing to count draws.

        Beside it, `_dot_legend` says what a cell of dots is worth. The two are
        separate vocabularies on one screen and each needs naming: a tick is a
        verdict, and a cell is eight parts.
        """
        out = Text()
        for state, word in (
            ("passed", "pass"),
            ("failed", "fail"),
            ("running", "running"),
            ("missing", "none"),
        ):
            out.append(state_mark(state), Style(color=state_color(state), bold=True))
            out.append(f" {word}  ", Style(color=theme.DIM))
        return out

    def _dot_legend(self) -> Text:
        """The other vocabulary: a cell of dots, where each dot is one part."""
        out = Text()
        out.append("⣿", Style(color=state_color("passed"), bold=True))
        out.append(" = 8 parts", Style(color=theme.DIM))
        return out

    def _inferred_legend(self) -> Text:
        """The third: a verdict glyph in the never-ran grey, which no run at
        that commit produced.

        Short because it sits third on one edge. The grey makes the same claim
        at every size — nothing the check reads changed between this commit and
        the one that ran, so the answer is the one that run reached.
        """
        out = Text()
        out.append_text(
            faded(Text(state_mark("passed"), Style(color=state_color("passed"), bold=True)))
        )
        out.append(" = inferred", Style(color=theme.DIM))
        return out

    # ---- actions ------------------------------------------------------------

    def _history(self) -> HistoryPanel:
        return self.query_one(HistoryPanel)

    def action_select_up(self) -> None:
        panel = self._history()
        panel.selected -= 1
        panel.refresh()
        self.update_edges()

    def action_select_down(self) -> None:
        panel = self._history()
        panel.selected += 1
        panel.refresh()
        self.update_edges()

    def action_page_up(self) -> None:
        panel = self._history()
        panel.selected -= panel.table_rows
        panel.refresh()
        self.update_edges()

    def action_page_down(self) -> None:
        panel = self._history()
        panel.selected += panel.table_rows
        panel.refresh()
        self.update_edges()

    def action_select_head(self) -> None:
        """`home` — the heading, which is the top of the table and where the
        selection rests. The newest commit is one `down` from it."""
        panel = self._history()
        panel.selected = HEADER_ROW
        panel.refresh()
        self.update_edges()

    def action_select_oldest(self) -> None:
        panel = self._history()
        panel.selected = len(self.commits) - 1
        panel.refresh()
        self.update_edges()

    def action_toggle_status(self) -> None:
        self.show_status = not self.show_status
        self._fit(self.app.size.height)

    def action_toggle_runs(self) -> None:
        self.show_runs = not self.show_runs
        self._fit(self.app.size.height)

    def action_toggle_history(self) -> None:
        self.show_history = not self.show_history
        self._fit(self.app.size.height)

    def action_toggle_jvms(self) -> None:
        self.show_jvms = not self.show_jvms
        self._fit(self.app.size.height)

    def action_toggle_live(self) -> None:
        self.show_live = not self.show_live
        self._fit(self.app.size.height)

    def action_reload(self) -> None:
        self.note = ""
        self.reload()

    def action_detail(self) -> None:
        commit = self._selected_commit()
        if commit is None:
            return
        inferred = [
            (check, self.inferred.get(check.key, {}).get(commit.sha))
            for check in CHECKS
        ]
        self.app.push_screen(
            RunDetailScreen(
                self.root,
                commit,
                self.ledger.at(commit.sha),
                [(check, run) for check, run in inferred if run is not None],
            )
        )

    def _selected_commit(self):
        """The commit the selection is on, or None where it is on the heading.

        None rather than the first commit: the heading is where the selection
        starts, and a key that opened HEAD from there would open something
        nobody picked.
        """
        panel = self._history()
        if not self.commits or panel.selected == HEADER_ROW:
            return None
        return self.commits[max(0, min(len(self.commits) - 1, panel.selected))]

    def action_open_log(self) -> None:
        """Hand the selected commit's newest log to $PAGER, with the UI
        suspended. A log is thousands of lines and a pager already knows how to
        read one; re-implementing search and scroll in here would be a worse
        pager attached to a status screen."""
        commit = self._selected_commit()
        if commit is None:
            return
        runs = self.ledger.at(commit.sha)
        files = [self.root / run.log for run in reversed(runs) if (self.root / run.log).is_file()]
        if not files:
            self.note = "no log file at this revision"
            self.update_edges()
            return
        pager = os.environ.get("PAGER", "less")
        with self.app.suspend():
            subprocess.call([pager, "-R", str(files[0])])
        self.note = ""
        self.refresh()

    def action_quit_app(self) -> None:
        self.app.exit()


class VtopApp(App):
    """btop's frame around the vaelii checkout."""

    TITLE = "vaelii-top"

    # Ctrl-C quits, from any screen and however many times it is pressed.
    #
    # Textual binds `ctrl+c` to `action_help_quit`, which quits nothing and
    # raises a toast reading "Press Ctrl+Q to quit" — so a reflexive Ctrl-C
    # leaves the UI up and advertises a key this tool does not use. `priority`
    # is what puts this ahead of the focused widget, and an App binding applies
    # on the modal detail screen too, so there is no screen the key does not
    # reach. `ctrl+q` stays bound because Textual binds it; it is not a key
    # anything here names.
    BINDINGS = [
        Binding("ctrl+c", "quit", "Quit", show=False, priority=True),
    ]
    CSS = """
    Screen {
        background: $vbg;
        color: $vfg;
    }
    #status-panel {
        height: 13;
    }
    #runs-panel {
        height: 7;
    }
    #history-panel {
        height: 1fr;
    }
    #jvms-panel {
        height: 11;
    }
    #live-panel {
        height: 3;
    }
    #tile-menu {
        height: 1fr;
        display: none;
    }
    /* The gutter that keeps a panel's content off its own frame: one row top
       and bottom, TWO cells each side.  Panel.DEFAULT_CSS says `1 1`, which
       lands a row flush against the `│` — readable in a flame graph, which
       wants every cell, and tight under a table of text.  Stated here rather
       than in theme.py so that file stays the copy jstacks has. */
    StatusPanel {
        height: 1fr;
        margin: 1 2;
    }
    RunsPanel {
        height: 1fr;
        margin: 1 2;
    }
    HistoryPanel {
        height: 1fr;
        margin: 1 2;
    }
    LivePanel {
        height: 1fr;
        margin: 1 2;
    }
    JvmPanel {
        height: 1fr;
        margin: 1 2;
    }
    RunDetailScreen {
        align: center middle;
        background: $vbg 60%;
    }
    #detail-panel {
        width: 92%;
        height: 86%;
        background: $vbg;
    }
    #detail-scroll {
        background: $vbg;
        scrollbar-size-vertical: 1;
        scrollbar-background: $vbg;
        scrollbar-background-hover: $vbg;
        scrollbar-background-active: $vbg;
        scrollbar-color: $vbox;
        scrollbar-color-hover: $vfg;
        scrollbar-color-active: $vfg;
    }
    #detail-body {
        height: auto;
    }
    """

    def get_css_variables(self) -> dict:
        variables = super().get_css_variables()
        variables.update(
            {
                "vbg": theme.BG,
                "vfg": theme.FG,
                "vbox": theme.HISTORY_BOX,
                "vsel": theme.SELECTED_BG,
            }
        )
        return variables

    def __init__(self, root: Path, commit_limit: int = 200) -> None:
        super().__init__()
        self.root = root
        self.commit_limit = commit_limit

    def on_mount(self) -> None:
        self.push_screen(TopScreen(self.root, self.commit_limit))
