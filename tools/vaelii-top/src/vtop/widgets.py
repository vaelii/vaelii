"""The two panels: the repo's status above, the history and the last runs below.

Both are plain `Widget.render()` widgets returning rich renderables, so a
repaint is one string build and no layout pass. The history widget owns the
selection and the scroll; the app repoints the panel edges around them.
"""

from __future__ import annotations

import time

from rich.console import Group, RenderableType
from rich.style import Style
from rich.text import Text
from textual import events
from textual.widget import Widget

from vtop import theme
from vtop.colors import (
    DIRT_MARK,
    STALE_FULL,
    STALE_GRADIENT,
    rgb_to_hex,
    state_color,
    state_mark,
)
from vtop.jvms import human_bytes
from vtop.runs import (
    CHECKS,
    MARKED_KINDS,
    ago,
    commit_distance,
    hms,
    moving_commits_since,
    roster_size,
    run_components,
)
from vtop.theme import GOOD, edge, gradient_at, label

# The ⁴jvms tile's fixed columns: the mark, the pid, the task, the two meters
# with their figures, and the elapsed time. Everything left over goes to the
# column that says which run a JVM belongs to, which is the one that reads
# better wide.
JVM_TASK_W = 26
JVM_FIXED_W = 2 + 7 + JVM_TASK_W + 16 + 19 + 8


def _note_width(width: int) -> int:
    return max(10, min(30, width - JVM_FIXED_W))


# The mark columns' width, headings included. Eight of them plus the revision
# and the age leave the subject whatever is left, which is why the headings are
# abbreviated rather than spelled out — and why this is 5 and not 6.
MARK_W = 5


def solid_meter(fraction: float, width: int, color: str, floor: int = 0) -> Text:
    """A btop bar meter in ONE colour, over a dark track.

    `theme.meter` colours each block along a gradient, so the bar states a
    scale running left to right. These bars state something else: the LENGTH is how
    fresh a verdict is and the COLOUR is how stale, so a gradient across the
    bar would say a fresh verdict is partly red.

    `floor` is the fewest blocks a bar that means something may draw. A verdict
    twelve commits back is fully stale and rounds to no blocks at all, which on
    the screen is the same bar a check that has never run gets — so a run that
    exists keeps one block, in its stale colour.
    """
    out = Text(no_wrap=True)
    if width <= 0:
        return out
    filled = max(floor, round(max(0.0, min(1.0, fraction)) * width))
    filled = min(width, filled)
    out.append("■" * filled, Style(color=color))
    out.append("─" * (width - filled), Style(color=theme.METER_BG))
    return out


def gradient_meter(fraction: float, width: int, stops) -> Text:
    """A btop bar meter coloured along a gradient, over the same dark track
    `solid_meter` uses.

    `theme.meter` fills its track with dim blocks, which is right in btop and
    wrong beside the bars above: on this screen a run of `■` is a quantity, and
    a meter whose empty half is also `■` reads as full to anyone who cannot
    separate the two greys — down a mono terminal, or in a screenshot.
    """
    out = Text(no_wrap=True)
    if width <= 0:
        return out
    filled = round(max(0.0, min(1.0, fraction)) * width)
    for i in range(width):
        if i < filled:
            out.append("■", Style(color=rgb_to_hex(gradient_at(stops, i / max(1, width - 1)))))
        else:
            out.append("─", Style(color=theme.METER_BG))
    return out


# Where each successive dot goes inside a braille cell: the left column top to
# bottom, then the right. A cell therefore fills as the count climbs — ⠁ ⠃ ⠇ ⡇
# ⡏ ⡟ ⡿ ⣿ — and a strip of them grows left to right the way btop's graphs do.
_FILL_ORDER = (0x01, 0x02, 0x04, 0x40, 0x08, 0x10, 0x20, 0x80)


def dot_cells(count: int) -> str:
    """`count` braille dots, packed eight to a cell, last cell part-filled."""
    out = []
    while count > 0:
        bits = 0
        for i in range(min(8, count)):
            bits |= _FILL_ORDER[i]
        out.append(chr(0x2800 + bits))
        count -= 8
    return "".join(out)


def packed_dots(passed: int, failed: int, absent: int) -> Text:
    """A run's parts as one dot each, eight to a braille cell.

    A verdict is one mark over as many as forty-eight checks, and "48 check(s)
    ok" states a count in digits a reader has to convert back into a size. This
    states it as a size: one dot per part, green for the ones that passed, red
    for the ones that failed, grey for the ones that did not run — a matrix's
    `--owed` three of fifteen leaves twelve grey dots, and a perf check below
    the gating floor is grey because it was measured and not judged.

    Each colour starts its own cell, because a braille cell takes one colour and
    a mixed one would have to lie about a dot. That costs at most two cells over
    a dense packing and keeps every dot honest.
    """
    out = Text(no_wrap=True)
    for count, state in ((passed, "passed"), (failed, "failed"), (absent, "missing")):
        if count > 0:
            out.append(dot_cells(count), Style(color=state_color(state)))
    return out


# Colour is what an inferred cell gives up. The GLYPH is the verdict — `✓`, `✗`,
# a braille cell of so many dots — and the never-ran grey under it says no run
# happened at this commit, which is the same grey a blank cell draws in. Three
# hues and not four, so the screen keeps colour for what was measured.
INFERRED_STYLE = Style(color=state_color("missing"), bold=False)


def faded(text: Text) -> Text:
    """The same cell, drawn in the never-ran grey and never bold.

    A cell is built either as one `Text(mark, style)` — whose style is the base
    and holds no span — or as a strip of appends, which holds spans and no base.
    Both are one colour here, so a mark and a strip read the same way.
    """
    out = Text(text.plain, INFERRED_STYLE, no_wrap=True, overflow="crop")
    if text.spans:
        out.stylize(INFERRED_STYLE, 0, len(text.plain))
    return out


# ---- the big bars, one part to a COLUMN ------------------------------------
#
# The history packs eight parts into one cell, because a row there is one commit
# among two hundred. The ⁵live tile has one job and four rows, so it spends a
# whole COLUMN on a part: two stacked braille cells, eight dot rows, filled from
# the bottom. `⣀ ⣤ ⣶ ⣿` is the ladder inside one cell, and a column is two of
# them — so a part is eight times the width and twice the height it has in the
# history, and the two still read as the same thing because the colours are the
# same colours.
#
# One part to a column also keeps the ORDER the run finished its parts in, which
# the packed strip gives up: a cell there takes one colour, so the strip has to
# group the passes and the failures apart. A column is one part, so it can be
# the part's own colour wherever the part sits.
_BAR_FILL = (0x00, 0xC0, 0xE4, 0xF6, 0xFF)  # a cell filled 0-4 dot rows, bottom up
BAR_ROWS = 8  # dot rows in one two-cell column

# How full a part's column is drawn. A part with a verdict fills it. A part not
# started gets the baseline row, which keeps the column's width and marks the
# slot the part will fill. A part in flight is neither, and PULSE draws it
# moving.
PART_LEVEL = {"passed": BAR_ROWS, "failed": BAR_ROWS, "missing": 1}

# The height a running column cycles through, one step per repaint. A part in
# flight has no progress to report — a matrix configuration says nothing at all
# between its first line and its last — so the column says "in flight" rather
# than a fraction it does not know. Offset by the column's index, which makes
# the block of running parts read as one movement across.
PULSE = (3, 4, 5, 6, 7, 6, 5, 4)


def bar_cells(level: int) -> tuple:
    """The upper and lower braille cell of a column filled `level` dot rows of
    eight, from the bottom. A blank upper cell is U+2800, which is a braille
    space and holds the column's width."""
    level = max(0, min(BAR_ROWS, level))
    return (
        chr(0x2800 + _BAR_FILL[max(0, level - 4)]),
        chr(0x2800 + _BAR_FILL[min(4, level)]),
    )


def live_parts(live) -> list:
    """A live run's parts as (state, index) in the order the run has them:
    what finished, what is in flight, what has not started."""
    parts = [(part.state, index) for index, part in enumerate(live.done)]
    start = len(parts)
    parts += [("running", start + i) for i in range(live.running)]
    start = len(parts)
    parts += [("missing", start + i) for i in range(live.pending)]
    return parts


def live_bars(live, now: float | None = None) -> tuple:
    """A live run's parts as two rows of braille columns, upper row first.

    Empty where the run has no parts to count: `lein test :fuzz` and `lein test
    :multi-jvm` are one JVM running one selector, and a bar chart of one column
    states a quantity that is not there. The caller draws a mark for those, the
    way every other tile does.
    """
    upper = Text(no_wrap=True)
    lower = Text(no_wrap=True)
    parts = live_parts(live)
    if live.kind in MARKED_KINDS or not parts:
        return (upper, lower)
    tick = int(now if now is not None else time.time())
    for state, index in parts:
        if state == "running":
            level = PULSE[(tick + index) % len(PULSE)]
        else:
            level = PART_LEVEL.get(state, 1)
        top, bottom = bar_cells(level)
        style = Style(color=state_color(state))
        upper.append(top, style)
        lower.append(bottom, style)
    return (upper, lower)


def live_dots(live) -> Text:
    """A run under way: what it has finished, what is in flight, what is left.

    Blue for the parts running right now, which is the whole of what a strip
    adds while a run goes — a lint eight checks in reads `⣿` green then one blue
    then two grey, and the blue moves.
    """
    out = Text(no_wrap=True)
    if live.kind in MARKED_KINDS:
        return out
    # NOTHING TO COUNT, NO STRIP. `lein test :fuzz` and `lein test :multi-jvm`
    # are one JVM running one selector: there are no parts, and a strip of one
    # dot is a dot that counts nothing — which is what the marks are for. Such a
    # row draws `▸` and says "under way" instead.
    if not live.expected and not live.done:
        return out
    passed = sum(1 for p in live.done if p.state == "passed")
    failed = sum(1 for p in live.done if p.state == "failed")
    for count, state in (
        (passed, "passed"),
        (failed, "failed"),
        (live.running, "running"),
        (live.pending, "missing"),
    ):
        if count > 0:
            out.append(dot_cells(count), Style(color=state_color(state)))
    return out


def live_for(live: dict, check, after: float = 0.0) -> object:
    """The run under way this column would show, newest across its sources.

    `after` is when the newest RECORDED run of this check started, and a live
    run older than that is not returned. A run that died leaves a log nothing
    finished, and the tile reads that as stalled for half an hour — so without
    this a lint that died at noon would keep the row from the lint that passed
    at half past, which is the row the tile exists to show.
    """
    best = None
    for key in check.keys:
        going = live.get(key)
        if going is None or going.started < after:
            continue
        if best is None or going.started > best.started:
            best = going
    return best


def run_dots(root, run) -> Text:
    """The packed strip for one run, or an empty Text where it has no parts."""
    if run.kind in MARKED_KINDS:
        return Text()
    parts = run_components(root, run)
    if not parts:
        return Text()
    passed = sum(1 for p in parts if p.state == "passed")
    failed = sum(1 for p in parts if p.state == "failed")
    # Parts the run did not judge, plus — for a matrix that says what roster it
    # was a subset of — the configurations that never ran at all.
    absent = len(parts) - passed - failed + max(0, roster_size(run) - len(parts))
    return packed_dots(passed, failed, absent)


def dirt_cell(dirty: int) -> Text:
    """The dirt column: two cells, the mark and a space, or two spaces.

    Its own column rather than a flag inside the summary, because it is a fact
    about WHICH TREE a verdict is about and belongs beside the revision. Fixed
    width so the columns after it line up down the tile whether a run was taken
    over a clean tree or not.
    """
    if dirty > 0:
        return Text(DIRT_MARK + " ", Style(color=theme.HI, bold=True))
    return Text("  ")


def _stale_color(distance) -> str:
    """The colour for a verdict `distance` commits behind HEAD."""
    if distance is None:
        return state_color("missing")
    t = min(1.0, distance / float(STALE_FULL))
    return rgb_to_hex(gradient_at(STALE_GRADIENT, t))


def _truncate(text: str, width: int) -> str:
    if width <= 1:
        return ""
    return text if len(text) <= width else text[: width - 1] + "…"


def _hour_axis(span: int, width: int) -> Text:
    """Three clock marks under the commit chart: oldest, midpoint, now.

    A braille cell holds two hours, and a series shorter than the chart is
    padded on the LEFT by `theme.braille_graph` — so the oldest label sits over
    the first cell that has a reading rather than at column zero, and a quiet
    weekend does not get a timestamp printed under empty space.
    """
    row = Text(no_wrap=True, overflow="crop")
    if width < 24 or span <= 0:
        return row
    now = time.time()
    slots = width * 2
    first = max(0, (slots - span)) // 2  # the leftmost cell with a reading
    last = width - 1

    def stamp(cell: int) -> str:
        return time.strftime("%a %H:%M", time.localtime(now - (slots - 1 - 2 * cell) * 3600))

    middle = (first + last) // 2
    line = [" "] * width
    for start, text in (
        (first, stamp(first)),
        (max(0, middle - len(stamp(middle)) // 2), stamp(middle)),
        (width - 3, "now"),
    ):
        start = max(0, min(width - len(text), start))
        # A label that would run into one already placed is dropped rather than
        # overwritten: two timestamps sharing characters read as a third time.
        if any(c != " " for c in line[max(0, start - 2) : start + len(text) + 2]):
            continue
        line[start : start + len(text)] = list(text)
    row.append("".join(line), Style(color=theme.GRAPH_TEXT))
    return row


class StatusPanel(Widget):
    """What the checkout is: version, branch, revision, dirt, distance from
    upstream, the tree's counts, and commits per hour over the last few days."""

    def __init__(self, screen_ref, **kwargs) -> None:
        super().__init__(**kwargs)
        self.screen_ref = screen_ref

    def render(self) -> RenderableType:
        status = self.screen_ref.status
        width = max(10, self.size.width)
        if status is None:
            return Text("reading the checkout …", style=Style(color=theme.DIM))

        rows = []

        # The revision line: what HEAD is, and how long it has been HEAD.
        head = Text(no_wrap=True, overflow="crop")
        head.append(f"{status.head:<10}", Style(color=theme.ACCENT, bold=True))
        subject_w = width - 10 - 8
        head.append(
            _truncate(status.head_subject, subject_w), Style(color=theme.FG)
        )
        head.append(
            f"{ago(status.head_when):>7}".rjust(width - head.cell_len),
            Style(color=theme.DIM),
        )
        rows.append(head)

        # The tree line. Dirt under src/ or test/ is called out on its own
        # because that is the dirt a verdict is taken over — the same two
        # directories scripts/lib/revision.sh reports.
        tree = Text(no_wrap=True, overflow="crop")
        tree.append(f"{'tree':<10}", Style(color=theme.DIM))
        if status.dirty_code:
            tree.append(DIRT_MARK + " ", Style(color=theme.HI, bold=True))
            tree.append(
                f"{status.dirty_code} dirty under src/ or test/",
                Style(color=theme.HI),
            )
        else:
            tree.append("src/ and test/ clean", Style(color=GOOD))
        tree.append(
            f"  ·  {status.dirty_all} modified  ·  {status.untracked} untracked",
            Style(color=theme.DIM),
        )
        rows.append(tree)

        # Upstream. A checkout with no upstream says so rather than showing
        # two zeros, which would read as "in step with a remote".
        remote = Text(no_wrap=True, overflow="crop")
        remote.append(f"{'upstream':<10}", Style(color=theme.DIM))
        if not status.upstream:
            remote.append("none tracked", Style(color=theme.DIM))
        else:
            remote.append(status.upstream, Style(color=theme.FG))
            remote.append("  ↑", Style(color=theme.DIM))
            remote.append(
                str(status.ahead),
                Style(color=theme.HI if status.ahead else theme.DIM, bold=bool(status.ahead)),
            )
            remote.append(" ↓", Style(color=theme.DIM))
            remote.append(
                str(status.behind),
                Style(color=theme.HI if status.behind else theme.DIM, bold=bool(status.behind)),
            )
        remote.append(
            f"   ·  {status.commits_total} commits", Style(color=theme.DIM)
        )
        rows.append(remote)

        counts = Text(no_wrap=True, overflow="crop")
        counts.append(f"{'tree size':<10}", Style(color=theme.DIM))
        counts.append(
            f"{status.src_namespaces} src ns  ·  {status.test_namespaces} test ns"
            f"  ·  {status.doc_pages} docs  ·  {status.kb_contexts} kb"
            f"  ·  {status.src_lines // 1000}k lines under src/",
            Style(color=theme.FG),
        )
        rows.append(counts)

        # Commits per hour, newest on the right — the same braille area chart
        # btop's cpu graph is, and jstacks' RUNNABLE graph. Two hours to a cell,
        # because a braille cell is two dot columns wide.
        graph_h = max(0, self.size.height - len(rows) - 1)
        if graph_h >= 2:
            series = self.screen_ref.commits_per_hour(hours=width * 2)
            peak = max(series) if series else 1.0
            rows.append(Text(""))
            caption = Text(no_wrap=True)
            caption.append(f"{'commits':<10}", Style(color=theme.DIM))
            caption.append(
                f"per hour over the last {len(series)} hour(s) — "
                f"{len(self.screen_ref.commits)} commits read, "
                f"peak {int(peak)} in an hour",
                Style(color=theme.GRAPH_TEXT),
            )
            rows.append(caption)
            # The axis costs a row, so a short terminal drops the axis first:
            # the chart still draws its bars and the caption still says how far
            # back the left edge is.
            axis = graph_h >= 4
            rows.extend(
                theme.braille_graph(
                    series,
                    width,
                    graph_h - (3 if axis else 2),
                    max(1.0, peak),
                    theme.CPU_GRADIENT,
                )
            )
            if axis:
                rows.append(_hour_axis(len(series), width))
        return Group(*rows)


class RunsPanel(Widget):
    """The last run of each check: verdict, freshness, and the revision it was
    taken at.

    Its own tile rather than a block above the history, because it is read on
    its own. The question "is this tree checked" is five rows and a glance; the
    history underneath answers the different question of what has landed since,
    and a reader who wants the first should not have to find it on top of the
    second. One consequence is that the five rows never scroll away.
    """

    def __init__(self, screen_ref, **kwargs) -> None:
        super().__init__(**kwargs)
        self.screen_ref = screen_ref

    def _live_row(self, line: Text, going, width: int) -> Text:
        # A run that has gone quiet reads amber and says for how long. Its parts
        # are still unfinished, so the strip is unchanged — what changed is
        # whether anything is working on them, and that is the thing worth
        # seeing: a matrix whose shells are alive and whose JVMs are gone looks
        # exactly like one that is running, until the clock says otherwise.
        colour = state_color("interrupted" if going.stalled else "running")
        mark = state_mark("interrupted" if going.stalled else "running")
        line.append(mark + "  ", Style(color=colour, bold=True))
        # The bar fills with the run rather than with its freshness: there is no
        # staleness to report about a run that is happening now. It counts parts
        # FINISHED, not parts started — a matrix that opened all fifteen logs
        # and has answered for none of them is at the beginning, and a full bar
        # over "0 of 15 done" says the opposite.
        fraction = (len(going.done) / going.expected) if going.expected else 0.0
        line.append_text(solid_meter(fraction, 10, colour, floor=1))
        line.append(f"  {going.revision or '—':<9}", Style(color=theme.ACCENT))
        line.append_text(dirt_cell(going.dirty))
        where = f"no output for {hms(going.quiet)}" if going.stalled else "running"
        line.append(f"{where:<24}", Style(color=colour))
        strip = live_dots(going)
        tail = f"{hms(going.elapsed):>7}  {'now':>4}"
        room = width - line.cell_len - len(tail) - 2
        if strip.cell_len and strip.cell_len + 2 <= room:
            line.append_text(strip)
            line.append("  ")
            room -= strip.cell_len + 2
        if going.expected:
            note = f"{len(going.done)} of {going.expected} done"
        else:
            note = "under way"
        line.append(_truncate(note, room), Style(color=theme.FG))
        line.append(tail.rjust(max(0, width - line.cell_len)), Style(color=theme.DIM))
        return line

    def render(self) -> RenderableType:
        width = max(20, self.size.width)
        ledger = self.screen_ref.ledger
        commits = self.screen_ref.commits
        rows = []
        live = self.screen_ref.live
        for check in CHECKS:
            run = ledger.latest(check)
            line = Text(no_wrap=True, overflow="crop")
            line.append(f"{check.column:<6}", Style(color=theme.TITLE))
            going = live_for(live, check, run.epoch if run is not None else 0.0)
            if going is not None:
                # A run under way replaces the last finished one in its row: the
                # row says where this check stands, and where it stands is
                # mid-run. The verdict it is about to reach is not one yet, so
                # the mark and the bar are blue and the age is how long it has
                # been going.
                rows.append(self._live_row(line, going, width))
                continue
            if run is None:
                line.append(
                    f"{state_mark('missing')}  ", Style(color=state_color("missing"))
                )
                line.append_text(solid_meter(0.0, 10, state_color("missing")))
                line.append("  " + " " * 9, Style(color=theme.DIM))
                line.append_text(dirt_cell(0))
                line.append("never run in this checkout", Style(color=theme.DIM))
                rows.append(line)
                continue
            distance = commit_distance(commits, run.revision)
            # The bar is filled against the commits that MOVED THIS CHECK, not
            # against every commit since. A `tools/` commit cannot change what
            # the suite answers, and a meter that counted it reported a green
            # taken at HEAD as five commits stale while the tree the suite reads
            # had not moved at all. `distance` still names the revision's place
            # in the history, because that is the question the revision answers.
            behind = moving_commits_since(commits, distance, check)
            colour = _stale_color(None if distance is None else behind)
            freshness = (
                0.0
                if distance is None
                else 1.0 - min(1.0, behind / float(STALE_FULL))
            )
            line.append(
                f"{state_mark(run.state)}  ",
                Style(color=state_color(run.state), bold=True),
            )
            line.append_text(solid_meter(freshness, 10, colour, floor=1))
            line.append(f"  {run.revision:<9}", Style(color=theme.ACCENT))
            line.append_text(dirt_cell(run.dirty))
            if distance is None:
                where = "older than this window"
            elif distance == 0:
                where = "at HEAD"
            elif behind == 0:
                # The revision is behind and the verdict is not: nothing this
                # check reads has landed since, so the answer still holds.
                where = f"{distance} back · reads HEAD"
            else:
                where = f"{distance} back · {behind} it reads"
            line.append(f"{where:<24}", Style(color=colour))
            tail = f"{hms(run.seconds):>7}  {ago(run.epoch):>4}"
            room = width - line.cell_len - len(tail) - 2
            # Packed eight dots to a cell, forty-eight checks are six cells —
            # so the strip sits BESIDE the sentence rather than replacing it,
            # and both fit. The strip says the shape, the sentence says the
            # figures.
            strip = run_dots(self.screen_ref.root, run)
            if strip.cell_len and strip.cell_len + 2 <= room:
                line.append_text(strip)
                line.append("  ")
                room -= strip.cell_len + 2
            # The suite is run three ways and this column takes the newest of
            # them, so a row filled by a matrix says so — otherwise "15 of 15
            # configurations" under `test` states a figure about the suite.
            note = run.summary
            if run.kind != check.kind:
                note = f"via {run.title} — {run.summary}"
            line.append(_truncate(note, room), Style(color=theme.FG))
            line.append(
                tail.rjust(max(0, width - line.cell_len)), Style(color=theme.DIM)
            )
            rows.append(line)
        return Group(*rows)


# The ⁵live tile's fixed left column: the history's heading for the check, then
# the check's full name on the upper row and the revision it started at on the
# lower one. Fixed so every run's bars start at the same cell and two runs can
# be read against each other.
LIVE_LABEL_W = 28

# How many runs under way the tile draws. Two rows apiece, and a machine with
# more than four checks going at once has a problem the ⁴jvms tile reports
# better than a fifth pair of bars would.
LIVE_ROWS_MAX = 4


class LivePanel(Widget):
    """The checks running RIGHT NOW, one part to a braille column.

    The `²runs` tile answers where each check last stood and the `³history`
    answers what has landed; this answers what is happening, and it is the only
    tile whose content changes between one repaint and the next. A run under way
    starts at HEAD or near it, so these bars are generally the top rows of the
    history being filled in — the same parts and the same colours, at eight
    times the width and twice the height, because a run you are waiting on is
    worth more of the screen than a commit from last week.
    """

    def __init__(self, screen_ref, **kwargs) -> None:
        super().__init__(**kwargs)
        self.screen_ref = screen_ref

    def _column_of(self, going) -> str:
        """The history heading this run will land in, or its kind where no
        column reads it.

        A column whose OWN key this is, before one that reads it second-hand: a
        matrix at `:default` fills both `mx:d` and `test`, and naming it `test`
        here would point at the wider column while the narrower one is the row
        the run is about.
        """
        for check in CHECKS:
            if going.key == check.keys[0]:
                return check.column
        for check in CHECKS:
            if going.key in check.keys:
                return check.column
        return going.kind

    def _rows(self, going, bar_w: int) -> list:
        """One run as two rows: the heading and the upper bars over the revision
        and the lower bars, with the count and the clock after them.

        `bar_w` is the widest bar block among the runs on screen, which every
        run pads to, so the figures line up down the tile even where one run has
        fifteen parts and the one under it has five.
        """
        state = "interrupted" if going.stalled else "running"

        upper = Text(no_wrap=True, overflow="crop")
        upper.append("  ")
        upper.append(f"{self._column_of(going):<6}", Style(color=theme.TITLE, bold=True))
        upper.append(f"{going.title:<{LIVE_LABEL_W - 8}}", Style(color=theme.FG))

        lower = Text(no_wrap=True, overflow="crop")
        lower.append("  ")
        lower.append(f"{going.revision or '?':<9}", Style(color=theme.ACCENT))
        lower.append_text(dirt_cell(going.dirty))
        lower.append(" " * max(0, LIVE_LABEL_W - lower.cell_len))

        top, bottom = live_bars(going)
        if top.cell_len and top.cell_len <= bar_w:
            upper.append_text(top)
            lower.append_text(bottom)
            drawn = top.cell_len
        else:
            # Nothing to count, or more parts than the tile is wide. Either way
            # the mark says "under way" without stating a quantity, which is the
            # rule every other tile follows: `lein test :fuzz` is one JVM, and a
            # bar chart of one column is not a chart.
            upper.append(
                state_mark(state), Style(color=state_color(state), bold=True)
            )
            lower.append(" ")
            drawn = 1
        pad = max(0, bar_w - drawn) + 2
        upper.append(" " * pad)
        lower.append(" " * pad)

        if going.expected:
            upper.append(
                f"{len(going.done)} of {going.expected} done", Style(color=theme.FG)
            )
        else:
            upper.append("under way", Style(color=theme.FG))
        lower.append(hms(going.elapsed), Style(color=theme.DIM))
        if going.stalled:
            lower.append(
                f"  silent {hms(going.quiet)}", Style(color=state_color("interrupted"))
            )
        return [upper, lower]

    def render(self) -> RenderableType:
        width = max(20, self.size.width)
        going = sorted(self.screen_ref.live.values(), key=lambda run: run.started)
        if not going:
            return Text(
                "no check is running — the bars fill here while one is",
                style=Style(color=theme.DIM),
            )
        going = going[:LIVE_ROWS_MAX]
        # Measured over the runs on screen and CLIPPED to what the tile is wide,
        # so a run with more parts than there is room for drops to its mark
        # rather than pushing the figures off the right edge.
        room = max(1, width - LIVE_LABEL_W - 20)
        bar_w = min(room, max(len(live_parts(run)) for run in going))
        rows = []
        for run in going:
            rows.extend(self._rows(run, bar_w))
        return Group(*rows)


class JvmPanel(Widget):
    """Every JVM on the machine: which run it belongs to, and what it costs.

    The tiles above answer what has been checked; this answers what is running
    the check. A row is one java process — the `lein` launcher and the JVM it
    trampolines into are two, because they are two, and folding them would hide
    the six hundred megabytes the launchers hold while a matrix runs fifteen of
    them.

    Processes from this checkout come first and are drawn at full weight; a JVM
    from another checkout, a daemon or somebody else's REPL is dimmed and kept,
    because the reason a suite is slow is often a process this repo did not
    start.
    """

    def __init__(self, screen_ref, **kwargs) -> None:
        super().__init__(**kwargs)
        self.screen_ref = screen_ref

    def _note(self, jvm) -> tuple:
        """(text, colour) for the middle column: what this JVM is part of.

        The PART of the live run where the process group names one, because
        that is the specific answer and the only one that differs down the
        column: thirteen JVMs of one matrix all belong to `matrix :default`, and
        a column repeating the run's progress on every row of them says nothing
        about any row. The run and its progress where no part is named, then the
        leiningen profile it compiles into, which at least says which classpath
        it is on.
        """
        going = self.screen_ref.live.get(jvm.run) if jvm.run else None
        if going is not None:
            colour = state_color("interrupted" if going.stalled else "running")
            if jvm.part:
                return (f"{going.title} — {jvm.part}", colour)
            if going.expected:
                return (
                    f"{going.title} — {len(going.done)} of {going.expected}",
                    colour,
                )
            return (going.title, colour)
        if jvm.role == "lein":
            return ("lein launcher", theme.DIM)
        if jvm.profile:
            return (f"profile {jvm.profile}", theme.DIM)
        if jvm.reads and not jvm.mine:
            return ("reads this checkout", theme.DIM)
        if not jvm.mine:
            return ("another checkout", theme.DIM)
        return ("", theme.DIM)

    def _row(self, jvm, width: int, cores: int, memory: int) -> Text:
        row = Text(no_wrap=True, overflow="crop")
        state = "running" if jvm.mine else "missing"
        row.append(
            f"{state_mark(state)} ",
            Style(color=state_color(state), bold=jvm.mine),
        )
        row.append(f"{jvm.pid:<7}", Style(color=theme.ACCENT if jvm.mine else theme.DIM))
        row.append(
            f"{_truncate(jvm.label, JVM_TASK_W - 1):<{JVM_TASK_W}}",
            Style(color=theme.FG if jvm.mine else theme.DIM),
        )
        note, note_color = self._note(jvm)
        note_w = _note_width(width)
        row.append(
            f"{_truncate(note, note_w - 1):<{note_w}}", Style(color=note_color)
        )

        # The CPU bar is a share of the WHOLE machine and the figure beside it
        # is percent of one core, so a shard JVM at 380% draws under half a bar
        # on ten cores and still says 380. One number would have to give up
        # either how hard the process is working or how much of the box is left.
        row.append_text(gradient_meter(jvm.cpu / (100.0 * max(1, cores)), 8, theme.CPU_GRADIENT))
        row.append(
            f" {jvm.cpu:>5.0f}% ",
            Style(color=theme.FG if jvm.cpu >= 1 else theme.DIM),
        )
        # Resident against the heap the JVM was given where `-Xmx` says, and
        # against physical memory where it does not: a 6g heap at 900M is a
        # different fact from 900M of a 64g box, and the bar means the tighter
        # of the two.
        ceiling = jvm.heap or memory or 1
        row.append_text(gradient_meter(jvm.rss / float(ceiling), 8, theme.CPU_GRADIENT))
        row.append(f" {human_bytes(jvm.rss):>5}", Style(color=theme.FG))
        row.append(
            f"/{human_bytes(jvm.heap):<4}" if jvm.heap else " " * 5,
            Style(color=theme.DIM),
        )
        row.append(f"{hms(jvm.elapsed):>8}", Style(color=theme.DIM))
        return row

    def _heading(self, width: int) -> Text:
        note_w = _note_width(width)
        head = Text(no_wrap=True, overflow="crop")
        head.append("  ")
        head.append(f"{'pid':<7}", Style(color=theme.DIM))
        head.append(f"{'task':<{JVM_TASK_W}}", Style(color=theme.DIM))
        head.append(f"{'belongs to':<{note_w}}", Style(color=theme.DIM))
        head.append(f"{'cpu':<16}", Style(color=theme.DIM))
        head.append(f"{'memory':<19}", Style(color=theme.DIM))
        head.append(f"{'time':>8}", Style(color=theme.DIM))
        return head

    def render(self) -> RenderableType:
        width = max(20, self.size.width)
        jvms = self.screen_ref.jvms
        if not jvms:
            return Text(
                "no JVM is running — nothing is being checked right now",
                style=Style(color=theme.DIM),
            )
        rows = [self._heading(width)]
        cores = self.screen_ref.cores
        memory = self.screen_ref.memory
        for jvm in jvms[: max(1, self.size.height - 1)]:
            rows.append(self._row(jvm, width, cores, memory))
        return Group(*rows)


# The selection's index for the HEADING, which is a row like any other but is
# not a commit. It is the resting position: the table opens on it, `up` from the
# newest commit returns to it, and it is the one row that never scrolls away, so
# a selection parked there cannot go off screen while you read something else.
# A negative index rather than an offset on every commit index, because then the
# commit indexes stay what they are — positions in `screen_ref.commits` — and
# every other reader of `selected` is unchanged.
HEADER_ROW = -1


class HistoryPanel(Widget):
    """The git history with one column per check.

    A row is a commit; a cell is that commit's verdict for one check, or a dot
    where the check has not run there. The `²runs` tile above says where each
    check last stood; this says what has landed since.

    The heading is selectable too, at HEADER_ROW. It carries no commit, so
    `enter` and `o` have nothing to open there — which is the point of it being
    where the selection starts: the tool opens with the table to read rather than
    with a commit picked out that nobody asked for.
    """

    def __init__(self, screen_ref, **kwargs) -> None:
        super().__init__(**kwargs)
        self.screen_ref = screen_ref
        self.selected = HEADER_ROW
        self.scroll = 0
        self.hover_row: int | None = None
        # Rows the last render put on screen, so a click maps back to a commit
        # without the widget having to recompute the layout.
        self._first_row = 0
        self._table_top = 0

    # ---- the table ----------------------------------------------------------

    def _verdict(self, run) -> Text:
        """What one recorded run draws: its packed strip, or the mark its
        verdict is where the run has no parts to count.

        A run taken over uncommitted work under `src/` or `test/` carries the
        dirt mark after it, the same `±` the `²runs` tile draws in a column of
        its own. The history has no column to spare, so the mark rides the cell
        — and it has to be there, because that verdict is about a tree no commit
        holds and nothing else in the row says so. Such a run is also refused as
        the source of an inferred cell (`runs.inferred_runs`), so without the
        mark a reader sees a green at one commit, no green at the next, and
        nothing that explains the gap.
        """
        strip = run_dots(self.screen_ref.root, run)
        if not strip.cell_len:
            strip = Text(
                state_mark(run.state), Style(color=state_color(run.state), bold=True)
            )
        if run.over_dirt:
            strip.append(DIRT_MARK, Style(color=theme.HI, bold=True))
        return strip

    def _cell(self, sha: str, check) -> Text:
        """One check's cell for one commit.

        A run with parts is its packed strip; a run without is the one mark its
        verdict is; a commit where the check never ran is a single grey dot.
        The three are the same vocabulary at three sizes, so a column reads down
        without the eye having to change what it is looking for.

        A commit with no run of its own may still have an answer: where nothing
        this check reads changed between it and a commit that did run, the two
        trees the check sees are the same tree and the verdict is the same
        verdict. Such a cell draws the glyph the run drew, in the never-ran
        grey: the shape is the verdict and the colour says no run happened here.
        Order of precedence is run under way, recorded run, inferred verdict,
        nothing — a recorded verdict is never replaced by an inferred one.
        """
        run = self.screen_ref.ledger.at_check(sha, check)
        going = live_for(
            self.screen_ref.live, check, run.epoch if run is not None else 0.0
        )
        if going is not None and going.revision and sha.startswith(going.revision[:7]):
            strip = live_dots(going)
            if strip.cell_len:
                return strip
            # A run with nothing to count draws its mark here too, or the cell
            # would be blank exactly while something is happening in it.
            state = "interrupted" if going.stalled else "running"
            return Text(state_mark(state), Style(color=state_color(state), bold=True))
        if run is not None:
            return self._verdict(run)
        taken_from = self.screen_ref.inferred.get(check.key, {}).get(sha)
        if taken_from is not None:
            return faded(self._verdict(taken_from))
        return Text(state_mark("missing"), Style(color=state_color("missing")))

    def _column_widths(self, visible: list) -> list:
        """How wide each check's column has to be, for the rows on screen.

        Measured over the VISIBLE rows rather than over the whole history, so a
        scroll through a stretch with no matrix run does not keep paying for the
        six cells one further down needs. It shifts as you scroll, which is the
        price of every column being exactly as wide as it has to be.
        """
        widths = []
        for check in CHECKS:
            wide = len(check.column)
            for commit in visible:
                wide = max(wide, self._cell(commit.sha, check).cell_len)
            widths.append(wide)
        return widths

    def _table_header(self, widths: list, selected: bool, hover: bool) -> Text:
        row = Text(no_wrap=True, overflow="crop")
        if selected:
            row.style = Style(bgcolor=theme.SELECTED_BG)
        elif hover:
            row.style = Style(bgcolor=theme.HOVER_BG)
        row.append("revision age  ", Style(color=theme.DIM))
        for check, wide in zip(CHECKS, widths):
            # Left, not centred: a cell's strip starts at the column's left
            # edge, so a centred heading sits off its own column.
            row.append(f"{check.column:<{wide}} ", Style(color=theme.TITLE))
        row.append(" subject", Style(color=theme.DIM))
        return row

    def _commit_row(
        self, index: int, width: int, widths: list, selected: bool, hover: bool
    ) -> Text:
        commit = self.screen_ref.commits[index]
        row = Text(no_wrap=True, overflow="crop")
        if selected:
            row.style = Style(bgcolor=theme.SELECTED_BG)
        elif hover:
            row.style = Style(bgcolor=theme.HOVER_BG)
        row.append(f"{commit.sha:<9}", Style(color=theme.ACCENT))
        row.append(f"{ago(commit.when):>3}  ", Style(color=theme.DIM))
        for check, wide in zip(CHECKS, widths):
            cell = self._cell(commit.sha, check)
            row.append_text(cell)
            row.append(" " * (wide - cell.cell_len + 1))
        row.append(" ")
        # A docs-only commit cannot move a verdict, so it is drawn quieter than
        # one under src/ or test/ — the distinction test-matrix.sh prints as
        # [src] / [docs] when it reports a tree that moved mid-run.
        style = Style(color=theme.FG) if commit.touches_code else Style(color=theme.DIM)
        row.append(_truncate(commit.subject, max(0, width - row.cell_len - 1)), style)
        return row

    @property
    def table_rows(self) -> int:
        """How many commit rows fit under the heading."""
        return max(1, self.size.height - 1)

    def clamp(self) -> None:
        """Keep the selection inside the table and scrolled into view.

        HEADER_ROW is the floor rather than zero, and it pins the scroll to the
        top: the heading sits above the first commit, so a selection on it with
        the table scrolled down would highlight a row that is not where the
        selection is.
        """
        total = len(self.screen_ref.commits)
        if total == 0:
            self.selected, self.scroll = HEADER_ROW, 0
            return
        self.selected = max(HEADER_ROW, min(total - 1, self.selected))
        if self.selected == HEADER_ROW:
            self.scroll = 0
            return
        rows = self.table_rows
        if self.selected < self.scroll:
            self.scroll = self.selected
        elif self.selected >= self.scroll + rows:
            self.scroll = self.selected - rows + 1
        self.scroll = max(0, min(max(0, total - rows), self.scroll))

    def render(self) -> RenderableType:
        width = max(20, self.size.width)
        self.clamp()
        commits = self.screen_ref.commits
        if not commits:
            rows = [
                Text("no history — is this a git checkout?", style=Style(color=theme.DIM))
            ]
            self._table_top = 0
            return Group(*rows)
        visible = commits[self.scroll : self.scroll + self.table_rows]
        widths = self._column_widths(visible)
        rows = [
            self._table_header(
                widths,
                self.selected == HEADER_ROW,
                self.hover_row == HEADER_ROW,
            )
        ]
        self._table_top = len(rows)
        self._first_row = self.scroll
        for offset, _ in enumerate(visible):
            index = self.scroll + offset
            rows.append(
                self._commit_row(
                    index, width, widths,
                    index == self.selected, index == self.hover_row,
                )
            )
        return Group(*rows)

    # ---- pointing at a row --------------------------------------------------

    def _row_at(self, y: int):
        """The row the pointer is over: a commit's index, HEADER_ROW for the
        heading, or None off the table."""
        if not self.screen_ref.commits:
            return None
        if y == self._table_top - 1:
            return HEADER_ROW
        index = self._first_row + (y - self._table_top)
        if self._table_top <= y and 0 <= index < len(self.screen_ref.commits):
            return index
        return None

    def on_mouse_move(self, event: events.MouseMove) -> None:
        row = self._row_at(event.y)
        if row != self.hover_row:
            self.hover_row = row
            self.refresh()

    def on_leave(self) -> None:
        if self.hover_row is not None:
            self.hover_row = None
            self.refresh()

    def on_click(self, event: events.Click) -> None:
        """Select the row under the pointer and open it.

        One click and not two: a row here is not something you edit, so there is
        nothing a selection does on its own that a reader would want without the
        detail behind it — and a click that only moved a highlight leaves the
        log a key press away with nothing saying which key.
        """
        row = self._row_at(event.y)
        if row is None:
            return
        self.selected = row
        self.refresh()
        # The heading carries no commit, so a click on it moves the selection
        # and opens nothing.
        if row != HEADER_ROW:
            self.screen_ref.action_detail()
        else:
            self.screen_ref.update_edges()

    def on_mouse_scroll_down(self, event: events.MouseScrollDown) -> None:
        self.scroll += 3
        self.selected = max(self.selected, self.scroll)
        self.refresh()
        event.stop()

    def on_mouse_scroll_up(self, event: events.MouseScrollUp) -> None:
        self.scroll = max(0, self.scroll - 3)
        self.selected = min(self.selected, self.scroll + self.table_rows - 1)
        self.refresh()
        event.stop()


class TileMenu(Widget):
    """What is on the screen when nothing is: the tiles and the keys that bring
    them back.

    A tile hidden by its own number is easy to hide and, with the screen blank,
    impossible to find again — the bindings are still live but nothing on the
    screen says so. So the last tile going away puts this in its place: one row
    per tile, its number picked out, and what that tile carries.

    It draws its own box rather than living in a `Panel`, because a panel fills
    its region and this is a small thing in the middle of an empty screen.
    """

    def __init__(self, screen_ref, **kwargs) -> None:
        super().__init__(**kwargs)
        self.screen_ref = screen_ref

    def _entries(self) -> list:
        """One row per tile: the key, the name, and what it carries.

        The roster is the screen's, so a tile added there shows up here without
        this file being edited — a menu that listed the tiles itself would be a
        second roster, and the one that went short would be the one nobody
        looks at until they need it.
        """
        return [
            (key, name, blurb)
            for key, name, blurb, _ in self.screen_ref.tiles()
        ]

    def render(self) -> RenderableType:
        width, height = self.size.width, self.size.height
        entries = self._entries()
        if width < 24 or height < len(entries) + 4:
            return Text("1 2 3 — tiles", style=Style(color=theme.DIM))

        color = theme.STATUS_BOX
        inner = [
            Text.assemble(
                ("  "),
                (f"{key}", Style(color=theme.HI, bold=True)),
                (f"  {name:<9}", Style(color=theme.TITLE)),
                (blurb, Style(color=theme.DIM)),
            )
            for key, name, blurb in entries
        ]
        inner.append(Text(""))
        inner.append(
            Text.assemble(
                ("  "),
                ("r", Style(color=theme.HI, bold=True)),
                ("  reload     ", Style(color=theme.TITLE)),
                ("q", Style(color=theme.HI, bold=True)),
                ("  quit", Style(color=theme.TITLE)),
            )
        )
        box_w = min(width - 4, max(38, max(line.cell_len for line in inner) + 4))

        rows = [
            edge(box_w, color, left=[label("tiles", bold=True)],
                 right=[Text("all hidden", style=Style(color=theme.DIM))])
        ]
        side = Style(color=color)
        for line in inner:
            row = Text("│", style=side, no_wrap=True, overflow="crop")
            row.append_text(line)
            pad = box_w - 2 - line.cell_len
            row.append(" " * max(0, pad))
            row.append("│", side)
            rows.append(row)
        rows.append(edge(box_w, color, top=False))

        # Centred by padding, not by CSS: the tiles this replaces are laid out
        # in a column that fills the screen, and an alignment rule on their
        # container would move them too.
        left = " " * max(0, (width - box_w) // 2)
        for row in rows:
            row.pad_left(len(left))
        top = max(0, (height - len(rows)) // 2)
        return Group(*([Text("")] * top + rows))


def _clock() -> Text:
    return Text(time.strftime("%H:%M:%S"), style=Style(color=theme.TITLE))
