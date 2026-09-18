"""btop-style drawing: the palette, framed panels whose edges carry
┐segment┌ labels, gradient meters, and braille graphs.

Taken from jstacks (../jstacks/src/jstacks/theme.py) with the two panel-frame
fields renamed for this screen's panels.  The drawing code is unchanged, so a
fix to an edge or a meter belongs in both.

The DEFAULT palette has one value jstacks does not: `selected_bg` is neutral
here rather than `#6a2f2f`, because red on this screen is a failed verdict and
a red selection bar crossed a row of green cells. Do not restore it from the
other tree.

The palette can be loaded from a btop `.theme` file (see load_theme). Those
files are plain `theme[key]="#rrggbb"` data, so we parse them ourselves and
read whatever btop already installed; nothing is bundled or copied. Colors
that carry meaning rather than style stay fixed: the verdict colors in
colors.py (green is a pass whatever the theme says) and the staleness
gradient.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from rich.console import Group, RenderableType
from rich.style import Style
from rich.text import Text
from textual.widget import Widget

from vtop.colors import blend, rgb_to_hex

RGB = tuple[int, int, int]


@dataclass(frozen=True)
class Theme:
    """Every color the chrome draws with."""

    name: str
    bg: str
    fg: str
    title: str  # panel titles
    hi: str  # hotkey letters and the superscript box numbers
    inactive: str  # unlit toggles, launcher rows
    dim: str  # secondary text
    meter_bg: str  # the unfilled part of a meter
    graph_text: str  # captions drawn over a graph
    selected_bg: str  # the history table's selection bar, a neutral tint
    selected_fg: str
    status_box: str  # the ¹repo panel's frame
    runs_box: str  # the ²runs panel's frame
    history_box: str  # the ³history panel's frame
    accent: str  # the revision column
    cpu_gradient: tuple  # the braille graph, bottom to top

    @property
    def hover_bg(self) -> str:
        """The table's hover tint, a step from the background toward the text."""
        return rgb_to_hex(blend(hex_to_rgb(self.bg), hex_to_rgb(self.fg), 0.08))


# Run status. Green reads as clean and yellow as held in any palette, so these
# stay put rather than following a theme.
GOOD = "#77ca9b"
WARN = "#cbc06c"

DEFAULT = Theme(
    name="default",
    bg="#000000",
    fg="#cccccc",
    title="#eeeeee",
    hi="#e0484f",
    inactive="#5a5a5a",
    dim="#808080",
    meter_bg="#3a3a3a",
    graph_text="#606060",
    # A step of the background toward the text, and no hue. Red belongs to a
    # failed verdict on this screen, and a selection bar in it put a red band
    # across a row of green cells that said nothing about any of them.
    selected_bg="#2d2d2d",
    selected_fg="#cccccc",
    status_box="#556d59",
    runs_box="#5b6480",
    history_box="#805252",
    accent="#74c7b8",
    cpu_gradient=((0x77, 0xCA, 0x9B), (0xCB, 0xC0, 0x6C), (0xDC, 0x4C, 0x4C)),
)

_active = DEFAULT

# The uppercase names the widgets read (theme.FG, theme.HI, ...), resolved
# against whichever theme is active when the line is drawn.
_FIELDS = {
    "BG": "bg",
    "FG": "fg",
    "TITLE": "title",
    "HI": "hi",
    "INACTIVE": "inactive",
    "DIM": "dim",
    "METER_BG": "meter_bg",
    "GRAPH_TEXT": "graph_text",
    "SELECTED_BG": "selected_bg",
    "SELECTED_FG": "selected_fg",
    "STATUS_BOX": "status_box",
    "RUNS_BOX": "runs_box",
    "HISTORY_BOX": "history_box",
    "ACCENT": "accent",
    "CPU_GRADIENT": "cpu_gradient",
    "HOVER_BG": "hover_bg",
}


def __getattr__(name: str):  # PEP 562
    field = _FIELDS.get(name)
    if field is None:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    return getattr(_active, field)


def active() -> Theme:
    return _active


def use(theme: Theme) -> None:
    """Make `theme` the palette every later repaint draws with."""
    global _active
    _active = theme


def hex_to_rgb(color: str) -> RGB:
    color = color.lstrip("#")
    return (int(color[0:2], 16), int(color[2:4], 16), int(color[4:6], 16))


def fade(color: str, amount: float) -> str:
    """Darken a hex color toward the background by `amount` (0..1)."""
    return rgb_to_hex(blend(hex_to_rgb(color), hex_to_rgb(_active.bg), amount))


def gradient_at(stops: Sequence[RGB], t: float) -> RGB:
    """The color `t` (0..1) of the way along a multi-stop gradient."""
    t = max(0.0, min(1.0, t))
    if len(stops) == 1:
        return stops[0]
    pos = t * (len(stops) - 1)
    i = min(int(pos), len(stops) - 2)
    return blend(stops[i], stops[i + 1], pos - i)


# --- btop .theme files ----------------------------------------------------

_THEME_LINE_RE = re.compile(r'^\s*theme\[([a-z_]+)\]\s*=\s*"([^"]*)"')

THEME_DIRS = (
    "~/.config/btop/themes",
    "$XDG_CONFIG_HOME/btop/themes",
    "/usr/share/btop/themes",
    "/usr/local/share/btop/themes",
    "/opt/homebrew/share/btop/themes",
)


class ThemeError(RuntimeError):
    pass


def parse_theme(text: str) -> dict[str, str]:
    """The `theme[key]="value"` pairs in a btop theme file, ignoring comments
    and anything else. A value is `#rrggbb`, a `#gg` greyscale shorthand, or
    empty (meaning "use the terminal default"); all three come back as
    written, normalized to 6 digits where they name a color."""
    colors: dict[str, str] = {}
    for line in text.splitlines():
        match = _THEME_LINE_RE.match(line)
        if match is None:
            continue
        key, value = match.group(1), match.group(2).strip()
        if re.fullmatch(r"#[0-9a-fA-F]{6}", value):
            colors[key] = value.lower()
        elif re.fullmatch(r"#[0-9a-fA-F]{2}", value):
            grey = value[1:].lower()
            colors[key] = f"#{grey * 3}"  # btop's greyscale shorthand
    return colors


def theme_from_colors(name: str, colors: dict[str, str]) -> Theme:
    """Map btop's keys onto our palette. btop themes carry keys for panels we
    don't have (temperature, memory, network, disk), which we ignore, and a
    few of ours are missing from most themes, so each falls back to something
    the file does define."""

    def pick(*keys: str, default: str) -> str:
        for key in keys:
            if colors.get(key):
                return colors[key]
        return default

    bg = pick("main_bg", default=DEFAULT.bg)  # empty means terminal default
    fg = pick("main_fg", default=DEFAULT.fg)
    inactive = pick("inactive_fg", default=rgb_to_hex(blend(hex_to_rgb(fg), hex_to_rgb(bg), 0.55)))
    dim = pick("graph_text", default=rgb_to_hex(blend(hex_to_rgb(fg), hex_to_rgb(bg), 0.4)))
    gradient = tuple(
        hex_to_rgb(colors[key]) for key in ("cpu_start", "cpu_mid", "cpu_end") if colors.get(key)
    )
    return Theme(
        name=name,
        bg=bg,
        fg=fg,
        title=pick("title", default=fg),
        hi=pick("hi_fg", default=fg),
        inactive=inactive,
        dim=dim,
        # Only a handful of themes set meter_bg, and div_line is no
        # substitute (it's pure black in some light themes, which would draw
        # the empty part of a meter heavier than the full part). Derive a
        # quiet track from the text color instead.
        meter_bg=pick(
            "meter_bg",
            default=rgb_to_hex(blend(hex_to_rgb(fg), hex_to_rgb(bg), 0.82)),
        ),
        graph_text=pick("graph_text", default=dim),
        selected_bg=pick("selected_bg", default=DEFAULT.selected_bg),
        selected_fg=pick("selected_fg", default=fg),
        status_box=pick("cpu_box", "div_line", default=fg),
        runs_box=pick("mem_box", "div_line", default=fg),
        history_box=pick("proc_box", "div_line", default=fg),
        accent=pick("proc_misc", default=fg),
        cpu_gradient=gradient if len(gradient) == 3 else DEFAULT.cpu_gradient,
    )


def theme_dirs() -> list[Path]:
    dirs = []
    for entry in THEME_DIRS:
        path = Path(os.path.expandvars(os.path.expanduser(entry)))
        if "$" not in str(path) and path.is_dir():
            dirs.append(path)
    return dirs


def available_themes() -> dict[str, Path]:
    """Installed btop themes by name, nearest config directory winning."""
    found: dict[str, Path] = {}
    for directory in theme_dirs():
        for path in sorted(directory.glob("*.theme")):
            found.setdefault(path.stem, path)
    return found


def load_theme(name_or_path: str) -> Theme:
    """Load a btop theme by name (as installed) or by path. "default" is our
    own built-in palette. Raises ThemeError if it can't be found or holds no
    colors we recognize."""
    if name_or_path in ("default", ""):
        return DEFAULT
    path = Path(name_or_path).expanduser()
    if not path.is_file():
        found = available_themes().get(name_or_path)
        if found is None:
            known = ", ".join(sorted(available_themes())) or "none found"
            raise ThemeError(f"unknown theme {name_or_path!r}. Installed: {known}")
        path = found
    try:
        text = path.read_text(errors="replace")
    except OSError as exc:
        raise ThemeError(f"could not read {path}: {exc}") from exc
    colors = parse_theme(text)
    if not colors:
        raise ThemeError(f"{path} has no theme[...] colors in it")
    return theme_from_colors(path.stem, colors)


# --- drawing --------------------------------------------------------------


def label(
    text: str,
    key: str | None = None,
    *,
    num: str | None = None,
    active: bool = True,
    bold: bool = False,
    color: str | None = None,
) -> Text:
    """The content of one ┐segment┌: text in the title color (grey when
    inactive) with its hotkey picked out in red. A key that doesn't occur in
    the text is prefixed instead ("9 kill -9"); `num` adds a btop-style
    superscript box number ("¹jvm")."""
    base = Style(color=color or (_active.title if active else _active.inactive), bold=bold)
    hot = Style(color=_active.hi, bold=bold)
    out = Text()
    if num:
        out.append(num, hot)
    i = text.find(key) if key else -1
    if key and i < 0:
        out.append(key, hot)
        out.append(" " + text, base)
    elif key:
        out.append(text[:i], base)
        out.append(key, hot)
        out.append(text[i + len(key) :], base)
    else:
        out.append(text, base)
    return out


def _fit(text: Text, width: int) -> None:
    """Crop in place to `width` cells, ending in … when something was cut.
    Rich's ellipsis overflow still emits the … at width 0, so crop there."""
    width = max(0, width)
    text.truncate(width, overflow="ellipsis" if width >= 1 else "crop")


def edge(
    width: int,
    color: str,
    left: Iterable[Text] = (),
    right: Iterable[Text] = (),
    center: Text | None = None,
    *,
    top: bool = True,
) -> Text:
    """One full edge of a panel, corners included, exactly `width` cells:
    ╭─┐a┌─┐b┌──────┐center┌──────┐c┌─╮. Whatever doesn't fit is dropped,
    the center first. A top edge (titles left, toggles right) then sheds
    right-side segments from the inside out, then left-side ones from the
    end; a bottom edge (key hints left, a counter right) sheds the hints
    first. A lone survivor is cropped."""
    line = Style(color=color)
    corner_l, corner_r = ("╭", "╮") if top else ("╰", "╯")
    if width < 2:
        return Text(corner_l[:width], style=line)
    inner = width - 2
    open_, close = ("┐", "┌") if top else ("┘", "└")

    def wrap(seg: Text) -> Text:
        t = Text(open_, style=line)
        t.append_text(seg)
        t.append(close, line)
        return t

    def run(segs: list[Text], lead: bool) -> Text:
        t = Text()
        if segs and lead:
            t.append("─", line)
        for i, seg in enumerate(segs):
            if i:
                t.append("─", line)
            t.append_text(wrap(seg))
        if segs and not lead:
            t.append("─", line)
        return t

    lefts, rights = list(left), list(right)

    def too_long() -> bool:
        return run(lefts, True).cell_len + run(rights, False).cell_len > inner

    if top:
        while rights and too_long():
            rights.pop(0)
        while len(lefts) > 1 and too_long():
            lefts.pop()
    else:
        while lefts and too_long():
            lefts.pop()
        while len(rights) > 1 and too_long():
            rights.pop(0)
    head = run(lefts, True)
    _fit(head, inner)
    tail = run(rights, False)
    _fit(tail, inner - head.cell_len)

    body = Text(corner_l, style=line, no_wrap=True, overflow="crop")
    body.append_text(head)
    gap = inner - head.cell_len - tail.cell_len
    mid = wrap(center) if center is not None else None
    start = (inner - mid.cell_len) // 2 if mid is not None else 0
    if mid is not None and head.cell_len < start and start + mid.cell_len < inner - tail.cell_len:
        body.append("─" * (start - head.cell_len), line)
        body.append_text(mid)
        body.append("─" * (inner - tail.cell_len - start - mid.cell_len), line)
    else:
        body.append("─" * gap, line)
    body.append_text(tail)
    body.append(corner_r, line)
    return body


def meter(fraction: float, width: int, stops: Sequence[RGB]) -> Text:
    """A btop bar meter: `width` ■ blocks, the filled share colored along the
    gradient, the rest a dark track."""
    out = Text(no_wrap=True)
    if width <= 0:
        return out
    filled = round(max(0.0, min(1.0, fraction)) * width)
    for i in range(width):
        if i < filled:
            color = rgb_to_hex(gradient_at(stops, i / max(1, width - 1)))
        else:
            color = _active.meter_bg
        out.append("■", Style(color=color))
    return out


# Braille dot bits per column, bottom row first.
_LEFT_DOTS = (0x40, 0x04, 0x02, 0x01)
_RIGHT_DOTS = (0x80, 0x20, 0x10, 0x08)


def braille_graph(
    values: Sequence[float],
    width: int,
    height: int,
    max_value: float,
    stops: Sequence[RGB],
) -> list[Text]:
    """Plot `values` (oldest first; the newest lands on the right edge) as a
    filled braille area chart `width` x `height` cells. Each cell holds two
    values side by side and four dot rows; lines are colored bottom to top
    along the gradient, like btop's cpu graph."""
    if width <= 0 or height <= 0:
        return []
    slots = width * 2
    recent = list(values)[-slots:]
    padded: list[float | None] = [None] * (slots - len(recent)) + recent
    dots_high = height * 4

    def level(v: float | None) -> int:
        if v is None or v <= 0 or max_value <= 0:
            return 0
        return max(1, min(dots_high, round(v / max_value * dots_high)))

    levels = [level(v) for v in padded]
    rows = []
    for r in range(height):
        floor = (height - 1 - r) * 4
        color = rgb_to_hex(gradient_at(stops, (height - 1 - r) / max(1, height - 1)))
        chars = []
        for c in range(width):
            code = 0
            for dots, lvl in ((_LEFT_DOTS, levels[2 * c]), (_RIGHT_DOTS, levels[2 * c + 1])):
                for k in range(max(0, min(4, lvl - floor))):
                    code |= dots[k]
            chars.append(chr(0x2800 + code) if code else " ")
        rows.append(Text("".join(chars), style=Style(color=color), no_wrap=True))
    return rows


class Panel(Widget):
    """A btop-style box. render() draws the rounded frame across the whole
    region, underneath its single child (which the CSS insets by one cell;
    wrap several widgets in a container), and the top and bottom edges carry
    ┐segment┌ labels set via set_edges.

    The inset is one `margin: 1 1` rather than per-side rules because a
    more specific `margin-bottom` rule replaces the whole margin, zeroing
    the other three sides."""

    DEFAULT_CSS = """
    Panel {
        padding: 0;
    }
    Panel > * {
        margin: 1 1;
    }
    """

    def __init__(self, *children: Widget, color: str | None = None, **kwargs) -> None:
        super().__init__(*children, **kwargs)
        # None follows the active theme's text color (see self.frame_color).
        self.color = color
        self._edges: tuple = ((), (), None, (), ())

    @property
    def frame_color(self) -> str:
        return self.color if self.color is not None else _active.fg

    def set_edges(
        self,
        top_left: Iterable[Text] = (),
        top_right: Iterable[Text] = (),
        center: Text | None = None,
        bottom_left: Iterable[Text] = (),
        bottom_right: Iterable[Text] = (),
    ) -> None:
        """Set the edge labels, repainting only if they changed (owners call
        this on every refresh tick)."""
        edges = (
            tuple(top_left),
            tuple(top_right),
            center,
            tuple(bottom_left),
            tuple(bottom_right),
        )
        if edges != self._edges:
            self._edges = edges
            self.refresh()

    def render(self) -> RenderableType:
        width, height = self.size.width, self.size.height
        if width < 2 or height < 2:
            return Text("")
        top_left, top_right, center, bottom_left, bottom_right = self._edges
        color = self.frame_color
        side = Style(color=color)
        rows = [edge(width, color, top_left, top_right, center)]
        for _ in range(height - 2):
            mid = Text("│", style=side, no_wrap=True)
            mid.append(" " * (width - 2))
            mid.append("│", side)
            rows.append(mid)
        rows.append(edge(width, color, bottom_left, bottom_right, top=False))
        return Group(*rows)
