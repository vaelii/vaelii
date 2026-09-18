"""Colour by verdict, plus the blending helpers the chrome draws with.

A verdict has three states and one absence, and each gets a fixed colour rather
than a themed one: green passed, red failed, amber interrupted, grey never run.
A theme that repainted those would repaint the only thing on the screen that
carries meaning on its own.
"""

from __future__ import annotations

RGB = "tuple[int, int, int]"

# Per run state, as `logs/runs.tsv` spells it.  `missing` is the absence of a
# row — a check this checkout has never run at all — and reads as grey so it
# cannot be mistaken for a pass.
STATE_COLOR = {
    "passed": "#77ca9b",
    "failed": "#dc4c4c",
    "interrupted": "#cbc06c",
    "missing": "#5a5a5a",
    # Under way, and therefore not a verdict. Blue rather than a fourth warm
    # colour because nothing on this screen should be able to mistake work in
    # progress for an answer about it.
    "running": "#4682dc",
}

# The marks that COUNT NOTHING: one verdict, one glyph. A run made of parts
# draws a packed dot strip instead (widgets.packed_dots), where a dot is a part
# and the colours are counts — so these have to be a different vocabulary, or a
# cell of one is read as a cell of the other. A tick and a cross say "verdict"
# at a glance and cannot be confused with a quantity.
#
# Colour is not the only difference between them, because colour alone says
# nothing in a screenshot, down a mono terminal, or to a reader who cannot tell
# the red from the green.
STATE_MARK = {
    "passed": "\u2713",       # ✓
    "failed": "\u2717",       # ✗
    "interrupted": "\u25cb",  # ○ — started, reached no verdict
    # The quietest glyph on the screen, because it is the commonest: most cells
    # in the history are a check that never ran at that commit, and a column of
    # them has to read as background rather than as content. U+22C5 is the small
    # one; U+00B7 sat as heavy as the tick beside it.
    "missing": "\u22c5",      # ⋅ — never ran here
    "running": "\u25b6",      # ▶ — under way, and therefore not a verdict yet
}

# How stale a verdict is, in commits between the revision it was taken at and
# HEAD.  The gradient the staleness meters fill along: green at the current
# revision, amber a few commits back, red once the verdict is about a tree
# nobody is working on any more.
STALE_GRADIENT = ((0x77, 0xCA, 0x9B), (0xCB, 0xC0, 0x6C), (0xDC, 0x4C, 0x4C))

# Past this many commits a verdict is drawn as fully stale.  Not a claim about
# when a green stops being true — that depends on what landed — but the point
# where the meter stops distinguishing, so it says "old" rather than a number
# the bar cannot show.
STALE_FULL = 12


def _clamp(value: float) -> int:
    return max(0, min(255, int(round(value))))


def blend(rgb, toward, amount: float):
    """Mix `rgb` toward `toward` by `amount` (0 = unchanged, 1 = fully `toward`)."""
    return tuple(_clamp(c + (t - c) * amount) for c, t in zip(rgb, toward))


def lighten(rgb, amount: float = 0.4):
    """Blend a colour toward white."""
    return blend(rgb, (255, 255, 255), amount)


def text_color_for(bg) -> str:
    """Black or white foreground, whichever contrasts more with bg."""
    r, g, b = bg
    luminance = 0.299 * r + 0.587 * g + 0.114 * b
    return "black" if luminance > 150 else "white"


def rgb_to_hex(rgb) -> str:
    return "#{:02x}{:02x}{:02x}".format(*rgb)


# A run taken over uncommitted work under `src/` or `test/`. It gets a column of
# its own beside the revision, because it is a fact about WHICH TREE the verdict
# is about and not about the verdict — a green over a dirty tree answers for no
# commit at all. `±` rather than a hazard triangle: nothing here is dangerous,
# there is just work in the tree that no revision holds.
DIRT_MARK = "\u00b1"


def state_color(state: str) -> str:
    return STATE_COLOR.get(state, STATE_COLOR["missing"])


def state_mark(state: str) -> str:
    return STATE_MARK.get(state, STATE_MARK["missing"])
