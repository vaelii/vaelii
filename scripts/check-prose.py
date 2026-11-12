#!/usr/bin/env python3
"""Prose style check: literal technical language, against a per-file budget.

Comments, docstrings, doc pages and test names state what the code does. A metaphor
standing in for a mechanism, an evaluative adjective with no measurement behind it, and
a pseudo-cleft that delays the subject are all decodable only by inference, so this
check fails on them. The rule and the substitution table are CONTRIBUTING.md §3.10.

Seven codes:

  P1  A metaphor where the mechanism has a name. `door` is two different things --
      an API entry point (`assert`, `match`, the served handlers) and a validation
      check (a class-name allowlist, an arity refusal) -- which is the reason it is
      banned rather than renamed in place. `seam` is a protocol, an extension point,
      a boundary or a call site; `cone` is an ancestor set or an upward closure.

  P2  Evaluative language carrying no measurement: load-bearing, earns its keep,
      earns its place, worth writing down, the tempting alternative, honest and
      honestly, payoff. Where the claim is quantitative, cite the test or bench that
      measures it (CONTRIBUTING §8).

  P3  Pseudo-cleft -- `What keeps the wrap on its release is the version check` --
      which withholds the subject until after the verb.

  P4  A copula with `are` straight after it -- `is are`, `be are`, `are are`. Not a
      style rule: no sentence needs the pair, so it marks a phrase substituted in
      without its verb being fixed. P1 and P2 name what to write instead, and a
      substitution made across the tree at once is how their hits get fixed, so the
      pass that fixes them is the one that leaves these.

  P5  A word that names no one mechanism and covers several: `roster` (a set, a list,
      a table, an allowlist), `gate` (a check, a refusal, a guard clause), `pin` (a test
      asserts, a fixture forces, a value is held), `stamp` (a fingerprint, a recorded
      value, a version), `window` (a touched set, a range, a buffer). Identifiers count:
      `exception-roster-gate` is a hit. The time sense of `window` (a time, idle, grace or
      retry window) and the gate tool's own tokens (`lein gate`, `gate.sh`, `GATE_*`,
      `logs/gate`) are not hits.

  P6  `view` in any sense but what a context sees up its `genlCx` ancestor set. A hit
      passes inside a phrase that names the context ("CxB's view", "the view context",
      "comes into view", `view-context`); a bare "the view" fails. A phrase wrapped onto
      the next line is read with the last three words of the line before it.

  P7  A prose sentence of `MAX_WORDS` (40) words or more. No regex can test §3.10's
      rule 6, one claim per sentence. Sentence length stands in for the rule. Prose is
      a markdown paragraph or list item, a full-line `;` comment or a docstring in a
      Clojure file, and a full-line `#` comment in a .py or .sh file. Fenced code,
      table rows, headings and HTML are not prose. A backtick span counts as one word.
      A link counts as its text. A comment or docstring is joined across its lines
      before it is split. A list item is never joined to the next one.

P5, P6 and P7 skip CHANGELOG.md's released sections (from the first `## 0.` heading on),
which are frozen. P6 skips the reference model under `test/vaelii/ref/`, whose `view`
and `view-of` are its own names for a context's visible set, and the glossary and
reserved-words pages that define the word.

The sentence-form rules that no regex reaches (name the subject, no fragment, mechanism
before reason) are held by review, not by this script. P7 measures sentence length, and
review holds the one-claim rule itself.

Each budget maps a path to the number of hits it is allowed: `scripts/prose-baseline.txt`
holds P1-P6 and `scripts/prose-length-baseline.txt` holds P7. A file absent from a budget
is held at zero, so a new or rewritten file is clean by default. Over budget fails, and
under budget fails too. `--update` lowers each listed count to the file's hits. It never
raises a count, and it never adds a file the budget does not list. Raising a count or
adding a file is a hand edit carrying a reason, so a regression appears in the diff
rather than in a refresh. `--seed` writes a budget file that does not exist yet from the
tree as it stands, and leaves an existing one as it is. The P1-P6 entries are P5 names
the code must still read or a changelog entry must quote; every other file is at zero
there.

    python3 scripts/check-prose.py            # the check
    python3 scripts/check-prose.py --update   # lower every stale budget
    python3 scripts/check-prose.py --seed     # write an absent budget file from the tree
    python3 scripts/check-prose.py --list     # every hit, file:line:code:text; P7 as
                                              # file:line: P7 (NN words) <first 12 words>…
"""

import bisect
import importlib.util
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SELF = os.path.abspath(__file__)
BASELINE = os.path.join(ROOT, "scripts", "prose-baseline.txt")
LENGTH_BASELINE = os.path.join(ROOT, "scripts", "prose-length-baseline.txt")

# P7 finds Clojure docstrings with check-doc-size.py's reader, which that script owns.
_spec = importlib.util.spec_from_file_location(
    "check_doc_size", os.path.join(ROOT, "scripts", "check-doc-size.py"))
DOC_SIZE = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(DOC_SIZE)

# Directories scanned, and the extensions scanned inside them.
SCAN_DIRS = ["src", "test", "bench", "docs", "handbook", "scripts", "resources/kb"]
SCAN_EXT = (".clj", ".cljc", ".cljs", ".md", ".py", ".sh", ".txt", ".edn")
# Directory names never descended into, wherever they appear: build output, vendored
# code, and the large gitignored working directories a bench tree keeps. A sibling
# repo's copy of this script carries the same list for the entries its own tree can
# hit, so one walk cannot be cheap here and a 500 GB traversal there. `.venv` and
# `__pycache__` are where a Python virtualenv or bytecode cache lands inside a scanned
# directory.
SKIP_DIRNAMES = {".git", "target", "node_modules", ".clj-kondo", "build",
                 "scratch", "corpus", "checkouts", "pdfs", "findings",
                 ".venv", "venv", "__pycache__"}
# A generated artifact larger than this is data, not prose: reading it costs more than
# any finding in it is worth.
MAX_BYTES = 2 * 1024 * 1024
ROOT_MD = ["README.md", "CHANGELOG.md", "CONTRIBUTING.md", "CONTRIBUTORS.md"]

# Files that STATE the rule quote the banned tokens in order to ban them, so they are
# exempt by name. Allowlisting a token instead would disable the check everywhere --
# the arrangement check-doc-drift.py's E7 and E11 already use.
EXEMPT = {
    "scripts/check-prose.py",
    "scripts/prose-baseline.txt",
    "scripts/prose-length-baseline.txt",
    "CONTRIBUTING.md",
}

# Case-SENSITIVE, with the three casings spelled out, because `COne` and `CTwo` are
# context symbols in the test world and a case-insensitive `\bcone\b` matches `COne`.
# `indoors`, `IndoorsFn` and `indoors-cat` are test-world vocabulary about cats and have
# nothing to do with the metaphor, so P1_NOT drops them.
def _cased(word):
    """A word, its Capitalised form and its SHOUTED form, as one alternation."""
    return "|".join((word, word.capitalize(), word.upper()))

P1 = re.compile(
    r"\b(?:" + "|".join(
        _cased(w) for w in
        ("doors", "door", "seams", "seam", "up-cones", "up-cone", "cones", "cone",
         "teeth", "spines", "spine")
    ) + r")\b"
    r"|[Tt]he [Ff]ront [Dd]oor|THE FRONT DOOR"
    r"|the ground (moves|shifts)"
    r"|holds? the line|the line to hold")
P1_NOT = re.compile(r"indoor", re.I)

P2 = re.compile(
    r"load-bearing"
    r"|earns? (its|their) keep"
    r"|worth (writing down|stating|saying)"
    r"|costs? (you )?nothing|what it buys"
    r"|the tempting (alternative|thing)|it is tempting"
    r"|\bhonest(ly)?\b|earns? (its|the|their) (place|entry)|\bpayoffs?\b"
    r"|(loud|quiet|cheap|free) enough"
    r"|and they are not the same"
    r"|, deliberately\."
    r"|reads (as|like) (though|a |an |the )"
    r"|the shape (of|that|a) ",
    re.I)

P3 = re.compile(r"(^|\. )What [a-z][a-z ,'`-]{5,60} is (a|the|an|what|not) ")

# A copula with `are` straight after it -- `is are`, `be are`, `are are`. No sentence
# needs the pair, so a hit is a phrase substituted in without its verb being fixed: the
# tree took 20 of them from one pass that rewrote `read as a` to `are indistinguishable
# from a` and left `is read as a` standing as `is are indistinguishable from a`.
# The rest of that pass -- `does not are`, `a are`, `to are` -- is NOT here, because the
# same shapes are ordinary English by ellipsis: "the 118 that do not are nouns" elides
# "carry a signature", and "the ops it applies to are the ones" ends a relative clause.
# Only this direction is unambiguous, so only this direction fails the build.
P4 = re.compile(r"(?<!-)\b(?:is|was|be|been|are|being)\s+are\b", re.I)
# `clojure.test` publishes both `is` and `are`, so `:refer [deftest testing is are]` is a
# require and not a sentence. The hyphen lookbehind above is for the other collision, a
# compound ending in a copula: OpenCyc's `many states-of-being are conceptualized`.
P4_NOT = re.compile(r":refer")

# Each P5 word, the tokens blanked out of a line before it is matched, and the files the
# word is not read in. A token is blanked rather than the match dropped, so a line holding
# both `lein gate` and a second `gate` still fails on the second.
P5_TERMS = [
    (re.compile(r"[Rr]oster|ROSTER"), [r"AUTHORS\.roster"], []),
    (re.compile(r"(?:(?<![A-Za-z])|(?<=un)|(?<=Un))gat(?:e|es|ed|ing)(?![a-z])"
                r"|(?<![A-Z])Gat(?:e|es|ed|ing)(?![a-z])"
                r"|(?<![A-Za-z])GAT(?:E|ES|ED|ING)(?![A-Z])"),
     [r"\blein (?:release-)?gate\b", r"\brelease-gate\b", r"\b(?:scripts/)?gate\\?\.sh\b",
      r"\b(?:logs|target)/gate\b", r"\b(?:VAELII_)?GATE_[A-Z_]+\b",
      r"\bgate_(?:slot_[a-z]+|cmd|label|rev)\b", r"\bgate-lock\b", r"\bgate[ -]slots?\b",
      r"\"gate\"", r"\bgate --[a-z-]+", r"\bgate:"],
     ["scripts/gate.sh"]),
    (re.compile(r"(?<![A-Za-z])(?:[Uu]n|UN|[Rr]e-?|RE-?)?(?:[Pp]in|PIN)"
                r"(?:s|ned|ning|nable|S|NED|NING)?(?![a-z])"), [], []),
    (re.compile(r"(?i)(?<![a-z])(?:un-?|re-?)?stamp"), [r"(?i)timestamp", r"StampedLock"], []),
    (re.compile(r"(?i)window"),
     [r"Windows", r"gitforwindows", r"\bwindows\?", r"on-windows", r"\"windows\"",
      r"show:window:top", r":framing :window",
      r"(?i)\b(?:time|timed|idle|crash|race|sprint|timeout|grace|retry|overlap|rate[- ]limit)"
      r"[- ]windows?\b",
      r"stat-window-ms", r"overlap-window"],
     []),
]
P5_TERMS = [(pat, [re.compile(x) for x in strips], set(files)) for pat, strips, files in P5_TERMS]

P6 = re.compile(r"(?<![A-Za-z])view(?:s|ed|er|ers)?(?![A-Za-z])", re.I)
# Words holding `view` that are not the word: `preview`, `viewBox`, the spatial
# `viewpoint`, the KB constant `image_viewing`, the test-world individual `Viewer`.
# Discord's permission token and the channel-access kind are literal identifiers.
P6_NOT = [re.compile(x, re.I) for x in (
    r"(?<!\w)(?-i:channel_view|VIEW_CHANNEL)(?!\w)",
    r"\bpreview", r"\breview", r"viewBox", r"viewport", r"scrollIntoView",
    r"ViewTransition", r"image_viewing", r"\bViewer\b", r"\bTmpViewer", r"viewpoint",
    r"point of view", r"gh run view", r"gh pr view")]
# The phrases that carry the kept sense: a named context's view, the view context,
# the qualified views docs/reference.md defines, and the visibility idioms.
P6_KEPT = [re.compile(x) for x in (
    r"\*{0,2}view\*{0,2}[- _]?contexts?\b", r"viewContext",
    r"\b[\w`*\[\]?-]+['’]s (own |whole |current |whole current )?views?\b",
    r"\b[\w`*?-]+s['’] (own )?views?\b",
    r"\b(own|joint|common|empty|wider|narrower) views?\b",
    r"\bwhose view",
    r"\b(comes?|came|coming|brings?|brought|into|out of|from|in)\s+\*?view\b\*?",
    r"\bview (at|from|of) (`?Cx\w*`?|`[A-Za-z?][\w?-]*`|(a|the|every|each|one|any|that) "
    r"(\w+ )?contexts?\b)",
    r"\bviews? at (a |each |every |one |its )?contexts?\b",
    r"\bviewed from\b",
    r"\b(joint |deep )?viewers?\b", r"deep-viewer!",
    r"(own|joint|common|into|the-rest-of-the|come|comes|came)-views?\b",
    r"the-view-licenses", r":sight-view")]
P6_SKIP = re.compile(r"^test/vaelii/ref/|^docs/(glossary|naming)\.md$")

# P7 flags a prose sentence of MAX_WORDS words or more. Sentence length stands in for
# §3.10's rule 6, one claim per sentence. No regex can test that rule.
MAX_WORDS = 40
# A unit is a markdown paragraph or one list item. A sentence never crosses a unit.
# Fenced code, table rows, headings, HTML and horizontal rules belong to no unit.
MD_FENCE = re.compile(r"^\s*(`{3,}|~{3,})")
MD_ITEM = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s+")
MD_NO_UNIT = re.compile(r"^\s*(?:\||#{1,6}(?:\s|$)|<|[-=_]{3,}|\*{3,}\s*$)")
# _mask rewrites each match of these to a string of the same length, so an offset into
# the masked text is an offset into the original. A backtick span becomes one word with
# no `.` in it. A link keeps its text only. An abbreviation loses its periods.
MD_CODE = re.compile(r"(`+).+?\1", re.S)
MD_LINK = re.compile(r"!?\[([^\]\n]*)\](?:\([^)\s]*\)|\[[^\]\n]*\])")
ABBREV = re.compile(r"(?i)\b(?:e\.g|i\.e|vs|cf|viz|approx|resp|incl|et al)\.")
# A bold or italic run-in label (`**An open.**`, `*Migration:*`) heads a unit and is
# not a sentence, so its words are masked out.
RUN_IN = re.compile(r"^\s*(?:\*\*(?:(?!\*\*).)+?[.:?!][\"'’”)]*\*\*"
                    r"|\*(?!\*)[^*\n]+?[.:?!][\"'’”)]*\*(?!\*))")
# A sentence ends at `.`, `?` or `!` and any closing marks, before whitespace and a
# character that is not a lowercase letter. A `.` with no whitespace after it, as in
# `1.5`, `0.33.0` and `seal.nippy`, ends nothing.
SENTENCE_END = re.compile(r"[.?!][)\]\"'’”*_]*(?=\s+[^\sa-z]|\s*$)")
# A word is a whitespace-delimited token holding a letter or a digit, so `—` is no word.
WORD = re.compile(r"[^\s\w]*\w\S*")
HASH_COMMENT = re.compile(r"^\s*#(?!!)")
# ALIGNED matches two or more spaces after a word, which separate the columns of a table.
# Two spaces after sentence punctuation do not match.
ALIGNED = re.compile(r"[^\s.?!:;,]\s{2,}\S")


def _blank(pats, line):
    for p in pats:
        line = p.sub(lambda m: " " * len(m.group(0)), line)
    return line


def p5_hits(rel, line):
    """Every P5 word in `line`, after each word's own tokens are blanked."""
    out = []
    for pat, strips, files in P5_TERMS:
        if rel in files:
            continue
        out += [m.group(0) for m in pat.finditer(_blank(strips, line))]
    return out


def p6_bare(line):
    """Is there a `view` in `line` that no kept phrase accounts for?"""
    probe = _blank(P6_NOT, line)
    return bool(P6.search(_blank(P6_KEPT, probe))) if P6.search(probe) else False


def md_units(numbered, comment=False):
    """Groups (line number, text) pairs into prose units, each a list of such pairs.

    In a comment or docstring (`comment`), a line with a run of two or more spaces after a
    word is a table row and belongs to no unit. A line indented less than the line before
    it starts a new unit there."""
    units, cur, fence, html_comment, last_indent = [], [], None, False, 0
    for ln, line in numbered:
        if fence:
            fence = None if line.strip().startswith(fence) else fence
            continue
        if html_comment:
            html_comment = "-->" not in line
            continue
        text = re.sub(r"^\s*>\s?", "", line)  # P7 reads a blockquote line as prose
        opens, item = MD_FENCE.match(text), MD_ITEM.match(text)
        row = comment and ALIGNED.search(text)
        indent = len(text) - len(text.lstrip())
        dedent = comment and text.strip() and indent < last_indent
        if opens or item or row or dedent or not text.strip() or MD_NO_UNIT.match(text):
            if cur:
                units.append(cur)
            cur = []
        last_indent = indent if text.strip() else last_indent
        if opens:
            fence = opens.group(1)
        elif MD_NO_UNIT.match(text):
            html_comment = text.lstrip().startswith("<!--") and "-->" not in text
        elif text.strip() and not row:
            cur.append((ln, (text[item.end():] if item else text).strip()))
    if cur:
        units.append(cur)
    return units


def clj_units(text):
    """Returns the prose units of a Clojure file's full-line `;` comments and docstrings."""
    starts = [0] + [m.end() for m in re.finditer("\n", text)]

    def line_of(off):
        return bisect.bisect_right(starts, off)

    blocks, cur = [], []
    for m in DOC_SIZE.TOKEN.finditer(text):
        if not m.group(0).startswith(";"):
            continue
        ln = line_of(m.start())
        if text[starts[ln - 1]:m.start()].strip():
            continue  # the comment follows code on its line
        if cur and cur[-1][0] != ln - 1:
            blocks.append(cur)
            cur = []
        cur.append((ln, re.sub(r"^;+ ?", "", m.group(0))))
    blocks += [cur] if cur else []
    for off, tok in DOC_SIZE.docstrings(text):
        body = re.sub(r"\\(.)", r"\1", tok[1:-1])
        blocks.append([(line_of(off) + i, x) for i, x in enumerate(body.split("\n"))])
    return [u for b in blocks for u in md_units(b, comment=True)]


def hash_units(lines):
    """Returns the prose units of a script's full-line `#` comments, not its shebang."""
    blocks, cur = [], []
    for ln, line in enumerate(lines, 1):
        if HASH_COMMENT.match(line):
            cur.append((ln, re.sub(r"^\s*#+ ?", "", line)))
        elif cur:
            blocks.append(cur)
            cur = []
    blocks += [cur] if cur else []
    return [u for b in blocks for u in md_units(b, comment=True)]


def prose_units(rel, lines):
    """Returns the prose units P7 reads in one file, chosen by its extension."""
    if rel.endswith(".md"):
        return md_units(enumerate(lines, 1))
    if rel.endswith((".clj", ".cljc", ".cljs")):
        return clj_units("\n".join(lines))
    if rel.endswith((".py", ".sh")):
        return hash_units(lines)
    return []


def _mask(text):
    """Rewrites `text`'s code spans, links, abbreviations and run-in label in place."""
    text = MD_CODE.sub(lambda m: "`" + "x" * (len(m.group(0)) - 2) + "`", text)
    text = MD_LINK.sub(lambda m: " " + m.group(1) + " " * (len(m.group(0)) - len(m.group(1)) - 1),
                       text)
    text = ABBREV.sub(lambda m: m.group(0).replace(".", "_"), text)
    return RUN_IN.sub(lambda m: " " * len(m.group(0)), text)


def sentences(unit):
    """Returns (line number, word count, first 12 words) per sentence of a prose unit."""
    text = "\n".join(t for _, t in unit)
    starts, off = [], 0
    for _, t in unit:
        starts.append(off)
        off += len(t) + 1
    masked = _mask(text)
    bounds = [m.end() for m in SENTENCE_END.finditer(masked)]
    out, begin = [], 0
    for end in bounds + [len(masked)]:
        words = list(WORD.finditer(masked, begin, end))
        begin = end
        if not words:
            continue
        head = text[words[0].start():words[min(11, len(words) - 1)].end()]
        head = " ".join(MD_LINK.sub(r"\1", head).split())
        ln = unit[bisect.bisect_right(starts, words[0].start()) - 1][0]
        out.append((ln, len(words), head))
    return out


def long_sentences(rel, lines):
    """Returns (line number, text) for every P7 hit in a file's `lines`."""
    return [(ln, f"({n} words) {head}…")
            for unit in prose_units(rel, lines)
            for ln, n, head in sentences(unit) if n >= MAX_WORDS]


def scan_files():
    """Every path the check reads, repo-relative and sorted."""
    seen = []
    for d in SCAN_DIRS:
        base = os.path.join(ROOT, d)
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = [x for x in dirnames if x not in SKIP_DIRNAMES]
            for fn in filenames:
                full = os.path.join(dirpath, fn)
                if not fn.endswith(SCAN_EXT):
                    continue
                try:
                    if os.path.getsize(full) > MAX_BYTES:
                        continue
                except OSError:
                    continue
                # `/`-spelled on every OS: EXEMPT and the baseline name files that way
                seen.append(os.path.relpath(full, ROOT).replace(os.sep, "/"))
    for fn in ROOT_MD:
        if os.path.exists(os.path.join(ROOT, fn)):
            seen.append(fn)
    return sorted(p for p in seen if p not in EXEMPT)


def hits_in(rel):
    """Every (line number, code, matched text) in one file."""
    out = []
    path = os.path.join(ROOT, rel)
    if os.path.abspath(path) == SELF:
        return out
    try:
        lines = open(path, errors="replace").read().splitlines()
    except OSError:
        return out
    # P5, P6 and P7 stop at the first released CHANGELOG section
    frozen = len(lines) + 1
    if rel == "CHANGELOG.md":
        frozen = next((i for i, l in enumerate(lines, 1) if l.startswith("## 0.")), frozen)
    for i, line in enumerate(lines, 1):
        if i < frozen:
            out += [(i, "P5", w) for w in p5_hits(rel, line)]
            if not P6_SKIP.search(rel) and p6_bare(line):
                prev = " ".join(lines[i - 2].split()[-3:]) if i > 1 else ""
                head = re.sub(r"^\s*(;+|#+|\*|//)?\s*", "", line)
                if p6_bare(prev + " " + head):
                    out.append((i, "P6", "view"))
        for code, pat in (("P1", P1), ("P2", P2), ("P3", P3), ("P4", P4)):
            for m in pat.finditer(line):
                text = m.group(0).strip()
                if code == "P1" and P1_NOT.search(m.group(0)):
                    continue
                if code == "P4" and P4_NOT.search(line):
                    continue
                out.append((i, code, text))
    return out + [(i, "P7", text) for i, text in long_sentences(rel, lines[:frozen - 1])]


def read_baseline(path):
    """path -> allowed count, plus the reason comment each line carries."""
    budget, reason = {}, {}
    if not os.path.exists(path):
        return budget, reason
    for line in open(path):
        line = line.rstrip("\n")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        budget[parts[1].strip()] = int(parts[0].strip())
        reason[parts[1].strip()] = parts[2].strip() if len(parts) > 2 else ""
    return budget, reason


HEADER = """\
# Per-file prose budget for scripts/check-prose.py -- the count of P1-P6 hits each
# file is allowed to carry while the tree is rewritten into literal technical language
# (CONTRIBUTING.md §3.10).
#
# Format: <count>\\t<path>\\t<reason>.  A file absent from this list is held at ZERO,
# so a new file and a rewritten one are clean by default.
#
# The ratchet: `--update` LOWERS a count.  It never raises one, and it never adds a file
# this list does not name.  Raising a count or adding a file is a hand edit that carries
# its reason on the line, so a regression shows up in the diff rather than in a refresh.
# A file whose real count is below its budget fails until it is lowered with `--update`,
# which is what keeps the number on this page moving down.
#
# The entries are P5 names the code must still read or a changelog entry must quote
# (CONTRIBUTING.md §3.10); every other file is at ZERO.
"""


LENGTH_HEADER = f"""\
# Per-file sentence-length budget for scripts/check-prose.py -- the count of P7 hits,
# prose sentences of {MAX_WORDS} or more words, each file is allowed to carry
# (CONTRIBUTING.md §3.10, rule 6).
#
# The format and the ratchet are scripts/prose-baseline.txt's: <count>\\t<path>\\t<reason>,
# and a file absent from this list is held at ZERO.  `--update` lowers a count.  It never
# raises one, and it never adds a file this list does not name.
"""

# Each row names a budget: its label, its file, the file's header, the over-budget
# message, and whether it holds P7 hits or P1-P6 hits. scripts/lint.sh reads both
# summary lines.
LEDGERS = [
    ("prose", BASELINE, HEADER,
     "metaphor or aphorism over the file's budget. State what the code does, literally "
     "(CONTRIBUTING.md §3.10).", False),
    ("prose P7", LENGTH_BASELINE, LENGTH_HEADER,
     f"sentences of {MAX_WORDS} or more words over the file's budget. Split each into one "
     "claim per sentence (CONTRIBUTING.md §3.10, rule 6).", True),
]


def write_baseline(path, header, counts, reason):
    with open(path, "w") as f:
        f.write(header)
        for rel in sorted(counts):
            if counts[rel] <= 0:
                continue
            why = reason.get(rel, "") or "awaiting rewrite"
            f.write(f"{counts[rel]}\t{rel}\t{why}\n")


def fmt(rel, ln, code, text):
    """Formats one hit as `--list` and the over-budget report print it."""
    return f"{rel}:{ln}: P7 {text}" if code == "P7" else f"{rel}:{ln}: {code} `{text}`"


def update(label, path, header, counts):
    """Lowers each count `path` lists to the file's hits in `counts`, and returns 1 when a
    file is over its budget. It never raises a count or adds a file `path` does not list."""
    budget, reason = read_baseline(path)
    lowered = {rel: min(n, counts.get(rel, 0)) for rel, n in budget.items()}
    over = sorted((rel, budget.get(rel, 0), n) for rel, n in counts.items()
                  if n > budget.get(rel, 0))
    write_baseline(path, header, lowered, reason)
    print(f"{label} baseline: {sum(1 for n in lowered.values() if n > 0)} files, "
          f"{sum(lowered.values())} hits allowed")
    if over:
        print("\nNOT lowered -- these files are OVER their budget, and --update never "
              "raises a count or adds a file:")
        for rel, was, now in over:
            print(f"  {rel}: budget {was}, found {now}")
        return 1
    return 0


def seed(label, path, header, counts):
    """Writes `path` from `counts` when `path` does not exist, and leaves an existing one."""
    if os.path.exists(path):
        print(f"{label} baseline: {os.path.relpath(path, ROOT)} exists, left as it is "
              f"(--update lowers it)")
        return 0
    write_baseline(path, header, counts, {})
    print(f"{label} baseline: seeded, {len(counts)} files, {sum(counts.values())} hits "
          f"allowed")
    return 0


def check(label, path, message, detail):
    """Holds each file's hits in `detail` to `path`'s budget, and returns 1 when one is off."""
    counts = {rel: len(hs) for rel, hs in detail.items()}
    budget, _ = read_baseline(path)
    over, stale = [], []
    for rel, n in sorted(counts.items()):
        allowed = budget.get(rel, 0)
        if n > allowed:
            over.append((rel, allowed, n))
    for rel, allowed in sorted(budget.items()):
        n = counts.get(rel, 0)
        if n < allowed:
            stale.append((rel, allowed, n))

    total = sum(counts.values())
    allowed_total = sum(budget.values())

    if not over and not stale:
        print(f"{label}: {total} of {allowed_total} allowed, "
              f"{len(counts)} files remaining")
        return 0

    if over:
        print(f"{label}: {message}\n")
        for rel, allowed, n in over:
            print(f"  {rel}: {n} hits, budget {allowed}")
            for hit in detail[rel][:6]:
                print(f"      {fmt(rel, *hit)}")
            if len(detail[rel]) > 6:
                print(f"      … {len(detail[rel]) - 6} more "
                      f"(python3 scripts/check-prose.py --list)")
        print()
    if stale:
        print(f"{label}: these files are now BELOW their budget. Lower them with --update "
              "so the ratchet holds the gain:\n")
        for rel, allowed, n in stale:
            print(f"  {rel}: {n} hits, budget {allowed}")
        print("\n  → python3 scripts/check-prose.py --update")
    return 1


def main():
    hits = {rel: sorted(hits_in(rel), key=lambda h: h[0]) for rel in scan_files()}
    rc = 0
    for label, path, header, message, length in LEDGERS:
        detail = {rel: [h for h in hs if (h[1] == "P7") == length] for rel, hs in hits.items()}
        detail = {rel: hs for rel, hs in detail.items() if hs}
        counts = {rel: len(hs) for rel, hs in detail.items()}
        if "--list" in sys.argv:
            for rel in sorted(detail):
                for hit in detail[rel]:
                    print(fmt(rel, *hit))
            print(f"\n{sum(counts.values())} {'P7 ' if length else ''}hits across "
                  f"{len(counts)} files")
        elif "--update" in sys.argv:
            rc |= update(label, path, header, counts)
        elif "--seed" in sys.argv:
            rc |= seed(label, path, header, counts)
        else:
            rc |= check(label, path, message, detail)
    return rc


if __name__ == "__main__":
    sys.exit(main())
