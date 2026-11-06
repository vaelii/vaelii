#!/usr/bin/env python3
"""Prose style check: literal technical language, against a per-file budget.

Comments, docstrings, doc pages and test names state what the code does. A metaphor
standing in for a mechanism, an evaluative adjective with no measurement behind it, and
a pseudo-cleft that delays the subject are all decodable only by inference, so this
check fails on them. The rule and the substitution table are CONTRIBUTING.md §3.10.

Six codes:

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

P5 and P6 skip CHANGELOG.md's released sections (from the first `## 0.` heading on),
which are frozen. P6 skips the reference model under `test/vaelii/ref/`, whose `view`
and `view-of` are its own names for a context's visible set, and the glossary and
reserved-words pages that define the word.

The sentence-form rules that no regex reaches (name the subject, no fragment, one claim
per sentence, mechanism before reason) are held by review, not by this script.

The budget, `scripts/prose-baseline.txt`, maps a path to the number of hits it is
allowed. A file absent from it is held at zero, so a new or rewritten file is clean by
default. Over budget fails; under budget also fails, with the fix being `--update`, which lowers a
count and never raises one. Raising a count is a hand edit carrying a reason, so a
regression appears in the diff rather than in a refresh. The baseline's entries are P5
names the code must still read or a changelog entry must quote; every other file is at zero.

    python3 scripts/check-prose.py            # the check
    python3 scripts/check-prose.py --update   # lower every stale budget
    python3 scripts/check-prose.py --list     # every hit, file:line:code:text
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SELF = os.path.abspath(__file__)
BASELINE = os.path.join(ROOT, "scripts", "prose-baseline.txt")

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
    # P5 and P6 stop at the first released CHANGELOG section
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
    return out


def read_baseline():
    """path -> allowed count, plus the reason comment each line carries."""
    budget, reason = {}, {}
    if not os.path.exists(BASELINE):
        return budget, reason
    for line in open(BASELINE):
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
# The ratchet: `--update` LOWERS a count and never raises one.  Raising a count is a
# hand edit that carries its reason on the line, so a regression shows up in the diff
# rather than in a refresh.  A file whose real count is below its budget fails until it
# is lowered with `--update`, which is what keeps the number on this page moving down.
#
# The entries are P5 names the code must still read or a changelog entry must quote
# (CONTRIBUTING.md §3.10); every other file is at ZERO.
"""


def write_baseline(counts, reason):
    with open(BASELINE, "w") as f:
        f.write(HEADER)
        for rel in sorted(counts):
            if counts[rel] <= 0:
                continue
            why = reason.get(rel, "") or "awaiting rewrite"
            f.write(f"{counts[rel]}\t{rel}\t{why}\n")


def main():
    update = "--update" in sys.argv
    listing = "--list" in sys.argv

    counts, detail = {}, {}
    for rel in scan_files():
        hs = hits_in(rel)
        if hs:
            counts[rel] = len(hs)
            detail[rel] = hs

    if listing:
        for rel in sorted(detail):
            for ln, code, text in detail[rel]:
                print(f"{rel}:{ln}: {code} `{text}`")
        print(f"\n{sum(counts.values())} hits across {len(counts)} files")
        return 0

    budget, reason = read_baseline()

    if update:
        merged = dict(counts)
        raised = []
        for rel, n in counts.items():
            if rel in budget and n > budget[rel]:
                raised.append((rel, budget[rel], n))
                merged[rel] = budget[rel]      # never raise
        write_baseline(merged, reason)
        total = sum(v for v in merged.values())
        print(f"prose baseline: {len(merged)} files, {total} hits allowed")
        if raised:
            print("\nNOT lowered -- these files are OVER their budget, and "
                  "--update never raises one:")
            for rel, was, now in sorted(raised):
                print(f"  {rel}: budget {was}, found {now}")
            return 1
        return 0

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
        print(f"prose: {total} of {allowed_total} allowed, "
              f"{len(counts)} files remaining")
        return 0

    if over:
        print("prose: metaphor or aphorism over the file's budget. State what the "
              "code does, literally (CONTRIBUTING.md §3.10).\n")
        for rel, allowed, n in over:
            print(f"  {rel}: {n} hits, budget {allowed}")
            for ln, code, text in detail[rel][:6]:
                print(f"      {rel}:{ln}: {code} `{text}`")
            if len(detail[rel]) > 6:
                print(f"      … {len(detail[rel]) - 6} more "
                      f"(python3 scripts/check-prose.py --list)")
        print()
    if stale:
        print("prose: these files are now BELOW their budget. Lower them with --update so "
              "the ratchet holds the gain:\n")
        for rel, allowed, n in stale:
            print(f"  {rel}: {n} hits, budget {allowed}")
        print("\n  → python3 scripts/check-prose.py --update")
    return 1


if __name__ == "__main__":
    sys.exit(main())
