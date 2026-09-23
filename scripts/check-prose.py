#!/usr/bin/env python3
"""Prose style check: literal technical language, against a per-file budget.

Comments, docstrings, doc pages and test names state what the code does. A metaphor
standing in for a mechanism, an evaluative adjective with no measurement behind it, and
a pseudo-cleft that delays the subject are all decodable only by inference, so this
check fails on them. The rule and the substitution table are CONTRIBUTING.md §3.10.

Four codes:

  P1  A metaphor where the mechanism has a name. `door` is two different things --
      an API entry point (`assert`, `match`, the served handlers) and a validation
      check (a class-name allowlist, an arity refusal) -- which is the reason it is
      banned rather than renamed in place. `seam` is a protocol, an extension point,
      a boundary or a call site; `cone` is an ancestor set or an upward closure.

  P2  Evaluative language carrying no measurement: load-bearing, earns its keep,
      worth writing down, the tempting alternative, the only honest option. Where the
      claim is quantitative, cite the test or bench that measures it (CONTRIBUTING §8).

  P3  Pseudo-cleft -- `What holds the wrap is a version pin` -- which withholds the
      subject until after the verb.

  P4  A copula with `are` straight after it -- `is are`, `be are`, `are are`. Not a
      style rule: no sentence needs the pair, so it marks a phrase substituted in
      without its verb being fixed. P1 and P2 name what to write instead, and a
      substitution made across the tree at once is how their hits get fixed, so the
      pass that fixes them is the one that leaves these.

The sentence-form rules that no regex reaches (name the subject, no fragment, one claim
per sentence, mechanism before reason) are held by review, not by this script.

The budget, `scripts/prose-baseline.txt`, maps a path to the number of hits it is
allowed. A file absent from it is pinned at zero, so a new or rewritten file is clean by
default. Over budget fails; under budget also fails, with the fix being `--update`, which lowers a
count and never raises one. Raising a count is a hand edit carrying a reason, so a
regression appears in the diff rather than in a refresh. The tree is at zero today, so the
baseline holds no entries.

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
SCAN_DIRS = ["src", "test", "bench", "docs", "scripts", "resources/kb"]
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
    r"|only honest|honest option"
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
                seen.append(os.path.relpath(full, ROOT))
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
    for i, line in enumerate(lines, 1):
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
# Per-file prose budget for scripts/check-prose.py -- the count of P1/P2/P3 hits each
# file is allowed to carry while the tree is rewritten into literal technical language
# (CONTRIBUTING.md §3.10).
#
# Format: <count>\\t<path>\\t<reason>.  A file absent from this list is pinned at ZERO,
# so a new file and a rewritten one are clean by default.
#
# The ratchet: `--update` LOWERS a count and never raises one.  Raising a count is a
# hand edit that carries its reason on the line, so a regression shows up in the diff
# rather than in a refresh.  A file whose real count is below its budget fails until it
# is re-pinned, which is what keeps the number on this page moving down.
#
# The tree is at ZERO, so this file has no entries. It stays because the ratchet is how
# a batch of new prose gets landed without blocking on rewriting all of it at once.
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
            print("\nNOT lowered -- these files are OVER their pinned budget, and "
                  "--update never raises one:")
            for rel, was, now in sorted(raised):
                print(f"  {rel}: pinned {was}, found {now}")
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
        print("prose: these files are now BELOW their pinned budget. Re-pin them so "
              "the ratchet holds the gain:\n")
        for rel, allowed, n in stale:
            print(f"  {rel}: {n} hits, budget {allowed}")
        print("\n  → python3 scripts/check-prose.py --update")
    return 1


if __name__ == "__main__":
    sys.exit(main())
