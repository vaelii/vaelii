#!/usr/bin/env python3
"""Docstring and comment size check, against a per-file budget.

A docstring states a fn's contract (economy.md): args, return, refusals, the invariants a
caller relies on. Past about 8 lines it holds rationale the doc page owns. A comment block
restating a doc page is the same fault. This check counts two numbers per `.clj` file under
src/, test/ and bench/:

  excess    the docstring lines past the 8th, summed over the file's docstrings (`ns`,
            `def*`, and `defprotocol` method docstrings)
  comments  the lines whose first non-blank character is `;`

The budget, `scripts/doc-size-baseline.txt`, holds both per file. A file absent from it is
allowed no excess and comments up to a tenth of its code lines. Over budget fails; under
budget also fails, and `--update` lowers the budget. `--update` never raises one: a raise
is a hand edit, so it shows in the diff.

    python3 scripts/check-doc-size.py                  # the check
    python3 scripts/check-doc-size.py --update [PATH…]  # lower the budgets (of PATHs only)
    python3 scripts/check-doc-size.py --top 20          # the files with the most of each
    python3 scripts/check-doc-size.py --stage PATH…     # lower PATHs' rows in the index

`--stage` reads each PATH and the baseline as staged, and stages the baseline with only
those rows lowered, so a commit carries its own rows and none of a peer's.
"""

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, "scripts", "doc-size-baseline.txt")
MAX_DOC = 8
NEW_FILE_COMMENT_SHARE = 0.10
DEFS = {"ns", "defn", "defn-", "defmacro", "defmulti", "def", "defonce", "defprotocol",
        "definterface", "defrecord", "deftype", "deftest", "defspec"}
PROTOCOLS = {"defprotocol", "definterface"}
TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|;[^\n]*|\\.|[()\[\]{}]|#\{|\^|[^\s,()\[\]{}"^;]+', re.S)


def scan_files():
    out = subprocess.run(["git", "ls-files", "src", "test", "bench"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.split()
    return [p for p in out if p.endswith((".clj", ".cljc"))]


def docstrings(text):
    """Returns (offset, token) per `ns`, `def*` and protocol-method docstring, in order."""
    stack, out = [], []  # each frame: [head, element count, pending def-doc, kind]
    meta_next = False
    for m in TOKEN.finditer(text):
        tok = m.group(0)
        if tok.startswith(";"):
            continue
        if tok == "^":
            meta_next = True
            continue
        if tok in ("(", "[", "{", "#{"):
            if stack and not meta_next:
                stack[-1][1] += 1
            stack.append([None, 0, None, tok])
            meta_next = False
            continue
        if tok in (")", "]", "}"):
            frame = stack.pop() if stack else None
            # `(def x "s")` is a string value; a def docstring needs a value after it
            if frame and frame[2] and not (frame[0] in ("def", "defonce") and frame[1] < 4):
                out.append(frame[2])
            continue
        if meta_next or tok.startswith("^"):
            meta_next = False
            continue
        if not stack:
            continue
        top = stack[-1]
        top[1] += 1
        if top[1] == 1 and top[3] == "(":
            top[0] = tok
        if tok.startswith('"'):
            if top[3] == "(" and top[0] in DEFS and top[1] == 3:
                top[2] = (m.start(), tok)
            elif (top[3] == "(" and len(stack) > 1 and stack[-2][0] in PROTOCOLS
                  and top[1] >= 3):
                out.append((m.start(), tok))
    return sorted(out)


def measure(text):
    """(excess docstring lines, comment lines, code lines) of one source file."""
    excess = sum(max(0, tok.count("\n") + 1 - MAX_DOC) for _, tok in docstrings(text))
    lines = text.split("\n")
    comments = sum(1 for ln in lines if ln.lstrip().startswith(";"))
    code = sum(1 for ln in lines if ln.strip() and not ln.lstrip().startswith(";"))
    return excess, comments, code


def git(*args, stdin=None):
    return subprocess.run(["git", *args], cwd=ROOT, input=stdin, capture_output=True,
                          text=True, check=True).stdout


def parse_baseline(text):
    budget = {}
    for line in text.splitlines():
        if line.strip() and not line.startswith("#"):
            ex, cm, rel = line.split("\t")[:3]
            budget[rel] = (int(ex), int(cm))
    return budget


def read_baseline():
    return parse_baseline(open(BASELINE).read()) if os.path.exists(BASELINE) else {}


HEADER = """\
# Per-file budget for scripts/check-doc-size.py: <excess docstring lines>\\t<comment
# lines>\\t<path>.  A file absent from this list is allowed no docstring line past the
# 8th, and comments up to a tenth of its code lines.  `--update` lowers a budget and never
# raises one; a raise is a hand edit.
"""


def render(budget):
    return HEADER + "".join(f"{budget[rel][0]}\t{budget[rel][1]}\t{rel}\n"
                            for rel in sorted(budget))


def write_baseline(budget):
    with open(BASELINE, "w") as f:
        f.write(render(budget))


def lower(budget, counts, scope):
    """Lower the rows in `scope` to `counts`; return the paths left over budget."""
    raised = []
    for rel in scope:
        if rel not in counts:
            budget.pop(rel, None)
            continue
        ex, cm, code = counts[rel]
        was = allowance(rel, budget, code)
        budget[rel] = (min(ex, was[0]), min(cm, was[1]))
        if ex > was[0] or cm > was[1]:
            raised.append(rel)
        default = allowance(rel, {}, code)
        if budget[rel][0] <= default[0] and budget[rel][1] <= default[1]:
            budget.pop(rel)
    return raised


def allowance(rel, budget, code):
    return budget.get(rel, (0, int(code * NEW_FILE_COMMENT_SHARE)))


def stage(paths):
    rel_base = os.path.relpath(BASELINE, ROOT)
    budget = parse_baseline(git("show", f":{rel_base}"))
    staged = set(git("ls-files", "--", *paths).split())
    counts = {rel: measure(git("show", f":{rel}")) for rel in staged}
    raised = lower(budget, counts, set(paths))
    blob = git("hash-object", "-w", "--stdin", stdin=render(budget)).strip()
    git("update-index", "--cacheinfo", f"100644,{blob},{rel_base}")
    for rel in sorted(raised):
        print(f"doc-size: {rel} is over its budget as staged")
    return 1 if raised else 0


def main(argv):
    if "--stage" in argv:
        return stage(argv[argv.index("--stage") + 1:])
    counts = {rel: measure(open(os.path.join(ROOT, rel), encoding="utf-8").read())
              for rel in scan_files()}
    budget = read_baseline()

    if "--top" in argv:
        n = int(argv[argv.index("--top") + 1])
        for i, label in ((0, "docstring lines past the 8th"), (1, "comment lines")):
            print(f"{label}:")
            for rel, c in sorted(counts.items(), key=lambda kv: -kv[1][i])[:n]:
                print(f"  {c[i]:6d}  {rel}")
        print(f"total: {sum(c[0] for c in counts.values())} excess docstring lines, "
              f"{sum(c[1] for c in counts.values())} comment lines")
        return 0

    if "--seed" in argv:  # first run only: take the tree as it stands
        budget = {rel: c[:2] for rel, c in counts.items()}
        argv = ["--update"]
    if "--update" in argv:
        paths = [p for p in argv[argv.index("--update") + 1:] if not p.startswith("-")]
        raised = lower(budget, counts, set(paths) if paths else set(budget) | set(counts))
        write_baseline(budget)
        for rel in sorted(raised):
            print(f"doc-size: {rel} is over its budget; --update does not raise it")
        return 1 if raised else 0

    over, stale = [], []
    for rel, (ex, cm, code) in sorted(counts.items()):
        b_ex, b_cm = allowance(rel, budget, code)
        if ex > b_ex or cm > b_cm:
            over.append(f"  {rel}: {ex} excess docstring lines (budget {b_ex}), "
                        f"{cm} comment lines (budget {b_cm})")
        elif rel in budget and (ex < b_ex or cm < b_cm):
            stale.append(f"  {rel}: {ex}/{cm} against {b_ex}/{b_cm}")
    stale += [f"  {rel}: no longer tracked" for rel in budget if rel not in counts]
    if over:
        print("doc-size: over budget. Cut the docstring to the contract and move the "
              "reason to the doc page (economy.md):\n" + "\n".join(over))
    if stale:
        print("doc-size: below budget. Lower it:\n" + "\n".join(stale)
              + "\n  → python3 scripts/check-doc-size.py --update <path>…")
    if over or stale:
        return 1
    print(f"doc-size: {sum(c[0] for c in counts.values())} excess docstring lines, "
          f"{sum(c[1] for c in counts.values())} comment lines in {len(counts)} files")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
