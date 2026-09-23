#!/usr/bin/env python3
"""Check that doc claims about the code still match the code.

Scans README.md and docs/**.md for the drift classes that actually bite. Two
checks reach wider than that, because the prose outside docs/ rots the same way
and nothing else reads it: the LINK check (E4) and ARCHAEOLOGY (E7/W7) also read
CHANGELOG.md, CONTRIBUTING.md, CLAUDE.md and .claude/rules/*.md — see
`extra_md_files`. The rest stay on docs/: they check claims about the engine,
and those files describe the project around it.

  E1  defrecord/defprotocol snippets whose name or field list no longer
      matches the definition under src/ (the Atomic/Rule/Deduction class).
  E2  Backticked var refs — `vaelii.x.y/fn` or `alias/fn` for a known
      alias — whose definition is missing from the resolved namespace.
  E3  VAELII_* env vars that appear nowhere in src/, scripts/, resources/,
      or project.clj.
  E4  The link check: backticked repo paths (docs/x.md, scripts/x,
      src/.../y.clj, resources/...) that do not exist, and — in the markdown
      outside docs/ — relative `[text](path)` targets that resolve to nothing.
      check-doc-links.py resolves markdown links across docs/ and the
      contributor scaffolding; the files here are the ones it does not read.
  E5  A reference from inside the repo to an agent instruction file
      (`CLAUDE.md`, `.claude/...`).  Those are stow-linked from a separate
      dotfiles repo and gitignored here, so a reader who clones this repo
      does not have them: a pointer at one is a dead end, and the knowledge
      belongs in docs/ instead.  Scans source and scripts as well as docs.
  E6  A doc under docs/ that nothing links to — docs/README.md is the map, so
      a doc it does not reach is one nobody finds.
  E7  Archaeology: prose narrating the project's own past ("there used to be",
      "was previously", "the old behaviour", "before the fix").  A doc and a
      comment describe what the code does now; a diff already records how it
      got here.  Only the unambiguous phrasings are errors — plain "X used to
      Y" collides with "used to" meaning *employed to* ("the key used to diff
      against what is stored"), so it is W7 and the hook catches it at the
      keystroke instead.  A phrasing joins E7 only when every sentence that can
      carry it states the project's past: "was the one" stays out, because
      "whether it was the one that closed the subscription" is a live hypothetical,
      and so does "has since moved", because evidence moves at run time.  Scans
      source and scripts as well as docs, plus the markdown in `extra_md_files`.  Two of those files STATE this rule and so
      quote its phrasings in order to ban them; they are exempt by name, the
      same way this checker excludes itself.
  E8  `(requiring-resolve 'ns/var)` on a literal symbol anywhere under src/
      except vaelii.impl.wiring — a layering cut left at its call site, where
      nothing counts it and nothing stops the next one.  A computed symbol (a
      keyword->var registry) and the two optional backends are exempt.
  E9  Futurology: prose naming work as forthcoming ("on the roadmap", "is the
      next step", "left for a future pass", a `## TODO` section).  E7's mirror
      image and the same argument — the present is the only tense a doc has.
      Stating an ABSENCE is not futurology and is wanted ("there is no beta
      network", "## What is not built"): an absence is a fact about the engine.
      What this bans is the promise attached to one.  Narrower than E7 by
      design, and NOT extended to the files E7 gained: a changelog's whole job
      is to say what a released version does, which is indistinguishable from a commitment in
      every tense the patterns match, and CONTRIBUTING.md carries a forward
      statement about licensing that is a promise on purpose.  Scoping the
      check to the docs that describe the engine keeps it a check about the
      engine.
  E10 A `declare` with no comment above it saying which cycle forces it, or one
      whose every use is below its own definition (so it does nothing).  The
      preferred fix is a reordering; the comment is where "an ordering cannot
      fix this" gets written down.
  E11 Borrowed vocabulary: another system's word for something this engine
      already names.  Cyc's microtheory is our context; its NART and NAUT are
      our reified and structural NAT.  Reads as vaelii's own vocabulary while
      belonging to somebody else, and for a coinage found in no general KR
      literature it also implies a provenance nobody claimed.  Quoting the
      other system is not borrowing — `genlMt` and `BaseKB` are identifiers
      IN OpenCyc, not words for anything here, and go untouched.  Scans the
      sources, the docs, `extra_md_files` and the shipped ontology under
      `resources/kb/`; the allowlist excuses a token where a doc needs the
      borrowed word to explain the borrowing.
  E12 A doc under docs/ whose title is not followed by the three orientation
      bullets — **Covers**, **Not here**, **Assumes**.  They are what lets a
      reader (or a model routing on minimum context) spend one sentence rather
      than one section discovering the page is the wrong one, and they are only
      worth reading if every page has them.  docs/README.md is the map and
      dependencies.md is generated, so neither carries them.
  E13 A ```clojure or ```edn block that is not a whole s-expression.  A snippet
      missing its last paren looks like a snippet, so the reader who pastes it
      reads the error as theirs.  A real scan rather than a bracket count —
      comments, strings and `\\(` char literals all carry brackets that close
      nothing.  Reads `extra_md_files` too: a broken example in the changelog
      misleads exactly as one under docs/ does.
  E14 A `.clj` under src/, test/ or bench/ that does not open with the two
      licence-header lines, in order: `SPDX-License-Identifier: SSPL-1.0` then
      the copyright.  The identifier is PINNED, not merely required — the engine
      is SSPL-1.0 and the adapter siblings are Apache-2.0, so a file carrying the
      sibling's identifier is a licensing defect a presence check waves through.
  E15 A **Breaking** changelog entry in the unreleased section with no `*Breaks:*`
      line.  `scripts/check-breaking-siblings.sh` greps the siblings for that
      line's tokens, so an entry without one is swept and reports nothing —
      indistinguishable from a sibling that is fine.  The unreleased section only:
      the convention is newer than the released sections, and rewriting those to
      satisfy it is archaeology.
  E16 A raw `IndexStore` read (`p/sentexes-with-functor`, `p/rules-by-consequent`,
      `p/count-at`, …) anywhere under src/ but the implementers.  The index answers
      what is STORED, and a stored sentex is not a believed one — so every read
      carries a question, and read straight off the protocol nothing says which
      answer the caller wanted: a forgotten belief filter and a deliberate as-stored
      read look identical.  `vaelii.impl.reads` asks it in the name of the read, and
      the roster (`E16_OK_FILES`) is the one place an exception is written down.
      `RecordStore` is outside the check by design — a record IS the storage.
  E17 A `tax/…-global` taxonomy read from a `(file, top-level def)` pair not in
      `E17_ROSTER`.  A read sees what its context sees, and on a KB where no edge is
      context-restricted the global closure and the scoped one are the same object —
      so a caller that meant to scope and did not is right on every KB but the one it
      is wrong on.  The roster records THAT a caller has a reason; the reason itself
      lives in that definition's own docstring.
  E18 A `.clj` under src/ that docs/namespaces.md neither glosses in its file map nor
      names in its "Not glossed above" block — or a name in either list that is no
      longer a file, or a count in that section's first sentence that disagrees with
      the two lists.  The map's claim is arithmetic ("covers N of the M namespaces"),
      and nothing else reads it, so a namespace added without a line goes on being
      unmapped silently while the number beside it keeps asserting otherwise.
  E19 A `(requiring-resolve 'ns/var)` in vaelii.impl.wiring whose target is not one of
      the three the layering allows: the two genuine mutual recursions
      (`vaelii.core/assert`, `vaelii.impl.provers/solve-goal`) and the teardown entry
      point (`vaelii.core/retract!`), which a below-core solver reaches because the
      teardown orchestration is core-private for now.  E8 forces every literal
      requiring-resolve into that one file; E19 caps what it holds.  A fourth target is a
      layering inversion — a below-core reader reached from core through a delay here
      rather than relocated below core so the call points down (docs/namespaces.md, "The
      layering").  Reuses E8's literal matcher, so a computed requiring-resolve is
      as invisible to it as to E8.

  W1  Line-number citations into .clj files (`foo.clj:123`) — warned, not
      failed: cite the var name instead, line numbers always rot.
  W2  Backticked `alias/name` for an UNKNOWN alias whose name is defined
      nowhere under src/ or test/ — a likely renamed alias.
  W6  Backticked KB symbols (`set/forwardRule`, `do/label` — namespaced KB
      performatives/markers, NOT Clojure vars) absent from the KB corpus.
  W7  The ambiguous half of E7 — see above.

Not flagged: MIME types (`application/json`), Maven coordinates / java
packages (dotted group ids not starting with `vaelii`).

vaelii is self-contained (no sibling checkouts), so every reference must
resolve within the repo — missing env vars and paths are hard errors, not
"unverifiable" warnings.

Errors exit 1; warnings exit 0. False positives go in
scripts/check-doc-drift-allowlist.txt (one literal token per line, matched
against the flagged token; # comments allowed).
"""
import itertools
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "src")
TEST_SRC = os.path.join(ROOT, "test")
RESOURCES = os.path.join(ROOT, "resources")
FENCE = re.compile(r"^\s*(```|~~~)")

# Conventional alias -> namespace map (harvested from the `:as` requires across
# src/ and test/). Aliases not listed fall back to a global any-namespace
# name-existence check (W2).
ALIASES = {
    "v": "vaelii.core", "core": "vaelii.core",
    "aspif": "vaelii.impl.asp.aspif", "atoms": "vaelii.impl.asp.atoms",
    "clasp": "vaelii.impl.asp.clasp", "clingo": "vaelii.impl.asp.clingo",
    "edge": "vaelii.impl.asp.edge", "label": "vaelii.impl.asp.label",
    "solver": "vaelii.impl.asp.solver",
    "budget": "vaelii.impl.budget",
    "cap": "vaelii.impl.capabilities", "capabilities": "vaelii.impl.capabilities",
    "chain": "vaelii.impl.chain",
    "checks": "vaelii.impl.checks", "core-context": "vaelii.host.core-context",
    "backend": "vaelii.impl.disk.backend", "disk": "vaelii.impl.disk.backend",
    "dur": "vaelii.impl.disk.durability", "f": "vaelii.impl.disk.files",
    "dkv": "vaelii.impl.disk.kv", "lock": "vaelii.impl.disk.lock",
    "drs": "vaelii.impl.disk.record-store",
    "infer": "vaelii.impl.infer",
    "integrate": "vaelii.impl.integrate", "jtms": "vaelii.impl.jtms",
    "kb": "vaelii.impl.kb", "kv": "vaelii.impl.kv",
    "levels": "vaelii.impl.levels", "lvl": "vaelii.impl.levels",
    "mem": "vaelii.impl.memory", "nm": "vaelii.impl.naming",
    "nat": "vaelii.impl.nat", "observe": "vaelii.impl.observe",
    "plan": "vaelii.impl.plan", "p": "vaelii.impl.protocols",
    "provers": "vaelii.impl.provers", "quasiquote": "vaelii.impl.quasiquote",
    "recovery": "vaelii.impl.recovery", "reindex": "vaelii.impl.reindex",
    "rete": "vaelii.impl.rete", "rewrite": "vaelii.impl.rewrite",
    "rw": "vaelii.impl.rewrite", "rules": "vaelii.impl.rules",
    "vr": "vaelii.impl.rules", "seed": "vaelii.host.seed",
    "sentex": "vaelii.impl.sentex", "sx": "vaelii.impl.sentex",
    "settle": "vaelii.impl.settle", "solve": "vaelii.impl.solve",
    "special": "vaelii.impl.special", "starter": "vaelii.host.starter",
    "strength": "vaelii.impl.strength", "tax": "vaelii.impl.taxonomy",
    "taxonomy": "vaelii.impl.taxonomy", "web": "vaelii.browser.web",
    "wff": "vaelii.impl.wff",
}

# `deftest` (clojure.test), `deftest-kb` (vaelii.test-util) and `defroutes`
# (reitit/ring) define vars too, and docs cite them by their test-ns / browser-ns
# alias; include so those refs resolve instead of warning.
#
# The optional alias prefix is what admits the QUALIFIED spellings, and it is
# `deftest-kb` that needs it: `tu/deftest-kb` is the repo's primary test form
# (`.claude/rules/testing.md`) and outnumbers bare `deftest` in the suite, so a
# pattern anchored at `(def` sees only the minority of the tests and every
# citation of the rest is indistinguishable from a missing definition.  `test-kb` precedes `test`
# in the alternation so the longer name wins without backtracking.
DEF_RE = (r"\((?:[a-z][\w.-]*/)?"
          r"def(?:n|n-|macro|multi|method|protocol|record|type|once|test-kb|test|routes)?"
          r"\s+(?:\^\S+\s+|\^\{[^}]*\}\s+)*")

# Namespaced KB SYMBOLS (performatives, work-state markers, aggregate operators,
# answer-set cardinality forms) — not Clojure vars. Checked for existence against
# the source + resources corpus (W6), never against the def index. `set/*Rule`,
# `do/label`, `agg/count`, `asp/atMost`, ...
KB_SYMBOL_PREFIXES = {"set", "do", "agg", "asp"}

# MIME types in API docs (`application/json`, `application/nippy`).
MIME_PREFIXES = {"application", "text", "multipart", "image", "audio", "video"}


def load_allowlist():
    allow = set()
    p = os.path.join(ROOT, "scripts", "check-doc-drift-allowlist.txt")
    if os.path.exists(p):
        for line in open(p):
            line = line.strip()
            if line and not line.startswith("#"):
                allow.add(line)
    return allow


def md_files():
    p = os.path.join(ROOT, "README.md")
    if os.path.exists(p):
        yield p
    for dirpath, _, names in os.walk(os.path.join(ROOT, "docs")):
        for n in sorted(names):
            if n.endswith(".md"):
                yield os.path.join(dirpath, n)


def extra_md_files():
    """The markdown outside README/docs that the repo's own rules still bind.

    Three checks read these and no others do: the link check (E4), archaeology
    (E7/W7) and the s-expression check (E13). The first two are rules about
    prose, and prose here rots exactly as it does under docs/ — a link into a
    directory that is not there is indistinguishable from a live one either way. E13 joins them
    on the same footing: whether an example parses is a fact about the example,
    not about which file carries it.

    CHANGELOG.md and CONTRIBUTING.md ship. CLAUDE.md and .claude/rules/ do not:
    they are stow-linked from a dotfiles repo and gitignored here, so a clone has
    neither and each is scanned only if it is present. That is also why they get
    three checks rather than all of them — the var, env and record checks verify
    claims about the engine, and these files describe the project around it.
    """
    for rel in ("CHANGELOG.md", "CONTRIBUTING.md", "CLAUDE.md"):
        p = os.path.join(ROOT, rel)
        if os.path.exists(p):
            yield p
    rules = os.path.join(ROOT, ".claude", "rules")
    if os.path.isdir(rules):
        for n in sorted(os.listdir(rules)):
            if n.endswith(".md"):
                yield os.path.join(rules, n)


def clj_files():
    for dirpath, _, names in os.walk(SRC):
        for n in names:
            if n.endswith(".clj"):
                yield os.path.join(dirpath, n)


# The opening line of a fence, with its info string. Separate from FENCE (which
# only asks "is this a fence line") because E13 needs the language and the line
# number, and the flat fenced/prose split above throws both away.
FENCE_OPEN = re.compile(r"^\s*(```|~~~)\s*([A-Za-z0-9_+-]*)")


def fenced_blocks(path):
    """Yield `(lang, start_line, body)` for each fenced block in `path`.

    The closing fence must use the SAME marker that opened it, so a ``` inside a
    ~~~ block is content rather than a terminator. The flat toggle used elsewhere
    in this file cannot tell those apart; it does not need to, and this does.
    """
    marker = lang = start = None
    buf = []
    for i, line in enumerate(open(path, errors="replace").read().splitlines(), 1):
        m = FENCE_OPEN.match(line)
        if marker is None:
            if m:
                marker, lang, start, buf = m.group(1), m.group(2).lower(), i, []
        elif m and m.group(1) == marker:
            yield lang, start, "\n".join(buf)
            marker = None
        else:
            buf.append(line)


def sexp_imbalance(src):
    """`None` if `src` is balanced, else a sentence saying how it is not.

    A real scan and not a bracket count: `;` comments, `"strings"` with their
    escapes, and `\\(` character literals all carry brackets that close nothing,
    and every one of them appears in these docs. Counting naively reports each as
    a broken example, which is how a check like this gets switched off.
    """
    close = {"(": ")", "[": "]", "{": "}"}
    stack, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c == "\\":                       # \( \; \" — one char literal
            i += 2
        elif c == ";":
            while i < n and src[i] != "\n":
                i += 1
        elif c == '"':
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                    continue
                if src[i] == '"':
                    i += 1
                    break
                i += 1
        else:
            if c in close:
                stack.append(close[c])
            elif c in ")]}":
                if not stack:
                    return f"a stray `{c}` closes nothing"
                want = stack.pop()
                if want != c:
                    return f"a `{c}` closes what a `{want}` should"
            i += 1
    if stack:
        return f"{len(stack)} unclosed — the block needs `{''.join(reversed(stack))}`"
    return None


def ns_to_path(ns):
    return os.path.join(SRC, ns.replace(".", "/").replace("-", "_") + ".clj")


def parse_field_vector(text, start):
    """Symbols inside the [...] starting at text[start]; ;; comments dropped."""
    depth, i, buf = 0, start, []
    while i < len(text):
        c = text[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                break
        buf.append(c)
        i += 1
    body = re.sub(r";[^\n]*", " ", "".join(buf))
    return re.findall(r"[A-Za-z_*+!?<>=-][\w*+!?<>=.'-]*", body)


def record_fields_in(text, name):
    m = re.search(r"\(def(?:record|protocol)\s+" + re.escape(name) + r"\b", text)
    if m is None:
        return None
    bracket = text.find("[", m.end())
    if bracket == -1:
        return []  # defprotocol: no field vector
    return parse_field_vector(text, bracket)


# Build the code-side indexes once.
src_text = {}
all_def_names = set()
for path in clj_files():
    text = open(path).read()
    src_text[path] = text
    for m in re.finditer(DEF_RE + r"([\w*+!?<>=.'-]+)", text):
        all_def_names.add(m.group(1))
    if "defprotocol" in text:  # protocol method signatures are definitions too
        for m in re.finditer(r"^\s+\(([a-z][\w*+!?<>=.'-]*)\s+\[", text, re.M):
            all_def_names.add(m.group(1))

# Test definitions count as "defined under the repo" for the W2 existence check:
# docs cite test vars by their test-ns alias. clj_files() only walks src/, so
# harvest the test tree's def names separately.
if os.path.isdir(TEST_SRC):
    for dirpath, _, names in os.walk(TEST_SRC):
        for n in names:
            if n.endswith(".clj"):
                try:
                    t = open(os.path.join(dirpath, n)).read()
                except (UnicodeDecodeError, OSError):
                    continue
                for m in re.finditer(DEF_RE + r"([\w*+!?<>=.'-]+)", t):
                    all_def_names.add(m.group(1))

# KB corpus for W6: every .clj/.txt/.edn under src + resources. Built lazily —
# only docs that mention KB symbols pay.
_kb_corpus = None


def kb_corpus():
    global _kb_corpus
    if _kb_corpus is None:
        chunks = list(src_text.values())
        for root in (RESOURCES,):
            for dirpath, _, names in os.walk(root):
                for n in names:
                    if n.endswith((".clj", ".txt", ".edn")):
                        try:
                            chunks.append(open(os.path.join(dirpath, n)).read())
                        except (UnicodeDecodeError, OSError):
                            pass
        _kb_corpus = "\n".join(chunks)
    return _kb_corpus


allow = load_allowlist()
allow_used = set()  # allowlist tokens that actually suppressed a finding
errors, warnings = [], []


def flag(kind, doc, token, msg):
    if token in allow:
        allow_used.add(token)
        return
    (errors if kind.startswith("E") else warnings).append(
        f"{kind} {os.path.relpath(doc, ROOT)}: {msg}")


# nsish words that are directory/language names, not aliases.
NS_STOP = {"docs", "scripts", "src", "resources", "test", "target",
           "checkouts", "bench", "vaelii"}

# Docs whose markdown TABLE ROWS may carry `file.clj:NNN` citations without a W1
# warning, because a test resolves each one (see the W1 loop below). Prose in the
# same file is still warned about — the exemption is the checked citations.
W1_CHECKED_BY_TEST = {"docs/operations.md"}

for doc in md_files():
    lines = open(doc).read().split("\n")

    # Split into fenced/unfenced views.
    in_fence, fence_lines, prose_lines = False, [], []
    for line in lines:
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        (fence_lines if in_fence else prose_lines).append(line)
    fenced, prose = "\n".join(fence_lines), "\n".join(prose_lines)
    whole = "\n".join(lines)

    # E1: defrecord/defprotocol snippets in fenced blocks.
    for m in re.finditer(r"\(def(record|protocol)\s+([A-Za-z][\w.-]*)", fenced):
        kind, name = m.groups()
        hits = [p for p, t in src_text.items()
                if re.search(r"\(def" + kind + r"\s+" + re.escape(name) + r"(?![\w.-])", t)]
        if not hits:
            flag("E1", doc, name, f"doc shows (def{kind} {name} ...) but no such "
                 f"def{kind} exists under src/")
            continue
        if kind == "record":
            doc_fields = parse_field_vector(fenced, fenced.find("[", m.end()))
            real_fields = record_fields_in(src_text[hits[0]], name)
            if doc_fields and real_fields and doc_fields != real_fields:
                flag("E1", doc, name,
                     f"(defrecord {name}) fields drifted: doc {doc_fields} "
                     f"vs code {real_fields} ({os.path.relpath(hits[0], ROOT)})")

    # E2: backticked var refs.
    for m in re.finditer(r"`([A-Za-z][\w.-]*)/([\w*+!?<>=.'-]+)`", whole):
        nsish, name = m.groups()
        token = f"{nsish}/{name}"
        if (nsish in NS_STOP or name.isdigit() or "<" in name or ">" in name
                or ("*" in name and not re.fullmatch(r"\*[^*]+\*", name))
                or re.search(r"\.(md|sh|clj|cljs|cljc|edn|txt|py|svg|yml|yaml|json|csv|log|idx)$", name)):
            continue
        if "." in nsish and nsish.startswith("vaelii"):
            ns = nsish
        elif nsish in ALIASES:
            ns = ALIASES[nsish]
        else:
            ns = None
        if ns:
            path = ns_to_path(ns)
            if os.path.exists(path):
                t = src_text.get(path, "")
                defined = re.search(DEF_RE + re.escape(name) + r"(?![\w*+!?<>=.'-])", t) \
                    or ("defprotocol" in t and re.search(r"^\s+\(" + re.escape(name) + r"\s+\[", t, re.M))
                if not defined:
                    flag("E2", doc, token,
                         f"`{token}` not defined in {os.path.relpath(path, ROOT)}")
            # ns file absent: skip (nothing to verify against).
        else:
            if nsish in MIME_PREFIXES:
                continue
            if "." in nsish and not nsish.startswith("vaelii"):
                continue  # Maven coordinate / java package, not an alias
            if nsish in KB_SYMBOL_PREFIXES:
                if token not in kb_corpus():
                    flag("W6", doc, token,
                         f"KB symbol `{token}` not found anywhere in src/ or "
                         f"resources/")
                continue
            # Unknown alias: any-namespace existence check.
            if re.fullmatch(r"[a-z][\w.-]*", nsish) and name not in all_def_names \
               and not name.startswith("*"):
                flag("W2", doc, token,
                     f"`{token}` — `{name}` not found as a definition anywhere "
                     f"under src/ or test/ (unknown alias `{nsish}`; rename?)")

    # E3: env vars.
    for var in set(re.findall(r"\bVAELII_[A-Z0-9_]+\b", whole)):
        if var in allow:
            allow_used.add(var)
            continue
        kw = ":" + var.lower().replace("_", "-")
        found = any(var in t or kw in t for t in src_text.values())
        if not found:
            # test/ carries the VAELII_TEST_* knobs; scan it too.
            roots = [os.path.join(ROOT, "project.clj"),
                     os.path.join(ROOT, "scripts"), RESOURCES, TEST_SRC]
            for p in roots:
                if os.path.isfile(p):
                    t = open(p).read()
                    if var in t or kw in t:
                        found = True
                        break
                    continue
                if os.path.isdir(p):
                    for dp, _, ns in os.walk(p):
                        for n in ns:
                            try:
                                t = open(os.path.join(dp, n)).read()
                                if var in t or kw in t:
                                    found = True
                                    break
                            except (UnicodeDecodeError, IsADirectoryError, OSError):
                                pass
                        if found:
                            break
                if found:
                    break
        if not found:
            flag("E3", doc, var,
                 f"env var {var} appears in docs but nowhere in code")

    # E4: backticked repo paths.
    for m in re.finditer(r"`((?:docs|scripts|src|resources)/[\w./-]+)`", prose):
        rel = m.group(1)
        if any(ch in rel for ch in "*<>{") or rel.endswith("/") \
           or "..." in rel or re.search(r"/[A-Z]($|/)", rel):
            continue
        if not os.path.exists(os.path.join(ROOT, rel)):
            flag("E4", doc, rel, f"path `{rel}` does not exist")

    # W1: line-number citations into clj files.
    #
    # The configuration table is the one place a line number is wanted, and the
    # reason is that something checks it: config_surface_test reads every
    # `file:line` cell out of that table and fails when the cited line does not
    # name the switch. W1's argument is that line numbers rot silently, and a
    # citation a test resolves does not — so the exemption is the rows of that
    # table, not the file around them.
    exempt_rows = os.path.relpath(doc, ROOT) in W1_CHECKED_BY_TEST
    for pline in prose_lines:
        if exempt_rows and pline.lstrip().startswith("|"):
            continue
        for m in re.finditer(r"[\w/-]+\.clj:\d+", pline):
            flag("W1", doc, m.group(0),
                 f"line-number citation `{m.group(0)}` — cite the var name instead")


# ── E5: no reference from inside the repo to an agent instruction file ──────
# They are gitignored here (stow-linked from a dotfiles repo), so a pointer at
# one is a dead end for anyone who clones this repo.  This file names them to
# check for them, so it excludes itself.
AGENT_FILE = re.compile(r"CLAUDE(\.local)?\.md|\.claude/")
SELF = os.path.abspath(__file__)


def repo_text_files():
    yield from md_files()
    for sub in ("src", "test", "bench"):
        for dirpath, _, names in os.walk(os.path.join(ROOT, sub)):
            for n in sorted(names):
                if n.endswith(".clj"):
                    yield os.path.join(dirpath, n)
    scripts = os.path.join(ROOT, "scripts")
    for dirpath, _, names in os.walk(scripts):
        for n in sorted(names):
            if n.endswith((".sh", ".py", ".clj")):
                yield os.path.join(dirpath, n)
    yield os.path.join(ROOT, "project.clj")


for path in repo_text_files():
    if os.path.abspath(path) == SELF or not os.path.exists(path):
        continue
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = AGENT_FILE.search(line)
        if m:
            rel = os.path.relpath(path, ROOT)
            flag("E5", path, m.group(0),
                 f"{rel}:{i} references `{m.group(0)}` — an agent instruction "
                 f"file, gitignored here; state the fact in docs/ instead")

# ── E6: every doc under docs/ is linked from another doc ───────────────────
# docs/README.md is the map, so it needs no inbound link; dependencies.md is
# generated.
UNLINKED_OK = {"docs/README.md", "docs/dependencies.md"}
MD_LINK = re.compile(r"\[[^\]]*\]\(([^)#]+)")

linked = set()
for doc in md_files():
    for m in MD_LINK.finditer(open(doc).read()):
        target = m.group(1).strip()
        if target.startswith(("http:", "https:", "mailto:")):
            continue
        resolved = os.path.normpath(os.path.join(os.path.dirname(doc), target))
        linked.add(os.path.relpath(resolved, ROOT))

for doc in md_files():
    rel = os.path.relpath(doc, ROOT)
    if rel == "README.md" or rel in UNLINKED_OK or rel in linked:
        continue
    flag("E6", doc, rel, f"`{rel}` is linked from no other doc — add it to the "
                         f"map so a reader can find it")

# ── E4 (extended): the link check over the markdown beside docs/ ────────────
# The same two rots as inside docs/ — a backticked repo path that no longer
# exists, and a relative markdown link that resolves to nothing — read over the
# files in extra_md_files(). A pointer into a directory that was removed reads
# exactly like a live one, and the reader who finds out is the one who followed
# it.
#
# Fenced blocks are skipped: an example link is not a claim about the tree.
for doc in extra_md_files():
    rel_doc = os.path.relpath(doc, ROOT)
    in_fence = False
    for i, line in enumerate(open(doc, errors="replace"), 1):
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        for m in MD_LINK.finditer(line):
            target = m.group(1).strip().split("?")[0]
            if not target or target.startswith(("http:", "https:", "mailto:")):
                continue
            resolved = os.path.join(os.path.dirname(doc), target)
            if not os.path.exists(resolved):
                flag("E4", doc, target,
                     f"{rel_doc}:{i} link `{target}` resolves to nothing")
        for m in re.finditer(r"`((?:docs|scripts|src|resources)/[\w./-]+)`", line):
            p = m.group(1)
            if any(ch in p for ch in "*<>{") or p.endswith("/") \
               or "..." in p or re.search(r"/[A-Z]($|/)", p):
                continue
            if not os.path.exists(os.path.join(ROOT, p)):
                flag("E4", doc, p, f"{rel_doc}:{i} path `{p}` does not exist")

# ── E7/W7: no archaeology — the present is the only tense ──────────────────
# Split by how ambiguous the phrasing is.  ARCHAEOLOGY is unambiguous: nothing
# but the project's own past reads that way, so it fails the build.  AMBIGUOUS
# is the "X used to Y" family, which collides with "used to" meaning *employed
# to* — a warning here, and the write-time hook is where it pays for itself.
# This file names the phrases to look for them, so it excludes itself.
# The banned repo name is assembled from halves: the checker must not itself
# contain the name it bans, or it would be the tree's one occurrence.
_BANNED_REPO = "vaelii-" + "shell"
ARCHAEOLOGY = re.compile(
    r"\b(there|it|which|that|this) used to\b"
    r"|\bwe used to\b"
    r"|\b(was|were) previously\b"
    r"|\bpreviously (wrong|broken|answerable|detected|named|called|stored|"
    r"written|done|built|required|the case)\b"
    r"|\bthe old (way|approach|code|version|behaviou?r|implementation|scheme"
    r"|form|rule|check|path|semantics)\b"
    r"|\bbefore (the|this|that) fix\b|\bprior to the fix\b"
    r"|\bthe point of the change\b"
    r"|\b(formerly|renamed from|was renamed|used to be called)\b"
    r"|\bhistorically\b|\bat one point\b"
    r"|\ban earlier (version|form|implementation|shape)\b"
    r"|\bthe earlier (code|version|form|rule|check|behaviou?r)\b"
    r"|\bsince (renamed|removed|deleted|dropped)\b"
    r"|\bno longer (a|an|the) (parameter|argument|var|function|namespace|field|key"
    r"|option)\b"
    r"|\b" + _BANNED_REPO + r"\b",
    re.I)
# "<lowercase word> used to <verb>", excluding the auxiliary ("be used to") and
# the appositive (", used to …") — both of which are the *employed to* sense.
AMBIGUOUS = re.compile(r"(?<!be )(?<!,)\b[a-z0-9`)\]*]+ used to [a-z]")
# A prompt under docs/design/**-prompts/ briefs work not yet done, so "before
# the change" there means "before you make it" — a verification step, not a
# memoir.
PROMPT_DIR = re.compile(r"docs/design/[a-z-]*prompts/")
# Two files STATE this rule, so they quote its phrasings in order to ban them —
# the same reason this checker excludes itself. Exempting the file is the only
# defensible option available: the allowlist matches a TOKEN, so excusing
# "there used to" there would disarm the check in every other file too.
E7_STATES_THE_RULE = {"CONTRIBUTING.md", ".claude/rules/conventions.md"}

for path in itertools.chain(repo_text_files(), extra_md_files()):
    if os.path.abspath(path) == SELF or not os.path.exists(path):
        continue
    rel = os.path.relpath(path, ROOT)
    if rel.startswith("docs/design/complete/") or rel.startswith("resources/") \
       or rel in E7_STATES_THE_RULE:
        continue          # dated reviews quote as-of; resources/ is third-party
    prompt = bool(PROMPT_DIR.search(rel))
    # W7 is prose-only: in a docstring "used to" is usually the *employed to*
    # sense ("the content used to diff against what is stored"), which would
    # make it permanent noise.  E7 still reads every file, and the write-time
    # hook covers the ambiguous half of a comment as it is typed.
    soft_ok = rel.endswith(".md") and not prompt
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = ARCHAEOLOGY.search(line)
        kind = "E7"
        if not m and soft_ok:
            m, kind = AMBIGUOUS.search(line), "W7"
        if m:
            flag(kind, path, m.group(0).strip(),
                 f"{rel}:{i} `{m.group(0).strip()}` — archaeology; say what "
                 f"the code does now, not what it did")

# ── E9: no futurology — the other direction of the same rule ────────────────
# E7 bans narrating the project's past; this bans announcing its future. A doc
# that names work as forthcoming is making a commitment on behalf of whoever
# reads it next, and what gets built is not knowable in advance.
#
# The distinction to keep: an ABSENCE is a fact and belongs in the docs — "there is no
# beta network", "## What is not built", "nothing reads the `:out` slot". A
# PROMISE about that absence does not. So the patterns below match the promise
# ("on the roadmap", "left for a future pass", "is the next step"), never the
# bare statement that something does not exist.
#
# Deliberately narrow, for the reason E7 is: "a future handle", "a future
# channel" and "a future change to this test" are all ordinary present-tense
# prose, and a check that flags them is a check people learn to route around.
#
# Narrow in SCOPE as well, and this is the one place the two rules part company:
# E7 reads extra_md_files() and E9 does not. A changelog exists to say what a
# released version does, and it says it in the tense these patterns match, so
# every entry would read as a commitment; CONTRIBUTING.md carries a licensing
# statement about later versions that is a promise deliberately made. Both are
# writing about the project rather than about the engine, and E9 is a rule about
# what the ENGINE docs may claim.
FUTUROLOGY = re.compile(
    r"^#{2,}\s*TODO\b"
    r"|\bon the roadmap\b|\bthe roadmap (files|names|calls|has)\b|\broadmap\.md\b"
    r"|\bis the next step\b|\bthe natural next (step|variant)\b"
    r"|\bleft for a (future|someday|later)\b"
    r"|\ba future (pass|release|version|variant|revision)\b"
    r"|\bwe (plan|intend) to\b|\bis planned for\b"
    r"|\bcoming soon\b|\bfor now, until\b"
    r"|\bthe remaining (step|work|win)\b"
    r"|\bis a follow-on\b|\bseparate follow-ons?\b"
    r"|\bwould replace it (later|eventually)\b",
    re.I | re.M)

for path in repo_text_files():
    if os.path.abspath(path) == SELF or not os.path.exists(path):
        continue
    rel = os.path.relpath(path, ROOT)
    # docs/design/ briefs unbuilt work by definition — that whole tree is the
    # place plans are allowed to live, and it does not ship. resources/ is
    # third-party. CONTRIBUTING.md states this rule, so it quotes the
    # phrasings in order to ban them.
    if (rel.startswith(("docs/design/", "resources/"))
            or rel == "CONTRIBUTING.md"):
        continue
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = FUTUROLOGY.search(line)
        if m:
            flag("E9", path, m.group(0).strip(),
                 f"{rel}:{i} `{m.group(0).strip()}` — futurology; say what the "
                 f"engine does now. An absence is a fact and may be stated; a "
                 f"plan to remove it may not")

# ── E8: a layering cut belongs in the wiring inventory, not at its call site ─
# `(requiring-resolve 'ns/var)` on a *literal* symbol is an edge the require graph
# could express but does not — a layering cut.  Left at its call site it is
# invisible: nothing counts them and nothing stops the next one.  So they live in
# vaelii.impl.wiring, one file, each owing the reason it cannot be an ordinary
# require (see that namespace's docstring).  Two shapes are not cuts:
#
#   - a *computed* symbol — `(requiring-resolve sym)` read off a keyword->var
#     registry (core's reasoners / calculi / solvers, imperative's `do/` handlers,
#     foreign's plugins, the LLM providers).  Deferral is the feature: the table is
#     the public way to ask for a subsystem, and naming one must not load eight.
#   - an optional dependency whose entire point is not being loaded — the dense TMS
#     (RoaringBitmap, fastutil), the clingo bridge (JNA, libclingo), the
#     embedded-SQLite and Postgres record stores (the Apache-2.0 `com.vaelii/sqlite`
#     and `com.vaelii/postgres` siblings the SSPL engine does not depend on), the
#     sampling profiler, and tools.namespace's dependency graph for the hot-reload dev
#     server (`vaelii.browser.reload`, which resolves it through a computed symbol) —
#     the last two shipping in the `:repl`/`:dev` profiles and therefore absent from a
#     served process by design.  A
#     require of one of those is not a layering cut this repo could straighten out:
#     it is a namespace that is not on the classpath, so the require would fail the
#     load rather than defer it.
#     Listed here by target, so adding one is a deliberate edit rather than a habit.
#
# What this does NOT see, stated so nobody over-trusts it: only the literal form
# is matched, so binding the symbol first — `(let [s 'a.b/c] (requiring-resolve s))`
# — is a cut this rule is indistinguishable from a registry and passes.  Closing that would mean
# banning the computed form outright, which is the form the four legitimate
# registries above are built from.  So the rule catches the cut somebody writes
# without thinking, not the one somebody hides; the inventory is a convention the
# check defends, not a sandbox it enforces.
E8_OK_FILES = {"src/vaelii/impl/wiring.clj"}
E8_OK_TARGETS = {"vaelii.impl.dense-jtms/create-dense-tms",
                 "vaelii.sqlite.record-store/sqlite-record-store",
                 "vaelii.postgres.record-store/pg-record-store",
                 "vaelii.impl.asp.clingo/solve",
                 "vaelii.impl.asp.clingo/classify-both",
                 "vaelii.impl.asp.clingo/available?",
                 "clj-async-profiler.core/serve-ui"}
E8_LITERAL = re.compile(r"\(requiring-resolve\s+'([^\s()]+)")

for path in clj_files():
    rel = os.path.relpath(path, ROOT)
    if rel in E8_OK_FILES:
        continue
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = E8_LITERAL.search(line)
        if not m or m.group(1) in E8_OK_TARGETS:
            continue
        flag("E8", path, m.group(1),
             f"{rel}:{i} `requiring-resolve '{m.group(1)}` — a layering cut at its "
             f"call site; give it a real fix, or move it to vaelii.impl.wiring "
             f"with the reason it cannot be a require")

# ── E19: wiring.clj holds only the layering's up-calls ──────────────────────
# E8 forces every literal `(requiring-resolve 'ns/var)` into vaelii.impl.wiring,
# but nothing caps what that one file holds.  A layering inversion surfaces there
# as one more upward requiring-resolve: a below-core reader reached from core
# through a delay here, rather than relocated below core so the call points down
# (docs/namespaces.md, "The layering").  So pin the inventory to the three the
# layering allows — the two genuine mutual recursions and the teardown entry point a
# below-core solver reaches while the teardown orchestration stays core-private; a
# fourth target is an inversion to relocate, not to add here.  Reuses E8_LITERAL, so a
# computed `(requiring-resolve sym)` is invisible to it exactly as it is to E8.
E19_WIRING = os.path.join(ROOT, "src/vaelii/impl/wiring.clj")
E19_OK_TARGETS = {"vaelii.core/assert",
                  "vaelii.impl.provers/solve-goal",
                  "vaelii.core/retract!"}
if os.path.exists(E19_WIRING):
    for i, line in enumerate(open(E19_WIRING, errors="replace"), 1):
        m = E8_LITERAL.search(line)
        if m and m.group(1) not in E19_OK_TARGETS:
            flag("E19", E19_WIRING, m.group(1),
                 f"src/vaelii/impl/wiring.clj:{i} `requiring-resolve "
                 f"'{m.group(1)}` — a target beyond the three wiring holds "
                 f"(vaelii.core/assert, vaelii.impl.provers/solve-goal, "
                 f"vaelii.core/retract!); relocate the callee below vaelii.core so the "
                 f"call points down, rather than adding an inversion here")

# ── E10: a declare owes a reason, and a dead one owes nothing ───────────────
# `declare` is how a file admits its definitions do not fall in dependency
# order.  Two things go wrong with one, and both are mechanical:
#
#   - it carries no reason.  A genuine cycle (`cmp-term` descends to `cmp-seq`,
#     which compares with `cmp-term`) and a mere ordering accident read exactly
#     alike at the declare, and only one of them is allowed to stay — so the
#     comment above it is what says which, and without it the next reader has to
#     re-derive the call graph to find out.
#   - it is dead.  A name whose every use is below its own definition needs no
#     forward reference at all; `defn` interns the var before compiling the body,
#     so even self-recursion does not need one.  A dead declare is indistinguishable from a claim
#     about the file that is not true.
#
# Reordering is the preferred fix and this rule does not know when one is
# possible — it asks for the reason, and the reason is where "an ordering cannot
# fix this" gets written down.
DECLARE = re.compile(r"^\s*\(declare\s+(.+?)\)\s*$")
DEFINES = r"^\s*\((?:defn-?|def|defmacro|defmulti|deftype|defrecord|defprotocol)\s+(?:\^\S+\s+)*{}[\s)]"


def blank_strings(text):
    """Strings and comments emptied, newlines kept, so line numbers still hold."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == "\\" and i + 1 < n:          # char literal: \" \( \;
            out.append("  ")
            i += 2
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            out.append("\n" * text[i:j].count("\n"))
            i = j
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


for path in clj_files():
    rel = os.path.relpath(path, ROOT)
    raw = open(path, errors="replace").read().splitlines()
    code = blank_strings("\n".join(raw)).splitlines()
    for i, line in enumerate(code):
        m = DECLARE.match(line)
        if not m:
            continue
        j = i - 1
        while j >= 0 and not raw[j].strip():
            j -= 1
        if not (j >= 0 and raw[j].lstrip().startswith(";;")):
            flag("E10", path, f"{rel}:declare",
                 f"{rel}:{i + 1} `{line.strip()}` — a declare with no reason above "
                 f"it; say which cycle forces it, or reorder and drop it")
        for name in m.group(1).split():
            pat = re.compile(DEFINES.format(re.escape(name)))
            defined = next((k for k, l in enumerate(code) if pat.match(l)), None)
            if defined is None:
                continue
            word = re.compile(rf"(?<![\w.*+!?<>=/-]){re.escape(name)}(?![\w.*+!?<>=/-])")
            if not any(word.search(l) for k, l in enumerate(code)
                       if k != i and k != defined and k < defined):
                flag("E10", path, f"{rel}:{name}",
                     f"{rel}:{i + 1} `{name}` is declared but never used above its "
                     f"definition (line {defined + 1}) — the declare does nothing; "
                     f"`defn` interns the var before it compiles the body")

# ── E11: borrowed vocabulary — somebody else's word for a thing we name ─────
# The engine calls it a CONTEXT, and a non-atomic term is a NAT — reified or
# structural. Cyc's words for those same things are not vaelii's, and prose
# that uses them gives the impression that they were: wrong for a reader who then looks
# them up, and for a coinage that appears in no general KR literature, a claim
# about where this engine came from that nobody made.
#
# Citing the other system stays legitimate, and this check leaves it alone:
# `genlMt`, `BaseKB` and `UniversalVocabularyMt` are IDENTIFIERS in OpenCyc,
# not words for anything here, so they are not borrowed vocabulary — they are
# quotations. Where a doc genuinely needs the borrowed word to explain the
# borrowing ("microtheories are contexts", to a reader arriving from Cyc), the
# allowlist takes the token, the same escape hatch every other check here has.
#
# Assembled from halves for the reason _BANNED_REPO is: a checker that spelt
# the words it bans would be the tree's only occurrence of them.
BORROWED = {
    "micro" + "theory": "context",
    "micro" + "theories": "contexts",
    "na" + "rt": "reified NAT",
    "na" + "ut": "structural NAT",
}
BORROWED_RE = re.compile(r"\b(" + "|".join(BORROWED) + r")\b", re.I)
# These two STATE this rule, so they spell the words in order to ban them —
# the same bind E7 is in, and the same fix. Exempting the files is the only
# defensible option: the allowlist matches a TOKEN, so excusing the borrowed word
# in them would disarm the check in every other file too.
E11_STATES_THE_RULE = {"CONTRIBUTING.md", ".claude/rules/conventions.md"}


def kb_text_files():
    """The shipped ontology, `resources/kb/**.txt`.

    Data rather than code, but the `comment` strings in it are vaelii's own
    prose about vaelii's own vocabulary, so the naming rules bind it. The rest
    of `resources/` is vendored (`public/htmx.min.js`) and is not read.
    """
    for dirpath, _, names in os.walk(os.path.join(RESOURCES, "kb")):
        for n in sorted(names):
            if n.endswith(".txt"):
                yield os.path.join(dirpath, n)


for path in itertools.chain(repo_text_files(), extra_md_files(),
                            kb_text_files()):
    if os.path.abspath(path) == SELF or not os.path.exists(path):
        continue
    rel = os.path.relpath(path, ROOT)
    if rel in E11_STATES_THE_RULE:
        continue
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = BORROWED_RE.search(line)
        if m:
            word = m.group(0)
            ours = BORROWED[word.lower()]
            flag("E11", path, word,
                 f"{rel}:{i} `{word}` is another system's word for what this "
                 f"engine calls a {ours}")

# ── E12: every doc opens with the three orientation bullets ─────────────────
# A reader arriving from the map, and a model routing on as little context as it
# can get away with, both decide from the same three lines: what the page covers,
# which neighbour owns the thing it is confused with, and what vocabulary to have
# first.  Their value is entirely in being universal — a reader who has to check
# whether this page happens to have them is back to reading the page.  So the
# convention is checked rather than trusted, the way the prose rules are.
ORIENTATION = ("- **Covers:**", "- **Not here:**", "- **Assumes:**")
# The map does not orient itself, and dependencies.md is generated output.
ORIENTATION_EXEMPT = {"docs/README.md", "docs/dependencies.md"}

for doc in md_files():
    rel = os.path.relpath(doc, ROOT)
    if not rel.startswith("docs" + os.sep) or rel in ORIENTATION_EXEMPT:
        continue
    lines = open(doc, errors="replace").read().splitlines()
    # The block sits between the title and the first section heading. A bullet
    # wraps across lines, so count the ones that START one rather than the
    # non-blank lines under the title.
    head = itertools.takewhile(lambda ln: not ln.startswith("## "), lines[1:])
    opens = [ln for ln in head if ln.startswith("- **")][:3]
    missing = [want for want, got in zip(ORIENTATION, opens + ["", "", ""])
               if not got.startswith(want)]
    if missing:
        flag("E12", doc, rel,
             f"{rel} does not open with {', '.join(m.strip('- *:') for m in missing)}"
             f" — every doc under docs/ carries Covers / Not here / Assumes under"
             f" its title, so a reader can route without reading the page")

# ── E13: every s-expression example is a whole s-expression ────────────────
# A truncated example is the one documentation error a reader cannot route
# around. Prose that has drifted still says something, and a dead link announces
# itself; a snippet missing its last paren looks exactly like a snippet, and the
# reader who pastes it gets an error about their own REPL rather than about the
# page. Nothing else here reads inside a fence for shape — E1 looks for a record
# definition and finds nothing to say about the other hundred-odd blocks.
#
# `clojure` and `edn` only: both are s-expression languages, so balance is a real
# property of them. A `sh` fence is not, and asking would be a category error.
#
# Deliberate fragments would be the one hard case, and there are none: every
# block in the tree balances today, so the check needs no allowlist and a failure
# means a genuinely broken example. Should a page ever want an open-ended
# snippet, `…` inside a complete form says the same thing and stays pasteable.
SEXP_FENCES = ("clojure", "edn")

for doc in itertools.chain(md_files(), extra_md_files()):
    rel = os.path.relpath(doc, ROOT)
    for lang, start, body in fenced_blocks(doc):
        if lang not in SEXP_FENCES or not body.strip():
            continue
        note = sexp_imbalance(body)
        if note:
            flag("E13", doc, f"{rel}:{start}",
                 f"the {lang} block at {rel}:{start} does not parse — {note}."
                 f" A reader pastes these; one that cannot be pasted is worse than"
                 f" no example, because the error it raises is about them")

# ── E14: every Clojure source opens with the licence header ────────────────
# The engine is SSPL-1.0 and the adapter siblings are Apache-2.0, on purpose —
# the split is between an engine and the things that plug into it. What makes a
# split like that hold is that every file says which side it is on, in a form a
# scanner reads: a file with no identifier inherits its licence from whatever the
# reader assumes, and a file carrying the *sibling's* identifier says the engine
# is Apache. Neither is visible by reading the code.
#
# Both lines and in this order, because that is what all 382 files do today and a
# convention with one exception is one nobody can check. The identifier is pinned
# rather than merely required: `SSPL-1.0` is the claim, and an Apache header here
# would be a licensing defect that a presence check waves through.
LICENCE_HEADER = ("SPDX-License-Identifier: SSPL-1.0",
                  "Copyright © 2026 Vaelii LLC and the Vaelii contributors.")


def licensed_clj_files():
    for sub in ("src", "test", "bench"):
        for dirpath, _, names in os.walk(os.path.join(ROOT, sub)):
            for n in sorted(names):
                if n.endswith(".clj"):
                    yield os.path.join(dirpath, n)


for path in licensed_clj_files():
    rel = os.path.relpath(path, ROOT)
    with open(path, errors="replace") as fh:
        head = [next(fh, "").strip(), next(fh, "").strip()]
    for want, got in zip(LICENCE_HEADER, head):
        if got != ";; " + want:
            flag("E14", path, rel,
                 f"{rel} does not open with the licence header — line "
                 f"{head.index(got) + 1} is {got!r}, expected ';; {want}'. Every"
                 f" .clj under src/, test/ and bench/ carries both lines, in that"
                 f" order; the engine is SSPL-1.0 and the sibling adapters are"
                 f" Apache-2.0, so a file that does not say which it is takes"
                 f" whichever the reader assumed")
            break

# ── E15: a Breaking entry says what it breaks ──────────────────────────────
# `scripts/check-breaking-siblings.sh` greps the sibling checkouts for the
# backticked tokens on an entry's `*Breaks:*` line. An entry without that line
# contributes no tokens, so the sweep runs over it and reports nothing — which
# reads exactly like a sweep that found nothing. The failure is on the record:
# 0.5.0 renamed an `open-kb` option, broke vaelii-foreign's test scaffolding and
# a downstream harness's benchmark cells, and both were found by hand afterwards.
#
# **The unreleased section only**, and that is the whole scoping decision. The
# convention is new: 0.4.0 has thirteen Breaking entries carrying no `*Breaks:*`
# line, 0.3.0 eight, 0.2.0 eight. Those shipped, and rewriting a released
# changelog to satisfy a rule invented after it is archaeology. The first `## `
# section is the one being written, so the check moves forward on its own at
# each release cut with nothing to remember.
#
# Both spellings of the class count, because the changelog uses both on purpose
# and check-breaking-siblings.sh reads both: a `**Breaking: …**` title and a
# `*Class:* Breaking` line say the same thing.
BREAKING_ENTRY = re.compile(r"\*\*Breaking:|\*Class:\*\s*\**Breaking")

changelog = os.path.join(ROOT, "CHANGELOG.md")
if os.path.exists(changelog):
    sections = re.split(r"^## ", open(changelog, errors="replace").read(), flags=re.M)
    if len(sections) > 1:
        unreleased = sections[1]
        version = unreleased.split("\n", 1)[0].strip()
        for entry in re.split(r"\n(?=- \*\*)", unreleased)[1:]:
            if not BREAKING_ENTRY.search(entry) or "*Breaks:*" in entry:
                continue
            title = re.sub(r"\s+", " ", entry.split("**")[1] if "**" in entry else entry)
            flag("E15", changelog, f"CHANGELOG.md:{title[:40]}",
                 f"CHANGELOG {version}: the Breaking entry \"{title[:60]}\" carries"
                 f" no *Breaks:* line. scripts/check-breaking-siblings.sh greps the"
                 f" siblings for the backticked tokens on that line, so an entry"
                 f" without one is swept and reports nothing — indistinguishable"
                 f" from a sibling that is fine. One line beside the class, holding"
                 f" each name a caller would have written (CONTRIBUTING §3.8)")

# ── E16: an index read is an entry point's, and an as-stored one is named ───────────
# The `IndexStore` posting sets are storage: they hold a defeated default, a
# conclusion whose support was withdrawn and a spelling an equality retired,
# because all three are revivable and belief lives in the JTMS instead. So every
# raw read has a question attached — stored, or believed — and read straight off
# `vaelii.impl.protocols` there is nothing to say which answer the caller wanted.
# A forgotten belief filter and a deliberate as-stored read are the same three
# characters.
#
# `vaelii.impl.reads` is where the question gets asked, in the name of the read:
# `as-stored-…` / `stored-…` over the index store, `believed-…` over the KB. This
# check is what keeps the entry points the only way in, and the roster below is the one
# place an exception is written down.
#
# The roster is not a list of trusted callers — it is the implementers. A store
# answering the protocol, the retrieval that *builds* the believed reads, and the
# dump that copies the index wholesale are all below the question rather than
# ducking it: there is no belief to filter by at the point they run.
#
# Scoped to the INDEX reads, and `RecordStore` is deliberately outside it: a record
# IS the storage, so fetching one asks nothing about belief. `p/get-sentex` beside a
# entry point here is the ordinary shape and not a second violation.
#
# What this does NOT see, stated so nobody over-trusts it: a read reached through a
# bound var (`(let [f p/lookup] (f idx path))`) is indistinguishable from a value and passes, and so
# does one behind a `resolve`. Closing that would mean banning the value form, which
# is the form the planner's injected cost model is built from. The rule catches the
# read somebody writes without thinking, not the one somebody hides.
E16_READS = ("lookup", "leaf-at", "count-at", "children", "count-children",
             "sentexes-in-context", "count-in-context",
             "sentexes-with-functor", "count-with-functor",
             "sentexes-with-arg", "count-with-arg", "sentexes-with-args",
             "rules-by-antecedent", "rules-by-consequent",
             "rules-with-exception-on", "exception-rules", "exception-rule?",
             "sentexes-with-term", "sentexes-with-terms",
             "terms", "term-count", "index-entries")
E16_OK_FILES = {
    # the entry points themselves
    "src/vaelii/impl/reads.clj",
    # the protocol that declares them
    "src/vaelii/impl/protocols.clj",
    # retrieval: kb and resolution are what a believed read is BUILT from — the
    # matcher, the visibility filters, the equality rewrite and `sentexes-matching`
    "src/vaelii/impl/kb.clj",
    "src/vaelii/impl/resolution.clj",
    # storage backends, answering the protocol or decorating another store
    "src/vaelii/impl/columnar.clj",
    "src/vaelii/impl/kv.clj",
    "src/vaelii/impl/disk/index_snapshot.clj",
    # the portable projection: a dump copies every entry the index holds, by
    # definition without reading one of them
    "src/vaelii/impl/io/snapshot.clj",
}
E16_BACKTICKED = re.compile(r"`[^`]*`")
E16_CALL = re.compile(r"\bp/(" + "|".join(re.escape(r) for r in E16_READS) + r")(?![\w?-])")

for path in clj_files():
    rel = os.path.relpath(path, ROOT)
    if rel in E16_OK_FILES:
        continue
    for i, line in enumerate(open(path, errors="replace"), 1):
        # a backticked `p/lookup` is prose ABOUT the read, which is what a doc
        # reference is for and never a call — E2 already checks those resolve
        m = E16_CALL.search(E16_BACKTICKED.sub("", line))
        if not m:
            continue
        flag("E16", path, f"p/{m.group(1)}",
             f"{rel}:{i} `p/{m.group(1)}` — a raw index read outside "
             f"vaelii.impl.reads. The index answers what is STORED, so the read owes "
             f"an answer to which it wants: `reads/as-stored-…` (and say in the "
             f"docstring what a stored-but-disbelieved answer is for) or "
             f"`reads/believed-…`. If this file implements the protocol rather than "
             f"reading through it, add it to E16_OK_FILES with the reason")

# ── E17: a global taxonomy read is rostered, never reached for ─────────────
# Context scoping is the third invariant: a read sees what its context sees, up the
# genlCx ancestor set. `vaelii.impl.taxonomy` answers each closure both ways — `genls` walks
# the edges visible from a context, `genls-global` walks every active edge whoever
# can see it — and on a KB where no edge is context-restricted the two return the
# same object. That is what makes the global read dangerous rather than merely
# broad: the caller that meant to scope and did not is right on every KB until the
# one it is wrong on.
#
# So a global read is a decision, and this is where the decisions are listed. Each
# roster entry is a `(file, top-level def)` pair, and the reason lives in that
# definition's own docstring — the roster records THAT there is one, the docstring
# says what it is. A caller that cannot state a reason wants the scoped arity.
#
# `vaelii.impl.taxonomy` itself is not on the roster and needs no entry: it calls its
# own readers unqualified, and this rule is about reaching one through the alias.
E17_GLOBAL = ("genls-global", "specs-global", "genl?-global", "context-up-global",
              "genlCx?-global", "genls-global-within", "specs-global-within")
E17_ROSTER = {
    # The public API offers both readings, and its shorter arity IS the global one —
    # `vaelii.core/genls` documents the pair (docs/taxonomy.md).
    ("src/vaelii/core.clj", "genls"),
    ("src/vaelii/core.clj", "specs"),
    ("src/vaelii/core.clj", "genl?"),
    # Assert-time refusals. A refusal is a claim about the KB and not about a vantage:
    # a cycle refused when asked from one context and allowed from another is not a
    # refusal, it is a coin toss.  `disjoint-problems` is the deliberate exception and
    # reads the scoped `genl?` instead — its overlap refusal is meant to agree with the
    # scoped `(genl a b)` query, so an `except` that hides the bridging edge admits the
    # pair (#92, docs/taxonomy.md).  The genl-relatedness guards in `disjoint?` itself
    # stay global; only the assert-time reading moved, which is why disjoint is not here.
    ("src/vaelii/impl/wff.clj", "genl-problems"),
    # `genlCx-problems` is `genl-problems`'s twin on the context side: it refuses a
    # `genlCx` cycle, which is a property of the whole edge set, so it reads
    # `genlCx?-global` for the same reason `genl-problems` reads `genl?-global`.
    ("src/vaelii/impl/wff.clj", "genlCx-problems"),
    # `covering-problems` refuses a part already above the whole because the edge the
    # cover installs would close a `genl` cycle, the refusal `genl-problems` makes, so
    # its cycle arm reads globally too; its disjointness arm stays scoped.
    ("src/vaelii/impl/wff.clj", "covering-problems"),
    ("src/vaelii/impl/wff.clj", "rule-edges"),
    ("src/vaelii/impl/checks.clj", "genls-problem"),
    ("src/vaelii/impl/checks.clj", "covering-genls-problem"),
    ("src/vaelii/impl/checks.clj", "mintable-type?"),
    # The forward join and the trigger keys. A firing is placed in a context the join
    # decides, so the candidate fan cannot be scoped by one — the rule index is keyed
    # on the global closure and the placement narrows afterwards (docs/contexts.md).
    ("src/vaelii/impl/rules.clj", "trigger-keys"),
    ("src/vaelii/impl/chain.clj", "subsumption-links"),
    ("src/vaelii/impl/chain.clj", "permuting-rejoin-rules"),
    ("src/vaelii/impl/chain.clj", "transitive-rejoin-rules"),
    ("src/vaelii/impl/chain.clj", "transitive-source-preds"),
    ("src/vaelii/impl/chain.clj", "walks-its-own-conclusion?"),
    ("src/vaelii/impl/inherit.clj", "moved-in"),
    ("src/vaelii/impl/inherit.clj", "crossings"),
    ("src/vaelii/impl/vantage.clj", "subsumption-support"),
    # Re-check triggers. A trigger must over-approximate in the direction the answer
    # is: a declaration this edge cannot see still qualifies a rule in some context
    # that can, and a missed trigger is a wrong belief where a spare one is a query
    # (`inherit/declared` states the argument in full).
    ("src/vaelii/impl/special.clj", "recheck-declaration"),
    ("src/vaelii/impl/special.clj", "arg-declared-types"),
    ("src/vaelii/impl/special.clj", "recheck-arg-inferred"),
    ("src/vaelii/impl/special.clj", "recheck-on-predicate"),
    ("src/vaelii/impl/special.clj", "rules-watching"),
    ("src/vaelii/impl/special.clj", "recheck-genl-edge"),
    ("src/vaelii/impl/special.clj", "recheck-negated-exceptions"),
    ("src/vaelii/impl/special.clj", "subtree-sentexes"),
    ("src/vaelii/impl/special.clj", "super-reaches-declaration?"),
    ("src/vaelii/impl/special.clj", "negative-subsumption-seeds"),
    ("src/vaelii/impl/special.clj", "subsumption-seeds"),
    ("src/vaelii/impl/special.clj", "roster-antecedent-functors"),
    # Settle's candidate discovery. An over-approximated candidate merely checks and
    # yields nothing, and the arbitration that follows is context-scoped anyway —
    # `instances-below` carries the reasoning and the measurement.
    ("src/vaelii/impl/settle.clj", "reachable-predicates"),
    ("src/vaelii/impl/settle.clj", "exposed-clashes-for-term"),
    ("src/vaelii/impl/settle.clj", "instances-below"),
    ("src/vaelii/impl/settle.clj", "spec-closure"),
    ("src/vaelii/impl/settle.clj", "member-owners"),
    ("src/vaelii/impl/settle.clj", "declaration-reach"),
    ("src/vaelii/impl/settle.clj", "predicate-subtree"),
    ("src/vaelii/impl/settle.clj", "partner-contexts"),
    ("src/vaelii/impl/settle.clj", "any-arity-declared?"),
    # The one that reads BOTH and compares them: `genl-view` is a cheap marker for
    # "every asker inside this sandwich reads the same set".
    ("src/vaelii/impl/settle.clj", "genl-view"),
    # The visibility filter cannot be scoped by the filter it derives — asking
    # `context-up` here would make except evaluation recursive on itself.
    ("src/vaelii/impl/resolution.clj", "visible-exception-index"),
    ("src/vaelii/impl/resolution.clj", "except-hidden-fn"),
    # The per-reader withdrawal reads the same raw ancestor set for the same reason: it
    # takes the except targets and the scoped defeats a reader sees, and the scoped
    # `context-up` is itself filtered by what the except targets hide.
    ("src/vaelii/impl/resolution.clj", "withdrawal*"),
    # The two diagnostics that report that withdrawal read the same raw ancestor set as
    # `withdrawal*`: a scoped read would name no vantage for a handle belief withdraws
    # through the unscoped one, so `belief-status` would answer `:withdrawn? true` with an
    # empty `:scoped-vantages` and `why-not` an empty `:withdrawn-by`.
    # The reader's own ancestor set again, for the same reason: it names the vantages
    # whose verdicts `withdrawal*` applies, and the two must read one relation or a
    # reader would take a verdict the withdrawal does not.
    ("src/vaelii/impl/resolution.clj", "undecided-pairs"),
    ("src/vaelii/impl/resolution.clj", "scoped-vantages"),
    ("src/vaelii/impl/resolution.clj", "scoped-defeats-seen"),
    # A report on the whole taxonomy, which has no vantage to read from.
    ("src/vaelii/impl/quality.clj", "taxonomy-coverage"),
    # The clash reading's candidate fan. A rule pair is decided from a common descendant
    # of the two rules' contexts — a vantage belonging to neither — so fanning from
    # either would drop a pair the context that can see both would find, and the pair
    # itself is decided scoped.
    ("src/vaelii/impl/quality.clj", "clash-partners"),
}
E17_CALL = re.compile(r"\btax/(" + "|".join(re.escape(n) for n in E17_GLOBAL) + r")(?![\w?-])")
E17_DEF = re.compile(r"\(def[\w-]*\s+(?:\^[^\s]+\s+)*([^\s\)]+)")

for path in clj_files():
    rel = os.path.relpath(path, ROOT)
    enclosing = "?"
    for i, line in enumerate(open(path, errors="replace"), 1):
        if line.startswith("(def"):
            m = E17_DEF.match(line)
            enclosing = m.group(1) if m else "?"
        m = E17_CALL.search(E16_BACKTICKED.sub("", line))
        if not m or (rel, enclosing) in E17_ROSTER:
            continue
        flag("E17", path, f"tax/{m.group(1)}",
             f"{rel}:{i} `{enclosing}` calls `tax/{m.group(1)}` — an unscoped taxonomy "
             f"read outside the roster. A read sees what its context sees (README.md, "
             f"context scoping), and on a KB where no edge is context-restricted the "
             f"global and the scoped answer are the same object — so a caller that "
             f"meant to scope and did not is right until it is not. Pass the context "
             f"(`tax/{m.group(1)[:-len('-global')]}`), or add `{enclosing}` to "
             f"E17_ROSTER and say in its docstring why it must not be scoped")

# ── E18: the namespace map accounts for every file under src/ ──────────────
# docs/namespaces.md is the file map, and it makes a countable claim: the glossed
# table covers N of the M namespaces under src/, and the "Not glossed above" block
# names the rest. A map that is one arithmetic sentence away from being wrong is a
# map a reader stops trusting the moment they find the file it forgot — and the
# forgetting is silent, because a new namespace changes nothing that any other check
# reads.
#
# So the two lists are checked against the filesystem instead. Every `.clj` under
# src/ must appear either as a glossed row (in a fence whose header line is
# `src/vaelii/…`, the path relative to that header) or by name in the closing block,
# and a name in either list must still be a file. The count in the prose is checked
# against the same two sets, so it cannot be updated to a number nobody measured.
E18_DOC = os.path.join(ROOT, "docs", "namespaces.md")
E18_COUNT = re.compile(r"The map covers (\d+) of the (\d+) namespaces under `src/`")


def e18_expand(token):
    """`host/llm/{a,b}.clj` -> the names it stands for; anything else, itself."""
    m = re.match(r"^(.*?)\{([^}]*)\}(.*)$", token)
    if not m:
        return [token]
    pre, inner, post = m.groups()
    return [n for part in inner.split(",") for n in e18_expand(pre + part.strip() + post)]


def e18_lists(text):
    """(glossed, by_name): the two rosters docs/namespaces.md holds, as paths under
    src/vaelii/. Brace groups are joined first — the llm and koinii ones wrap."""
    glossed, by_name, header, fenced = set(), set(), None, False
    joined = re.sub(r"\{[^}]*\}", lambda m: re.sub(r"\s+", "", m.group(0)), text)
    for line in joined.split("\n"):
        if FENCE.match(line):
            fenced = not fenced
            header = None
            continue
        if not fenced or not line.strip():
            continue
        if line.strip().endswith("/") and not line.startswith(" "):
            header = line.strip()
            continue
        if header is None:
            for token in re.findall(r"[\w./{},-]*\.clj", line):
                by_name.update(e18_expand(token))
        elif header.startswith("src/vaelii/"):
            m = re.match(r"^\s+([\w./-]+\.clj)\s", line)
            if m:
                glossed.add(header[len("src/vaelii/"):] + m.group(1))
    return glossed, by_name


if os.path.exists(E18_DOC):
    e18_text = open(E18_DOC, errors="replace").read()
    e18_glossed, e18_named = e18_lists(e18_text)
    e18_actual = {os.path.relpath(p, os.path.join(SRC, "vaelii")) for p in clj_files()}
    for ns in sorted(e18_actual - e18_glossed - e18_named):
        flag("E18", E18_DOC, ns,
             f"src/vaelii/{ns} is in neither list in docs/namespaces.md — give it a "
             f"glossed row in the file map, or name it in the \"Not glossed above\" "
             f"block, and move the count in that section's first sentence to match")
    for ns in sorted((e18_glossed | e18_named) - e18_actual):
        flag("E18", E18_DOC, ns,
             f"docs/namespaces.md lists `{ns}`, which is no longer under src/vaelii/ — "
             f"drop the row and move the count in \"Not glossed above\" to match")
    e18_m = E18_COUNT.search(e18_text)
    if not e18_m:
        flag("E18", E18_DOC, "namespaces-count",
             "docs/namespaces.md no longer states \"The map covers N of the M "
             "namespaces under `src/`\" — that sentence is what this check counts "
             "against, so keep its wording")
    elif (int(e18_m.group(1)), int(e18_m.group(2))) != (len(e18_glossed), len(e18_actual)):
        flag("E18", E18_DOC, "namespaces-count",
             f"docs/namespaces.md says the map covers {e18_m.group(1)} of "
             f"{e18_m.group(2)} namespaces under src/; it covers "
             f"{len(e18_glossed)} of {len(e18_actual)}")

for e in errors:
    print(e)
for w in warnings:
    print("warn:", w)

# Dead allowlist entries: tokens that suppressed nothing this run, so the doc
# reference they excused is gone or the checker stopped flagging it. Advisory
# only (exit unaffected) — prune them from the allowlist.
dead = sorted(allow - allow_used)
if dead:
    print(f"\nadvisory: {len(dead)} dead allowlist entr"
          f"{'y' if len(dead) == 1 else 'ies'} (matched nothing this run) — "
          f"prune from scripts/check-doc-drift-allowlist.txt:")
    for tok in dead:
        print(f"  - {tok}")

# scripts/lint.sh greps the verdict for `N errors, M warnings across K docs`, so
# that phrase stays whole and on one line; the extras get a line above it.
print(f"\nThe link, archaeology and s-expression checks also read "
      f"{sum(1 for _ in extra_md_files())} files beside docs/.")
print(f"{len(errors)} errors, {len(warnings)} warnings "
      f"across {sum(1 for _ in md_files())} docs.")
sys.exit(1 if errors else 0)
