#!/usr/bin/env python3
"""The `lein perf` checks and `lein perf-ab` probes a change owes.

    python3 scripts/perf-owed.py [--base REV] [--head REV] --kind checks|probes
    python3 scripts/perf-owed.py [--base REV] [--head REV] --why

The change is the diff from the base to the head revision, or to the working tree with no
--head. The base defaults to the merge base with the upstream branch, else with origin/main. `--kind` prints one line: `all`, a
comma-separated list for `--only`, or nothing when the change owes none. `--why` prints each
owed check and probe beside the changed code that selects it.

Engine code (src/) is read through the reach map `lein perf --reach` writes to
`.git/vaelii-perf/reach.tsv` (bench/vaelii/bench/reach.clj): per key, the checks and probes
that executed it. A key is `ns/var` for a fn and the fns nested in it, `ns/Type` for a
record or type, and `ns` for an anonymous top-level fn. A top-level form whose tokens match
one of the other revision's, comments, layout and docstring aside, selects nothing: it moved,
or its code did not change. A def or defn the change adds, whose name no changed Clojure
file names at the base, and one it deletes, whose name none names at the head, select
nothing: only changed code reaches it, and that code selects. Any other changed top-level
form selects:

  - a defn the map holds: per changed token, the targets that executed the line entry of
    the innermost list around it that marks its own evaluation (a call, an `if`-family
    macro, `case`, a loop macro, `fn` or `reify`) and holds an entry in the line map (below),
    else the targets that executed the defn;
  - a def, defrecord or deftype the map holds: the targets that executed it;
  - a defn the map lacks that the file held at the map's revision: none, since no target
    executes it.  One added since that revision, or one a top-level form running at load
    names (a def's initializer; a `declare` runs nothing), selects every target reaching its
    namespace;
  - a defmethod, extend-protocol or extend-type: the targets that executed an anonymous fn
    of its namespace;
  - a defmacro or definline: every target, since its expansion lands in other namespaces;
  - an ns form: none, since a require changes nothing until a changed form calls it;
  - any other form (a def holding data): every target reaching its namespace.

The two harnesses, bench/vaelii/bench/perf.clj and ab.clj, are read through a symbol graph
over their own top-level forms, since a delay one check forces holds state the next check
reads without executing it. A changed form selects the checks whose entry in `checks`
reaches it, and the probes in `probes` that reach it; a form no entry reaches is harness
code and selects every target of its file. Shipped KB content (resources/kb/upper and
middle) selects the targets that reach a form calling a shipped-KB loader, and with no map so
does a change to a loader file (STARTER_FILES).

The line map, `reach-lines.tsv` beside it, holds per line of src/ holding a line entry the
targets that executed that entry; a census at a dirty tree writes none that is read. A line
of the base maps to the map's revision through the diff between the two, and a line the
diff changed has no entry.

A target the map does not list, and one whose census run threw, is owed by every engine or
content change. With no map, and for a file whose namespace the map holds no key for (one
added since the map's revision, or one no target executed then), the per-file rules below
(ENGINE_RE, GROUPS, STARTER_FILES) stand in for the map, and a check is named by its group.

Exit: 0, or 2 on a bad argument.
"""

import argparse
import bisect
import difflib
import os
import re
import subprocess
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PERF = "bench/vaelii/bench/perf.clj"
AB = "bench/vaelii/bench/ab.clj"
ALL = "*all*"
# The top-level forms whose body runs at a call, not at load.
CALL_HEADS = {"defn", "defn-", "defmacro", "definline", "defmulti", "defmethod", "defrecord",
              "deftype", "defprotocol", "definterface", "extend-protocol", "extend-type",
              "comment", "ns", "declare"}
# The heads whose form names a var only changed code can reach when the change adds or
# deletes it.
VAR_HEADS = {"def", "defonce", "defn", "defn-"}
# The heads whose form takes a docstring after its name, when a value or body follows it.
DOC_HEADS = {"def", "defonce", "defn", "defn-", "defmacro", "definline", "defmulti"}
CONTENT_RE = re.compile(r"^resources/kb/(upper|middle)/")
LOADER_RE = re.compile(r"\b(core-context|seed|starter)/[a-z]")

# The per-file rules for a tree with no reach map. A change to the API or the engine owes
# every probe. It owes the `groups` of perf.clj that a GROUPS row names for its file, and
# every check where no row names it. A probe times a whole operation through the API (an
# assert, a load, a recover), so any engine change can add a cost to it.
ENGINE_RE = re.compile(r"^src/vaelii/(core\.clj$|impl/)")
GROUPS = [
    (r"(kv|reads)\.clj", ["all"]),
    (r"(dense_kv|dense_roots|columnar|reindex|tokens|literal_cache)\.clj|(overlay|disk|types)/",
     ["index"]),
    (r"taxonomy\.clj", ["taxonomy", "membership", "inherit", "placement", "clashes"]),
    (r"except\.clj", ["exceptions", "placement"]),
    (r"inherit\.clj", ["inherit", "clashes"]),
    (r"(clashes|discovery)\.clj", ["clashes"]),
    (r"(decide|journal)\.clj|decide/", ["placement", "argtypes", "membership", "tuples", "clashes"]),
    (r"(recovery|reasoning_image)\.clj", ["recover"]),
    (r"(qcn|qcn_kb|space|stp|sign|quality|context_nat|plan)\.clj|asp/", ["solvers"]),
    (r"(nat|nat_maintenance|feed)\.clj", ["chaining"]),
]
STARTER_FILES = re.compile(r"^src/vaelii/(starter|host/(starter|core_context|seed))\.clj$")

# The heads whose list emits no line entry of its own: special forms and the macros
# expanding to one. A list whose head is another macro the census found loaded is read the
# same way, unless ENTRY_MACROS names it: each of those expands to a call or an `if` on its
# own line.
NO_ENTRY = {"do", "let*", "loop*", "letfn*", "try", "catch", "finally", "throw", "quote", "var",
            "new", "set!", "recur", "def", "monitor-enter", "monitor-exit", "case*", "deftype*",
            "reify*", "import*"}
ENTRY_MACROS = {"when", "when-not", "when-let", "when-some", "when-first", "if-let", "if-some",
                "if-not", "cond", "condp", "case", "doseq", "dotimes", "while", "for", "fn",
                "delay", "lazy-seq", "reify"}
# The heads whose body forms run in order once the list runs (from the index given), and
# the heads whose binding vector's initial values run before the body.
SEQ_HEADS = {"do": 1, "let": 2, "let*": 2, "loop": 2, "loop*": 2, "when": 2, "when-not": 2,
             "when-let": 2, "when-some": 2, "when-first": 2}
BINDING_HEADS = {"let", "let*", "loop", "loop*"}
# The heads whose child lists are method or field specs, not calls.
SPEC_HEADS = {"reify", "proxy", "deftype", "defrecord", "extend-type", "extend-protocol",
              "extend", "definterface", "defprotocol"}
TOKEN_RE = re.compile(r"""
    (?P<ws>[\s,]+)
  | (?P<comment>;[^\n]*|\#![^\n]*)
  | (?P<str>\#?"(?:\\.|[^"\\])*")
  | (?P<char>\\(?:newline|space|tab|formfeed|backspace|return|u[0-9a-fA-F]{4}|o[0-7]{1,3}|.))
  | (?P<open>\#\(|\#\{|\#\?@?\(|\#::?[^\s,;"()\[\]{}]*\{|[(\[{])
  | (?P<close>[)\]}])
  | (?P<prefix>\#_|\#\^|\^|\#'|'|`|~@|~|@)
  | (?P<atom>\#\#?[^\s,;"()\[\]{}\\^`~@]+|[^\s,;"()\[\]{}\\^`~@'\#][^\s,;"()\[\]{}\\^`~@]*)
""", re.X)
FORM_RE = re.compile(r"^\(([^\s()\[\]{}]+)\s*((?:\^\{[^}]*\}\s+|\^\S+\s+)*)([^\s()\[\]{}\"]+)?")
HUNK_RE = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")
SYMBOL_RE = re.compile(r"[A-Za-z*+!?<>=_-][\w*+!?<>=.-]*")
NOISE_RE = re.compile(r'"(?:\\.|[^"\\])*"|;[^\n]*|(?<![\w*+!?<>=.-]):[\w*+!?<>=./:-]+')


def symbols(code):
    """Returns the symbols of Clojure `code`, its strings, comments and keywords removed."""
    return set(SYMBOL_RE.findall(NOISE_RE.sub(" ", code)))


def git(*args):
    """Returns git's stdout for `args` run in the repository root, or None on failure."""
    r = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def read(path):
    """Returns the working tree's text of `path`, or the empty string when it is absent."""
    full = os.path.join(ROOT, path)
    if not os.path.exists(full):
        return ""
    with open(full, encoding="utf-8") as f:
        return f.read()


def forms(text):
    """Returns `(start, end, head, name)` per top-level form of Clojure source `text`: a
    form starts at a line opening with `(` and ends before the next one. Lines are 1-based."""
    lines = text.split("\n")
    starts = [i for i, l in enumerate(lines, 1) if l.startswith("(")]
    out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] - 1 if k + 1 < len(starts) else len(lines)
        m = FORM_RE.match(lines[s - 1])
        out.append((s, e, m.group(1) if m else None, m.group(3) if m else None))
    return out


def changed_lines(diff):
    """Returns `(old, new)`, the changed line numbers on each side of a `-U0` diff."""
    old, new = set(), set()
    for line in diff.split("\n"):
        m = HUNK_RE.match(line)
        if m:
            a, c, b, d = (int(x) if x is not None else 1 for x in m.groups())
            old.update(range(a, a + c))
            new.update(range(b, b + d))
    return old, new


def touched(text, lines):
    """Returns the forms of `text` holding any non-blank line of `lines`."""
    ls = text.split("\n")
    lines = [n for n in lines if 0 < n <= len(ls) and ls[n - 1].strip()]
    return [f for f in forms(text) if any(f[0] <= n <= f[1] for n in lines)]


def ns_of(path):
    """Returns the namespace a source path holds: src/vaelii/impl/dense_kv.clj names
    vaelii.impl.dense-kv."""
    stem = re.sub(r"^(src|bench|test)/|\.cljc?$", "", path)
    return stem.replace("/", ".").replace("_", "-")


class Node:
    """A list, vector, map or set of a Tree: its open token, its line, and its children,
    each a Node or a token index. `data` marks a quoted list, a `case` test and the forms
    inside them; `spec` a method spec of SPEC_HEADS; `skip` the children a `^` or `#_`
    takes."""

    def __init__(self, kind, tok, line, parent):
        self.kind, self.tok, self.line, self.parent = kind, tok, line, parent
        self.children, self.skip = [], set()
        self.data = self.spec = False
        self.first = None

    def items(self, tree):
        """Returns the children `^` and `#_` do not take, a token as its text."""
        return [c if isinstance(c, Node) else tree.toks[c][1]
                for k, c in enumerate(self.children) if k not in self.skip]

    def head(self, tree):
        """Returns the first child's text when it is a token, else the child or None."""
        return tree.toks[self.first][1] if isinstance(self.first, int) else self.first


class Tree:
    """The tokens of Clojure source `text`, each `(kind, text, first line, last line)`, and
    the nesting of its lists, vectors, maps and sets under `root`."""

    def __init__(self, text):
        self.toks, line = [], 1
        for m in TOKEN_RE.finditer(text):
            k, t = m.lastgroup, m.group()
            if k not in ("ws", "comment"):
                self.toks.append((k, t, line, line + t.count("\n")))
            line += t.count("\n")
        self.root = Node(None, -1, 0, None)
        self.owner = [self.root] * len(self.toks)   # token -> the node holding it
        self.node = {}                               # open or close token -> its node
        stack, pend = [self.root], []
        for i, (k, t, ln, _) in enumerate(self.toks):
            top = stack[-1]
            if k == "close":
                if top is not self.root:
                    self.node[i] = top
                    stack.pop()
                continue
            self.owner[i] = top
            if k == "prefix":
                pend.append(t)
                continue
            at, head = len(top.children), top.head(self)
            if set(pend) & {"^", "#^", "#_"}:
                top.skip.add(at)
            elif top.first is None:
                top.first = i
            data = top.data or bool(set(pend) & {"'", "`", "#_"}) or head == "quote"
            if top.data and set(pend) & {"~", "~@"}:
                data = False
            pend = []
            if k != "open":
                top.children.append(i)
                continue
            n = Node(t[-1] if t[-1] != "{" else t, i, ln, top)
            if top.first == i:
                top.first = n
            n.data = data or (head == "case" and at >= 2 and at % 2 == 0)
            n.spec = head in SPEC_HEADS
            top.children.append(n)
            self.node[i] = n
            stack.append(n)

    def span(self, a, b):
        """Returns the indexes of the tokens touching lines a to b - 1."""
        return [i for i, (_, _, s, e) in enumerate(self.toks) if s < b and e >= a]

    def after(self, line):
        """Returns the index of the first token starting past `line`."""
        return next((i for i, t in enumerate(self.toks) if t[2] > line), len(self.toks))

    def start(self, i, gap):
        """Returns the node a change at token `i` lies directly in: for a token, the node
        holding it, or the node around a bracket's node; for a gap before token `i`, the
        node the inserted text lands in."""
        if i >= len(self.toks):
            return self.root
        n = self.node.get(i)
        if n is None:
            return self.owner[i]
        if gap and self.toks[i][0] == "close":
            return n
        return n.parent

    def top(self, n):
        """Returns the top-level form holding node `n`, or None for the root."""
        while n is not None and n.parent is not self.root:
            n = n.parent
        return n


def top_texts(text):
    """Returns `{line: tokens}` per top-level list of Clojure source `text`, the texts of its
    tokens with a DOC_HEADS docstring left out: a form moved, or changed only in its comments,
    layout or docstring, holds the same tokens at both revisions."""
    t = Tree(text)
    closes = {id(n): i for i, n in t.node.items() if i != n.tok}
    out = {}
    for k, n in enumerate(t.root.children):
        if not isinstance(n, Node) or k in t.root.skip or id(n) not in closes:
            continue
        toks = list(range(n.tok, closes[id(n)] + 1))
        kids = [c for j, c in enumerate(n.children) if j not in n.skip]
        if n.head(t) in DOC_HEADS and len(kids) > 3 and isinstance(kids[2], int) \
                and t.toks[kids[2]][0] == "str":
            toks.remove(kids[2])
        out[n.line] = tuple(t.toks[i][1] for i in toks)
    return out


def emits_entry(n, tree, macros):
    """Whether evaluating node `n` executes a line entry on its first line: a call, an
    interop call, a keyword lookup, or a head ENTRY_MACROS names."""
    if n.kind != "(" or n.data or n.spec:
        return False
    h = n.head(tree)
    if isinstance(h, Node):
        return h.kind == "("
    if not h or h[0] in "0123456789\"\\#^'":
        return False
    if h.startswith(":"):
        return True
    base = h.rsplit("/", 1)[-1] if "/" in h[1:] else h
    if base in NO_ENTRY or (h.endswith(".") and h != "."):
        return False
    return base in ENTRY_MACROS or base not in macros


def before(tree, n, pos):
    """Returns the nodes node `n` evaluates, in order, on every path to its child at `pos`:
    the earlier body forms of a SEQ_HEADS list and the initial values of a BINDING_HEADS
    binding vector."""
    kids = [c if k not in n.skip else None for k, c in enumerate(n.children)]
    head, up = n.head(tree), n.parent.head(tree) if n.parent else None
    if n.kind == "[" and up in BINDING_HEADS and n.parent.children[1:2] == [n]:
        out = kids[1:pos:2]
    elif head in SEQ_HEADS and pos > SEQ_HEADS[head]:
        out = kids[SEQ_HEADS[head]:pos]
        if head in BINDING_HEADS and isinstance(kids[1], Node):
            out = before(tree, kids[1], len(kids[1].children)) + out
    else:
        out = []
    return [c for c in out if isinstance(c, Node)]


def entry_at(tree, n, i, top, hit, macros):
    """Returns `(node, targets)` for a change at token `i` in node `n` of Tree `tree`: walking
    out to `top`, per node the nearest earlier form `before` names, then the node itself,
    the first that `emits_entry` and whose line `hit` maps to targets. `(None, None)` when
    none does."""
    pos = sum(1 for c in n.children if (c.tok if isinstance(c, Node) else c) < i)
    while n is not None and n is not top and n is not tree.root:
        for c in before(tree, n, pos)[::-1] + [n]:
            ts = hit(c.line) if emits_entry(c, tree, macros) else None
            if ts is not None:
                return c, ts
        pos, n = n.parent.children.index(n), n.parent
    return None, None


def line_map(diff):
    """Returns a function from a line of a `-U0` diff's new side to its old-side line, None
    for a line the diff changed."""
    hunks = [tuple(int(x) if x is not None else 1 for x in m.groups())
             for m in map(HUNK_RE.match, diff.split("\n")) if m]

    def old_line(n):
        off = 0
        for a, c, b, d in hunks:
            if d and b <= n < b + d:
                return None
            if (d and b + d <= n) or (not d and b < n):
                off += c - d
        return n + off
    return old_line


def paired_closes(tree, changed):
    """Returns the close tokens of `changed` that close a list whose open token is in
    `changed` too. A token diff matches a close bracket to any of a run of them, so per run
    of adjacent closes, as many changed closes as the run closes lists with a changed open."""
    out, runs = set(), defaultdict(list)
    for i in sorted(changed):
        if tree.toks[i][0] == "close":
            k = i
            while k > 0 and tree.toks[k - 1][0] == "close":
                k -= 1
            runs[k].append(i)
    for k, closes in runs.items():
        e = k
        while e < len(tree.toks) and tree.toks[e][0] == "close":
            e += 1
        n = sum(1 for j in range(k, e) if j in tree.node and tree.node[j].tok in changed)
        out.update(closes[:n])
    return out


def sites(old, new, diff):
    """Returns `(i, gap)` per change of a `-U0` diff from Tree `old` to Tree `new`: `i` an
    old token index, `gap` true for text inserted before it. Tokens compare by text, so a
    change of layout or comments has no site, and a close of a list whose open changed has
    none of its own (`paired_closes`)."""
    out, gone, added = [], set(), set()
    for m in map(HUNK_RE.match, diff.split("\n")):
        if not m:
            continue
        a, c, b, d = (int(x) if x is not None else 1 for x in m.groups())
        oi = old.span(a, a + c) if c else []
        ni = new.span(b, b + d) if d else []
        base = oi[0] if oi else old.after(a)
        if not c and base > 0 and old.toks[base - 1][3] > a:
            out.append((base - 1, False, ()))   # lines inserted inside a multi-line string
            continue
        ops = difflib.SequenceMatcher(None, [old.toks[i][1] for i in oi],
                                      [new.toks[j][1] for j in ni], autojunk=False)
        for tag, i1, i2, j1, j2 in ops.get_opcodes():
            if tag == "equal":
                continue
            gone.update(oi[i1:i2])
            added.update(ni[j1:j2])
            if tag == "insert":
                out.append((oi[i1] if i1 < len(oi) else (oi[-1] + 1 if oi else base), True,
                            ni[j1:j2]))
            else:
                out.extend((oi[i], False, ()) for i in range(i1, i2))
    old_pairs, new_pairs = paired_closes(old, gone), paired_closes(new, added)
    return [(i, gap) for i, gap, ins in out
            if not (i in old_pairs and not gap) and not (ins and set(ins) <= new_pairs)]


class Lines:
    """The line map: per file of src/, the lines holding a line entry and the targets that
    executed each, read when first asked for; and the macros the census found loaded."""

    def __init__(self, path, targets):
        self.header, self.macros, self.sets, self.files = None, set(), {}, {}
        self.targets = targets
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.rstrip("\n")
                if line.startswith("# reach "):
                    self.header = line
                elif line.startswith("# macros"):
                    self.macros = set(line.split()[2:])
                elif "\t" in line:
                    k, v = line.split("\t", 1)
                    (self.files if k.startswith("src/") else self.sets)[k] = v

    def at(self, path, n):
        """Returns the targets that executed the line entry on line `n` of `path`, or None
        when no line entry sits on it."""
        row = self.files.get(path)
        if isinstance(row, str):
            row = self.files[path] = dict(x.split(":") for x in row.split())
        sid = (row or {}).get(str(n))
        if sid is None:
            return None
        if isinstance(self.sets[sid], str):
            self.sets[sid] = {self.targets[int(i)] for i in self.sets[sid].split()}
        return self.sets[sid]


class Harness:
    """The symbol graph over perf.clj's or ab.clj's top-level forms: which entries of
    `checks` (perf.clj) or `probes` (ab.clj) reach each form."""

    def __init__(self, text, probes):
        fs = forms(text)
        lines = text.split("\n")
        listed = "probes" if probes else "checks"
        whole = {f[3]: "\n".join(lines[f[0] - 1:f[1]]) for f in fs if f[3] and f[2] != "ns"}
        body = {n: b for n, b in whole.items() if n != listed}
        edges = {n: symbols(b) & body.keys() for n, b in body.items()}
        self.roots = {}         # target -> the form names its entry mentions
        self.entry_at = {}      # line -> target, for the lines of `checks` or `probes`
        for s, e, _, name in fs:
            if name != listed:
                continue
            if probes:
                for i in range(s, e + 1):
                    for n in re.findall(r"#'([^\s\]]+)", lines[i - 1]):
                        self.roots["ab:" + n] = {n}
                        self.entry_at[i] = "ab:" + n
                continue
            entries = [(i, m.group(1)) for i in range(s, e + 1)
                       for m in [re.search(r"\{:name\s+:(\S+)", lines[i - 1])] if m]
            for k, (i, n) in enumerate(entries):
                j = entries[k + 1][0] if k + 1 < len(entries) else e + 1
                self.roots[n] = symbols("\n".join(lines[i - 1:j - 1])) & body.keys()
            # a comment or blank line belongs to the entry after it, any other to the one
            # it sits in
            at = [i for i, _ in entries]
            for i in range(s, e + 1) if entries else ():
                text = lines[i - 1].strip()
                k = bisect.bisect_left(at, i) if not text or text.startswith(";") \
                    else bisect.bisect_right(at, i) - 1
                self.entry_at[i] = entries[min(max(k, 0), len(entries) - 1)][1]
        self.reach = defaultdict(set)   # form name -> targets reaching it
        for t, roots in self.roots.items():
            seen, todo = set(), list(roots)
            while todo:
                n = todo.pop()
                if n not in seen:
                    seen.add(n)
                    todo.extend(edges.get(n, ()))
            for n in seen:
                self.reach[n].add(t)
        self.content = set().union(*[self.reach[n] for n, b in body.items() if LOADER_RE.search(b)])
        self.listed = listed
        self.names = set(whole)

    def select(self, form, lines, prev=None):
        """Returns `(targets, why)` for a changed form of the harness.  A form of the base
        revision passes `prev`, the base's Harness: its entry lines map through `prev`, and
        a form the file no longer holds selects nothing, since its callers changed too."""
        s, e, head, name = form
        if head == "comment" or (prev and name != self.listed and name not in self.names):
            return set(), None
        if name == self.listed:
            at = (prev or self).entry_at
            return {at[n] for n in lines if s <= n <= e and n in at} & self.roots.keys(), "its entry"
        if name in self.reach:
            return set(self.reach[name]), name
        return set(self.roots), f"{name or head}, harness code"


class Reach:
    """The reach map: per key, the targets that executed it."""

    def __init__(self, path):
        self.rev, self.dirty, self.targets, self.failed = None, "0", [], []
        self.keys = {}
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.rstrip("\n")
                if line.startswith("# reach "):
                    self.rev, self.dirty = (line.split() + ["0"])[2:4]
                elif line.startswith("# targets"):
                    self.targets = line.split()[2:]
                elif line.startswith("# failed"):
                    self.failed = line.split()[2:]
                elif "\t" in line:
                    k, ix = line.split("\t", 1)
                    self.keys[k] = {self.targets[int(i)] for i in ix.split()}
        self.by_ns = defaultdict(set)
        for k, ts in self.keys.items():
            self.by_ns[k.split("/", 1)[0]] |= ts
        self.namespaces = frozenset(self.by_ns)
        lines = re.sub(r"\.tsv$", "-lines.tsv", path)
        self.lines = Lines(lines, self.targets) if os.path.exists(lines) else None
        if self.lines and (self.dirty != "0" or self.lines.header != f"# reach {self.rev} 0"):
            self.lines = None

    def select(self, ns, form, held, at_load):
        """Returns `(targets, why)` for a changed engine form.  `held` is whether the file
        held a defn of that name at the map's revision, and `at_load` whether a top-level
        form of the file that runs at load names it."""
        _, _, head, name = form
        key = f"{ns}/{name}"
        if head in ("defmacro", "definline"):
            return {ALL}, f"{key} is a {head}"
        if head in ("comment", "ns"):
            return set(), None
        if head in ("defmethod", "extend-protocol", "extend-type"):
            return set(self.keys.get(ns, ())), f"{ns}, {head} {name}"
        if at_load:
            return set(self.by_ns[ns]), f"{key}, named at load"
        if name and key in self.keys:
            return set(self.keys[key]), key
        if head in ("defn", "defn-") and held:
            return set(), key
        return set(self.by_ns[ns]), f"{ns}, {head} {name or ''}".rstrip()


def static_select(path):
    """Returns `(checks, probes)` the per-file rules owe for one changed path."""
    if ENGINE_RE.search(path):
        rest = path.removeprefix("src/vaelii/impl/")
        return next((set(gs) for pat, gs in GROUPS if re.match(pat, rest)), {"all"}), {"all"}
    return set(), set()


def by_line(p, reach, old_text, new_text, diff, to_map, at_load):
    """Returns the changed forms of src/ file `p` as `owed` reads them, `(form, lines, old)`
    per form: an old form a changed token lies in, and a new form unless it is a defn the old
    text holds too. The form of a defn the map holds carries a fifth item, a `(targets,
    why)` per change off the line map; `to_map` takes a line of `old_text` to the map's
    revision."""
    old_t, new_t = Tree(old_text), Tree(new_text)
    ns, macros = ns_of(p), reach.lines.macros
    tops = defaultdict(list)
    for i, gap in sites(old_t, new_t, diff):
        n = old_t.start(i, gap)
        tops[old_t.top(n if gap or i >= len(old_t.toks) else old_t.node.get(i, old_t.owner[i]))] \
            .append((n, i, gap))
    tops.pop(None, None)
    out = []
    for top, ss in tops.items():
        if old_t.root.children.index(top) in old_t.root.skip:
            continue    # a `#_` form
        kids = [c for k, c in enumerate(top.children) if k not in top.skip]
        head, name = (top.items(old_t) + [None, None])[:2]
        name = name if isinstance(name, str) else None
        form = (top.line, top.line, head, name)
        key = f"{ns}/{name}"
        if head not in ("defn", "defn-") or key not in reach.keys or name in at_load:
            out.append((form, set(), True))
            continue
        doc = kids[2] if len(kids) > 3 and isinstance(kids[2], int) \
            and old_t.toks[kids[2]][0] == "str" else None
        hit = lambda line: reach.lines.at(p, to_map(line)) if to_map(line) else None
        sel = {}
        for n, i, gap in ss:
            if i != doc or gap:
                node, ts = entry_at(old_t, n, i, top, hit, macros)
                sel[key if node is None else f"{key}:{node.line}"] = \
                    reach.keys[key] if node is None else ts
        if sel:
            out.append((form + ([(ts, why) for why, ts in sorted(sel.items())],), set(), True))
    old_defns = {n for _, _, h, n in forms(old_text) if h in ("defn", "defn-")}
    changed = changed_lines(diff)[1]
    out += [(f, changed, False) for f in touched(new_text, changed)
            if f[2] not in ("defn", "defn-") or f[3] not in old_defns]
    return out


def owed(base, reach=None, head=None):
    """Returns `(owed, unreached)`: owed maps a target (a check name, a group name with no
    map, `ab:<probe>`, or ALL) to the first reason that selects it. The change runs from
    `base` to `head`, or to the working tree when `head` is None."""
    span = [base] + ([head] if head else [])
    paths = (git("diff", "--name-only", *span) or "").split()
    show = lambda rev, p: git("show", f"{rev}:{p}") or ""
    current = (lambda p: show(head, p)) if head else read
    harness = {PERF: Harness(current(PERF), False), AB: Harness(current(AB), True)}
    out, unreached = {}, []
    relevant = False
    clj = [p for p in paths if p.endswith((".clj", ".cljc"))]
    # The symbols every changed Clojure file holds at the base (True) and at the head (False).
    named = {True: set().union(*[symbols(show(base, p)) for p in clj]),
             False: set().union(*[symbols(current(p)) for p in clj])}

    def add(ts, why):
        for t in ts:
            out.setdefault(t, why)

    for p in paths:
        if not (p.startswith(("src/", "bench/")) and p.endswith((".clj", ".cljc"))) \
                and not CONTENT_RE.search(p):
            continue
        unmapped = reach is None or ns_of(p) not in reach.namespaces
        if CONTENT_RE.search(p) or (unmapped and STARTER_FILES.search(p)):
            relevant = True
            add(harness[PERF].content | harness[AB].content, p)
            continue
        diff = git("diff", "-U0", "--no-color", *span, "--", p) or ""
        old, new = changed_lines(diff)
        fs = [(f, old, True) for f in touched(show(base, p), old)] + \
             [(f, new, False) for f in touched(current(p), new)]
        if p in harness:
            prev = Harness(show(base, p), p == AB)
            for f, ls, was in fs:
                ts, why = harness[p].select(f, ls, prev if was else None)
                add(ts, f"{p}: {why}")
            continue
        if not p.startswith("src/"):
            continue
        relevant = True
        if unmapped:
            c, pr = static_select(p)
            add(c, p)
            add({"ab:" + n for n in pr}, p)
            continue
        held_at_map = {n for _, _, h, n in forms(show(reach.rev, p)) if h in ("defn", "defn-")}
        text = current(p).split("\n")
        at_load = set().union(*[symbols("\n".join(text[s - 1:e])) - ({n} if h in DOC_HEADS else set())
                                for s, e, h, n in forms(current(p)) if h not in CALL_HEADS])
        if reach.lines is not None:
            to_map = line_map(git("diff", "-U0", "--no-color", reach.rev, base, "--", p) or "")
            fs = by_line(p, reach, show(base, p), current(p), diff, to_map, at_load)
        tops = {True: top_texts(show(base, p)), False: top_texts(current(p))}
        same = set(tops[True].values()) & set(tops[False].values())
        for f, _, was in fs:
            if tops[was].get(f[0]) in same:
                continue    # a form moved, or changed only in comments, layout or docstring
            if f[2] in VAR_HEADS and f[3] and f[3] not in named[not was]:
                continue    # a var the change adds or deletes: its callers changed too
            for ts, why in f[4] if len(f) > 4 else \
                    [reach.select(ns_of(p), f, f[3] in held_at_map, f[3] in at_load)]:
                if why and not ts:
                    unreached.append(f"{p}: {why}")
                add(ts, f"{p}: {why}")
    if reach is not None and relevant:
        known = set(reach.targets)
        add(set(harness[PERF].roots) - known, "not in the reach map")
        add(set(harness[AB].roots) - known, "not in the reach map")
        add(set(reach.failed), "its census run threw")
    return out, sorted(set(unreached))


def kind(owed_map, probes):
    """Returns the `--kind` line: `all`, a comma-separated list, or the empty string."""
    sel = {t.removeprefix("ab:") for t in owed_map if t == ALL or t.startswith("ab:") == probes}
    if ALL in sel or "all" in sel:
        return "all"
    return ",".join(sorted(sel))


def reach_path():
    """Returns the reach map's path, in the repository's shared git directory."""
    common = git("rev-parse", "--path-format=absolute", "--git-common-dir")
    return os.path.join(common.strip(), "vaelii-perf", "reach.tsv") if common else None


def default_base():
    """Returns the merge base with the upstream branch, else with origin/main, else HEAD."""
    for ref in ("@{upstream}", "origin/main"):
        b = git("merge-base", ref, "HEAD")
        if b:
            return b.strip()
    return "HEAD"


def main(argv):
    ap = argparse.ArgumentParser(prog="perf-owed.py")
    ap.add_argument("--base")
    ap.add_argument("--head")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--kind", choices=["checks", "probes"])
    g.add_argument("--why", action="store_true")
    a = ap.parse_args(argv)
    base = a.base or default_base()
    for rev in filter(None, (base, a.head)):
        if git("rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}") is None:
            print(f"perf-owed: no such revision: {rev}", file=sys.stderr)
            return 2
    path = reach_path()
    reach = Reach(path) if path and os.path.exists(path) else None
    sel, unreached = owed(base, reach, a.head)
    if a.kind:
        line = kind(sel, a.kind == "probes")
        if line:
            print(line)
        return 0
    short = (git("rev-parse", "--short", base) or base).strip()
    if reach is None:
        print("no reach map: per-file rules, a check named by its group (lein perf --reach measures one)")
    else:
        behind = git("rev-list", "--count", f"{reach.rev}..HEAD")
        where = f"{behind.strip()} commit(s) behind HEAD" if behind is not None and \
            git("merge-base", "--is-ancestor", reach.rev, "HEAD") is not None else "not an ancestor of HEAD"
        dirty = f", measured over {reach.dirty} dirty file(s)" if reach.dirty != "0" else ""
        print(f"reach map at {reach.rev}, {where}{dirty}")
    for probes, label, cmd in ((False, "checks", "lein perf --owed"),
                               (True, "probes", f"lein perf-ab {short} --owed")):
        line = kind(sel, probes)
        if not line:
            print(f"{label} owed: none")
            continue
        print(f"{label} owed: {'all' if line == 'all' else len(line.split(','))} — {cmd}")
        for t in sorted(t for t in sel if t == ALL or t.startswith("ab:") == probes):
            print(f"  {t.removeprefix('ab:'):44} {sel[t]}")
    for u in unreached:
        print(f"no target executes {u}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
