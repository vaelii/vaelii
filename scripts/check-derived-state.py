#!/usr/bin/env python3
"""scripts/check-derived-state.py — every piece of state the engine keeps has a register row.

`vaelii.impl.caches/register-derived` is the derived-state register (docs/caches.md):
each row declares its key, what it reads and the write events that retire it.  A
structure without a row is one no test checks against the writes that move it.  This
check fails on two kinds of unregistered state:

  - a top-level `defonce` under `src/vaelii/impl/`, or a top-level `def` whose value is
    an atom, a volatile or a `java.util.concurrent` structure, that no
    `register-derived` or `register-cache` form in the same file names as `#'name`;
  - a field of the `Reasoning` record (`vaelii.impl.types.reasoning`) that no
    `register-derived` form locates with `:at [[:field …]]`;
  - a row id in `scripts/derived-state-features.edn` that no `register-derived` form
    declares, or one that two features name;
  - a `register-derived` form with no `:holds-content? true|false`, or one declaring
    true that `HOLDS_CONTENT` does not name: such a row holds a sentence the KB holds or
    would hold outside every store (docs/nmtms.md, "3. Separated state");
  - a row of kind `:index` or `:cache`, computed at the write or the settle, whose
    `:reads` do not reach M1 and whose namespace does not implement `IndexStore`, that
    `OUTSIDE_INDEX` does not name: such a row keeps a belief-free index outside the
    IndexStore (the same section);
  - a row registered in a file of `COVERED_FILES` with no `:covered-by`, unless
    `COVERAGE_OWED` names it, or a `:covered-by` naming a `lein perf` check
    (`bench/vaelii/bench/perf.clj`) or a perf-ab probe (`bench/vaelii/bench/ab.clj`)
    that does not exist: the check names the measurement that fails when the structure
    is replaced by a recompute at its read (docs/caches.md, "The derived-state
    register").

The keys inside a field that holds several rows' entries (`:taxonomy`,
`:nogood-candidates`) are written from many namespaces under keys that
are partly data (a reader), so `derived_state_test` checks them at run time instead.

State that is not derived from the KB's knowledge (instrumentation, storage spaces,
locks, configuration, warning flags, native handles) is named in `NOT_DERIVED` below
with the reason.  An entry there that names no stateful def, or one that is registered,
fails too, so the list cannot go stale.

    scripts/check-derived-state.py     # exit 1 on a finding
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPL = ROOT / "src" / "vaelii" / "impl"
REASONING = IMPL / "types" / "reasoning.clj"
FEATURES = ROOT / "scripts" / "derived-state-features.edn"
PERF = ROOT / "bench" / "vaelii" / "bench" / "perf.clj"
AB = ROOT / "bench" / "vaelii" / "bench" / "ab.clj"

# `(file relative to src/vaelii/impl, var or Reasoning field) -> reason`.
NOT_DERIVED: dict[tuple[str, str], str] = {
    ("asp/clingo.clj", "lib"): "the native clingo library handle",
    ("asp/solver.clj", "clasp-usable"): "a probe of the environment for the clasp binary",
    ("asp/solver.clj", "clingo-verdict"): "whether the native clingo library loads",
    ("asp/solver.clj", "clingo-vm-error-logged?"): "a one-time warning flag",
    ("budget.clj", "running"): "a count of the metered reads running",
    ("caches.clj", "derived"): "the derived-state register itself",
    ("caches.clj", "registry"): "the cache register itself",
    ("caches.clj", "the-profile"): "configuration: the cache scale, pressure and overrides",
    ("caches.clj", "guard"): "the memory-pressure guard's listener state",
    ("caches.clj", "critical"): "the heap mark's and the guard's reading of the last collection",
    ("caches.clj", "heap-mark"): "the heap mark's armed pool: JVM-wide listener state",
    ("caches.clj", "guard-lifecycle"): "a lock",
    ("caches.clj", "tallying"): "instrumentation: the derived-state event instrument's state",
    ("columnar.clj", "state-spaces"): "storage: the columnar index spaces",
    ("dense_kv.clj", "index-spaces"): "storage: the dense index spaces",
    ("disk/backend.clj", "stores"): "storage: the open disk stores by directory",
    ("disk/durability.clj", "registry"): "storage lifecycle: the stores the daemon syncs",
    ("disk/durability.clj", "next-id"): "storage lifecycle: a registration counter",
    ("disk/durability.clj", "scheduler"): "storage lifecycle: the sync executor",
    ("disk/durability.clj", "shutdown-hook"): "storage lifecycle: the JVM shutdown hook",
    ("disk/durability.clj", "compaction-executor"): "storage lifecycle: the compaction executor",
    ("disk/durability.clj", "compaction-in-flight"): "storage lifecycle: the stores compacting",
    ("disk/durability.clj", "last-compact-check-ms"): "storage lifecycle: the compaction throttle",
    ("disk/durability.clj", "compaction-paused"): "storage lifecycle: the pause count",
    ("disk/durability.clj", "compaction-stopped"): "storage lifecycle: the stop flag",
    ("disk/durability.clj", "lifecycle"): "a lock",
    ("disk/durability.clj", "quiescence"): "a lock",
    ("disk/durability.clj", "writes-in-flight"): "storage lifecycle: the public writes running",
    ("disk/durability.clj", "abort-requested"): "storage lifecycle: a shutdown's stop request",
    ("except.clj", "frame-writes"): "a count of the index writes a reader frame reads by storage, which a pass's kept frames compare",
    ("except.clj", "yield-writes"): "a count of the forced-monotonic facts leaving the index, which the held `yielding-reads?` compares",
    ("except.clj", "yield-stores"): "a bounded log of the functors of the forced-monotonic facts stored, which the held `yielding-reads?` reads",
    ("progress.clj", "timer"): "the executor that logs the progress lines no tick does",
    ("disk/files.clj", "dir-fsync-warned"): "a one-time warning flag",
    ("disk/index_snapshot.clj", "image-state"): "the write cadence of the index image",
    ("disk/lock.clj", "held"): "the directory locks this process holds",
    ("disk/record_store.clj", "rewrite-barrier"): "a test hook inside compaction",
    ("feed.clj", "dispatch"): "the renderer `vaelii.core` installs",
    ("foreign.clj", "registered"): "configuration: the reader formats registered in code",
    ("io/frames.clj", "open-readers"): "resource lifecycle: the frame readers to close",
    ("io/thaw.clj", "installed"): "the thaw allowlist hook",
    ("io/thaw.clj", "original-read-record"): "the thaw allowlist hook",
    ("io/thaw.clj", "original-read-deftype"): "the thaw allowlist hook",
    ("kb.clj", "default-ram-space-opens"): "a one-time warning counter",
    ("logging.clj", "dial"): "configuration: the log level",
    ("memory.clj", "record-spaces"): "storage: the in-memory record spaces",
    ("memory.clj", "record-counters"): "storage: the in-memory handle counters",
    ("memory.clj", "record-reserved"): "storage: the handle ranges each in-memory space skips for its forks",
    ("memory.clj", "space-reasoners"): "storage: the reasoner set each in-memory record space records",
    ("memory.clj", "index-spaces"): "storage: the in-memory index spaces",
    ("memory.clj", "engine-space-seq"): "a private space id counter",
    ("naming.clj", "advised"): "a one-time warning set",
    ("observe.clj", "holds"): "the open belief holds by token, the lifecycle of M3",
    ("observe.clj", "neighbour-hits"): "instrumentation: R7's process counters",
    ("observe.clj", "neighbour-misses"): "instrumentation: R7's process counters",
    ("observe.clj", "on-add"): "the store observer hooks R9 installs",
    ("observe.clj", "on-remove"): "the store observer hooks R9 installs",
    ("profile.clj", "tally"): "instrumentation: the profiler",
    ("rete.clj", "reg-queue"): "the reference queue R9's weak keys are purged through",
    ("settle_phases.clj", "clock"): "instrumentation: the settle phase clock",
    ("types/reasoning.clj", "violations"): "a report ledger of what writes exposed, read by no derivation",
    ("types/reasoning.clj", "settle-stats"): "instrumentation: settle pass counts",
    ("types/reasoning.clj", "chain-stats"): "instrumentation: chaining run counts",
}

# `row id -> what its entries hold`: the rows still holding KB content outside the KB.
# An entry leaves when its row's content becomes stored sentexes; an entry naming a row
# that does not declare `:holds-content? true` fails, so the list only shrinks.
HOLDS_CONTENT: dict[str, str] = {
    "S5": "closed-extent and separation refusals",
}

# `row id -> what it indexes`: the rows still holding a belief-free index outside the
# IndexStore.  Same shrink-only rule as HOLDS_CONTENT.
OUTSIDE_INDEX: dict[str, str] = {
    "R9": "the rete matcher's facts by functor and argument, held only under "
          "`VAELII_RETE=1` or `rete/track!`",
}

# The files whose rows must name the perf check or perf-ab probe that fails without them.
COVERED_FILES: set[str] = {"decide/arity.clj"}

# `row id -> why it has no `:covered-by` yet`.  Same shrink-only rule as HOLDS_CONTENT: an
# entry naming a row that declares `:covered-by`, or a row outside COVERED_FILES, fails.
COVERAGE_OWED: dict[str, str] = {
    "N3": "unmeasured: the recompute-at-read replacement has not been timed",
    "N8": "unmeasured: the recompute-at-read replacement has not been timed",
}

# The row whose entries are the beliefs; a row reading it, directly or through other
# rows, reads belief.
BELIEF_ROW = "M1"

STATEFUL_DEF_BODY = re.compile(
    r"^\s*\((?:atom|volatile!|observe/held-atom|held-atom|ref|agent)\b"
    r"|^\s*\((?:java\.util\.concurrent\.[\w.$]+|Atomic\w+|ConcurrentHashMap|WeakHashMap|"
    r"java\.util\.WeakHashMap|java\.util\.LinkedHashMap|LinkedHashMap)\.")
REGISTER = re.compile(r"\((?:caches/)?register-(?:derived|cache)\b")
DERIVED = re.compile(r"\((?:caches/)?register-derived\s+\{:id\s+:([A-Z]+\d+)\b")
HOLDS = re.compile(r":holds-content\?\s+(true|false)\b")
READS = re.compile(r":reads\s+\[([^\]]*)\]")
KIND = re.compile(r":kind\s+:([\w-]+)")
COMPUTED = re.compile(r":computed\s+:([\w-]+)")
INDEX_STORE_IMPL = re.compile(r"^\s*p/IndexStore\s*$", re.M)
COVERED_BY = re.compile(r":covered-by\s+\{([^}]*)\}")


def top_level_forms(text: str):
    """Yield `(start, end)` spans of the top-level forms in `text`, skipping strings,
    character literals and comments when counting brackets."""
    i, n, depth, start = 0, len(text), 0, None
    while i < n:
        c = text[i]
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c == "\\" and i + 1 < n:
            i += 2
            continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if c in "([{":
            if depth == 0:
                start = i
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0 and start is not None:
                yield start, i + 1
                start = None
        i += 1


def skip_meta(s: str, i: int) -> int:
    """The index past whitespace and any `^meta` forms at `i`."""
    while True:
        while i < len(s) and s[i].isspace():
            i += 1
        if i < len(s) and s[i] == "^":
            i += 1
            if i < len(s) and s[i] == "{":
                for a, b in top_level_forms(s[i:]):
                    i += b
                    break
            else:
                while i < len(s) and not s[i].isspace():
                    i += 1
            continue
        return i


def def_name_and_body(form: str):
    """`(head, name, body)` of a top-level `def`/`defonce`, or None."""
    m = re.match(r"\((defonce|def)\s", form)
    if not m:
        return None
    i = skip_meta(form, m.end())
    j = i
    while j < len(form) and not form[j].isspace() and form[j] not in "()":
        j += 1
    name = form[i:j]
    body = form[j:]
    # a docstring between the name and the value
    k = skip_meta(body, 0)
    if body[k:k + 1] == '"':
        k += 1
        while k < len(body) and body[k] != '"':
            k += 2 if body[k] == "\\" else 1
        body = body[k + 1:]
    return m.group(1), name, body


def covered_by(form: str) -> dict[str, list[str]] | None:
    """`{"perf": [check …], "perf-ab": [probe …]}` of a `register-derived` form's
    `:covered-by` map, or None when the form has none."""
    m = COVERED_BY.search(form)
    if not m:
        return None
    out: dict[str, list[str]] = {}
    for k, vec in re.findall(r":(perf-ab|perf)\s+\[([^\]]*)\]", m.group(1)):
        out.setdefault(k, []).extend(re.findall(r":([\w-]+)", vec))
    return out


def coverage_findings(rel: str, line: int, rid: str, form: str, checks: set[str],
                      probes: set[str], owed: dict[str, str]) -> list[str]:
    """The findings on row `rid`'s `:covered-by`, registered at `rel:line`: none outside
    COVERED_FILES; one for a row with no `:covered-by` that `owed` does not name,
    for an empty one, and for each name no check or probe carries."""
    if rel not in COVERED_FILES:
        return []
    cov = covered_by(form)
    if cov is None:
        return [] if rid in owed else [
            f"{rel}:{line}: row {rid} names no `:covered-by` perf check or perf-ab probe, "
            f"and is not in COVERAGE_OWED"]
    out = []
    if not any(cov.values()):
        out.append(f"{rel}:{line}: row {rid}'s `:covered-by` names no check or probe")
    out.extend(f"{rel}:{line}: row {rid}'s `:covered-by` names `:{c}`, no `lein perf` check"
               for c in cov.get("perf", []) if c not in checks)
    out.extend(f"{rel}:{line}: row {rid}'s `:covered-by` names `:{c}`, no perf-ab probe"
               for c in cov.get("perf-ab", []) if c not in probes)
    return out


# The coverage rule's own fixture: a row in a covered file with no `:covered-by` is found,
# as is one naming a check that does not exist; a covered row, an owed row and a row in
# another file are not.
COVERAGE_FIXTURE = [
    ("decide/arity.clj", "Z1", "(caches/register-derived {:id :Z1 :kind :cache})"),
    ("decide/arity.clj", "Z2", "(caches/register-derived {:id :Z2 "
                               ":covered-by {:perf [:ok-check] :perf-ab [:no-probe]}})"),
    ("decide/arity.clj", "Z3", "(caches/register-derived {:id :Z3 "
                               ":covered-by {:perf [:ok-check] :perf-ab [:ok-probe]}})"),
    ("decide/arity.clj", "Z5", "(caches/register-derived {:id :Z5 :kind :cache})"),
    ("decide/tuple.clj", "Z4", "(caches/register-derived {:id :Z4 :kind :cache})"),
]


def main() -> int:
    findings: list[str] = []
    checks = set(re.findall(r"\{:name\s+:([\w-]+)", PERF.read_text()))
    ab = re.search(r"\(def probes\b(.*?)\]\)", AB.read_text(), re.S)
    probes = set(re.findall(r"#'([\w-]+)", ab.group(1))) if ab else set()
    fixture = [f.split(": ")[1] for rel, rid, form in COVERAGE_FIXTURE
               for f in coverage_findings(rel, 1, rid, form, {"ok-check"}, {"ok-probe"},
                                                 {"Z5": "owed"})]
    if fixture != ["row Z1 names no `:covered-by` perf check or perf-ab probe, and is not "
                   "in COVERAGE_OWED", "row Z2's `:covered-by` names `:no-probe`, no perf-ab "
                   "probe"]:
        findings.append(f"scripts/check-derived-state.py: the coverage rule's own fixture "
                        f"no longer reads as it should: {fixture}")
    covered_rows: set[str] = set()
    stateful: dict[tuple[str, str], str] = {}
    registered_vars: set[tuple[str, str]] = set()
    located_fields: set[str] = set()
    row_ids: set[str] = set()
    content_rows: set[str] = set()
    # row id -> (file:line, reads, kind, computed, owner implements IndexStore)
    rows: dict[str, tuple[str, list[str], str, str, bool]] = {}

    for path in sorted(IMPL.rglob("*.clj")):
        rel = str(path.relative_to(IMPL))
        text = path.read_text()
        index_store = bool(INDEX_STORE_IMPL.search(text))
        for a, b in top_level_forms(text):
            form = text[a:b]
            line = text.count("\n", 0, a) + 1
            d = def_name_and_body(form)
            if d:
                head, name, body = d
                if head == "defonce" or STATEFUL_DEF_BODY.search(body):
                    stateful[(rel, name)] = f"{rel}:{line}"
            for rid in DERIVED.findall(form):
                row_ids.add(rid)
                reads, kind, computed = READS.search(form), KIND.search(form), COMPUTED.search(form)
                rows[rid] = (f"{rel}:{line}",
                             re.findall(r":([\w-]+)", reads.group(1)) if reads else [],
                             kind.group(1) if kind else "", computed.group(1) if computed else "",
                             index_store)
                findings.extend(coverage_findings(rel, line, rid, form, checks, probes,
                                                  COVERAGE_OWED))
                if rel in COVERED_FILES:
                    covered_rows.add(rid)
                    if covered_by(form) is not None and rid in COVERAGE_OWED:
                        findings.append(f"{rel}:{line}: row {rid} declares `:covered-by` "
                                        f"and COVERAGE_OWED still names it")
                h = HOLDS.search(form)
                if not h:
                    findings.append(f"{rel}:{line}: row {rid} declares no "
                                    f"`:holds-content? true|false`")
                elif h.group(1) == "true":
                    content_rows.add(rid)
                    if rid not in HOLDS_CONTENT:
                        findings.append(f"{rel}:{line}: row {rid} holds KB content outside "
                                        f"the KB (`:holds-content? true`), and is not in "
                                        f"HOLDS_CONTENT")
            if REGISTER.search(form):
                for v in re.findall(r"#'([\w.*+!?<>=/-]+)", form):
                    registered_vars.add((rel, v.split("/")[-1]))
                for at in re.finditer(r":at\s*\[", form):
                    span = next(top_level_forms(form[at.end() - 1:]), None)
                    if span:
                        vec = form[at.end() - 1:at.end() - 1 + span[1]]
                        located_fields.update(re.findall(r"\[\s*:([\w-]+)", vec[1:]))

    rec = re.search(r"\(defrecord\s+Reasoning\s+\[([^\]]*)\]", REASONING.read_text())
    fields = rec.group(1).split() if rec else []
    if not fields:
        findings.append("types/reasoning.clj: no `defrecord Reasoning` field vector found")

    for key, where in sorted(stateful.items()):
        if key in registered_vars or key in NOT_DERIVED:
            continue
        findings.append(f"{where}: `{key[1]}` holds state and has no register row "
                        f"(`caches/register-derived` naming #'{key[1]}), and is not in "
                        f"NOT_DERIVED")
    for f in fields:
        if f in located_fields or ("types/reasoning.clj", f) in NOT_DERIVED:
            continue
        findings.append(f"types/reasoning.clj: Reasoning field `{f}` has no register row "
                        f"locating it (`:at [[:{f} …]]`), and is not in NOT_DERIVED")
    for key in sorted(NOT_DERIVED):
        if key[0] == "types/reasoning.clj":
            if key[1] not in fields:
                findings.append(f"NOT_DERIVED names `{key[1]}`, which is no Reasoning field")
            elif key[1] in located_fields:
                findings.append(f"NOT_DERIVED names `{key[1]}`, which a register row locates")
        elif key not in stateful:
            findings.append(f"NOT_DERIVED names {key[0]} `{key[1]}`, which is no stateful def")
        elif key in registered_vars:
            findings.append(f"NOT_DERIVED names {key[0]} `{key[1]}`, which is registered")

    findings.extend(f"HOLDS_CONTENT names {r}, which no row declaring "
                    f"`:holds-content? true` is" for r in sorted(HOLDS_CONTENT)
                    if r not in content_rows)

    findings.extend(f"COVERAGE_OWED names {r}, which no row in {sorted(COVERED_FILES)} is"
                    for r in sorted(COVERAGE_OWED) if r not in covered_rows)

    def reads_belief(rid: str, seen: frozenset = frozenset()) -> bool:
        return rid == BELIEF_ROW or (rid in rows and rid not in seen and any(
            reads_belief(r, seen | {rid}) for r in rows[rid][1]))

    outside: set[str] = set()
    for rid, (where, reads, kind, computed, index_store) in sorted(rows.items()):
        if (kind in ("index", "cache") and computed in ("write", "settle")
                and rid not in content_rows and not index_store
                and not reads_belief(rid)):
            outside.add(rid)
            if rid not in OUTSIDE_INDEX:
                findings.append(f"{where}: row {rid} keeps a belief-free index at the write "
                                f"outside the IndexStore, and is not in OUTSIDE_INDEX "
                                f"(docs/nmtms.md, \"3. Separated state\")")
    findings.extend(f"OUTSIDE_INDEX names {r}, which is no belief-free index kept outside "
                    f"the IndexStore" for r in sorted(OUTSIDE_INDEX) if r not in outside)

    featured: dict[str, int] = {}
    for vec in re.findall(r":rows\s*\[([^\]]*)\]", re.sub(r";[^\n]*", "", FEATURES.read_text())):
        for r in re.findall(r":([\w-]+)", vec):
            featured[r] = featured.get(r, 0) + 1
            if r not in row_ids:
                findings.append(f"{FEATURES.relative_to(ROOT)}: `:{r}` is no register row")
    findings.extend(f"{FEATURES.relative_to(ROOT)}: `:{r}` is in {n} features"
                    for r, n in sorted(featured.items()) if n > 1)

    for f in findings:
        print(f)
    regd = sum(1 for k in stateful if k in registered_vars)
    allowed = sum(1 for k in stateful if k in NOT_DERIVED)
    print(f"derived-state: {len(stateful)} stateful defs ({regd} registered, "
          f"{allowed} not derived), {len(fields)} Reasoning fields, "
          f"{len(row_ids)} rows ({len(content_rows)} holding content, "
          f"{len(outside)} indexing outside the IndexStore), "
          f"{len(featured)} in a feature, "
          f"{len(findings)} findings")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
