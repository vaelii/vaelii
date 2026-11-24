#!/usr/bin/env bash
# scripts/perf-ab.sh — `lein perf-ab <base-rev>`: the working tree against an older
# revision, in absolute time, on this machine and this JDK.
#
# `lein perf` judges the growth of a cost between two sizes, so a cost added to every
# operation moves both readings and passes; `test/vaelii/assert_cost_test.clj` counts
# index operations, so a slower operation that reads no more of the index passes too.
# This is the check for that class: the probes in `vaelii.bench.ab`, run in fresh JVMs
# alternating base and head, and judged by the paired ratio head/base.
#
# The base is `git archive`d into `testbench/perf-ab/<hash>/` (kept for the next run)
# and the head's `bench/vaelii/bench/ab.clj` is copied over its own, so both sides time
# the same probe code.  The pair order alternates per rep, so a drift in machine load
# lands on both sides.
#
#   lein perf-ab <base-rev> [--reps N] [--first-rep K] [--threshold X] [--only probe,probe | --owed]
#   lein perf-ab --judge [--threshold X] <rows.tsv>…
#
# `--owed` runs the probes the change from the base to the working tree reaches, read off
# scripts/perf-owed.py, and exits 0 having run nothing when it reaches none.
#
# The reps are numbered K to K+N-1 (`--first-rep`, default 1), and an odd rep runs the
# base first.  Each run writes its rows to `logs/perf-ab/run-<pid>.tsv`, one per rep, side
# and probe.  `--judge` runs nothing and judges the rows of the files it is given, so
# reps run on several machines with distinct K are judged as one run:
# .github/workflows/perf.yml runs one rep per runner that way.
#
# A probe REGRESSED when its median paired ratio exceeds the threshold (default 1.25)
# and every pair but at most one reads above 1.  Exit: 0 clean, 1 on a regression,
# 2 on a bad argument, 3 when a JVM stopped before printing its rows.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# shellcheck source=scripts/lib/runlog.sh
. "$ROOT/scripts/lib/runlog.sh"
# shellcheck source=scripts/lib/slots.sh
. "$ROOT/scripts/lib/slots.sh"

usage() {
  echo "usage: lein perf-ab <base-rev> [--reps N] [--first-rep K] [--threshold X] [--only a,b | --owed]" >&2
  echo "       lein perf-ab --judge [--threshold X] <rows.tsv>…" >&2
  exit 2
}

# judge <threshold> <rows.tsv>…: the table and the verdict line, over every file's rows.
judge() {
  python3 - "$@" <<'PY'
import sys, statistics as st
thr = float(sys.argv[1])
rows = [l.split("\t") for f in sys.argv[2:] for l in open(f).read().splitlines()]
by = {}
for rep, side, probe, ms in rows:
    by.setdefault(probe, {}).setdefault(rep, {})[side] = float(ms)
bad = []
print(f"\n{'probe':16} {'base ms':>10} {'head ms':>10} {'head/base':>10}  pairs slower")
for probe, reps in by.items():
    pairs = [(r["base"], r["head"]) for r in reps.values() if "base" in r and "head" in r]
    ratios = [h / b for b, h in pairs]
    med = st.median(ratios)
    slower = sum(x > 1 for x in ratios)
    verdict = ""
    if med > thr and slower >= len(ratios) - 1:
        verdict = "REGRESSED"; bad.append(probe)
    elif med < 1 / thr and slower <= 1:
        verdict = "faster"
    print(f"{probe:16} {st.median(b for b, _ in pairs):10.3f} {st.median(h for _, h in pairs):10.3f}"
          f" {med:9.2f}x  {slower}/{len(ratios)}  {verdict}")
print()
print(f"{len(bad)} of {len(by)} probes REGRESSED: {bad}" if bad
      else f"{len(by)} probe(s) within {thr}x of the base")
PY
}

if [[ "${1:-}" == --judge ]]; then
  shift; THRESHOLD=1.25
  if [[ "${1:-}" == --threshold ]]; then
    [[ $# -ge 2 ]] || usage; THRESHOLD="$2"; shift 2
  fi
  [[ $# -ge 1 ]] || usage
  for f in "$@"; do [[ -s "$f" ]] || { echo "perf-ab --judge: no rows in $f" >&2; exit 2; }; done
  out=$(judge "$THRESHOLD" "$@") || exit 2
  printf '%s\n' "$out"
  [[ "$out" != *REGRESSED* ]] || exit 1
  exit 0
fi

[[ $# -ge 1 && "$1" != --* ]] || usage
BASE_REV="$1"; shift
REPS=5; FIRST=1; THRESHOLD=1.25; ONLY=(); OWED=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --reps)      [[ $# -ge 2 ]] || usage; REPS="$2"; shift 2 ;;
    --first-rep) [[ $# -ge 2 && "$2" =~ ^[1-9][0-9]*$ ]] || usage; FIRST="$2"; shift 2 ;;
    --threshold) [[ $# -ge 2 ]] || usage; THRESHOLD="$2"; shift 2 ;;
    --only)      [[ $# -ge 2 ]] || usage; ONLY=(--only "$2"); shift 2 ;;
    --owed)      OWED=1; shift ;;
    *)           usage ;;
  esac
done
BASE=$(git rev-parse --short "$BASE_REV^{commit}" 2>/dev/null) \
  || { echo "perf-ab: no such revision: $BASE_REV" >&2; exit 2; }
if (( OWED )); then
  [[ ${#ONLY[@]} -eq 0 ]] || usage
  sel=$(python3 scripts/perf-owed.py --base "$BASE" --kind probes) || exit 2
  case "$sel" in
    "")  echo "perf-ab --owed: the change since $BASE owes no probe"; exit 0 ;;
    all) ;;
    *)   ONLY=(--only "$sel") ;;
  esac
fi

require_primary "lein perf-ab"
perf_lock_take lein perf-ab "$@"

AB_ROOT="logs/perf-ab"
LOG="$AB_ROOT/run-$$.log"
TSV="$AB_ROOT/run-$$.tsv"
BASE_TREE="testbench/perf-ab/$BASE"
mkdir -p "$AB_ROOT" || exit 1

if [[ ! -f "$BASE_TREE/project.clj" ]]; then
  mkdir -p "$BASE_TREE" && git archive "$BASE" | tar -x -C "$BASE_TREE" || exit 1
fi
mkdir -p "$BASE_TREE/bench/vaelii/bench"
cp bench/vaelii/bench/ab.clj "$BASE_TREE/bench/vaelii/bench/ab.clj" || exit 1

runlog_start
{ revision_header "perf-ab against $BASE"
  echo "# base $(git log -1 --format='%h %s' "$BASE")"
  echo "# $REPS rep(s), threshold ${THRESHOLD}x"; } >"$LOG"
cat "$LOG"

# side <name> <dir>: one JVM, every probe, rows appended to the TSV.  A JVM that exits
# non-zero stopped at a probe that threw, and the probes after it printed nothing.
side() {
  local name="$1" dir="$2" out rc
  out=$(cd "$dir" && lein with-profile +bench run -m vaelii.bench.ab ${ONLY[@]+"${ONLY[@]}"} 2>&1)
  rc=$?
  printf '%s\n' "$out" | sed "s/^/[$name] /" >>"$LOG"
  printf '%s\n' "$out" | awk -v s="$name" -v r="$rep" '$1=="ab-result"{print r"\t"s"\t"$2"\t"$3}' >>"$TSV"
  if [[ $rc -ne 0 ]] || ! grep -q '^ab-result' <<<"$out"; then
    echo "perf-ab: the $name JVM exited $rc after $(grep -c '^ab-result' <<<"$out") result(s):" >&2
    tail -20 <<<"$out" >&2
    return 1
  fi
}

: >"$TSV"
for rep in $(seq "$FIRST" $((FIRST + REPS - 1))); do
  echo "perf-progress $((rep - FIRST + 1))/$REPS" >&2
  if (( rep % 2 )); then side base "$BASE_TREE" && side head "$ROOT"
  else                   side head "$ROOT"      && side base "$BASE_TREE"; fi || exit 3
done

judge "$THRESHOLD" "$TSV" | tee -a "$LOG"

ln -sfn "$(basename "$LOG")" "$AB_ROOT/latest" 2>/dev/null || true
verdict=$(grep -E '^[0-9]+ (probe\(s\) within|of [0-9]+ probes REGRESSED)' "$LOG" | tail -1)
[[ -n "$verdict" ]] || exit 1
if [[ "$verdict" == *REGRESSED* ]]; then rc=1; state=failed; else rc=0; state=passed; fi
runlog_record perf-ab "$BASE" "$state" "$verdict" "$LOG"
exit "$rc"
}
