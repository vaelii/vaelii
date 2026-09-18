#!/usr/bin/env bash
# scripts/perf.sh — `lein perf`: the scaling gate, with its report kept.
#
# The checks themselves are `vaelii.bench.perf`, and this adds nothing to what
# they judge.  What it adds is the RECORD: the report goes to
# `logs/perf/run-<pid>.log`, `logs/perf/latest` points at the newest, and one row
# lands in `logs/runs.tsv` naming the revision, the clock and the verdict
# (scripts/lib/runlog.sh).
#
# WHY A WRAPPER AND NOT A CALL INSIDE THE HARNESS.  One ledger writer, in shell,
# read by every runner — `lein lint`, the suite, the matrix and this.  A second
# copy in Clojure would be a second spelling of the row format, and the two would
# drift silently, because nothing compares a TSV against another language's idea
# of it.  The cost is one extra leiningen boot (~1s against a ~40s stage).
#
# Arguments pass straight through, so `lein perf --quick`, `lein perf --only
# <name>` and `lein perf --tolerance <x>` are unchanged.
#
# `2>&1` merges the harness's stderr into the log, which is where the
# `perf-progress k/total` markers live — `scripts/gate.sh` polls those into its
# live bar and redirects both streams into one file anyway, so the merge changes
# nothing a reader sees.
#
# Exit: the harness's own status — 0 when every check passed, 1 on a regression,
# 2 on a bad argument.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# shellcheck source=scripts/lib/runlog.sh
. "$ROOT/scripts/lib/runlog.sh"

PERF_ROOT="logs/perf"
LOG="$PERF_ROOT/run-$$.log"
mkdir -p "$PERF_ROOT" || exit 1

runlog_start
revision_stamp perf >"$LOG"
# `${PIPESTATUS[0]}`, not `$?`: a pipeline reports `tee`'s status, and a perf gate
# as green as `tee` is gates nothing.
lein with-profile +bench run -m vaelii.bench.perf "$@" 2>&1 | tee -a "$LOG"
rc=${PIPESTATUS[0]}

ln -sfn "$(basename "$LOG")" "$PERF_ROOT/latest" 2>/dev/null || true
runlog_prune "$PERF_ROOT" "${PERF_KEEP_RUNS:-40}"

# The harness's own closing line is the summary — `N check(s) ok…` or `N of M
# checks REGRESSED: …`.  Read back out of the log rather than recomputed here,
# so this file states no count of its own to go stale (scripts/gate.sh's rule).
verdict=$(sed 's/\x1b\[[0-9;]*m//g' "$LOG" \
            | grep -E '^[0-9]+ (check\(s\) ok|of [0-9]+ checks REGRESSED)' | tail -1)

# NO VERDICT LINE, NO ROW.  The harness prints one on every run it completes,
# pass or fail, so its absence means this was not a run: a refused argument
# (`--only <no such check>` exits 2 before anything is measured), a ^C, a JVM
# that died.  A ledger row for one of those would read as a failing perf gate
# at this revision and send somebody looking for a regression nobody caused.
if [[ -n "$verdict" ]]; then
  [[ $rc -eq 0 ]] && state=passed || state=failed
  runlog_record perf - "$state" "$verdict" "$LOG"
fi
exit "$rc"
