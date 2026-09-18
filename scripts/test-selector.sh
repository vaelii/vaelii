#!/usr/bin/env bash
# scripts/test-selector.sh — one `lein test <selector>` run, with its report kept.
#
# Behind the two aliases whose selectors NOTHING ELSE RUNS:
#
#   lein test-multi-jvm   the cross-process tests — `:multi-jvm` is opt-in, so
#                         `lein test`, `lein test :all` and the gate all pass over it
#   lein test-fuzz        the exhaustive truncation sweep, opt-in for the other
#                         reason: no configuration varies it, so a matrix row
#                         would repeat identical work
#
# Both are owed by a change nothing else covers — the single-writer lock, disk
# open/close, recovery, the daemon and the CLI's `--dir` for the first; a durable
# file format, its framing or its recovery for the second (README.md's entry
# points).  A run that leaves no trace is one nobody can say happened, which for
# a selector no gate reaches is the whole question: this writes the report to
# `logs/test/<selector>-run-<pid>.log` and one row to `logs/runs.tsv`
# (scripts/lib/runlog.sh).
#
# `scripts/test-parallel.sh` does this for the sharded selectors and is not what
# runs here.  Neither of these may be sharded: `:multi-jvm` forks a second JVM
# and `:fuzz` names its own four backends, so both want one JVM and the whole
# selector in it.
#
#   bash scripts/test-selector.sh :multi-jvm
#   bash scripts/test-selector.sh :fuzz [<namespace> …]
#
# Arguments after the selector pass through to `lein test`.
#
# Exit: `lein test`'s own status.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# shellcheck source=scripts/lib/runlog.sh
. "$ROOT/scripts/lib/runlog.sh"

[[ $# -ge 1 && "$1" == :* ]] || {
  echo "test-selector: first argument must be a selector, e.g. :multi-jvm" >&2
  exit 2
}
SELECTOR="$1"; shift

TEST_ROOT="logs/test"
LOG="$TEST_ROOT/${SELECTOR#:}-run-$$.log"
mkdir -p "$TEST_ROOT" || exit 1

runlog_start
revision_stamp "test $SELECTOR" >"$LOG"
# `${PIPESTATUS[0]}`, not `$?`: a pipeline reports `tee`'s status, and a suite as
# green as `tee` is reports nothing.  This is the mistake test-parallel.sh names
# in its header and reads an exit marker to avoid.
lein test "$SELECTOR" "$@" 2>&1 | tee -a "$LOG"
rc=${PIPESTATUS[0]}

ln -sfn "$(basename "$LOG")" "$TEST_ROOT/${SELECTOR#:}-latest" 2>/dev/null || true
runlog_prune "$TEST_ROOT" "${TEST_KEEP_RUNS:-40}"

# The totals out of the log, which is where clojure.test wrote them — this file
# counts nothing of its own, so there is no second count to disagree.
body=$(sed 's/\x1b\[[0-9;]*m//g' "$LOG")
ran=$(printf '%s' "$body" | grep -E '^Ran [0-9]+ tests containing' | tail -1)
bad=$(printf '%s' "$body" | grep -E '^[0-9]+ failures, [0-9]+ errors' | tail -1)

# NO TOTALS LINE, NO ROW.  clojure.test prints one on every run that reaches the
# end, so its absence is a run that did not: a selector that matched nothing, a
# ^C, a JVM that died at load.  A row for one of those would read as a verdict.
if [[ -n "$ran" && -n "$bad" ]]; then
  if [[ $rc -eq 0 && "$bad" == "0 failures, 0 errors"* ]]; then state=passed; else state=failed; fi
  runlog_record test "$SELECTOR" "$state" "${ran#Ran } — $bad" "$LOG"
fi
exit "$rc"
