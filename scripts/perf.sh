#!/usr/bin/env bash
# scripts/perf.sh — `lein perf`: the scaling checks, with their report kept.
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
# of it.  The cost is one extra leiningen boot (~1s against a stage of about an hour).
#
# Arguments pass straight through, so `lein perf --quick`, `lein perf --only
# <name>[,<name>…]` and `lein perf --tolerance <x>` are unchanged.  `--owed`, `-n` and
# `--reach` are this wrapper's own (below).
#
# `2>&1` merges the harness's stderr into the log, which is where the
# `perf-progress k/total` markers live — `scripts/gate.sh` polls those into its
# live bar and redirects both streams into one file anyway, so the merge changes
# nothing a reader sees.
#
# Exit: the harness's own status — 0 when every check passed, 1 on a regression,
# 2 on a bad argument.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# shellcheck source=scripts/lib/runlog.sh
. "$ROOT/scripts/lib/runlog.sh"

# `--owed[=<ref>]` runs the checks the change since <ref> reaches, read off
# scripts/perf-owed.py, and `-n` prints them and the code selecting each without running.
# The ref defaults to the merge base with the upstream branch.
OWED=0; OWED_BASE=(); DRY=0; REACH=0; PASS=()
for a in "$@"; do
  case "$a" in
    --owed)   OWED=1 ;;
    --owed=*) OWED=1; OWED_BASE=(--base "${a#--owed=}") ;;
    -n)       DRY=1 ;;
    --reach)  REACH=1 ;;
    *)        PASS+=("$a") ;;
  esac
done
if (( OWED )); then
  (( DRY )) && exec python3 scripts/perf-owed.py ${OWED_BASE[@]+"${OWED_BASE[@]}"} --why
  sel=$(python3 scripts/perf-owed.py ${OWED_BASE[@]+"${OWED_BASE[@]}"} --kind checks) || exit 2
  case "$sel" in
    "")  echo "lein perf --owed: the change owes no check"; exit 0 ;;
    all) set -- ${PASS[@]+"${PASS[@]}"} ;;
    *)   set -- --only "$sel" ${PASS[@]+"${PASS[@]}"} ;;
  esac
fi

# `--reach` writes the reach map and the line map scripts/perf-owed.py reads, into the
# clone's shared git directory, so every worktree of the clone reads the same maps.  It
# runs each check at both sizes and each perf-ab probe once under the JaCoCo agent
# (bench/vaelii/bench/reach.clj).
if (( REACH )); then
  # shellcheck source=scripts/lib/slots.sh
  . "$ROOT/scripts/lib/slots.sh"
  require_primary "lein perf --reach"
  perf_lock_take lein perf --reach
  MAP="$(git rev-parse --path-format=absolute --git-common-dir)/vaelii-perf/reach.tsv"
  LOG="logs/perf/reach-$$.log"
  mkdir -p logs/perf || exit 1
  runlog_start
  revision_header "perf reach" >"$LOG"
  # The agent writes each class it instruments here (project.clj's `:reach`), and a class
  # an earlier run wrote carries another revision's line numbers.
  rm -rf target/reach-classes
  lein with-profile +bench,+reach run -m vaelii.bench.reach "$MAP" "$(revision_hash)" \
    "$(revision_dirty)" 2>&1 | tee -a "$LOG"
  rc=${PIPESTATUS[0]}
  summary=$(grep -E '^[0-9]+ target\(s\)' "$LOG" | tail -1)
  if [[ -n "$summary" ]]; then
    [[ $rc -eq 0 ]] && state=passed || state=failed
    runlog_record perf reach "$state" "$summary" "$LOG"
  fi
  exit "$rc"
fi

# `--list` prints the checks' names and claims, measures nothing, runs anywhere and
# writes no log or ledger row.  A worktree runs `lein gate`, and `lein perf` only with
# `--only` (scripts/lib/slots.sh says why).
case " $* " in
  *" --list "*) exec lein with-profile +bench run -m vaelii.bench.perf "$@" ;;
esac
# shellcheck source=scripts/lib/slots.sh
. "$ROOT/scripts/lib/slots.sh"
case " $* " in
  *" --only "*) ;;
  *) require_primary "lein perf without --only" ;;
esac
perf_lock_take lein perf "$@"

PERF_ROOT="logs/perf"
LOG="$PERF_ROOT/run-$$.log"
mkdir -p "$PERF_ROOT" || exit 1

runlog_start
revision_header perf >"$LOG"
# `${PIPESTATUS[0]}`, not `$?`: a pipeline reports `tee`'s status, and a perf check
# that reports `tee`'s status checks nothing.
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
# that died.  A ledger row for one of those would read as a failing perf check
# at this revision and send somebody looking for a regression nobody caused.
if [[ -n "$verdict" ]]; then
  [[ $rc -eq 0 ]] && state=passed || state=failed
  runlog_record perf - "$state" "$verdict" "$LOG"
fi
exit "$rc"
}
