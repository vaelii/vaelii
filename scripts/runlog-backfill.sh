#!/usr/bin/env bash
# scripts/runlog-backfill.sh — the runs already on disk, as ledger rows.
#
# `scripts/lib/runlog.sh` records a run as it finishes, so the ledger starts
# empty in a checkout that has been building for weeks.  The verdicts are not
# missing, though: every gate left `target/gate/run-*/{lint,test,perf}.log` and
# every matrix left `logs/test-matrix/run-*/summary.tsv`, and each of those
# opens with the revision stamp `scripts/lib/revision.sh` writes.  This reads
# them and appends the rows nothing wrote at the time.
#
# IDEMPOTENT, and on the `log` column: a row names the file or directory it was
# derived from, so a second pass adds nothing.  That is also what makes it safe
# beside a live run — a gate going right now has a row of its own to write, and
# this one skips the path once that row exists.
#
# WHAT IS APPROXIMATE, and it is one column.  A gate stage log carries its start
# time and not its duration, so `seconds` for lint and perf is the gap from the
# stamp to the log's last write.  That over-reads by however long the file sat
# after the stage finished, which is nothing for a stage whose last line is its
# verdict.  The suite and the matrix report their own wall clock and use it.
# Every other column is read, not inferred.
#
#   bash scripts/runlog-backfill.sh          # append what is missing
#   bash scripts/runlog-backfill.sh -n       # say what it would append
#
# Exit: 0 whatever it finds.  A tree with no artifacts to read is a new
# checkout, not a failure.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# shellcheck source=scripts/lib/runlog.sh
. "$ROOT/scripts/lib/runlog.sh"
# the roster sizes, to tell a matrix from a subset by what it ran
# shellcheck source=scripts/lib/suite-configs.sh
. "$ROOT/scripts/lib/suite-configs.sh"
ROUTINE_TOTAL=$(( ${#ALL_BACKENDS[@]} + ${#ALL_SWEEPS[@]} - ${#ROUTINE_SKIP[@]} ))

DRY=0
case "${1:-}" in
  -n|--dry-run) DRY=1 ;;
  -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' "${BASH_SOURCE[0]}"; exit 0 ;;
  "") ;;
  *) echo "runlog-backfill: unknown argument $1" >&2; exit 2 ;;
esac

# The `log` values the ledger already holds, so a path is read once.
KNOWN=""
[[ -r "$RUNLOG_FILE" ]] && KNOWN=$(awk -F'\t' 'NR>1 { print $11 }' "$RUNLOG_FILE")

known() {                      # known <log path>
  printf '%s\n' "$KNOWN" | grep -qxF "$1"
}

# `date` parses a fixed timestamp two incompatible ways: BSD (macOS) wants
# `-j -f <format>`, GNU coreutils wants `-d`.  Try BSD first and fall back,
# because this repo is authored on macOS and gated on Linux.
to_epoch() {                   # to_epoch "YYYY-MM-DD HH:MM:SS"
  local stamp="$1" out
  out=$(date -j -f '%Y-%m-%d %H:%M:%S' "$stamp" '+%s' 2>/dev/null) \
    || out=$(date -d "$stamp" '+%s' 2>/dev/null) || out=""
  printf '%s' "$out"
}

mtime_of() {                   # mtime_of <path>
  stat -f %m "$1" 2>/dev/null || stat -c %Y "$1" 2>/dev/null || echo 0
}

# The revision stamp at the top of every log these read:
#   `# <name> at <rev> — <state clause> — <YYYY-MM-DD HH:MM:SS>`
# Three readers rather than one call returning three values, because a log
# missing its stamp must leave each field empty rather than shift the others.
stamp_line() { head -1 "$1" 2>/dev/null | grep '^# ' || true; }
stamp_rev()  { printf '%s' "$1" | sed -n 's/^# [^ ]* at \([0-9a-f]\{6,\}\) .*/\1/p'; }
stamp_date() { printf '%s' "$1" | grep -oE '[0-9]{4}-[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2}:[0-9]{2}' | tail -1; }
stamp_dirty() {
  local n
  n=$(printf '%s' "$1" | sed -n 's/.*tree DIRTY: \([0-9]*\) uncommitted.*/\1/p')
  printf '%s' "${n:-0}"
}

strip_ansi() { sed 's/\x1b\[[0-9;]*m//g'; }

added=0; skipped=0

# emit <kind> <variant> <state> <seconds> <epoch> <rev> <dirty> <summary> <log>
#
# The ledger writer's own function does the formatting; this sets the five
# fields `runlog_start` would otherwise have read from the clock and from git,
# because the run being recorded happened days ago.
emit() {
  local kind="$1" variant="$2" state="$3" secs="$4" epoch="$5" rev="$6" dirty="$7" summary="$8" log="$9"
  if [[ $DRY -eq 1 ]]; then
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$kind" "$variant" "$state" "$rev" "$log" "$summary"
    added=$((added + 1))
    return 0
  fi
  RUNLOG_EPOCH="$epoch"
  RUNLOG_STARTED=$(date -r "$epoch" '+%Y-%m-%dT%H:%M:%S' 2>/dev/null \
                   || date -d "@$epoch" '+%Y-%m-%dT%H:%M:%S' 2>/dev/null || echo '')
  RUNLOG_REV="$rev"
  RUNLOG_DIRTY="$dirty"
  RUNLOG_SUBJECT=$(git log -1 --pretty=%s "$rev" 2>/dev/null || echo '')
  # `runlog_record` computes the duration from the clock, which is right for a
  # run that just finished and wrong for one from last week.  Hand it the
  # measured figure by moving the epoch forward and back around the call.
  local real="$RUNLOG_EPOCH"
  RUNLOG_EPOCH=$(( $(date '+%s') - secs ))
  local started="$RUNLOG_STARTED"
  runlog_record "$kind" "$variant" "$state" "$summary" "$log"
  # Rewrite the two clock columns of the row just appended to the run's own,
  # rather than the now the writer stamped.  `ed`-free and in place: the last
  # line is the one this call wrote, and no other writer appends between the
  # two statements of one shell.
  awk -F'\t' -v OFS='\t' -v n="$(wc -l < "$RUNLOG_FILE" | tr -d ' ')" \
      -v started="$started" -v epoch="$real" \
      'NR == n { $1 = started; $2 = epoch } { print }' \
      "$RUNLOG_FILE" > "$RUNLOG_FILE.$$" && mv "$RUNLOG_FILE.$$" "$RUNLOG_FILE"
  RUNLOG_EPOCH="$real"
  added=$((added + 1))
}

# ---- the gate stages ---------------------------------------------------------
for dir in target/gate/run-*; do
  [[ -d "$dir" ]] || continue
  for stage in lint test perf; do
    log="$dir/$stage.log"
    [[ -f "$log" ]] || continue
    if known "$log"; then skipped=$((skipped + 1)); continue; fi
    line=$(stamp_line "$log")
    rev=$(stamp_rev "$line"); date_str=$(stamp_date "$line"); dirty=$(stamp_dirty "$line")
    [[ -n "$rev" && -n "$date_str" ]] || continue
    epoch=$(to_epoch "$date_str"); [[ -n "$epoch" ]] || continue
    secs=$(( $(mtime_of "$log") - epoch )); (( secs < 0 )) && secs=0
    body=$(strip_ansi < "$log")
    variant="-"; state=interrupted; summary=""
    case "$stage" in
      lint)
        summary=$(printf '%s' "$body" | grep -E '^lint: ' | tail -1)
        summary="${summary#lint: }"
        [[ "$summary" == *clean* ]] && state=passed
        [[ "$summary" == *FAILED* ]] && state=failed ;;
      test)
        variant=$(printf '%s' "$body" | grep -oE 'namespaces at :[a-z]+' | head -1)
        variant=":${variant##*:}"; [[ "$variant" == ":" ]] && variant=":default"
        ran=$(printf '%s' "$body" | grep -E '^Ran [0-9]+ tests containing' | tail -1)
        bad=$(printf '%s' "$body" | grep -E '^[0-9]+ failures, [0-9]+ errors' | tail -1)
        wall=$(printf '%s' "$body" | grep -oE 'in [0-9]+s$' | tail -1)
        [[ -n "$wall" ]] && { wall="${wall#in }"; secs="${wall%s}"; }
        if [[ -n "$ran" && -n "$bad" ]]; then
          if [[ "$bad" == "0 failures, 0 errors"* ]]; then state=passed; else state=failed; fi
        fi
        summary="${ran#Ran } — ${bad}" ;;
      perf)
        summary=$(printf '%s' "$body" \
                    | grep -E '^[0-9]+ (check\(s\) ok|of [0-9]+ checks REGRESSED)' | tail -1)
        [[ "$summary" == *"check(s) ok"* ]] && state=passed
        [[ "$summary" == *REGRESSED* ]] && state=failed ;;
    esac
    # A run directory holding `INTERRUPTED` reached no verdict whatever its log's
    # last line says — gate.sh writes that file precisely so a partial log cannot
    # be read as one.
    [[ -f "$dir/INTERRUPTED" ]] && state=interrupted
    emit "$stage" "$variant" "$state" "$secs" "$epoch" "$rev" "$dirty" \
         "${summary:-no verdict line}" "$log"
  done
done

# ---- the matrix runs ---------------------------------------------------------
# `summary.tsv` is the verdict — one row per configuration, written whatever the
# outcome — and the selector is in each config log's `# env … lein test :SEL`
# line, since the summary has no column for it.
for dir in logs/test-matrix/run-*; do
  [[ -d "$dir" ]] || continue
  summary_tsv="$dir/summary.tsv"
  [[ -f "$summary_tsv" ]] || continue
  if known "$dir"; then skipped=$((skipped + 1)); continue; fi
  # The log written FIRST, by mtime — the run's start stamp is at the top of
  # whichever configuration launched first, and every one of them carries a
  # stamp of its own (`ls | head` reads a name where this reads a time).
  first_log=""; first_m=0
  for f in "$dir"/*.log; do
    [[ -f "$f" ]] || continue
    m=$(mtime_of "$f")
    if [[ -z "$first_log" ]] || (( m < first_m )); then first_log="$f"; first_m=$m; fi
  done
  [[ -n "$first_log" ]] || continue
  line=$(stamp_line "$first_log")
  rev=$(stamp_rev "$line"); date_str=$(stamp_date "$line"); dirty=$(stamp_dirty "$line")
  [[ -n "$rev" && -n "$date_str" ]] || continue
  epoch=$(to_epoch "$date_str"); [[ -n "$epoch" ]] || continue
  # The selector off the `# env … lein test :SEL` line test-matrix.sh writes,
  # and ONLY that line: clojure.test prints `lein test :only <ns>/<test>` beside
  # every failure, so a grep for `lein test :` over the whole log reads a
  # failure hint as the run's selector — which is how a red `:default` matrix
  # would be filed under a selector nothing ran.  The most common one wins,
  # because a reused output directory can hold logs from two invocations.
  selector=$(grep -hoE '^# env .* lein test :[a-z]+$' "$dir"/*.log 2>/dev/null \
               | sed 's/.*lein test //' | sort | uniq -c | sort -rn | head -1 | awk '{print $2}')
  [[ -n "$selector" ]] || selector=":default"
  total=$(awk -F'\t' 'NR>1 && $1 != "" { n++ } END { print n+0 }' "$summary_tsv")
  (( total > 0 )) || continue
  bad=$(awk -F'\t' 'NR>1 && $4 != "passed" && $1 != "" { n++ } END { print n+0 }' "$summary_tsv")
  # Concurrent runs, so the matrix's wall clock is the span from the first
  # stamp to the last log write, not the sum of the per-config seconds.
  last=0
  for f in "$dir"/*.log; do
    [[ -f "$f" ]] || continue
    m=$(mtime_of "$f"); (( m > last )) && last=$m
  done
  secs=$(( last - epoch )); (( secs < 0 )) && secs=0
  if (( bad == 0 )); then state=passed; else state=failed; fi
  # `roster backfilled` and not a roster name: which group was ASKED for is the
  # one fact these artifacts do not carry, and naming a guess would put a wrong
  # word in a column a reader compares runs on.
  #
  # What RAN is a count, though, and that is the fact the variant needs: a run
  # short of the routine roster is a subset and is filed as one, the same rule
  # test-matrix.sh applies to a live run.  So a backfilled `--owed` run does not
  # land in the column that answers when the whole roster last went green.
  variant="$selector"
  if (( total < ROUTINE_TOTAL )); then variant="$selector owed"; fi
  emit matrix "$variant" "$state" "$secs" "$epoch" "$rev" "$dirty" \
       "$(printf '%d configurations, roster backfilled, %d failed, 0 skipped' "$total" "$bad")" \
       "$dir"
done

if [[ $DRY -eq 1 ]]; then
  printf 'runlog-backfill: %d row(s) to append, %d already recorded\n' "$added" "$skipped"
else
  printf 'runlog-backfill: %d row(s) appended to %s, %d already recorded\n' \
    "$added" "$RUNLOG_FILE" "$skipped"
fi
exit 0
