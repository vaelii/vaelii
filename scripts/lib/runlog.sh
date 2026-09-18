#!/usr/bin/env bash
# scripts/lib/runlog.sh — one appended row per check run: what ran, at which
# revision, when, for how long, and what it said.
#
# The stage logs already hold every detail, and they are the wrong shape for one
# question: WHICH REVISION was the last one lint / the suite / perf / the matrix
# actually passed at?  Answering that from `target/gate/run-*/` means opening a
# dozen directories, reading each one's first line for the revision, and guessing
# at the verdict from the tail — and `target/` is deleted by `lein clean`, so the
# history goes with it.  So each runner appends one row here as it exits.
#
# The ledger is a LEDGER: append-only, one row per run, never rewritten.  A row is
# a fact about a run that finished, so a re-run at the same revision adds a row
# rather than replacing one, and reading "the last lint" is reading the last row
# with that kind.
#
# `logs/runs.tsv`, not `target/`: `lein clean` empties target between runs, and a
# run history that a build step deletes is not a history.  `logs/` is gitignored,
# so the ledger is per checkout — which is what it describes.
#
# The columns, and why each one is in the row rather than derivable:
#
#   started    ISO 8601 local time, the column a reader scans
#   epoch      the same instant, sortable and diffable without a date parser
#   seconds    wall clock; a run killed halfway is `interrupted`, not a fast pass
#   kind       lint | test | perf | matrix | reflect
#   variant    the selector or roster this run was: `:default`, `:all`, `full`,
#              `owed`, or `-` where the kind has no axis.  A `:default` suite and
#              an `:all` suite are different verdicts and must not overwrite
#              each other's "last run"
#   state      passed | failed | interrupted
#   revision   the short hash the run STARTED at.  Not HEAD-at-read-time: the
#              tree moves under a 35-minute matrix, and the verdict belongs to
#              the tree that was compiled
#   dirty      files under src/ or test/ uncommitted when it started.  A green
#              row over a dirty tree answers for no commit at all, and a reader
#              cannot tell without this column
#   subject    the revision's commit subject, so a reader placing a row in the
#              history does not have to go to git for every one
#   summary    the run's own closing figures — check counts, test and assertion
#              totals, configurations
#   log        where the full output is, relative to the repo root
#
# Sourced, never executed, and it reads only its arguments and the repository —
# `revision.sh`'s rule, so any runner can take this without taking anything else.
# It sources `revision.sh` itself when the caller has not.
#
#   . scripts/lib/runlog.sh
#   runlog_start                       # stamps the revision and the clock
#   … run the thing …
#   runlog_record <kind> <variant> <state> <summary> <log>

# shellcheck source=scripts/lib/revision.sh
if ! declare -f revision_hash >/dev/null 2>&1; then
  . "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/revision.sh"
fi

RUNLOG_FILE="${RUNLOG_FILE:-logs/runs.tsv}"
RUNLOG_COLUMNS=$'started\tepoch\tseconds\tkind\tvariant\tstate\trevision\tdirty\tsubject\tsummary\tlog'

# Captured at the START of a run, because that is the tree the run is a verdict
# about.  Reading them at the end would credit a 35-minute matrix to whatever
# landed while it went (scripts/lib/revision.sh says what that cost once).
runlog_start() {
  RUNLOG_EPOCH=$(date '+%s')
  RUNLOG_STARTED=$(date '+%Y-%m-%dT%H:%M:%S')
  RUNLOG_REV=$(revision_hash)
  RUNLOG_DIRTY=$(revision_dirty)
  RUNLOG_SUBJECT=$(git log -1 --pretty=%s 2>/dev/null || echo '')
}

# Tabs and newlines are the record separator, so a subject or summary carrying
# one would silently add a column or a row.  Squashed to spaces here rather than
# quoted, because every reader of a TSV that quotes is a reader that has to
# unquote.
runlog_clean() {
  printf '%s' "$1" | tr '\t\n\r' '   ' | sed 's/  */ /g; s/^ //; s/ $//'
}

# runlog_record <kind> <variant> <state> <summary> <log>
#
# Never fails the caller: a run's verdict does not depend on whether its row got
# written, and a ledger write that could fail a green gate is a ledger nobody
# keeps.  Every step is guarded and the function always returns 0.
runlog_record() {
  local kind="${1:-?}" variant="${2:--}" state="${3:-?}" summary="${4:-}" log="${5:--}"
  local secs
  [[ -n "${RUNLOG_EPOCH:-}" ]] || runlog_start
  # Wall clock from the epoch stamp, never from `$SECONDS`: several of these
  # runners reset `SECONDS` to time an inner step (`scripts/lint.sh`'s `check`
  # does it per check), so a duration read from it is the last step's, not the
  # run's.
  secs=$(( $(date '+%s') - RUNLOG_EPOCH ))

  mkdir -p "$(dirname "$RUNLOG_FILE")" 2>/dev/null || return 0
  # The header goes in once, when the file is created.  A reader keys on the
  # column names rather than on position, so adding a column later does not
  # need the old rows rewritten — it needs this line to have been there.
  [[ -s "$RUNLOG_FILE" ]] || printf '%s\n' "$RUNLOG_COLUMNS" >>"$RUNLOG_FILE" 2>/dev/null || return 0

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${RUNLOG_STARTED:-}" "${RUNLOG_EPOCH:-0}" "$secs" \
    "$kind" "${variant:--}" "$state" \
    "${RUNLOG_REV:-no-git}" "${RUNLOG_DIRTY:-0}" \
    "$(runlog_clean "${RUNLOG_SUBJECT:-}")" \
    "$(runlog_clean "$summary")" \
    "$(runlog_clean "$log")" \
    >>"$RUNLOG_FILE" 2>/dev/null || return 0
  return 0
}

# runlog_prune <dir> <keep> — keep the newest <keep> `run-*` entries under <dir>.
#
# The ledger is append-only and small; the LOGS it points at are not, so the
# directories rotate.  A row whose log has been pruned still carries the
# verdict, the revision and the figures — which is the point of the row being
# separate from the log.  Anything touched in the last day is kept whatever the
# count, so a concurrent run is never a candidate (test-matrix.sh's rule).
runlog_prune() {
  local dir="${1:-}" keep="${2:-20}" entry i=0
  [[ -n "$dir" && -d "$dir" ]] || return 0
  while IFS= read -r entry; do
    i=$((i + 1))
    (( i <= keep )) && continue
    # `find -mmin -1440` on the entry itself: a live run's log was written to
    # minutes ago, so this is what keeps one from being pruned.  Newest first by
    # mtime, and no `mapfile` — bash 3.2 ships as /bin/bash here.
    [[ -n "$(find "$entry" -maxdepth 0 -mmin -1440 2>/dev/null)" ]] && continue
    rm -rf "$entry" 2>/dev/null || true
  done < <(ls -dt "$dir"/run-* 2>/dev/null)
  return 0
}
