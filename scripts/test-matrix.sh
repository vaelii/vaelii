#!/usr/bin/env bash
# scripts/test-matrix.sh — several configurations at once: the nine storage backends
# and the six sweeps, concurrently, with one JVM each.
#
# Minutes where `test-backends.sh` and `test-sweeps.sh` in sequence take an hour.  Same
# runs, same verdicts; what changes is that the box runs more than one of them at a
# time.  **This is the one to run before landing a change that owes the matrix** — a
# change touching storage, the index, records, recovery or overlay (the backend half),
# or inference, the TMS, the planner or context retrieval (the sweep half).  The two
# single-axis scripts remain, and are what to reach for when you want one axis, one
# config, or a readable per-run wall time.
#
# RUN WHAT THE CHANGE OWES, NOT EVERYTHING.  `--owed` reads the changed files and runs
# the configurations that could disagree about them, printing the classification as it
# goes; `scripts/lib/suite-configs.sh` carries the map and the reason each row is what
# it is.  A bare run is the ROUTINE roster — thirteen of the fifteen, the two
# durable-records-with-a-derived-index pairs that are a third copy of one claim sitting
# out — and `full` is the fifteen, which is what a release runs and what a change to
# the record/index boundary itself owes.  Every run names what did not run, on the header
# and again on the verdict.
#
# WHY CONCURRENT IS SAFE, given both of those scripts are sequential on purpose:
#
#   - **The in-memory registry is per JVM.**  Two runs over the same space number do not
#     collide, which is the same fact `test-parallel.sh` shards on.
#   - **A durable run's store path is `<vaelii.disk.dir>/space-<n>`**
#     (`impl/disk/backend.clj`), and every config here gets its own `vaelii.disk.dir`
#     under this run's output directory.  Distinct directories, so the single-writer
#     lock is never contended and the six-block `VAELII_TEST_SPACE` limit — which is
#     about sharing one directory — never binds.
#   - **No test asserts an elapsed-time bound.**  Contention costs wall clock and cannot
#     cost a verdict, which is what makes a dozen suites on ten cores a scheduling
#     question rather than a correctness one.
#
# WHAT IT COSTS.  A run's wall time here is a function of what else was running, so it
# is not a measurement — read `lein perf` for those, and never while this is going.  The
# per-namespace progress the single-axis scripts print is dropped too: a dozen
# interleaved streams are not readable.  On a terminal you get instead a LIVE DASHBOARD,
# repainted in place, in which COMMAND LINES AND BARS ALTERNATE: a configuration that is
# running shows the command that runs THAT configuration and nothing else, its log file
# after the `#`, and then a bar on its own line filling as its suite reaches namespaces.
# A bar shares its line with nothing, which is what keeps a frame inside the terminal's
# width; the bars are green until something fails and red after.  Off a terminal (a pipe,
# a redirect, CI, `SUITE_PROGRESS=lines`) that would be cursor-motion noise in a log, so
# those get the scrolling form: a line per configuration as it starts and finishes, and a
# heartbeat naming how far each running config has got.
#
# LONGEST FIRST.  Whoever starts last sets the finish, so the last thing to start has to
# be the shortest thing there is: the durable five take ~10-12 minutes under a full box
# against ~4-5 for the rest, and a 4-minute sweep starting at minute nine outlasts a
# 12-minute disk run that started at zero.  Order comes from the previous run's measured
# seconds (`logs/test-matrix/config-timings.tsv`, per checkout), and from a
# durable-is-slower prior before anything has been measured.
#
# WHAT FAILED, AND WHETHER IT IS THE SUITE'S ANSWER.  A red run names the failing TESTS
# rather than their namespaces, and the report closes with those tests rolled up across
# configurations: a test that failed under every run is the suite's answer at this
# revision, and one that failed under only some is a difference between configurations —
# which is the finding, and the reason there is more than one run.  Every row is in
# `failures.tsv` whatever the console prints, and the console shrinks its shape as the
# count grows: blocks under nine, a line each under thirty, a count past that.
#
# THE TREE MOVING UNDER IT.  Several agents write this checkout, and a matrix is long
# enough for two commits.  Every config records the revision it compiled, and the
# report at the end says whether they all compiled the same one — and if not, lists the
# commits that landed, marks the ones that touched `src/` or `test/`, and names which
# configs are on which side.  **A red run under a commit you did not write is that
# commit's to answer for.**  Report it, re-run that one config, and carry on; the matrix
# is owed by whoever landed the change, not by whoever happened to be running it.  A
# tree that was already dirty when the matrix started is the worse case and says so:
# uncommitted work compiled into every run, and the result answers for no commit
# at all.
#
# **Do not edit the tree while this is running**, and the revision a config compiled is
# not the whole of why.  A namespace is compiled once at boot, so an edit after that
# cannot reach a run already going — but a test that reads a file at RUN time does see
# it: `config_surface_test` slurps `docs/operations.md` while its own roster is already
# compiled, so editing that doc mid-matrix moved one run's failure count and not
# another's.  The failing set stayed identical, which is the property that matters, and
# the count is what somebody reads first.  The dirty-by-the-end line says this happened;
# it cannot say what it cost.
#
# Usage:
#   ./scripts/test-matrix.sh                  # the routine roster, :default
#   ./scripts/test-matrix.sh --owed           # only what the changed files owe
#   ./scripts/test-matrix.sh --owed -n        # ...and print that set without running it
#   ./scripts/test-matrix.sh --owed=<ref>     # ...measuring the change from <ref> instead
#   ./scripts/test-matrix.sh full             # all fifteen — a release, or a protocol change
#   ./scripts/test-matrix.sh full :all        # ...with the ^:slow half — before a tag
#   ./scripts/test-matrix.sh backends         # one axis (also: sweeps, routine, full)
#   ./scripts/test-matrix.sh memory disk-log rete   # only these
#   ./scripts/test-matrix.sh --jobs 4         # fewer at a time, on a box you are using
#   ./scripts/test-matrix.sh --keep           # keep each durable run's scratch directory
#   ./scripts/test-matrix.sh --fail-fast      # launch nothing new once one has failed
#   ./scripts/test-matrix.sh --ordered        # longest first, not shuffled
#   TEST_MATRIX_SEED=42 ./scripts/test-matrix.sh   # replay a given shuffle
#
# Env:
#   TEST_MATRIX_OUT   log directory (default logs/test-matrix/run-<pid>, outside target/
#                     so a concurrent build's clean cannot delete a live run)
#   MATRIX_KEEP_RUNS  past run dirs to keep (default 20); a run touched in the last 24h is
#                     never pruned regardless, so a parallel run is never a candidate
#   MATRIX_JOBS       how many at a time (default: scripts/lib/slots.sh)
#   TEST_MATRIX_SEED  the shuffle seed (default: a fresh one, reported per run), the
#                     counterpart of `test-shuffle.sh`'s TEST_SHUFFLE_SEED.  A seed
#                     replays an order within one script and not across the two: the
#                     rosters differ, and `test-shuffle.sh` pins memory first.
#                     `--ordered` ignores the seed.
#   MATRIX_JVM_OPTS   extra JVM_OPTS for every run.  Empty by default.  On a loaded box
#                     `-XX:ActiveProcessorCount=2` is the one worth trying — each JVM
#                     otherwise sizes its GC and JIT pools from all ten cores while
#                     doing one core of work — but measure it rather than believing it.
#                     It lands in each log's own `# env … lein test …` line either way,
#                     so a run stays reproducible by copying that line.
#   MATRIX_HEARTBEAT  seconds between scrolling progress lines when NOT on a terminal
#                     (default 60; 0 turns them off).  The live dashboard ignores it —
#                     it repaints every second — and `SUITE_PROGRESS=lines` is what
#                     turns the dashboard off in favour of the heartbeat on a terminal.
#
# ^C stops every running suite and then the script.
#
# Exit: 0 when every configuration run passed (and 0 with nothing run when `--owed`
# finds nothing owed, which it says), 1 when one failed, 130 when interrupted.  A tree
# that moved does not change the exit status — it is a fact about the runs, not a
# verdict on them, and a green matrix across two revisions is still that many green runs.

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# leiningen's own terminal state, handed down first by the alias: lein-shell pipes
# this script's stdout, so `-t 1` (in suite-marks.sh, sourced below) would say "not a
# terminal" and the live dashboard would fall back to the scrolling heartbeat even
# with someone watching.  Absent when run directly, where `-t 1` stands.
case "${1:-}" in
  --tty)    SUITE_TTY=1; shift ;;
  --no-tty) SUITE_TTY=0; shift ;;
esac

# colours, `hms`, the log readers, and — through it — the revision helpers
# shellcheck source=scripts/lib/suite-marks.sh
. scripts/lib/suite-marks.sh
# shellcheck source=scripts/lib/suite-configs.sh
. scripts/lib/suite-configs.sh
# the default slot count, shared with test-parallel.sh so the rule cannot drift
# shellcheck source=scripts/lib/slots.sh
. scripts/lib/slots.sh
# one row in `logs/runs.tsv` per matrix: the revision, the clock, the roster and the
# verdict.  `summary.tsv` beside each run holds the per-configuration detail; this is
# the one line that says WHICH REVISION the matrix last went green at, without
# opening two dozen run directories to find it
# shellcheck source=scripts/lib/runlog.sh
. scripts/lib/runlog.sh

# The live dashboard — a repainted frame in which each configuration's command line and
# its bar alternate — runs on a terminal.  A pipe, a redirect or CI gets the scrolling
# heartbeat lines instead: a log wants those, and cursor motion painted into one is
# noise.  `SUITE_PROGRESS=lines` forces the heartbeat on a terminal too.
if (( IS_TTY )) && [[ "$PROGRESS" == marks ]]; then LIVE=1; else LIVE=0; fi

# ---- how wide, and how tall ---------------------------------------------------
#
# A BAR GETS ITS OWN LINE, alternating with the `command # log` line above it, and the
# reason is arithmetic rather than taste.  **NO LINE MAY EXCEED `COLS`.**  A line that
# does is two screen rows where the frame counts one, and the `\033[<n>A` that repaints
# it then moves up one row short — every second, so the dashboard walks down the screen
# leaving a trail of itself.  A bar sharing its line with a command and an absolute log
# directory cannot be held under that bound: the directory alone runs to about fifty
# columns and the command to eighteen, which leaves an 80-column terminal no room for a
# bar at all.  So a bar shares its line with nothing, every line is clamped, and `BLOCK`
# is counted from the rows actually painted rather than assumed.
#
# `BARW` is the COMPACT layout's bar — the one that does share its line, with a name and
# a count of known width, so a constant is enough for it.  The alternating layout sizes
# each bar from the text beside it instead (`bar_width`): the suffix there carries a
# revision and a clock, and a constant that fits one frame is a constant that overflows
# the next.
BARW=$(( COLS - 46 )); (( BARW < 12 )) && BARW=12; (( BARW > 32 )) && BARW=32

# How many cells are left for a bar once its indent and the text after it are spoken
# for.  The suffix is ASCII — counts, a clock, a revision — so its length is its width,
# which is exactly why the bar is sized from it and not the other way round.  The
# leading `- 1` is the column of headroom a terminal that wraps ON the last cell needs.
bar_width() {                                      # bar_width <indent> <suffix>
  local w=$(( COLS - 1 - $1 - 2 - ${#2} ))
  (( w < 12 )) && w=12
  (( w > 56 )) && w=56
  printf '%s' "$w"
}

# `ROWS` and `COLS` are suite-marks', measured off `/dev/tty` where there is one.  The
# height settles one decision here: a frame taller than the terminal cannot be repainted
# in place at all — it scrolls, and every cursor-up lands somewhere it did not mean to —
# so `redraw` measures its frame against `ROWS` and falls back to the compact
# one-line-per-configuration form rather than painting a broken one.

SELECTOR=":default"
JOBS="${MATRIX_JOBS:-}"
KEEP=0
FAIL_FAST=0
OWED=0
OWED_BASE=""
DRY=0
SHUFFLE=1
HEARTBEAT="${MATRIX_HEARTBEAT:-60}"
WANTED=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --jobs) [[ $# -ge 2 ]] || { echo "test-matrix: --jobs needs a value" >&2; exit 2; }
            JOBS="$2"; shift 2 ;;
    --jobs=*) JOBS="${1#*=}"; shift ;;
    --keep) KEEP=1; shift ;;
    --fail-fast) FAIL_FAST=1; shift ;;
    # the launch order: shuffled by default, longest-first on request.  The block that
    # orders the roster below says what each costs.
    --ordered) SHUFFLE=0; shift ;;
    --owed) OWED=1; shift ;;
    # a ref rather than a bare flag, so it cannot be confused with the positional
    # configuration names: `--owed main` would read as "--owed, and also run `main`",
    # which is not a configuration and would abort with a puzzling message
    --owed=*) OWED=1; OWED_BASE="${1#--owed=}"
              [[ -n "$OWED_BASE" ]] || { echo "test-matrix: --owed= needs a commit" >&2; exit 2; }
              # resolved here rather than at the diff, where a bad ref is a silent
              # empty change set and reads as "this change owes nothing"
              git rev-parse --verify --quiet "${OWED_BASE}^{commit}" >/dev/null || {
                echo "test-matrix: --owed=$OWED_BASE is not a commit this repository has" >&2
                exit 2; }
              shift ;;
    -n|--dry-run) DRY=1; shift ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    :all|:slow|:default) SELECTOR="$1"; shift ;;
    :*) echo "unknown selector $1 (:all, :slow, :default)" >&2; exit 2 ;;
    -*) echo "unknown flag $1 (try --help)" >&2; exit 2 ;;
    # a GROUP word first — `config_group` is the only thing that knows one, so a name
    # in neither table is refused by the branch below rather than run as nothing
    *) if config_group "$1" >/dev/null 2>&1 || config_kind "$1" >/dev/null; then
         WANTED+=("$1")
       else
         echo "unknown configuration $1" >&2
         echo "  backends: ${ALL_BACKENDS[*]}" >&2
         echo "  sweeps:   ${ALL_SWEEPS[*]}" >&2
         echo "  groups:   backends sweeps routine full" >&2
         exit 2
       fi
       shift ;;
  esac
done

# ---- --owed: the configurations THIS working tree's changes owe ---------------
#
# Every changed file put to `config_owed_for_path` (scripts/lib/suite-configs.sh, which
# carries the map and the reason each row is what it is), and the union run.  Changed
# means: uncommitted, untracked, and — when the branch has an upstream — every commit
# not yet on it, since a matrix is owed by the change and not by whether it is committed
# yet.
#
# `--owed=<ref>` names the baseline instead, and the case for it is the default's blind
# spot: "not yet upstream" is empty the moment you push, so a change committed and pushed
# in pieces — which is the cadence this repo asks for — owes nothing by the time anybody
# asks.  The matrix is still owed; only the question went stale.  `--owed=<ref>` measures
# from a commit you name, so `--owed=origin/main@{1}` or `--owed=<the commit before your
# first>` answers what the work owes rather than what is left un-pushed.  Uncommitted and
# untracked files are still included: the baseline moves, the working tree still counts.
#
# The classification is PRINTED, one line per file that owes something, because a floor
# somebody cannot see is a floor they cannot correct: a file whose row is wrong is
# visible here and nowhere else.  Files owing nothing are a count, not a column.
owed_changed_paths() {
  { git diff --name-only HEAD
    git ls-files --others --exclude-standard
    if [[ -n "$OWED_BASE" ]]; then
      git diff --name-only "$OWED_BASE...HEAD"
    else
      local up
      up=$(git rev-parse --abbrev-ref --symbolic-full-name '@{upstream}' 2>/dev/null) \
        && git diff --name-only "$up...HEAD"
    fi
  } 2>/dev/null | sort -u
}

if (( OWED )); then
  quiet=0
  while IFS= read -r path; do
    [[ -n "$path" ]] || continue
    got=$(config_owed_for_path "$path")
    if [[ -n "$got" ]]; then
      printf '  %s%-44s%s %s\n' "$DIM" "$path" "$OFF" "$got"
      # deliberately unquoted: a row is a space-separated list of names and groups
      # shellcheck disable=SC2206
      WANTED+=($got)
    else
      quiet=$((quiet + 1))
    fi
  done < <(owed_changed_paths)
  (( quiet > 0 )) && echo "  ${DIM}${quiet} other changed file(s) owe no configuration${OFF}"
  if [[ ${#WANTED[@]} -eq 0 ]]; then
    echo "${GREEN}these changes owe the matrix no configuration${OFF}" \
         "${DIM}— nothing here swaps a store or an implementation, so \`lein gate\` is the gate${OFF}"
    exit 0
  fi
fi

# A bare run is the ROUTINE roster, not every configuration: `routine` in
# scripts/lib/suite-configs.sh says which two sit out and why, and the header below
# names them every time, because a roster that quietly shrank is a matrix that means
# less than the word does.
if [[ ${#WANTED[@]} -eq 0 ]]; then WANTED=(routine); fi
# What this run calls its roster, for the ledger row.  `--owed` names itself rather
# than listing the configurations it resolved to: the set is a function of the diff,
# so the word is the reproducible thing and the list is in `summary.tsv`.
if (( OWED )); then ROSTER_LABEL="owed"; else ROSTER_LABEL="${WANTED[*]}"; fi
CONFIGS=()
while IFS= read -r c; do CONFIGS+=("$c"); done < <(expand_configs "${WANTED[@]}")
[[ ${#CONFIGS[@]} -gt 0 ]] || { echo "no configurations selected" >&2; exit 2; }

# What is NOT running, in the full roster's order — read once here and printed with the
# header and again with the verdict.  Uniform across every way of choosing: a bare run,
# a group, `--owed` and a hand-named list all answer the same question the same way.
SAT_OUT=()
for c in "${ALL_BACKENDS[@]}" "${ALL_SWEEPS[@]}"; do
  running=0
  for r in "${CONFIGS[@]}"; do [[ "$c" == "$r" ]] && { running=1; break; }; done
  (( running )) || SAT_OUT+=("$c")
done
ROSTER_TOTAL=$(( ${#ALL_BACKENDS[@]} + ${#ALL_SWEEPS[@]} ))
# The routine roster's size, which is the floor a run has to reach to be filed as
# the matrix rather than as a subset (see the ledger row at the end).
ROUTINE_TOTAL=$(( ROSTER_TOTAL - ${#ROUTINE_SKIP[@]} ))

# WHAT THIS ROSTER COVERS: `full` where nothing sits out, `routine` where the only
# ones sitting out are the two the routine roster leaves out, empty otherwise.  A
# subset that covers the routine roster answers the matrix column's question as
# well as its own — `--owed` on a change that owes everything runs a wider roster
# than a bare `lein test-matrix` does — so the ledger row below names it and the
# tool reading the row files it under both columns.
COVERS=""
covered=1
# `${SAT_OUT[@]+...}` because bash 3.2 — which is what macOS ships — treats an empty
# array expanded as `"${a[@]}"` under `set -u` as an unbound variable.  SAT_OUT is empty
# exactly when the roster leaves nothing out, so a `--owed` set covering all
# $ROSTER_TOTAL configurations is the case that reaches it.
for c in ${SAT_OUT[@]+"${SAT_OUT[@]}"}; do
  optional=0
  for s in "${ROUTINE_SKIP[@]}"; do [[ "$c" == "$s" ]] && { optional=1; break; }; done
  (( optional )) || { covered=0; break; }
done
if (( covered )); then
  if [[ ${#SAT_OUT[@]} -eq 0 ]]; then COVERS="full"; else COVERS="routine"; fi
fi

# THE LAUNCH ORDER, of which there are two: a SHUFFLE, which is the default, and
# LONGEST FIRST under `--ordered`.
#
# Shuffled, for the reason `test-shuffle.sh` shuffles its walk.  A slot count under the
# configuration count means somebody starts in a second wave, and a fixed order picks the
# same first wave every time — so a matrix stopped early, by `--fail-fast` or by ^C or by
# the box, has always covered the same prefix and never the rest.  A random order reaches
# a different set first on each run, and the seed is printed, so an order worth having
# again is replayed with `TEST_MATRIX_SEED=<n>`.
#
# Longest first is what a slot count under the configuration count would otherwise want,
# because whoever starts last sets the wall clock: the last thing to start should be the
# shortest thing there is.  Measured: the durable five take ~10-12 minutes under a full
# box against ~4-5 for the rest, and a 4-minute sweep starting at minute nine finishes
# after the 12-minute disk run that started at zero.  That is the whole difference
# between 13 minutes and 12, which is the price the shuffle pays and `--ordered` does
# not.  Reach for `--ordered` when the wall clock is what you are spending.
#
# Weights come from the last run in this checkout (`config-timings.tsv`, kept beside the
# run directories and shared by every run, the way `gate.sh` keeps its shard timings) and
# fall back to a prior when there are none: a durable record store writes files and is
# slower, which is a fact about the configuration rather than about the machine, so it is
# safe to assume before anything has been measured.  `test-parallel.sh` bin-packs from
# measurement for the same reason and with the same fallback.  Every run records its
# seconds either way, so `--ordered` reads the timings a shuffled run wrote.
# Run logs live under logs/, NOT target/.  A concurrent `lein clean` — or the auto-clean
# lein runs before a compile/uberjar/coverage task — wipes all of target/, and a live
# matrix run's per-configuration logs and disk scratch sit inside its run directory.  logs/
# is gitignored and no lein task touches it, so a run in one checkout survives a build in
# another.  `prune_old_runs` (below) is the only thing that deletes a run dir now.
MATRIX_ROOT="logs/test-matrix"
MATRIX_TIMINGS="$MATRIX_ROOT/config-timings.tsv"
order_longest_first() {
  local c w
  for c in "${CONFIGS[@]}"; do
    w=""
    [[ -r "$MATRIX_TIMINGS" ]] && w=$(awk -F'\t' -v c="$c" '$1 == c { print $2 }' "$MATRIX_TIMINGS" | tail -1)
    if [[ -z "$w" ]]; then
      if config_wants_disk "$c"; then w=600; else w=300; fi
    fi
    printf '%s\t%s\n' "$w" "$c"
  done | sort -k1,1nr -k2,2 | cut -f2        # ties on the name, so the order is content's
}
# The seed is captured even when nobody gave one, so every run prints an order that can
# be run again.  `shuffle_inplace` is scripts/lib/suite-configs.sh's, over the global
# SHUF and in this shell — that file says why a subshell would make the seed a lie.
SEED="${TEST_MATRIX_SEED:-$RANDOM}"
RANDOM=$SEED
ORDERED=()
if (( SHUFFLE )); then
  ORDER_LABEL="shuffled"
  SHUF=("${CONFIGS[@]}")
  shuffle_inplace
  ORDERED=("${SHUF[@]}")
else
  ORDER_LABEL="longest first"
  while IFS= read -r c; do ORDERED+=("$c"); done < <(order_longest_first)
fi
CONFIGS=("${ORDERED[@]}")

# Slots default from `scripts/lib/slots.sh` — the same rule `test-parallel.sh` shards by:
# half the performance cores, less the vaelii JVMs already running on the box.  Each run is
# about one core of test work, so a slot count near the core count keeps every core busy
# while leaving the box usable; more slots than cores does not go faster and costs another
# JVM's memory each.  slots.sh says why it is P/2 (not `cores - 2`) and load-aware.
[[ -z "$JOBS" ]] && JOBS=$(default_slots)
[[ $JOBS -gt ${#CONFIGS[@]} ]] && JOBS=${#CONFIGS[@]}

# `-n` prints the plan and runs nothing — what `--owed` selected, in the order it would
# start them, at the slot count it would use.  A matrix is minutes to an hour, so the
# question "is this the right set?" wants an answer before it, not after.
if (( DRY )); then
  echo "${BOLD}${#CONFIGS[@]} of $ROSTER_TOTAL configuration(s), $JOBS at a time${OFF}" \
       "${DIM}$SELECTOR${OFF}"
  [[ ${#SAT_OUT[@]} -gt 0 ]] && echo "${DIM}not run: ${SAT_OUT[*]}${OFF}"
  (( SHUFFLE )) && echo "${DIM}seed $SEED  (TEST_MATRIX_SEED=$SEED to replay this order)${OFF}"
  echo "${DIM}${ORDER_LABEL}:${OFF}"
  for c in "${CONFIGS[@]}"; do
    printf '  %-16s %s%s%s\n' "$c" "$DIM" "env $(config_env "$c") lein test $SELECTOR" "$OFF"
  done
  exit 0
fi

# Keep a generous tail of past run directories and never delete a recent one.  Nothing
# pruned before — a stray `lein clean` did the deleting instead, and took live runs with it
# (their logs live under target/ no longer, see MATRIX_ROOT above).  Delete only a run dir
# that is BOTH beyond the newest `keep` AND untouched for over a day: a run still in progress
# — in this checkout or a parallel one — is touched within the day, so it is never a
# candidate.  Newest-first by mtime; bash 3.2 ships as /bin/bash, so no `mapfile`.
prune_old_runs() {
  local root="$1" keep="$2" d i=0
  [[ -d "$root" ]] || return 0
  while IFS= read -r d; do
    i=$((i + 1))
    (( i <= keep )) && continue
    [[ -n "$(find "$d" -maxdepth 0 -mmin -1440 2>/dev/null)" ]] && continue
    rm -rf "$d"
  done < <(ls -dt "$root"/run-* 2>/dev/null)
}

# A run owns its directory — `gate.sh` and `test-backends.sh`, same reason: two matrices
# in one checkout must not interleave a log or delete each other's live disk scratch.
# MATRIX_ROOT is set above (under logs/, so no lein clean can reach a live run).
mkdir -p "$MATRIX_ROOT"                        # a fresh checkout has no logs/ yet
if [[ -n "${TEST_MATRIX_OUT:-}" ]]; then
  OUT_DIR="$TEST_MATRIX_OUT"; mkdir -p "$OUT_DIR"
else
  prune_old_runs "$MATRIX_ROOT" "${MATRIX_KEEP_RUNS:-20}"
  OUT_DIR="$MATRIX_ROOT/run-$$"; mkdir -p "$OUT_DIR"
  ln -sfn "$(basename "$OUT_DIR")" "$MATRIX_ROOT/latest" 2>/dev/null || true
fi
# absolute, so the reproducer header's `# <dir>` pastes from any directory rather than
# only from the checkout root.  The dir exists by now (mkdir above), so the `cd` holds.
ABS_OUT_DIR=$(cd "$OUT_DIR" 2>/dev/null && pwd) || ABS_OUT_DIR="$OUT_DIR"

RUN_NS_COUNT=$(selected_ns_count "$SELECTOR")

# ^C stops every running suite and then the script.  `set -m` puts each job in its own
# process group so one signal reaches everything a run is — the `lein` wrapper, its JVM
# and the project JVM it forks — rather than killing the wrapper and orphaning the JVM
# that holds the CPU.  `test-backends.sh` carries the long form.
set -m
FAILED=()
n=${#CONFIGS[@]}

# ---- the plan, for a reader watching this run go ------------------------------
#
# A run that has started says nothing about itself until it ends: the ledger row
# is written at exit, and the run directory holds only whichever configuration
# logs have been opened so far.  A watcher then cannot tell a `--owed` run of
# three from a `full` run whose other twelve have not started, and cannot tell
# how far along either is.  So state it once, here, where all three facts are
# settled and none of them can change.
#
# Written before the first configuration launches and never rewritten.  The
# verdict is still `summary.tsv`'s and the ledger row's; this is the intention,
# and a run that is killed leaves it behind saying what it had meant to do.
{
  printf 'selector\t%s\n' "$SELECTOR"
  printf 'roster\t%s\n' "$ROSTER_LABEL"
  printf 'configs\t%d\n' "$n"
  printf 'of\t%d\n' "$ROSTER_TOTAL"
  # the routine roster's size, which is the floor the ledger row below files a
  # run as a subset under.  Written here so a watcher decides the variant the
  # way this script decides it, rather than on the roster word alone — the two
  # rules disagreed on a hand-named short list, and a run changed column as it
  # finished.
  printf 'routine\t%d\n' "$ROUTINE_TOTAL"
  # what this roster covers, where it covers one.  The INTENTION, like the rest of
  # the plan: a run interrupted with configurations still to go covers whatever it
  # reached, and the ledger row at the end is what says so.
  [[ -n "$COVERS" ]] && printf 'covers\t%s\n' "$COVERS"
  # the order and the seed that chose it, so a run reproduced from this file runs the
  # configurations in the order this one did
  printf 'order\t%s\n' "$ORDER_LABEL"
  (( SHUFFLE )) && printf 'seed\t%s\n' "$SEED"
  printf 'sequence\t%s\n' "${CONFIGS[*]}"
} > "$OUT_DIR/matrix.plan" 2>/dev/null || true

# Which PROCESS GROUP each configuration runs in, one row appended by `launch` as
# that configuration starts.  Nothing else can say which configuration a JVM is
# running: a configuration is chosen by the environment variables `launch` passes
# its subshell, and an environment never reaches a command line — so a process
# table alone tells thirteen matrix JVMs apart by pid and by nothing else, and
# vaelii-top's JVM tile (the vaelii-tools repository) had to repeat this run's progress on every one of
# them.  `set -m` puts each configuration's subshell in a group of its own, and
# the launcher JVM and the project JVM it trampolines into both carry it, so the
# group names both.
#
# Appended as the run goes and not written with `summary.tsv` at the end, because
# a reader watching a run is the only reader it has.  A relaunched configuration
# appends a second row; the group the first names is gone by then, so both stand.
printf 'config\tpid\tpgid\tlog\n' > "$OUT_DIR/configs.tsv" 2>/dev/null || true
state=(); pid=(); pgid=(); rev=(); logf=(); startt=(); secs=(); diskd=(); fin=()
for ((i = 0; i < n; i++)); do state[i]=queued; pid[i]=0; pgid[i]=0; secs[i]=0; diskd[i]=""; fin[i]=""; done

# ---- the per-row reproducer ---------------------------------------------------
#
# What each dashboard row is labelled with: the command that runs THAT configuration
# and nothing else.  A row's name alone answers "which one is slow"; the command
# answers the question a red row actually raises, which is "how do I run just this
# again", and it is the same question the header's `lein lint` / `lein test` lines are
# there to answer for the matrix as a whole.
#
# `lein test-matrix <cfg>` rather than the env-prefixed `lein test` it expands to.  Both
# run the one configuration; only this one fits — the tactician row's environment is two
# assignments and 84 columns before a log path is appended, and a label that wraps is the
# defect this layout exists to fix.  It is also the spelling the docs teach.
row_cmd() {                                        # row_cmd <config>
  if [[ "$SELECTOR" == ":default" ]]; then printf 'lein test-matrix %s' "$1"
  else printf 'lein test-matrix %s %s' "$1" "$SELECTOR"; fi
}

# One label column for every row including the header's, so the `#` comments line up
# down the whole frame.  Measured rather than guessed: which configurations run is
# decided at runtime, and `--owed` can pick any subset of names of any length.
CMD_W=$(( ${#SELECTOR} + 11 ))                     # `lein test <selector>`
rcmd=()
for ((i = 0; i < n; i++)); do
  rcmd[i]=$(row_cmd "${CONFIGS[i]}")               # once, not once a second: `redraw`
  (( ${#rcmd[i]} > CMD_W )) && CMD_W=${#rcmd[i]}   # repaints at 1 Hz and a command
done                                               # substitution there is a fork a row
(( CMD_W > COLS - 24 )) && CMD_W=$(( COLS - 24 ))  # a narrow terminal wins the argument

# shellcheck disable=SC2317,SC2329  # invoked from the INT/TERM trap below
stop_all() {
  local i
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == running ]] || continue
    [[ "${pgid[i]}" -gt 0 ]] && kill -TERM -"${pgid[i]}" 2>/dev/null
  done
  for _ in $(seq 1 20); do
    local alive=0
    for ((i = 0; i < n; i++)); do
      [[ "${state[i]}" == running && "${pgid[i]}" -gt 0 ]] || continue
      kill -0 -"${pgid[i]}" 2>/dev/null && alive=1
    done
    [[ $alive -eq 0 ]] && return 0
    sleep 0.25
  done
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == running && "${pgid[i]}" -gt 0 ]] && kill -KILL -"${pgid[i]}" 2>/dev/null
  done
}

# shellcheck disable=SC2317,SC2329  # ditto — `trap on_interrupt INT TERM`
on_interrupt() {
  trap - INT TERM
  echo; echo "  ${RED}^C${OFF} ${DIM}stopping every running suite${OFF}"
  { stop_all; } 2>/dev/null
  echo "  ${DIM}partial logs in $OUT_DIR/${OFF}"
  exit 130
}
trap on_interrupt INT TERM

# The log a config writes.  `<config>.log` belongs to the routine run; any other
# selector says which it was, so a `:slow` pass sits beside a `:default` one.
log_for() {
  if [[ "$SELECTOR" == ":default" ]]; then printf '%s/%s.log' "$OUT_DIR" "$1"
  else printf '%s/%s%s.log' "$OUT_DIR" "$1" "${SELECTOR/:/.}"; fi
}

# How many namespaces a running config has reached — `lein test` prints one header per
# namespace before running it, so counting them is the progress the heartbeat reports.
ns_reached() {
  local c                                          # `grep -c` prints 0 and exits 1, so
  c=$(grep -acE '^lein test [A-Za-z0-9._-]+$' "$1" 2>/dev/null)   # no `|| echo 0` — that
  printf '%s' "${c:-0}"                            # would print the zero twice
}

launch() {                                         # launch <index>
  # two `local`s, not one: a `local a=$1 b=${x[$a]}` expands every word before the
  # builtin runs, so `b` would index with the CALLER's `a`
  local i="$1"
  local cfg="${CONFIGS[$i]}" log envv=() opts
  log=$(log_for "$cfg"); logf[i]="$log"
  # as an `env` argument list rather than an assignment prefix: a prefix is recognized
  # before expansion, so one built from a variable cannot be used.  Word-splitting is
  # what is wanted — the tactician row is two assignments and neither holds a space.
  # shellcheck disable=SC2207
  envv=( $(config_env "$cfg") )
  opts="${MATRIX_JVM_OPTS:-}"
  if config_wants_disk "$cfg"; then
    # `.noindex` SUFFIX, NOT A MARKER FILE.  A durable config's store is thousands of
    # record-log and idx writes per run, and `mds_stores` indexing them competes for the
    # device the durable half is already bound on (~20% CPU alongside `fseventsd`,
    # measured during a full matrix).  Spotlight skips a directory whose NAME ends
    # `.noindex`; a `.metadata_never_index` file inside one does nothing on macOS 26 —
    # both were probed against a control, and only the suffix held.  The logs beside it
    # keep their names and stay searchable: it is the scratch that churns, not them.
    diskd[i]="$OUT_DIR/$cfg.disk.noindex"
    rm -rf "${diskd[i]}"
    opts="$opts -Dvaelii.disk.dir=${diskd[i]}"
  fi
  [[ -n "${opts// /}" ]] && envv+=(JVM_OPTS="${opts# }")
  rev[i]=$(revision_hash)                          # what THIS run is about to compile
  startt[i]=$SECONDS
  # revision, then the command verbatim: two lines at the top of every log, so the one
  # config that went red is reproducible by copying its second line.  The console cannot
  # carry it — a dozen launches with a `-Dvaelii.disk.dir=…` each is not a readable
  # column — and the log is where somebody debugging that config is already looking.
  revision_stamp "$cfg" > "$log"
  printf '# env %s lein test %s\n' "${envv[*]}" "$SELECTOR" >> "$log"
  # `< /dev/null` is what keeps it running: `set -m` puts the job outside the terminal's
  # foreground group and leiningen pumps its own stdin into the project subprocess, so a
  # run that reads the tty takes SIGTTIN and the whole group stops — 0% CPU and an empty
  # log, indistinguishable from a hang.
  #
  # The status comes from the marker the run echoes into its own log, never from a
  # pipeline: `test-parallel.sh`'s rule, and here it is also how completion is noticed
  # without `wait -n`, which is bash 4.3 and this is the 3.2 macOS ships.
  ( env "${envv[@]}" lein test "$SELECTOR" < /dev/null >> "$log" 2>&1
    echo "MATRIX-EXIT:$?" >> "$log" ) &
  pid[i]=$!
  pgid[i]=$(ps -o pgid= -p "${pid[i]}" 2>/dev/null | tr -d ' ')
  pgid[i]="${pgid[i]:-${pid[i]}}"
  # the group is what says which configuration a JVM under it is running; see the
  # configs.tsv header above
  printf '%s\t%s\t%s\t%s\n' "$cfg" "${pid[i]}" "${pgid[i]}" "$log" \
    >> "$OUT_DIR/configs.tsv" 2>/dev/null || true
  state[i]=running
  # the live dashboard carries a launching config as a bar that starts filling; only
  # the scrolling view announces it as a line
  (( LIVE )) || printf '  %s▸%s %-16s %s%s  # %s%s\n' \
    "$DIM" "$OFF" "$cfg" "$DIM" "${rev[i]}" "$log" "$OFF"
}

reap() {                                           # reap <index> -> prints its row
  local i="$1"                                     # separately, per `launch` above
  local cfg="${CONFIGS[$i]}" log="${logf[$i]}" code summary counts mark elapsed
  wait "${pid[i]}" 2>/dev/null
  code=$(grep -a '^MATRIX-EXIT:' "$log" | tail -1 | cut -d: -f2)
  code="${code:-1}"
  elapsed=$((SECONDS - startt[i])); secs[i]=$elapsed
  summary=$(run_summary "$log")
  counts=$(run_counts "$log")
  if [[ "$code" -eq 0 ]]; then mark="$TICK"; state[i]=passed
  else mark="$CROSS"; state[i]=failed; FAILED+=("$cfg"); fi
  fin[i]="${summary:-did not finish}${counts:+, $counts}"
  # On the dashboard the finished row and its ✔/✘ are already in the block, and the
  # failing tests are the end-of-run rollup's to name; only the scrolling view prints
  # the row and its failures inline as they land.
  if (( ! LIVE )); then
    printf '  %s %-16s %-52s %8s  %s\n' \
      "$mark" "$cfg" "${fin[i]}" "$(hms $elapsed)" "${rev[i]}"
    # the failing TESTS, not just their namespaces: "which namespace" cannot tell a
    # broken test from a configuration that disagrees, and the rollup needs the names
    if [[ "$code" -ne 0 ]]; then
      local shown=0 total
      total=$(failing_tests "$log" | wc -l | tr -d ' ')
      while read -r t; do
        [[ -z "$t" ]] && continue
        (( shown >= 8 )) && break
        printf '      %s %s\n' "$CROSS" "$t"
        shown=$((shown + 1))
      done < <(failing_tests "$log")
      (( total > shown )) && printf '      %s… and %d more in %s%s\n' \
        "$DIM" "$((total - shown))" "$log" "$OFF"
    fi
  fi
  [[ $KEEP -eq 1 || -z "${diskd[i]}" ]] || rm -rf "${diskd[i]}"
}

# ---- the live dashboard (a terminal only) -----------------------------------
# `redraw` repaints one row per configuration in place — queued, a filling bar while
# running, ✔/✘ when done — from the same `ns_reached` poll the heartbeat reads.  It is
# gated on `LIVE`, so a pipe or CI never sees a cursor-motion byte; the scrolling
# heartbeat is what those get.

# a proportional bar `━━━╾────────` `w` cells wide: heavy for the reached fraction, a
# half-heavy head at the frontier, light for the rest.  No padding follows it, so its
# multi-byte cells never have to line up with a byte-counted `printf` width — the colour
# escapes it emits are zero-width bytes, so they do not disturb that either.  The reached
# run and its head carry the verdict colour `col`; the unreached remainder is dim grey,
# so the bar is indistinguishable from a filling gauge rather than a solid green (or red) block.
bar() {                                            # bar <reached> <total> <width> <col>
  local reached="$1" total="$2" w="$3" col="$4" fill i s=""
  (( total < 1 )) && total=1
  fill=$(( reached * w / total )); (( fill > w )) && fill=w
  # `${s}` braced, not `$s`: in a non-UTF-8 locale bash's bare-`$s` name scanner
  # swallows the high bytes of the glyph that follows, and under `set -u` the bogus
  # name reads as unbound and the bar comes back empty.  The braces end the name.
  s="${col}"
  for ((i = 0; i < w; i++)); do
    if   (( i <  fill )); then s="${s}━"
    elif (( i == fill )); then s="${s}╾${DIM}"     # head, then dim for the unreached rest
    else                       s="${s}─"
    fi
  done
  printf '%s%s' "$s" "$OFF"
}

BLOCK=0                                            # rows painted last time; 0 = not yet

# One painted line.  Every line of a frame goes through here, for the two things a
# repaint needs and a bare `printf` does not: the old content of the row is cleared
# first (a short line must not leave the tail of a longer one behind it), and the row
# is COUNTED — `BLOCK` is what the next frame moves the cursor up by, and a frame that
# guesses its own height is a frame that walks down the screen.
#
# Reached through dynamic scope, so `rows` is `redraw`'s local; `ns_lines` in
# suite-marks.sh takes the same shape for the same reason.
paint() { printf '\033[K%s\n' "$1"; rows=$((rows + 1)); }

# `…/tail`, never `head…`.  What a path's last components say — which run, which
# configuration — is the whole of what the reader wants from it; the `/Users/…` in front
# is what they already know, and a right-truncation keeps exactly that and drops the
# rest.
elide() {                                          # elide <text> <room>
  local tail
  (( ${#1} <= $2 )) && { printf '%s' "$1"; return; }
  tail="${1: -$(($2 - 1))}"
  # cut back to a separator when there is one, so the elision lands between components
  # rather than inside a name: `…/vaelii/logs/run-48213`, not `…ull/vaelii/logs/…`
  [[ "$tail" == */* ]] && tail="/${tail#*/}"
  printf '…%s' "$tail"
}

# The same for text whose HEAD is the informative end — a run summary, where the counts
# come first.  Marked, because `154418 assertion` is a number of assertions and a lie,
# where `154418 assertion…` is a column that ran out of room.
clip() {                                           # clip <text> <room>
  (( ${#1} <= $2 )) && { printf '%s' "$1"; return; }
  printf '%s…' "${1:0:$(($2 - 1))}"
}

# Pad to a column width in CHARACTERS.  `printf`'s `%-*.*s` counts BYTES, and the two
# functions above end their work with a three-byte `…`: a precision lands mid-glyph and
# emits half of it, and a width counts it as three columns and pads two short.  So no
# padded field in this frame goes through `printf`'s width — `clip` and `elide` have
# already bounded the text, and this pads it the way they measured it.
pad() {                                            # pad <text> <width>
  (( ${#1} >= $2 )) && { printf '%s' "$1"; return; }
  printf '%s%*s' "$1" $(( $2 - ${#1} )) ""
}

# A `<command>  # <comment>` label row, clamped to the terminal.  The command sits in
# the measured column so every `#` in the frame lines up, and the comment is elided
# rather than allowed to wrap — this is the row whose overflow broke the repaint.
label() {                                          # label <lead> <command> <comment>
  local room=$(( COLS - 1 - 4 - CMD_W - 4 ))
  (( room < 8 )) && room=8
  printf '%s %s%s  # %s%s' "$1" "$DIM" "$(pad "$2" "$CMD_W")" "$(elide "$3" "$room")" "$OFF"
}

redraw() {
  (( LIVE )) || return 0
  # up over the block painted last time, so this paint lands on top of it rather than
  # below it
  (( BLOCK > 0 )) && printf '\033[%dA' "$BLOCK"
  # green until something fails, then red — the bars carry the matrix's verdict-so-far,
  # not just each run's progress
  local barcol="$GREEN"; (( ${#FAILED[@]} > 0 )) && barcol="$RED"
  local i cfg run=0 donec=0 q=0 reached=0 rows=0 tall extra sfx room
  local -a rv=()
  # One poll per config, read by both the aggregate bar and its own row, so a running
  # config's log is grepped once a paint rather than twice.  A finished config counts as
  # its whole namespace budget reached; a queued one as none.
  for ((i = 0; i < n; i++)); do
    case "${state[i]}" in
      running)       rv[i]=$(ns_reached "${logf[i]}"); run=$((run + 1)) ;;
      passed|failed) rv[i]=$RUN_NS_COUNT;              donec=$((donec + 1)) ;;
      *)             rv[i]=0;                          q=$((q + 1)) ;;
    esac
    reached=$((reached + rv[i]))
  done

  # WHETHER THE ALTERNATING FRAME FITS.  Two lines per running configuration, one for
  # every other, plus the aggregate pair and the footer.  A frame taller than the
  # terminal cannot be repainted in place — the terminal scrolls out from under the
  # cursor arithmetic — so when it does not fit, the bar lines are dropped and the
  # compact row carries its bar inline, which is what this dashboard was before.  The
  # fallback is chosen per frame: a matrix whose last runs are finishing shrinks back
  # into the alternating form on its own.
  tall=$(( 3 + n + run ))
  local alt=1; (( tall > ROWS - 2 )) && alt=0

  # THE MATRIX AS ONE BAR, under its own reproducer.  Every namespace of every
  # configuration is a cell, so it advances even while a row is mid-run.
  if (( alt )); then
    paint "$(label "   " "lein test $SELECTOR" "$ABS_OUT_DIR")"
    sfx=$(printf '%d/%d  %s' "$reached" "$((n * RUN_NS_COUNT))" "$(hms $((SECONDS - T0)))")
    paint "$(printf '    %s  %s%s%s' \
      "$(bar "$reached" "$((n * RUN_NS_COUNT))" "$(bar_width 4 "$sfx")" "$barcol")" \
      "$DIM" "$sfx" "$OFF")"
  else
    paint "$(printf '  %s%-*s%s %s' "$DIM" "$CMD_W" "lein test $SELECTOR" "$OFF" \
      "$(bar "$reached" "$((n * RUN_NS_COUNT))" "$BARW" "$barcol")")"
  fi

  for ((i = 0; i < n; i++)); do
    cfg="${CONFIGS[i]}"
    case "${state[i]}" in
      running)
        if (( alt )); then
          # the row's own two lines: what to type to run it, where its log is, and then
          # the bar with nothing else on the line to push it off the edge
          paint "$(label "  ${DIM}⋯${OFF}" "${rcmd[i]}" "${logf[i]##*/}")"
          sfx=$(printf '%s/%s  %s %s' "${rv[i]}" "$RUN_NS_COUNT" \
                       "$(hms $((SECONDS - startt[i])))" "${rev[i]}")
          paint "$(printf '    %s  %s%s%s' \
            "$(bar "${rv[i]}" "$RUN_NS_COUNT" "$(bar_width 4 "$sfx")" "$barcol")" \
            "$DIM" "$sfx" "$OFF")"
        else
          paint "$(printf '  %s⋯%s %-16.16s %s %s/%s  %s%s %s%s' \
            "$DIM" "$OFF" "$cfg" "$(bar "${rv[i]}" "$RUN_NS_COUNT" "$BARW" "$barcol")" \
            "${rv[i]}" "$RUN_NS_COUNT" "$DIM" "$(hms $((SECONDS - startt[i])))" \
            "${rev[i]}" "$OFF")"
        fi ;;
      passed|failed)
        # one line: a finished row has no bar to alternate with, and its summary is the
        # answer its command was asked for
        local m="$TICK"; [[ "${state[i]}" == failed ]] && m="$CROSS"
        if (( alt )); then
          sfx=$(printf '%s %s' "$(hms "${secs[i]}")" "${rev[i]}")
          room=$(( COLS - 1 - 4 - CMD_W - 2 - ${#sfx} ))
          (( room < 8 )) && room=8
          (( room > 34 )) && room=34                # a wide terminal is not a reason to
                                                    # stretch a summary across it
          paint "$(printf '  %s %s%s%s %s %s%s%s' \
            "$m" "$DIM" "$(pad "${rcmd[i]}" "$CMD_W")" "$OFF" \
            "$(pad "$(clip "${fin[i]}" "$room")" "$room")" "$DIM" "$sfx" "$OFF")"
        else
          paint "$(printf '  %s %-16.16s %-44.44s %s%s %s%s' \
            "$m" "$cfg" "${fin[i]}" "$DIM" "$(hms "${secs[i]}")" "${rev[i]}" "$OFF")"
        fi ;;
      *)
        # `queued` and `skipped` both land here and those are two different things news.
        # `--fail-fast` sets `skipped` on everything after the failure, and a frame
        # spelling that `queued` says work is still coming when the run has stopped —
        # the closing frame is the one a reader keeps, and it would be the lie.  The
        # summary below already distinguishes them; this makes the frame agree with it.
        local w="queued"; [[ "${state[i]}" == skipped ]] && w="never started"
        if (( alt )); then
          paint "$(printf '  %s·%s %s%-*s%s %s%s%s' \
            "$DIM" "$OFF" "$DIM" "$CMD_W" "${rcmd[i]}" "$OFF" "$DIM" "$w" "$OFF")"
        else
          paint "$(printf '  %s·%s %-16.16s %s%s%s' "$DIM" "$OFF" "$cfg" "$DIM" "$w" "$OFF")"
        fi ;;
    esac
  done
  paint "$(printf '  %s%d running · %d done · %d queued        %s elapsed%s' \
    "$DIM" "$run" "$donec" "$q" "$(hms $((SECONDS - T0)))" "$OFF")"

  # A frame shrinks when a running row finishes and loses its bar line, leaving the
  # screen rows below this one still holding the previous frame's text.  Blank them, then
  # come back up, so the next frame moves over what is actually there.
  extra=$(( BLOCK - rows ))
  if (( extra > 0 )); then
    for ((i = 0; i < extra; i++)); do printf '\033[K\n'; done
    printf '\033[%dA' "$extra"
  fi
  BLOCK=$rows
}

START_REV=$(revision_hash)
START_DIRTY=$(revision_dirty)
T0=$SECONDS

# The ledger row's clock starts here, and its revision is the one the header prints
# rather than a second read of git: a matrix is ~35 minutes, and two reads a
# microsecond apart are still two facts that can disagree once somebody lands a
# commit between them.
runlog_start
RUNLOG_REV="$START_REV"
RUNLOG_DIRTY="$START_DIRTY"

echo "${BOLD}running ${n} of $ROSTER_TOTAL configuration(s), $JOBS at a time${OFF}" \
     "${DIM}$SELECTOR — $RUN_NS_COUNT of $NS_COUNT namespaces${OFF}"
if [[ ${#SAT_OUT[@]} -gt 0 ]]; then
  echo "${DIM}not run: ${SAT_OUT[*]} — \`full\` runs all $ROSTER_TOTAL${OFF}"
fi
echo "${DIM}at $(revision_line)${OFF}"
if (( SHUFFLE )); then
  echo "${DIM}order: ${CONFIGS[*]}${OFF}"
  echo "${DIM}seed $SEED  (TEST_MATRIX_SEED=$SEED replays this order, --ordered runs longest first)${OFF}"
fi
# The two commands this stands in for, as pasteable reproducers: the `lint` you still owe
# by hand (the matrix does not run it), and the `test` run itself — its `#` carries the
# run's log directory, absolute so it pastes from anywhere.  Under a live terminal the
# test line is repainted as a filling bar by `redraw`; without one it is this static line.
printf '    %s%-*s  # static analysis (run it by hand)%s\n' "$DIM" "$CMD_W" "lein lint" "$OFF"
(( LIVE )) || printf '    %s%-*s  # %s%s\n' "$DIM" "$CMD_W" "lein test $SELECTOR" "$ABS_OUT_DIR" "$OFF"
if [[ "${START_DIRTY:-0}" -gt 0 ]]; then
  echo "  ${RED}⚠${OFF} ${DIM}src/ or test/ is dirty: every run below compiles that"
  echo "     uncommitted work, so this matrix answers for no commit${OFF}"
fi
# One suite is one core for minutes; a dozen beside somebody else's is a slower
# everything.  A warning and not a refusal — sharing the box is normal here.
if pgrep -f 'lein test|vaelii\.bench' >/dev/null 2>&1; then
  echo "  ${RED}⚠${OFF} ${DIM}a suite or bench JVM is already running in this checkout;" \
       "expect both to be slower${OFF}"
fi
echo

# hide the cursor while the block is being repainted, and put it back however the
# script ends — a clean finish, a failure, or the INT/TERM trap's `exit 130`
if (( LIVE )); then printf '\033[?25l'; trap 'printf "\033[?25h"' EXIT; fi

done_n=0; running=0; next=0; last_beat=$SECONDS
while (( done_n < n )); do
  while (( running < JOBS && next < n )); do
    if (( FAIL_FAST && ${#FAILED[@]} > 0 )); then break; fi
    launch "$next"; next=$((next + 1)); running=$((running + 1))
  done

  # nothing running and nothing launchable: --fail-fast stopped the queue
  if (( running == 0 && next < n )); then
    for ((i = next; i < n; i++)); do state[i]=skipped; done
    break
  fi

  for ((i = 0; i < next; i++)); do
    [[ "${state[i]}" == running ]] || continue
    grep -qa '^MATRIX-EXIT:' "${logf[i]}" 2>/dev/null || continue
    reap "$i"
    running=$((running - 1)); done_n=$((done_n + 1))
    last_beat=$SECONDS                             # a row just landed; no beat is due
  done

  if (( LIVE )); then
    redraw
  elif (( HEARTBEAT > 0 && running > 0 && SECONDS - last_beat >= HEARTBEAT )); then
    line=""; shown=0
    for ((i = 0; i < next; i++)); do
      [[ "${state[i]}" == running ]] || continue
      if (( shown < 5 )); then
        line="$line${line:+ · }${CONFIGS[i]} $(ns_reached "${logf[i]}")/$RUN_NS_COUNT"
        shown=$((shown + 1))
      fi
    done
    (( running > shown )) && line="$line · …"
    printf '  %s⋯ %s  %d done · %d running · %d queued   %s%s\n' \
      "$DIM" "$(hms $((SECONDS - T0)))" "$done_n" "$running" "$((n - next))" "$line" "$OFF"
    last_beat=$SECONDS
  fi

  # The poll delay, but interruptibly.  A bare `sleep 2` is an EXTERNAL foreground
  # command, and `set -m` gives it its own process group and hands it the terminal
  # — so a ^C goes to the sleep's group, not to this shell, and the INT/TERM trap
  # never runs.  Nearly all of this loop's wall time is that sleep, so nearly every
  # ^C lands in it and the whole interrupt is lost: the runs keep going, orphaned.
  # Background the sleep and `wait` on it instead — `wait` is a builtin, so this
  # shell stays in the foreground group and a trapped signal returns from it at
  # once, running `on_interrupt`.  Same reason `test-backends.sh` waits on its
  # backgrounded suite.  `2>/dev/null` swallows the job-done notice `set -m` prints.
  if (( done_n < n )); then
    if (( LIVE )); then sleep 1 & else sleep 2 & fi   # a beat a second under the
    wait "$!" 2>/dev/null                             # dashboard, so the bars visibly move
  fi
done

# the final frame, then the cursor below it and back on, so the failures rollup prints
# under a dashboard that already shows every configuration's verdict
if (( LIVE )); then redraw; printf '\033[?25h'; fi

END_REV=$(revision_hash)
END_DIRTY=$(revision_dirty)
ELAPSED=$((SECONDS - T0))

# ---- the machine-readable half ----------------------------------------------
# One row per configuration, so a later reader — or the agent that ran this — does not
# have to parse the console.  Written whatever the verdict.
{
  printf 'config\tkind\trevision\tstate\tseconds\tsummary\tcounts\n'
  for ((i = 0; i < n; i++)); do
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "${CONFIGS[i]}" "$(config_kind "${CONFIGS[i]}")" "${rev[i]:-}" "${state[i]}" \
      "${secs[i]}" \
      "$([[ -n "${logf[i]:-}" ]] && run_summary "${logf[i]}")" \
      "$([[ -n "${logf[i]:-}" ]] && run_counts "${logf[i]}")"
  done
} > "$OUT_DIR/summary.tsv"

# What the NEXT run orders itself by.  Per checkout rather than per run — it is feedback
# for the next matrix, not output of this one, so it sits above the run directories the
# way `gate.sh` keeps its shard timings.  A configuration that did not finish keeps
# whatever it last measured rather than a zero, which would promote it to shortest and
# put it last.
mkdir -p "$(dirname "$MATRIX_TIMINGS")" 2>/dev/null || true
{
  [[ -f "$MATRIX_TIMINGS" ]] && cat "$MATRIX_TIMINGS"
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == passed || "${state[i]}" == failed ]] || continue
    # Only a run that actually ran the suite teaches the next one anything.  A minute is
    # a sanity floor rather than a tuning constant: the shortest configuration measured
    # here is nearly four, and anything under a minute is a boot failure, a stand-in
    # `lein`, or a run killed early — each of which would otherwise be recorded as "the
    # fastest configuration" and launched last forever after.
    [[ -n "$(run_summary "${logf[i]}")" && "${secs[i]}" -ge 60 ]] || continue
    printf '%s\t%s\n' "${CONFIGS[i]}" "${secs[i]}"
  done
} | awk -F'\t' '$1 != "" && $2 != "" { s[$1] = $2 } END { for (k in s) printf "%s\t%s\n", k, s[k] }' \
  | sort > "$MATRIX_TIMINGS.$$.new" && mv "$MATRIX_TIMINGS.$$.new" "$MATRIX_TIMINGS"

echo
# ---- failures by test --------------------------------------------------------
# The question a red matrix asks second, after "whose commit is this": is it the SUITE's
# answer, or a difference between configurations?  Naming the failing namespace per run
# cannot answer it — the same namespace under a dozen runs is a dozen lines that all
# say the same word, and reading a dozen logs by hand is what this script exists to
# replace.  A test that failed under every run that finished is the suite's answer at
# this revision; one that failed under only some is a difference between them, and the
# runs it did NOT fail under are the finding.
if [[ ${#FAILED[@]} -gt 0 ]]; then
  fails_tsv="$OUT_DIR/failures.tsv"
  : > "$fails_tsv"
  ran=0; ran_list=""
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == passed || "${state[i]}" == failed ]] || continue
    ran=$((ran + 1)); ran_list="$ran_list ${CONFIGS[i]}"
    while read -r t; do
      [[ -n "$t" ]] && printf '%s\t%s\n' "$t" "${CONFIGS[i]}" >> "$fails_tsv"
    done < <(failing_tests "${logf[i]}")
  done

  # Three shapes, chosen by how much there is to say, because a report nobody reads to
  # the end reports nothing.  Under nine distinct failures each gets a block; up to
  # thirty, a line each; past that, the count and where the rows are.  The blocks are
  # the useful case and the common one — a matrix goes red on one or two tests far more
  # often than on thirty, and thirty is a signal in itself.
  #
  # Sorted inside awk rather than piped through `sort`, since these are multi-line
  # records and sorting the LINES interleaves them.  Ties break on the test name: the
  # order has to be a function of content, never of which run happened to finish first.
  awk -F'\t' -v ran="$ran" -v all="$ran_list" \
      -v dim="$DIM" -v bold="$BOLD" -v off="$OFF" -v rows="$fails_tsv" '
    { if (!(($1 SUBSEP $2) in pair)) { pair[$1 SUBSEP $2] = 1; cnt[$1]++; }
      seen[$1] = seen[$1] " " $2 " " }
    END {
      m = split(all, cfgs, " ")
      for (a = 2; a <= m; a++) {                     # by name, so "not in:" reads the same
        v = cfgs[a]; b = a - 1                       # however the launch order came out
        while (b > 0 && cfgs[b] > v) { cfgs[b + 1] = cfgs[b]; b-- }
        cfgs[b + 1] = v
      }
      n = 0
      for (t in cnt) { name[++n] = t; if (index(t, "/") > 0) { split(t, p, "/"); ns[p[1]] = 1 } }
      nns = 0; for (x in ns) nns++
      for (i = 1; i <= n; i++)                       # selection sort: count desc, name asc
        for (j = i + 1; j <= n; j++)
          if (cnt[name[j]] > cnt[name[i]] ||
              (cnt[name[j]] == cnt[name[i]] && name[j] < name[i])) {
            tmp = name[i]; name[i] = name[j]; name[j] = tmp
          }

      printf "%sfailures by test%s — %d distinct in %d namespace(s), over %d run(s) that finished\n",
             bold, off, n, nns, ran

      # who failed it, said from whichever end is shorter
      for (i = 1; i <= n; i++) {
        t = name[i]; miss = ""; k = 0; hit = ""
        for (j = 1; j <= m; j++) {
          if (cfgs[j] == "") continue
          if (index(seen[t], " " cfgs[j] " ") == 0) { k++; if (k <= 5) miss = miss " " cfgs[j] }
          else if (cnt[t] <= 5) hit = hit " " cfgs[j]
        }
        if (k > 5) miss = miss " …and " (k - 5) " more"
        which[i] = (k == 0) ? "every configuration" \
                 : (k <= 4) ? "all but" miss \
                 : (cnt[t] <= 5) ? hit : "see " rows
      }

      if (n <= 8) {
        for (i = 1; i <= n; i++) {
          printf "  %s────────────────────────────────────────%s\n", dim, off
          printf "  Failing test: %s\n", name[i]
          printf "  Configs:      %d of %d\n", cnt[name[i]], ran
          printf "  Which:        %s\n", which[i]
        }
      } else if (n <= 30) {
        for (i = 1; i <= n; i++)
          printf "  %2d/%d  %-56s %s%s%s\n", cnt[name[i]], ran, name[i], dim, which[i], off
      } else {
        printf "  %d distinct failures is too many to list — every row is in %s\n", n, rows
        for (i = 1; i <= 5; i++)
          printf "  %2d/%d  %s\n", cnt[name[i]], ran, name[i]
        printf "  %s…and %d more%s\n", dim, n - 5, off
      }

      # what the table means, which is the question somebody opened it with
      partial = 0
      for (i = 1; i <= n; i++) if (cnt[name[i]] < ran) partial = 1
      print ""
      if (partial)
        printf "  %sA test some runs passed is a difference BETWEEN configurations — the ones it\n  did not fail under are named beside it, and that is the finding.%s\n", dim, off
      else
        printf "  %sEvery run that finished failed the same tests, so this is the suite'"'"'s answer at\n  this revision rather than a difference between storage or implementation.%s\n", dim, off
    }
  ' "$fails_tsv"
  echo
fi

# ---- the verdict -------------------------------------------------------------
skipped=0
for ((i = 0; i < n; i++)); do [[ "${state[i]}" == skipped ]] && skipped=$((skipped + 1)); done
if [[ ${#FAILED[@]} -eq 0 && $skipped -eq 0 ]]; then
  # the roster is part of the verdict, not a footnote to it: "all green" over a subset
  # is a different sentence from "all green" over the fifteen, and this is the line
  # that gets quoted into a commit message
  if [[ ${#SAT_OUT[@]} -gt 0 ]]; then
    echo "${GREEN}${BOLD}all $n of $ROSTER_TOTAL configurations green${OFF}" \
         "${DIM}in $(hms $ELAPSED) — not run: ${SAT_OUT[*]} ($OUT_DIR/)${OFF}"
  else
    echo "${GREEN}${BOLD}all $n configurations green${OFF} ${DIM}in $(hms $ELAPSED) ($OUT_DIR/)${OFF}"
  fi
else
  echo "${RED}${BOLD}${#FAILED[@]} of $n failed:${OFF} ${FAILED[*]}" \
       "${DIM}in $(hms $ELAPSED)${OFF}"
  (( skipped > 0 )) && echo "  ${DIM}$skipped never started (--fail-fast)${OFF}"
  # one path each while that is a short list, the directory once when it is not: a
  # dozen-line column of near-identical paths is the part of a report people skip
  if [[ ${#FAILED[@]} -le 5 ]]; then
    for c in "${FAILED[@]}"; do echo "  ${DIM}$(log_for "$c")${OFF}"; done
  else
    echo "  ${DIM}logs: $OUT_DIR/<config>.log — one per failure, and failures.tsv${OFF}"
  fi
fi
# Beside the verdict rather than only in the header, which is an hour of scrollback away
# by now: a red matrix is re-run, and re-running it in the order that produced the red
# is how a scheduling-dependent failure is caught a second time.
(( SHUFFLE )) && echo "  ${DIM}shuffled, seed $SEED — TEST_MATRIX_SEED=$SEED runs this order again${OFF}"

# ---- did every run run the same suite? ---------------------------------------
# The question a GREEN matrix asks, and the one nothing used to answer.  Thirteen runs
# that all pass have still told you nothing if one of them ran four hundred fewer
# assertions than the rest: a namespace that failed to load, a `deftest` that stood aside
# without saying so, a gate that inherited a switch and measured nothing.  Every one of
# those is green.  `config_expected_delta` expects no shortfall anywhere and says why no
# configuration stands aside; any shortfall is reported here.
#
# Only for a matrix that finished clean.  An error aborts the rest of its namespace, so a
# red run is short by an amount that means nothing, and saying so beside the failure it
# already reported is noise.  Only for one revision, too — counts taken either side of a
# commit are not comparable, which is what the block below this one exists to say.
deltas_bad=0
if [[ ${#FAILED[@]} -eq 0 ]]; then
  count_pairs=(); revs_agree=1; count_rev=""
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == passed ]] || continue
    a=$(run_assertions "${logf[i]}"); [[ -n "$a" ]] || continue
    count_pairs+=("${CONFIGS[i]}:$a")
    if [[ -z "$count_rev" ]]; then count_rev="${rev[i]:-}"
    elif [[ "${rev[i]:-}" != "$count_rev" ]]; then revs_agree=0; fi
  done
  if [[ ${#count_pairs[@]} -gt 1 ]]; then
    if [[ $revs_agree -eq 1 ]]; then
      if ! delta_report=$(assertion_deltas_ok "${count_pairs[@]}"); then
        echo
        echo "${BOLD}assertion counts: a run did not run what the others ran${OFF}"
        echo "$delta_report"
        echo "  ${DIM}Every run here passed, so this is not a failing test — it is a test that"
        echo "  did not run.  Find what the short run skipped — or, where an artifact really"
        echo "  is one implementation's, assert that configuration's own expectation.${OFF}"
        deltas_bad=1
      fi
    else
      echo
      echo "${DIM}assertion counts: not compared — the runs did not all compile one revision${OFF}"
    fi
  fi
fi

# ---- was the tree holding still? ---------------------------------------------
# The question a red matrix on a shared checkout asks first, and the one nobody can
# answer afterwards from the logs alone.
echo
if [[ "$START_REV" == "$END_REV" && "${START_DIRTY:-0}" -eq 0 && "${END_DIRTY:-0}" -eq 0 ]]; then
  echo "${DIM}tree: stable — every run compiled $START_REV, src/ and test/ clean${OFF}"
else
  echo "${BOLD}tree: not stable across this matrix${OFF}"
  [[ "${START_DIRTY:-0}" -gt 0 ]] && \
    echo "  ${RED}⚠${OFF} dirty at the start: ${START_DIRTY} uncommitted file(s) under src/ or test/" \
         "— every run compiled them, so this answers for no commit"
  [[ "${END_DIRTY:-0}" -gt 0 && "${START_DIRTY:-0}" -eq 0 ]] && \
    echo "  ${RED}⚠${OFF} dirty by the end: ${END_DIRTY} uncommitted file(s) — a run that started" \
         "late compiled work no earlier run saw, and a test that reads a file at run time
     (a doc, a golden, a resource) saw the edit even in a run already going"
  if [[ "$START_REV" != "$END_REV" ]]; then
    echo "  ${RED}⚠${OFF} HEAD moved: $START_REV → $END_REV.  What landed:"
    while read -r sha subject; do
      [[ -z "$sha" ]] && continue
      # a commit that touched neither src/ nor test/ cannot move a count, and saying so
      # is most of the triage
      if [[ -n "$(git show --format= --name-only "$sha" -- src test 2>/dev/null)" ]]; then
        printf '      %s %s[src]%s  %s\n' "$sha" "$BOLD" "$OFF" "$subject"
      else
        printf '      %s %s[docs]%s %s\n' "$sha" "$DIM" "$OFF" "$subject"
      fi
    done < <(git log --reverse --format='%h %s' "$START_REV..$END_REV" 2>/dev/null)
    # which side each config compiled: the revision it read at launch
    older=""; newer=""
    for ((i = 0; i < n; i++)); do
      [[ -z "${rev[i]:-}" ]] && continue
      if [[ "${rev[i]}" == "$START_REV" ]]; then older="$older ${CONFIGS[i]}"
      else newer="$newer ${CONFIGS[i]}(${rev[i]})"; fi
    done
    [[ -n "$older" ]] && echo "      ${DIM}compiled $START_REV:${OFF}$older"
    [[ -n "$newer" ]] && echo "      ${DIM}compiled a later one:${OFF}$newer"
  fi
  echo "  ${DIM}A run that is red under a commit you did not write is that commit's to"
  echo "  answer for: say so, re-run the one config, and let whoever landed it run the"
  echo "  matrix. Your own change is cleared by a green run at a revision that holds it.${OFF}"
fi

# ---- the ledger row ----------------------------------------------------------
# The selector is the `variant` column: a `:default` matrix and an `:all` matrix are
# different verdicts, and the row for one must not read as the last run of the other.
# The roster goes in the summary instead, because it is what the count is OVER — "all
# green" over `routine` is a different sentence from "all green" over `full`, and a
# reader of the row needs both numbers to tell them apart.
matrix_summary=$(printf '%d of %d configurations, roster %s, %d failed, %d skipped' \
                   "$n" "$ROSTER_TOTAL" "$ROSTER_LABEL" "${#FAILED[@]}" "$skipped")

# A SUBSET IS ITS OWN VERDICT, so it goes under its own variant rather than
# overwriting the matrix's.  `lein test-matrix --owed` is the common way to run
# one — it runs what the changed files owe — and "the matrix is green" off
# thirteen configurations is a different sentence from the same words off three.
# Filed under one variant, the cheap run would keep hiding when the whole roster
# last ran, which is the question the row exists to answer.
#
# Decided on what was ASKED FOR and on WHAT RAN, either one: `--owed` files under
# the owed variant however many configurations the diff owed, and a count short of
# the routine roster files under it whatever asked.  A hand-named list therefore
# lands here too, and belongs here — its claim is partial for the same reason.
#
# The `--owed` half is not redundant.  An `--owed` run that owes every
# configuration is a full roster and was still an owed run, and filing it as the
# matrix moved it out of the owed column at the moment it finished — the column
# it had been in for the twenty minutes it ran.  The row's own summary carries
# the count and the roster word, so a reader who wants to know how wide the run
# was reads it there.
#
# A subset that COVERS the routine roster keeps its own variant and names the
# coverage in it, so one row answers two columns: the owed column it was run
# under, and the matrix column whose question it also settled.  Claimed only
# where nothing was skipped — a run stopped by `--fail-fast` or by ^C planned a
# roster it did not finish, and the plan's word for it is an intention.
matrix_variant="$SELECTOR"
if (( OWED || n < ROUTINE_TOTAL )); then
  matrix_variant="$SELECTOR owed"
  if [[ -n "$COVERS" && $skipped -eq 0 ]]; then matrix_variant="$SELECTOR owed covering"; fi
fi
if [[ ${#FAILED[@]} -eq 0 && $skipped -eq 0 && $deltas_bad -eq 0 ]]; then
  matrix_state=passed
elif (( skipped == n )); then
  # Nothing ran at all, which `--fail-fast` cannot produce and an interrupt can.
  matrix_state=interrupted
else
  matrix_state=failed
fi
runlog_record matrix "$matrix_variant" "$matrix_state" "$matrix_summary" "$OUT_DIR"

[[ "$matrix_state" == passed ]] && exit 0
exit 1
