#!/usr/bin/env bash
# scripts/test-shuffle.sh — the whole matrix in a random order, memory first,
# stopping at the first configuration that fails.
#
# `test-backends.sh` runs the eight storage backends in a fixed order and
# `test-sweeps.sh` the six engine sweeps in theirs; both run every configuration
# and report a row each.  This runs BOTH lists as one, SHUFFLED, and stops the
# moment one fails.  It is the smoke test the full matrix is not: a single walk
# that starts where a break is likeliest to matter — a bare `lein test` on memory,
# the cheapest configuration and the one every other is compared against — and, if
# that holds, spreads out across the rest in an order that differs run to run.
#
# The assertion counts are compared at the foot, as the fixed-order runners compare
# them: `config_expected_delta` expects no shortfall anywhere, so a run that counted
# fewer assertions than the rest is a skip and fails the walk like a red run would.
#
# WHY SHUFFLE.  The matrix's promise is that all fourteen configurations agree, and
# a fixed order tests that promise the same way every time.  A random order does
# not find more bugs in one run, but across runs it reaches a different
# configuration first, so an interrupted walk has still covered a random subset
# rather than always the same prefix — and an order-of-runs coupling, if one ever
# creeps in, has somewhere to show.  The order is reported and seeded, so a walk
# that failed can be replayed exactly (`TEST_SHUFFLE_SEED=<n>`).
#
# WHY MEMORY FIRST.  It is not shuffled into the pack: a break in the default suite
# is a break everywhere, and proving that the dense index or the node engine agrees
# with a suite that does not itself pass is time spent to learn nothing.  So memory
# leads, and the shuffle is over everything behind it.  (Give explicit names and it
# shuffles exactly those, memory included — the pin is only for the default walk.)
#
# This is FAIL-FAST by nature — "until one fails" is the whole point — where
# `test-backends.sh`/`test-sweeps.sh` run to the end and tally.  Reach for those, or
# `test-matrix.sh`, when you want every configuration's verdict; reach for this when
# you want to know, quickly and from a fresh angle each time, whether they still all
# pass.
#
# The roster, the env that selects each configuration, and the per-namespace
# progress graph are the shared libraries the sibling scripts use
# (scripts/lib/suite-configs.sh, scripts/lib/suite-marks.sh) — a run here reads
# exactly as a run there.
#
# A leading-colon argument is a TEST SELECTOR passed straight to `lein test`
# (`:default`, the fast pass, is the default; `:all` before a release).  Any other
# argument is a configuration name, and giving one or more runs only those.
#
# Usage:
#   ./scripts/test-shuffle.sh                 # memory, then the rest shuffled, :default
#   ./scripts/test-shuffle.sh :all            # the ^:slow tests too
#   ./scripts/test-shuffle.sh -n              # print the shuffled plan and stop
#   ./scripts/test-shuffle.sh disk tms-reference  # only these, shuffled
#   TEST_SHUFFLE_SEED=42 ./scripts/test-shuffle.sh   # replay a given order
#
# Env:
#   TEST_SHUFFLE_OUT    log directory (default target/test-shuffle)
#   TEST_SHUFFLE_SEED   the shuffle seed (default: a fresh one, reported per run)
#   SUITE_PROGRESS      marks | lines | auto (scripts/lib/suite-marks.sh)
#
# ^C stops the suite that is running and then the script.
#
# Exit: 0 when every configuration passed, 1 when one failed, 130 when interrupted.

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# leiningen's own terminal state, handed down first by the alias: lein-shell pipes
# this script's stdout, so `-t 1` here would say "not a terminal" and the graph
# would fall to one line per namespace even with someone watching (suite-marks.sh
# reads SUITE_TTY at source time below).  Absent when run directly, where `-t 1` stands.
case "${1:-}" in
  --tty)    SUITE_TTY=1; shift ;;
  --no-tty) SUITE_TTY=0; shift ;;
esac

# shellcheck source=scripts/lib/suite-marks.sh
. scripts/lib/suite-marks.sh
# shellcheck source=scripts/lib/suite-configs.sh
. scripts/lib/suite-configs.sh

DRY=0
SELECTOR=":default"
WANTED=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    -n|--dry-run) DRY=1; shift ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    :all|:slow|:default) SELECTOR="$1"; shift ;;
    :*) echo "unknown selector $1 (:all, :slow, :default)" >&2; exit 2 ;;
    -*) echo "unknown flag $1 (try --help)" >&2; exit 2 ;;
    # named rather than left to run time: an unknown configuration would otherwise
    # run the suite with no switch set and report a clean pass for one nothing ran.
    # A GROUP word (`backends`, `sweeps`, `routine`, `full`) stands for its list and is
    # expanded below, so `test-shuffle sweeps` is a random walk over one axis.
    *) config_group "$1" >/dev/null 2>&1 || config_kind "$1" >/dev/null \
         || { echo "unknown configuration $1 (${ALL_BACKENDS[*]} ${ALL_SWEEPS[*]}," \
                   "or a group: backends sweeps routine full)" >&2; exit 2; }
       WANTED+=("$1"); shift ;;
  esac
done

# The seed is captured even when it was not given, so every run reports an order
# that can be replayed — the point of a shuffle you might have to explain.
SEED="${TEST_SHUFFLE_SEED:-$RANDOM}"
RANDOM=$SEED

# `shuffle_inplace` shuffles the global array SHUF, and lives in
# scripts/lib/suite-configs.sh because `test-matrix.sh` shuffles its roster too.  That
# file carries why the shuffle runs in this shell rather than in a subshell, which is
# what makes TEST_SHUFFLE_SEED name the order it actually produces.

SHUF=()
if [[ ${#WANTED[@]} -gt 0 ]]; then
  # groups expanded and repeats dropped first, so `full memory` is fourteen runs and
  # not fifteen with one of them twice
  while IFS= read -r c; do SHUF+=("$c"); done < <(expand_configs "${WANTED[@]}")
  shuffle_inplace
  CONFIGS=("${SHUF[@]}")
else
  # memory pinned first; everything else — the other backends and every sweep —
  # shuffled behind it
  for c in "${ALL_BACKENDS[@]}" "${ALL_SWEEPS[@]}"; do
    [[ "$c" == memory ]] || SHUF+=("$c")
  done
  shuffle_inplace
  CONFIGS=(memory "${SHUF[@]}")
fi

OUT_DIR="${TEST_SHUFFLE_OUT:-target/test-shuffle}"
RUN_NS_COUNT=$(selected_ns_count "$SELECTOR")

# the plan up front — an ordered shuffle is only reproducible if you can read what
# it chose, and the seed beside it is how to choose it again
echo "${BOLD}shuffling the suite across ${#CONFIGS[@]} configuration(s)${OFF}" \
     "${DIM}$SELECTOR — $RUN_NS_COUNT of $NS_COUNT namespaces${OFF}"
echo "${DIM}at $(revision_line)${OFF}"
echo "${DIM}order: ${CONFIGS[*]}${OFF}"
echo "${DIM}seed $SEED  (TEST_SHUFFLE_SEED=$SEED to replay this order)${OFF}"

if [[ $DRY -eq 1 ]]; then
  echo
  for cfg in "${CONFIGS[@]}"; do
    # shellcheck disable=SC2207
    envv=( $(config_env "$cfg") )
    config_wants_disk "$cfg" && envv+=("JVM_OPTS=-Dvaelii.disk.dir=$OUT_DIR/$cfg.disk")
    printf '  %s  %senv %s lein test %s%s\n' "$cfg" "$DIM" "${envv[*]}" "$SELECTOR" "$OFF"
  done
  exit 0
fi

mkdir -p "$OUT_DIR"
echo "${DIM}logs in $OUT_DIR/${OFF}"
echo

# ^C stops the run in progress AND the script — the long form of why neither half
# is automatic is in `test-backends.sh`; in short, `set -m` gives the run its own
# process group so one signal reaches the `lein` wrapper, its JVM, the project JVM
# and the readers on the pipe together.  SIGTERM first, so a disk-backed run's
# durability shutdown hook closes its logs before SIGKILL takes anything left.
set -m
child_pid=""
child_pgid=""
current_cfg=""
current_log=""
diskdir=""
DONE_RUNS=()
# the per-run assertion count and revision, for the comparison at the foot
COUNT_PAIRS=()
REVS=()

# shellcheck disable=SC2317,SC2329  # invoked from the INT/TERM trap below
stop_child() {
  [[ -z "$child_pgid" ]] && return 0
  kill -TERM -"$child_pgid" 2>/dev/null
  for _ in $(seq 1 20); do
    kill -0 -"$child_pgid" 2>/dev/null || return 0
    sleep 0.25
  done
  kill -KILL -"$child_pgid" 2>/dev/null
}

# shellcheck disable=SC2317,SC2329  # ditto — `trap on_interrupt INT TERM`
on_interrupt() {
  trap - INT TERM
  echo
  echo "  ${RED}^C${OFF} ${DIM}stopping ${current_cfg:-the run}${OFF}"
  { stop_child; [[ -n "$child_pid" ]] && wait "$child_pid"; } 2>/dev/null
  [[ -z "$diskdir" ]] || rm -rf "$diskdir"
  [[ -n "$current_log" ]] && echo "  ${DIM}partial log: $current_log${OFF}"
  echo
  echo "${RED}interrupted${OFF} ${DIM}after ${#DONE_RUNS[@]} of ${#CONFIGS[@]}${OFF}"
  exit 130
}
trap on_interrupt INT TERM

for cfg in "${CONFIGS[@]}"; do
  if [[ "$SELECTOR" == ":default" ]]; then
    log="$OUT_DIR/$cfg.log"
  else
    log="$OUT_DIR/$cfg${SELECTOR/:/.}.log"
  fi
  current_cfg="$cfg"
  current_log="$log"

  # the env that selects this configuration (suite-configs.sh), plus a private disk
  # directory for a durable one — those derive their store path from it, so nothing
  # a previous mode wrote is still lying there.  As an `env` argument list, not a
  # prefix: a prefix is recognized before expansion, so one built from a variable
  # cannot be used.
  # shellcheck disable=SC2207
  envv=( $(config_env "$cfg") )
  diskdir=""
  if config_wants_disk "$cfg"; then
    diskdir="$OUT_DIR/$cfg.disk"
    rm -rf "$diskdir"
    envv+=("JVM_OPTS=-Dvaelii.disk.dir=$diskdir")
  fi

  # the command verbatim so a run can be reproduced by copying the line, and the log
  # it is going to — printed BEFORE the run, so a suite still going is already tailable
  echo "  ${DIM}env ${envv[*]} lein test $SELECTOR  # $log${OFF}"
  echo "  ${DIM}loading a JVM and all $NS_COUNT test namespaces; the first namespace waits on that${OFF}"
  start=$SECONDS
  revision_stamp "config $cfg" > "$log"
  RUN_START=$start
  # `< /dev/null`: `set -m` puts this job outside the terminal's foreground group, so
  # a run that reads the tty from there takes SIGTTIN and the whole group stops —
  # `test-backends.sh` carries the long form.  `lein test` has no use for stdin.
  env "${envv[@]}" lein test "$SELECTOR" < /dev/null 2>&1 | tee -a "$log" | ns_progress &
  child_pid=$!
  child_pgid=$(ps -o pgid= -p "$child_pid" 2>/dev/null | tr -d ' ')
  child_pgid="${child_pgid:-$child_pid}"
  wait "$child_pid" 2>/dev/null
  code=$?
  child_pid=""
  child_pgid=""
  DONE_RUNS+=("$cfg")
  elapsed=$((SECONDS - start))

  summary=$(run_summary "$log")
  counts=$(run_counts "$log")
  rev=$(revision_hash)
  run_asserts=$(run_assertions "$log")
  [[ -n "$run_asserts" ]] && COUNT_PAIRS+=("$cfg:$run_asserts")
  REVS+=("$rev")

  if [[ $code -eq 0 ]]; then
    printf '  %s %-16s %-52s %8s  %s\n' \
      "$TICK" "$cfg" "${summary:-did not finish}${counts:+, $counts}" "$(hms $elapsed)" "$rev"
    # a passing durable run's store has served its purpose; leave a failing one for
    # inspection
    [[ -n "$diskdir" ]] && rm -rf "$diskdir"
    diskdir=""
    continue
  fi

  # a failure ends the walk — "until one fails" is the whole contract
  printf '  %s %-16s %-52s %8s  %s\n' \
    "$CROSS" "$cfg" "${summary:-did not finish}${counts:+, $counts}" "$(hms $elapsed)" "$rev"
  while read -r ns; do
    [[ -z "$ns" ]] && continue
    printf '      %s %s\n' "$CROSS" "$ns"
  done < <(failing_namespaces "$log")
  echo
  echo "${RED}${BOLD}stopped: $cfg failed${OFF}" \
       "${DIM}(${#DONE_RUNS[@]} of ${#CONFIGS[@]} run, at $rev — $log)${OFF}"
  exit 1
done

# Thirteen green runs have still said nothing if one of them ran fewer assertions than
# the rest — the same check the fixed-order runners make.  `config_expected_delta`
# expects no shortfall anywhere; any shortfall is a skip and fails the walk.  Skipped
# when the runs did not all compile one revision.
echo
if [[ ${#COUNT_PAIRS[@]} -gt 1 ]]; then
  if [[ $(printf '%s\n' "${REVS[@]}" | sort -u | wc -l) -le 1 ]]; then
    if ! delta_report=$(assertion_deltas_ok "${COUNT_PAIRS[@]}"); then
      echo "${BOLD}assertion counts: a run did not run what the others ran${OFF}"
      echo "$delta_report"
      echo "  ${DIM}Every run passed, so this is a test that did not run rather than one that"
      echo "  failed.  Find what the short run skipped — or, where an artifact really is"
      echo "  one implementation's, assert that configuration's own expectation.${OFF}"
      echo
      echo "${RED}${BOLD}stopped: the counts differ${OFF}" \
           "${DIM}(all ${#CONFIGS[@]} run, at $(revision_hash) — $OUT_DIR/)${OFF}"
      exit 1
    fi
  else
    echo "${DIM}assertion counts: not compared — the runs did not all compile one revision${OFF}"
  fi
fi
echo "${GREEN}${BOLD}all ${#CONFIGS[@]} configurations green${OFF}" \
     "${DIM}at $(revision_hash) — seed $SEED ($OUT_DIR/), assertion counts equal${OFF}"
exit 0
