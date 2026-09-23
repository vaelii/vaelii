#!/usr/bin/env bash
# scripts/test-backends.sh — run the whole suite once per storage backend and
# report a ✔ / ✘ per test namespace as it goes, then one per run.
#
# Storage is two independent choices (docs/storage.md): the RECORD store, which
# must survive (`:memory` / `:disk`), and the INDEX, which is derived state
# `reindex` recomputes from the records (`:memory` / `:dense` / `:columnar` /
# `:snapshot` / `:disk-log`).  That is 2 × 5 = 10 pairings, of which EIGHT are legal —
# RAM records under the durable index and RAM records under the mapped image are both
# refused, the first leaving index files that describe records that are gone, the
# second asking for an image every open discards — and each of the eight has a
# `:backend` name spelled `<records>-<index>`, which is what `VAELII_TEST_BACKEND`
# takes.  Every one of them loads the same shipped text KB (`resources/kb/*.txt`);
# what differs is only where the sentexes live and how they are indexed.
# A ninth run, `overlay`, is not a ninth pair but the fork decorator
# (docs/overlay.md) over an empty base.
#
# Each run prints the command it is about to run and the log it is writing —
# `env … lein test :default  # target/test-backends/<backend>.log` — so it is
# tailable while it goes and reproducible by copying the line.  The line carries only
# what THAT run needs: a scratch disk directory (`-Dvaelii.disk.dir`) is a
# durable run's concern, so a RAM-only one is given no `-D` at all and reads as
# the plain `lein test` it is.
#
# Then the run's own output becomes a ✔/✘ per test namespace, printed as each
# one finishes rather than at the end — so a suite eight minutes in has said
# eight minutes' worth about where it is.  On a TERMINAL that is the marks alone,
# in groups of ten across rows as wide as it, each row closing with the count: a
# progress bar whose bricks each mean something, and three lines a backend rather
# than 165.  Redirected to a log or a pipe it is one line per namespace instead —
# named, counted and timed — because an unterminated row of ticks in a file
# answers none of the questions a tail of it is asking.  `SUITE_PROGRESS` forces
# either.  Everything else the suite prints (reflection warnings, the engine's own
# :warn logs, the failure reports) goes to the log, and a failing run names its
# failing namespaces under its summary line — which is where a name is worth
# reading, since by then it is the answer to a question.
#
# Every line that carries a verdict carries the REVISION it is a verdict about:
# the header, each backend's summary row, and the log's own first line.  Read per
# run, not once, and a change between runs is called out where it happens — nine
# runs are ~40 minutes, and a commit landing in the middle of them moves the
# counts under the runs still to come.
#
# The FIRST mark of a run lands ~20s after its command line, and none of that
# gap is this script: `lein test` boots a JVM and then compiles and loads every
# test namespace before it runs any of them, so there is nothing to mark until
# it has.  The run says as much on the line under the command, because silence
# nobody accounted for is indistinguishable from a hang.
#
# The suite is expected to be **failing-set-identical** across every run — a
# backend that answers differently is a bug in the backend, not a feature of
# it.  The assertion COUNT is identical too: where a tally is one store's — the
# columnar trie counts no node probes, so it reports no `:fan` — the test asserts
# that backend's own reading rather than standing aside (docs/profile.md), so no
# run is expected short.  Any difference is a run that skipped something the
# others ran.
#
# That is CHECKED at the foot of this script rather than left to be read, since
# it is the one difference a green matrix hides: a dozen passing runs say
# nothing if one of them ran four hundred fewer assertions.  The expected
# shortfall is `config_expected_delta` in scripts/lib/suite-configs.sh — zero for
# every configuration — and it is where a stand-aside would be recorded if one
# ever had to exist.
#
# Runs here are SEQUENTIAL, and that is a choice about readability rather than a
# constraint: one run at a time is one run's wall time, and a box you can still
# use.  What forbids sharing is a DIRECTORY, not a count — a durable store lives
# at `<vaelii.disk.dir>/space-<n>`, and every run below already gets its own
# `vaelii.disk.dir`, so the single-writer lock is never contended and the
# six-block `VAELII_TEST_SPACE` limit is about a case this does not create.
# **`scripts/test-matrix.sh` is the concurrent one** — these nine and the six
# sweeps at once, ~13 minutes against the ~60 the two scripts take in sequence,
# and what to run when a change owes the matrix.  Reach for this script for one
# axis, one backend, or a wall time that means something.
#
# A leading-colon argument is a TEST SELECTOR, passed straight to `lein test`
# (project.clj defines them).  `:default` — what a bare run takes — skips the
# thirty-four `^:slow` tests, the exhaustive cross-products and randomized oracles
# that carry 80k of the suite's 283k assertions; `:slow` is those alone;
# `:all` is both.  Nine backends multiply that gap by nine, which is why the
# fast pass is the default here for the same reason it is in `lein test` — and
# why the matrix is worth running at `:all` before a storage change lands.  A
# non-default selector writes `<backend>.<selector>.log`, so a `:slow` pass does
# not overwrite what a full one left.
#
# Usage:
#   ./scripts/test-backends.sh                       # all nine, :default
#   ./scripts/test-backends.sh :all                  # all nine, slow tests included
#   ./scripts/test-backends.sh :slow memory          # the slow tests, one backend
#   ./scripts/test-backends.sh memory disk-memory    # only these
#   ./scripts/test-backends.sh --tms dense           # the dense TMS instead
#   ./scripts/test-backends.sh --fail-fast
#   ./scripts/test-backends.sh --keep                # keep each run's disk dir
#
# Env:
#   TEST_BACKENDS_OUT   log directory (default target/test-backends)
#   SUITE_PROGRESS      marks | lines | auto (default: marks on a terminal, lines
#                       into anything else)
#
# ^C stops the suite that is running and then the script — one interrupt gets
# you out of the whole matrix, not out of one run of it.
#
# Exit: 0 when every run passed, 1 when one failed, 130 when interrupted.

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# leiningen's own terminal state, handed down first by the alias: lein-shell pipes
# this script's stdout, so `-t 1` (in suite-marks.sh, sourced below) would say "not a
# terminal" and the graph would fall to one line per backend even with someone
# watching.  Absent when run directly, where `-t 1` stands.
case "${1:-}" in
  --tty)    SUITE_TTY=1; shift ;;
  --no-tty) SUITE_TTY=0; shift ;;
esac

# The roster, and the environment that selects each: `scripts/lib/suite-configs.sh`,
# shared with `test-sweeps.sh` and `test-matrix.sh` so a new backend is one edit.
# `overlay` is a ninth run and not a ninth pair: it is the DECORATOR — a private
# writable fork over a shared read-only base (docs/overlay.md) — with the base left
# empty, which is the claim that a fork of nothing behaves exactly like the thing it
# forked.
# shellcheck source=scripts/lib/suite-configs.sh
. scripts/lib/suite-configs.sh
ALL=("${ALL_BACKENDS[@]}")

TMS=""
FAIL_FAST=0
KEEP=0
SELECTOR=":default"
WANTED=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    # A value is REQUIRED: `shift 2` on a one-element stack shifts nothing and
    # returns 1, so the loop never advances and `--tms` alone spins forever.
    --tms) [[ $# -ge 2 ]] || { echo "test-backends: --tms needs a value" >&2; exit 2; }
           TMS="$2"; shift 2 ;;
    --tms=*) TMS="${1#*=}"; shift ;;
    --fail-fast) FAIL_FAST=1; shift ;;
    --keep) KEEP=1; shift ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    # checked here rather than left to lein, which answers an unknown selector with
    # "Please specify :test-selectors in project.clj" — true, and not the problem
    :all|:slow|:default) SELECTOR="$1"; shift ;;
    :*) echo "unknown selector $1 (:all, :slow, :default)" >&2; exit 2 ;;
    -*) echo "unknown flag $1 (try --help)" >&2; exit 2 ;;
    *) WANTED+=("$1"); shift ;;
  esac
done

if [[ ${#WANTED[@]} -gt 0 ]]; then
  BACKENDS=("${WANTED[@]}")
else
  BACKENDS=("${ALL[@]}")
fi

# A run owns its directory (gate.sh, same reason): the logs and the disk scratch
# roots live under it, so two concurrent matrices — the two non-overlapping
# VAELII_TEST_SPACE blocks testing.md sanctions — cannot rm -rf each other's live
# store or interleave one log.  `latest` points at the newest and is what to tail;
# an explicit TEST_BACKENDS_OUT is used verbatim.
BACKENDS_ROOT="target/test-backends"
if [[ -n "${TEST_BACKENDS_OUT:-}" ]]; then
  OUT_DIR="$TEST_BACKENDS_OUT"
  mkdir -p "$OUT_DIR"
else
  OUT_DIR="$BACKENDS_ROOT/run-$$"
  mkdir -p "$OUT_DIR"
  ln -sfn "$(basename "$OUT_DIR")" "$BACKENDS_ROOT/latest" 2>/dev/null || true
fi

# The colours, the marks and the log readers, shared with `test-sweeps.sh` — the
# other script that runs the whole suite more than once, and which would otherwise
# carry a second copy of them to drift against this one.
# shellcheck source=scripts/lib/suite-marks.sh
. scripts/lib/suite-marks.sh

RUN_NS_COUNT=$(selected_ns_count "$SELECTOR")

# ^C stops the run in progress AND the script.  Neither half is automatic.
#
# A `lein test` left in the foreground swallows the interrupt and the `for` loop
# marches on to the next backend, so getting out of a nine-run matrix takes
# nine interrupts.  So the suite runs in the background and the script `wait`s
# on it, which a trap CAN interrupt.
#
# Killing it then needs two things bash does not give by default.  `set -m` puts
# each background job in its own process group, so one signal reaches every
# process a run is (the `lein` wrapper, its JVM, the project JVM it forks, and
# the `tee`/`awk` reading them) — signalling a pid alone would kill one and
# orphan the rest.  The job is a pipeline, so its group is named by its FIRST
# process while `$!` is its last; `ps` is what reads the group off the pid bash
# hands back.  And `set -m` un-does the rule that a background job in a
# job-control-less shell has SIGINT set to IGNORED, which would make an
# interrupt unkillable by the very signal the user pressed.  SIGTERM first, so
# the durability shutdown hook runs and a disk-backed run closes its logs
# cleanly, then SIGKILL for anything that will not go.
set -m
child_pid=""
child_pgid=""
current_backend=""
current_log=""
diskdir=""
FAILED=()
COUNT_PAIRS=()
DONE_RUNS=()
rev=""
prev_rev=""
REVS=()

# Two codes for one fact: shellcheck 0.10 split "this function is never called"
# out of SC2317 into SC2329, so naming only the new one leaves the script red on
# every older shellcheck — including the one ubuntu-latest ships, which is how
# this surfaced. Both, so a contributor and CI reach the same verdict.
# shellcheck disable=SC2317,SC2329  # invoked from the INT/TERM trap below
stop_child() {
  [[ -z "$child_pgid" ]] && return 0
  kill -TERM -"$child_pgid" 2>/dev/null            # the negative pid: the whole group
  for _ in $(seq 1 20); do
    kill -0 -"$child_pgid" 2>/dev/null || return 0
    sleep 0.25
  done
  kill -KILL -"$child_pgid" 2>/dev/null
}

# shellcheck disable=SC2317,SC2329  # ditto — `trap on_interrupt INT TERM`
on_interrupt() {
  trap - INT TERM                                  # a second ^C is the OS's now
  echo
  echo "  ${RED}^C${OFF} ${DIM}stopping ${current_backend:-the run}${OFF}"
  # 2>/dev/null over both: reaping a signalled job is where bash prints its
  # `Terminated: 15` report, one line per process in the pipeline
  { stop_child; [[ -n "$child_pid" ]] && wait "$child_pid"; } 2>/dev/null
  [[ $KEEP -eq 1 || -z "$diskdir" ]] || rm -rf "$diskdir"
  [[ -n "$current_log" ]] && echo "  ${DIM}partial log: $current_log${OFF}"
  echo
  echo "${RED}interrupted${OFF} ${DIM}after ${#DONE_RUNS[@]} of ${#BACKENDS[@]}${OFF}"
  exit 130
}
trap on_interrupt INT TERM

echo "${BOLD}running the suite on ${#BACKENDS[@]} backend(s)${OFF}" \
     "${DIM}$SELECTOR — $RUN_NS_COUNT of $NS_COUNT namespaces${OFF}${TMS:+  (tms=$TMS)}"
echo "${DIM}at $(revision_line)${OFF}"
echo "${DIM}logs in $OUT_DIR/${OFF}"
echo

for backend in "${BACKENDS[@]}"; do
  # `<backend>.log` belongs to the routine run; any other selector says which it
  # was, so a `:slow` pass and a `:default` pass sit beside each other
  if [[ "$SELECTOR" == ":default" ]]; then
    log="$OUT_DIR/$backend.log"
  else
    log="$OUT_DIR/$backend${SELECTOR/:/.}.log"
  fi
  current_backend="$backend"
  current_log="$log"

  # as an `env` argument list rather than an assignment prefix: a prefix is
  # recognized before expansion, so a conditionally-present one cannot be built
  envv=(VAELII_TEST_BACKEND="$backend")
  # a private disk directory, but only for a run with a durable half: those
  # derive their store's path from this property, so nothing a previous mode
  # wrote is still lying there.  A RAM-only run reads no directory, and being
  # handed one would only put a `-D` on its line that means nothing.
  diskdir=""
  case "$backend" in
    disk-*)                                        # the RECORD half, i.e. the name's prefix
      diskdir="$OUT_DIR/$backend.disk"
      rm -rf "$diskdir"
      envv+=(JVM_OPTS="-Dvaelii.disk.dir=$diskdir") ;;
  esac
  [[ -n "$TMS" ]] && envv+=(VAELII_TEST_TMS="$TMS")

  # The revision THIS run is about to be taken at, read per run rather than once:
  # nine runs are ~40 minutes and another agent landing a test in the middle of
  # them moves the counts under the runs still to come.  Said out loud when it
  # happens, because the symptom — counts that differ between backends — is the
  # symptom of a run that skipped something, and telling them apart afterwards
  # costs an investigation.
  rev=$(revision_hash)
  if [[ -n "$prev_rev" && "$rev" != "$prev_rev" ]]; then
    echo "  ${RED}⚠${OFF} ${DIM}the tree moved: $prev_rev → $rev —" \
         "counts below are not comparable with the ones above${OFF}"
  fi
  prev_rev="$rev"
  REVS+=("$rev")

  # the command verbatim, so a run can be reproduced by copying the line, and
  # the log it is going to — printed BEFORE the run, so a suite still going is
  # already tailable
  echo "  ${DIM}env ${envv[*]} lein test $SELECTOR  # $log${OFF}"
  # ~20s of silence follows, and none of it is this script: `lein test` boots a
  # JVM (~6s to its first byte), then compiles and LOADS every test namespace
  # before running any of them, so there is no namespace to mark until it has.
  # Every one of them, whatever the selector — narrowing what runs does not narrow
  # what is compiled.  Said out loud, because a silence nobody accounted for reads
  # as a hang.
  echo "  ${DIM}loading a JVM and all $NS_COUNT test namespaces; the first namespace waits on that${OFF}"
  start=$SECONDS
  # backgrounded and waited on, so ^C reaches the handler above rather than
  # being swallowed by a foreground child.  `tee` keeps the whole run in the
  # log; the terminal gets the marks alone.  With `pipefail` the pipeline's
  # status is `lein`'s, since neither reader fails.
  #
  # `< /dev/null` is what keeps it RUNNING.  `set -m` puts the job in its own
  # process group, which is therefore not the terminal's foreground group, and
  # leiningen pumps its own stdin into the project subprocess — so a run started
  # from a terminal reads the tty from the background, takes SIGTTIN, and the
  # whole group STOPS: 0% CPU, an empty log, no output ever, indistinguishable
  # from a hang until `ps` shows the state as `T`.  `lein test` has no use for
  # stdin, so give it none.
  # the stamp first, then append: a log has to say what it was run *against*, or a
  # count that moved because the tree moved is indistinguishable from one that moved
  # because a run skipped something.  Labelled with the backend, so a per-config log
  # names its config on line 1 as well as the revision
  revision_stamp "backend $backend" > "$log"
  RUN_START=$start                                 # the clock a `lines` run times against
  env "${envv[@]}" lein test "$SELECTOR" < /dev/null 2>&1 | tee -a "$log" | ns_progress &
  child_pid=$!
  child_pgid=$(ps -o pgid= -p "$child_pid" 2>/dev/null | tr -d ' ')
  child_pgid="${child_pgid:-$child_pid}"
  wait "$child_pid" 2>/dev/null                    # 2>/dev/null: the job-done notice
  code=$?
  child_pid=""
  child_pgid=""
  DONE_RUNS+=("$backend")
  elapsed=$((SECONDS - start))

  # the two lines clojure.test prints last, tightened into one column; absent
  # when the run died before reaching them
  summary=$(run_summary "$log")
  counts=$(run_counts "$log")
  # the count on its own, for the cross-run comparison at the foot of this script
  run_asserts=$(run_assertions "$log")
  [[ -n "$run_asserts" ]] && COUNT_PAIRS+=("$backend:$run_asserts")

  # the revision on the row itself: this is the line that gets quoted into a
  # report, and a count quoted without one is a count nobody can reproduce
  if [[ $code -eq 0 ]]; then mark="$TICK"; else mark="$CROSS"; FAILED+=("$backend"); fi
  printf '  %s %-16s %-52s %8s  %s\n' \
    "$mark" "$backend" "${summary:-did not finish}${counts:+, $counts}" "$(hms $elapsed)" "$rev"

  # what failed, again, under the run's own summary — the marks above have
  # scrolled by the time a nine-run matrix ends
  if [[ $code -ne 0 ]]; then
    while read -r ns; do
      [[ -z "$ns" ]] && continue
      printf '      %s %s\n' "$CROSS" "$ns"
    done < <(failing_namespaces "$log")
  fi

  [[ $KEEP -eq 1 || -z "$diskdir" ]] || rm -rf "$diskdir"
  if [[ $code -ne 0 && $FAIL_FAST -eq 1 ]]; then
    echo; echo "${RED}stopping: --fail-fast${OFF}"; break
  fi
done

echo
# One revision for the whole matrix is the case stated here plainly; more than
# one is the case stated here loudly, since the runs then answer for different
# trees and the failing-set-identical claim is about a tree.
# guarded on the length: this is bash 3.2, where `"${a[@]}"` on an empty array is an
# unbound-variable error under `set -u` rather than an empty list
if [[ ${#REVS[@]} -eq 0 ]]; then
  matrix_rev="at $(revision_hash)"
else
  uniq_revs=$(printf '%s\n' "${REVS[@]}" | sort -u | tr '\n' ' ')
  if [[ $(printf '%s\n' "${REVS[@]}" | sort -u | wc -l) -gt 1 ]]; then
    matrix_rev="across ${uniq_revs% }"
  else
    matrix_rev="at ${uniq_revs% }"
  fi
fi

# ---- did every run run the same suite? ---------------------------------------
# A green set of runs has still said nothing if one of them ran fewer assertions than the
# rest: a namespace that failed to load, a `deftest` that stood aside without saying so, a
# gate that inherited a switch and measured nothing.  Every one of those is green.
# `config_expected_delta` in suite-configs.sh expects no shortfall anywhere, and says why
# no configuration stands aside; any shortfall is reported here and fails the run.  Skipped when something
# already failed — an error aborts the rest of its namespace, so the shortfall means
# nothing — and when the runs did not all compile one revision.
deltas_bad=0
if [[ ${#FAILED[@]} -eq 0 && ${#COUNT_PAIRS[@]} -gt 1 ]]; then
  if [[ $(printf '%s\n' "${REVS[@]}" | sort -u | wc -l) -le 1 ]]; then
    if ! delta_report=$(assertion_deltas_ok "${COUNT_PAIRS[@]}"); then
      echo "${BOLD}assertion counts: a run did not run what the others ran${OFF}"
      echo "$delta_report"
      echo "  ${DIM}Every run passed, so this is a test that did not run rather than one that"
      echo "  failed.  Find what the short run skipped — or, where an artifact really is"
      echo "  one implementation's, assert that configuration's own expectation.${OFF}"
      deltas_bad=1
    fi
  else
    echo "${DIM}assertion counts: not compared — the runs did not all compile one revision${OFF}"
  fi
fi

if [[ ${#FAILED[@]} -eq 0 ]]; then
  echo "${GREEN}${BOLD}all ${#BACKENDS[@]} backends green${OFF} ${matrix_rev}" \
       "${DIM}($OUT_DIR/)${OFF}"
  [[ $deltas_bad -eq 0 ]] && exit 0
  exit 1
fi
echo "${RED}${BOLD}${#FAILED[@]} of ${#BACKENDS[@]} failed:${OFF} ${FAILED[*]} ${DIM}(${matrix_rev})${OFF}"
# Same naming rule the run used, not a hardcoded `<backend>.log` — under any
# selector but `:default` the log is `<backend>.<selector>.log`, and printing the
# wrong path on a red run points whoever has to debug it at a file that isn't there.
# `deep.yml` runs exactly such a selector.
for b in "${FAILED[@]}"; do
  if [[ "$SELECTOR" == ":default" ]]; then
    echo "  ${DIM}$OUT_DIR/$b.log${OFF}"
  else
    echo "  ${DIM}$OUT_DIR/$b${SELECTOR/:/.}.log${OFF}"
  fi
done
exit 1
