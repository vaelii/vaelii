#!/usr/bin/env bash
# scripts/gate.sh — the checks that can say "no" before you land.
#
# TWO gates, and the split is the point — a fast one to run before every commit,
# a full one to run before a tag or a perf-sensitive land:
#
#   lein gate           FAST — lint + test:
#     lint   static analysis  (scripts/lint.sh — its checks, in three concurrent lanes)
#     test   the suite        (`lein test`, `:default` selector, memory stores; incl. assert_cost_test)
#
#   lein release-gate   FULL — lint + test + uberjar + perf:
#     uberjar  the standalone jar (`lein uberjar`, AOT of every namespace), then a load
#              of `vaelii.core` from it — `build_uberjar` below
#     perf     the scaling claims (`lein perf` — growth ratios, not milliseconds)
#
# PERF — why it is not in the fast gate.  It takes about an hour (SHAPE below), so
# a gate that always ran it is one people skip, and a skipped gate catches nothing.
# Two things buy the drop back:
#   - the CONSTANT-cost class (a fixed op added to every write) is a COUNT, not a
#     duration, and `assert_cost_test` asserts it in the fast test stage of every `lein gate`.
#   - the SUPER-LINEAR class (a cost that turns quadratic) is what the perf ratios
#     uniquely catch; CI's `deep.yml` perf job runs them, and `lein release-gate`
#     runs them here.  When the pending diff touches the retrieval / inference /
#     index / TMS core and this gate did not run perf, it prints "perf owed" at the
#     end and names the command — the ask the split leans on (non-blocking).
#   - a diff that touches `decide/arity.clj`, or an arity `defn` of `checks`, `kb` or
#     `provers`, prints "perf-ab owed" naming the four arity probes of `vaelii.bench.ab`
#     (`arity_fns_changed`): a constant added to every write passes the growth checks.
#
# The `:default` selector on the test stage — the `^:slow` half is yours to run:
#   - `lein test :all` — the deferred tests, 47% of the assertions (CONTRIBUTING.md §5).
#     `lein gate --all` / `lein release-gate --all` runs it here.  When the pending
#     diff touches the index, TMS or inference files the slow tests drive and this
#     gate ran `:default`, it prints "slow owed" beside "perf owed" (non-blocking).
#   - `lein test-red` — the `^:red` tests, which no gate runs.  A diff touching a file
#     they drive, or a test file holding the mark, prints "red owed" (non-blocking).
#   - `./scripts/test-backends.sh` — the eight record×index pairs plus the overlay
#     decorator.  **Anything touching storage, the index, records, or recovery must
#     run this**; the suite must be failing-set-identical across all nine, and the
#     memory-store run the gate does is one of the nine.
#
# NOT fail-fast by default, and that is the main decision here.  The suite takes
# minutes; stopping at the first failure means fixing lint, waiting out the
# tests, finding a test failure, waiting again, then finding the perf one —
# three full cycles to learn what one run already knew.  So every stage runs,
# each one's output is captured, and the report at the end names all of them.
# `--fail-fast` when you would rather stop.
#
#   lein gate                  # fast: lint + test
#   lein release-gate          # full: lint + test + uberjar + perf  (`gate.sh --release`)
#   lein gate --perf           # a fast gate plus perf, without the release framing
#   lein gate --fail-fast      # stop at the first failure
#   lein gate --quick          # add perf as a coarse read: one attempt, widened bound
#   lein gate --skip test      # drop a stage; repeatable
#   lein gate --only perf      # run one; repeatable  (names perf, so it runs)
#   lein gate --only uberjar   # the jar build alone
#   lein gate --all            # test stage at `:all` — the ^:slow tests too
#   lein gate --jobs 4         # test shards (default: scripts/lib/slots.sh; 1 = one JVM)
#   lein gate --sequential     # the old shape: one test JVM, one stage at a time
#   lein gate --brief          # stage verdicts only, without each stage's list of checks
#
# A passing stage prints WHAT IT CHECKED under its row — lint's checks by name
# and summary, perf's every claim, the suite's shard banner and totals.  Four green
# rows say a gate passed and not what it covered, and "what did that green actually
# check" is the question a reader of one is being asked.  `stage_detail` says why it
# reads those out of the stage logs rather than keeping a list here.
#
# SHAPE.  `lint` and `test` run **concurrently**, then `perf` alone.  Two reasons it
# is that split and not all three at once:
#
#   - lint is static analysis and test is a JVM suite; neither can perturb the
#     other's answer, so lint is a free minute inside the suite's wall clock.
#   - **perf runs alone on purpose.**  It judges growth ratios rather than
#     milliseconds, which is what makes it machine-independent — but a reading taken
#     while the test shards saturate the box is noise, and a perf gate that goes
#     amber under its own harness is one nobody trusts.  A full run took 46 to 74
#     minutes over 283 checks (`logs/runs.tsv`, 2026-11-03 to 2026-11-06).
#
# The test stage itself is sharded across JVMs (`scripts/test-parallel.sh`), which is
# safe because the in-memory registry isolates separate JVMs — see that script.  It
# starts only once this gate holds one of the box-wide gate slots (`gate_slot_take`,
# scripts/lib/slots.sh), so its shard count reads the box after admission.  Lint runs
# while the gate waits, and the slot is released before the perf stage.
#
# Env:
#   GATE_OUT        log directory (default logs/gate/run-<pid>)
#   GATE_KEEP_RUNS  past run directories kept under logs/gate (default 40)
#   GATE_JOBS       default shard count for the test stage
#   GATE_MAX_CONCURRENT  gate test stages admitted at once, box-wide (default 2, 0 = no cap)
#   GATE_NO_WAIT    exit 75 instead of waiting when every gate slot is held
#   PERF_TOLERANCE  passed to `lein perf --tolerance` — raise it on a loaded box
#
# Each stage streams to its own log, tailable while it goes.  On the console a
# stage is ONE chunk — its command, then its verdict, then its detail, printed
# together when it finishes and set off by a blank line — so a stage appears as one
# block with its context attached rather than a header at the top and a result
# far below.  A failing stage prints the tail of its log inline; the whole log is
# always on disk.
#
# Every one of those says which REVISION it is a verdict about — the banner, each
# stage log's first line, and the closing pass/fail line — and the closing line says
# so when the tree moved during the run.  A gate is minutes long on a checkout
# several writers work in, so "which tree was this green for" is a real question,
# and a green quoted without an answer to it is not evidence of anything.
#
# **A run owns its log directory**, and must: several writers share one working tree here,
# so two gates run in it at once.  Sharing one `test.log`, `perf.log` or shard log hands
# the reader the other run's verdict with nothing to say so, and a gate whose verdict may
# belong to someone else is not a gate.  Do not collapse these back to a single
# directory.  The logs and the shard scratch go under `logs/gate/run-<pid>`, and
# `logs/gate/latest` points at the newest, which is what to tail.  Under `logs/`, not
# `target/`: `lein jar`, `lein install` and `lein clean` empty `target/`, and one of them
# during a gate deletes its shard logs, so the gate finds no exit marker and records the
# run as interrupted.  `runlog_prune` keeps the newest GATE_KEEP_RUNS directories.
#
# The **timings** do not move with them: they are feedback for the next run rather than
# output of this one, so every run in the checkout shares `logs/test-timings.tsv`
# (`scripts/test-parallel.sh`), where neither a per-run directory nor `lein clean`
# reaches them.
#
# ^C takes the stages with it and says so: every stage runs in a process group of its
# own, the handler signals those groups, and the run directory gets an `INTERRUPTED`
# file plus a line in each stage log that had started.  That is what keeps `latest`
# from pointing at a half-run nobody can tell from a verdict.
#
# Exit: 0 when every stage passed, 1 when one failed, 130 when interrupted.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail   # NOT -e: every stage must run even after one fails.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# The revision and the dirty state, shared with the two suite scripts.  A verdict
# names the tree it is a verdict about: it goes on the banner, on the closing line,
# and at the top of every stage log, so a log read an hour later — or quoted into a
# report — says what it was taken against.
# shellcheck source=scripts/lib/revision.sh
. "$ROOT/scripts/lib/revision.sh"
# the box-wide gate slots the test stage waits for
# shellcheck source=scripts/lib/slots.sh
. "$ROOT/scripts/lib/slots.sh"
# `runlog_prune`, which rotates the run directories
# shellcheck source=scripts/lib/runlog.sh
. "$ROOT/scripts/lib/runlog.sh"

GATE_ROOT="${GATE_ROOT:-logs/gate}"
OUT="${GATE_OUT:-$GATE_ROOT/run-$$}"
# the test stage reads this, and reading a *different* variable is how the two halves of
# one directory drift apart — set it here rather than letting `test-parallel.sh` default
# on its own, or `GATE_OUT` moves the four stage logs and leaves the shard logs behind
export VAELII_GATE_OUT="$OUT"
export VAELII_GATE_TIMINGS="${VAELII_GATE_TIMINGS:-logs/test-timings.tsv}"
TAIL_LINES=40

fail_fast=0; quick=0; all=0; sequential=0; brief=0; release=0; with_perf=0
jobs="${GATE_JOBS:-}"; skip=(); only=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --fail-fast) fail_fast=1; shift ;;
    --quick)     quick=1; shift ;;
    # perf is opt-in: `--release` is the full gate (lint + test + uberjar + perf), `--perf`
    # adds perf to a fast run without the release framing.  See PERF, below.
    --release)   release=1; shift ;;
    --perf)      with_perf=1; shift ;;
    --all)       all=1; shift ;;
    --brief)     brief=1; shift ;;
    --sequential) sequential=1; shift ;;
    --jobs)      [[ $# -ge 2 ]] || { echo "gate: --jobs needs a value" >&2; exit 2; }
                 jobs="$2"; shift 2 ;;
    # A value is REQUIRED. `shift 2` on a one-element stack shifts nothing and
    # returns 1, so `while [[ $# -gt 0 ]]` never advances and `gate --skip` spins
    # forever instead of complaining.
    --skip)      [[ $# -ge 2 ]] || { echo "gate: --skip needs a value" >&2; exit 2; }
                 skip+=("$2"); shift 2 ;;
    --only)      [[ $# -ge 2 ]] || { echo "gate: --only needs a value" >&2; exit 2; }
                 only+=("$2"); shift 2 ;;
    # the whole header, and not a line range of it: the range was a number to keep
    # in step with the prose above it, and it stopped mid-sentence when nobody did
    -h|--help)   awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' \
                     "${BASH_SOURCE[0]}"; exit 0 ;;
    *) echo "gate: unknown argument $1" >&2; exit 2 ;;
  esac
done

# What this run calls itself, in the banner and the verdict: the release gate is the
# same script with perf on, so it says so rather than reading like a plain gate.
gate_cmd="lein gate"; gate_label="gate"
[[ $release -eq 1 ]] && { gate_cmd="lein release-gate"; gate_label="release gate"; }

# Colour: VAELII_COLOR=always|never forces; otherwise on for a capable terminal.
# `lein gate` pipes our stdout, so key off TERM as well as `-t 1` — TERM survives
# the pipe where the tty test does not.
color=0
case "$(printf '%s' "${VAELII_COLOR:-}" | tr '[:upper:]' '[:lower:]')" in
  always) color=1 ;;
  never)  color=0 ;;
  *) [[ -z "${NO_COLOR:-}" && -z "${CI:-}" \
        && ( -t 1 || ( -n "${TERM:-}" && "${TERM:-}" != dumb ) ) ]] && color=1 ;;
esac
if [[ $color -eq 1 ]]; then
  GREEN=$'\e[32m'; RED=$'\e[1;31m'; DIM=$'\e[2m'; BOLD=$'\e[1m'; RST=$'\e[0m'
else
  GREEN=''; RED=''; DIM=''; BOLD=''; RST=''
fi

# The live perf bar repositions the cursor, so it wants a real terminal — not merely
# colour, which `VAELII_COLOR=always` can force onto a pipe where cursor motion is noise.
live=0; [[ $color -eq 1 && -t 1 ]] && live=1

# ---- interruption -------------------------------------------------------
#
# A gate is minutes long, so it gets interrupted; what it must not do is leave the
# stages running and the directory reading like a verdict.  Two halves:
#
#   - **the stages go with it.**  Every stage is backgrounded and `wait`ed on — a trap
#     can interrupt `wait`, where a foreground child swallows the ^C — and `set -m`
#     puts each job in a process group of its own, so one signal reaches every process
#     a stage is: the `lein` wrapper, its JVM, and the shard JVMs `test-parallel.sh`
#     forks.  Signalling the pid alone kills one and orphans the rest.  `set -m` also
#     un-does the rule that a background job in a job-control-less shell has SIGINT set
#     to IGNORED — an exec'd JVM inherits that, and a JVM deaf to the very signal the
#     user pressed is what outlives the shell it was started from.  SIGTERM first, so a
#     JVM runs its shutdown hooks, then SIGKILL for whatever will not go.  This is the
#     same shape, and for the same reasons, as `scripts/test-backends.sh`.
#   - **the directory says so.**  `INTERRUPTED` lands in `$OUT`, and a line goes into
#     each stage log that had started — the stage logs are what a reader tails, and a
#     partial one whose last line is a pass reads exactly like a stage that passed.
set -m
stage_pgids=()
spawned_pid=""

spawn () {                     # spawn <log> <cmd...>; the pid lands on $spawned_pid
  local log="$1" pgid; shift
  # `< /dev/null` is what keeps a stage RUNNING.  Its group is not the terminal's
  # foreground group, and leiningen pumps its own stdin into the project subprocess —
  # so a gate started from a terminal reads the tty from the background, takes SIGTTIN,
  # and the whole group STOPS: 0% CPU, an empty log, indistinguishable from a hang
  # until `ps` shows the state as `T`.  No stage has any use for stdin.
  "$@" < /dev/null >>"$log" 2>&1 &
  spawned_pid=$!
  pgid=$(ps -o pgid= -p "$spawned_pid" 2>/dev/null | tr -d ' ')
  stage_pgids+=("${pgid:-$spawned_pid}")
}

# Two codes for one fact: shellcheck 0.10 split "this function is never called" out of
# SC2317 into SC2329, so naming only the new one leaves the script red on every
# older shellcheck.  Name both, and a contributor and CI reach the same verdict.
# shellcheck disable=SC2317,SC2329  # invoked from the INT/TERM trap below
stop_stages () {
  [[ ${#stage_pgids[@]} -gt 0 ]] || return 0
  local g alive
  for g in "${stage_pgids[@]}"; do kill -TERM "-$g" 2>/dev/null; done
  for _ in $(seq 1 20); do                # up to 5s of shutdown hooks
    alive=0
    for g in "${stage_pgids[@]}"; do kill -0 "-$g" 2>/dev/null && alive=1; done
    [[ $alive -eq 0 ]] && return 0
    sleep 0.25
  done
  for g in "${stage_pgids[@]}"; do kill -KILL "-$g" 2>/dev/null; done
}

# shellcheck disable=SC2317,SC2329  # ditto — reached only through `interrupted`
note_interrupted () {          # note_interrupted <signal-name>
  local sig="$1" note s
  note="gate interrupted (SIG$sig) at $(date '+%Y-%m-%d %H:%M:%S'), $(revision_line)"
  {
    echo "$note"
    echo
    echo "The stage logs beside this file are partial: the stages were killed where"
    echo "they stood, so a log whose last line passes is a stage that had not yet"
    echo "reached whatever would have failed.  Nothing in this directory is a verdict."
  } >"$OUT/INTERRUPTED" 2>/dev/null || true
  for s in lint test uberjar perf reflect jvm; do
    if [[ -f "$OUT/$s.log" ]]; then
      printf '\n# %s — killed, not finished\n' "$note" >>"$OUT/$s.log" 2>/dev/null || true
    fi
  done
}

# shellcheck disable=SC2317,SC2329  # ditto — `trap 'interrupted INT' INT`
interrupted () {               # interrupted <signal-name>
  trap - INT TERM              # a second one is the OS's now
  printf '\e[?25h'             # the perf bar may have hidden the cursor; put it back
  printf '\n%sgate interrupted (SIG%s)%s %s— stopping the stages%s\n' \
    "$RED" "$1" "$RST" "$DIM" "$RST"
  # A bare `wait` reaps every stage, not just the one being waited on when the signal
  # landed — under `lint ‖ test` there are two.  2>/dev/null over both: reaping a
  # signalled job is where bash prints its `Terminated: 15` report, one line per process.
  { stop_stages; wait; } 2>/dev/null
  note_interrupted "$1"
  printf '%s✗ gate interrupted%s — no verdict; partial logs in %s\n' "$RED" "$RST" "$OUT"
  exit 130
}

# Both loops are guarded on the array's length rather than expanding it blind:
# this is bash 3.2 (what macOS ships), where `"${a[@]}"` on an *empty* array under
# `set -u` is an unbound-variable error rather than an empty list.
wanted () {                    # is stage $1 in this run?
  local s="$1" x
  if [[ ${#only[@]} -gt 0 ]]; then
    for x in "${only[@]}"; do [[ "$x" == "$s" ]] && return 0; done
    return 1
  fi
  if [[ ${#skip[@]} -gt 0 ]]; then
    for x in "${skip[@]}"; do [[ "$x" == "$s" ]] && return 1; done
  fi
  return 0
}

[[ -z "${GATE_OUT:-}" ]] && runlog_prune "$GATE_ROOT" "${GATE_KEEP_RUNS:-40}"
mkdir -p "$OUT" || exit 1
# `latest` is a convenience and never a source of truth: it is repointed per run, so a
# concurrent gate moves it under you.  Tail it to watch; cite `$OUT` when reporting.
ln -sfn "$(basename "$OUT")" "$GATE_ROOT/latest" 2>/dev/null || true
pass=0; fail=0; failed=(); skipped=()

# Armed here rather than at the top: the handler writes `INTERRUPTED` into `$OUT`, and
# before this line there is neither a directory to write it to nor a stage to stop.
trap 'interrupted INT' INT
trap 'interrupted TERM' TERM
# `interrupted` exits through this trap too, so a held gate slot is released on every exit
trap gate_slot_release EXIT

# The banner, in `announce`'s shape: what this gate is a verdict about, and where
# its logs are.  Read once here and again at the end, because a gate is minutes
# long on a checkout several writers work in.
gate_rev=$(revision_hash)
# Each banner leads with the command that reproduces that section, so the whole
# line copy-pastes to re-run it and the `#` turns the blurb and log path into a
# shell comment.  No `==>`/label gutter before the command — that would break the
# paste.  The gate affords this where the matrix cannot: three short stages, not a
# dozen-wide column of `-Dvaelii.disk.dir=…` launches (test-matrix.sh says why).
printf '%s%s%s  %s# %s — logs in %s%s\n' \
  "$BOLD" "$gate_cmd" "$RST" "$DIM" "$(revision_line)" "$OUT" "$RST"

announce () {                  # announce <name> <blurb> <cmd...>
  local name="$1" blurb="$2"; shift 2
  # command first so the whole line pastes to re-run the stage; the blurb and log
  # path follow the `#` as a comment.  The stage name is not repeated — the command
  # and the `<name>.log` path on this same line already say which stage it is.
  # The uberjar stage's command is a function of this script, so its pasteable form is
  # the gate invocation that runs it.
  local cmd="$*"
  [[ "$name" == uberjar ]] && cmd="lein gate --only uberjar"
  printf '%s%s%s  %s# %s → %s%s\n' \
    "$BOLD" "$cmd" "$RST" "$DIM" "$blurb" "$OUT/$name.log" "$RST"
}

# ---- what each stage actually checked ------------------------------------
#
# A stage row is a verdict and not a list of checks.  `✓ lint` and `✓ perf` each stand
# for many independent checks, and four green rows cannot tell a gate that covered
# something from one that skipped it — which is the question somebody quoting a
# green gate is actually being asked, and the reason `--only` and `--skip` exist
# at all.  So each passing stage prints what it ran.
#
# **Read back out of each stage's own log, never listed here.**  Every stage
# already prints its own list of checks; a second copy in this file would be one more
# thing to drift, and it would drift silently, because nothing compares the two.
# The cost is that this parses another script's output — so each case matches on
# that script's *indentation contract* rather than on its wording, which is the
# part that does not move when somebody rewrites a summary line.
#
# Passing stages only: a failing one prints its log tail, which is this and more.
strip_ansi () { sed 's/\x1b\[[0-9;]*m//g'; }

stage_detail () {              # stage_detail <name>
  [[ $brief -eq 0 ]] || return 0
  local name="$1" log="$OUT/$1.log" names
  [[ -r "$log" ]] || return 0
  case "$name" in
    lint)
      # lint.sh indents every check row by two and nothing else — not its header,
      # not its verdict — so this is its check list verbatim, the clj-kondo version
      # note included when it fires.
      grep '^  ' "$log" | sed 's/^  /        /' ;;
    perf)
      # Thirty-nine names is a list rather than a column. The log's own closing
      # line owns the count; these are what the count was over. Wrapped under a
      # hanging indent computed from the label, so a run with a three-digit count
      # still lines up.
      names=$(grep -oE '^  [a-z][a-z0-9-]+ +(PASS|FAIL)' "$log" \
                | awk '{print $1}' | paste -sd, - | sed 's/,/, /g')
      [[ -n "$names" ]] || return 0
      printf '%s\n' "$names" | fold -s -w 64 | sed 's/[[:space:]]*$//' \
        | awk -v n="$(grep -c -E '^  [a-z][a-z0-9-]+ +(PASS|FAIL)' "$log")" '
            NR == 1 { label = sprintf("        %s check(s): ", n)
                      pad = sprintf("%*s", length(label), "")
                      print label $0; next }
            { print pad $0 }' ;;
    test)
      # The shard banner and the aggregate, which together say how much ran and
      # how it was cut up. Namespace names are 222 lines and live in the log.
      grep -hoE 'running [0-9]+ namespaces at [^ ]+ across [0-9]+ shard\(s\)' "$log" \
        | head -1 | sed 's/^/        /'
      grep -hoE 'Ran [0-9]+ tests containing [0-9]+ assertions' "$log" \
        | tail -1 | sed 's/^/        /' ;;
    reflect|jvm)
      grep -vE '^#|^\s*$' "$log" | head -3 | sed 's/^/        /' ;;
    uberjar)
      grep -E '^uberjar: ' "$log" | sed 's/^uberjar: /        /' ;;
  esac
}

report_stage () {              # report_stage <name> <exit-code> <seconds>
  local name="$1" code="$2" t1="$3" log="$OUT/$1.log"
  if [[ $code -eq 0 ]]; then
    printf '    %s✓%s %-5s %s[%ds]%s\n' "$GREEN" "$RST" "$name" "$DIM" "$t1" "$RST"
    if [[ $color -eq 1 ]]; then stage_detail "$name"
    else stage_detail "$name" | strip_ansi; fi
    pass=$((pass + 1))
  else
    printf '    %s✗ %-5s FAILED (exit %d)%s %s[%ds]%s\n' \
      "$RED" "$name" "$code" "$RST" "$DIM" "$t1" "$RST"
    printf '%s' "$DIM"
    # What to echo under a red stage depends on what its log is.  lint.sh already
    # prints one line per passing check and the full detail of only the FAILED
    # ones, so the whole of that report is the useful thing — a 40-line tail cuts
    # the earliest failed check (drift and kondo run before cljfmt) off the top and
    # hands you the last check's rows instead, which is how a red `drift kondo`
    # shows nothing but a cljfmt diff.  test and perf logs are thousands of lines,
    # so those stay a tail.  `^#` drops the revision header.
    if [[ "$name" == lint ]]; then
      while IFS= read -r line; do printf '      %s\n' "$line"; done \
        < <(grep -v '^#' "$log")
    else
      while IFS= read -r line; do printf '      %s\n' "$line"; done \
        < <(tail -n "$TAIL_LINES" "$log")
    fi
    printf '%s' "$RST"
    fail=$((fail + 1)); failed+=("$name")
  fi
}

# ---- the live perf bar ---------------------------------------------------
#
# perf runs about an hour of scaling checks and reports them all at once at the end, so its stage
# would otherwise be a blank wait.  Under a live terminal it gets a filling bar instead.
# `vaelii.bench.perf` names its check total in the opening banner and prints a
# `perf-progress k/total …` marker as each check finishes; `perf_bar` reads the total from
# the banner and counts the markers.  The bar is the matrix's shape — filled green, the
# unreached tail dim grey (scripts/test-matrix.sh carries the same glyphs and the
# non-UTF-8-locale note on why `${s}` is braced).
bar () {                                            # bar <reached> <total> <width>
  local reached="$1" total="$2" w="$3" fill i s=""
  (( total < 1 )) && total=1
  fill=$(( reached * w / total )); (( fill > w )) && fill=w
  s="${GREEN}"
  for ((i = 0; i < w; i++)); do
    if   (( i <  fill )); then s="${s}━"
    elif (( i == fill )); then s="${s}╾${DIM}"
    else                       s="${s}─"
    fi
  done
  printf '%s%s' "$s" "$RST"
}

# Repaint a one-line bar for the perf stage while <pid> runs, in place with `\r`, then
# erase it so `report_stage` prints the verdict where it stood.  The `sleep` is backgrounded
# and waited on for the same reason the stages are — a foreground `sleep` swallows the ^C
# and the INT trap never runs (see the interruption note above).
perf_bar () {                                       # perf_bar <pid> <log>
  local pid="$1" log="$2" total reached
  printf '\e[?25l'                                  # hide the cursor while it repaints
  while kill -0 "$pid" 2>/dev/null; do
    total=$(grep -oE '[0-9]+ check\(s\)' "$log" 2>/dev/null | grep -oE '[0-9]+' | head -1)
    [[ -n "$total" ]] || total=0
    reached=$(grep -c '^perf-progress ' "$log" 2>/dev/null); reached=${reached:-0}
    printf '\r\e[K    %s  %s%s/%s%s' \
      "$(bar "$reached" "$total" 28)" "$DIM" "$reached" "$total" "$RST"
    sleep 0.5 & wait $! 2>/dev/null
  done
  printf '\r\e[K\e[?25h'                            # erase the bar; the verdict prints here
}

run_stage () {                 # run_stage <name> <blurb> <cmd...>
  local name="$1" blurb="$2"; shift 2
  if ! wanted "$name"; then skipped+=("$name"); return 0; fi

  local t0 code
  echo                         # a blank line sets each stage off as its own chunk
  announce "$name" "$blurb" "$@"
  t0=$SECONDS
  # Captured, never piped: a pipeline reports the *last* command's status, which
  # is how a green gate over a red suite happens.  The header first and the stage
  # appended after it — a `#` line the readers of these logs cannot match.
  #
  # Spawned and waited for rather than run in the foreground, so this stage is a
  # process group the interrupt handler can reach.  `wait` is interruptible, which
  # is what lets that handler run at all while a stage is going.
  revision_header "$name" >"$OUT/$name.log"
  [[ "$name" == test ]] && gate_slot_note >>"$OUT/$name.log"
  spawn "$OUT/$name.log" "$@"
  # perf alone gets the live bar: it is the one stage that runs by itself with nothing to
  # show meanwhile.  The bar loop returns when the process exits, and the `wait` below then
  # reaps its retained status — polling with `kill -0` never consumed it.
  [[ "$name" == perf && $live -eq 1 ]] && perf_bar "$spawned_pid" "$OUT/$name.log"
  wait "$spawned_pid" 2>/dev/null     # 2>/dev/null: the job-done notice
  code=$?
  report_stage "$name" "$code" "$((SECONDS - t0))"
  [[ $code -ne 0 && $fail_fast -eq 1 ]] && return 1
  return 0
}

# admit_test takes a gate slot for the test stage, waiting while every slot is held.  Under
# GATE_NO_WAIT=1 with none free it stops the stages already running and exits 75.  GATE_SLOT
# is exported so the `lein test-parallel` the stage runs takes no second slot.
admit_test () {
  local rc=0
  gate_slot_take "$gate_cmd" "$@" || rc=$?
  export GATE_SLOT
  if [[ $rc -ne 0 ]]; then
    { stop_stages; wait; } 2>/dev/null
    printf '%s✗ %s not run%s — no gate slot free and GATE_NO_WAIT is set\n' "$RED" "$gate_label" "$RST"
    exit "$rc"
  fi
  [[ $GATE_SLOT_WAITED -gt 0 ]] && printf '  %swaited %s for a gate slot%s\n' \
    "$DIM" "$(lock_duration "$GATE_SLOT_WAITED")" "$RST"
  return 0
}

# gate_slot_note prints the test log's line on the slot this gate holds and the wait for it.
gate_slot_note () {
  [[ -n "${GATE_SLOT:-}" ]] || return 0
  printf '# waited %s for a gate slot (%s)\n' "$(lock_duration "$GATE_SLOT_WAITED")" \
    "$(basename "$GATE_SLOT")"
}

# The reflection ratchet's other half.  `scripts/check-reflection.sh` compiles src and
# bench; the **test tree** is compiled by `lein test` itself under the same
# `*warn-on-reflection*`, so its warnings are already in this stage's log and reading
# them adds no work.  Compiling the test tree in the lint pass instead would take it
# from 8 seconds to 74.  The split is stated in that script's header, and this is the
# half it names — the incident the whole ratchet exists for happened in `test/`.
check_test_reflection () {
  wanted test || return 0
  [[ -r "$OUT/test.log" ]] || return 0
  local t0=$SECONDS rc=0
  revision_header reflect >"$OUT/reflect.log"
  # `lein test-parallel` keeps each shard's compile output in that shard's log and puts
  # only the summary in test.log, so the warnings are read from all of them.
  cat "$OUT/test.log" "$OUT"/test.shard-*.log >"$OUT/test.reflect.log" 2>/dev/null
  REFLECTION_LOG="$OUT/test.reflect.log" bash scripts/check-reflection.sh \
    >>"$OUT/reflect.log" 2>&1 || rc=$?
  report_stage reflect "$rc" "$((SECONDS - t0))"
}

# The JVM warnings in the lint and test logs, every shard's included.  Each names a
# permission a JVM wanted and was not given, or an option it no longer takes: a
# restricted native call (JNA), a `sun.misc.Unsafe` caller (aircompressor, under nippy),
# a dynamically loaded agent, a deprecated `-XX:` flag, and the launcher's CLASSPATH
# leaking into a nested `lein`.  project.clj's `:jvm-opts` and `:shell` answer the ones
# known today; this is what goes red when a dependency or a new JDK adds one.
# shellcheck disable=SC2016  # the $ is a literal in the pattern
JVM_WARNING='^WARNING: (A restricted method|A terminally deprecated method|A Java agent has been loaded dynamically|You have \$CLASSPATH set)|VM warning:'
check_jvm_warnings () {
  local t0=$SECONDS rc=0 logs=() f hits
  for f in "$OUT/lint.log" "$OUT/test.log" "$OUT"/test.shard-*.log; do
    [[ -r "$f" ]] && logs+=("$f")
  done
  [[ ${#logs[@]} -gt 0 ]] || return 0
  revision_header jvm >"$OUT/jvm.log"
  hits=$(grep -hE "$JVM_WARNING" "${logs[@]}" | sort | uniq -c | sort -rn)
  if [[ -n "$hits" ]]; then
    printf '%s\n' "$hits" >>"$OUT/jvm.log"; rc=1
  else
    echo "no JVM warnings in ${#logs[@]} stage log(s)" >>"$OUT/jvm.log"
  fi
  report_stage jvm "$rc" "$((SECONDS - t0))"
}

# One test JVM under `--sequential`, and under `--fail-fast` too: stopping at the
# first failure is a claim about *order*, and there is no order among stages that
# started together.
[[ $fail_fast -eq 1 ]] && sequential=1

if [[ $sequential -eq 1 ]]; then
  test_cmd=(lein test); [[ $all -eq 1 ]] && test_cmd+=(:all)
else
  test_cmd=(lein test-parallel); [[ $all -eq 1 ]] && test_cmd+=(:all)
  [[ -n "$jobs" ]] && test_cmd+=(--jobs "$jobs")
fi
test_blurb="the suite$([[ $all -eq 1 ]] && echo " (:all)")$([[ $sequential -eq 0 ]] && echo ", sharded")"

perf_args=(perf)
[[ $quick -eq 1 ]] && perf_args+=(--quick)
[[ -n "${PERF_TOLERANCE:-}" ]] && perf_args+=(--tolerance "$PERF_TOLERANCE")

# The uberjar stage.  `lein uberjar` AOT-compiles every namespace, which no other stage
# does, so a class file name past a filesystem's 255-byte limit (#179) or a failure that
# only an AOT load shows is caught here.  The build goes to this run's directory with
# auto-clean off: lein's clean deletes all of `target/` under `:target-path "target/%s"`,
# and with it every concurrent gate's logs.  A jar that loads `vaelii.core` in a JVM of its
# own passes, and its build directory (about 165 MB) is deleted; a failure keeps it.
# shellcheck disable=SC2317,SC2329  # invoked through run_stage's "$@"
build_uberjar () {
  local dir="$OUT/uberjar" jar
  lein update-in : merge "{:target-path \"$dir/%s\" :auto-clean false}" -- uberjar || return
  jar=$(find "$dir" -name '*-standalone.jar' | head -1)
  [[ -n "$jar" ]] || { echo "uberjar: no standalone jar under $dir"; return 1; }
  "${JAVA_CMD:-java}" -cp "$jar" clojure.main \
    -e "(require 'vaelii.core 'vaelii.host.serve 'vaelii.web)" || return
  echo "uberjar: $(basename "$jar") ($(du -h "$jar" | awk '{print $1}')) loads vaelii.core and the two servers"
  command rm -rf "$dir"
}

# The uberjar stage runs under `--release` or `--only uberjar`, after test and before
# perf, which runs alone.
uberjar_opted=0
[[ $release -eq 1 ]] && uberjar_opted=1
if [[ ${#only[@]} -gt 0 ]]; then
  for x in "${only[@]}"; do [[ "$x" == uberjar ]] && uberjar_opted=1; done
fi

# perf is opt-in — the fast gate is lint + test.  It runs when the release gate
# asks for it (`--release`), when `--perf`/`--quick` name it, or when `--only perf`
# does.  `wanted perf` still applies on top, so `--skip perf` and a non-perf
# `--only` both keep it off.
perf_opted=0
[[ $release -eq 1 || $with_perf -eq 1 || $quick -eq 1 ]] && perf_opted=1
if [[ ${#only[@]} -gt 0 ]]; then
  for x in "${only[@]}"; do [[ "$x" == perf ]] && perf_opted=1; done
fi

if [[ $sequential -eq 1 ]]; then
  # Cheapest first, so `--fail-fast` gets you the fast answer first.
  run_stage lint "static analysis" lein lint || true
  if ! [[ $fail -gt 0 && $fail_fast -eq 1 ]]; then
    wanted test && admit_test "${test_cmd[@]}"
    run_stage test "$test_blurb" "${test_cmd[@]}" || true
    gate_slot_release
  fi
  check_test_reflection
  check_jvm_warnings
  [[ $uberjar_opted -eq 1 ]] && { [[ $fail -gt 0 && $fail_fast -eq 1 ]] || run_stage uberjar "the standalone jar" build_uberjar || true; }
  [[ $perf_opted -eq 1 ]] && { [[ $fail -gt 0 && $fail_fast -eq 1 ]] || run_stage perf "the scaling claims" lein "${perf_args[@]}" || true; }
else
  # lint ‖ test, then perf alone — see SHAPE at the top.  Both start silently; each
  # one's header prints WITH its verdict and detail as a single chunk when it
  # finishes (below), so a concurrent stage is still one contiguous block to scan
  # rather than a header up top and a result far down.  A one-line note names what
  # is running so the console is not blank while they go.
  lint_pid=""; test_pid=""; lint_t0=0; test_t0=0
  if wanted lint; then
    lint_t0=$SECONDS
    revision_header lint >"$OUT/lint.log"
    spawn "$OUT/lint.log" lein lint; lint_pid=$spawned_pid
  else skipped+=(lint); fi
  if wanted test; then
    admit_test "${test_cmd[@]}"
    test_t0=$SECONDS
    revision_header test >"$OUT/test.log"
    gate_slot_note >>"$OUT/test.log"
    spawn "$OUT/test.log" "${test_cmd[@]}"; test_pid=$spawned_pid
  else skipped+=(test); fi

  running=()
  [[ -n "$lint_pid" ]] && running+=("lint")
  [[ -n "$test_pid" ]] && running+=("test")
  if [[ ${#running[@]} -gt 0 ]]; then
    run_note="${running[*]}"; run_note="${run_note// / ‖ }"
    printf '  %srunning %s …%s\n' "$DIM" "$run_note" "$RST"
  fi

  # Reported lint-then-test regardless of which finishes first, so the report reads
  # top to bottom; each `wait` blocks until that stage is done.  Its exit code is
  # captured into a variable BEFORE the header prints — announce's own $? would
  # otherwise clobber the one report_stage needs.
  if [[ -n "$lint_pid" ]]; then
    wait "$lint_pid" 2>/dev/null; lint_rc=$?
    # A lint that ended while this gate waited for a slot can be gone from bash's job
    # table by now, and `wait` then returns 127 for a lint that passed (a 74-minute
    # wait, 2026-10-10).  Its log's verdict line records the same outcome.
    if [[ $lint_rc -eq 127 ]]; then
      if sed 's/\x1b\[[0-9;]*m//g' "$OUT/lint.log" | grep -qE '^lint: ([0-9]+)/\1 clean'; then
        lint_rc=0
      else
        lint_rc=1
      fi
    fi
    echo; announce lint "static analysis" lein lint
    report_stage lint "$lint_rc" "$((SECONDS - lint_t0))"
  fi
  if [[ -n "$test_pid" ]]; then
    wait "$test_pid" 2>/dev/null; test_rc=$?
    gate_slot_release
    echo; announce test "$test_blurb" "${test_cmd[@]}"
    report_stage test "$test_rc" "$((SECONDS - test_t0))"
  fi
  check_test_reflection
  check_jvm_warnings

  [[ $uberjar_opted -eq 1 ]] && { run_stage uberjar "the standalone jar" build_uberjar || true; }
  [[ $perf_opted -eq 1 ]] && { run_stage perf "the scaling claims" lein "${perf_args[@]}" || true; }
fi

echo
if [[ ${#skipped[@]} -gt 0 ]]; then
  printf '%sskipped: %s%s\n' "$DIM" "${skipped[*]}" "$RST"
fi

# ---- owed advisories: what this gate left out that the pending diff owes ----------
#
# The fast gate drops perf and the `^:slow` half, and each has a changed-file regex that
# names it when the diff about to land touches its files.  Both are non-blocking: a
# reminder, not a refusal — a gate you run ten times while developing must not fail on
# every hot-path edit.  An owed run answers for every commit it contains, so one green run
# at the newest commit of a batch covers the batch; the advisory asks for a run at a
# revision holding these files, not a run per commit.
#
# PERF_SENSITIVE_RE.  The fast gate drops perf, and two things buy that back (see PERF in
# the header): `assert_cost_test` asserts the CONSTANT-cost class in the test stage, and CI
# runs the ratios.  What neither the fast gate nor a glance catches is a change to the
# retrieval / inference / index / TMS core that turns a cost SUPER-LINEAR.  The set is the
# files whose code runs inside a `perf.clj` claim's timed body or a cost test's measured
# region, plus the backward-chaining and matcher files (`levels`, `tactics`, `rete`,
# `abduce`) that sit on a read path no claim times yet.  A file a claim times belongs here
# even when it was split out of one that is (`assert_entry`, `settle_phases`,
# `nat_maintenance`, the `types/` records); a file no claim or cost test executes does not
# (the public API's shims, io, and the domain reasoners without a claim).  Edit it here
# when a claim starts timing a file or the hot surface moves.
PERF_SENSITIVE_RE='^src/vaelii/core\.clj$|^src/vaelii/impl/(provers|resolution|except|inherit|chain|settle|settle_phases|recheck|clashes|discovery|decide|decide/[a-z_]+|journal|recovery|reasoning_image|vantage|assert_entry|jtms|dense_jtms|caches|taxonomy|nat|nat_maintenance|context_nat|plan|tactics|rules|rete|strength|levels|special|wiring|checks|violations|abduce|sentex|wff|naming|kb|memory|observe|reindex|literal_cache|tokens|columnar|kv|dense_kv|dense_roots|rewrite|reads|feed|integrate|quasiquote|skolem|capabilities|profile|qcn|qcn_kb|space|stp|quality|handle_set|overlay/kv|overlay/frozen|asp/solve_context|sign|asp/label|asp/prover)\.clj$|^src/vaelii/impl/(disk|types)/'
#
# SLOW_OWED_RE.  The engine files the `^:slow` tests drive, in three groups: the index
# (the retrieval, record and posting stores the index oracles compare), the TMS (the
# belief network, settle and the checks the order and concurrency sweeps exercise) and
# inference (the chainers, provers, taxonomy and the qualitative reasoners the scenario
# and whole-KB round trips run).  The slow tests outside all three (the aspif solver, the
# catalog load, the feed socket, the koinii wire scenarios) name no file here.  Edit it
# when a slow test starts driving a file, or a file's slow tests lose their marks.
SLOW_OWED_RE='^src/vaelii/core\.clj$|^src/vaelii/impl/(resolution|except|literal_cache|memory|columnar|dense_kv|dense_roots|reindex|tokens|kv|kb|reads|journal|recovery|caches|jtms|dense_jtms|settle|settle_phases|recheck|clashes|discovery|decide|decide/[a-z_]+|vantage|integrate|assert_entry|checks|violations|strength|levels|observe|chain|rete|provers|inference|tactics|plan|rules|inherit|taxonomy|special|sentex|wff|nat|nat_read|nat_maintenance|context_nat|rewrite|abduce|qcn|qcn_kb|stp)\.clj$|^src/vaelii/impl/types/(trie|postings|snapshot|dense_roots)\.clj$|^src/vaelii/impl/disk/index_snapshot\.clj$'
#
# RED_OWED_RE.  The files the `^:red` tests drive: every one asserts and asks through
# `vaelii.core`, so the inference, TMS and context files answer for them, and the temporal
# reasoners and the shipped ontology answer for `temporal_capability_test` and
# `pr_status_true_when_test`.  A test file holding a `^:red` mark owes the run too, and
# `git grep` names those, so the list cannot drift from the marks.  Edit the regex when a
# red test starts driving a file.
RED_OWED_RE='^src/vaelii/core\.clj$|^src/vaelii/impl/(resolution|assert_entry|kb|budget|rewrite|except|inherit|chain|settle|settle_phases|recheck|clashes|discovery|decide|decide/[a-z_]+|vantage|jtms|dense_jtms|taxonomy|nat|nat_read|nat_maintenance|context_nat|plan|tactics|rules|rete|strength|levels|special|checks|violations|provers|inference|abduce|wff|capabilities|qcn|qcn_kb|stp|interval|point|timepoint|duration|calendar|datetime|fluent|projection|relative|scenario|space)\.clj$|^resources/kb/'
red_marked=$(git grep -lE '\^:red|\^\{:red true' -- test 2>/dev/null | sed 's/[.]/\\./g; s/^/^/; s/$/$/' | paste -sd'|' -)
[[ -n "$red_marked" ]] && RED_OWED_RE="$RED_OWED_RE|$red_marked"

# perf_groups_for_path.  The `groups` keys of bench/vaelii/bench/perf.clj whose checks
# time a changed engine file's code, so the perf owed line names `lein perf --only` over
# them.  A file not named here prints `all`, which owes the whole run.  The map is a floor:
# a change whose reach is wider than its file's row owes the whole run too.
perf_groups_for_path () {
  case "${1#src/vaelii/impl/}" in
    kv.clj|reads.clj)                             echo all ;;
    dense_kv.clj|dense_roots.clj|columnar.clj|reindex.clj|tokens.clj|\
    literal_cache.clj|overlay/*|disk/*|types/*)  echo index ;;
    taxonomy.clj)                                 echo taxonomy membership inherit placement clashes ;;
    except.clj)                                   echo exceptions placement ;;
    inherit.clj)                                  echo inherit clashes ;;
    clashes.clj|discovery.clj)                    echo clashes ;;
    decide.clj|decide/*|journal.clj)              echo placement argtypes membership tuples clashes ;;
    recovery.clj|reasoning_image.clj)             echo recover ;;
    qcn.clj|qcn_kb.clj|space.clj|stp.clj|sign.clj|quality.clj|context_nat.clj|plan.clj|asp/*)
                                                  echo solvers ;;
    nat.clj|nat_maintenance.clj|feed.clj)         echo chaining ;;
    *)                                            echo all ;;
  esac
}

# What is about to land: committed-since-upstream ∪ staged ∪ unstaged.  Fall back to
# origin/main, then to the uncommitted diff alone, when no upstream is tracked.
pending_files () {
  command -v git >/dev/null 2>&1 || return 0
  git rev-parse --git-dir >/dev/null 2>&1 || return 0
  local base
  base=$(git merge-base '@{upstream}' HEAD 2>/dev/null) \
    || base=$(git merge-base origin/main HEAD 2>/dev/null) || base=""
  { [[ -n "$base" ]] && git diff --name-only "$base" HEAD
    git diff --name-only HEAD
    git diff --cached --name-only; } 2>/dev/null | sort -u
}

owed_advisory () {                 # owed_advisory <label> <regex> <what> <why> <command>
  local hot n
  hot=$(printf '%s\n' "$pending" | grep -E "$2" || true)
  [[ -n "$hot" ]] || return 0
  n=$(printf '%s\n' "$hot" | grep -c .)
  printf '%s⚠ %s owed%s — %d %s file(s) about to land, and this gate did not run it:\n' \
    "$BOLD" "$1" "$RST" "$n" "$3"
  printf '%s\n' "$hot" | head -8 | sed 's/^/    /'
  [[ $n -gt 8 ]] && printf '    … and %d more\n' "$((n - 8))"
  printf '  %s\n' "$4"
  printf '  run %s at a revision holding them; one green run at the newest commit answers for every earlier one.\n\n' \
    "$5"
}
pending=$(pending_files)
perf_groups=$(printf '%s\n' "$pending" | grep -E "$PERF_SENSITIVE_RE" \
  | while read -r f; do perf_groups_for_path "$f"; done | tr ' ' '\n' | sort -u | paste -sd, -)
case ",$perf_groups," in
  *,all,*) perf_cmd="${BOLD}lein perf${RST}" ;;
  *)       perf_cmd="${BOLD}lein perf --only $perf_groups${RST}" ;;
esac
[[ $perf_opted -eq 0 ]] && owed_advisory perf "$PERF_SENSITIVE_RE" hot-path \
  "a change here can turn a cost super-linear — the test stage cannot see that." \
  "${BOLD}lein release-gate${RST} (lint + test + uberjar + perf), or $perf_cmd alone,"
{ [[ $all -eq 0 ]] || ! wanted test; } && owed_advisory slow "$SLOW_OWED_RE" "index / TMS / inference" \
  "the ^:slow half holds the order sweeps and oracles over these files — :default skips it." \
  "${BOLD}lein gate --all${RST} (or ${BOLD}lein test :slow${RST} alone)"
owed_advisory red "$RED_OWED_RE" "red-test" \
  "a red test that passes keeps its mark until a run of the :red selector names it." \
  "${BOLD}lein test-red${RST}"

# The arity readers a perf-ab probe times (`vaelii.bench.ab`: arity-assert, arity-edge-move,
# arity-read, arity-recover).  `decide/arity.clj` is all arity.  `checks.clj`, `kb.clj` and
# `provers.clj` also hold unrelated code, so only a changed line inside a top-level `defn`
# whose name contains `arity`, metadata before the name included, counts (`kb/relation-arity`,
# `provers/relation-variable-arity?`, `checks/variable-arity?`).
ARITY_AB_PROBES=arity-assert,arity-edge-move,arity-read,arity-recover
arity_fns_changed () {             # arity_fns_changed <base> <file>
  local base="$1" file="$2"
  [[ -f "$file" ]] || return 1
  local ranges
  ranges=$(awk '
    /^\(/ { if (start) print start, NR - 1; start = ($0 ~ /^\(defn-? +(\^[^ ]+ +|\^\{[^}]*\} +)*[^ ^]*arity/) ? NR : 0 }
    END    { if (start) print start, NR }' "$file" | paste -sd';' -)
  [[ -n "$ranges" ]] || return 1
  { git diff -U0 "$base" -- "$file"; } 2>/dev/null | awk -v ranges="$ranges" '
    BEGIN { n = split(ranges, r, ";"); for (i = 1; i <= n; i++) { split(r[i], p, " "); lo[i] = p[1]; hi[i] = p[2] } }
    /^@@/ { s = $3; sub(/^\+/, "", s); split(s, q, ","); a = q[1] + 0; c = (q[2] == "") ? 1 : q[2] + 0
            b = (c == 0) ? a : a + c - 1
            for (i = 1; i <= n; i++) if (a <= hi[i] && b >= lo[i]) { found = 1 } }
    END   { exit found ? 0 : 1 }'
}
perf_ab_arity_advisory () {
  local base hot="" f
  base=$(git merge-base '@{upstream}' HEAD 2>/dev/null) \
    || base=$(git merge-base origin/main HEAD 2>/dev/null) || return 0
  while IFS= read -r f; do
    case "$f" in
      src/vaelii/impl/decide/arity.clj) hot+="$f"$'\n' ;;
      src/vaelii/impl/checks.clj|src/vaelii/impl/kb.clj|src/vaelii/impl/provers.clj)
        arity_fns_changed "$base" "$f" && hot+="$f"$'\n' ;;
    esac
  done <<<"$pending"
  [[ -n "$hot" ]] || return 0
  printf '%s⚠ perf-ab owed%s — arity code about to land, and no gate stage times it in absolute ms:\n' "$BOLD" "$RST"
  printf '%s' "$hot" | sed 's/^/    /'
  printf '  %slein perf-ab %s --only %s%s\n' "$BOLD" "$(git rev-parse --short "$base")" "$ARITY_AB_PROBES" "$RST"
  printf '  run it at a revision holding them, from the primary, with the box idle.\n\n'
}
perf_ab_arity_advisory

# The starter load and recover a perf-ab probe times (`vaelii.bench.ab`: starter-load,
# starter-recover).  A shipped KB file or a loader moves both readings of every `lein perf`
# check that loads it, so only the absolute times show it.
STARTER_AB_PROBES=starter-load,starter-recover
perf_ab_starter_advisory () {
  local base hot
  base=$(git merge-base '@{upstream}' HEAD 2>/dev/null) \
    || base=$(git merge-base origin/main HEAD 2>/dev/null) || return 0
  hot=$(printf '%s\n' "$pending" | grep -E '^(resources/kb/(upper|middle)/|src/vaelii/host/(starter|core_context|seed)\.clj$)' || true)
  [[ -n "$hot" ]] || return 0
  printf '%s⚠ perf-ab owed%s — shipped KB content or its loader about to land, and no gate stage times it in absolute ms:\n' "$BOLD" "$RST"
  printf '%s\n' "$hot" | sed 's/^/    /'
  printf '  %slein perf-ab %s --only %s%s\n' "$BOLD" "$(git rev-parse --short "$base")" "$STARTER_AB_PROBES" "$RST"
  printf '  run it at a revision holding them, from the primary, with the box idle.\n\n'
}
perf_ab_starter_advisory

# The revision on the verdict line, since that is the line that gets reported.  A
# gate is minutes long and this tree has several writers, so a commit landing
# inside one is worth naming: the stages then ran against two trees and the
# verdict is about neither.
end_rev=$(revision_hash)
if [[ "$end_rev" == "$gate_rev" ]]; then
  at="at $gate_rev"
else
  at="at $gate_rev, and the tree moved to $end_rev during the run"
fi

if [[ $fail -eq 0 ]]; then
  printf '%s✓ %s passed%s %s — %d stage(s), logs in %s\n' "$GREEN" "$gate_label" "$RST" "$at" "$pass" "$OUT"
  exit 0
fi
printf '%s✗ %s failed%s %s — %s (%d of %d) — full output in %s\n' \
  "$RED" "$gate_label" "$RST" "$at" "${failed[*]}" "$fail" "$((pass + fail))" "$OUT"
exit 1
}
