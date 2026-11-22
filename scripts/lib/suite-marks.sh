#!/usr/bin/env bash
# scripts/lib/suite-marks.sh — the per-namespace progress marks, shared by the two
# scripts that run the whole suite more than once.
#
# `test-backends.sh` varies STORAGE and `test-sweeps.sh` varies the ENGINE
# implementation the suite runs against, but a run is a run: both boot a JVM,
# load every test namespace, and then take twenty minutes saying nothing unless
# somebody makes them.  This file is the making-them, and it lives here so the
# two scripts share one answer rather than two that drift.
#
# What is NOT here: each script's run loop, its interrupt handling and its
# summary.  Those touch variables only the caller has — a disk directory to
# clean, an env list to build — and generalizing them would buy indirection
# rather than reuse.  The rule for what belongs in this file is that it reads
# only its arguments.
#
# Sourced, never executed:
#   . scripts/lib/suite-marks.sh
#
# Every name below is read by the sourcing script and by nothing in here, which is
# what a library is and what SC2034 cannot see across a `.` boundary — hence the
# file-level disable rather than one per assignment.
# shellcheck disable=SC2034

# The revision helpers, which `gate.sh` takes without taking any of this.
# shellcheck source=scripts/lib/revision.sh
. "$(dirname "${BASH_SOURCE[0]}")/revision.sh"
# The `lein test :only` patterns `failing_namespaces` and `failing_tests` read, which the
# CI suite step reads too, as the run goes.
# shellcheck source=scripts/lib/failed-selectors.sh
. "$(dirname "${BASH_SOURCE[0]}")/failed-selectors.sh"

# Whether the run's OUTPUT reaches a terminal — the one switch behind both the
# colour below and the marks-vs-lines default further down.  `-t 1` answers it when
# this script's own stdout IS that terminal, which it is for a direct
# `./scripts/test-shuffle.sh`.  A caller wedged behind a pipe it cannot see past —
# `lein test-shuffle` reaches the script through lein-shell, which always pipes the
# child's stdout — cannot ask `-t 1`, so it sets SUITE_TTY to the answer only it
# holds (the alias reads the leiningen JVM's own `System/console`).  Unset, the
# common case, is just `-t 1` as before.
if [[ -n "${SUITE_TTY:-}" ]]; then
  if [[ "$SUITE_TTY" == 0 ]]; then IS_TTY=0; else IS_TTY=1; fi
elif [[ -t 1 ]]; then IS_TTY=1; else IS_TTY=0; fi

# Colour only when someone is watching; a redirected run stays greppable.
if (( IS_TTY )); then
  GREEN=$'\033[32m'; RED=$'\033[31m'; DIM=$'\033[2m'; BOLD=$'\033[1m'; OFF=$'\033[0m'
else
  GREEN=""; RED=""; DIM=""; BOLD=""; OFF=""
fi
TICK="${GREEN}✔${OFF}"
CROSS="${RED}✘${OFF}"

hms() { printf '%dm%02ds' $(($1 / 60)) $(($1 % 60)); }

# MARKS or LINES: the same progress, rendered for whoever is reading it.
#
# A terminal gets the mark rows below, because a row of ticks is readable while it
# is being *watched* and three lines a backend beats 165.  Everything else — a
# redirect, a pipe, a `nohup … | tail -f`, CI, a scripted shell — gets one line per
# namespace, because a mark row written to a file is the worst of both: a partial
# row is one unterminated line whose count arrives sixty namespaces later, and no
# part of it says which namespace was slow or which one was running when the run
# died.  `SUITE_PROGRESS=marks|lines` forces either.
case "$(printf '%s' "${SUITE_PROGRESS:-auto}" | tr '[:upper:]' '[:lower:]')" in
  marks)   PROGRESS=marks ;;
  lines)   PROGRESS=lines ;;
  auto|"") if (( IS_TTY )); then PROGRESS=marks; else PROGRESS=lines; fi ;;
  *) echo "SUITE_PROGRESS must be marks, lines or auto (got $SUITE_PROGRESS)" >&2; exit 2 ;;
esac

# What a run pipes its output into.  The caller sets `RUN_START=$SECONDS` first, so
# a line can carry the run's own clock rather than the script's.
ns_progress() {
  if [[ "$PROGRESS" == marks ]]; then ns_marks; else ns_lines; fi
}

# what `lein test` compiles before it can run the first namespace — the number the
# wait is proportional to, and NOT the number of marks a run will print: the
# selector narrows what RUNS, never what is loaded, so every run pays this in full.
NS_COUNT=$(find test -name '*_test.clj' | wc -l | tr -d ' ')

# …and how many of them the selector will actually run, which is the denominator the
# marks count towards.  Leiningen prints one `lein test <ns>` header per namespace
# holding at least one SELECTED test, so a namespace whose every test is `^:slow`
# emits nothing under `:default` and would otherwise leave the count short.  Read off
# the source: the three forms that define a test all sit at column 0, and a `^:slow`
# on the `ns` form marks the whole file (which is what leiningen's metadata merge
# means).
TEST_FORM='^\((tu/deftest-kb|deftest|defspec) '
selected_ns_count() {
  local sel="$1" f slow plain count=0
  while IFS= read -r f; do
    if grep -qE '^\(ns +\^:slow' "$f"; then
      slow=1; plain=0
    else
      slow=$(grep -cE "$TEST_FORM\\^:slow" "$f")
      plain=$(grep -cE "${TEST_FORM}[^^]" "$f")
    fi
    case "$sel" in
      :slow)    (( slow  > 0 )) && count=$((count + 1)) ;;
      :default) (( plain > 0 )) && count=$((count + 1)) ;;
      *)        count=$((count + 1)) ;;
    esac
  done < <(find test -name '*_test.clj')
  echo "$count"
}

# How wide a row of marks is: as many groups of ten as the terminal has room
# for, keeping the right-hand column free for the running count.  Ten to a group
# because the point of grouping is to be countable at a glance.
#
# THE SIZE IS ASKED OF `/dev/tty` FIRST, and that is not belt-and-braces.  `tput` reads
# the size from its own stdout, and every script sourcing this file can be reached
# through a pipe — `lein test-backends` and `lein test-matrix` go through lein-shell,
# which always pipes the child's stdout — where `tput` answers terminfo's DEFAULTS, 80
# by 24, rather than the terminal's size.  `/dev/tty` is the controlling terminal
# whatever stdout has been redirected to, so `stty` on it answers where `tput` cannot.
# Where there is no controlling terminal either — CI, a cron, a container — both fail
# and the defaults are the answer.  `SUITE_TTY` already carries the tty question
# across the same boundary for the same reason; this carries the size.
term_size() {                                      # -> "<rows> <cols>"
  local s
  # the `2>/dev/null` is on the GROUP, not on `stty`: where there is no controlling
  # terminal the `</dev/tty` fails during redirection, before `stty` runs, and bash
  # reports that on its own stderr — a diagnostic on every CI run for a probe that is
  # allowed to fail.
  { s=$(stty size </dev/tty); } 2>/dev/null
  [[ "$s" =~ ^[0-9]+\ [0-9]+$ ]] && { printf '%s' "$s"; return; }
  printf '%s %s' "$(tput lines 2>/dev/null)" "$(tput cols 2>/dev/null)"
}
read -r ROWS COLS <<<"$(term_size)"
[[ "$COLS" =~ ^[0-9]+$ ]] && (( COLS >= 40 )) || COLS=80   # a pty can report 0
# The height matters to one caller — `test-matrix.sh` will not paint a frame taller than
# the terminal, because a frame that scrolls cannot be repainted in place.
[[ "$ROWS" =~ ^[0-9]+$ ]] && (( ROWS >= 10 )) || ROWS=24
ROW_GROUPS=$(( (COLS - 13 + 1) / 11 ))
(( ROW_GROUPS < 1 )) && ROW_GROUPS=1
MARKS_PER_ROW=$(( ROW_GROUPS * 10 ))

# One mark per test namespace, printed while the suite runs — the marks alone,
# in rows, which is a progress bar whose bricks each mean something.  A name per
# namespace is 165 lines a run and 1300 a matrix, and reading them is not how
# anybody uses this; where the ✘ falls in the row is.  Names come back after a
# failing run, which is when they answer a question.
#
# `lein test` prints `lein test <ns>` BEFORE running that namespace and
# `lein test :only <ns>/<test>` above every failure inside one, so a namespace's
# verdict is known when the next header (or the closing `Ran N tests`) arrives —
# one namespace of lag, and nothing waits for the run to end.  The failure lines
# name their own namespace, so a report that lands late is still attributed to
# the right one.  `fflush` because the mark is the progress: buffered, it would
# arrive with the summary it exists to precede.
#
# `$RUN_NS_COUNT` is the caller's, set from `selected_ns_count` above once the
# selector is parsed — the one value here that is read rather than computed.
ns_marks() {
  awk -v tick="$TICK" -v cross="$CROSS" -v total="$RUN_NS_COUNT" -v per="$MARKS_PER_ROW" '
    BEGIN { width = per + int((per - 1) / 10); digits = length(total) }
    function blanks(n,   s) { s = ""; while (n-- > 0) s = s " "; return s }
    function emit(   mark) {
      if (ns == "") return
      mark = (ns in bad) ? cross : tick
      if (col == 0) printf("  ")                  # the row indent
      else if (col % 10 == 0) printf(" ")         # the group gap
      printf("%s", mark)
      col++; count++
      if (col == per) endrow(); else fflush()
      ns = ""
    }
    # the count sits in a fixed column, so a partial row is padded to the width
    # a full one would have had rather than left where it happened to stop
    function endrow(   used) {
      if (col == 0) return
      used = col + int((col - 1) / 10)
      printf("%s  %*d/%d\n", blanks(width - used), digits, count, total)
      col = 0
      fflush()
    }
    /^lein test :only / { split($4, part, "/"); bad[part[1]] = 1; next }
    /^lein test [A-Za-z0-9._-]+$/ { emit(); ns = $3; next }
    /^Ran [0-9]+ tests/ { emit(); endrow() }
    END { emit(); endrow() }
  '
}

# The same progress, one line per namespace — what a log, a pipe or CI gets.
#
# Named, counted and timed twice: the namespace's own seconds and the run's, so a
# tail of a 20-minute log answers "where is it, how far in, and what is slow" from
# the last line rather than from a row of identical ticks.  The name is what makes
# it worth the lines: a ✘ says which file to open the moment it happens, and a run
# killed mid-namespace leaves the namespace it was in as the last thing it said.
#
# Bash rather than awk, for the clock: the awk macOS ships has no `systime`, and a
# `date` per namespace is a fork per namespace to learn what `$SECONDS` already
# knows.  The reading rules are `ns_marks`' above, including the one about a
# failure report being attributed to the namespace it names.
ns_lines() {
  local line rest only ns="" bad_ns="" mark count=0 ns_t0=0 now
  local t0="${RUN_START:-$SECONDS}" digits=${#RUN_NS_COUNT}

  # Reached through dynamic scope, so it reads and clears the locals above; a
  # namespace is emitted when the next one starts, which is when its verdict and
  # its duration are both known.
  _ns_line() {
    [[ -z "$ns" ]] && return 0
    now=$SECONDS
    count=$((count + 1))
    if [[ "$bad_ns" == "$ns" ]]; then mark="$CROSS"; else mark="$TICK"; fi
    printf '  %s %*d/%d  %-44s %7s %8s\n' \
      "$mark" "$digits" "$count" "$RUN_NS_COUNT" "$ns" \
      "$(hms $((now - ns_t0)))" "$(hms $((now - t0)))"
    ns=""
  }

  while IFS= read -r line; do
    case "$line" in
      "lein test :only "*)                         # a failure, inside the namespace it names
        only="${line#lein test :only }"; bad_ns="${only%%/*}" ;;
      "lein test "*)
        rest="${line#lein test }"
        [[ "$rest" =~ ^[A-Za-z0-9._-]+$ ]] || continue
        _ns_line; ns="$rest"; ns_t0=$SECONDS ;;
      "Ran "*" tests containing "*) _ns_line ;;
    esac
  done
  _ns_line                                         # a run that died before `Ran`
}

# The two lines clojure.test prints last, tightened into one column, plus the
# failing namespaces a red run should name under its summary.  Both read the log
# rather than the exit code, so a run that died before printing them says "did
# not finish" instead of claiming a count it never reached.
run_summary() {
  grep -aE '^Ran [0-9]+ tests' "$1" | tail -1 \
    | sed -E 's/^Ran ([0-9]+) tests containing ([0-9]+) assertions\.?$/\1 tests, \2 assertions/'
}
run_counts() {
  grep -aE '^[0-9]+ failures, [0-9]+ errors' "$1" | tail -1 | sed 's/\.$//'
}
failing_namespaces() {
  grep -aoE "^lein test :only ${FAILED_SELECTOR_NS}/" "$1" \
    | sed -E 's|^lein test :only ||; s|/$||' | sort -u
}

# The same failures one level finer, `<namespace>/<test>` each — and the level the
# question a red matrix asks second is answered at.  "Which namespace" cannot tell a
# broken test from a backend that disagrees; "which test, under which configurations"
# can: the same test failing under every run is the suite's answer at this revision,
# and a test failing under only some of them is a difference between them, which is the
# whole reason there is more than one run.
failing_tests() {
  grep -aoE "^lein test :only ${FAILED_SELECTOR_NS}/${FAILED_SELECTOR_TEST}" "$1" \
    | sed -E 's|^lein test :only ||' | sort -u
}

# The assertion count alone, for `assertion_deltas_ok` — empty for a run that never
# printed one, which that function skips rather than counting as a zero.
run_assertions() {
  run_summary "$1" | sed -nE 's/^[0-9]+ tests, ([0-9]+) assertions$/\1/p'
}
