#!/usr/bin/env bash
# scripts/coverage.sh — run cloverage over vaelii core and report the
# total form/line coverage %.
#
# Thin wrapper over `lein cloverage` (the task is added by injecting
# lein-cloverage into the root :plugins via `update-in` — see CLOVERAGE_VERSION
# below for why the :dev-profile declaration alone isn't enough). Cloverage
# instruments every namespace under
# src/, runs the test suite against the instrumented code, writes
# an HTML report, and prints a console summary table. This script:
#   - runs it under +test (so the :test env + cleanup injections apply, exactly
#     like `lein test`; cloverage is NOT the `test` task, so :test is not
#     auto-merged — we add it explicitly),
#   - uses the project's `:default` test selector by default (drops :slow /
#     :perf, same as the routine `lein test` loop),
#   - parses the "ALL FILES" row and prints % Forms and % Lines.
#
# Because it instruments the whole core tree and runs the full suite, a run is
# much slower and heavier than `lein test` — expect minutes, not seconds.
#
# Usage:
#   ./scripts/coverage.sh                  # :default selector
#   ./scripts/coverage.sh :all             # any leading-colon arg overrides the selector
#   ./scripts/coverage.sh :fast
#   ./scripts/coverage.sh --fail-under 70  # exit non-zero if min(forms,lines) < 70%
#   ./scripts/coverage.sh -- -n 'vaelii\.lang.*'   # pass everything after -- straight to cloverage
#
# Env:
#   COVERAGE_PROFILE  Leiningen profile string (default "+test"; memory backend).
#                     For another backend, put +test LAST so its :test env (the
#                     ./kb/<backend>-test paths) wins the merge — a backend
#                     profile listed after +test overrides the path and the run
#                     would hit the REAL ./kb/<backend> dir:
#                       COVERAGE_PROFILE=+bench,+test ./scripts/coverage.sh
#   COVERAGE_EXCLUDE  Space-separated -e regexes for namespaces cloverage can't
#                     instrument (default: the two known un-instrumentable
#                     namespaces). Set empty to disable exclusions.
#   COVERAGE_TEST_SKIP  Space-separated test namespaces to leave unrun (default
#                     reload-test, which reloads the engine from disk
#                     uninstrumented). Skipping a test keeps every source namespace
#                     in the measurement — unlike COVERAGE_EXCLUDE, which changes
#                     what the percentage is over. Set empty to run the whole suite.
#
# Output:
#   target/coverage/index.html    HTML report (gitignored under /target/)
#   testbench/coverage/run.log    raw cloverage output (gitignored under /testbench/)

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# lein-cloverage version, injected into the ROOT :plugins below. Keep in sync
# with project.clj's `:dev {:plugins [[lein-cloverage …]]}`. The plugin declared
# in :dev does NOT register the `cloverage` task when invoked through
# `with-profile +test` on lein 2.9.8 (profile-level plugins aren't resolved as
# tasks there), so we add it to the root via `update-in` instead of relying on
# :dev being active.
CLOVERAGE_VERSION="${CLOVERAGE_VERSION:-1.2.4}"

PROFILE="${COVERAGE_PROFILE:-+test}"
SELECTOR=":default"
FAIL_UNDER=""
PASSTHROUGH=()

# Args: a leading-colon token sets the selector, --fail-under N sets the
# threshold, and everything after a literal `--` is forwarded to cloverage.
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; PASSTHROUGH+=("$@"); break ;;
    --fail-under) FAIL_UNDER="$2"; shift 2 ;;
    --fail-under=*) FAIL_UNDER="${1#*=}"; shift ;;
    :*) SELECTOR="$1"; shift ;;
    *) PASSTHROUGH+=("$1"); shift ;;
  esac
done

OUT_DIR="${OUT_DIR:-./testbench/coverage}"
mkdir -p "$OUT_DIR"
LOG="$OUT_DIR/run.log"

CLOVERAGE_ARGS=(--no-colorize --selector "$SELECTOR")
[[ -n "$FAIL_UNDER" ]] && CLOVERAGE_ARGS+=(--fail-threshold "$FAIL_UNDER")

# Namespaces cloverage cannot instrument: a top-level form whose eval (cloverage
# re-evals every form of a namespace one at a time to instrument it) compiles a single
# method past the JVM's 64 KB per-method bytecode limit, and the run dies on "Method code
# too large!".  Two do, both protocol declarations split into files of their own so the
# code that implements them stays instrumented: jtms-protocol (the 35-method `Tms`
# protocol, split out of vaelii.impl.jtms) and protocols (the 31-method `IndexStore`).
# Neither holds code to cover, so excluding them loses nothing, and cloverage's
# `--exclude-call clojure.core/defprotocol` does not rescue either — the form still
# compiles whole.
#
# vaelii.impl.kv and vaelii.impl.asp.clingo instrument cleanly on lein-cloverage 1.2.4
# and run the suite with no failure of their own, so they are measured: kv at ~98% of
# forms, clingo at ~13%, since only the JNA path it holds is uncovered wherever
# libclingo is absent.
#
# Keep this list discovered, not remembered: when a run dies on "Method code too
# large!", add the namespace it names and say so here; when a namespace here instruments,
# take it out.  Override the whole set with COVERAGE_EXCLUDE (space-separated regexes);
# set it empty to disable exclusions.
DEFAULT_EXCLUDE='^vaelii\.impl\.jtms-protocol$ ^vaelii\.impl\.protocols$'
for ns in ${COVERAGE_EXCLUDE-$DEFAULT_EXCLUDE}; do
  CLOVERAGE_ARGS+=(-e "$ns")
done

# Test namespaces to SKIP — a different thing from the exclusions above, and the
# distinction is the whole point. `-e` drops a namespace out of the *measurement*
# (its forms stop counting, so the percentage changes basis); this drops a *test*,
# which leaves every source namespace measured and only removes whatever coverage
# that one test contributed. Prefer this: the number stays comparable.
#
# One is skipped by default. `reload-test` reloads, from disk, every namespace an edit to `vaelii.impl.sentex`
# reaches — nearly the whole engine — plus `dense-jtms`, and leaves them reloaded for the
# rest of the JVM. Cloverage runs the test namespaces in name order in one JVM, so run,
# it leaves every test namespace after it (settle, special, taxonomy, the web tests)
# exercising uninstrumented code that counts for nothing — eight points of the forms
# total. Skipping it costs the coverage of `vaelii.browser.reload`'s reload path.
#
# `order-independence-test`, which replays each scenario under every permutation of its
# operation list, runs: about 75 s instrumented, against a few seconds without.
#
# Cloverage has `-t/--test-ns-regex` (which tests to run) but no test-exclude, so
# this is spelled as a negative lookahead over the alternation. Set
# COVERAGE_TEST_SKIP empty to run everything.
#
# The trailing `.*` is required: the regex is matched against the WHOLE
# namespace name, so a lookahead with nothing after it matches only the literal
# `vaelii.` prefix and therefore selects no test namespaces at all. That failure is
# silent and looks like success — the run finishes fast and reports a number (8.70%
# forms, from namespace loading alone). Whenever this regex changes, check the run
# logs a plausible count of `Testing ` lines before trusting the percentage.
COVERAGE_TEST_SKIP="${COVERAGE_TEST_SKIP-reload-test}"
if [[ -n "$COVERAGE_TEST_SKIP" ]]; then
  read -r -a skips <<< "$COVERAGE_TEST_SKIP"
  alternation=$(IFS='|'; echo "${skips[*]}")
  CLOVERAGE_ARGS+=(-t "^vaelii\\.(?!(?:${alternation})\$).*")
fi

# bash 3.2 (macOS) errors on "${arr[@]}" when arr is empty under `set -u`,
# so only splice the pass-through args when there are any.
[[ ${#PASSTHROUGH[@]} -gt 0 ]] && CLOVERAGE_ARGS+=("${PASSTHROUGH[@]}")

PLUGIN_INJECT=(update-in :plugins conj "[lein-cloverage \"$CLOVERAGE_VERSION\"]" --)

echo "lein ${PLUGIN_INJECT[*]} with-profile $PROFILE cloverage ${CLOVERAGE_ARGS[*]}  # $LOG"
echo "(instruments all of src/ + runs the suite — this takes a while)"
echo

# tee so the user sees live progress; PIPESTATUS keeps lein's real exit code.
# `update-in :plugins conj … --` adds lein-cloverage to the ROOT :plugins so the
# `cloverage` task resolves (see CLOVERAGE_VERSION note above).
lein "${PLUGIN_INJECT[@]}" with-profile "$PROFILE" cloverage "${CLOVERAGE_ARGS[@]}" 2>&1 | tee "$LOG"
exit_code=${PIPESTATUS[0]}

# The summary table's total row is labelled "ALL FILES"; the two %.2f cells
# after it are % Forms and % Lines.
ALL_ROW=$(grep -aE "ALL FILES" "$LOG" | tail -1)
read -r FORMS LINES <<< "$(echo "$ALL_ROW" | grep -oE "[0-9]+\.[0-9]+" | head -2 | tr '\n' ' ')"

echo
echo "=== coverage ($SELECTOR) ==="
if [[ -n "${FORMS:-}" && -n "${LINES:-}" ]]; then
  printf "  %-9s %s%%\n" "forms:" "$FORMS"
  printf "  %-9s %s%%\n" "lines:" "$LINES"
  echo "  HTML report: target/coverage/index.html"
else
  echo "  could not parse coverage summary — see $LOG"
  [[ $exit_code -eq 0 ]] && exit_code=1
fi

exit "$exit_code"
