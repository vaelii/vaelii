#!/usr/bin/env bash
# scripts/coverage.sh — run cloverage over vaelii core and report the
# total form/line coverage %.
#
# Runs `lein cloverage` (the task is added by injecting lein-cloverage into the root
# :plugins via `update-in` — see CLOVERAGE_VERSION below for why the :dev-profile
# declaration alone isn't enough) in several JVMs. Each instruments every namespace
# under src/ and runs part of the test suite against the instrumented code, and a last
# JVM merges their hits into one HTML report and one console summary table. This script:
#   - runs each under +test (so the :test env + cleanup injections apply, exactly
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
#   ./scripts/coverage.sh --jobs 2         # pass 2's test namespaces split across two JVMs
#   ./scripts/coverage.sh -- -n 'vaelii\.lang.*'   # pass everything after -- straight to cloverage
#
# Every instrumented JVM runs `vaelii.coverage/install!` from a lein injection before
# cloverage instruments, which replaces cloverage's probe with one that does nothing
# after a form's first hit. A covered form's hit count reads 1, and the report, which
# shows a form as covered or not, is the one cloverage's own probe writes. On index-test
# and naf-test, cloverage's probe ran at 5.0x the uninstrumented time and this one at
# 2.9x; over seven test namespaces run side by side, this one took 2726 s against 6451 s
# and wrote a byte-identical report (one box, 2026-11-09).
#
# The run has two passes. Pass 1 runs the COVERAGE_FIRST_PASS test namespaces in one
# JVM. Pass 2 runs every other test namespace in --jobs JVMs at once, each over the
# namespaces `scripts/ci-shard.sh <b> N --leg memory` assigns it, and `install!` leaves
# every form pass 1 hit without a probe there. A form pass 1 missed still calls the probe
# on every execution in pass 2. Every JVM still registers every form, so the
# form indices agree across the passes and the merge adds pass 1's hits back. Over
# naf-test, nat-test and closure-join-test run side by side on one box, with the default
# pass 1 below, pass 2 took 1.86x the uninstrumented time and a run probing every form
# 2.73x; a seven-namespace run in two passes wrote the report a single JVM under
# cloverage's own probe writes, byte for byte (2026-11-09).
#
# Each JVM instruments all of src/ (about 90 s on a CI runner) and writes its per-form hit
# counts through `vaelii.coverage/write-hits`; a last JVM sums them and writes the
# report, the summary table and the --fail-under verdict. The merge refuses JVMs that
# instrumented different forms. A namespace whose coverage depends on what an earlier
# namespace in the same JVM ran can measure differently under the split.
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
#                     uninstrumented, and the three ontology content tests).
#                     Skipping a test keeps every source namespace
#                     in the measurement — unlike COVERAGE_EXCLUDE, which changes
#                     what the percentage is over. Set empty to run the whole suite.
#   COVERAGE_FIRST_PASS  Space-separated test namespaces pass 1 runs (default below,
#                     where the choice is stated). Set empty to run pass 2 alone,
#                     every form with a probe.
#
# Output:
#   target/coverage/index.html    HTML report (gitignored under /target/)
#   testbench/coverage/run.log    the merge's output (gitignored under /testbench/)
#   testbench/coverage/run-first.log  pass 1's cloverage output, each line in the
#                                 console prefixed `[first] `
#   testbench/coverage/run-<b>.log  pass 2 JVM <b>'s cloverage output, prefixed `[b] `

{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
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
JOBS=1
PASSTHROUGH=()

# Args: a leading-colon token sets the selector, --fail-under N sets the
# threshold, --jobs N the JVM count, and everything after a literal `--` is
# forwarded to cloverage.
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; PASSTHROUGH+=("$@"); break ;;
    --fail-under) FAIL_UNDER="$2"; shift 2 ;;
    --fail-under=*) FAIL_UNDER="${1#*=}"; shift ;;
    --jobs) JOBS="$2"; shift 2 ;;
    --jobs=*) JOBS="${1#*=}"; shift ;;
    :*) SELECTOR="$1"; shift ;;
    *) PASSTHROUGH+=("$1"); shift ;;
  esac
done
[[ "$JOBS" =~ ^[1-9][0-9]*$ ]] || { echo "coverage: --jobs takes a positive integer, not $JOBS" >&2; exit 2; }

# The plugin reads CLOVERAGE_VERSION from the environment for the cloverage library
# it adds, and the --jobs merge adds the same library to its own JVM.
export CLOVERAGE_VERSION

OUT_DIR="${OUT_DIR:-./testbench/coverage}"
mkdir -p "$OUT_DIR"
LOG="$OUT_DIR/run.log"

CLOVERAGE_ARGS=(--no-colorize --selector "$SELECTOR")

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
# Four are skipped by default. `reload-test` reloads, from disk, every namespace an edit to `vaelii.impl.sentex`
# reaches — nearly the whole engine — plus `dense-jtms`, and leaves them reloaded for the
# rest of the JVM. Cloverage runs the test namespaces in name order in one JVM, so run,
# it leaves every test namespace after it (settle, special, taxonomy, the web tests)
# exercising uninstrumented code that counts for nothing — eight points of the forms
# total. Skipping it costs the coverage of `vaelii.browser.reload`'s reload path.
#
# `ontology-test`, `ontology-rules-test` and `ontology-folk-taxonomy-test` assert the
# shipped ontology's content, and every other leg runs them. Instrumented, the three
# take 44 minutes of the job whose limit deep.yml states.
#
# `order-independence-test`, which replays each scenario under every permutation of its
# operation list, runs: about 12 minutes instrumented.
COVERAGE_TEST_SKIP="${COVERAGE_TEST_SKIP-reload-test ontology-test ontology-rules-test ontology-folk-taxonomy-test}"

# Pass 1's test namespaces. The seven took 134 s together on a CI runner under
# cloverage's own probe (run 42549554706), and hit 229,773 of 500,372 forms on one box
# (2026-11-09). Pass 1 runs before pass 2 starts, so a namespace added here adds its own
# instrumented time to the run. It shortens pass 2 by the probe calls of the forms it
# hits that pass 2 runs repeatedly: a pass 2 namespace that the deep job log shows far
# over its uninstrumented time runs forms in loops that pass 1 never reached.
COVERAGE_FIRST_PASS="${COVERAGE_FIRST_PASS-index-test equational-test duration-test dot-test equality-test inherit-test context-scoping-test}"

# bash 3.2 (macOS) errors on "${arr[@]}" when arr is empty under `set -u`,
# so only splice the pass-through args when there are any.
[[ ${#PASSTHROUGH[@]} -gt 0 ]] && CLOVERAGE_ARGS+=("${PASSTHROUGH[@]}")

# `update-in :plugins conj … --` adds lein-cloverage to the ROOT :plugins so the
# `cloverage` task resolves (see CLOVERAGE_VERSION note above).
PLUGIN_INJECT=(update-in :plugins conj "[lein-cloverage \"$CLOVERAGE_VERSION\"]" --)
MERGE_DEP=(update-in :dependencies conj "[cloverage \"$CLOVERAGE_VERSION\"]" --)
SHARD_DIR=target/coverage-shards
rm -rf "$SHARD_DIR"
# One resolution before the JVMs start, so they do not fetch a cold ~/.m2 at once.
lein "${PLUGIN_INJECT[@]}" "${MERGE_DEP[@]}" with-profile "$PROFILE" deps || exit 1

# listed NS NAMES: whether test namespace NS is vaelii.<name> for a name in the
# space-separated NAMES.
listed() {
  local s
  for s in $2; do [[ "$1" == "vaelii.$s" ]] && return 0; done
  return 1
}

# instrumented B HITS NS…: one instrumented JVM over the test namespaces NS…, writing
# $SHARD_DIR/B/hits.tsv.gz and $OUT_DIR/run-B.log, with every form the hit file HITS
# hit left without a probe (none when HITS is empty). Its status is the SHARD-EXIT
# marker its own group echoes, never the pipeline's, which is awk's.
instrumented() {
  local b=$1 install="((requiring-resolve 'vaelii.coverage/install!)${2:+ \"$2\"})"
  shift 2
  {
    lein "${PLUGIN_INJECT[@]}" update-in :injections conj "$install" -- \
      with-profile "$PROFILE" cloverage "${CLOVERAGE_ARGS[@]}" \
      -t "^(?:$(IFS='|'; echo "${*//./\\.}"))\$" \
      -o "$SHARD_DIR/$b" --no-html --no-summary -c vaelii.coverage/write-hits
    echo "SHARD-EXIT:$?"
  } 2>&1 | tee "$OUT_DIR/run-$b.log" | awk -v p="[$b] " '{ print p $0; fflush() }'
}

started=(); hits=(); names=(); first_hits=""
for s in $COVERAGE_FIRST_PASS; do
  [[ -f "test/vaelii/$(echo "$s" | tr .- /_).clj" ]] ||
    { echo "coverage: COVERAGE_FIRST_PASS names vaelii.$s, which has no file under test/" >&2; exit 2; }
  listed "vaelii.$s" "$COVERAGE_TEST_SKIP" || names+=("vaelii.$s")
done
if [[ ${#names[@]} -gt 0 ]]; then
  echo "pass 1: ${#names[@]} test namespaces  # $OUT_DIR/run-first.log"
  instrumented first "" "${names[@]}"
  first_hits="$SHARD_DIR/first/hits.tsv.gz"
  [[ -f "$first_hits" ]] || { echo "coverage: pass 1 wrote no hits: $OUT_DIR/run-first.log"; exit 1; }
  started+=(first); hits+=("$first_hits")
fi

echo "(pass 2 instruments all of src/ in each of $JOBS JVMs + runs the rest of the suite split across them — this takes a while)"
pids=()
for ((b = 1; b <= JOBS; b++)); do
  # ci-shard.sh lists `*_test.clj` namespaces only, and refuses a deftest outside one.
  list=$(scripts/ci-shard.sh "$b" "$JOBS" --leg memory) || exit 1
  names=()
  for ns in $list; do
    listed "$ns" "$COVERAGE_TEST_SKIP $COVERAGE_FIRST_PASS" || names+=("$ns")
  done
  [[ ${#names[@]} -eq 0 ]] && continue
  started+=("$b"); hits+=("$SHARD_DIR/$b/hits.tsv.gz")
  echo "JVM $b: ${#names[@]} test namespaces  # $OUT_DIR/run-$b.log"
  instrumented "$b" "$first_hits" "${names[@]}" &
  pids+=("$!")
done
for p in ${pids[@]+"${pids[@]}"}; do wait "$p"; done

exit_code=0
for b in ${started[@]+"${started[@]}"}; do
  grep -q '^SHARD-EXIT:0$' "$OUT_DIR/run-$b.log" || { echo "JVM $b did not exit 0: $OUT_DIR/run-$b.log"; exit_code=1; }
done

if [[ ${#hits[@]} -eq 0 ]]; then
  echo "coverage: every test namespace is skipped"
  exit_code=1
else
  merge_args=(--output target/coverage)
  [[ -n "$FAIL_UNDER" ]] && merge_args+=(--fail-under "$FAIL_UNDER")
  echo "lein ${MERGE_DEP[*]} run -m vaelii.coverage ${merge_args[*]} ${hits[*]}  # $LOG"
  lein "${MERGE_DEP[@]}" run -m vaelii.coverage "${merge_args[@]}" "${hits[@]}" 2>&1 | tee "$LOG"
  merge_exit=${PIPESTATUS[0]}
  [[ $merge_exit -ne 0 ]] && exit_code=$merge_exit
fi

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
}
