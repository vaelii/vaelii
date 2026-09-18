#!/usr/bin/env bash
# The suite across N JVMs instead of one.
#
# The test stage is the gate's long pole — 395s of a ~490s `:default` run — and it is
# one JVM walking 187 namespaces in sequence.  Splitting it is safe for one reason:
# **the in-memory registry is per-JVM**, so two runs over the same space number do not
# collide (docs/storage.md).  Each shard is its own `lein test`, its own KB registry,
# its own `:once` fixtures and its own net-neutrality baseline; nothing crosses.
#
# What this does NOT do, and must not:
#
#   - **Split a namespace.**  A shard is a whole number of namespaces, because a
#     `:once` fixture is what several tests in one file share.
#   - **Run the durable backends.**  Two disk suites over one directory collide on the
#     single-writer lock, and `VAELII_TEST_SPACE` admits only six non-overlapping
#     blocks — so this refuses a `VAELII_TEST_BACKEND` with a durable half rather than
#     sharding into corruption.  `scripts/test-backends.sh` is sequential on purpose
#     and stays that way.
#   - **Hide a failure.**  Every shard's exit status is read from a marker the shard
#     itself echoes, never from a pipeline (`lein test | tee` reports `tee`).  The
#     aggregate is red if any shard is.
#
# Balance comes from measured time, not guesswork: each run records how long every
# namespace took to `target/gate/test-timings.tsv`, and the next run bin-packs
# longest-first into the emptiest shard.  With no timings yet it falls back to
# round-robin, which is a worse split and still correct.
#
# Usage:
#   scripts/test-parallel.sh                 # :default, jobs from scripts/lib/slots.sh
#   scripts/test-parallel.sh :all            # the ^:slow tests too
#   scripts/test-parallel.sh --jobs 4        # a fixed shard count
#   scripts/test-parallel.sh :all --jobs 6
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1

# what the shards are a verdict about — the header line, and the first line of every
# shard log
# shellcheck source=scripts/lib/revision.sh
. scripts/lib/revision.sh
# one row in `logs/runs.tsv` per run: the revision, the clock, the totals and the
# verdict, so "which revision did the suite last pass at" is one file to read
# rather than a dozen `target/gate/run-*` directories a `lein clean` can delete
# shellcheck source=scripts/lib/runlog.sh
. scripts/lib/runlog.sh
# the default shard count, shared with test-matrix.sh so the rule cannot drift
# shellcheck source=scripts/lib/slots.sh
. scripts/lib/slots.sh

# Logs and scratch are **per run**; the timings are **per checkout**, and the split is
# the point.  `gate.sh` hands this a fresh `target/gate/run-<pid>` so two gates in one
# working tree cannot read each other's shard logs — but the timings are feedback for
# the *next* run rather than output of this one, so they live above the run directory
# and every run in this checkout shares the one file.  Put them inside `$OUT` and each
# run starts blind, silently falling back to round-robin sharding: a slower gate whose
# only symptom is being slower.
OUT="${VAELII_GATE_OUT:-target/gate}"
TIMINGS="${VAELII_GATE_TIMINGS:-target/gate/test-timings.tsv}"

selector=":default"
jobs=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    :*)       selector="$1"; shift ;;
    --jobs)   [[ $# -ge 2 ]] || { echo "test-parallel: --jobs needs a value" >&2; exit 2; }
              jobs="$2"; shift 2 ;;
    --jobs=*) jobs="${1#--jobs=}"; shift ;;
    *) echo "test-parallel: unknown argument $1" >&2; exit 2 ;;
  esac
done

# A durable half means one lock and six usable space blocks — not shardable.
case "${VAELII_TEST_BACKEND:-memory}" in
  *disk*)
    echo "test-parallel: VAELII_TEST_BACKEND=${VAELII_TEST_BACKEND} has a durable half." >&2
    echo "  Two disk suites over one directory collide on the single-writer lock." >&2
    echo "  Use scripts/test-backends.sh, which is sequential for this reason." >&2
    exit 2 ;;
esac

[[ -z "$jobs" ]] && jobs=$(default_slots)   # P-2 minus running vaelii JVMs; see scripts/lib/slots.sh

mkdir -p "$OUT" || exit 1
# The revision the shards are about, read BEFORE the first JVM boots: a sharded
# suite is minutes long on a checkout several agents write to, and a verdict
# credited to whatever landed while it ran is a verdict about no tree at all.
runlog_start
# the timings sit above `$OUT` when the gate hands us a per-run directory, so their own
# parent may not exist yet on a fresh checkout
mkdir -p "$(dirname "$TIMINGS")" || exit 1

# ---- the namespaces ---------------------------------------------------------
# `_test.clj` only: `world.clj`, `test_util.clj` and friends are support code that
# declares no tests, and naming one would only cost a load.
namespaces=()
while IFS= read -r f; do
  ns="${f#test/}"; ns="${ns%.clj}"; ns="${ns//\//.}"; ns="${ns//_/-}"
  namespaces+=("$ns")
done < <(find test -name '*_test.clj' | sort)

n=${#namespaces[@]}
if [[ $n -eq 0 ]]; then echo "test-parallel: no test namespaces found" >&2; exit 2; fi
[[ $jobs -gt $n ]] && jobs=$n

# ---- bin-pack ---------------------------------------------------------------
# Longest-processing-time-first: sort by last run's duration descending, and hand each
# namespace to whichever shard is currently lightest.  This is the standard 4/3-optimal
# greedy, and on this suite it matters — the spread between the heaviest namespace and
# the median is large enough that round-robin leaves one shard running alone at the end.
assign_out="$OUT/.shard-assign"
awk -v jobs="$jobs" -v timings="$TIMINGS" '
  BEGIN {
    while ((getline line < timings) > 0) {
      split(line, f, "\t"); if (f[1] != "") secs[f[1]] = f[2] + 0
    }
    close(timings)
  }
  { ns[NR] = $0; w[NR] = (ns[NR] in secs) ? secs[ns[NR]] : -1 }
  END {
    # unknown namespaces get the mean, so a new test is not always packed last
    total = 0; known = 0
    for (i = 1; i <= NR; i++) if (w[i] >= 0) { total += w[i]; known++ }
    mean = (known > 0) ? total / known : 1
    for (i = 1; i <= NR; i++) if (w[i] < 0) w[i] = mean

    # selection sort by weight desc (NR is small; keeping this dependency-free)
    for (i = 1; i <= NR; i++) order[i] = i
    for (i = 1; i <= NR; i++)
      for (j = i + 1; j <= NR; j++)
        if (w[order[j]] > w[order[i]]) { t = order[i]; order[i] = order[j]; order[j] = t }

    for (b = 1; b <= jobs; b++) load[b] = 0
    for (k = 1; k <= NR; k++) {
      idx = order[k]; light = 1
      for (b = 2; b <= jobs; b++) if (load[b] < load[light]) light = b
      load[light] += w[idx]
      printf "%d\t%s\n", light, ns[idx]
    }
  }
' <(printf '%s\n' "${namespaces[@]}") > "$assign_out"

echo "running $n namespaces at $selector across $jobs shard(s) — $(revision_line) — logs in $OUT"
# The same facts into the run directory, for a reader watching this run go.  The
# shard logs carry the revision stamp but not the selector or the shard count,
# and a bare `lein test-parallel` writes no other file here — `gate.sh` captures
# this stdout into `test.log`, and a run outside the gate captures nothing.  So
# a watcher had nothing to read the plan off (tools/vaelii-top/src/vtop/live.py).
printf 'selector\t%s\nshards\t%d\nnamespaces\t%d\n' \
  "$selector" "$jobs" "$n" > "$OUT/test.plan" 2>/dev/null || true

# ---- run --------------------------------------------------------------------
t0=$SECONDS
pids=(); shard_logs=()
for ((b = 1; b <= jobs; b++)); do
  shard_ns=()
  while IFS= read -r ns; do shard_ns+=("$ns"); done < <(awk -F'\t' -v b="$b" '$1==b {print $2}' "$assign_out")
  [[ ${#shard_ns[@]} -eq 0 ]] && continue

  log="$OUT/test.shard-$b.log"; timing="$OUT/.timing-$b.tsv"
  shard_logs+=("$log")
  # The status comes from the marker the shard echoes, never from the pipeline: `tee`
  # exits 0 over a red suite, which is exactly how a green gate hides one.
  # Namespaces first, THEN the selector: `split-selectors` splits leiningen's argv on
  # the first keyword and hands everything after a selector to that selector as its
  # own arguments — so `lein test :default <ns>` calls the `:default` predicate with
  # the namespace as a second argument and dies on arity, rather than filtering by it.
  revision_stamp "shard $b" > "$log"
  (
    { lein test "${shard_ns[@]}" "$selector"; echo "SHARD-EXIT:$?"; } 2>&1 \
      | tee -a "$log" \
      | while IFS= read -r line; do
          case "$line" in
            "lein test "*) printf '%s\t%s\n' "$SECONDS" "${line#lein test }" ;;
          esac
        done > "$timing"
  ) &
  pids+=("$!")
done

for p in "${pids[@]}"; do wait "$p"; done
elapsed=$((SECONDS - t0))

# ---- timings for the next run ----------------------------------------------
# Each `lein test <ns>` line is a start stamp; a namespace's cost is the gap to the
# next one.  The last namespace in a shard has no successor, so it keeps its previous
# figure rather than a guess.
{
  [[ -f "$TIMINGS" ]] && cat "$TIMINGS"
  for ((b = 1; b <= jobs; b++)); do
    [[ -f "$OUT/.timing-$b.tsv" ]] || continue
    awk -F'\t' 'NR>1 { printf "%s\t%d\n", prev_ns, $1 - prev_t } { prev_t=$1; prev_ns=$2 }' "$OUT/.timing-$b.tsv"
  done
} | awk -F'\t' '$1 != "" { secs[$1] = $2 } END { for (k in secs) printf "%s\t%s\n", k, secs[k] }' \
  | sort > "$TIMINGS.$$.new" && mv "$TIMINGS.$$.new" "$TIMINGS"
rm -f "$OUT"/.timing-*.tsv "$assign_out"

# ---- aggregate --------------------------------------------------------------
# Summed, not eyeballed: the whole point of sharding is that no single log carries the
# suite's totals any more, and a missing shard has to read as a failure.
tests=0; assertions=0; failures=0; errors=0; bad=0; missing=()
for log in "${shard_logs[@]}"; do
  if ! grep -q '^SHARD-EXIT:' "$log"; then missing+=("$log"); bad=1; continue; fi
  grep -q '^SHARD-EXIT:0$' "$log" || bad=1
  while IFS= read -r line; do
    t=$(echo "$line" | sed -n 's/^Ran \([0-9]*\) tests containing \([0-9]*\) assertions.*/\1 \2/p')
    [[ -n "$t" ]] && { tests=$((tests + ${t% *})); assertions=$((assertions + ${t#* })); }
  done < <(grep '^Ran .* tests containing' "$log")
  while IFS= read -r line; do
    f=$(echo "$line" | sed -n 's/^\([0-9]*\) failures, \([0-9]*\) errors.*/\1 \2/p')
    [[ -n "$f" ]] && { failures=$((failures + ${f% *})); errors=$((errors + ${f#* })); }
  done < <(grep '^[0-9]* failures, [0-9]* errors' "$log")
done

echo
printf 'Ran %d tests containing %d assertions.\n' "$tests" "$assertions"
printf '%d failures, %d errors.\n' "$failures" "$errors"
printf 'across %d shard(s) in %ds\n' "${#shard_logs[@]}" "$elapsed"

if [[ ${#missing[@]} -gt 0 ]]; then
  printf 'shard(s) produced no exit marker (killed?): %s\n' "${missing[*]}" >&2
fi

# The ledger row.  The selector is the `variant` column and not part of the kind,
# because a `:default` suite and an `:all` suite are different verdicts: the row
# for one must not read as the last run of the other.  A shard with no exit
# marker was killed, so that run is `interrupted` rather than failed — it reached
# no verdict, and a ledger that called it a failure would send somebody looking
# for a test that never ran.
suite_summary=$(printf '%d tests, %d assertions, %d failures, %d errors, %d shard(s)' \
                  "$tests" "$assertions" "$failures" "$errors" "${#shard_logs[@]}")
if [[ ${#missing[@]} -gt 0 ]]; then
  runlog_record test "$selector" interrupted "$suite_summary" "$OUT"
elif [[ $bad -ne 0 || $failures -ne 0 || $errors -ne 0 ]]; then
  runlog_record test "$selector" failed "$suite_summary" "$OUT"
else
  runlog_record test "$selector" passed "$suite_summary" "$OUT"
fi

if [[ $bad -ne 0 || $failures -ne 0 || $errors -ne 0 ]]; then
  echo
  echo "failing tests:"
  grep -h -A3 '^\(FAIL\|ERROR\) in' "${shard_logs[@]}" 2>/dev/null | head -n 120
  exit 1
fi
exit 0
