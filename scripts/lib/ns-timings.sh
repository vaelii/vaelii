#!/usr/bin/env bash
# scripts/lib/ns-timings.sh — how long each namespace of a `lein test` run took.
#
# Sourced, never executed:
#   . scripts/lib/ns-timings.sh
#   lein test … 2>&1 | ns_timings FILE | tee LOG
#
# `ns_timings` copies stdin to stdout unchanged and writes `namespace<TAB>seconds`
# rows to FILE.  A namespace's cost is the gap from its own `lein test <ns>` line
# to the next one, and clojure.test's `Ran N tests` total closes the last
# namespace.  Each row is written when the line after the namespace arrives, so
# a run killed partway keeps the rows of the namespaces it finished.
#
# scripts/test-parallel.sh packs its local shards from these rows, and
# .github/workflows/test.yml packs its CI shards from them (scripts/ci-weights.sh
# turns a run's rows into the weights the next run reads).

# The clock is in microseconds: bash 5's EPOCHREALTIME, else perl's Time::HiRes for
# bash 3.2 (macOS's /bin/bash), else whole SECONDS.  Most namespaces take under a
# second, and at whole seconds they all read 0 and pack into one shard.
ns_timings() {
  local out="$1" line prev="" pt=0 t d
  : > "$out"
  while IFS= read -r line; do
    printf '%s\n' "$line"
    case "$line" in
      "lein test "*|"Ran "*" tests containing "*)
        if [[ -n "${EPOCHREALTIME:-}" ]]; then t=${EPOCHREALTIME/[.,]/}
        else t=$(perl -MTime::HiRes=time -e 'printf "%d", time * 1e6' 2>/dev/null) || t=$((SECONDS * 1000000))
        fi
        if [[ -n "$prev" ]]; then
          d=$(((t - pt) / 10000))
          printf '%s\t%d.%02d\n' "$prev" "$((d / 100))" "$((d % 100))" >> "$out"
        fi
        prev=""; pt=$t
        [[ "$line" == "lein test "* ]] && prev="${line#lein test }" ;;
    esac
  done
}

# `ns_timings_rerun FILE NAMESPACE…` runs the NAMESPACEs again three times over in
# one `lein test` call, interleaved (a b a b a b), its output on stdout.  On a green
# rerun it writes each namespace's median rerun time into FILE's row for it.  A red
# rerun keeps every first time and prints a GitHub `::warning::` line, so the rerun
# decides no verdict.  .github/workflows/test.yml reruns the namespaces
# scripts/ci-weights.sh's --list form names: one CI shard ran vaelii.quote-test in
# 92 s against the 27 s its runner's speed predicted, on a tree where it took 105 s
# locally against 114 s on the tree before.
#
# A namespace that runs first in a JVM also pays the JVM's and the KB's start-up.
# Under the recurring-failures-first order that is no longer the lightest
# namespace: vaelii.query-context-test read 73 s against 7 s expected when it ran
# first.  A single rerun is a fresh JVM, so it pays the start-up again.  Of three
# interleaved runs only the first pays it, and the median is a warm time.  A
# namespace with fewer than three rerun rows takes the median of the rows it has.
ns_timings_rerun() {
  local out="$1" rerun i
  local -a runs=()
  shift
  [[ $# -gt 0 ]] || return 0
  rerun=$(mktemp) || return 1
  for i in 1 2 3; do runs+=("$@"); done
  if (set -o pipefail; lein test "${runs[@]}" 2>&1 | ns_timings "$rerun"); then
    awk -F'\t' -v OFS='\t' '
      NR == FNR { if ($1 != "") { n[$1]++; v[$1, n[$1]] = $2 + 0 }; next }
      ($1 in n) {
        k = n[$1]
        for (i = 1; i <= k; i++) s[i] = v[$1, i]
        for (i = 2; i <= k; i++) for (j = i; j > 1 && s[j - 1] > s[j]; j--) {
          t = s[j]; s[j] = s[j - 1]; s[j - 1] = t
        }
        $2 = sprintf("%.2f", s[int((k + 1) / 2)])
      }
      { print }' "$rerun" "$out" > "$out.new" && mv "$out.new" "$out"
    awk -F'\t' '$1 != "" { n[$1]++ } END { for (k in n) if (n[k] < 3)
      printf "::warning::%s ran %d time(s) when run again, not 3\n", k, n[k] }' "$rerun"
  else
    echo "::warning::a namespace failed when run again for its time; every first time stands"
  fi
  rm -f "$rerun"
}

# `ns_timings_average PREV NEW` writes `namespace<TAB>seconds` rows to stdout: each
# NEW figure moved NS_TIMINGS_WEIGHT of the way from PREV's figure for the same
# namespace, an exponential moving average.  A namespace in one file only keeps that
# file's figure.  PREV may be missing, and `#` lines in either file are skipped.
#
# One run's figure is a noisy reading of a namespace's cost: disjointness-audit-test
# took 143 s, 159 s and 270 s on three CI runs of the same tree, and a local run on
# one shard reads every namespace slower than one on five.  At a weight of 0.3 the
# average's variance from that noise is 0.3/1.7 = 18% of one reading's, and a
# namespace whose real cost changes is 76% of the way to the new figure after four
# runs.
NS_TIMINGS_WEIGHT=0.3
ns_timings_average() {
  local prev="$1" new="$2"
  [[ -f "$prev" ]] || prev=/dev/null
  awk -F'\t' -v a="$NS_TIMINGS_WEIGHT" '
    $1 == "" || $1 ~ /^#/ { next }
    FILENAME == ARGV[1] { old[$1] = $2 + 0; next }
    { cur[$1] = $2 + 0 }
    END {
      for (k in old) if (!(k in cur)) printf "%s\t%.2f\n", k, old[k]
      for (k in cur) printf "%s\t%.2f\n", k, (k in old) ? a * cur[k] + (1 - a) * old[k] : cur[k]
    }' "$prev" "$new" | LC_ALL=C sort
}
