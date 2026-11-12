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

# `ns_timings_rerun FILE NAMESPACE…` runs each NAMESPACE again with `lein test`, its
# output on stdout, and on a green rerun writes the smaller of the two times into
# FILE's row for it.  A red rerun keeps the first time and prints a GitHub
# `::warning::` line, so the rerun decides no verdict.  .github/workflows/test.yml
# reruns the namespaces scripts/ci-weights.sh's --list form names: one CI shard ran
# vaelii.quote-test in 92 s against the 27 s its runner's speed predicted, on a tree
# where it took 105 s locally against 114 s on the tree before.  `lein test` runs a
# namespace named twice in one call only once, so each rerun is its own call.
ns_timings_rerun() {
  local out="$1" ns rerun
  shift
  rerun=$(mktemp) || return 1
  for ns in "$@"; do
    if (set -o pipefail; lein test "$ns" 2>&1 | ns_timings "$rerun"); then
      awk -F'\t' -v OFS='\t' 'NR == FNR { if ($1 != "") r[$1] = $2 + 0; next }
        ($1 in r) && r[$1] < $2 + 0 { $2 = sprintf("%.2f", r[$1]) } { print }' \
        "$rerun" "$out" > "$out.new" && mv "$out.new" "$out"
    else
      echo "::warning::$ns failed when run again for its time; its first time stands"
    fi
  done
  rm -f "$rerun"
}

# `ns_timings_rerun_fits BASELINE SHARD SLOW…` succeeds when rerunning the SLOW
# namespaces is predicted to take no longer than the whole SHARD (a space-separated
# list of its namespaces).  Both predictions are sums of BASELINE's
# `namespace<TAB>seconds` rows, and a namespace BASELINE does not name counts at the
# mean of the rows it does.  When the rerun would cost more than the shard, it prints
# a `::warning::` line and fails, and the shard skips the rerun.  The first times then
# stand and the `weights` job fails on them.  A run where most namespaces regress
# therefore fails in about one shard's time, instead of running most of the shard again.
ns_timings_rerun_fits() {
  local base="$1" shard="$2"
  shift 2
  [[ $# -gt 0 ]] || return 0
  [[ -f "$base" ]] || return 0
  awk -F'\t' -v shard="$shard" -v slow="$*" '
    $1 == "" || $1 ~ /^#/ { next }
    { w[$1] = $2 + 0; tot += $2 + 0; n++ }
    END {
      mean = n ? tot / n : 0
      k = split(shard, s, " "); for (i = 1; i <= k; i++) sh += (s[i] in w) ? w[s[i]] : mean
      k = split(slow, r, " "); for (i = 1; i <= k; i++) re += (r[i] in w) ? w[r[i]] : mean
      if (re > sh) {
        printf "::warning::the rerun (%.0f s) would take longer than the shard (%.0f s), so it is skipped\n", re, sh
        exit 1
      }
    }' "$base"
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
