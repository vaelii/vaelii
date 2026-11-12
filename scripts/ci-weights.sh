#!/usr/bin/env bash
# scripts/ci-weights.sh — rewrite the CI shard weights from measured namespace times.
#
#   scripts/ci-weights.sh <run-id> [--repo owner/name]      # both legs, from a run's logs
#   scripts/ci-weights.sh --from DIR --leg disk|memory --out FILE [--prev FILE]
#                                                           # one leg, from timing rows
#   scripts/ci-weights.sh --from DIR --leg disk|memory --check BASELINE
#                                                           # one leg, judged against BASELINE
#   scripts/ci-weights.sh --from DIR --leg disk|memory --list BASELINE
#                                                           # the namespaces --check would name
#
# scripts/ci-shard.sh packs the shards of .github/workflows/test.yml by measured
# namespace time, one weights file per leg: scripts/ci-test-weights-disk.tsv and
# scripts/ci-test-weights-memory.tsv.  The two legs differ per namespace (the
# durable record store costs some namespaces far more than others), so each leg
# is packed from its own column.
#
# THE RUN-ID FORM rewrites both committed files from a finished run's job logs.
# The runner prefixes every line with a timestamp, so the gap between one `lein test <namespace>`
# line and the next is what that namespace cost on CI's hardware.
#
# THE --from FORM is what the workflow runs after every green leg: DIR holds one
# `<shard>-of-<total>.tsv` per shard, the `namespace<TAB>seconds` rows its
# scripts/lib/ns-timings.sh wrote, and FILE goes into the Actions cache, where the
# next run's shards read it in place of the committed file.  A DIR missing a shard
# is refused: that shard's namespaces would be written at 0.00.  The committed
# files are the fallback for a run that finds no cache entry.  With --prev, the
# weights the run packed from, each measured figure goes into PREV's as a moving
# average (scripts/lib/ns-timings.sh, `ns_timings_average`), so one slow runner
# moves a weight by 0.3 of its excess.
#
# A NAMESPACE THE RUN DID NOT ENTER IS WRITTEN AT 0.00 rather than left out, so a
# namespace whose every test is `^:slow` is weighted at what it costs the
# `:default` selector instead of at the mean.  A namespace added to the tree since
# the run gets no line at all, and scripts/ci-shard.sh gives it the mean.
#
# THE --check FORM judges a leg's timings against BASELINE, the weights develop's
# newest push wrote, and prints a Markdown report.  A runner VM runs every namespace it holds
# at one speed, which ranged 0.6x to 1.4x of the median over the green runs in
# 42343717621..42631334242.  A shard's speed is therefore the median, over its
# namespaces weighted SPEED_FLOOR s or more, of measured / baseline, and the leg's
# speed is the median of its shards' speeds.  The check exits 1 on a namespace
# finding and 3 on a leg finding alone:
#   - a namespace weighted NS_FLOOR s or more took NS_SLOWER times its shard's speed
#     and NS_EXCESS s more than that speed predicts, so that namespace slowed;
#   - the leg's speed is LEG_SLOWER or more, so every namespace slowed together.
# Over 16 of those runs the leg's speed ranged 0.69 to 1.06 and no namespace
# crossed both namespace limits.  Over the 8 runs of two branches whose suite cost
# 2x to 3x develop's, every run on each leg crossed at least one limit.  A
# namespace BASELINE does not name is not judged.
#
# THE --list FORM prints the namespaces the --check form's namespace finding names,
# one per line, over whichever shard files DIR holds: a namespace is judged at its
# own shard's speed, so one shard's file is enough.  A shard of
# .github/workflows/test.yml runs those namespaces again (scripts/lib/ns-timings.sh,
# `ns_timings_rerun`) before it uploads its timings.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

REPO="vaelii/vaelii"
RUN=""; FROM=""; LEG=""; OUT=""; PREV=""; CHECK=""; LIST=""
SPEED_FLOOR=2 LEG_SLOWER=1.25 NS_FLOOR=5 NS_SLOWER=2 NS_EXCESS=60

usage() {
  sed -n '4,10p' "$0" | sed 's/^# \{0,1\}//' >&2
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --repo) REPO="${2:?--repo needs owner/name}"; shift 2 ;;
    --from) FROM="${2:?--from needs a directory}"; shift 2 ;;
    --leg)  LEG="${2:?--leg needs disk or memory}"; shift 2 ;;
    --out)  OUT="${2:?--out needs a file}"; shift 2 ;;
    --prev) PREV="${2:?--prev needs a file}"; shift 2 ;;
    --check) CHECK="${2:?--check needs a file}"; shift 2 ;;
    --list) LIST="${2:?--list needs a file}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "ci-weights: unknown option $1" >&2; usage; exit 2 ;;
    *)  RUN="$1"; shift ;;
  esac
done

tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT

find test -name '*_test.clj' \
  | sed -e 's|^test/||' -e 's|\.clj$||' -e 's|/|.|g' -e 's|_|-|g' \
  | sort > "$tmp/tree.txt"

# write_weights <leg> <timings.tsv> <out> <source line>: the header, then one row per
# tree namespace, 0.00 for one the timings lack.
write_weights() {
  local leg="$1" timings="$2" out="$3" source="$4" total count
  total=$(awk -F'\t' '{ s += $2 } END { printf "%.0f", s }' "$timings")
  count=$(wc -l < "$tmp/tree.txt" | tr -d ' ')
  {
    cat <<HDR
# scripts/ci-test-weights-$leg.tsv — how long each test namespace takes on a CI
# runner, VAELII_TEST_BACKEND=$( [[ $leg == disk ]] && echo disk-log || echo memory ).
#
# \`namespace<TAB>seconds\`.  scripts/ci-shard.sh --leg $leg bin-packs the namespaces
# by these numbers so that the shards of that .github/workflows/test.yml leg finish
# together.  The workflow reads this file only when the Actions cache holds no
# timings from an earlier green run of the leg.  A namespace absent here still runs,
# weighted at the mean; one at 0.00 has every test \`^:slow\` or \`^:multi-jvm\`.
#
# Regenerate with scripts/ci-weights.sh <run-id>.
#
# Source: $source, $count namespaces, ${total}s of namespace time.
HDR
    awk -F'\t' '
      NR == FNR { w[$1] = $2; next }
      { printf "%s\t%.2f\n", $1, ($1 in w) ? w[$1] : 0 }' "$timings" "$tmp/tree.txt"
  } > "$out.new" && mv "$out.new" "$out"
  echo "ci-weights: $out — $count namespaces, ${total}s, from $source" >&2
}

# check_leg <leg> <dir> <baseline> [list]: the --check form's report on stdout, its
# exit 1 on a namespace finding and 3 on a leg finding alone; with `list`, the
# namespace finding's names and exit 0.  A shard file's rows are in run order.  The
# namespace finding skips each shard's first row, because the first namespace in a
# JVM also pays the JVM's and the KB's start-up, about 70 s on CI.  On CI,
# vaelii.query-context-test read 76 s against 6 s expected when it ran first, and
# 75 s when rerun alone.  The insertion sort keeps to POSIX awk, which
# has no asort.
check_leg() {
  awk -F'\t' -v leg="$1" -v baseline="$3" -v list="${4:-}" -v speed_floor="$SPEED_FLOOR" \
      -v leg_slower="$LEG_SLOWER" -v ns_floor="$NS_FLOOR" -v ns_slower="$NS_SLOWER" \
      -v ns_excess="$NS_EXCESS" '
    function median(a, n,    i, j, x) {
      for (i = 2; i <= n; i++) {
        x = a[i]
        for (j = i - 1; j >= 1 && a[j] > x; j--) a[j + 1] = a[j]
        a[j + 1] = x
      }
      return (n % 2) ? a[(n + 1) / 2] : (a[n / 2] + a[n / 2 + 1]) / 2
    }
    FILENAME == baseline { if ($1 != "" && $1 !~ /^#/) w[$1] = $2 + 0; next }
    $1 == "" { next }
    { s = FILENAME; sub(/^.*\//, "", s); sub(/-of-.*$/, "", s)
      if (!(s in rows)) shard[++shards] = s
      n = ++rows[s]; ns[s, n] = $1; t[s, n] = $2 + 0 }
    END {
      for (i = 1; i <= shards; i++) {
        s = shard[i]; k = 0
        for (j = 1; j <= rows[s]; j++)
          if ((ns[s, j] in w) && w[ns[s, j]] >= speed_floor) r[++k] = t[s, j] / w[ns[s, j]]
        speed[s] = k ? median(r, k) : 1
        all[i] = speed[s]
      }
      legspeed = median(all, shards)
      if (!list) {
        printf "### %s leg against %s\n\n", leg, baseline
        printf "Leg speed %.2f; the check fails at %.2f.\n\n", legspeed, leg_slower
      }
      for (i = 1; i <= shards; i++) {
        s = shard[i]
        for (j = 2; j <= rows[s]; j++) {
          if (!(ns[s, j] in w) || w[ns[s, j]] < ns_floor) continue
          expect = w[ns[s, j]] * speed[s]
          if (t[s, j] >= ns_slower * expect && t[s, j] - expect >= ns_excess) {
            if (list) { print ns[s, j]; continue }
            if (!found++)
              print "| namespace | shard | shard speed | baseline s | expected s | measured s | ratio |\n|---|---|---|---|---|---|---|"
            printf "| %s | %s | %.2f | %.0f | %.0f | %.0f | %.1fx |\n",
                   ns[s, j], s, speed[s], w[ns[s, j]], expect, t[s, j], t[s, j] / expect
          }
        }
      }
      if (list) exit 0
      if (found) printf "\n%d namespace(s) took %sx or more of the expected time, and %d s or more beyond it.\n",
                        found, ns_slower, ns_excess
      slow = legspeed >= leg_slower
      printf "\nci-weights: %s check %s\n", leg, found ? "FAILED" : slow ? "found the leg slow" : "passed"
      exit (found ? 1 : (slow ? 3 : 0))
    }' "$3" "$2"/*-of-*.tsv
}

if [[ -n "$FROM" ]]; then
  [[ -n "$LEG" && -z "$RUN" ]] || { usage; exit 2; }
  [[ ( -n "$OUT" && -z "$CHECK$LIST" ) || ( -z "$OUT$PREV" && -n "$CHECK" && -z "$LIST" ) \
     || ( -z "$OUT$PREV$CHECK" && -n "$LIST" ) ]] || { usage; exit 2; }
  case "$LEG" in disk|memory) ;; *) echo "ci-weights: --leg is disk or memory, not $LEG" >&2; exit 2 ;; esac
  if [[ -n "$LIST" ]]; then
    [[ -f "$LIST" ]] || { echo "ci-weights: --list $LIST is not a file" >&2; exit 1; }
    compgen -G "$FROM/*-of-*.tsv" > /dev/null || { echo "ci-weights: no <shard>-of-<total>.tsv under $FROM" >&2; exit 1; }
    check_leg "$LEG" "$FROM" "$LIST" list
    exit
  fi
  files=$(cd "$FROM" 2>/dev/null && ls -- *-of-*.tsv 2>/dev/null)
  of=$(sed -n 's/^[0-9]*-of-\([0-9]*\)\.tsv$/\1/p' <<< "$files" | sort -u)
  complete=0
  if [[ "$of" =~ ^[0-9]+$ && "$(wc -l <<< "$files" | tr -d ' ')" -eq "$of" ]]; then
    complete=1
    for ((i = 1; i <= of; i++)); do [[ -f "$FROM/$i-of-$of.tsv" ]] || complete=0; done
  fi
  if [[ $complete -ne 1 ]]; then
    echo "ci-weights: $FROM does not hold one <shard>-of-<total>.tsv per shard: $(tr "\n" " " <<< "$files")" >&2
    exit 1
  fi
  if [[ -n "$CHECK" ]]; then
    [[ -f "$CHECK" ]] || { echo "ci-weights: --check $CHECK is not a file" >&2; exit 1; }
    check_leg "$LEG" "$FROM" "$CHECK"
    exit
  fi
  mkdir -p "$(dirname "$OUT")" || exit 1
  # A namespace appears in one shard's rows only; the last row wins if one repeats.
  find "$FROM" -name '*-of-*.tsv' -exec cat {} + \
    | awk -F'\t' '$1 != "" { s[$1] = $2 } END { for (k in s) printf "%s\t%s\n", k, s[k] }' \
    | sort > "$tmp/$LEG.tsv"
  [[ -s "$tmp/$LEG.tsv" ]] || { echo "ci-weights: no timing rows under $FROM" >&2; exit 1; }
  source="${GITHUB_REPOSITORY:-$REPO} run ${GITHUB_RUN_ID:-local}"
  if [[ -n "$PREV" ]]; then
    [[ -f "$PREV" ]] || { echo "ci-weights: --prev $PREV is not a file" >&2; exit 1; }
    # every tree namespace gets a measured figure, 0 for one the run did not enter, so
    # a namespace that turned all-`^:slow` falls toward 0.00 instead of holding PREV's
    awk -F'\t' 'NR == FNR { m[$1] = $2; next } { printf "%s\t%s\n", $1, ($1 in m) ? m[$1] : 0 }' \
      "$tmp/$LEG.tsv" "$tmp/tree.txt" > "$tmp/$LEG.measured"
    # shellcheck source=scripts/lib/ns-timings.sh
    . scripts/lib/ns-timings.sh
    ns_timings_average "$PREV" "$tmp/$LEG.measured" > "$tmp/$LEG.tsv"
    source="$source, averaged into $PREV at $NS_TIMINGS_WEIGHT"
  fi
  write_weights "$LEG" "$tmp/$LEG.tsv" "$OUT" "$source"
  exit 0
fi

[[ -n "$RUN" && -z "$LEG$OUT$PREV$CHECK$LIST" ]] || { usage; exit 2; }
command -v gh >/dev/null 2>&1 || { echo "ci-weights: gh not found on PATH" >&2; exit 127; }

# One `gh` call resolves the job ids; the logs come one job at a time because a
# run's combined log is a zip this would have to unpack.  The required-check jobs
# `memory` and `disk` log no `lein test` line and are skipped.
jobs=$(gh api "repos/$REPO/actions/runs/$RUN/jobs" --paginate \
         --jq '.jobs[] | select(.name | test("^(memory|disk)-shard-[0-9]+$")) | "\(.id) \(.name)"') || exit 1
if [[ -z "$jobs" ]]; then
  echo "ci-weights: run $RUN has no memory or disk shard jobs" >&2
  exit 1
fi

: > "$tmp/disk.log"
: > "$tmp/memory.log"
while read -r id name; do
  echo "ci-weights: reading $name" >&2
  gh run view --repo "$REPO" --job "$id" --log >> "$tmp/${name%%-*}.log" || exit 1
done <<< "$jobs"

# A namespace's cost is the gap from its own `lein test` line to the next one, and
# the last namespace of a shard is closed by that shard's `Ran N tests` line. The
# runner prefixes every line with a timestamp, so the field before the message is the clock; a run
# crossing midnight adds the day back rather than recording a negative gap.
timings() {
  awk -F'\t' '
    { line = $0
      sub(/^[^\t]*\t[^\t]*\t/, "", line)   # the job and step columns gh prefixes
      sub(/^[^0-9]+/, "", line)               # a byte-order mark on the first line
      if (line !~ /^[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]T/) next
      clock = substr(line, 12, 15); msg = substr(line, index(line, "Z ") + 2)
      split(clock, c, ":"); t = c[1] * 3600 + c[2] * 60 + c[3]
      if (msg ~ /^lein test vaelii/) { ns = substr(msg, 11) }
      else if (msg ~ /^Ran [0-9]+ tests/) { ns = "" }
      else next
      if (prev != "") { d = t - pt; if (d < 0) d += 86400; secs[prev] = d }
      prev = ns; pt = t
    }
    END { for (k in secs) printf "%s\t%.2f\n", k, secs[k] }' "$1" | sort
}

for leg in disk memory; do
  timings "$tmp/$leg.log" > "$tmp/$leg.tsv"
  [[ -s "$tmp/$leg.tsv" ]] || { echo "ci-weights: no namespace timings in the $leg-shard logs" >&2; exit 1; }
  write_weights "$leg" "$tmp/$leg.tsv" "scripts/ci-test-weights-$leg.tsv" "$REPO run $RUN"
done
exit
}
