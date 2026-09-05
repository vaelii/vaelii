#!/usr/bin/env bash
# scripts/ci-weights.sh — rewrite scripts/ci-test-weights.tsv from a finished CI run.
#
#   scripts/ci-weights.sh <run-id> [--repo owner/name] [--out FILE]
#
# scripts/ci-shard.sh packs the shards of .github/workflows/test.yml by measured
# namespace time, and this script is where those measurements come from.  Every
# line a `lein test` job logs is stamped by the runner, so the gap between one
# `lein test <namespace>` line and the next is what that namespace cost on the
# hardware CI actually runs on.  Point this at a green run of the workflow after
# a change that moves the numbers, commit the result, and the shards go back to
# finishing together.
#
# THE DISK-LOG SHARDS SUPPLY THE COLUMN.  They are the slower leg, so they are the
# one whose balance decides the workflow's wall time.  The memory shards are read
# too, and only to report how closely the two legs agree — the header this writes
# carries that correlation, which is the argument for one column serving both.
#
# A NAMESPACE THE RUN DID NOT ENTER IS WRITTEN AT 0.00 rather than left out, so a
# namespace whose every test is `^:slow` is weighted at what it costs the
# `:default` selector instead of at the mean.  A namespace added to the tree since
# the run gets no line at all, and scripts/ci-shard.sh gives it the mean.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

OUT=scripts/ci-test-weights.tsv
REPO="vaelii/vaelii"
RUN=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --repo) REPO="${2:?--repo needs owner/name}"; shift 2 ;;
    --out)  OUT="${2:?--out needs a file}"; shift 2 ;;
    -h|--help) sed -n '2,5p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "ci-weights: unknown option $1" >&2; exit 2 ;;
    *)  RUN="$1"; shift ;;
  esac
done

if [[ -z "$RUN" ]]; then
  echo "usage: scripts/ci-weights.sh <run-id> [--repo owner/name] [--out FILE]" >&2
  exit 2
fi
command -v gh >/dev/null 2>&1 || { echo "ci-weights: gh not found on PATH" >&2; exit 127; }

tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT

# One `gh` call resolves the job ids; the logs come one job at a time because a
# run's combined log is a zip this would have to unpack.
jobs=$(gh api "repos/$REPO/actions/runs/$RUN/jobs" --paginate \
         --jq '.jobs[] | select(.name | test("^(memory|disk)(-shard-[0-9]+)?$")) | "\(.id) \(.name)"') || exit 1
if [[ -z "$jobs" ]]; then
  echo "ci-weights: run $RUN has no memory or disk jobs" >&2
  exit 1
fi

: > "$tmp/disk.log"
: > "$tmp/memory.log"
while read -r id name; do
  # The gate jobs `memory` and `disk` match the same pattern as their shards and
  # log no `lein test` line, so reading them adds nothing and costs one request.
  # The pattern takes them so that this also reads a run from before either leg
  # was sharded, where the whole leg is one job under the bare name.
  case "$name" in
    disk*)   dest="$tmp/disk.log" ;;
    memory*) dest="$tmp/memory.log" ;;
    *) continue ;;
  esac
  echo "ci-weights: reading $name" >&2
  gh run view --repo "$REPO" --job "$id" --log >> "$dest" || exit 1
done <<< "$jobs"

# A namespace's cost is the gap from its own `lein test` line to the next one, and
# the last namespace of a shard is closed by that shard's `Ran N tests` line. The
# runner stamps every line, so the field before the message is the clock; a run
# crossing midnight adds the day back rather than recording a negative gap.
timings() {
  awk -F'\t' '
    { line = $0
      sub(/^[^\t]*\t[^\t]*\t/, "", line)   # the job and step columns gh prefixes
      sub(/^[^0-9]+/, "", line)               # a byte-order mark on the first line
      if (line !~ /^[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]T/) next
      stamp = substr(line, 12, 15); msg = substr(line, index(line, "Z ") + 2)
      split(stamp, c, ":"); t = c[1] * 3600 + c[2] * 60 + c[3]
      if (msg ~ /^lein test vaelii/) { ns = substr(msg, 11) }
      else if (msg ~ /^Ran [0-9]+ tests/) { ns = "" }
      else next
      if (prev != "") { d = t - pt; if (d < 0) d += 86400; secs[prev] = d }
      prev = ns; pt = t
    }
    END { for (k in secs) printf "%s\t%.2f\n", k, secs[k] }' "$1" | sort
}

timings "$tmp/disk.log"   > "$tmp/disk.tsv"
timings "$tmp/memory.log" > "$tmp/memory.tsv"
[[ -s "$tmp/disk.tsv" ]] || { echo "ci-weights: no namespace timings in the disk-shard logs" >&2; exit 1; }

find test -name '*_test.clj' \
  | sed -e 's|^test/||' -e 's|\.clj$||' -e 's|/|.|g' -e 's|_|-|g' \
  | sort > "$tmp/tree.txt"

# Pearson's r over the namespaces both legs timed, plus the ratio of their totals.
# The header states both, because one column standing for two legs is a claim
# about them and a reader is owed the number behind it.
read -r agree ratio pairs <<< "$(awk -F'\t' '
  NR == FNR { d[$1] = $2 + 0; next }
  ($1 in d) { n++; x[n] = d[$1]; y[n] = $2 + 0; sx += x[n]; sy += y[n] }
  END {
    if (n < 2) { print "0 0 0"; exit }
    mx = sx / n; my = sy / n
    for (i = 1; i <= n; i++) { a = x[i] - mx; b = y[i] - my; num += a * b; dx += a * a; dy += b * b }
    printf "%.3f %.2f %d\n", num / sqrt(dx * dy), sx / sy, n
  }' "$tmp/disk.tsv" "$tmp/memory.tsv")"

total=$(awk -F'\t' '{ s += $2 } END { printf "%.0f", s }' "$tmp/disk.tsv")
count=$(wc -l < "$tmp/tree.txt" | tr -d ' ')

{
  cat <<HDR
# scripts/ci-test-weights.tsv — how long each test namespace takes on a CI runner.
#
# \`namespace<TAB>seconds\`.  scripts/ci-shard.sh bin-packs the namespaces by these
# numbers so that the shards of one .github/workflows/test.yml leg finish within
# seconds of each other instead of within minutes.
#
# MEASURED ON THE DISK-LOG LEG, AND THE MEMORY LEG READS THE SAME COLUMN.  Both
# legs run the same namespaces in the same order of cost: over the $pairs namespaces
# the run below timed on both, the per-namespace disk-log and memory figures
# correlate at r = $agree, memory being the faster by a factor of $ratio throughout.
# A second column would carry that one constant and nothing else, and a constant
# factor moves no namespace between shards.
#
# A NAMESPACE ABSENT HERE STILL RUNS.  scripts/ci-shard.sh takes the namespace
# list from the tree and reads this file for weights alone, giving a namespace it
# does not find the mean of the ones it does.  A new test therefore costs balance
# until the next regeneration and never costs coverage.  A namespace at 0.00 is one
# whose every test is \`^:slow\` or \`^:multi-jvm\`, so the \`:default\` selector these
# shards run enters none of it.
#
# Regenerate from a green run of the workflow:
#
#   scripts/ci-weights.sh <run-id>          # rewrites this file in place
#
# Source: $REPO run $RUN, VAELII_TEST_BACKEND=disk-log, $count namespaces,
# ${total}s of namespace time across the disk-shard jobs.
HDR
  awk -F'\t' '
    NR == FNR { w[$1] = $2; next }
    { printf "%s\t%s\n", $1, ($1 in w) ? w[$1] : "0.00" }' "$tmp/disk.tsv" "$tmp/tree.txt"
} > "$OUT.new" && mv "$OUT.new" "$OUT"

echo "ci-weights: $OUT — $count namespaces, ${total}s, from $REPO run $RUN" >&2
