#!/usr/bin/env bash
# scripts/ci-shard.sh — the test namespaces one CI shard runs.
#
#   scripts/ci-shard.sh <shard> <of> [--weights FILE]   # 1-based: `3 4` is the third of four
#
# .github/workflows/test.yml runs each backend leg across several runner VMs,
# and this script decides which namespaces every VM gets.  The memory leg and
# the disk-log leg call it over the same namespace list with different shard
# counts, so the rule for splitting the suite is stated once.
#
# A SHARD IS A WHOLE NUMBER OF NAMESPACES.  Several tests in one file share a
# `:once` fixture, so no file is split across two shards.  scripts/test-parallel.sh
# refuses the same thing for the same reason.
#
# THE SPLIT IS BY MEASURED TIME, NOT BY FILE COUNT.  Namespace cost is spread
# widely enough that an equal count of files is not an equal amount of work: the
# alphabetical halves this replaced put 752s on one runner and 1060s on the other
# in run 33979380791, a 29% spread that the slower half pays for.  Every
# namespace is weighted by scripts/ci-test-weights.tsv and handed to whichever
# shard is lightest so far, longest first — the standard greedy bin-pack, which
# scripts/test-parallel.sh already runs against its own local timings.
#
# A STALE WEIGHT PUTS A NAMESPACE IN THE WRONG SHARD; A MISSING ONE DROPS NO
# TEST.  The namespace list comes from the tree rather than from the weights
# file, so a namespace the file does not name still runs, weighted at the mean of
# the namespaces the file does name.  scripts/ci-weights.sh regenerates the file
# from a finished run.
#
# The output is one namespace per line on stdout, ready for `lein test`; the
# summary line goes to stderr so a caller can read the list from a pipe.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

WEIGHTS=scripts/ci-test-weights.tsv

usage() {
  echo "usage: scripts/ci-shard.sh <shard> <of> [--weights FILE]   # 1-based, e.g. 3 4" >&2
}

# A flag rather than an environment variable, and the reason is that
# vaelii.config-surface-test freezes every `VAELII_*` name the tree reads against
# a golden and a row in docs/operations.md.  A path this script reads is an
# argument to this script; the operator-facing table is not where it belongs.
positional=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --weights) WEIGHTS="${2:?--weights needs a file}"; shift 2 ;;
    --weights=*) WEIGHTS="${1#--weights=}"; shift ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "ci-shard: unknown option $1" >&2; usage; exit 2 ;;
    *) positional+=("$1"); shift ;;
  esac
done

[[ ${#positional[@]} -eq 2 ]] || { usage; exit 2; }
shard="${positional[0]}"
of="${positional[1]}"
[[ "$shard" =~ ^[0-9]+$ && "$of" =~ ^[0-9]+$ ]] || { usage; exit 2; }
if (( of < 1 || shard < 1 || shard > of )); then
  echo "ci-shard: shard $shard of $of is not a shard." >&2
  exit 2
fi

# The shards split a list of FILENAMES; `lein test` selects by NAMESPACE.  A test
# file the glob below misses is therefore run by no shard at all, and every shard
# stays green having skipped it.  Refuse instead: a file defining a top-level
# `deftest` (or `tu/deftest-kb`) has to be named `*_test.clj`.
missed=$(grep -rlE '^\((clojure\.test/)?deftest|^\(tu/deftest-kb' \
           --include='*.clj' --include='*.cljc' test | grep -v '_test\.clj$' || true)
if [[ -n "$missed" ]]; then
  echo "ci-shard: test file(s) outside the *_test.clj glob the shards split on:" >&2
  echo "$missed" >&2
  exit 1
fi

namespaces=()
while IFS= read -r f; do
  ns="${f#test/}"; ns="${ns%.clj}"; ns="${ns//\//.}"; ns="${ns//_/-}"
  namespaces+=("$ns")
done < <(find test -name '*_test.clj' | sort)

if [[ ${#namespaces[@]} -eq 0 ]]; then
  echo "ci-shard: no test namespaces under test/" >&2
  exit 1
fi

# Weight every namespace, heaviest first.  The sort is on the weight descending
# and the name ascending, so two namespaces of equal weight land in a fixed
# order and every shard computes the same assignment from the same input.
printf '%s\n' "${namespaces[@]}" \
  | awk -v weights="$WEIGHTS" '
      BEGIN {
        total = 0; known = 0
        while ((getline line < weights) > 0) {
          if (line ~ /^#/ || line ~ /^[ \t]*$/) continue
          split(line, f, "\t")
          if (f[1] == "") continue
          secs[f[1]] = f[2] + 0; total += f[2] + 0; known++
        }
        close(weights)
        mean = (known > 0) ? total / known : 1
      }
      { printf "%012.3f\t%s\n", (($0 in secs) ? secs[$0] : mean), $0 }' \
  | LC_ALL=C sort -k1,1r -k2,2 \
  | awk -F'\t' -v shard="$shard" -v of="$of" '
      { light = 1
        for (b = 2; b <= of; b++) if (load[b] < load[light]) light = b
        load[light] += $1 + 0; count[light]++
        if (light == shard) print $2
      }
      END {
        for (b = 1; b <= of; b++) all += load[b]
        msg = sprintf("shard %d of %d: %d of %d namespaces, %.0fs of %.0fs predicted",
                      shard, of, count[shard] + 0, NR, load[shard] + 0, all)
        print msg > "/dev/stderr"
      }'
