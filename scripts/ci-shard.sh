#!/usr/bin/env bash
# scripts/ci-shard.sh — the test namespaces one CI shard runs.
#
#   scripts/ci-shard.sh <shard> <of> [--leg disk|memory] [--weights FILE] [--history FILE]
#                                                  # 1-based: `3 4` is the third of four
#
# .github/workflows/test.yml runs each backend leg across several runner VMs,
# and this script decides which namespaces every VM gets.  The memory leg and
# the disk-log leg call it over the same namespace list, each with its own
# weights, so the rule for splitting the suite is stated once.
#
# A SHARD IS A WHOLE NUMBER OF NAMESPACES.  Several tests in one file share a
# `:once` fixture, so no file is split across two shards.  scripts/test-parallel.sh
# refuses the same thing for the same reason.
#
# THE SPLIT IS BY MEASURED TIME, NOT BY FILE COUNT.  Namespace cost is spread
# widely enough that an equal count of files is not an equal amount of work: the
# alphabetical halves this replaced put 752s on one runner and 1060s on the other
# in run 33979380791, a 29% spread that the slower half pays for.  Every
# namespace is weighted by its leg's weights file and handed to whichever
# shard is lightest so far, longest first — the standard greedy bin-pack, which
# scripts/test-parallel.sh already runs against its own local timings.
#
# The weights are the leg's own: scripts/ci-test-weights-<leg>.tsv, or --weights
# FILE, which the workflow passes when the previous green run of that leg left
# its timings in the Actions cache.  Every shard of one run must read the same
# file, or a namespace lands in two shards or in none, so the workflow resolves
# the cache entry once and hands every shard the same key.
#
# A STALE WEIGHT PUTS A NAMESPACE IN THE WRONG SHARD; A MISSING ONE DROPS NO
# TEST.  The namespace list comes from the tree rather than from the weights
# file, so a namespace the file does not name still runs, weighted at the mean of
# the namespaces the file does name.  scripts/ci-weights.sh regenerates the files.
#
# THE ORDER INSIDE A SHARD PUTS RECURRING FAILURES FIRST.  Once the shards are
# packed, each runs its own namespaces by policy 1 of scripts/ci-test-history.tsv
# (or --history FILE).  Policy 1 sorts by recurring-failure count descending, then
# the leg's weight descending, then name ascending.  So a namespace that keeps
# failing on CI reports before the rest of the shard, and the expensive ones start
# early.  Only the order
# moves.  The history is read after the packing and the packing never sees it, so
# every shard holds the same namespaces with or without it, and nothing stops
# early: the shard still runs every namespace it was given.  The file is checked
# in and every shard reads the same one, so a run replays from the tree alone.  A
# history is ignored whole when it is missing, marked `status: stale`, of another
# policy version, empty, or has one row that is not `namespace<TAB>count`.  The
# shard then runs lightest, heaviest, second lightest, second heaviest, and so on,
# the order it ran before the history existed.  The file is data: awk matches each row
# against a pattern and nothing in it is sourced or evaluated.
#
# The output is one namespace per line on stdout, ready for `lein test`; the
# summary line goes to stderr so a caller can read the list from a pipe.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

WEIGHTS=""
HISTORY=scripts/ci-test-history.tsv
LEG=disk

usage() {
  echo "usage: scripts/ci-shard.sh <shard> <of> [--leg disk|memory] [--weights FILE] [--history FILE]   # 1-based, e.g. 3 4" >&2
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
    --history) HISTORY="${2:?--history needs a file}"; shift 2 ;;
    --history=*) HISTORY="${1#--history=}"; shift ;;
    --leg) LEG="${2:?--leg needs disk or memory}"; shift 2 ;;
    --leg=*) LEG="${1#--leg=}"; shift ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "ci-shard: unknown option $1" >&2; usage; exit 2 ;;
    *) positional+=("$1"); shift ;;
  esac
done

[[ ${#positional[@]} -eq 2 ]] || { usage; exit 2; }
case "$LEG" in disk|memory) ;; *) echo "ci-shard: --leg is disk or memory, not $LEG" >&2; exit 2 ;; esac
[[ -n "$WEIGHTS" ]] || WEIGHTS="scripts/ci-test-weights-$LEG.tsv"
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
  | awk -F'\t' -v shard="$shard" -v of="$of" -v weights="$WEIGHTS" -v history="$HISTORY" '
      # The recurring-failure history, policy 1 (scripts/ci-test-history.tsv says
      # what the numbers are).  Each row is matched whole against the pattern
      # `namespace<TAB>count`; a row that does not match makes the whole file
      # unusable rather than half-used, and nothing in the file is run.
      BEGIN {
        use = 0; why = ""; rows = 0; policy = 0; status = ""
        nsre = "^[a-z][a-z0-9]*(-[a-z0-9]+)*([.][a-z][a-z0-9]*(-[a-z0-9]+)*)*$"
        while ((rc = (getline line < history)) > 0) {
          if (line == "# policy: 1") { policy++; continue }
          if (line ~ /^# policy:/)   { why = why "policy is not 1; "; continue }
          if (line ~ /^# status:/)   { status = status substr(line, 11) ","; continue }
          if (line ~ /^#/ || line ~ /^[ \t]*$/) continue
          n = split(line, f, "\t")
          if (n != 2 || f[1] !~ nsre || f[2] !~ /^(0|[1-9][0-9]*)$/ || length(f[2]) > 6 || (f[1] in fails)) {
            why = why "row " (rows + 1) " is not namespace<TAB>count; "; break
          }
          fails[f[1]] = f[2] + 0; rows++
        }
        if (rc < 0)                    why = "missing; "
        else if (why == "") {
          if (policy != 1)             why = "no \"# policy: 1\" line; "
          else if (status != "current,") why = "status is not current; "
          else if (rows == 0)          why = "no rows; "
          else use = 1
        }
        close(history)
      }
      { light = 1
        for (b = 2; b <= of; b++) if (load[b] < load[light]) light = b
        load[light] += $1 + 0; count[light]++
        if (light == shard) { mine[++m] = $2; cost[$2] = $1 + 0 }
      }
      # Does a run before b?  Policy 1: more recurring failures first, then the
      # heavier, then the name, so two shards given one input print one order.
      function before(a, b,   fa, fb) {
        fa = (a in fails) ? fails[a] : 0; fb = (b in fails) ? fails[b] : 0
        if (fa != fb) return fa > fb
        if (cost[a] != cost[b]) return cost[a] > cost[b]
        return a < b
      }
      END {
        if (use) {
          # An insertion sort: a shard holds some fifty namespaces, and awk has no
          # portable sort of its own.
          for (i = 2; i <= m; i++) {
            x = mine[i]
            for (j = i - 1; j >= 1 && before(x, mine[j]); j--) mine[j + 1] = mine[j]
            mine[j + 1] = x
          }
          for (i = 1; i <= m; i++) print mine[i]
          order = "recurring failures first, from " history
        } else {
          # The shard runs its namespaces lightest, heaviest, second lightest, second
          # heaviest, and so on, so the runtime is spread evenly over the run.
          hi = 1
          for (lo = m; lo >= hi; lo--) {
            print mine[lo]
            if (hi < lo) print mine[hi++]
          }
          sub(/; $/, "", why)
          order = "lightest/heaviest alternating, history " history " ignored: " why
        }
        for (b = 1; b <= of; b++) all += load[b]
        msg = sprintf("shard %d of %d: %d of %d namespaces, %.0fs of %.0fs predicted, from %s; order: %s",
                      shard, of, count[shard] + 0, NR, load[shard] + 0, all, weights, order)
        print msg > "/dev/stderr"
      }'
exit
}
