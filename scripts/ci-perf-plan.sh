#!/usr/bin/env bash
# scripts/ci-perf-plan.sh — the perf-ab probes a change owes, split into one CI job per rep
# and part.
#
#   scripts/ci-perf-plan.sh <base-rev> <reps>
#
# .github/workflows/perf.yml runs this once per pull request and hands its output to the
# jobs after it.  It prints two `key=value` lines, the form $GITHUB_OUTPUT reads:
#
#   probes=<names>   the probes owed, comma-separated, or `all`, or empty
#   matrix=<json>    {"include":[{"rep":1,"part":"rest","probes":"<names>"},…]}, one
#                    entry per rep and part holding a probe
#
# scripts/perf-owed.py selects the probes, from the change between <base-rev> and the
# working tree.  `lein perf --reach` writes the reach map into a clone's git directory, so
# a runner has none, and the selection falls back to perf-owed.py's per-file rules.  A
# changed file under src/vaelii/impl/, or src/vaelii/core.clj, owes every probe.  A change
# under resources/kb/, or to a shipped-KB loader, owes the probes that call a loader.
#
# Each rep's probes run in two parts: `starter-load` alone, and the rest.  On the GitHub
# runners starter-load took 44-52 s per load (2026-11-21), and each of its JVMs loads the
# shipped KB four times, so it alone takes about as long as the other 15 probes together.
#
# Exit: 0, or 2 on a bad argument or a selection that failed.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

if [[ $# -ne 2 || ! "$2" =~ ^[1-9][0-9]*$ ]]; then
  echo "usage: scripts/ci-perf-plan.sh <base-rev> <reps>" >&2
  exit 2
fi

probes=$(python3 scripts/perf-owed.py --base "$1" --kind probes) || exit 2
echo "probes=$probes"
python3 - "$probes" "$2" <<'PY' || exit 2
import importlib.util, json, sys
spec = importlib.util.spec_from_file_location("po", "scripts/perf-owed.py")
po = importlib.util.module_from_spec(spec)
spec.loader.exec_module(po)
sel, reps = sys.argv[1], int(sys.argv[2])
listed = [n.removeprefix("ab:") for n in po.Harness(open(po.AB).read(), True).roots]
names = listed if sel == "all" else [n for n in sel.split(",") if n]
unknown = sorted(set(names) - set(listed))
if unknown:
    sys.exit(f"ci-perf-plan: perf-owed.py selected {unknown}, which {po.AB}'s `probes` does not list")
solo = "starter-load"
parts = [(k, v) for k, v in ((solo, [n for n in names if n == solo]),
                             ("rest", [n for n in names if n != solo])) if v]
print("matrix=" + json.dumps({"include": [{"rep": r, "part": k, "probes": ",".join(v)}
                                          for r in range(1, reps + 1) for k, v in parts]},
                             separators=(",", ":")))
PY
exit
}
