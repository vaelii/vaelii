#!/usr/bin/env bash
# The test namespaces whose bodies gate on an answer-set solver being present.
#
# Every such namespace reads `solver/available?` (or `clasp/available?`, for the one
# that asserts the refusal an absent binary earns) at load, and wraps the solver tests
# in `(when asp? …)`. Without a solver on the box those bodies do not run and the
# namespace still reports as passing, so the `asp` CI job installs clasp and runs
# exactly this list.
#
# DERIVED, not written down: the list is recomputed from the tree on every run, so a
# namespace that starts gating on the solver is covered the day it lands rather than
# the day somebody remembers to add it here. `vaelii.asp-roster-test` pins the same
# scan against a committed roster, so the set changing is visible in review.
#
# Prints one namespace per line, sorted.
set -euo pipefail
cd "$(dirname "$0")/.."
grep -rlE '\((solver|clasp)/available\?\)' test/ \
  | grep -v '/asp_roster_test\.clj$' \
  | sed -e 's|^test/||' -e 's|\.clj$||' -e 's|/|.|g' -e 's|_|-|g' \
  | sort
