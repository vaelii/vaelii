#!/usr/bin/env bash
# scripts/lib/revision.sh — what a run was taken against, in the two shapes that
# want it: a `#` line at the top of a log, and a short line beside the output.
#
# A verdict that does not name its revision is half a verdict.  On a shared
# checkout those are two different questions: a matrix takes ~35 minutes and
# another writer landing a test halfway through moves the test and assertion
# counts under it — the artifact then shows counts that differ per run, which
# reads exactly like a run that skipped something.  It cost one investigation to
# establish that it was not.  The same applies to a `lein gate` run whose log is read an
# hour later, and to a number quoted into a report.
#
# `REVISION_PATHS` are the paths a run compiles or loads: `src/`, `test/`,
# `resources/` (the shipped KB every open loads), `bench/` (the perf claims) and
# the two project files (dependency versions, the test heap).  A dirty `docs/` or
# `CHANGELOG.md` cannot move a count, and reporting it would say DIRTY on every
# run of a repo where somebody is always writing.
#
# Sourced, never executed:
#   . scripts/lib/revision.sh
#
# The rule for what belongs in here is `suite-marks.sh`'s: it reads only its
# arguments and the repository, so both the suite scripts and `gate.sh` can take
# it without taking anything else.

# The revision, short.  `no-git` rather than empty, so a log line states a fact
# about a tarball rather than showing a field somebody forgot to fill in.
revision_hash() {
  git rev-parse --short HEAD 2>/dev/null || echo "no-git"
}

REVISION_PATHS=(src test resources bench project.clj project-env.clj)
REVISION_SCOPE="src/, test/, resources/, bench/ and the project files"

# How many files under REVISION_PATHS the run was taken over rather than at.
revision_dirty() {
  git status --porcelain -- "${REVISION_PATHS[@]}" 2>/dev/null | wc -l | tr -d ' '
}

# `<hash> — <state>`, and nothing else: no colour, no newline, no label.  The
# caller owns all three, which is what lets one line serve a console header, a
# summary row and the log header below.
revision_line() {
  local rev dirty
  rev=$(revision_hash)
  dirty=$(revision_dirty)
  if [ "${dirty:-0}" -gt 0 ]; then
    printf '%s — tree DIRTY: %s uncommitted file(s) under %s' "$rev" "$dirty" "$REVISION_SCOPE"
  else
    printf '%s — %s clean' "$rev" "$REVISION_SCOPE"
  fi
}

# The first line of a log: the same fact, dated, and commented so the greps that
# read these logs back (`^Ran `, `^lein test :only `) cannot match it.  `$1`
# names what was run — every caller passes it (the backend, the sweep, the
# `lein gate` stage); the `suite run` default is a fallback for a bare call, not the common case.
revision_header() {
  printf '# %s at %s — %s\n' "${1:-suite run}" "$(revision_line)" "$(date '+%Y-%m-%d %H:%M:%S')"
}
