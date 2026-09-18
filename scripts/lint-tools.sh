#!/usr/bin/env bash
# scripts/lint-tools.sh — ruff over the Python this repo ships under tools/.
#
# tools/vaelii-top is ~1,800 lines of Python and no other lint stage reads it:
# clj-kondo, cljfmt, reflect and unused are Clojure, lint-shellcheck globs
# scripts/*.sh, and check-doc-links/check-doc-drift walk docs/ plus a fixed list
# of root markdown.  Only lint-conflict-markers reached tools/, and it greps
# every tracked file for one pattern.  So five dead imports sat in the tree
# through four commits.
#
# THE ROSTER IS `git ls-files`, not a hand-kept list — the opposite of
# scripts/lint-shellcheck.sh, whose roster is written out file by file.  The two
# differ because the trees differ: scripts/ holds shell beside Python beside
# .edn and a release can withhold a script, while tools/ is whole Python
# packages with a working directory that must not be read.  A checkout's
# tools/vaelii-top/.venv holds ~30,000 vendored files and is gitignored, so
# asking git for the tracked set both names every file and excludes the venv,
# with no list to keep current.
#
# A MISSING ruff SKIPS, it does not fail.  ruff is not in any CI image this repo
# uses and is not a lein dependency, so a hard check would red every runner and
# every contributor who has not installed it.  The stage prints what it did
# either way, and the row says "skipped" rather than "clean" so a skip is not
# read as a pass.  The same reasoning scripts/lint.sh applies to a clj-kondo
# version older than the CI pin.
#
#   lein lint-tools          # this check alone
#   bash scripts/lint-tools.sh
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# -z/-d, because a path can hold a space and the loop must not split on one.
files=()
while IFS= read -r -d '' f; do files+=("$f"); done \
  < <(git ls-files -z -- 'tools/**/*.py')

if [[ ${#files[@]} -eq 0 ]]; then
  echo "lint-tools: no Python under tools/"
  exit 0
fi

if ! command -v ruff >/dev/null 2>&1; then
  echo "lint-tools: skipped — ruff not on PATH (${#files[@]} file(s) unchecked)"
  echo "Install: brew install ruff (macOS), or pipx install ruff"
  exit 0
fi

# Rules and target version live in tools/vaelii-top/pyproject.toml, which ruff
# discovers from each file's own directory.  A second tool added under tools/
# states its own.
# -q drops ruff's "All checks passed!" banner; the row below is the summary
# scripts/lint.sh reads, and two success lines would make it pick the wrong one.
ruff check -q "${files[@]}" || exit 1
echo "lint-tools: ${#files[@]} file(s) clean"
