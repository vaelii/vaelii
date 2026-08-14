#!/usr/bin/env bash
# scripts/lint.sh — unified static-analysis runner behind `lein lint`.
#
# Runs every check (NOT fail-fast, so one pass surfaces every problem), captures
# each one's output + exit code, and prints a uniform report: one ✓/✗ line per
# check, a short summary on success, the full captured detail only under a FAILED
# check, and a dim [Ns] on the slow ones.  Exit non-zero iff any check failed.
#
#   - glossary    structural lint for docs/glossary.md (badges + order + links)
#   - versions    the coordinates this tree states twice agree (sibling pin,
#                 lein-cloverage)
#   - links       relative markdown links across README + docs/ resolve
#   - drift       doc claims about the code still match the code
#   - kondo       clj-kondo over src + test + bench   (native binary; a NOTE
#                 under the row when the local version is not the CI pin)
#   - cljfmt      `lein cljfmt check` — formatting     (config in project.clj :cljfmt)
#   - shellcheck  the repo's shell scripts
#   - reflect     a compile pass over src + bench; any reflection/boxing warning
#                 fails.  The test tree is covered by gate.sh instead — see the
#                 header of scripts/check-reflection.sh for why the split exists
#   - unused      a public var under impl/ that nothing references, against
#                 scripts/unused-publics-baseline.txt
#   - authorship  the roster and matching rules behind the `authorship` CI gate,
#                 against synthetic commits (`--selftest`; no network).  The gate
#                 itself only runs on a pull request, so this is the one place the
#                 rules are exercised before one arrives
#
#   lein lint               # the clean report
#   VERBOSE=1 lein lint     # also dump each check's full output, pass or fail
#   bash scripts/lint.sh -v # same, when run directly
#
# The granular `lein lint-glossary` / `lint-versions` / `lint-links` /
# `lint-drift` / `lint-kondo` / `lint-cljfmt` / `lint-shellcheck` /
# `lint-reflect` / `lint-unused` / `lint-authorship` aliases run a single check
# for a quick one-off.
set -uo pipefail   # NOT -e: every check must run even after one fails.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# Read the inherited VERBOSE env (or a -v arg) before normalizing it to 0/1 —
# don't reset to 0 first, that would clobber `VERBOSE=1 lein lint`.
if [[ "${1:-}" == "-v" || "${VERBOSE:-0}" == "1" ]]; then VERBOSE=1; else VERBOSE=0; fi

# Colour: VAELII_COLOR=always|never forces; otherwise on for a capable terminal
# (NO_COLOR / CI off).  `lein lint` pipes our stdout, so key off TERM as well as
# `-t 1`, since TERM survives that pipe.
color=0
case "$(printf '%s' "${VAELII_COLOR:-}" | tr '[:upper:]' '[:lower:]')" in
  always) color=1 ;;
  never)  color=0 ;;
  *) [[ -z "${NO_COLOR:-}" && -z "${CI:-}" \
        && ( -t 1 || ( -n "${TERM:-}" && "${TERM:-}" != dumb ) ) ]] && color=1 ;;
esac
if [[ $color -eq 1 ]]; then
  GREEN=$'\e[32m'; RED=$'\e[1;31m'; YELLOW=$'\e[33m'; DIM=$'\e[2m'; BOLD=$'\e[1m'; RST=$'\e[0m'
else
  GREEN=''; RED=''; YELLOW=''; DIM=''; BOLD=''; RST=''
fi

pass=0; fail=0; failed_labels=()
# The `.XXXXXX` is mandatory, not decoration.  `-t` means two different things:
# BSD mktemp (macOS) takes a PREFIX and appends its own randomness, while GNU
# coreutils takes a TEMPLATE and rejects one with fewer than three X's.  So a
# bare `-t vaelii-lint` works here and dies on every Linux runner with "too few
# X's in template" — leaving `$out` empty, every check writing to nothing, and
# all six reported as FAILED.  A template with X's satisfies both.  Same
# spelling as vaelii-foreign's scripts/lint.sh.
out="$(mktemp -t vaelii-lint.XXXXXX)"
trap 'rm -f "$out"' EXIT

# summary <label> <outfile> — a short one-line success summary, drawn from the
# tool's own output where a figure carries info, else fixed text.
summary() {
  local label="$1" o="$2" s=""
  case "$label" in
    glossary)   s="$(grep -oE '\([0-9]+ entries\)' "$o" | head -1 | tr -d '()')" ;;
    versions)   s="$(sed -n 's/^lint-versions: OK (\(.*\))$/\1/p' "$o" | head -1)" ;;
    links)      s="all resolve" ;;
    drift)      s="$(grep -oE '[0-9]+ errors, [0-9]+ warnings across [0-9]+ docs' "$o" | head -1)"
                s="${s/across /(}"; s="${s/ docs./ docs)}" ;;
    kondo)      s="$(grep -oE 'errors: [0-9]+, warnings: [0-9]+' "$o" | tail -1)" ;;
    cljfmt)     s="all files formatted" ;;
    shellcheck) s="scripts clean" ;;
    reflect)    s="$(grep -oE 'no reflection warnings.*' "$o" | head -1)" ;;
    unused)     s="$(grep -oE '[0-9]+ known[^.]*' "$o" | head -1)" ;;
    authorship) s="$(grep -oE '[0-9]+ checks, all pass' "$o" | head -1)" ;;
  esac
  echo "${s:-ok}"
}

# print_status <label> <rc> <outfile> <seconds> — render one result row.
print_status() {
  local label="$1" rc="$2" o="$3" t="$4" tstr=""
  (( t >= 2 )) && tstr=" ${DIM}[${t}s]${RST}"
  if [[ $rc -eq 0 ]]; then
    printf '%s✓%s %s%s\n' "$GREEN" "$RST" "$(summary "$label" "$o")" "$tstr"
    pass=$((pass + 1))
    [[ $VERBOSE -eq 1 ]] && sed 's/^/        /' "$o"
  else
    printf '%s✗%s FAILED%s\n' "$RED" "$RST" "$tstr"
    sed 's/^/        /' "$o"
    [[ "$label" == cljfmt ]] && printf "        %s→ run \`lein fix\`%s\n" "$DIM" "$RST"
    fail=$((fail + 1)); failed_labels+=("$label")
  fi
}

# tool_hint <bin> — one-line install pointer for a lint dep beyond java/lein.
tool_hint() {
  case "$1" in
    clj-kondo)  echo "brew install borkdude/brew/clj-kondo (macOS), or https://github.com/clj-kondo/clj-kondo/blob/master/doc/install.md" ;;
    shellcheck) echo "brew install shellcheck (macOS), or your distro's shellcheck package" ;;
    python3)    echo "brew install python3 (macOS), or your distro's python3 package" ;;
    *)          echo "" ;;
  esac
}

# check <label> -- <cmd...> — run a check, streaming its row.  <cmd...> starts
# with the binary it needs, so a missing one is detected here once.
check() {
  local label="$1"; shift
  [[ "${1:-}" == "--" ]] && shift
  local bin="$1" hint
  printf '  %-11s ' "$label"
  SECONDS=0
  if ! command -v "$bin" >/dev/null 2>&1; then
    hint="$(tool_hint "$bin")"
    { printf '%s not found on PATH.\n' "$bin"
      [[ -n "$hint" ]] && printf 'Install: %s\n' "$hint"
    } >"$out"
    print_status "$label" 127 "$out" 0
    return
  fi
  "$@" >"$out" 2>&1
  local rc=$? t=$SECONDS
  print_status "$label" "$rc" "$out" "$t"
}

# kondo_version_note — say so when the local clj-kondo is not the one CI pins.
#
# The kondo check runs whatever binary is on PATH, and CI runs the version
# `.github/workflows/lint.yml` names.  Nothing made those the same, so a local
# `lint: 6/6 clean` could sit against a red CI lint: a newer kondo infers more
# and flags what an older one passes, which is a green squash arriving on
# staging with five errors waiting for it.
#
# A NOTE and never a failure, deliberately.  The pin moves whenever the workflow
# is edited, and a package manager can lag it for weeks — brew was four months
# behind the pin at one point, so there was a window where no `brew install`
# could satisfy a hard check.  Refusing to run the linter at all during that
# window costs more than the drift it would report.  Silent when the two agree,
# and silent when either side cannot be read: an unreadable pin is a fact about
# this script's parsing, not a finding about the tree.
kondo_version_note() {
  local pin have
  command -v clj-kondo >/dev/null 2>&1 || return 0
  pin="$(sed -n 's/^[[:space:]]*clj-kondo:[[:space:]]*\([0-9][0-9.]*\).*/\1/p' \
           .github/workflows/lint.yml 2>/dev/null | head -1)"
  have="$(clj-kondo --version 2>/dev/null \
            | grep -oE '[0-9]{4}\.[0-9]{2}\.[0-9]{2}' | head -1)"
  [[ -n "$pin" && -n "$have" && "$pin" != "$have" ]] || return 0
  printf '  %-11s %s! local %s, CI pins %s — CI can fail on what this passes%s\n' \
         '' "$YELLOW" "$have" "$pin" "$RST"
  printf '  %-11s %s  brew upgrade borkdude/brew/clj-kondo, or install-clj-kondo --version %s%s\n' \
         '' "$DIM" "$pin" "$RST"
}

printf '%slint%s\n' "$BOLD" "$RST"

check glossary   -- bash scripts/lint-glossary.sh
check versions   -- bash scripts/lint-versions.sh
check links      -- python3 scripts/check-doc-links.py --public-view
check drift      -- python3 scripts/check-doc-drift.py
check kondo      -- clj-kondo --lint src test bench
kondo_version_note
check cljfmt     -- lein cljfmt check
# Named one by one rather than globbed, so adding a script is a decision — and so
# the list has to be kept. A script missing from it is one nothing checks, which is
# how a `mktemp -t` form that works on BSD and dies on GNU coreutils reached a
# runner. Add the file here in the same commit that adds the file.
check shellcheck -- shellcheck scripts/lint.sh scripts/lint-glossary.sh scripts/lint-versions.sh \
                               scripts/coverage.sh scripts/gate.sh scripts/test-backends.sh \
                               scripts/test-sweeps.sh scripts/lib/suite-marks.sh \
                               scripts/update-badges.sh scripts/link-checkouts.sh \
                               scripts/check-reflection.sh scripts/test-parallel.sh \
                               scripts/run-bench-caches.sh
check reflect    -- bash scripts/check-reflection.sh
check unused     -- python3 scripts/check-unused-publics.py
check authorship -- python3 scripts/check-authorship.py --selftest

total=$((pass + fail))
if [[ $fail -eq 0 ]]; then
  printf '%slint: %d/%d clean%s\n' "$GREEN" "$pass" "$total" "$RST"
  exit 0
fi
printf '%slint: %d/%d — %s FAILED%s\n' "$RED" "$pass" "$total" "${failed_labels[*]}" "$RST"
exit 1
