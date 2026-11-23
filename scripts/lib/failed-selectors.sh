#!/usr/bin/env bash
# scripts/lib/failed-selectors.sh — the `lein test :only <namespace>/<test>` lines a red
# run prints, read in one place: off a finished log by suite-marks.sh, and off the run
# itself, as it goes, by the CI suite step.
#
# Sourced, never executed:
#   . scripts/lib/failed-selectors.sh
#   lein test … 2>&1 | ns_timings FILE | annotate_failed_selectors LEG SHARD LOG ARTIFACT | tee LOG
#
# Leiningen's test report prints `lein test :only <namespace>/<test>` above every failing
# assertion, the selector that reruns that one test.  The two patterns below are the
# characters suite-marks.sh's `failing_namespaces` and `failing_tests` have always
# accepted in each half, and both now read them from here.  Like suite-marks.sh, this
# file reads only its arguments, and sourcing it runs nothing.
#
# Every name below is read by the sourcing script, which SC2034 cannot see across a `.`.
# shellcheck disable=SC2034

FAILED_SELECTOR_NS='[a-zA-Z0-9._-]+'
FAILED_SELECTOR_TEST='[a-zA-Z0-9._?!*<>=+-]+'

# GitHub keeps 10 error annotations a step, and drops the rest without a word.  Past
# the cap, one warning says how many more tests failed and where they are.
FAILED_SELECTOR_ANNOTATIONS_MAX=10
# The longest `<namespace>/<test>` annotated; a longer one is counted as malformed.
FAILED_SELECTOR_ID_MAX=200
# The longest annotation message, before escaping.
FAILED_SELECTOR_MESSAGE_MAX=500
# How many distinct failing tests the stage remembers to tell a repeat from a new one.
# Past it the count of tests past the cap is a floor, and the warning says so.
FAILED_SELECTOR_SEEN_MAX=1000

# GitHub's workflow-command escapes: `gh_escape_data` for the message after `::`, and
# `gh_escape_property` for a `key=value` before it, where `:` and `,` would end the value.
# Each prints its argument escaped, with no newline.
gh_escape_data() {
  local s="$1" pct='%'
  s=${s//"$pct"/%25}; s=${s//$'\r'/%0D}; s=${s//$'\n'/%0A}
  printf '%s' "$s"
}
gh_escape_property() {
  local s
  s=$(gh_escape_data "$1")
  s=${s//:/%3A}; s=${s//,/%2C}
  printf '%s' "$s"
}

# `annotate_failed_selectors LEG SHARD LOG ARTIFACT` copies stdin to stdout unchanged and,
# the first time a failing test's line arrives, writes one `::error` workflow command
# for it to stderr, where the runner reads it and the log `tee` writes never holds it.
# LEG and SHARD (`<n>/<of>`) say which job failed, and LOG and ARTIFACT where its full
# output is.  An argument that is not of the shape CI passes reads `(invalid)`.
#
# What is annotated is the test's name, matched whole against the two patterns above and
# at most FAILED_SELECTOR_ID_MAX long — never the failure's report, which can quote any
# value a test held.  A `lein test :only ` line that does not match is forwarded like any
# other, counted, and named in no annotation.  Every annotation is escaped and its
# message cut at FAILED_SELECTOR_MESSAGE_MAX.
#
# The stage never stops reading before its input ends: past the cap it keeps forwarding,
# and at the end it writes one `::warning` for the tests past the cap and the markers
# that did not match.
#
# Its exit status is ns_timings': it forwards each line with the same `printf`, so a
# consumer that fails or stops reading fails the pipe as it did without the stage, and
# otherwise it returns 0.  An annotation that cannot be written is dropped: each is
# written from a subshell, so a closed or broken stderr fails that subshell alone.
#
# Bash 3.2 (macOS's /bin/bash) runs it: no associative arrays, so the tests already seen
# are one newline-separated string, and a repeat of the line just before skips the scan.
annotate_failed_selectors() {
  local LC_ALL=C
  local leg="${1:-}" shard="${2:-}" log="${3:-}" artifact="${4:-}"
  local re="^lein test :only (${FAILED_SELECTOR_NS})/(${FAILED_SELECTOR_TEST})\$"
  local max="$FAILED_SELECTOR_ANNOTATIONS_MAX" seen=$'\n' nseen=0 full=0
  local line last="" id ns file shown=0 more=0 bad=0 msg
  [[ "$leg" =~ ^[a-z][a-z0-9-]{0,31}$ ]] || leg='(invalid)'
  [[ "$shard" =~ ^[0-9]{1,4}/[0-9]{1,4}$ ]] || shard='(invalid)'
  [[ "$log" =~ ^[A-Za-z0-9._/-]{1,200}$ ]] || log='(invalid)'
  [[ "$artifact" =~ ^[A-Za-z0-9._-]{1,100}$ ]] || artifact='(invalid)'
  [[ "$max" =~ ^[0-9]{1,3}$ ]] || max=10

  # A failed forward flushes bash 3.2's buffered bytes into /dev/null as ns_timings' does,
  # so the annotation subshell does not write them to stderr.
  while :; do
    if IFS= read -r line; then
      printf '%s\n' "$line" || { printf '%s' '' > /dev/null; false; }
    elif [[ -n "$line" ]]; then                    # a last line with no newline
      printf '%s' "$line" || { printf '%s' '' > /dev/null; false; }
    else
      break
    fi
    case "$line" in
      "lein test :only "*) ;;
      *) continue ;;
    esac
    id="${line#lein test :only }"
    if [[ ! "$line" =~ $re ]] || (( ${#id} > FAILED_SELECTOR_ID_MAX )); then
      bad=$((bad + 1)); continue
    fi
    [[ "$id" == "$last" ]] && continue
    last="$id"
    [[ "$seen" == *$'\n'"$id"$'\n'* ]] && continue
    if (( nseen < FAILED_SELECTOR_SEEN_MAX )); then
      seen+="$id"$'\n'; nseen=$((nseen + 1))
    else
      full=1
    fi
    if (( shown >= max )); then more=$((more + 1)); continue; fi
    shown=$((shown + 1))
    ns="${id%%/*}"; file="test/${ns//.//}"; file="${file//-/_}.clj"
    msg="$id fails in the $leg leg, shard $shard. Its output is in $log (artifact $artifact)."
    _failed_selector_emit error "$id fails ($leg, shard $shard)" "$msg" "$file"
  done

  if (( more > 0 || bad > 0 )); then
    msg=""
    if (( more > 0 )); then
      (( full )) && more="$more or more"
      if [[ "$more" == 1 ]]; then msg="1 more failing test past the cap of $max is not annotated."
      else msg="$more more failing tests past the cap of $max are not annotated."; fi
    fi
    if (( bad > 0 )); then
      [[ -n "$msg" ]] && msg+=" "
      if (( bad == 1 )); then msg+="1 failure marker that does not name one namespace/test is not annotated."
      else msg+="$bad failure markers that do not name one namespace/test are not annotated."; fi
    fi
    msg+=" Every failure is in $log (artifact $artifact)."
    _failed_selector_emit warning "Unannotated failures ($leg, shard $shard)" "$msg" ""
  fi
  return 0
}

# `_failed_selector_emit LEVEL TITLE MESSAGE FILE` writes one workflow command to stderr,
# naming FILE only when the tree has it.
_failed_selector_emit() {
  local props="" msg="${3:0:FAILED_SELECTOR_MESSAGE_MAX}"
  [[ -n "$4" && -f "$4" ]] && props="file=$(gh_escape_property "$4"),"
  props+="title=$(gh_escape_property "$2")"
  ( printf '::%s %s::%s\n' "$1" "$props" "$(gh_escape_data "$msg")" ) >&2 2>/dev/null || :
}
