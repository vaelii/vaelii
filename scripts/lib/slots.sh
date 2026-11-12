#!/usr/bin/env bash
# scripts/lib/slots.sh — how the suite runners share the box: how many JVMs one spins up by
# default, which checkout runs the heavy ones, and the one-matrix-at-a-time lock.
#
# The slot count first: how many JVMs a suite runner spins up in parallel by default,
# in one place so the two runners cannot drift: `test-parallel.sh` shards the namespaces,
# `test-matrix.sh` fans out the configurations, and both size their fan-out from here.
#
# The rule is two terms:
#
#   slots = P − 2 − (vaelii JVMs already running)        floored at 1
#
#   - **P − 2**, where P is the performance-core count read from `hw.perflevel0.logicalcpu`
#     on Apple Silicon — the performance tier alone, the efficiency cores NOT folded in.  Two
#     are held back for the concurrent `lint` stage and the OS.  On a 10-core (8P + 2E) box
#     that is 6 test JVMs, leaving two performance cores plus both efficiency cores free:
#     because P counts only performance cores, `P − 2` never reaches down into the E-cores the
#     way a naive `ncpu − 2` would.  A homogeneous box — an Intel Mac, or Linux CI — has no
#     `perflevel` key and falls back to `ncpu` / `nproc`, where `− 2` just leaves two cores
#     for everything else.
#   - **minus the vaelii JVMs already up.**  This is a shared checkout (several writers in one
#     tree) beside sibling checkouts, so a bench, a dev REPL or another `lein gate` is often already
#     eating cores.  Each such JVM is a slot this run should not also claim, so the count is
#     load-aware rather than a constant.
#
# That second term makes the answer depend on what else is running, so it is NOT the plain
# `P − 2` default — `default_slots` says so on stderr when the subtraction changes the number,
# and stays quiet on an idle box where the two agree.  The count on stdout is the only thing
# a caller captures (`jobs=$(default_slots)`); the note is stderr.
#
# Sourced, never executed:
#   . scripts/lib/slots.sh

# vaelii JVMs already running — the project / bench / dev JVMs doing work, NOT the leiningen
# launcher that spawns each (it pairs with a project JVM already counted, and is a near-idle
# bootstrap parent).  `pgrep -f` matches the full argv and excludes itself, so a bash script,
# a `tail -f` on a log or this call is never counted; the `java.*vaelii` shape keeps it to
# JVMs.  A rough estimate across this checkout AND its siblings — erring toward fewer slots.
# The arguments are process groups whose JVMs are not counted: a running matrix passes its
# own configurations' groups, so it does not count its own JVMs as load.
running_vaelii_count() {
  local pids pid row pg cmd n=0 skip=" $* "
  pids=$(pgrep -f 'java.*vaelii' 2>/dev/null) || pids=''
  for pid in $pids; do
    row=$(ps -o pgid=,command= -p "$pid" 2>/dev/null) || continue
    read -r pg cmd <<<"$row"
    case "$cmd" in
      *leiningen.core.main*) continue ;;   # the launcher parent; its project JVM is counted
    esac
    [[ "$skip" == *" $pg "* ]] || n=$((n + 1))
  done
  printf '%s\n' "$n"
}

# slots_beside [pgid…] prints `<slots> <running> <base>`: the rule above, with the JVMs in
# those process groups left out of `running`.  A running matrix re-reads it
# (scripts/test-matrix.sh).
# shellcheck disable=SC2120  # scripts/test-matrix.sh passes the process groups
slots_beside() {
  local pcores=''
  # perflevel0 is the performance tier on Apple Silicon; the key is absent everywhere else.
  pcores=$(sysctl -n hw.perflevel0.logicalcpu 2>/dev/null) || pcores=''
  [[ -n "$pcores" ]] || pcores=$(sysctl -n hw.ncpu 2>/dev/null) || pcores=''
  [[ -n "$pcores" ]] || pcores=$(nproc 2>/dev/null) || pcores=''
  [[ -n "$pcores" ]] || pcores=4

  local base=$((pcores - 2)); (( base < 1 )) && base=1
  local running; running=$(running_vaelii_count "$@")
  local slots=$((base - running)); (( slots < 1 )) && slots=1
  printf '%s %s %s\n' "$slots" "$running" "$base"
}

default_slots() {
  local slots running base
  read -r slots running base < <(slots_beside)

  # Say when the load term moved the number off the plain P−2 default; quiet when it did not.
  if (( running > 0 )); then
    printf 'slots: %d vaelii JVM(s) already running — using %d, not the default P-2=%d\n' \
      "$running" "$slots" "$base" >&2
  fi
  printf '%s\n' "$slots"
}

# ---- the heavy runs belong to the primary checkout ---------------------------------------
#
# A matrix, an axis sweep or `lein perf` in a linked worktree is a second fleet of JVMs
# beside the primary's, and every runner above drops to one slot when it counts them.  So
# these run from the primary, which also owns the one matrix lock below.  `lein perf --only`,
# limited to the checks a change needs, runs anywhere (scripts/perf.sh).  A separate
# clone is not a linked worktree and is not refused.  `ALLOW_WORKTREE_RUN=release` runs
# one anyway, for the release agent's runs in a scratch worktree at the carved sha; any
# other value is refused, because every other run goes in the primary on main.

# The repository's shared git directory, absolute: the primary's `.git`, from any worktree.
common_git_dir() {
  git rev-parse --path-format=absolute --git-common-dir 2>/dev/null
}

# require_primary <what> exits 3 in a linked worktree, naming the primary to run <what> from.
require_primary() {
  local own common
  own=$(git rev-parse --path-format=absolute --absolute-git-dir 2>/dev/null) || return 0
  common=$(common_git_dir) || return 0
  [[ "$own" == "$common" || "${ALLOW_WORKTREE_RUN:-}" == release ]] && return 0
  printf '%s runs from the primary checkout, %s, not from a linked worktree.\n' \
    "$1" "${common%/.git}" >&2
  printf '  Land the change, then run it there. ALLOW_WORKTREE_RUN=release is for the\n' >&2
  printf '  release agent'\''s runs at a carved sha only.\n' >&2
  exit 3
}

# ---- one matrix at a time, and a queue for the rest --------------------------------------
#
# Two matrices at once each run at one slot, so a second request does not start a second
# matrix.  An `--owed` request that finds one running appends its baseline to the queue
# and returns; the running matrix, as it ends, starts one more over the union of the
# queued baselines, at the primary's HEAD.  A running `--owed` matrix that sees the queue
# non-empty ends at its first verdict (scripts/test-matrix.sh, "ONE VERDICT, THEN MAKE
# ROOM").  The lock and the queue live in the shared git directory, so every worktree of
# the repository sees the same ones.
#
#   lock    `<pid> <revision> <epoch> <run dir>` of the matrix running now
#   queue   one `<commit> <selector> <requester>` line per request waiting for the next
#           matrix
#   red     `<epoch> <run dir>` of the last red matrix, until a green one; see below
#   jobs    the running matrix's slot count, set by `--set-jobs <n>` and re-read by its
#           scheduler every pass; taking and releasing the lock clear it, so a count
#           set for one matrix never carries into the next.  A matrix started with no
#           `--jobs` and given no `--set-jobs` re-reads the slot rule instead, each pass
#           a configuration ends and every MATRIX_SLOTS_EVERY seconds (`slots_beside`)

matrix_state_dir() {
  local d
  d=$(common_git_dir) || return 1
  mkdir -p "$d/vaelii-matrix" 2>/dev/null || return 1
  printf '%s/vaelii-matrix\n' "$d"
}

# box_state_dir prints the directory every clone on the box shares, creating it:
# VAELII_BOX_STATE_DIR, else `$XDG_STATE_HOME/vaelii`, else `~/.local/state/vaelii`.  The
# perf lock and the gate slots live there.  The matrix lock and its queue stay per clone,
# because a queued line names a commit of that clone.
box_state_dir() {
  local d="${VAELII_BOX_STATE_DIR:-${XDG_STATE_HOME:-$HOME/.local/state}/vaelii}"
  mkdir -p "$d" 2>/dev/null || return 1
  printf '%s\n' "$d"
}

# lock_create <lock file> <line> creates the lock file holding <line>, or returns 1 when the
# file exists.  noclobber opens it O_CREAT|O_EXCL, so of two takers only one creates it.
# Every take and restore goes through here rather than `ln`, which Android refuses: a
# lock file is created before its line is written, so an empty one is a take in progress.
lock_create() {
  ( set -o noclobber; printf '%s\n' "$2" >"$1" ) 2>/dev/null
}

# lock_break_stale <lock file> <line> removes the lock file when it still holds <line>, the
# stale lock read before.  An empty <line> is a take in progress, and is left alone until
# the file is a minute old, which outlasts any taker not killed between create and write.
# The rename to a name of this shell's own is atomic, so of two waiters breaking one stale
# lock only one moves it.  A file that no longer holds <line> is a lock taken since the
# read, and goes back through `lock_create`, which refuses to overwrite a lock taken in
# between.
lock_break_stale() {
  local held="$1.stale.$$"
  [[ -z "$2" && -n "$(find "$1" -maxdepth 0 -mmin -1 2>/dev/null)" ]] && return 0
  mv "$1" "$held" 2>/dev/null || return 0
  [[ "$(cat "$held" 2>/dev/null)" == "$2" ]] || lock_create "$1" "$(cat "$held")"
  rm -f "$held"
}

# The lock's line when a live matrix holds it, else nothing.  A lock whose pid is gone,
# or is no longer a test-matrix, is stale and is removed.
matrix_lock_holder() {
  local dir line pid
  dir=$(matrix_state_dir) || return 0
  line=$(cat "$dir/lock" 2>/dev/null) || return 0
  pid=${line%% *}
  if [[ -n "$pid" ]] && ps -o command= -p "$pid" 2>/dev/null | grep -q 'test-matrix'; then
    printf '%s\n' "$line"
  else
    lock_break_stale "$dir/lock" "$line"
  fi
}

# matrix_lock_take <revision> <run dir> takes the lock for this shell, or returns 1 while
# another matrix holds it.
matrix_lock_take() {
  local dir
  dir=$(matrix_state_dir) || return 0
  matrix_lock_holder >/dev/null
  lock_create "$dir/lock" "$$ $1 $(date '+%s') $2" || return 1
  rm -f "$dir/jobs"
}

matrix_lock_release() {
  local dir line
  dir=$(matrix_state_dir) || return 0
  line=$(cat "$dir/lock" 2>/dev/null) || return 0
  [[ "${line%% *}" == "$$" ]] && rm -f "$dir/lock" "$dir/jobs"
  return 0
}

# The file the running matrix re-reads its slot count from.  Its scheduler resolves the
# path once and reads it with the `read` builtin, so the one-second poll forks nothing.
matrix_jobs_file() {
  local dir
  dir=$(matrix_state_dir) || return 1
  printf '%s/jobs\n' "$dir"
}

# Who is asking for a matrix, as one word: the session id in EDIT_SESSION when the
# caller's environment sets one, else the login name.
matrix_requester() {
  if [[ -n "${EDIT_SESSION:-}" ]]; then
    printf 'session:%s\n' "$EDIT_SESSION"
  else
    printf 'user:%s\n' "${USER:-unknown}"
  fi
}

# matrix_queue_add <commit> <selector> <requester>
matrix_queue_add() {
  local dir
  dir=$(matrix_state_dir) || return 1
  printf '%s %s %s\n' "$1" "$2" "$3" >>"$dir/queue"
}

# Prints the queued requests (and empties the queue) as one `<commit> <selector>
# <requesters>`: the commit every queued baseline descends from, `:all` where the
# selectors differ, and the requesters comma-joined.  Prints nothing when the queue is
# empty.
matrix_queue_take() {
  local dir taken bases sels base sel who
  dir=$(matrix_state_dir) || return 0
  [[ -s "$dir/queue" ]] || return 0
  taken="$dir/queue.$$"
  mv "$dir/queue" "$taken" 2>/dev/null || return 0
  bases=$(cut -d' ' -f1 "$taken" | sort -u)
  sels=$(cut -d' ' -f2 "$taken" | sort -u)
  who=$(cut -d' ' -f3 "$taken" | grep -v '^$' | sort -u | paste -sd, -)
  rm -f "$taken"
  # word-split on purpose: one commit per word
  # shellcheck disable=SC2086
  if [[ $(printf '%s\n' "$bases" | wc -l) -gt 1 ]]; then
    base=$(git merge-base --octopus $bases 2>/dev/null) || base=$(printf '%s\n' "$bases" | head -1)
  else
    base=$bases
  fi
  if [[ $(printf '%s\n' "$sels" | wc -l) -gt 1 ]]; then sel=":all"; else sel=$sels; fi
  printf '%s %s %s\n' "$base" "$sel" "${who:-unknown}"
}

# ---- the configurations a yield stopped ---------------------------------------------------
#
# `yield-stopped` lists, one per line, the configurations an `--owed` run left without a
# verdict when it yielded to a queued request.  The next `--owed` run that owes one launches
# it first and does not yield before it has a verdict, so the slowest configuration is not
# stopped by every yield in turn.  Only the lock holder writes the file.

# matrix_yield_stopped_add <config>…
matrix_yield_stopped_add() {
  local dir
  dir=$(matrix_state_dir) || return 1
  (( $# > 0 )) || return 0
  printf '%s\n' "$@" >>"$dir/yield-stopped"
}

# The listed configurations, one per line, each once.
matrix_yield_stopped() {
  local dir
  dir=$(matrix_state_dir) || return 0
  [[ -s "$dir/yield-stopped" ]] || return 0
  sort -u "$dir/yield-stopped"
}

# matrix_yield_stopped_take <config>… removes those configurations from the list: the run
# holding the lock owes each of them a verdict now.
matrix_yield_stopped_take() {
  local dir rest
  dir=$(matrix_state_dir) || return 0
  [[ -s "$dir/yield-stopped" ]] || return 0
  rest="$dir/yield-stopped.$$"
  sort -u "$dir/yield-stopped" | grep -vxF -f <(printf '%s\n' "$@") >|"$rest"
  mv "$rest" "$dir/yield-stopped"
}

# ---- the cooldown after a red matrix ------------------------------------------------------
#
# A red matrix writes `red`: `<epoch> <run dir>`.  For MATRIX_RED_COOLDOWN seconds after
# it (1800 by default) a new matrix, started or queued, is refused, because a re-run that
# soon repeats the same failures.  A green matrix removes the file.

matrix_red_mark() {
  local dir
  dir=$(matrix_state_dir) || return 0
  printf '%s %s\n' "$(date '+%s')" "$1" >|"$dir/red"
}

matrix_red_clear() {
  local dir
  dir=$(matrix_state_dir) || return 0
  rm -f "$dir/red"
}

# The `red` line while the cooldown lasts, else nothing.
matrix_red_recent() {
  local dir line cool="${MATRIX_RED_COOLDOWN:-1800}"
  [[ "$cool" =~ ^[0-9]+$ ]] || cool=1800
  (( cool > 0 )) || return 0
  dir=$(matrix_state_dir) || return 0
  line=$(cat "$dir/red" 2>/dev/null) || return 0
  (( $(date '+%s') - ${line%% *} < cool )) && printf '%s\n' "$line"
  return 0
}

# ---- one perf run at a time, and a cap on concurrent sharded suites -----------------------
#
# `lein perf` and `lein perf-ab` time code, and a second perf run beside the first loads the
# cores both are timing: each reads the other's JVMs as its own regression, and the suites
# other sessions run beside them drop to one slot. So every perf run, `--only` and `lein gate`'s
# perf stage included, from any clone or worktree on the box, holds `perf-lock` in
# `box_state_dir` while it measures.
#
# `lein test-parallel` sizes its shard count from the vaelii JVMs already running
# (`default_slots`, floored at `TEST_MIN_JOBS`), so seven suites started together would each
# start that floor's shards. So a sharded suite holds one of GATE_MAX_CONCURRENT gate slots
# (2 by default, `0` for no cap), `gate-lock.1` … `gate-lock.<n>` in `box_state_dir`, shared
# by every clone and worktree on the box. `lein gate` takes its slot for its test stage alone
# and exports GATE_SLOT, so the `lein test-parallel` it runs takes none of its own; a
# `lein test-parallel` run outside `lein gate` takes one for its whole run. The shards start after
# the take, so their count reads the box as it is at admission. Lint runs while `lein gate`
# waits, and `lein gate` releases its slot before its perf stage takes `perf-lock`, so no
# process holds both.
#
# A run that finds every slot of its lock held waits, naming the holders once a minute;
# `PERF_NO_WAIT=1` and `GATE_NO_WAIT=1` exit 75 instead.
#
#   perf-lock, gate-lock.<i>  `<pid> <revision> <epoch> <requester> <command…> (in <checkout>)`
#                             of the holder

# lock_holder <lock file> <command regex> prints the lock's line when its pid is alive and
# that pid's command matches the regex, else nothing. A lock whose pid is gone, or runs
# another command, is stale and is removed.
lock_holder() {
  local line pid
  line=$(cat "$1" 2>/dev/null) || return 0
  pid=${line%% *}
  if [[ -n "$pid" ]] && ps -o command= -p "$pid" 2>/dev/null | grep -qE "$2"; then
    printf '%s\n' "$line"
  else
    lock_break_stale "$1" "$line"
  fi
}

# lock_duration <seconds> prints `4m12s`, or `12s` under a minute.
lock_duration() {
  if (( $1 >= 60 )); then printf '%dm%02ds\n' $(($1 / 60)) $(($1 % 60)); else printf '%ds\n' "$1"; fi
}

# lock_describe <line> prints a lock line as `pid <pid> at <revision>, <requester>, held
# <age>: <command>`.
lock_describe() {
  local pid rev epoch who cmd
  read -r pid rev epoch who cmd <<<"$1"
  [[ "$epoch" =~ ^[0-9]+$ ]] || epoch=$(date '+%s')
  printf 'pid %s at %s, %s, held %s: %s\n' "$pid" "$rev" "$who" \
    "$(lock_duration $(( $(date '+%s') - epoch )))" "$cmd"
}

# lock_take <dir fn> <name> <slots> <command regex> <no-wait variable> <noun> <command…>
# takes one slot of a lock for this shell, in the directory <dir fn> prints: the file
# `<name>` when <slots> is 1, else the first free of `<name>.1` … `<name>.<slots>`. It
# sets LOCK_FILE to the file taken and LOCK_WAITED to the seconds it waited. While every
# slot is held it waits, naming the holders once a minute, or returns 75 when the variable
# named <no-wait variable> is non-empty. Each attempt is one `lock_create` per slot.
lock_take() {
  local dirfn="$1" name="$2" n="$3" re="$4" nowait="$5" noun="$6"; shift 6
  local dir line f i held state waited=0 files=()
  LOCK_FILE=''; LOCK_WAITED=0
  dir=$("$dirfn") || return 0
  if (( n == 1 )); then files=("$dir/$name"); state="the $noun is held"; else
    for ((i = 1; i <= n; i++)); do files+=("$dir/$name.$i"); done
    state="all $n ${noun}s are held"
  fi
  local top; top=$(git rev-parse --show-toplevel 2>/dev/null) || top=$PWD
  while :; do
    line="$$ $(git rev-parse --short HEAD 2>/dev/null) $(date '+%s') $(matrix_requester) $* (in ${top/#"$HOME"/\~})"
    for f in "${files[@]}"; do
      lock_holder "$f" "$re" >/dev/null
      if lock_create "$f" "$line"; then
        LOCK_FILE=$f; LOCK_WAITED=$waited
        return 0
      fi
    done
    held=$(for f in "${files[@]}"; do lock_holder "$f" "$re"; done)
    if [[ -n "$held" ]]; then
      if [[ -n "${!nowait:-}" ]]; then
        printf '%s:\n' "$state" >&2
        while IFS= read -r f; do printf '  %s\n' "$(lock_describe "$f")" >&2; done <<<"$held"
        printf '  %s is set, so this exits 75; unset it to wait (scripts/lib/slots.sh).\n' "$nowait" >&2
        return 75
      fi
      if (( waited % 60 == 0 )); then
        printf 'waiting (%s so far): %s:\n' "$(lock_duration "$waited")" "$state" >&2
        while IFS= read -r f; do printf '  %s\n' "$(lock_describe "$f")" >&2; done <<<"$held"
      fi
    fi
    # backgrounded and waited on, so a trapped INT or TERM runs at once
    sleep 5 & wait $! 2>/dev/null   # 2>/dev/null: the job-done notice under set -m
    waited=$((waited + 5))
  done
}

# lock_release <lock file> removes the file when this shell's pid holds it.
lock_release() {
  local line
  [[ -n "$1" ]] || return 0
  line=$(cat "$1" 2>/dev/null) || return 0
  [[ "${line%% *}" == "$$" ]] && rm -f "$1"
  return 0
}

# perf_lock_take <command…> takes the perf lock for this shell, waiting while another perf
# run holds it (or exiting 75 under PERF_NO_WAIT=1), and releases it when the shell exits.
# A holder that is no longer perf.sh or perf-ab.sh is stale.
perf_lock_take() {
  lock_take box_state_dir perf-lock 1 'perf(-ab)?\.sh' PERF_NO_WAIT 'perf lock' "$@" || exit $?
  [[ -n "$LOCK_FILE" ]] && trap perf_lock_release EXIT
  return 0
}

perf_lock_release() {
  local dir
  dir=$(box_state_dir) || return 0
  lock_release "$dir/perf-lock"
}

# gate_slot_take <command…> takes a gate slot for this shell and sets GATE_SLOT to its file
# and GATE_SLOT_WAITED to the seconds waited; returns 75 under GATE_NO_WAIT=1 when none is
# free. GATE_MAX_CONCURRENT=0 takes nothing. A holder that is no longer gate.sh or
# test-parallel.sh is stale. The caller releases with gate_slot_release, on its EXIT trap too.
gate_slot_take() {
  local n="${GATE_MAX_CONCURRENT:-2}" rc=0
  [[ "$n" =~ ^[0-9]+$ ]] || n=2
  GATE_SLOT=''; GATE_SLOT_WAITED=0
  (( n > 0 )) || return 0
  lock_take box_state_dir gate-lock "$n" 'gate\.sh|test-parallel\.sh' GATE_NO_WAIT 'gate slot' "$@" || rc=$?
  GATE_SLOT=$LOCK_FILE
  # shellcheck disable=SC2034  # gate.sh reads it
  GATE_SLOT_WAITED=$LOCK_WAITED
  return "$rc"
}

gate_slot_release() {
  lock_release "${GATE_SLOT:-}"
  GATE_SLOT=''
}
