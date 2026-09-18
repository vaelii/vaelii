#!/usr/bin/env bash
# scripts/lib/suite-configs.sh — the fifteen configurations the whole suite can be run
# in, and the environment that selects each.  One table, three readers.
#
# Two axes, and they are independent (which is why they are two lists and not a
# cross-product):
#
#   BACKENDS — where the sentexes live.  Eight legal record×index pairs, spelled
#              `<records>-<index>`, plus `overlay`, which is not a ninth pair but the
#              fork decorator over an empty base (docs/overlay.md).
#   SWEEPS   — which implementation answers, storage held at the default.  Six
#              components the engine otherwise picks for itself.
#
# `test-backends.sh` runs the first list, `test-sweeps.sh` the second, and
# `test-matrix.sh` runs both at once — so the roster lives here rather than in the
# script that happened to need it first.  Adding a backend or a sweep is an edit to this
# file and to nothing else.
#
# Three more readings of the same table live here for the same reason: the GROUP words a
# runner takes in place of a list of names (`config_group`), the ROUTINE roster a bare
# run uses against the full fifteen (`ROUTINE_SKIP`), and what a changed FILE owes
# (`config_owed_for_path`), which is how a change runs the configurations that could
# disagree about it instead of all of them.
#
# Sourced, never executed:
#   . scripts/lib/suite-configs.sh
#
# Read by the sourcing script and by nothing here — SC2034 cannot see across a `.`.
# shellcheck disable=SC2034

# In the order they run: the three RAM-record pairs first (fast, no files), then the
# five durable-record ones — the rebuilt indexes, then the mapped image, then the durable
# one, so the runs that write least go first — then the decorator.
ALL_BACKENDS=(memory memory-dense memory-columnar
              disk-memory disk-dense disk-columnar disk-snapshot disk-log
              overlay)

# Cheapest first, so a matrix that is going to fail on the retrieval switch says so
# before spending twenty minutes on the node engine.  Kept as parallel arrays rather
# than one associative array: bash 3.2 is what macOS ships, and `declare -A` is bash 4.
ALL_SWEEPS=(tms-reference rete hier-off plan-off query-engine tactician)
SWEEP_ENVS=(
  "VAELII_TEST_TMS=reference"
  "VAELII_RETE=1"
  "VAELII_HIER=0"
  "VAELII_PLAN=0"
  "VAELII_QUERY_ENGINE=inference"
  "VAELII_QUERY_ENGINE=inference VAELII_QUERY_STRATEGY=breadth-first"
)

# ---- the ROUTINE roster ---------------------------------------------------
#
# What a bare `test-matrix.sh` runs, against the fifteen `full` runs.  Two
# configurations sit it out, and both are the same one claim written a third time.
#
# `disk-memory`, `disk-dense` and `disk-columnar` are durable records under a DERIVED
# index.  Each index half already runs under RAM records in the list above, the records
# half runs under `disk-log`, and what the pairing adds beyond those is the `reindex` on
# open — the same rebuild whichever derived index it fills.  `mixed_backend_test` holds
# that protocol in an ordinary `lein test` and `backend_parity_test` runs its scripted
# session on all three, so one of them stands for the composition here and the other two
# are the cross-product for its own sake.
#
# They are also three of the five longest runs, at the head of a longest-first schedule,
# which is what makes the difference readable rather than notional: the routine roster
# finishes in about two thirds of the full one's wall clock.
#
# `full` is what a release runs, and what to run when the change is to the record/index
# protocol itself.  Nothing is DROPPED here — a skipped configuration is named on the
# console every time, because a roster that quietly shrank is a matrix that means less
# than the word does.
ROUTINE_SKIP=(disk-dense disk-columnar)

# The GROUP words a runner takes in place of a list of configuration names.  One line
# per group, so a caller can `while read`.  Non-zero for a word that is not a group,
# which is how a runner tells a group from a configuration without a second table.
config_group() {
  local want="$1" c s
  case "$want" in
    backends) printf '%s\n' "${ALL_BACKENDS[@]}"; return 0 ;;
    sweeps)   printf '%s\n' "${ALL_SWEEPS[@]}"; return 0 ;;
    full)     printf '%s\n' "${ALL_BACKENDS[@]}" "${ALL_SWEEPS[@]}"; return 0 ;;
    routine)
      for c in "${ALL_BACKENDS[@]}" "${ALL_SWEEPS[@]}"; do
        for s in "${ROUTINE_SKIP[@]}"; do [[ "$c" == "$s" ]] && continue 2; done
        printf '%s\n' "$c"
      done
      return 0 ;;
  esac
  return 1
}

# Expand any GROUP words among the arguments and drop repeats, printing one
# configuration per line in the ROSTER's own order rather than the caller's:
# `backends hier-off` and `hier-off backends` name the same set, a matrix reorders by
# measured seconds anyway, and `config_owed_for_path` emits group words and
# configuration names in the same breath.  Anything in neither table is dropped, so a
# caller validates names with `config_kind` first if it wants a refusal.
expand_configs() {
  local want g out=() c seen
  for want in "$@"; do
    if g=$(config_group "$want"); then
      while IFS= read -r c; do out+=("$c"); done <<< "$g"
    else
      out+=("$want")
    fi
  done
  (( ${#out[@]} )) || return 0
  for c in "${ALL_BACKENDS[@]}" "${ALL_SWEEPS[@]}"; do
    for seen in "${out[@]}"; do
      [[ "$c" == "$seen" ]] && { printf '%s\n' "$c"; break; }
    done
  done
}

# ---- the launch order ------------------------------------------------------
#
# Fisher-Yates over the global array SHUF, in place and IN THIS SHELL — not a function
# that echoes its result through `< <(…)`.  Process substitution forks a subshell, and
# bash reseeds `$RANDOM` in a subshell from the pid, so a seeded sequence produced there
# is NOT the seed's sequence, and the seed a run reports would name an order it never
# produced.  `$RANDOM` is a builtin; `shuf` is GNU coreutils, which macOS ships no more
# than it ships bash 4's namerefs (3.2).
#
# The caller seeds `RANDOM` itself and prints the seed it used, so a run's order can be
# replayed by giving that seed back.  `test-shuffle.sh` and `test-matrix.sh` both shuffle
# their roster this way, and both accept the seed in an environment variable.
shuffle_inplace() {
  local i j tmp n=${#SHUF[@]}
  for (( i = n - 1; i > 0; i-- )); do
    j=$(( RANDOM % (i + 1) ))
    tmp="${SHUF[i]}"; SHUF[i]="${SHUF[j]}"; SHUF[j]="$tmp"
  done
}

# ---- what a changed FILE owes ----------------------------------------------
#
# The matrix's claim is that the suite is failing-set-identical across configurations,
# so what a change owes is decided by which configurations could disagree ABOUT IT.
# Three answers, and the third is the one that keeps this honest:
#
#   SWAPPED     the file is one half of a configuration — a record store, an index, a
#               decorator, a matcher, a TMS, an executor, a planner.  The
#               configurations that swap it are named exactly.
#   SHARED      the file is what the configurations disagree THROUGH: retrieval, the
#               index logic every backend runs, the belief and settle readers a
#               backend's answers reach a caller by.  Owes `routine`.
#   NOTHING     `lein gate` runs this same suite on `memory`, and a file no
#               configuration swaps or reads through cannot answer differently under
#               one.  Prints nothing.
#
# **This is a floor, not a proof.**  A configuration disagreeing about a third-bucket
# file is possible — it is a bug in one of the first two, reached from an odd angle —
# so a change whose blast radius you cannot see owes `routine`, and saying so costs one
# argument.  What the floor buys is that the common case stops running fifteen suites
# to learn something thirteen of them were never asked.
config_owed_for_path() {
  case "$1" in
    # --- swapped: the file IS half of a configuration ---
    # one per representation this directory holds a half of: the durable log index,
    # the record store every durable pairing shares (`disk-memory` is the cheapest
    # that reindexes over it), and the mapped image, whose writer, stamp and cadence
    # live here too — so `index_snapshot.clj` owes the configuration it implements
    src/vaelii/impl/disk/*)              printf 'disk-log disk-memory disk-snapshot' ;;
    src/vaelii/impl/overlay/*)           printf 'overlay' ;;
    src/vaelii/impl/columnar.clj)        printf 'memory-columnar disk-columnar' ;;
    src/vaelii/impl/dense_kv.clj)        printf 'memory-dense disk-dense' ;;
    # the roots backend is shared by BOTH dense index families, so either alone would
    # leave half of what the file answers unrun
    src/vaelii/impl/dense_roots.clj)     printf 'memory-dense memory-columnar' ;;
    src/vaelii/impl/jtms.clj \
    |src/vaelii/impl/dense_jtms.clj \
    |src/vaelii/impl/jtms_protocol.clj)  printf 'tms-reference' ;;
    src/vaelii/impl/rete.clj)            printf 'rete' ;;
    src/vaelii/impl/inference.clj \
    |src/vaelii/impl/tactics.clj)        printf 'query-engine tactician' ;;
    # the ranking is read by BOTH executors — `tactics` sums `explain`'s estimates for
    # node selection — so a change here owes the node engine's two as well as its own
    src/vaelii/impl/plan.clj)            printf 'plan-off query-engine tactician' ;;
    # the chainer is the matcher's reference half, and the join it leads is read
    # through the index — so it owes the alternative matcher and the backends both
    src/vaelii/impl/chain.clj)           printf 'rete backends' ;;
    # retrieval is the swept half AND what every backend is read through
    src/vaelii/impl/resolution.clj)      printf 'hier-off backends' ;;
    # --- swapped on both store axes at once: every backend ---
    src/vaelii/impl/memory.clj \
    |src/vaelii/impl/kv.clj \
    |src/vaelii/impl/kb.clj \
    |src/vaelii/impl/protocols.clj \
    |src/vaelii/impl/capabilities.clj \
    |src/vaelii/impl/reads.clj \
    |src/vaelii/impl/sentex.clj)         printf 'backends' ;;
    # --- shared: what the configurations disagree through ---
    src/vaelii/impl/checks.clj \
    |src/vaelii/impl/settle.clj \
    |src/vaelii/impl/taxonomy.clj \
    |src/vaelii/impl/inherit.clj \
    |src/vaelii/impl/rewrite.clj \
    |src/vaelii/impl/caches.clj \
    |src/vaelii/impl/literal_cache.clj)  printf 'routine' ;;
    # the roster itself, and the harness that installs the switches: a change here
    # changes what every other run MEANS, so it owes all of them
    scripts/lib/suite-configs.sh \
    |test/vaelii/test_util.clj)          printf 'full' ;;
  esac
}

# backend | sweep, or nothing and a non-zero status for a name in neither list.  A
# caller checks this before running anything: an unknown name would otherwise run the
# suite with no switch set at all and report a clean pass for a configuration nothing
# ran, which is the exact failure the switches' own domains refuse.
config_kind() {
  local want="$1" b s
  for b in "${ALL_BACKENDS[@]}"; do [[ "$b" == "$want" ]] && { printf 'backend'; return 0; }; done
  for s in "${ALL_SWEEPS[@]}"; do [[ "$s" == "$want" ]] && { printf 'sweep'; return 0; }; done
  return 1
}

# The environment assignments that select a configuration, space-separated — a
# backend's one, or a sweep's one or two.  Never the disk directory: which directory a
# durable run writes to is the caller's to name, since the caller owns the run's output
# tree and two concurrent matrices must not share one.
config_env() {
  local want="$1" i
  for i in "${!ALL_BACKENDS[@]}"; do
    [[ "${ALL_BACKENDS[$i]}" == "$want" ]] && { printf 'VAELII_TEST_BACKEND=%s' "$want"; return 0; }
  done
  for i in "${!ALL_SWEEPS[@]}"; do
    [[ "${ALL_SWEEPS[$i]}" == "$want" ]] && { printf '%s' "${SWEEP_ENVS[$i]}"; return 0; }
  done
  return 1
}

# Does this configuration write a durable store?  The RECORD half is the name's prefix,
# and a RAM-only run reads no directory at all — handing it one would only put a `-D` on
# its command line that means nothing.
config_wants_disk() {
  case "$1" in
    disk-*) return 0 ;;
    *) return 1 ;;
  esac
}

# ---- how many assertions a configuration is EXPECTED to run short ----------
#
# The suite is failing-set-identical across all fifteen, and the assertion COUNT moves
# only where a test says why.  `test-backends.sh` and `test-sweeps.sh` have both stated
# that for as long as they have existed; what follows is the same claim, checked.  Any
# other difference is a run that skipped something the others ran — a namespace that
# failed to load, a `deftest` that stood aside without saying so, a switch that turned a
# gate off — and every one of those is indistinguishable from a green run.
#
# No configuration stands aside, and the table is empty by design.  Where an assertion
# pins an artifact of one implementation — the columnar trie's absent `:fan`
# (`profile_test/the-fan-tally-counts-what-the-walk-touched`, docs/profile.md), the node
# engine's one-solution-per-answer `prove` (the `tu/query-engine-override` sites in
# `backward_test`, `query_test` and `inference_test`, docs/inference.md) — the test
# asserts that configuration's own expectation rather than skipping, so every
# configuration runs the same number of assertions and any shortfall is a skip.
#
# The function stays so the runners have one place to read an expected delta from.  A
# configuration that has to stand aside would be recorded here with its reason, in the
# commit that adds it — and the point of the empty table is that none has.
config_expected_delta() {
  case "$1" in
    *) printf '0' ;;
  esac
}

# Check `name:assertions` pairs against that table.  Prints one line per configuration
# whose shortfall is not the expected one and returns 1; silent and 0 when they all hold.
#
# The baseline is the highest `count + expected`, not simply the highest count, and that
# is what makes a SUBSET checkable: `./scripts/test-sweeps.sh query-engine tactician`
# runs two configurations that are both expected to be 8 short, and against a bare
# maximum each would look like the full count and the other would look 0 short.
# Reconstructing the full count from every run and taking the highest gives the same
# baseline whichever configurations were asked for.
assertion_deltas_ok() {
  local pair name count baseline=0 full actual expected bad=0
  for pair in "$@"; do
    count="${pair##*:}"
    case "$count" in ''|*[!0-9]*) continue ;; esac
    full=$(( count + $(config_expected_delta "${pair%%:*}") ))
    (( full > baseline )) && baseline=$full
  done
  (( baseline == 0 )) && return 0            # nothing finished; nothing to compare
  for pair in "$@"; do
    name="${pair%%:*}"; count="${pair##*:}"
    case "$count" in ''|*[!0-9]*) continue ;; esac
    expected=$(config_expected_delta "$name")
    actual=$(( baseline - count ))
    if (( actual != expected )); then
      printf '  %-16s ran %s assertions — %s short of %s, where the table expects %s\n' \
        "$name" "$count" "$actual" "$baseline" "$expected"
      bad=1
    fi
  done
  return $bad
}
