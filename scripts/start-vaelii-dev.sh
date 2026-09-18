#!/usr/bin/env bash
# scripts/start-vaelii-dev.sh [KB-DIR] — the browser for development: an nREPL, hot
# reload of src, and the sampling profiler's UI, all bound to the loopback interface.
#
#   browser   http://127.0.0.1:${VAELII_WEB_PORT:-3000}
#   profiler  http://127.0.0.1:${VAELII_PROFILER_PORT:-8080}
#   nREPL     127.0.0.1, on LEIN_REPL_PORT or a free port, written to .nrepl-port
#
# This is `lein browser` run headless, with VAELII_DEV and VAELII_PROFILER set. The
# browser opens on the starter ontology and loads KB-DIR as a catalog job with belief
# recovered (VAELII_KB_DIR, docs/web.md); the KB becomes the active one when the load
# finishes, and /kbs shows its progress until then. KB-DIR defaults to
# checkouts/kb beside this checkout. The heap is VAELII_HEAP, default 40g
# (scripts/lib/start.sh).
#
# An edit under src shows on the next page refresh, and a KB loaded before it keeps
# answering. This script is the only thing that turns hot reload on (VAELII_DEV=1 below);
# `lein browser` alone and a served process never reload. An edit inside a protocol,
# record or type definition, or to a held namespace, takes a restart, and every page names
# it until then (docs/web.md).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/start.sh
. "$ROOT/scripts/lib/start.sh"

KB="$(start_kb_dir "${1:-}")" || exit 1
cd "$ROOT"

export VAELII_KB_DIR="$KB" VAELII_DEV=1 VAELII_PROFILER=1
JVM_OPTS="${JVM_OPTS:-} $(start_jvm_opts)"
export JVM_OPTS

echo "vaelii dev: browser :${VAELII_WEB_PORT:-3000}, profiler :${VAELII_PROFILER_PORT:-8080}, loading $KB" >&2
exec lein browser :headless
