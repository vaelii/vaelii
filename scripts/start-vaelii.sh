#!/usr/bin/env bash
# scripts/start-vaelii.sh [KB-DIR] [BROWSER-FLAGS...] — the browser alone: no nREPL, no
# hot reload, no profiler. BROWSER-FLAGS are `vaelii.web`'s own (--port N, --listen
# ADDR); a --listen off the loopback interface requires VAELII_API_TOKEN (docs/web.md).
#
# The browser opens on the starter ontology and loads KB-DIR as a catalog job with belief
# recovered (VAELII_KB_DIR, docs/web.md); the KB becomes the active one when the load
# finishes. KB-DIR defaults to checkouts/kb beside this checkout, and a first
# argument that starts with `--` is a flag, not a KB-DIR. The heap is VAELII_HEAP,
# default 40g (scripts/lib/start.sh).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/start.sh
. "$ROOT/scripts/lib/start.sh"

kb_arg=""
if [ $# -gt 0 ] && [ "${1#--}" = "$1" ]; then
  kb_arg="$1"
  shift
fi
KB="$(start_kb_dir "$kb_arg")" || exit 1
cd "$ROOT"

export VAELII_KB_DIR="$KB"
JVM_OPTS="${JVM_OPTS:-} $(start_jvm_opts)"
export JVM_OPTS

echo "vaelii: browser, loading $KB" >&2
exec lein run -m vaelii.web "$@"
