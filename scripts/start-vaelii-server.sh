#!/usr/bin/env bash
# scripts/start-vaelii-server.sh [KB-DIR] [PORT] [--listen ADDR] — the daemon
# (`vaelii.serve`) over KB-DIR, run for serving rather than for development:
#
#   * no development profile and no user profile (`with-profile -user,-dev`), so no
#     nREPL, no tools.namespace reload and no profiler agent are on the classpath;
#   * a Leiningen trampoline, so the daemon's JVM is the only one left running;
#   * every request carries a bearer token. The token is VAELII_API_TOKEN, else the one
#     in ~/.vaelii/api-token, which this script writes the first time (32 random bytes as
#     hex, mode 600). A client presents it as `Authorization: Bearer <token>`.
#
# The daemon binds the loopback interface unless --listen names an address; a
# non-loopback --listen also drops the Host allowlist unless VAELII_ALLOWED_HOSTS names
# one (docs/operations.md). PORT defaults to 4200. KB-DIR defaults to
# checkouts/kb beside this checkout; the daemon opens it under the backend its
# files were written by, and recovers belief, installing the store's reasoning image when
# the image matches this build. The heap is VAELII_HEAP, default 40g
# (scripts/lib/start.sh).
#
# SLF4J prints one "no providers" warning at startup: the no-op provider ships in the
# :dev and :uberjar profiles, and this run drops :dev.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/start.sh
. "$ROOT/scripts/lib/start.sh"

kb_arg=""
if [ $# -gt 0 ] && [ -d "$1" ]; then
  kb_arg="$1"
  shift
fi
port=4200
if [ $# -gt 0 ] && [[ "$1" =~ ^[0-9]+$ ]]; then
  port="$1"
  shift
fi
KB="$(start_kb_dir "$kb_arg")" || exit 1
cd "$ROOT"

if [ -z "${VAELII_API_TOKEN:-}" ]; then
  token_file="$HOME/.vaelii/api-token"
  if [ ! -s "$token_file" ]; then
    mkdir -p "$HOME/.vaelii"
    (umask 077 && openssl rand -hex 32 >| "$token_file")
    echo "wrote a new API token to $token_file" >&2
  fi
  VAELII_API_TOKEN="$(cat "$token_file")"
  export VAELII_API_TOKEN
fi

JVM_OPTS="${JVM_OPTS:-} $(start_jvm_opts)"
export JVM_OPTS

echo "vaelii daemon: port $port, opening $KB" >&2
exec lein with-profile -user,-dev trampoline run -m vaelii.serve "$port" "$KB" "$@"
