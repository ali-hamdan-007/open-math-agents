#!/usr/bin/env bash
set -euo pipefail
work=$(cd "$(dirname "$0")" && pwd)
ramsey=$(cd "$work/../.." && pwd)
build=${1:-"$ramsey/focused"}
mkdir -p "$build"
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
if [[ -n ${LEAN_BIN:-} ]]; then
    lean_cmd=("$LEAN_BIN")
else
    lean_cmd=("$ramsey/lean-focus.sh")
    if [[ "$build" != "$ramsey/focused" ]]; then
        printf 'Set LEAN_BIN for a custom build directory.\n' >&2
        exit 2
    fi
fi
cd "$work"
for source in Green154EdgeCore.lean Green154EdgeChunk*.lean Green154EdgeSeed.lean; do
    printf 'Checking %s\n' "$source"
    "${lean_cmd[@]}" -o "$build/${source%.lean}.olean" "$source"
done
