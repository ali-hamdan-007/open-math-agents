#!/usr/bin/env bash
set -eu
base=/tmp/ali189-active.CE0Lol
test -e "$base/LIVE" && test ! -e "$base/PAUSE" && test ! -e "$base/HALT" || exit 3
source_dir="$(cd "$(dirname "$0")" && pwd)"
fresh="$(mktemp -d "$source_dir/import-XXXXXX")"
cp "$source_dir/Graph189CompletionAudit.lean" "$fresh/"
sed 's|export LEAN_PATH="$d:|export LEAN_PATH="$d:$p/global/moderate:|' "$source_dir/check.sh" > "$fresh/check.sh"
cd "$fresh"
bash check.sh Graph189CompletionAudit
