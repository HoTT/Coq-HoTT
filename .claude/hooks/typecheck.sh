#!/usr/bin/env bash
# PostToolUse hook: after an edit to a .v file, typecheck it with bin/build
# and feed any errors back to Claude (exit code 2 + stderr).

set -uo pipefail

ROOT="${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

file="$(jq -r '.tool_input.file_path // .tool_response.filePath // empty')"
case "$file" in
  *.v) ;;
  *) exit 0 ;;
esac
case "$file" in
  /*) ;;
  *) file="$ROOT/$file" ;;
esac
case "$file" in
  "$ROOT"/*) ;;
  *) exit 0 ;;  # outside the repository, e.g. a scratch file
esac
[ -f "$file" ] || exit 0

if out="$("$ROOT/bin/build" "$file" 2>&1)"; then
  exit 0
fi

{
  echo "Typechecking ${file#"$ROOT"/} with bin/build failed:"
  # Strip ANSI colour codes and keep the output to a reasonable size.
  printf '%s\n' "$out" | sed 's/\x1b\[[0-9;]*m//g' | tail -n 80
} >&2
exit 2
