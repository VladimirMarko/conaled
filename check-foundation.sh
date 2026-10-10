#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
export LEAN_PATH=".${LEAN_PATH:+:$LEAN_PATH}"
"$LEAN" --version
for module in Squares Compiler SquareCompiler FirstOrder Dependent Verification; do
  printf 'Checking %s.lean\n' "$module"
  "$LEAN" -o "$module.olean" "$module.lean"
done
