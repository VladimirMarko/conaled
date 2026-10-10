#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}
if [ -n "${LEAN_PATH:-}" ]; then
  export LEAN_PATH=".:$LEAN_PATH"
else
  export LEAN_PATH="."
fi
"$LEAN" --version
for module in Squares Compiler SquareCompiler FirstOrder Dependent Verification; do
  printf 'Checking %s.lean\n' "$module"
  "$LEAN" -o "$module.olean" "$module.lean"
done
