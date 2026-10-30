#!/usr/bin/env bash
# Diagnostic fixture for #222. Success means the recorded failure was reproduced.
# Run with: direnv exec . bash scripts/repro-lake-output-mismatch.sh
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
fixture_dir=$(mktemp -d "${TMPDIR:-/tmp}/conaled-lake-output-mismatch.XXXXXXXX")
trap 'rm -rf -- "$fixture_dir"' EXIT
cp "$repo_root/lean-toolchain" "$fixture_dir/lean-toolchain"
cd "$fixture_dir"
cat > lakefile.toml <<'TOML'
name = "cacheRepro"
version = "0.1.0"
defaultTargets = ["Repro"]
[[lean_lib]]
name = "Repro"
roots = ["Repro"]
globs = ["Repro", "Leaf"]
TOML
cat > Leaf.lean <<'LEAN'
namespace Leaf
def oldValue : Nat := 1
end Leaf
LEAN
cat > Repro.lean <<'LEAN'
import Leaf
#check Leaf.oldValue
LEAN
lake build > initial.log 2>&1 || { cat initial.log; exit 1; }
cp .lake/build/lib/lean/Leaf.olean old.olean
cp .lake/build/lib/lean/Leaf.olean.hash old.hash
cat > Leaf.lean <<'LEAN'
namespace Leaf
def oldValue : Nat := 1
def newValue : Nat := 2
end Leaf
LEAN
lake build > updated.log 2>&1 || { cat updated.log; exit 1; }
cp .lake/build/lib/lean/Leaf.trace updated.trace
cat > Repro.lean <<'LEAN'
import Leaf
#check Leaf.newValue
LEAN

# Each probe starts from the same intentionally inconsistent artifact set.
# The source and trace describe the new module; the binary describes the old one.
expect_missing_declaration() {
  local mode=$1
  cp old.olean .lake/build/lib/lean/Leaf.olean
  cp old.hash .lake/build/lib/lean/Leaf.olean.hash
  cp updated.trace .lake/build/lib/lean/Leaf.trace
  local -a options=()
  case "$mode" in
    ordinary) ;;
    no-sidecar) rm .lake/build/lib/lean/Leaf.olean.hash ;;
    rehash) options=(--rehash) ;;
    no-cache) options=(--no-cache) ;;
  esac
  if lake "${options[@]}" build > probe.log 2>&1; then
    echo "Unexpected success for $mode: investigate whether Lake now rejects or repairs this state."
    cat probe.log
    exit 1
  fi
  if ! rg -q 'Unknown identifier.*Leaf.newValue' probe.log; then
    echo "Unexpected failure for $mode (not the recorded symptom):"
    cat probe.log
    exit 1
  fi
  echo "$mode: reproduced missing Leaf.newValue"
}
expect_missing_declaration ordinary
expect_missing_declaration ordinary
expect_missing_declaration no-sidecar
expect_missing_declaration rehash
expect_missing_declaration no-cache

# Invalidate the input trace while leaving the old binary in place.
rm .lake/build/lib/lean/Leaf.trace
lake build > recovered.log 2>&1 || { cat recovered.log; exit 1; }
rg -q 'Leaf.newValue : Nat' recovered.log || { cat recovered.log; exit 1; }
echo 'trace removed: rebuilt successfully and exposed Leaf.newValue'
echo 'PASS: inconsistent-output reuse reproduced; trace invalidation recovered it.'
