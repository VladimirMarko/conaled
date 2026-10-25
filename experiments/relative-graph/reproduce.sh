#!/usr/bin/env bash
# Run from the conaled checkout: direnv exec . bash experiments/relative-graph/reproduce.sh
set -euo pipefail
# The release pin is an ancestor of the selected newer pin; see pin-alignment.md.
conleche_pin=8e166ca53cd1f864b63c13cc1d326d38316d00ea
release_pin=67f04630d88718e81aa4d07ab64501f68f105398
case "${1:-}" in
  "") include_lean4lean=true ;;
  --conleche-only) include_lean4lean=false ;;
  *) printf 'Usage: %s [--conleche-only]\n' "$0" >&2; exit 2 ;;
esac
artifact_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
run_dir=$(mktemp -d "${TMPDIR:-/tmp}/conaled-relative-graph.XXXXXX")
printf 'Isolated results: %s\n' "$run_dir"

git clone --quiet https://github.com/leanprover/con-leche "$run_dir/con-leche"
git -C "$run_dir/con-leche" checkout --quiet --detach "$conleche_pin"
git -C "$run_dir/con-leche" merge-base --is-ancestor "$release_pin" "$conleche_pin"
git -C "$run_dir/con-leche" show --no-patch --format='%H %cI %s' "$release_pin" "$conleche_pin" \
  | tee "$run_dir/conleche-provenance.txt"
if "$include_lean4lean"; then
  git clone --quiet https://github.com/digama0/lean4lean "$run_dir/lean4lean"
  git -C "$run_dir/lean4lean" checkout --quiet --detach 67f63b0c818920dfaed2ad07ccff187a6a8fe1e3
fi

(
  cd "$run_dir/con-leche"
  lean --version | tee "$run_dir/conleche-version.txt"
  lake build ConLeche.MainTheorem 2>&1 | tee "$run_dir/conleche-build.log"
  lake env lean "$artifact_dir/ConLecheAudit.lean" 2>&1 | tee "$run_dir/conleche-audit.log"
  for module in ArtifactAudit GraphAdapter GraphEnvironment GraphDeclarations PrimitiveLaws ClosedGraph AcceptedGraph GraphChecks; do
    lake env lean -R "$artifact_dir" -o ".lake/build/lib/lean/$module.olean" \
      "$artifact_dir/$module.lean" 2>&1 | tee "$run_dir/$module.log"
  done
)
if "$include_lean4lean"; then
(
  cd "$run_dir/lean4lean"
  lean --version | tee "$run_dir/lean4lean-version.txt"
  lake build Lean4Lean.Theory.Typing.Basic Lean4Lean.Theory.Typing.Lemmas \
    Lean4Lean.Theory.Typing.UniqueTyping 2>&1 | tee "$run_dir/lean4lean-build.log"
  lake env lean "$artifact_dir/Lean4LeanAudit.lean" 2>&1 | tee "$run_dir/lean4lean-audit.log"
)
fi
# The Lean4Lean diagnostic intentionally reports sorryAx for IsDefEq.uniq.
# Success means the experiment ran; it is not an adoption/audit approval.
printf 'Completed; inspect inventories and limitations in %s\n' "$run_dir"
