# Bounded FRP Spec import prototype

2026-11-02. **The first focused compiler check passed with exit code 0 and no
diagnostics.** No import correction was needed. This is a cross-cutting
dependency-load prototype, not chapter acceptance, an integrated proof audit,
or authorization to change/restart the active candidate.

## Exact change

`Applications/FRP/Spec.lean` is an exact copy of the current integrated source
except for replacing its single `import Mathlib` line with:

```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Ext
```

The existing `SquareKit.FunctionCategory` and `SquareKit.CartesianMap` imports
remain. Every definition, statement, proof, comment and other byte is unchanged.
`Spec.original.lean` preserves the input; `imports.patch` preserves the complete
diff. Reversing just the replacement reconstructs the original source exactly.
Both main and candidate source hashes remained unchanged after this check.

| Input | SHA-256 |
| --- | --- |
| Original Spec in main, candidate and `Spec.original.lean` | `c0b5d8155c574329fac0b4aced18c69322b33f8e4e6bbb5278365a7fc57211f8` |
| Staged Spec | `b5df6de8a4ed0188009b4d35c8508512418a8e980a85300691d3585894d22230` |
| Complete import-only patch | `3bcb10c798f98bc935c8c93c35efe14aa35efb2f6b1f69a838116c4bdef18e73` |
| Exact setup copy | `6b4af7891d8b68f01d431a82dd1a707b7e0d446479daf8935cc8f08f68ca787b` |

## Setup reuse and actual import evidence

The setup was copied byte for byte from the active candidate's already-written
`vfa-validation/.lake/build/ir/Applications/FRP/Spec.setup.json`. It retains
module name `Applications.FRP.Spec`, package `compilingWithSquares`, legacy
module mode (`isModule: false`), empty options, empty plugin/dynamic-library
lists, and all 9,035 existing absolute artifact mappings. The seven explicit
source imports' mapped artifacts were present before launch. Dependencies were
read from their completed candidate artifacts; this task wrote none of them.

The setup has **no `imports` override**. In pinned Lean 4.35.0:

- `Lean/Setup.lean:188–213` defines `imports? := none` separately from
  `importArts`; the latter supplies pre-resolved artifact paths.
- `Lean/Elab/Frontend.lean:302` selects
  `setup.imports?.getD stx.imports`, so this setup uses the staged parsed header.
- `Lean/Environment.lean:2233,2242` resolves artifacts by requested module name.
- `Lean/Shell.lean:541–555` retains the setup's module name when compiling the
  staged absolute source path.

This was also checked against the actual output: `out/Spec.ilean` reports module
`Applications.FRP.Spec` and exactly the five Mathlib imports above plus the two
retained SquareKit imports in `directImports`. It does not list `Mathlib` as an
umbrella import. The generated C initializer declarations agree. The old
umbrella's presence as an unused key in the copied artifact-resolution map did
not silently preserve it as a direct import root. The extracted header and C
evidence are saved in `postcheck-evidence.json`.

## Exact check and outcome

The active candidate compiler's observed options were `-o`, `-i`, `-c`,
`--setup` and `--json`, with empty setup options. The prototype retained those
settings, the pinned compiler and Nix shell, changing only source/output/setup
paths to staging. One auxiliary compiler ran with `LEAN_NUM_THREADS=1`.

Working directory: `/workspace/scratch/0c54f2db1fdf/conaled`.

```bash
export PATH=/root/.nix-profile/bin:$PATH
export NIX_CONFIG='build-users-group =
experimental-features = nix-command flakes'
export LEAN_NUM_THREADS=1
timeout --signal=TERM --kill-after=5s 180s nix develop --command \
  /root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
  /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/Applications/FRP/Spec.lean \
  -o /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/out/Spec.olean \
  -i /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/out/Spec.ilean \
  -c /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/out/Spec.c \
  --setup /workspace/scratch/0c54f2db1fdf/work-state/staging/frp-imports/Spec.setup.json \
  --json
```

`run-initial.py` executed this command and recorded:

- Start: `2026-11-02T05:39:07.643072+00:00`.
- Finish: `2026-11-02T05:40:08.098483+00:00`.
- Exit: **0**. Timed out: **false**. Diagnostics: **none** (empty log).
- Whole-invocation elapsed time: **60.455 seconds**, including Nix startup.
  The 180-second timeout covered the entire invocation, with a five-second
  termination grace period that was not used.

The exact argument vector/environment additions are in `initial-result.json`;
the empty combined stdout/stderr log is `initial-diagnostics.jsonl`. Output
sizes and hashes are in `postcheck-evidence.json`. All emitted files are under
`out/`; no compiler output path targets main or candidate sources/caches.

## Review and limits

`/root/environment/lean_info_read` independently inspected the source-byte
comparison, patch, identities, setup copy and runner. It found no discrepancy:
the change is limited to the imports, setup preserves the staged header, the
execution bound is explicit, and output paths remain within staging. That
review ran no compiler and is not a mandatory chapter review.

The result establishes that this exact Spec source compiles with these narrower
imports and the recorded existing artifacts. It does **not** validate
Equivalence, direct/indirect clients, an integrated candidate, or a transitive
axiom audit. No `lake build`, cache fetch, dependency mutation, source mutation
in either checkout, or signal to the active candidate process occurred.

This is not a controlled timing or compiler-output-flag comparison. No claim
about peak memory, speedup or the cause of the original run's paging follows
from the elapsed duration. The active candidate continues unchanged.

The copied setup contains workspace-specific absolute paths. A restored
workspace must recreate the pinned dependency artifacts and an appropriate
setup before reproducing this check; source and recorded identities are the
durable deliverables. Generated outputs are reproducible intermediates, and
their recorded hashes are historical evidence if checkpoint capture omits them.
