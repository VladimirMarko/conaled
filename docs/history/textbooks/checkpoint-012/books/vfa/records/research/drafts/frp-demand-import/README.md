# Local #1021: isolated Demand import correction

Status: **the single authorized staging check passed**, 2026-11-02. This is evidence for a small client import correction against candidate `777bab9b2510deab54603c3df267e5c134a3e1e0`; it is not a whole-candidate result or chapter acceptance. Main and candidate source files were not edited, and no primary validation process was signalled.

## Failure and correction

The primary candidate log `work-state/validation/1002-candidate-777bab9.log` reported `Applications/FRP/Demand.lean:139:16`: after `simp_all [next]`, `exact ⟨n, le_rfl, ha⟩` supplied `le_rfl : n ≤ n` where `n < n + 1` was expected. `original-diagnostic.txt` preserves the exact diagnostic, and `inputs.json` preserves the original compiler trace and argument vector.

The staged `Applications/FRP/Demand.lean` adds exactly one line immediately after `import Applications.FRP.Trace`:

```lean
import Mathlib.Order.SuccPred.Nat
```

Removing that single added line reproduces every original byte; no declaration, proof, comment, or other import changed. `imports.patch` contains the complete diff. The candidate and main original source files were byte-identical before the check and remain so afterward.

The pinned Mathlib file `Mathlib/Order/SuccPred/Nat.lean:34` supplies `Nat.instSuccAddOrder` and imports `Mathlib.Algebra.Order.SuccPred`. The latter file's `Order.lt_add_one_iff` at line 240 is a `[simp]` theorem, reducing `x < y + 1` to `x ≤ y` under the appropriate successor-order and no-maximum instances. This explains the missing simplification supplied by the explicit import. The checked result concerns the complete unchanged Demand module, not a substituted or isolated proof example.

## Setup construction and artifact resolution

The starting setup was the actual current candidate file `vfa-validation/.lake/build/ir/Applications/FRP/Demand.setup.json` (980 artifact mappings). It has no `imports` override and does not map `Mathlib.Order.SuccPred.Nat`. The frozen `work-state/staging/frp-imports/Spec.setup.json` has 9,035 mappings, also without an imports override.

`prepare.py` retained **every current mapping unchanged** and added only names absent from the current setup. It retained all current top-level fields and their values: module name `Applications.FRP.Demand`, package `compilingWithSquares`, `isModule: false`, empty `options`, `plugins`, and `dynlibs`. The union has 9,040 mappings: 980 current plus 8,060 missing names; five current names were absent from the older broad map. `inputs.json` records the exact added-name list. The broader map is solely artifact resolution and does not request additional imports.

Trace, Spec, and Frontier resolve to their completed candidate artifacts. The added Nat module resolves to completed artifacts in the candidate's pinned Mathlib dependency. Fifteen protected source/setup/artifact identities were checked before and after execution; none changed. Their complete hashes are in `inputs.json` and `postcheck-evidence.json`.

## Exact execution and result

Preparation and the sole compiler invocation were launched from `/workspace/scratch/0c54f2db1fdf` with:

```sh
python3 work-state/staging/frp-demand-import/prepare.py
python3 work-state/staging/frp-demand-import/run-check.py
python3 work-state/staging/frp-demand-import/postcheck.py
```

Only `run-check.py` invokes Lean. It uses working directory `/workspace/scratch/0c54f2db1fdf/conaled`, the pinned Nix shell, the exact original Lean executable `/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, and the original `-o`, `-i`, `-c`, `--setup`, and `--json` argument structure. Only the input, output, and setup paths point to this staging directory. The complete executed argument vector and environment additions, including the exact original candidate `LEAN_PATH`, are recorded in `STARTED.json` and `result.json`.

The wrapper was `timeout --signal=TERM --kill-after=5s 180s nix develop --command …`, so the 180-second limit covered the entire Nix/Lean invocation, with a five-second forced-termination grace. `LEAN_NUM_THREADS=1`. The runner starts its own process session and refuses a second launch once `STARTED.json` exists. No retry occurred. `environment-evidence.json` records the toolchain and Nix configuration identities without invoking another compiler.

| Observation | Result |
| --- | --- |
| Start / finish (UTC) | 2026-11-02 06:18:16.204625 / 06:20:26.191242 |
| Elapsed time / exit | 129.985 seconds / 0 |
| Timeout | No |
| Diagnostics | Empty output, zero bytes |
| Emitted module | `Applications.FRP.Demand` |
| Emitted direct imports, in order | `Applications.FRP.Trace`; `Mathlib.Order.SuccPred.Nat` |
| Protected inputs changed | None of 15 |

The emitted `.ilean` header is preserved in `postcheck-evidence.json`; it contains exactly the two direct imports above. The C initializer declarations independently agree (plus Lean's `Init` initializer). All emitted staging artifacts were hashed after completion, then removed after metadata extraction; no staged artifact was installed in a candidate or main cache.

## Identities

All hashes below are SHA-256. The manifest `SHA256SUMS` covers the retained staging files; `postcheck-evidence.json` records the generated artifacts that were removed.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| Original Demand source | 10,411 | `516ebcd62d8f03157d96ac176829d23ac6687f8b21b8ff6337050f0e489b92ff` |
| Staged Demand source | 10,445 | `4e92f97ac56aa684c27f3421cdf1890b64159b631fdd828c420af00d3d9c6ad6` |
| Actual current Demand setup | 691,644 | `1b9f62b23b5487f4abab3be43f990008a08df248a6ef60741ce3c4e720c3f875` |
| Frozen broad Spec setup | 7,051,229 | `6b4af7891d8b68f01d431a82dd1a707b7e0d446479daf8935cc8f08f68ca787b` |
| Merged staging Demand setup | 7,584,966 | `3a254c514b4c6f5d8d9bcccdb7c4dea18e417647a1cbb336c0031dc84bfe7935` |
| Generated Demand `.olean` (removed) | 822,784 | `7d575732266d7f2f57ea74273d75e4358973db3ddafc493631e6a5e507ad1f06` |
| Generated Demand `.ilean` (removed) | 31,904 | `1881ffbcfd4ea4028396571a580a640b5b4b8de16b09e6ff23634b152bda561c` |
| Generated Demand `.c` (removed) | 87,947 | `ace7393ba08c35ac66ce89cbb59e374783cc47f4fac11cbf5c9ebb2fe93aef97` |

This result justifies proposing the single explicit import for integration and a fresh candidate review/build. It does not change the failed candidate's status, certify downstream modules, close local #1021, or advance a book chapter. The staging files are frozen for the parent workflow's review and durability checkpoint.
