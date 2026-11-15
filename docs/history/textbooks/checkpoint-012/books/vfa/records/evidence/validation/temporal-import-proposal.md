# Temporal import proposal — read-only decision evidence

Date: 2026-11-02. Context: the active full candidate is `bed44c1`; its log records `Applications.FRP.Temporal` taking 756 seconds. This investigation read complete unchanged sources and pinned dependency sources. It ran no compiler/build, changed no source/cache/configuration, and signalled no process. This note does not authorize changing or restarting that candidate.

## Proposed bounded correction

For `SquareKit/Temporal/Finite.lean` only, replace its sole import `Mathlib.Tactic` with:

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Convert
```

Preserve every non-import byte. This is a conservative explicit statement of the module's finite-index/equivalence and `convert` dependencies. At the pinned version, `Mathlib.Data.Fin.Basic` alone has the same transitive import closure: it publicly imports `Mathlib.Tactic.Common`, whose line 50 publicly imports `Mathlib.Tactic.Convert`. Keeping the explicit `Convert` line documents the tactic used without increasing the current dependency closure. This is not a claim that no smaller combination of lower-level files could ever suffice.

The complete source contains finite temporal constructors, structural recursion/folds/maps, a finite-window representation and its inverse equivalence, and a terminal-evidence impossibility theorem. The following dependency audit accounts for its substantive external names and tactics:

| Source need | Existing pinned provider |
| --- | --- |
| `Fin`, `Fin.elim0`, `Fin.succ`, `Fin.cases`, arithmetic on their values | `Mathlib/Data/Fin/Basic.lean:8–13` imports Batteries Fin, Nat support and the core Fin development. Core `Init/Data/Fin/Basic.lean:31` defines `elim0`; `Init/Data/Fin/Lemmas.lean:952` defines `cases`. |
| `Until.windowEquiv` and `≃` | `Mathlib/Data/Fin/Basic.lean:11` publicly imports `Mathlib.Logic.Equiv.Defs`. |
| `eqRec_eq_cast`, `cast_cast`, `cast_eq` in the reconstruction proofs | `Batteries/Logic.lean:78`, core `Init/PropLemmas.lean:22`, and `Init/Core.lean:870`, respectively. Equiv's function/subtype/logic imports supply the Batteries lemma. |
| `Sigma.mk.inj_iff`, `heq_eq_eq`, `Prod.mk.injEq`, `Prod.ext`, `Eq.mp`, `Eq.mpr`, function composition/identity | Core and the imported basic logic/equivalence development; no additional mathematical hierarchy appears in the source. |
| `omega`, `simp`, `simp_all`, `simpa`, induction/cases, `obtain`, `refine`, `congr`, `funext`, rewriting | Core elaborator tactics plus the common tactic support imported by Fin.Basic. Pinned `Lean/Elab/Tactic.lean:36` imports `Lean.Elab.Tactic.Omega`. |
| The single `convert ih using 1` in `ofWindow_window` | `Mathlib/Tactic/Convert.lean`, explicitly retained. |

Core source paths above are under `/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/`; package paths are under `/workspace/scratch/0c54f2db1fdf/conaled/.lake/packages/`. Read-only access to the pinned core source used the approved escalated executor; no toolchain executable was invoked.

## Concrete import-load evidence

The completed candidate `SquareKit.Temporal.Finite.ilean` reports exactly `Mathlib.Tactic` as its direct import. Its actual setup has **3,121 artifact mappings**, with module name `SquareKit.Temporal.Finite`, package `compilingWithSquares`, `isModule: false`, empty options/plugins/dynlibs, and no imports override. The FRP temporal client's setup has 3,138 mappings and direct imports Finite, Demand, and Progress.Processors.

A read-only source-graph traversal removed nested block/line comments, followed import edges through the checked-out project/package sources, and counted distinct resolved module names. It included public, ordinary and meta edges; compiler-distribution modules (`Init`, `Lean`, `Std`, `Lake`) were outside these counts.

| Direct package roots | Resolved package modules | Of which Mathlib |
| --- | ---: | ---: |
| `Mathlib.Tactic` | 3,121 | 2,837 |
| `Mathlib.Data.Fin.Basic`, `Mathlib.Tactic.Convert` | 496 | 224 |

The current graph count agrees with the actual Finite setup count. The proposed roots therefore remove **2,625 resolved package modules** from this module's source import closure. These are dependency counts, not measured resident memory, loaded declaration counts, or a predicted speedup. `Fin.Basic` still includes `Tactic.Common` and its associated support.

## Affected clients and remaining uncertainty

The direct project clients are `SquareKit.Temporal.Relations`, `SquareKit.Temporal.Syntax`, and `Applications.FRP.Temporal`. The reverse closure contains **34 production modules including Finite** (33 clients), matching the reported bottleneck scope. Scanning all repository Lean files also finds seven experiment and three script clients, which are excluded from that production count.

The production closure includes temporal relations/batch relations/syntax; FRP temporal payload and causality, finite delay, feedback, pipelines, drivers, reactive contracts/consumers and indefinite service; `Applications.Progress.OccurrenceCursor`; their examples; and the `SquareApplications`/`ProofAudit` roots. These clients currently inherit the umbrella's declarations, instances, simp rules and tactics. A successful focused Finite check would verify only Finite; client compatibility still requires the normal candidate review/build. The prior Demand import failure is a concrete reason to retain this distinction.

`SquareKit/Temporal/Monitor.lean` independently imports `Mathlib.Tactic`, and `Applications.FRP.Monitor` imports it alongside the temporal causality branch. Its source uses core Boolean/List/range/take/ofFn facts and Mathlib's generic `lt_of_le_of_ne` with the natural-number order instance (`Mathlib/Data/Nat/Basic.lean:34`). It therefore shares the umbrella-load question but has a separate dependency boundary. Its independent broad import can retain the heavy closure for monitor clients even if Finite is narrowed. Further Monitor minimization and checking are deferred; no Monitor change is proposed in this bounded Finite test.

**Decision:** a single bounded, isolated focused check of the complete Finite source with the two explicit imports is justified by the concrete 3,121-to-496 dependency reduction. The check should preserve every non-import byte, use the original pinned compiler/options with staging-only outputs and no imports override, and inspect emitted direct-import metadata. It should report failure/timeout without speculative retries. The global simp environment and downstream implicit dependencies remain uncertainties until checked. This proposal neither establishes an elapsed-time improvement nor advances a chapter or the active full gate.

## Exact existing identities

Both main and candidate copies of each temporal source below were byte-identical when inspected. SHA-256:

| Existing file | Bytes | SHA-256 |
| --- | ---: | --- |
| `SquareKit/Temporal/Finite.lean` | 4,961 | `a5250768a66bb6103b3edb188f4ec370f2e9f9f8937ea066c914b3f6056b90a9` |
| `SquareKit/Temporal/Monitor.lean` | 9,116 | `8f9138dccb411976303f1e1b69ceb7a9b61aafebbb00c5b4cec172b9b7139fdd` |
| `lake-manifest.json` | 3,138 | `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b` |
| Candidate `Finite.setup.json` | 2,329,513 | `66b8e39dac0fb306ac3bfad9d0dfdd64a59320187b45256a949e13218d1d0e2f` |
| Candidate `Finite.ilean` | 13,979 | `9503ee0ef91863873a85ff7110a9aa40d8f079780af32d04945a96d07399d60f` |
| Mathlib `Tactic.lean` | 18,296 | `e2edc116c09e6fd631b561d79c97ff88c5672df397abf71c6e2056270b484754` |
| Mathlib `Data/Fin/Basic.lean` | 19,251 | `2e2366059b7e366871729f63f4c98102bbd7d9b5f3d9982cbf0651e674c1f3e0` |
| Mathlib `Tactic/Convert.lean` | 16,040 | `cbffa3b86d16e0f006755cec72b12dc00da33c0228419e483a2ddba1ee27a32c` |
| Mathlib `Tactic/Common.lean` | 5,884 | `7ac187f6724a3254dbb6f9b73f59d857fca95caa822a84d8edb9e7e61a592452` |

Pins: Lean `leanprover/lean4:v4.35.0`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`. Candidate metadata paths are under `vfa-validation/.lake/build/ir/SquareKit/Temporal/` and `vfa-validation/.lake/build/lib/lean/SquareKit/Temporal/`; the timing is in `work-state/validation/1002-candidate-bed44c1.log`.

Frozen decision input; no implementation, validation result, or acceptance is claimed.
