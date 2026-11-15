# Monitor import diagnosis and ST-003 disposition

This is a supplement to the existing Preface/Perm review loop, coordinated by
`/root/formal_review`. The original Standards reviewer
`/root/formal_review/standards` performed the bounded read-only assessment below.
The original Spec reviewer `/root/formal_review/spec` is retained for the concrete
correction and completed gate evidence. This note creates no new enclosing loop,
does not replace prior full-source analyses, and grants no integrated-gate credit.

## Reviewed identity and actual failed run

- Fixed enclosing base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Reviewed candidate: `cf0a687265c1929ffd3ff6f15fa18febe0fb61b5`.
- Retained full scope: 26 files, +500/-17, no exclusions.
- Validation checkout: `vfa-summation-validation`.
- Complete attempt evidence:
  `validation/1002-candidate-cf0a687-summation-fresh1/`.

The execution API and kit result both returned exit 1. The kit reports
`timed_out:false` and `recorder_error:null`. There were 936 successful ordinary
modules before module 937, `SquareKit.Temporal.Monitor`, failed. No exhaustive
audit ran and no successful fresh verification record exists.

The final output is 89,126 bytes with SHA-256
`4e08aafee0a0a8f53804c346bb97521d600e9e7b24a4950883435a1ad4bdd244`.
Standards and the coordinator independently reproduced this identity from the
preserved output. The launch's historical running status does not supersede the
completed result and terminal records.

## ST-003 is fixed

Standards independently matched the committed corrected
`Examples.IndefiniteService` source to SHA-256
`0daaf049128e56210c605cc5b2d5cf8b155aad1727eac6bad189615fc75fa7fd`.
The complete log records:

```text
[603/953] Examples.IndefiniteService (3.15s)
```

The checker then proceeds through later modules. This establishes actual complete
elaboration of the corrected source, satisfying the remaining ST-003 obligation.
The first 47,143 bytes of the final log reproduce SHA-256
`f570ff2a06393a2825a5d8b5b1fe65f8abc513997acae1ec7b0aff3b6b010eb6`,
the progress-prefix binding retained in
`validation/1039-indefinite-service-fresh-progress.json`.

ST-003 is therefore **fixed on cf0a687**. This disposition uses the completed
module evidence, not an assertion that the enclosing fresh run passed.

The same log corroborates the previous ST-004/ST-005 fixes: complete FiniteMH at
665, StructuredCosts at 931, and `Examples.StructuredLinearCosts` at 933 succeed.
Their existing fixed dispositions remain unchanged.

## ST-006: incomplete import narrowing in Monitor

**Severity: Medium. Status: Open, awaiting actual corrected-module validation.**

The fixed-base diff shows that this task replaced Monitor's
`import Mathlib.Tactic` with `import Mathlib.Data.Nat.Basic` and
`import Lean.Elab.Tactic.Omega`; its remaining body was preserved. The failure is
attributable to the task's incomplete import narrowing, not to an unchanged
baseline file.

Standards inspected the exact pinned Mathlib sources and version-5 metadata.
They support this single additional import while retaining the existing imports
and every prior source byte:

```lean
import Mathlib.Order.Lattice
```

| Source location | Actual failure | Support supplied by the proposed import |
|---|---|---|
| Line 58 | Invalid `hj.trans` projection | `Mathlib.Order.Basic` defines the `LE.le.trans` alias. |
| Line 59 | The same missing transitivity projection | The same alias supports this second use. |
| Line 123 | `simpa using h` leaves the bound `k <= min k xs.length` | `LinearOrder.toLattice` supplies `inf := min`, and the lattice definitions supply `[simp] le_inf_iff`. |
| Line 176 | Unknown `lt_self_iff_false` | `Mathlib.Order.Basic` defines this theorem with `[simp]`. |

The public import path is explicit: `Mathlib.Order.Lattice` imports
`Mathlib.Order.ULift`, which publicly imports `Mathlib.Order.Basic`.
`Order.Basic` defines `lt_self_iff_false` at line 121 and `LE.le.trans` at line 125.
`Order.Lattice` defines `LinearOrder.toLattice` at line 278 with `inf := min` and
publicly imports `Order.Defs.Lattice`. The annotation at line 117 in the latter
generates `[simp] le_inf_iff`. The existing `Mathlib.Data.Nat.Basic` import supplies
`LinearOrder Nat`.

This explains the additional min-bound simplification. `Order.Basic` alone is
not a complete source justification: the already-imported `le_min_iff` in
`Order.Defs.LinearOrder` is not marked `[simp]` there. Pinned source and metadata
agree on the supporting declarations, and the named `Order.Lattice.olean` is
installed.

This remains a **static recommendation**, not a successful compiler result.
Neither reviewer nor coordinator ran a compiler, build, cache operation or
process-control command. If this prefix is the sole source change, the new full
enclosing scope will remain 26 files and become +501/-17. The concrete correction
candidate must be recorded and assessed separately under
`specs/1040-monitor-order-imports.md`.

## Retained findings and remaining gates

| Finding | Disposition at this assessment |
|---|---|
| ST-001 | Fixed. |
| ST-002 | Open, Medium; bounded artifact-incident preservation/recovery evidence remains required. |
| ST-003 | Fixed on cf0a687 by actual complete corrected-module elaboration. |
| ST-004 / ST-005 | Fixed; additionally corroborated by this fresh attempt. |
| ST-006 | Open, Medium; the single-import Monitor correction requires actual validation and reviewer disposition. |
| SP-VAL-001 | Open on the retained Spec axis. |

**Standards remains Blocked. Formal acceptance remains Blocked.** There are two
open Standards findings, with worst severity Medium. The Spec axis has not been
re-run merely for this failure diagnosis; its prior source analysis and blocked
validation outcome remain in force.

Root will preserve the failed attempt, record the exact correction candidate,
and obtain actual whole-source Monitor and bounded remaining-consumer checks
with private diagnostic outputs. Re-derive candidate-specific dependency
selectors/provenance. Do not copy diagnostic or prior fresh outputs into the
managed cache. Preserve the quarantined old 4adc checkout and its unknown child
status; the existing stable-input and isolated-output conditions remain in force.

The corrected candidate still requires a new complete fresh build and exhaustive
audit, the unchanged non-repairing collector/classification, guarded build with
postguard and a new audit/verification record, the managed ProofAudit prerequisite,
all four regressions, both independent final evidence reviews, and immediate
candidate verification. Acceptance and its uploaded checkpoint must precede any
next-chapter implementation. No prior failed run or focused check substitutes
for these gates.

This note was written by the coordinator after root confirmed checkpoint 103's
capture/upload had completed and explicitly authorized preserving the returned
diagnosis and disposition. It changes evidence only, not source or gate policy.
