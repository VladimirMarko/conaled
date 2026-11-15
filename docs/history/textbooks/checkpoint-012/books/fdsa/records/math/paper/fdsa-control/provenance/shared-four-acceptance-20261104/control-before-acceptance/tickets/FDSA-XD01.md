# FDSA-XD01 — Shared difference-list closure observations

State: committed source draft; compilation and final reviews pending.
Triage: ready-for-agent. Parent: FDSA-000.
Depends on: repaired FDSA-001 acceptance and later integration validation.

Cross-cutting scope: measured suffix callbacks, separate closure creation and
application observations, ordinary DList value correspondence and compositional
builder workloads. Chapter-specific sorting/traversal recurrences remain queued.

Exact requirements: `reviews/difference-list-cost-requirements.md`.
Design/reuse preflight: `research/difference-list-cost-preflight.md`.
Base: `a14977b9e316cc484ffad8a470d26b15615956c0`.
Branch/worktree: `work/fdsa-builder-costs` / `conaled-builder-costs`.

- [x] Exact model, public interface and boundary expectations frozen before code.
- [x] Core operations/laws and connected cases written and source statement-reviewed.
- [ ] Focused elaboration and integrated immutable candidate full verification pass.
- [ ] Independent Standards/Spec reviews have no unresolved findings.
- [ ] Final candidate verified; durable checkpoint saved and exposed.

No concurrent compiler is permitted during the frozen old Chapter 1 gate.
Sharing a closure description is not memoization of its output. The actual
asc/scanner correspondence and repeated ordinary append/reverse comparison
remain Chapter 2 obligations; no chapter is activated by this unit.

Original source draft: `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8`.
Current corrected draft: `62809ced86c561c7a6cce8b71e727177a3f17fb8`.
Exact requirements SHA-256:
`cb215a33cce3dd258cca37b9d703522d19caf2da76767c01e573d268b3e92c4e`.
The author-side example/source preflight found no mathematical mismatch and
identified two wording clarifications, both applied before committing.
Root inspected the complete core and client derivations and integrated the
public root. `git diff --cached --check` passed; no Lean validation ran.
See `reviews/difference-list-cost-candidate.md`.

`XD01-DOC-001` corrects the AFP Natural_Mergesort source attribution only.
The old design preflight remains historical and must be read with
`reviews/difference-list-provenance-correction.md`. The correction is committed;
its independent final confirmation and all unit validation remain pending.

Recovery checkpoint 0025 is saved with the correction successor and retained
erratum; its receipt is in `../checkpoints.json`. All acceptance gates remain
pending.

## Combined receiving source continuation — 2026-11-04T14:30:56.029869+00:00

This unit retains its full original scope and history within I=312aafb4446b995ff5542041b4e2e074f776db1e over accepted foundationF. Both independent current source assessments are complete with zero unresolved findings; SH4-HIST-001 is resolved by four normal recorded history-preserving merges, with initialH's noncompliance retained. See reviews/shared-four-integration-round1.md and both named current reports. No full I check, receiving314type command, final approval or acceptance is yet credited. All existing original findings, focused evidence qualifications and mathematical/compatibility cases remain; no completion box closes through source preparation alone.
