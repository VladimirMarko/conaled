# FDSA-XP01 — Shared ordered and signed potential accounting

State: implementation draft written; focused compilation and final reviews pending.
Triage: ready-for-agent. Parent: FDSA-000.

Depends on: FDSA-001 acceptance; existing shared foundation branch.
Cross-cutting consumers: Chapters19–23, with later algorithm-specific obligations
remaining queued in chapter order.

Exact requirements are frozen before code changes in
`reviews/potential-requirements.md`. Starting candidate:
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`.

## Draft implementation

The independent preflight is complete in
`research/potential-generalization-preflight.md`. Its exact-capability design
is implemented as a draft in `Applications/Resources/Potential.lean`: raw work
and charges have separate carriers, additive maps preserve budgets, and mapped
boundary laws support preserved invariants. Signed telescoping uses group
subtraction. Existing Nat theorem statements remain, with the identified FIFO
raw-zero annotation. The natural ordered-group import supplies the instances
used when the old Nat bounds specialize the generic result.

`Examples/MappedPotentialAccounting.lean` connects the actual counter's local
law to Real accounting, negative charges to initial credit, a fractional
valid-domain example to invariant-aware bounds, and ordered free-monoid
observations to exact telescoping. Reconstruction notes record intended
statements and independent expected calculations. These are written source,
not checked Lean results yet. No compiler was launched for this unit while
the frozen Chapter1 full check was running.

Committed draft: `c28ba71863d2a35ee1c3a089caa90464e4cca692` on
`work/fdsa-list-foundations`. This commit is for recovery and subsequent
validation; it is not an accepted candidate.

## Completion gates

- [x] Existing measured execution and natural accounting interfaces inspected.
- [x] Exact scope, source statements and connected-case expectations recorded.
- [ ] Definitions and proofs implemented with existing Nat contracts preserved.
- [ ] Connected cases and statement review completed.
- [ ] Focused builds, immutable candidate verification and exhaustive audit pass.
- [ ] Independent Standards and Spec reviews have no unresolved findings.
- [ ] Candidate identity verified and checkpoint saved/uploaded.

This ticket does not claim that unary accounting proves multi-input ownership,
later dynamic-table/heap algorithms, or any chapter's full coverage.

## Development continuation — 2026-11-04T11:09:46.778661+00:00

Exact isolated candidate `5ffa882bbcb34c1c533710a0c980423484e5a77d` on work/fdsa-potential-development in the existing
central checkout retains unaccepted Z plus only the original six XP01 paths.
F/R/Z/X branch refs are unchanged. The original c28 draft and all preflights remain.
A host checkout-residual issue and both stopped preflights are recorded honestly;
no XP01 compiler has run yet. Focused compilation, actual statement inspection,
complete independent axes and all eventual full acceptance gates remain pending.
See reviews/potential-round1.md and provenance/xp01-development-integration-20261104/.
This does not activate Chapters19–23 or change the recorded acceptance order.
