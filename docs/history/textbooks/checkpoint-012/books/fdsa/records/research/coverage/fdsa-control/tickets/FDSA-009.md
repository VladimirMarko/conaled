# FDSA-009 — AVL Trees

State: queued. Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, starting printed page 105.
Depends on: FDSA-008.

## Scope

Cover every mathematical construction, theorem and exercise in this source unit,
with exact scope and reusable existing declarations inventoried before implementation.
Preserve the book's assumptions and cost model; harmonize with conaled interfaces.

## Completion gates

- [x] Item-by-item source coverage and reuse/gap map completed.
- [ ] Definitions and proofs implemented without admissions or additional axioms.
- [ ] Checked uses and statement review retained.
- [ ] Applicable immutable-candidate build and exhaustive proof audit passed.
- [ ] Independent Standards and Spec reviews have no unresolved findings.
- [ ] Accepted candidate verified and recovery checkpoint saved/uploaded.

## Primary source links

- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/AVL_Bal_Set.html
- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/AVL_Set.html

No formalization or completion is claimed by this queued ticket.

## Source-preparation snapshot

Recorded 2026-11-02: `research/chapter09-obligations.md`,
SHA-256 `daf503cbdbbd80320bbe4b6cfe2c73102f39dcf50ae49cbd544907eec95c689b`.
This is source/reuse preparation, not a checked implementation or chapter
acceptance. The autonomous scope is specified; the chapter remains queued
behind its stated predecessor and retains every build/review gate.

## Source-scope reconciliation, 2026-11-02

Current inventory: `research/chapter09-obligations.md`,
SHA-256 `6ade1fd1a470c64d613212098e311d2e0189f62bd82045dbb2f8f4387f426285`.
The earlier snapshot is preserved byte-for-byte under
`reviews/source-inventories-before-scope-repair/`. Reasons, IDs,
old/new hashes and remaining source gaps are recorded in
`research/scope-reconciliation.md` (SHA-256
`21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87`).
This clarifies required coverage without implementation or acceptance
credit. The chapter/appendix retains its current dependency gates.
