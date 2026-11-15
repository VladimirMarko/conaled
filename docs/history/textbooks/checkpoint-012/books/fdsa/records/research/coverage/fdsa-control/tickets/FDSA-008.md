# FDSA-008 — Red-Black Trees

State: queued. Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, starting printed page 95.
Depends on: FDSA-007.

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

- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/RBT_Map.html
- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/RBT_Set.html
- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/RBT_Set2.html

No formalization or completion is claimed by this queued ticket.

## Source-preparation snapshot

Recorded 2026-11-02: `research/chapter08-obligations.md`,
SHA-256 `1c55482207ef854a43b8d54c1f7a128ad71f01ad5054f5a8415340ac772dd783`.
This is source/reuse preparation, not a checked implementation or chapter
acceptance. The autonomous scope is specified; the chapter remains queued
behind its stated predecessor and retains every build/review gate.

## Source-scope reconciliation, 2026-11-02

Current inventory: `research/chapter08-obligations.md`,
SHA-256 `16e26a46452d06401e1f50317fb8d7e3ad4a341a2070870b07c7014f1b2e07e1`.
The earlier snapshot is preserved byte-for-byte under
`reviews/source-inventories-before-scope-repair/`. Reasons, IDs,
old/new hashes and remaining source gaps are recorded in
`research/scope-reconciliation.md` (SHA-256
`21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87`).
This clarifies required coverage without implementation or acceptance
credit. The chapter/appendix retains its current dependency gates.
