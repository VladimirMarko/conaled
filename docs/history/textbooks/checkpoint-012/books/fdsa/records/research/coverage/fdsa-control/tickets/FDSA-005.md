# FDSA-005 — Binary Search Trees

State: queued. Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, starting printed page 59.
Depends on: FDSA-004.

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

- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Interval_Tree.html
- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Tree_Rotations.html
- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Tree_Set.html

No formalization or completion is claimed by this queued ticket.

## Source-preparation snapshot

Recorded 2026-11-02: `research/chapter05-obligations.md`,
SHA-256 `a80e32867234bf2bb2d291ee7bb249afc051dde128cb3c1f7879609567831a45`.
This is source/reuse preparation, not a checked implementation or chapter
acceptance. The autonomous scope is specified; the chapter remains queued
behind its stated predecessor and retains every build/review gate.

## Source-scope reconciliation, 2026-11-02

Current inventory: `research/chapter05-obligations.md`,
SHA-256 `f512f6b3723e8e036e9292aab985e93d15b2bf49b1c2c6dff79b3e6911ffcaad`.
The earlier snapshot is preserved byte-for-byte under
`reviews/source-inventories-before-scope-repair/`. Reasons, IDs,
old/new hashes and remaining source gaps are recorded in
`research/scope-reconciliation.md` (SHA-256
`21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87`).
This clarifies required coverage without implementation or acceptance
credit. The chapter/appendix retains its current dependency gates.
