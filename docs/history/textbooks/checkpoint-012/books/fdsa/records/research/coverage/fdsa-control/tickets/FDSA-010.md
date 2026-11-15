# FDSA-010 — Beyond Insert and Delete: Union, Intersection and Difference

State: queued. Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, starting printed page 117.
Depends on: FDSA-009.

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

- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Set2_Join.html
- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Set2_Join_RBT.html
- https://isabelle.in.tum.de/dist/library/HOL/HOL-Data_Structures/Set_Specs.html

No formalization or completion is claimed by this queued ticket.

## Source-preparation snapshot

Recorded 2026-11-02: `research/chapter10-obligations.md`,
SHA-256 `2bc962c3041e5e4d5ba15bdcf01d5b278ff91231fb83f347982a7ff585eac321`.
This is source/reuse preparation, not a checked implementation or chapter
acceptance. The autonomous scope is specified; the chapter remains queued
behind its stated predecessor and retains every build/review gate.

## Source-scope reconciliation, 2026-11-02

Current inventory: `research/chapter10-obligations.md`,
SHA-256 `f3703190c2c5591a8b8685e88205652ca412e90fedb3b467ceb5d4bfd55eac0b`.
The earlier snapshot is preserved byte-for-byte under
`reviews/source-inventories-before-scope-repair/`. Reasons, IDs,
old/new hashes and remaining source gaps are recorded in
`research/scope-reconciliation.md` (SHA-256
`21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87`).
This clarifies required coverage without implementation or acceptance
credit. The chapter/appendix retains its current dependency gates.

## Conditional expected-work preparation, 2026-11-02

`research/treap-conditional-work-preflight.md`, SHA-256
`99e7c6128c5a941d0dbef0b473c0f4f27e73d8f75b69aa64d347937dd4b2dcc1`,
records a possible repair of the open C10-117 probabilistic bridge. It uses
coarse ancestor histories, two color-restricted search laws, the actual
Figure 11 left-maximum `join2`, and a conditional weighted-cluster bound
with constant 9 before the deterministic layer sum. Canonical-tree,
conditional-law, execution-cost and book/paper correspondence lemmas remain
explicit future work.

The same report preserves exact counterfamilies to transporting the
fixed-subset first-position mean into every recursive history and to
bounding actual local `join2` work by the actual local split work. Those
counterfamilies do not refute the stated total expected-work theorem. The
book's right-minimum helper is still a separate execution/work bridge.

The independent fixed-global-law position/internal-order plan is retained
in `research/permutation-placement-order-preflight.md`, SHA-256
`3fe9a8d80a6a57faa4265ecb85267216039dae9f39164cf928560c1bae9cba81`,
with a separate bounded assessment under `reviews/`. It does not resolve
the recursive conditioning issue on its own.

Root read both complete reports. No implementation scope, obligation ID,
source inventory, acceptance status or chapter dependency changed. This
ticket remains queued and C10-117 remains open.

Checkpoint 0026 preserves these reports and all prior refs/tickets. Its
SHA-256 is `e15a5b11fbd651a7f0738da8ed61c5c8517d218a0f23d4bb7d0ef73070696b24`;
saved file ID: `libfile_6702730c53d08191adbcd7d085ce32d4`. The separate
treap peer assessment was still pending when the archive was captured.

The subsequent bounded mathematical assessment is retained as
`reviews/treap-conditional-work-source-preflight.md`. It found no concrete
error, including in the fixed-key history partition and weighted layer
assembly. This post-checkpoint record does not close any formal obligation
or review gate.
