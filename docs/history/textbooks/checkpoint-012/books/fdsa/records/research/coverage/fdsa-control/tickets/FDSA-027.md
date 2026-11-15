# FDSA-027 — Alpha-Beta Pruning

State: queued. Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, starting printed page 319.
Depends on: FDSA-026.

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

- https://isa-afp.org/browser_info/current/AFP/Alpha_Beta_Pruning/Alpha_Beta_Lattice.html

No formalization or completion is claimed by this queued ticket.

## Source-preparation snapshot

Recorded 2026-11-02: `research/chapter27-obligations.md`,
SHA-256 `49b7665f87a87b78a3990a650a02ffea803051105d589376d4c8f672dda86d5f`.
This is source/reuse preparation, not a checked implementation or chapter
acceptance. The autonomous scope is specified; the chapter remains queued
behind its stated predecessor and retains every build/review gate.

## Source-scope reconciliation, 2026-11-02

Current inventory: `research/chapter27-obligations.md`,
SHA-256 `4a7c5a4675822ac7ed0dad125be33b4eb637410ed04beaf8cc07da4672b22ea3`.
The earlier snapshot is preserved byte-for-byte under
`reviews/source-inventories-before-scope-repair/`. Reasons, IDs,
old/new hashes and remaining source gaps are recorded in
`research/scope-reconciliation.md` (SHA-256
`21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87`).
This clarifies required coverage without implementation or acceptance
credit. The chapter/appendix retains its current dependency gates.

## Bounded cache-source recovery, 2026-11-02

`research/chapter27-cache-source-recovery.md`, SHA-256
`c731e8591cd2591c75b444eb31ca075f1b13d951bcf255401a6646e200e6e2f7`,
recovers AlphaBetaDuo (Li et al., IJCAI 2022 Algorithm 2) and the complete
relevant proofs from the official JIAF long version. The cited HAL v2 PDF
remains inaccessible, and equality with that unread version is not claimed.
Retrieval metadata is also retained as
`provenance/chapter27-cache-source-recovery.json` (byte-identical to the
reading-source provenance at SHA-256
`8c77bbd78dd6a798c5cc85be232e305009b2be43a393108c766ddbc773c5ecbe`).

Current inventory SHA-256:
`87ba6c9cbca1df75012cc594668ea1c7c0b76cfb76ea8e1cee9f7276e4e298e6`.
Its previous exact bytes remain at
`reviews/source-inventories-before-cache-recovery/chapter27-obligations.md`,
SHA-256 `4a7c5a4675822ac7ed0dad125be33b4eb637410ed04beaf8cc07da4672b22ea3`.
All 185 IDs are retained. C27-180–185 now specify the exact paired/stateful
recurrence, leaf-exact cache invariant, arbitrary-window squash relation,
global refinement and reuse contract, finite-computation correction and
source-proof repairs. They remain queued, unimplemented and unaccepted.
