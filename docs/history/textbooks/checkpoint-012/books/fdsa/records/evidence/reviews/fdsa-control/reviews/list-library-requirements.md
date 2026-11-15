# FDSA-APP-A — List Library

State: active cross-cutting foundation; acceptance pending.
Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, printed pages 343–345 (346 is blank).
Depends on: FDSA-001 acceptance before integration/acceptance.

This uses the user's cross-cutting exception for shared list interfaces. It does
not advance or accept the sequential chapters. Development branch
`work/fdsa-list-foundations` starts from the saved insertion-cost candidate
`697bcf242ce65d74815b5639bddb1c6e754dd10f` in the existing isolated
`conaled-insertion-costs` worktree. The related insertion work remains preserved
on its original branch. Combined foundation review uses fixed base
`1aabd512284fe86254278ac631eda061d311050b` and includes both exact ticket scopes;
the additional source diff relative to 697bcf2 is Appendix A only.

## Scope

Cover every mathematical construction, theorem and exercise in this source unit,
with exact scope and reusable existing declarations inventoried before implementation.
Preserve the book's assumptions and cost model; harmonize with conaled interfaces.

The complete value-level scope comprises length, append, set membership, map,
filter, concat, take, drop, head, tail, butlast, reverse, zero-based indexing,
list update, half-open natural ranges, replicate, distinctness, sum, nonempty
minimum and sortedness for an arbitrary relation. Reuse their standard
definitions and exact equation theorems, with an item-by-item map and meaningful
checked clients. Do not introduce a parallel list representation.

- For source `hd`, indexing and minimum outside their specified domain, use
  existing Option or proof-domain APIs and prove agreement on valid inputs.
  Do not impose `Inhabited` on all payloads or invent an arbitrary default.
- Preserve total empty/out-of-range behavior of tail, take, drop, butlast and
  list update; preserve inclusive/exclusive range endpoints.
- Expose necessary algebraic assumptions for sum and minimum recurrences.
  Distinguish arbitrary relation sortedness from linear-order instances.
- These are value equations. Existing optimized realizations do not inherit
  the source's execution costs by output equality; Chapter1 handles reversal
  costs and AppendixB retains the remaining tariff obligations.
- Retain checked boundary/composition cases, including an empty payload type,
  duplicate values, valid/invalid indexing and updates, half-open ranges and
  minimum with repeated values. Record per-claim statement review.

## Completion gates

- [ ] Item-by-item source coverage and reuse/gap map completed.
- [ ] Definitions and proofs implemented without admissions or additional axioms.
- [ ] Checked uses and statement review retained.
- [ ] Applicable immutable-candidate build and exhaustive proof audit passed.
- [ ] Independent Standards and Spec reviews have no unresolved findings.
- [ ] Accepted candidate verified and recovery checkpoint saved/uploaded.

## Primary source links

No direct source hyperlink in the pinned PDF.

No completion is claimed until all gates above pass on the same candidate.
