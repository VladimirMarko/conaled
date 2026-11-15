# FDSA-APP-A — List Library

State: accepted at f17cc6b; all twenty list-library entries covered; acceptance checkpoint saved/uploaded.
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

- [x] Item-by-item source coverage and reuse/gap map completed.
- [x] Definitions and proofs implemented without admissions or additional axioms.
- [x] Checked uses and statement review retained.
- [x] Applicable immutable-candidate build and exhaustive proof audit passed.
- [x] Independent Standards and Spec reviews have no unresolved findings.
- [x] Accepted candidate verified and recovery checkpoint saved/uploaded.

## Primary source links

No direct source hyperlink in the pinned PDF.

No completion is claimed until all gates above pass on the same candidate.

## Current candidate evidence

Candidate `333f900d04be3153518e68cc8c10920f40a08e05` includes the preserved
FDSA-X002 candidate plus `Examples.ListLibrary`, its public import, and the
complete Appendix A coverage/statement-review map. The isolated development
checkout is clean. Both focused builds passed; the final source version is
checked in `reviews/list-library-refined.log` (exit 0). It includes the
empty-domain minimum operation case as well as head/index failure on `Empty`.

The source inventory has all twenty entries in `research/appendix-a-obligations.md`.
The exact original requirements used for review are saved separately in
`reviews/list-library-requirements.md`, SHA-256
`83cffa5aff717943d449f4380189a9e9a761252730f5a14f4e392f1e62d154d4`.
No full candidate audit or final independent approval has occurred for this
foundation candidate.


## Accepted foundation continuation — 4 November 2026

Accepted and integrated locally at `f17cc6b1a2bf44215b16202ed0fcee2b5c130761`, from accepted Chapter1 base `07e480f6ec9958d4975bb90151005b84f2907614`. The original four-unit/nine-path scope and prefix c80eec92 are unchanged. The recovered full normal candidate check and exhaustive audit passed (967 checked project modules;45,294 kernel-safe declarations,25,117 theorems; only propext,Classical.choice,Quot.sound). These are whole-project counts. All145 actual public types were fully assessed by both independent axes with matching before/after inputs. Standards and Spec both passed with zero unresolved findings; FDN-ELAB-001/002 are resolved.

Qualified immediate `./check.sh --verify-candidate HEAD` passed at exactF before the local fast-forward at13:55:30UTC. The unrelated baseline file, tracked/index state and accepted Chapter1 history were preserved. No GitHub mutation or push occurred. The authoritative evidence and exact hashes are in `provenance/foundation-acceptance-20261104/acceptance.json`, with full/145/final-review/immediate/fast-forward records. Earlier development paragraphs above are historical, including interrupted or unknown-terminal attempts; their outcomes are not rewritten.

Acceptance checkpoint creation/upload is the remaining durability action; the combined checkpoint checkbox stays pending until that upload actually succeeds. No Chapter2, Chapter3 or other shared-unit acceptance follows automatically.

Accepted inventory coverage is A-001 through A-020, including all displayed cases and domain/boundary distinctions.


Durability completed 2026-11-04T14:08:43.703250+00:00: verified/uploaded checkpoint0109,22,290,443bytes,SHA949b1525e093857799316ea33e22f82cec9056abbd2ef393a1fa8657b04a1e08,libfile_84959da777948191832d2e322bf6fb16. The earlier pending-upload wording records the capture boundary. See provenance/foundation-acceptance-20261104/durability.json.
