# Chapter 1 recovery diagnostic — 2026-11-03

Read-only recovery analysis within the existing Chapter 1 implementation/review
loop. This report is not a final Standards or Spec review and grants no acceptance.
No source, Git ref, dependency, compiler, cache or old review record was changed.

## Identity and retained scope

- Original base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Repaired candidate: `07e480f6ec9958d4975bb90151005b84f2907614`.
- Main branch remains the earlier candidate
  `1aabd512284fe86254278ac631eda061d311050b`.
- Direct Git comparison confirms the original complete fourteen-path scope:
  `Applications/Arithmetic/EuclidInduction.lean`,
  `Applications/Resources/{CallComparison,CallCount,ListReversal,Measured,SharedDemand}.lean`,
  `Examples/{CallModels,FunctionalBasics,ListReversal,SharedDemand}.lean`,
  `SquareApplications.lean`, `docs/SOURCES.md`, and
  `docs/research/{fdsa-call-models,fdsa-reconstruction-map}.md`.
- Requirements remain the original chapter requirements and cost-model addendum.
  Their bytes/hash identities were recomputed and match the retained handoff:
  2672 bytes / `7b7ce18bcfe9bb888ac9e99810a1095a823f9a67dbb54717c5bf673017a890ba`,
  and 9471 bytes / `1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1`.

Applicable AGENTS, implementation, example-driven-development, shared review,
architectural/domain guidance, glossary, ADR 0001 and worked-example guidance
were read. The original requirements, addendum, retained Spec findings,
Standards report, repair source preflights and final-review handoff were read.
Source inspection used `git show` of the immutable repaired candidate; it did
not inspect a concurrently edited candidate checkout.

## What the repaired source supplies

| Retained finding | Source remedy observed | Remaining status |
| --- | --- | --- |
| SPEC-001: uniform fine/coarse comparison | `CallComparison.refinedCost_le` derives the whole-trace bound from per-entry bounds. `catalogue_refined_bounds` supplies a fixed finite maximum. Both real-cast Big-O directions retain a trace-independent constant. `Examples.CallModels` links actual append cost to branch events and the illustrative exact tariff `5*n+2`. | Implemented; still open for matching final review and validation. |
| SPEC-002: qualified entry omission | The pointwise bound retains `1 ≤ T`; the family theorem retains eventual positivity. The reverse comparison is unconditional. Tick value/cost connections, the zero example and the infinitely-often-zero family are present. | Implemented; still open for matching final review and validation. |
| SPEC-003: actual shared demand | `SharedDemand.request` is an option-cache hit/miss operation. Value validity is proved separately; repeated requests preserve and reuse cached values. Exact remaining-work conservation is derived from transitions and telescoped through existing `run_potential_exact`, then yields the eager-catalogue bound. Connected examples exercise repeated demand, skipped expensive work, preserved values, empty types and shared/unshared recursive duplication. | Implemented; still open for matching final review and validation. |
| SPEC-V001: complete candidate verification | No complete success or candidate verification JSON is present for the repaired candidate. | Unresolved. |

The three repaired models do not assume the desired whole-run inequality.
Finiteness belongs to local-body or eager-computation catalogues, not payloads.
The source and accompanying note retain the external-program correspondence
boundary, callback-work-only observation, zero-cost exception and absence of a
compiler/runtime/hardware theorem. No concrete new mathematical defect was
found in this bounded inspection. This is not an exhaustive renewed comparison
to the primary book: the excluded `book-source/chapter01.txt` is absent from
the recovery material, so the pinned source comparison is retained historical
evidence rather than freshly reproduced evidence.

The inspected delta from substantive repair `a14977b9e316cc484ffad8a470d26b15615956c0`
to `07e480f` changes only proof scripts in three files. The type signatures,
definitions, hypotheses and independent expected observations shown in that
delta are unchanged. Earlier source assessments can therefore be retained by
replacement reviewers as evidence, while still reviewing the whole scope and
matching final candidate. New source preparation is not currently justified
by any defect found in this diagnostic.

## Actual recovered validation evidence

The historical focused attempt 4 metadata records exit 0 and clean matching
candidate `07e480f` for four targets: `Applications.Resources.CallComparison`,
`Applications.Resources.SharedDemand`, `Examples.CallModels`, and
`Examples.SharedDemand`. The complete 3394-byte log was read; its recomputed
SHA-256 is `06cfb75ecf8a74fe25f48f3869cefe6359ab5d2ac4bad92c8beff0adc0e99ae9`,
matching the metadata. The final line records successful completion. This is
historical focused evidence, not a new build or full acceptance evidence.

The recovered full attempt 3 log is exactly 167645 bytes / 1024 lines, SHA-256
`53ddc9b5648b195561255ffafe6c2074dff92aa20e54ecb395511c922774870e`, matching
the saved root-read prefix record. Its recorder contains only historical
`result: running`, process identities and start fields. The expected
`provenance/chapter01-repair-attempt3-verification.json` is absent. Consequently
the archive supplies neither the actual terminal result nor a successful full
audit. Historical process handles or PIDs cannot be resumed from this recovery
workspace, and no terminal failure or success is inferred from their absence.

## Next useful action

Recover the pinned toolchain/dependencies and validate the unchanged immutable
candidate in an isolated checkout under the repository's existing rules.
Retain the unknown terminal outcome of the old run. A new run needs its own
record and log; no previous metadata should be overwritten. The full ordinary
guarded candidate check remains the prescribed route unless new concrete
evidence activates a different rule in the integrity-incident runbook.

After matching full success, resume the same logical review loop using the
retained records. Original agent names describe the previous conversation;
replacement coordinator and independent axes may be necessary. Keep the fixed
base, complete fourteen-path scope, both requirement records and all four open
Spec finding IDs. Both axes must pass the exact candidate, followed immediately
by `./check.sh --verify-candidate HEAD` before acceptance. Preserve the final
evidence in the acceptance checkpoint before Chapter 2 activation.

No additional readiness packet, new formal claim, source correction, repeated
optional regression suite or expansion of the frozen initial Chapter 2 prefix
is called for by this diagnostic.
