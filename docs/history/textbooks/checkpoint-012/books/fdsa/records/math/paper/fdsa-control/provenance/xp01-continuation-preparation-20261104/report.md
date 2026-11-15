# XP01 continuation preparation — read-only source and evidence inventory

Recorded 4 November 2026 by `/root/shared_acceptance_sequence` for root's next
checkpoint. This report preserves a completed bounded investigation. It is not
implementation, compilation, an independent final review, acceptance, or a new
mathematical preflight. Only this new provenance package is authorized for writing.

## Ordering and acceptance boundary

Accepted Chapter 1 remains R=`07e480f6ec9958d4975bb90151005b84f2907614`.
The current mandatory acceptance sequence remains:

1. Exact foundation F=`f17cc6b1a2bf44215b16202ed0fcee2b5c130761`.
2. The declared combined XM01 / XD01 / XQ01 / XU01 candidate, retaining each
   unit's complete original scope, requirements and review/finding records.
3. XU02, with its predecessor acceptance requirements.
4. XU03, with its predecessor acceptance requirements.
5. Complete Chapter 2, including all retained obligations and full gates.

Chapter 3 remains queued until Chapter 2 acceptance and its acceptance checkpoint.
This XP01 preparation does not insert a prerequisite into that sequence or
activate Chapters 3 or 19–23. XP01 remains the already recorded shared exception;
its own source, compatibility, review and acceptance requirements are unchanged.

## Exact saved draft and included paths

The saved XP01 draft is `c28ba71863d2a35ee1c3a089caa90464e4cca692` on
`work/fdsa-list-foundations`. Its only parent is
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`. The subject is
`feat(resources): generalize potential accounting (#174)`.

The single XP01 commit changes these six paths. Full blob/SHA-256/size identities
are retained in `receipt.json`; all source was read through immutable Git objects.

| Path | Included change |
| --- | --- |
| `Applications/Resources/Potential.lean` | Generalizes the existing trajectory budget and adds mapped, invariant-aware and signed accounting laws. |
| `Applications/Resources/FIFOContracts.lean` | Annotates the discarded raw work in `abstractBudget` as `(0 : Nat)`. |
| `Examples/MappedPotentialAccounting.lean` | Adds counter, initial-credit, fractional-validity and ordered-observation clients. |
| `SquareApplications.lean` | Imports the new example through the public entrypoint. |
| `docs/research/fdsa-potential-accounting.md` | Records source correspondence, capability assumptions, cases and limits. |
| `docs/research/fdsa-reconstruction-map.md` | Adds shared preparation coverage while Chapter 19 remains queued. |

Read-only `git merge-base` results for the XP01 draft were:

| Other immutable candidate | Merge base |
| --- | --- |
| Accepted R=`07e480f6ec9958d4975bb90151005b84f2907614` | `1aabd512284fe86254278ac631eda061d311050b` |
| Exact F=`f17cc6b1a2bf44215b16202ed0fcee2b5c130761` | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Central snapshot=`8ba7ae11a657e8a4af025f60b4e1a54dddb3c512` | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |

The original combined `1aabd512…` to `c28ba718…` scope has 13 paths, including
the foundation prefix. The current foundation continuation explicitly separates
that first prefix from XP01; it does not waive the later scope. The retained
integration preflight calls for preserving saved histories and accepted
corrections. A later affine tip must not be used to bypass XP01, which is already
included in that saved ancestry. No merge, cherry-pick or merge simulation was run.

## Compatibility facts and required future checks

R, F and central `8ba7ae11…` all retain old Potential blob
`82e8613245bbdc5db45507e84ccf7b7cb9d694b1` and FIFOContracts blob
`51a45acf742f9e984188094bb72d3744e9f6e19b`. XP01 instead contains Potential blob
`3ffc5e120f94f87c77a442728f654f3fa94d3aeb` and FIFOContracts blob
`01839707e852b3faff6ef1a49ad88a76fb5e5c18`. Thus the present foundation and
Chapter 2 builds do not elaborate XP01's generalized implementation.

The statement texts of these eight retained Nat contracts compare byte-for-byte
equal across `c80eec9…` to `c28ba718…`: `run_potential`,
`run_potential_exact`, `run_cost_le`, `run_zero_potential`,
`run_constant_charge`, `budget_constant`, `budget_le_constant` and
`charge_iff_signed`. This is source comparison, not printed-type or elaboration
evidence. `Measured.lean` and `Workload.lean` are unchanged across the XP01 change.

| Existing client | Compatibility obligation retained |
| --- | --- |
| `FIFOContracts.abstractBudget` | Keep the explicit Nat raw-zero annotation and existing abstract trajectory/charges. |
| FIFO refinement, append and sequential bounds | Preserve unfolding shapes, observation refinement, initialization credit and retained boundary potentials. |
| `BinaryCounter` | Preserve actual `incWithCost`, exact telescope and constant-budget connections. |
| `SymmetricCosts` | Preserve both source-charge and structural-work uses of `run_constant_charge`. |
| `RandomAccess.End` | Preserve its exact potential and `budget_constant` application. |
| Existing natural potential/FIFO examples | Preserve their contracts and simplification shapes. |
| Accepted `SharedDemand` core and examples | Recheck the actual caller under the generalized implementation; source preservation does not establish compatibility. |

Accepted `Applications/Resources/SharedDemand.lean`, blob
`449d7fce653a449be11209c4cb8cb23ae1240609`, imports Potential. Its
`run_work_remaining` calls `run_potential_exact` and simplifies with
`budget_constant`; the cost bounds and connected examples use that result.
The repaired SharedDemand files were absent from the old XP01 branch and must
survive reconciliation with accepted R. No change to their mathematical meaning
is proposed. Their actual rebuild is required even if the source merge is clean.

## Existing assessment, findings and secured-evidence limits

`research/potential-draft-preflight.md` already assessed immutable `c28ba718…`
against the frozen requirements and reported no mathematical or public-contract
blocker. It explicitly requested no source change, while leaving proof-term
elaboration and downstream compilation unverified. That completed bounded
assessment is retained; this investigation does not repeat it or promote it to
an independent final review.

The preserved assessment covers the split raw/charge carriers, ordered additive
boundary laws, invariant-local laws, signed commutative-group charge, natural
wrappers and these connected cases: the existing counter transported from its
local law, actual negative charges and initial credit, fractional potential on a
preserved nonempty domain with an invalid-state counterexample, and ordered
free-monoid observations. Later algorithms and binary-input ownership histories
remain outside this shared unary accounting extension.

`reviews/shared-foundations-validation.json` is the original combined historical
record. It binds `c28ba718…` and all five original requirement hashes, states that
XP01 has no focused compile result and that full gates and independent final
review are pending, and contains empty `gates` and `accepted_units` arrays. Its
historical Chapter 1 prerequisite status is superseded by accepted R; its missing
XP01 validation is not superseded.

`reviews/shared-foundations-round1.md` explicitly excludes later XP01 from exact
F's first-prefix scope. Its independent foundation source assessments and
FDN-ELAB-001/002 dispositions are not XP01 review or validation. No XP01-specific
final independent Standards/Spec pair or concrete open compiler finding was
identified in the inspected XP01 records. This report asserts an evidence gap,
not a newly discovered source defect.

The bounded absence-of-evidence search was `rg -l` for the complete XP01 commit
SHA in `fdsa-control/provenance`, restricted to files named `result.json`,
`native-result.json`, `acceptance.json` or `verification.json`. It returned no
matching path (exit 1). This is not a search of every historical log, arbitrary
record name, external system or other conversation. No running process was polled.

## Concrete next steps when root schedules XP01

1. Preserve the current acceptance sequence above and the completed old
   mathematical preflight. Do not reopen implementation without a source or
   elaboration gap that warrants it.
2. On the appropriate then-accepted base, prepare a distinct immutable XP01
   candidate retaining R, foundation corrections and all six XP01 changes.
   Compare with both the accepted base and original saved scope; preserve saved
   refs and record any resolution. This report performs no assembly.
3. Reconcile public imports and both documentation files without overwriting
   accepted coverage. The original note and map have present-tense draft/pending
   wording: before freezing the future candidate, record accurate dated
   development history so later acceptance does not itself require a status
   commit. Keep mathematical prose and mandatory gates unchanged.
4. Obtain actual focused elaboration for the generalized implementation and
   connected compatibility targets. Concrete existing examples are
   `Examples.MappedPotentialAccounting`, `Examples.PotentialAccounting`,
   `Examples.FIFOContracts`, `Examples.RandomAccessEndCosts` and
   `Examples.SharedDemand`, with the core dependencies. The natural potential
   example imports the existing counter and symmetric workload.
5. Inspect actual fully explicit printed types on that same candidate, especially
   carrier/universe assumptions, the retained Nat contracts and connected uses.
   Source-text equality and prepared programs alone give no type-output credit.
6. Complete the applicable full guarded check and exhaustive proof audit, securing
   actual exits, complete closed logs and matching candidate evidence. Apply the
   README's normal/fresh criteria; this preparation creates no fresh-build trigger
   and does not remove any applicable gate.
7. Obtain independent Standards and Spec outcomes over the full declared scope,
   retaining original requirements, findings and the old bounded assessment.
   After all gates pass, run immediate qualified candidate verification before
   exact integration, accurate local tracker updates and an acceptance checkpoint.

No unary accounting theorem supplies binary-input ownership histories,
persistent-alias credit, later algorithm-specific potentials or complexity bounds.
Those original chapter obligations remain open.

## Honest read boundary and author readback

Fully read in this investigation: the 48-line XP01 ticket; 116-line frozen
requirements; 321-line design preflight; 90-line draft preflight; 216-line current
foundation round record; 44-line historical validation JSON; and the 163-line
draft public potential note. Read the complete XP01 diff for Potential,
FIFOContracts, the public import and reconstruction mapping. Read immutable
declaration inventories and all eight retained Nat statement comparisons, selected
accepted SharedDemand call-site contexts and selected compatibility imports/calls.
The relevant shared-integration-preflight sections were reread; its full 205-line
contents had already been read during the earlier shared-acceptance preparation.

An initial batched output was truncated; both potential preflights were reread in
complete, nontruncated outputs before the findings were delivered. A separate
large, unrelated 110-type reuse record was only partially displayed and is not
claimed as fully read or as XP01 evidence. The new example's complete proof bodies
were not reassessed here; the preserved draft preflight owns that earlier bounded
assessment. No new source/math-review result is claimed.

The final report is read back in full before the compact receipt is finalized.
Only the two files in this new provenance package are written. No source, ref,
ticket, existing control/review report, worktree, compiler, cache, output or process
mutation is authorized or performed. HOLD follows the completed package.
