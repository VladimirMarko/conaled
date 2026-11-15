# Chapter 1 cost-model repair candidate handoff

Recorded 2026-11-02.

- Original review base: `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Prior candidate: `1aabd512284fe86254278ac631eda061d311050b`.
- Repair draft: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Branch: `work/fdsa-basics-cost-models`.
- Development checkout: `conaled-ch01-cost-models`; clean after commit.
- Commit: `feat(resources): compare FDSA call observations (#174)`.
- Frozen addendum: `chapter01-cost-model-requirements.md`, SHA-256
  `1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1`.

The original `chapter01-requirements.md`, full `../REQUEST.md`, original base
and all retained findings remain in force. The review scope is the entire
chapter from the original base, not just the most recent seven-file repair.
The original obligations snapshot is preserved as `chapter01-obligations-round1.md`;
the live inventory explicitly corrects its earlier source-scope dismissal.

## Repair contents

`Applications/Resources/CallComparison.lean` defines an occurrence-list tariff
and derives uniform local/finite-catalogue bounds and both asymptotic
directions. It also supplies the positive and eventually positive entry-unit
comparisons with their unconditional reverse directions. `Examples.CallModels`
connects the actual append count to an explicit branch trace and tariff,
retaining empty and duplicate cases, and refutes the insufficient
non-identically-zero hypothesis with an intermittent family.

`Applications/Resources/SharedDemand.lean` defines pure callback requests
through an option cache, separates validity and demanded values from work,
preserves stored entries through arbitrary prefixes, and derives exact
remaining-work conservation and the eager-catalogue upper bound through the
existing executor/potential interface. `Examples.SharedDemand` retains
repeated and skipped work, equal values under distinct identities, arbitrary
payloads, an empty catalogue with empty payload type, and actual shared/eager
single-bind versus unshared double-bind recursive computations.

The public application root imports both example modules. The reconstruction
map and new `docs/research/fdsa-call-models.md` identify the source claims and
conditional interpretation. No compiler/runtime/hardware stack or blanket
external-language simulation is asserted.

## Statement review and source preflight

Root's implementation-side assessment is
`chapter01-cost-models-author-review.md`. The architecture contributor's
bounded read-only pass separately inspected the tariff and entry statements,
actual append bridge, counterexample and pinned supporting APIs. It reported
no mathematical blocker or definite API mismatch. Relevant source hashes:

| File | SHA-256 |
| --- | --- |
| `Applications/Resources/CallComparison.lean` | `e7abd72465ebcb5eca87afe6812626dd0690ed284ceef3753727a22c0e190905` |
| `Examples/CallModels.lean` | `0eccc57807372e8612828be6737256bf6c3c9d099a163685be22b23c0d2f8aa1` |
| `Applications/Resources/SharedDemand.lean` | `c9740655b7afb51b28b044f1a72006d7a393b74a3e60e2f26464dc7eca7ee996` |
| `Examples/SharedDemand.lean` | `73f4cfc1c3a8ee5bddd37ec4bc1937d66dd08f6eae4e35a25849e860b42a10d2` |

The contributor checked the pinned `Finset.le_sup`,
`Asymptotics.isBigO_iff`, `Real.norm_natCast` and
`Filter.eventually_atTop` signatures and the existing
`Resources.isBigO_of_nat_bound` proof pattern. The author inspected the cache
transition and every connected case. These source passes did not run Lean
and do not replace retained independent Standards and Spec review.

The retained independent Spec reviewer later performed a narrow source pass
on this exact commit, recorded in `chapter01-cost-models-spec-preflight.md`.
It found no mathematical statement/source issue in the three repairs and
assigned no supplemental finding. This did not inspect elaborated signatures,
run Lean or provide final approval. All retained findings and validation
blockers remain unresolved; final review still requires a validated candidate.

The retained independent Standards reviewer subsequently inspected the full
repaired candidate against the original base, carrying prior analysis only
for byte-unchanged paths. Its bounded source assessment found no new concrete
Standards issue. Report: `chapter01-cost-models-standards-preflight.md`,
SHA-256 `fdb52f4e70c8ef36d4b9bbfd37ed0684d5b271dc937bf0dbfec1d82fc79adcdb`.
Final Standards remains Blocked and all retained Spec findings remain open;
this source assessment does not validate elaboration or close a gate.

A separate bounded SharedDemand API preflight is retained in
`chapter01-shared-demand-api-preflight.md`. It inspected the executor,
potential, update, finite-sum and repeated-request interfaces and found no
concrete likely mismatch. It ran no compiler and is neither an additional
Standards/Spec review nor final approval.

## Validation boundary and next step

`git diff --cached --check` passed before commit. No focused compilation,
whole-candidate check, exhaustive audit, axiom summary or candidate success
record exists for the repair. SPEC-001/002/003 remain unresolved pending
review of the actual validated candidate; SPEC-V001 remains unresolved.

The frozen old-candidate guarded check continues unchanged in
`conaled-ch01-review`. Collect its exit status and any success record first.
Its source and required gates must not be changed during the run. Once idle,
reuse that isolated checkout and its normal Lake outputs for this repaired
candidate. Complete focused elaboration and applicable whole-candidate
verification under the pinned Nix environment, then supply matching evidence
to the retained coordinator `/root/chapter01_review` and its two axes.

Any elaboration correction requires a new commit and matching evidence. Only
both independent passing outcomes on the same final candidate plus immediate
`--verify-candidate` permit acceptance. Even a successful old-candidate check
cannot close the reopened source findings. No chapter or appendix is accepted
by this draft or this handoff.
