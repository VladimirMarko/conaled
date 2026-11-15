# Chapter 2 Standards review — round 3

**Outcome: Blocked pending exact-candidate validation.** The retained independent
Standards reviewer has completed the full-scope static reassessment. There are
**zero new or unresolved code/prose findings**, no worst code/prose severity,
and no heuristic change requests. CH02-PRE-005 remains open, and the linked
IMPORT-VAL-004 repair still needs terminal compiler evidence. This report
approves neither Chapter 2 nor either prerequisite.

Reviewer: `/root/chapter02_review/standards`. Date: 2026-11-02.
This continues the existing Chapter 2 loop and preserves
[`chapter02-standards-r1.md`](chapter02-standards-r1.md). The round-2 candidate
was prepared between these reviews; this report does not invent an intervening
completed Standards outcome.

## Exact full scope

- Original fixed base and independently confirmed merge base:
  `82501d108f33c62d21b5e0d0f7d2376b902d8d49`.
- Candidate: `99a29dcd02eb529fbefbb675e244a8c47b78cdef`.
- Frozen checkout: `/workspace/scratch/ca9a61d0bf30/validation-chapter02-r3`.
  Observed HEAD equals the candidate and porcelain status is empty.
- Full diff: `git diff 82501d108f33c62d21b5e0d0f7d2376b902d8d49...99a29dcd02eb529fbefbb675e244a8c47b78cdef`.
- Full scope: **42 files, 39 Lean files, 33 commits, 4,468 insertions and
  4 deletions**. No unrelated changes or exclusions.
- `../validation/chapter02-candidate-r3.json` records the entire changed-file
  set and commit sequence. All **42 SHA256 fingerprints** independently match
  this checkout. Manifest SHA256:
  `e6b4991105910790cb24e6b2fb2f2ffacc8864ba4d5326808bdb1af235886b36`.
- Relative to previously reviewed `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4`,
  the entire difference is four added import lines in four additional files.
  The two intervening commits are `c372c470008cdda3043040683451662f61131f81`
  and `99a29dcd02eb529fbefbb675e244a8c47b78cdef`, both Conventional Commits
  with local ticket reference `#10018`.

The full source change, rather than only those four lines, is this review's
acceptance scope. The complete round-1 statement, architecture and connected
case assessment remains usable for the identical chapter files. Its conclusions
were reconsidered against the unchanged requirements and the import additions'
affected consumers. The old Blocked outcome is not promoted to approval.

## Requirements and standards identities

The saved requirements remain byte-identical to the prior review:

| Requirement | SHA256 |
| --- | --- |
| Original `REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `chapter02.md`, version 1 | `240b6bfec9f9e8599f1034abc309499928c8472edf76481b553ef99ce40ff944` |
| `import-footprint.md`, version 1 | `cf8fb3133b83ac59fdf6fd46b818d8b279d96385f5de50da843ef9b7fd62444d` |

Candidate AGENTS, README, GLOSSARY, architectural-quality and domain guidance,
review-loop, ADRs 0001/0010, example-driven-development, code-review and its
heuristics were independently confirmed unchanged. Their previously read
contents were applied again. The local-ticket and no-GitHub-write user override
continues to govern. No new interpretation framework, compiler frontend or
foundational architecture is introduced by these corrections.

`check.sh`, the Nix flake and lock, toolchain, Lake configuration/manifest and
`SquareApplications.lean` are also unchanged from round 1. The complete task
still requires stable isolated candidate validation, exhaustive audit, exact
record matching and both independent review axes. Nothing in this report
changes or bypasses that gate.

## Full chapter architecture and statement assessment

The Chapter 2 implementation, proofs, examples and three documentation files
are unchanged from the fully inspected round-1 snapshot. Consequently the
following substantive Standards conclusions remain applicable to this exact
candidate:

| Area | Retained assessment |
| --- | --- |
| Stacks and source integer update | Operation-only stack interface and separate relational laws have List/custom realizations, sufficient-fuel success and actual primitive counts. Signed update distinguishes negative traversal from an early rejection and reuses the checked nonnegative path-copy contract. Empty failures and successful empty results remain distinct. |
| Ordered sets and comparisons | Mathlib `BinaryTree`, independent whole-tree content, strict all-descendant ordering, finite contents and generic set clients remain separate. Existing fold fusion is reused. Actual baseline, candidate and combined recurrences justify their comparison measures; valid skew-tree instances establish the sharpness cases without assuming balance. |
| Shared heap execution | Existing store allocation and extension are reused without importing durability/crash assumptions. Backward references supply sufficient frontier fuel. Actual baseline and optimized traversals derive success, value representation, exact counts and retention. No final value equality is presented as address identity or zero allocation. |
| Endpoint and path contracts | `Rebuilds` retains opposite ancestor branches while leaving its focus unconstrained. The distinct duplicate endpoint theorem retains the matched nonempty root and every descendant observation. Map `WrittenAt` preserves both children at a changed endpoint. Connected examples distinguish these obligations. |
| General constructors and costs | `Fits` requires exact unfolded size, uniform contents and child-size balance throughout. Complete and paired executions use actual shared roots, with exact frontier and visit formulas. Standard asymptotic adapters preserve small-size conventions and model/runtime boundaries. |
| Maps and composition | Key-only ordering leaves payloads unconstrained. Pure independent observation, directed lookup, overwrite laws and finite-domain evidence remain separate. Actual bind/lookup, old/new observations and optional payload distinctions connect through existing ordinary and relational squares, with composed clients. |
| Integration and scope | All nine chapter example imports and their module closure remain present. Source mapping retains chapter/thesis ownership, unproved later obligations and contextual dispositions. No source manuscript, extra axiom, unsafe shortcut, disabled linter or altered audit policy is introduced. |

The prior detailed public-declaration/case matrix is retained in the round-1
report. Its assumptions, nonvacuous examples and composition connections have
not changed. The compiler still must establish the exact final imported
environment; byte preservation alone does not prove equality of elaborated
kernel artifacts or substitute for the integrated build.

## Four new imports and affected consumers

I independently inspected the new import commands, affected proof uses and
their actual pinned Mathlib providers. The Mathlib checkout is clean at
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

| Consumer and added provider | Assessment |
| --- | --- |
| `Applications/FRP/Demand.lean`: `Mathlib.Order.SuccPred.Nat` | Provides `Nat.instSuccAddOrder` and imports the successor arithmetic API with the simplifier rule `Order.lt_add_one_iff`. This is the missing context for the unchanged `pending_registered` strict-earlier-registration proof after `simp_all [next]`. Its strict conclusion, request provenance and response/fairness contracts are preserved. |
| `Applications/FRP/Finite.lean`: `Mathlib.Data.Set.Finite.Lattice` | Declares `Set.Finite.biUnion`, used by `finiteHistory` to combine finite timestamp support with finite local indices. The finite-history equivalence and stable ordered-batch clients are unchanged. |
| `Examples/FRP.lean`: `Mathlib.Algebra.Order.Archimedean.Real.Basic` | Supplies the real Archimedean instance and imported natural-upper-bound API used by `ticks_finiteHistory`. The existing infinite-future/finite-history example and its bound argument are unchanged; no global finiteness assumption was added. |
| `Examples/IndefiniteService.lean`: `Mathlib.Data.Nat.Size` | Declares `Nat.size_pow : size (2 ^ n) = n + 1`, exactly the existing unbounded-size example's rewrite. The witness `2^bound` and contradiction of `bound+1 ≤ bound` remain. Existing finite-trace, stream, resource, compiled-delay, productivity and relational-transport cases are unchanged. |

For all six import consumers, including the two originally narrowed files,
removing only import lines leaves the same bytes as round 1. Each entire
consumer file is byte-identical to prerequisite candidate
`901f734161920a76f3b399a575805b9a1d31e971`. The original Spec/Equivalence header
assessment therefore remains applicable alongside these explicit consumer
repairs. No body, statement, option, expected example, public integration,
dependency pin or check implementation was weakened.

These additions are direct provider repairs within the saved import
requirement. They introduce no new all-library aggregate. This assessment
does not assert a memory or timing improvement, or that no further transitive
consumer failure can be found by the full build.

## Retained findings

| Stable ID | Standards disposition on this candidate |
| --- | --- |
| CH02-PRE-001 | Static implementation closure retained and verified: unchanged endpoint/descendant theorems and meaningful terminal cases. |
| CH02-PRE-002 | Static implementation closure retained and verified: unchanged actual abort/combined execution, original-state duplicate result, zero-cell count and same-run comparison contract. |
| CH02-PRE-003 | Static implementation closure retained and verified: unchanged `WrittenAt` execution contract and replacement-child example. |
| CH02-PRE-004 | Static implementation closure retained and verified: unchanged observation adapters and composed clients through the existing interfaces. |
| CH02-PRE-005 | **Open mandatory chapter gate.** Frozen source identity is established, but exact full chapter validation, exhaustive audit, success record and final verification are absent. |
| IMPORT-VAL-001 | Direct successor provider is statically justified and fixed with independently matched focused compiler evidence; full candidate gate still pending. |
| IMPORT-VAL-002 | Direct finite-union provider is statically justified and fixed with independently matched focused compiler evidence; full candidate gate still pending. |
| IMPORT-VAL-003 | Real Archimedean provider is statically justified and fixed with independently matched focused compiler evidence; full candidate gate still pending. |
| IMPORT-VAL-004 | **Proposed repair statically supported; terminal compiler verification pending.** Preserve the observed missing `Nat.size_pow` failure and unsolved goal in the preceding candidate. Do not infer successful compilation from provider inspection or an interrupted run. |

PERSIST-VAL-001's previous fixed disposition remains preserved in the separate
prerequisite loop; no SharedList code changed here. This chapter review does
not retroactively accept that prerequisite. The independent Spec axis retains
its own dispositions; these are Standards assessments only.

## Validation evidence and interruption boundary

The successful `../validation/import-footprint-r2-focused-r2.json` record has
exit code 0, equal before/at-start/after maps and `inputs_unchanged: true`.
I independently matched all **23 recorded source/config hashes** to this
Chapter 2 checkout. The preserved log ends `Build completed successfully
(1134 jobs)`. It covers `Examples.FRPDemand` and `Examples.FRP` under the pinned
offline Nix environment. Its development HEAD field names `226ebae`, but the
explicit corrected input bytes match the current candidate. This supports
IMPORT-VAL-001..003 without turning that focused run into chapter approval.

The previous `324962e` full check observed IMPORT-VAL-004; its exact compiler
diagnostic remains in
`../validation/import-footprint-324962e-observed-errors.json`. The later
`../validation/runtime-interruption-20261102-2240.json` records loss of the
owned full-run session without a terminal result and exact-cwd liveness
observations. It does not establish an OOM, Lean crash or integrity cause.
The owning focused worker's subsequent
`../validation/import-footprint-r3-focused-interruption-r1.json` confirms that
its session disappeared before the repaired target compiled, without a terminal
exit or target success. Its source check still matched all 60 saved inputs.
At inspection the automatic focused record likewise has no terminal
exit/end/after evidence. Those observations establish no successful run and
close no validation finding.

Root has now started the unchanged stock full gate on prerequisite `901f734`;
`../validation/import-footprint-901f734-full-r1.json` records the command and
start at 22:44:09 UTC with status running and acceptance false. Its ordinary
cache-recovery record is `../validation/import-footprint-r3-cache-copy.json`.
Recovery of ordinary outputs is not a copied approval. This is still a
different candidate from the Chapter 2 integration and has no supplied terminal
success at this review.

The preserved Chapter 2 family-focused evidence remains development evidence
with the identities and qualifications already reviewed in round 1. Earlier
constructor/physical-map observation snapshots predate the optional root
observer addition; later focused records cover that final observer. Neither
these runs nor any future successful prerequisite check can approve this
different complete chapter candidate.

At this review, `validation-chapter02-r3/.lake/verification.json` is absent.
No successful full `99a29dc` build/audit or final verify evidence has been
supplied. Required acceptance remains `./check.sh --candidate HEAD` on this
stable isolated candidate, followed by its matching success record and
immediate `./check.sh --verify-candidate HEAD`, with both axes Passed on the
identical complete candidate. No copied prior success record suffices.

## Continuation and final result

For unchanged `99a29dcd02eb529fbefbb675e244a8c47b78cdef`, provide complete exact
validation and final verification evidence through the retained coordinator.
This full static assessment can be reused while the new terminal evidence is
assessed. Any source correction requires another immutable candidate and
full fixed-base reassessment carrying all stable findings.

I performed only read-only source/evidence inspection and wrote this assigned
report. No compiler, process signal, source/ref/index/dependency change, or
build-output mutation was performed.

**Standards outcome: Blocked.** **Code/prose findings: 0; worst severity: none.**
The remaining barriers are CH02-PRE-005 and linked IMPORT-VAL-004's pending
terminal evidence. Fixed base:
`82501d108f33c62d21b5e0d0f7d2376b902d8d49`. Candidate:
`99a29dcd02eb529fbefbb675e244a8c47b78cdef`.
