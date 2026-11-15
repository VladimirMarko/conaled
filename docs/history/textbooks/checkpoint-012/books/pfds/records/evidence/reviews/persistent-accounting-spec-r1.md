# Local 10021 — independent Spec review, round 1

Reviewer: `/root/persistent_accounting_review/spec`, 2026-11-03.
This reviewer did not implement the change, coordinate the Standards axis, or
read the Standards report before submitting this report.

**Outcome: Blocked.** There are **0 static mathematical or requirements findings**
and **1 unresolved Blocking validation finding**, PERSIST-ACC-SPEC-VAL-001.
The bounded foundation is not accepted. This review does not accept Chapter 2,
any later chapter, task 10017, or the whole book/thesis union.

## Immutable complete scope

- Bounded base: `3dd930c3e3989f3e5530463f3ac937a629551335`.
- Original full integration base: the same exact commit.
- Candidate: `577be121e074ddb5de6727a7481c115cb61b3b27`.
- Merge base: `3dd930c3e3989f3e5530463f3ac937a629551335`.
- Checkout: `/workspace/scratch/ca9a61d0bf30/validation-persistent-accounting`.
- Branch: `pfds/persistent-accounting-review-r3`.
- Scope: all 11 changed files and all 5 commits; no exclusions.

The checkout was observed clean at the pinned candidate. Scope was inspected
with the supplied three-dot diff, whose base is an ancestor of the candidate.
All 11 file hashes in `validation/persistent-accounting-candidate-r3.json`
matched the files read from that checkout. The commits, in order, are:

1. `dc16a3b457b0393bb94188269fa3749deef39657`
2. `c6f96cfc6d3ef6f715e72206c1b69359af4928fc`
3. `eedaeca6fc2fcc3f73cb92630dc8d8acf2bd50f8`
4. `eb61c35f911ad0fac36758c878559eaf5f795cfa`
5. `577be121e074ddb5de6727a7481c115cb61b3b27`

The complete changed file set is:

- `Applications/Resources/Persistent/History.lean`
- `Applications/Resources/Persistent/Debits.lean`
- `Applications/Resources/Persistent/Realization.lean`
- `Applications/Resources/Persistent/Observation.lean`
- `Examples/PersistentHistory.lean`
- `Examples/PersistentDebits.lean`
- `Examples/PersistentRealization.lean`
- `Examples/PersistentObservation.lean`
- `Examples/PersistentSourceBoundary.lean`
- `SquareApplications.lean`
- `docs/research/pfds-persistent-accounting.md`

## Requirements and review evidence

The governing bounded requirements are
`requirements/persistent-debit-foundation.md`, version 1, SHA256
`2a89d7818d73e0b1b118ebf7d902a75afb2b6e25afaae6b9c7842d229964922f`.
The digest was independently read and matched. The complete user requirements
in `requirements/REQUEST.md` and `requirements/REQUEST-union-v2.md` were also
read. Their respective hashes are
`b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499`
and `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c`.
The review follows `reviews/persistent-accounting-577be12-dispatch.md` and the
existing implementation/review record; this is its first independent Spec axis.

Applicable candidate guidance was read through AGENTS, the README environment
and build/audit sections, the shared review procedure, example-driven development
and its worked example, architectural/domain/glossary guidance, relevant ADRs
0001/0006/0010, language direction and review heuristics. The user explicitly
replaces GitHub tracking with local records. No external tracker action occurred.

Every changed core, client and public document was read. Relevant unchanged
dependencies were inspected, including `Resources.Measured`, `Resources.Workload`,
the finite pure source cache-count theorem, and the actual repeated-force and
handled-exception source clients in `Examples.SuspensionPureCacheCounts`.
The three persistent implementation handoffs were read as author evidence;
their historical pending/failure descriptions are superseded by their appended
completion records, not silently erased. They did not replace inspection of
the actual definitions and proof connections.

The source comparison used the supplied source identities, the frozen
`persistent-trace-source-scope.md` and reuse evidence, and independently read
the existing extracted text for the complete bounded passages: book printed
57–63, PDF 69–75, and thesis printed 19–24, PDF 31–36. The source note preserves
the earlier visual inspection of decisive graph definitions and formulas.
This reviewer did not claim a new visual rendering check or a whole-chapter
source inventory. The two sources agree on the abstract graph and set/multiset
argument used here. Their concrete algorithm and timing obligations remain
outside this bounded child task and explicitly owned by task 10017.

## Requirement coverage and statement review

| Requirement | Candidate evidence and assessment |
| --- | --- |
| Unrestricted operation-history graphs | `history` is nonempty finite `Quiver.Path u v` with the required direction and empty path. No acyclicity, thinness, finite vertex universe, one-identity or one-predecessor restriction is imposed. The History clients retain distinct parallel arrows, a loop, a two-node cycle, a join with two inputs/results and an explicit cross-identity dependency. |
| Reflexivity, path/edge inclusion, transitivity and maps | Public `history_refl`, `history_of_path`, `history_of_edge`, `history_trans` and `history_map` use ordinary Mathlib path operations. Connected cycle/join/map clients exercise them. Map preservation asserts only the forward history implication. |
| Separate finite scope closure | `HistoryClosed` requires every logical predecessor of every member to remain in scope. Empty/union/intersection closure is supplied. Full and open cyclic scopes establish satisfiable and failing cases; no finite closed scope is asserted to exist for every graph. |
| Source conditions I, II and III | `Fresh`, `Allocated` and `Paid` are separate propositions; `Discipline` is an optional bundle. Allocation labels are unrestricted sets, while discharge and realization labels are multisets. II and III quantify over support membership with explicit witnesses, retaining the source's treatment of duplicates. |
| Allocation provenance and uniqueness | `realized_origin` composes the II and III history witnesses. `allocation_origin_unique` uses freshness without an irrelevant graph premise. `realized_origin_unique` combines existence and uniqueness. The Parallel client establishes a unique concrete origin. |
| Finite realized-support bound | `paidWithin_of_closed` derives an in-scope discharge witness from `Paid` and closure. `realized_support_subset` derives inclusion; the cardinality result composes finite-set monotonicity with `supportUnion_card_le`. The desired global inequality is not substituted for the local source law. |
| Open-scope boundary | `PaidWithBoundary` retains an actual discharge in the realizing operation's logical history and requires either an in-scope witness or membership in the explicit boundary. `realized_card_le_boundary` retains the boundary cardinality. The cyclic client supplies the omitted witness and exhibits realized 1 versus internal discharge 0. |
| Finite allocations and realized/unrealized partition | `allocationUnion_card` uses freshness only where disjointness is needed. Realized inclusion uses II, III and closure. `unrealizedDebits` is the allocated union minus realized support, not the complement in the entire debit universe. Parallel allocation of 7 and 8 realizes only 7 and leaves exactly 8 unrealized. |
| Injective renaming | Ordinary embeddings, set images, multiset maps and finite-set maps transport the source discipline and support/cardinality observations. Provenance/payment and discharge multiplicity intentionally need only a function; freshness and support-cardinality preservation retain injectivity. Generic Parallel renaming and the concrete 7-to-17 measured run exercise the transports. |
| Existing measured executor and exact balance | `realizeStep` adapts the unchanged `Resources.run`: charge is unshared work plus newly encountered support, and state unions that support into `seen`. The step/run identities retain the initial and final cardinalities without truncated subtraction. No second executor or additive finite-set-cardinality instance is introduced. |
| Same-run finite-node bound and initial state | `realize_run_cost_of_enumeration` uses both `Nodup` and exact `toFinset` equality to replace the unshared list sum by a finite-node sum. Closed and boundary bounds apply to that same measured run. Separate seen-support bounds and the exact identity retain initial-state effects. |
| Composition and enumeration counterexample | Clients use the existing `run_append` theorem with the intermediate support state. The legal fork costs 4. Repeating its left node costs 5 while preserving the same finite scope and budget 4; the client explicitly proves failure of `Nodup`. |
| Source boundary and exceptional retry | `PersistentSourceBoundary` reuses actual source event-count theorems. Repeated successful force agrees with the abstract one-address charge on its body-entry count. The handled retry has two body entries and zero successful writes, exceeding the same abstract charge 1. No general body-work or transition-count correspondence is inferred. |
| Public integration and explicit remaining work | `SquareApplications` imports all four new core modules and all five new clients. Public documentation states the exact abstract scope, chronology boundary and outstanding task 10017 work. The tracker retains task 10017 and TU.TRACE as open/unproved, and the foundation row as unaccepted. |

### Mathematical assumptions and nonvacuity

The basic graph admits distinct vertices in one another's histories. Consequently
history membership does not imply temporal order or antisymmetry. The final
documentation correction accurately states what the boundary law provides:
a supporting discharge outside the finite scope, with temporal correspondence
still to be proved for a concrete evaluator. It does not revive the earlier
ambiguous suggestion that graph membership alone proves chronologically prior
payment.

The aggregate numerical bound properly needs less than the entire source
discipline. `Paid` and history closure suffice for it; freshness and allocation
provenance remain separate requirements for faithful labels and for the stronger
origin/partition conclusions. The independently labelled examples make the
distinctions nonvacuous: invented allocation fails II despite III, duplicate
allocation fails I, and globally sufficient incomparable payments fail III.
The public `PaidWithin` numerical helper is explicitly named and is derived
from local source legality in the principal history theorem.

Multiset multiplicity and support cardinality remain different observations.
Parallel realizes the same debit twice at one operation, while Fork realizes it
in two logical branches. The former has support 1 and discharge multiplicity 2;
the latter has support/discharge 1 but realization multiplicity 2. These expose
the source's memoization/call-by-name distinction without assuming disjoint
realizations or discharges.

The realized-work interpreter is a definition with an exact proved observation
law. It is not presented as an already-proved cost model for arbitrary source
programs. Its unshared sum counts list occurrences. A repeated operation label
is not silently reinterpreted as a distinct source occurrence when invoking
the finite-node theorem. `Nodup` and exact enumeration make that boundary
explicit, and the duplicate-fork client shows its concrete consequence.

Boundary credit and initially realized support are independent. The open-cycle
bound has external credit 1 and internal payment 0 but still charges realization
1. Starting with the debit in `seen` reduces that charge to 0. The boundary
predicate still supplies a real history witness; merely inventing a boundary
name cannot provide the missing discharge. An arbitrary boundary may overpay
the bound, but no theorem asserts that every unused boundary member itself has
been discharged or realized.

The source retry counterexample is connected to the original observation of the
same concrete program/capture/parameters. The new theorem obtains the two body
entries and zero writes from the existing public result, while independently
deriving the abstract charge through `realize_run_cost`. It does not erase
exceptions from the source model or convert cache-write uniqueness into body
attempt uniqueness. The positive case is explicitly limited to the selected
body-entry observation; it is not a universal source/target incidence proof.

## Validation evidence and unresolved finding

The terminal focused record `validation/persistent-accounting-r3.json` reports
exit 0 at `eb61c35f911ad0fac36758c878559eaf5f795cfa`, covering the four core and
five client targets. Its queued, starting and final 67-input maps are identical.
All 67 hashes independently matched the reviewed candidate, and Git confirms
that the subsequent change is only `docs/research/pfds-persistent-accounting.md`.
The raw log ends in successful completion of 875 jobs. The record SHA256 is
`801806ab88e673ebaa73be8fc3e6e2f1767871850a92dd6548e6a4e678b5b5e0`;
the log SHA256 is
`997451a3e8ab5380aefd07db74c971740c35f72b39f1fafdd6b1ad6ad2515fba`.
This is matching development evidence, not integrated acceptance evidence.

### PERSIST-ACC-SPEC-VAL-001 — Blocking — unresolved

**Requirement:** The bounded requirements' completion section, README acceptance
modes, and shared review procedure require the clean isolated candidate's own
stock full build and exhaustive audit, a matching verification record, both
independent axes, and immediate final candidate verification before acceptance.
The inherited task 10020 dependency must also satisfy its applicable gates.

**Evidence:** `validation/persistent-accounting-candidate-r3.json` explicitly
records the own full gate as not run. At review, the anticipated
`validation/persistent-accounting-577be12-full-r1.json` and the candidate's
`.lake/verification.json` are absent. The completed nine-target focus and the
ordinary-output copy do not run the entire integrated acceptance procedure or
produce its success record. Task 10020 remains unaccepted and blocked on its
separate gate. No current full-build/audit/final-verification success is supplied
for candidate `577be121e074ddb5de6727a7481c115cb61b3b27`.

**Consequence:** The candidate cannot be accepted and this Spec outcome cannot
be Passed, despite the absence of an identified static mathematical defect.

**Required resolution:** Complete the applicable predecessor gates, then run
the candidate's own documented pinned-Nix `./check.sh --candidate HEAD` in the
frozen isolated checkout. Preserve terminal raw results, exhaustive audit output
and the matching `.lake/verification.json`. Supply that exact evidence to the
retained review pair. Resolve any resulting findings, retain both independent
full-scope outcomes on the same candidate, and perform the immediate
`./check.sh --verify-candidate HEAD` before accepting identical bytes. Any
correction that changes the candidate requires both full-scope continuations.
No source correction is requested solely by this validation finding.

## Disposition and continuation

No prior independent Spec findings exist for this task. This report introduces
only PERSIST-ACC-SPEC-VAL-001 and leaves it unresolved. No static claim,
assumption, example expectation or coverage obligation is requested to change.
The bounded child scope is consistent with the user's permitted cross-cutting
work because task 10017's original Chapter 4/5 dependencies and complete
source/work correspondence remain recorded, and no chapter frontier advances.

This reviewer ran no Lean compiler, full/focused gate, cache operation, or
runtime test; made no source, Git/index/ref, tracker or acceptance change; and
wrote only this assigned report. Read-only scope, hash and evidence inspection
do not replace the pending gate. The reviewer remains available for this same
loop's exact-evidence or correction continuation.

**Final scope:** base `3dd930c3e3989f3e5530463f3ac937a629551335`, candidate
`577be121e074ddb5de6727a7481c115cb61b3b27`, 11 files, 5 commits, no exclusions.
**Spec: Blocked; 0 static findings; 1 validation finding; worst severity Blocking.**
