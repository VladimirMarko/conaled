# XP01 development before foundation acceptance: bounded ordering plan

Recorded 4 November 2026 by `/root/shared_acceptance_sequence` at root's request.
This sole new file is a read-only planning result. No source, ref, index, worktree,
compiler, cache, existing control record or acceptance state was changed. Existing
XP01 mathematical and compatibility assessments are retained, not repeated.

## Decision

**The already recorded XP01 exception permits isolated development of its existing
draft before the live foundation acceptance closes.** This does not permit XP01
acceptance before its prerequisites, inclusion in the exact F candidate, insertion
into the current Chapter 2 acceptance sequence, or beginning a later chapter.

Root's concrete alternative is consistent with the controlling provisions:
after checkpoint 0099 secures exact Z and the completed available review/type
evidence, reuse the idle central worktree for a new development branch based on
exact F, merging only original XP01 draft c28ba718. Keep the original XP01 branch,
the Chapter 2 branch at Z, and the accepted/foundation refs unchanged. This uses
an existing isolated checkout and its private outputs, without a third cache or
an additional worktree. This report neither performs nor starts that work.

No concrete authority or ordering provision found in the inspected records
prohibits that development-only combination. This is an interpretation of the
existing user exception and frozen scope, not a new exception or gate waiver.

## Controlling provisions and their limits

- `REQUEST.md`, lines 24–26, requires chapter order and expressly says:
  "You may make exceptions for cross-cutting concerns."
- `reviews/potential-requirements.md`, lines 3–5, explicitly identifies XP01
  as a bounded cross-cutting unit under that exception, preparing shared
  accounting for Chapters 19–23 without activating or accepting those chapters.
- `tickets/FDSA-XP01.md`, lines 6–12, retains Chapter 1 acceptance and the existing
  foundation branch as dependencies. Lines 15–35 record the already written
  c28ba718 draft, including that its source was developed while the earlier
  Chapter 1 full check remained frozen. That history supplies no compile or
  acceptance credit; it confirms the distinction between drafting and promotion.
- `reviews/potential-requirements.md`, lines 26–30, freezes c80eec9 as the original
  starting candidate and 1aabd51 as the combined historical review base, and
  requires the frozen validation checkout to remain untouched. Its final
  paragraph requires immutable validation, audit, both independent axes and
  immediate identity verification, while allowing truthful draft checkpoints.
- `reviews/shared-integration-preflight.md`, lines 7–9 and 99, requires repaired
  Chapter 1 and the existing foundation scope for XP01 integration/acceptance.
  Its Stage D leaves later shared work outside the Chapter 2 prerequisite set.
  Lines 156–160 preserve development history and defer an integration candidate
  until its prerequisite is actually satisfied. Those provisions remain in force.
- The preflight's line 107 says: "Nothing in this section authorizes action while
  the current gate or Chapter 1 acceptance prerequisite remains outstanding."
  Its stated historical current gate is the old Chapter 1 command in lines 7–9.
  The report itself grants no mutation authority. Repaired Chapter 1 is now
  accepted at R; the authority for a new development assignment comes from the
  governing user exception and root's explicit coordination, not that old plan.
  This interpretation does not relabel the still-pending F acceptance as passed.
- Current continuation lines 224–244 expressly keep F first, forbid assembling
  an acceptance candidate in the live F tree, retain the sequence below, and
  place XP01 outside exact F and current C2. The proposed new branch changes
  none of those accepted/candidate refs or scopes.
- `AGENTS.md` and `implement/SKILL.md` keep this work within the existing loop;
  planning does not start another implementation or review loop. The review
  procedure requires immutable source identities, preserved scope/findings,
  matching validation inputs and both independent axes before acceptance.

The exact saved requirements name the historical author worktree
`conaled-insertion-costs`. They do not require that obsolete physical path to be
recreated. Reusing the already qualified idle isolated central checkout preserves
the isolation requirement; its actual starting state and future assignment must
be recorded honestly.

## Exact source identities and inspected merge scope

| Role | Exact commit |
| --- | --- |
| Accepted Chapter 1 R | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Live foundation F | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |
| Original foundation prefix B | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` |
| Original XP01 draft X | `c28ba71863d2a35ee1c3a089caa90464e4cca692` |
| Reviewed Chapter 2 development Z | `4b5dbfa07288acc73f25c27838d3fb2f78e77d71` |

Read-only Git verified that X's sole parent and merge-base(F, X) are both B.
R is an ancestor of F, and F is an ancestor of Z. X is an ancestor of neither
F nor Z. The protected branch refs still resolve to the table's exact commits:
`work/fdsa-book`, `work/fdsa-foundation-integration`,
`work/fdsa-ch02-development`, and `work/fdsa-list-foundations` respectively.
The proposed name `work/fdsa-potential-development` was absent when checked.

X differs from B in precisely these six original XP01 paths:

1. `Applications/Resources/Potential.lean`.
2. `Applications/Resources/FIFOContracts.lean`.
3. `Examples/MappedPotentialAccounting.lean`.
4. `SquareApplications.lean`.
5. `docs/research/fdsa-potential-accounting.md`.
6. `docs/research/fdsa-reconstruction-map.md`.

F differs from B in eleven paths. Its intersection with the six XP01 paths is
only `SquareApplications.lean` and the reconstruction map. Both complete shared-file
diffs were read. F adds the accepted CallModels/SharedDemand imports near the end
of the public root; X adds MappedPotentialAccounting beside PotentialAccounting.
F's map changes preserve accepted Chapter 1 repairs, the Chapter 2 active row,
and their interpretation boundaries; X changes the Chapter 19 row and inserts a
short shared-accounting draft paragraph before Chapter 1. The displayed hunks
are separate. This is inspected overlap evidence, not a merge simulation or a
claim that Git has reported a conflict-free result.

A faithful development merge based on F should therefore retain every F byte
outside those six paths, add only the original XP01 scope, and retain both sides
of the root/map union. The actual resulting tree and any resolution still need
comparison; never replace complete files with an older branch snapshot. No affine,
accumulated-work, later probability, or Chapter 2 development source is included.

## Concrete future route for root

1. Finish checkpoint 0099 and expose its verified upload before repurposing the
   central checkout. Preserve exact Z, all closed focused/type commands, their
   complete logs/input identities, completed available review dispositions and
   any actual verification record outside mutable output locations. A sealed
   checkpoint or completed type review does not itself accept C2.
2. Record that root's owned central commands are closed and that its source/index
   is clean. Do not infer process quiescence from this planning report or old
   session identifiers. Keep F's live checkout, branch, source and outputs intact.
3. In the existing central `conaled-ch02-top-down` checkout, root may create a new
   development branch at exact F and merge only exact X by an ordinary
   history-preserving merge. Preserve `work/fdsa-ch02-development=Z`, original
   `work/fdsa-list-foundations=X`, accepted R and live F refs. No reset/rebase or
   whole-tree replacement is proposed. If unrecorded edits appear, preserve them
   and resolve the concrete ownership issue rather than forcing the switch.
4. Record the new development commit, both parents, original B-to-X six-path
   scope, historical combined review base 1aabd51, and F as an explicitly
   **unaccepted development incorporation base**. Compare the actual tree with
   both F and X. Retain accepted SharedDemand and foundation compiler corrections.
   Do not claim that this changes the accepted integration base or closes a unit.
5. Any subsequent compiler command is root-owned, newly named and recorded on
   that exact immutable development commit. It may use the existing private
   central project/dependency outputs through the unchanged qualified native
   adapter and stock Lake. No copying/relinking outputs from F, third cache,
   added worktree, historical verification-file installation or pin/profile
   change is proposed. Stock dependency tracking and the applicable guards own
   reuse; this report grants no artifact or old-evidence credit.
6. The already recorded focused compatibility targets remain
   `Examples.MappedPotentialAccounting`, `Examples.PotentialAccounting`,
   `Examples.FIFOContracts`, `Examples.RandomAccessEndCosts`, and
   `Examples.SharedDemand`, with their real imported core dependencies. Actual
   diagnostics may justify bounded corrections within the original XP01 scope.
   The completed mathematical/compatibility preflights identify no current
   preparatory source repair; do not invent one or repeat those assessments.
7. Keep all development results separate from acceptance. The outstanding full
   guarded checks/audits, actual statement inspection, complete independent
   Standards/Spec outcomes and immediate candidate verification remain mandatory
   at the eventual proper XP01 acceptance stage. If F needs a correction successor,
   reconcile that real accepted successor later; development based on current F
   does not authorize retaining a superseded foundation.

The original author-only alternative also remains valid: reuse an idle source
worktree on a separate descendant of X without a compiler/cache assignment.
Root's central alternative is more useful for testing the existing draft with
accepted R and foundation corrections while avoiding another cache. Neither
alternative has been executed by this agent.

## Ordering and resource limits

The accepted sequence remains **F → combined XM01/XD01/XQ01/XU01 → XU02 → XU03
→ complete C2**, followed by its checkpoint and then Chapter 3. XP01 is not
inserted into that sequence and must not delay its required acceptance work.
No Chapter 19–23 algorithm, potential, binary ownership theorem or complexity
bound is added to this bounded unit. Original XP01 acceptance prerequisites
and the whole-book chapter obligations remain unchanged.

Root's latest resource observation for this task is approximately 5.83 GiB
available; the older CURRENT snapshot reports an earlier measurement. This
report made no new resource measurement or compiler launch. Reusing an existing
qualified checkout requires no fresh installation/cache copy, but available
space does not prove a future build's peak fits. Root must retain the actual
resource guard and one-thread/private-output discipline when scheduling work.
No new threshold, concurrency permission, fresh-mode waiver or acceptance gate
is created here. F remains the sole live compiler at the parent's observation.

## Read boundary and source identities

Complete reads for this planning task: REQUEST (148 lines), XP01 ticket (48),
frozen potential requirements (116), design preflight (321), draft preflight
(90), shared-integration preflight (205), CURRENT (275), STATUS (48), AGENTS
(76), implementation skill (83), and shared review procedure (115). The current
ticket index was inspected only in the returned XP01/ordering/status contexts.
An initially truncated combined read was replaced by complete nontruncated reads
of CURRENT/STATUS and the implementation/review instructions. No new Lean proof
assessment, dependency-cache inspection, merge simulation or process probe occurred.

| Record | SHA-256 of inspected file |
| --- | --- |
| `REQUEST.md` | `670038db71064a643014c952161666544cf37a4c9e17f14ddc7c4478e78dc6d8` |
| `tickets/FDSA-XP01.md` | `8fca8643f217d732a615cee5252f945189bd31b2befd687e053832cd92c15884` |
| `reviews/potential-requirements.md` | `545b5d2ff4a93594f2b1ca245594233bdfcf461b8f4fe14b3bbe698e6ad1aa2f` |
| `research/potential-generalization-preflight.md` | `c47864985fc8c1c6baffa5601d2610268b7f5c2cd895073966eb214e365226ae` |
| `research/potential-draft-preflight.md` | `fba713681c8eb3a80720b10d9ed0d0a33b46d2dddd883b7bd2ca0bc263f254f2` |
| `reviews/shared-integration-preflight.md` | `e1d9c119e2bca35bbbd283eb47d05330f35d7e548f92e063eeebe7d4d53552eb` |
| `CURRENT.md` after0098 snapshot | `50a86e3c3d2fea317de024ac89fbcdd8392c2b0713e44f6c7ab900b9d0f88e24` |
| `STATUS.md` after0098 snapshot | `b2aab6810a9f1a5f3e4f363102101fba499236c7ae0fedf506ce779734e05328` |
| `tickets/INDEX.md` (bounded contexts only) | `5db920e01cad3452e826b8e747894beca02f04e4d1fe324654f53cbda56c74f8` |
| repository `AGENTS.md` | `5d017d009307c72a7616d7afe0bee9fb5a7105fe2f6f4e1da3fdccf070d4b4fe` |
| `.agents/skills/implement/SKILL.md` | `dcb604c159e9450af969fecedd595c216ac3850c8ee523766fa5cdc20b87d3df` |
| `docs/agents/review-loop.md` | `0561fafdb97423533dd3d85ba71ab89b09c4e148c1312035846fdf80be45e64c` |

The new report is read back in full at handoff. All earlier files in this
preparation package remain unchanged. HOLD follows for checkpoint 0099.
