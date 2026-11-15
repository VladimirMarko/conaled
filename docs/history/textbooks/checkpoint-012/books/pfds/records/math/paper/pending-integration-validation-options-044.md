# Pending integration validation: permitted consolidation and limits

Read-only workflow analysis, 2026-11-03. This report changes no candidate,
requirement, controller, review outcome, acceptance state or running process.
The coordinator inspected the actual Git graph, saved requirements and pinned
guidance. `/root/chapter02_continuation_plan` supplied read-only requirement
analysis; `/root/recovery_audit` supplied read-only workflow analysis. Neither
was conducting an acceptance review. This is the only file written for this task.

## Decision

**Conditional yes:** the pending scopes can be explicitly retargeted, through
new rounds of their existing reviews, to one exact consolidated candidate and
share that candidate's genuine full-build/audit record. No inspected requirement
permanently mandates acceptance of each historical tip SHA or a separate replay
of an identical full command for each ticket. Every predecessor acceptance gate,
full original review base, statement/source obligation, independent review and
final verification remains binding. A common candidate is eligible for this
workflow; it is not currently accepted by this analysis.

**The next full run cannot simply be redirected from 901 to 3cf under the current
records.** To replace rather than complete the separate 901 gate, local 10013 and
10018 must also be explicitly included in the retargeting, with their original
bases, requirements, complete scopes and both axes continued on the new exact
candidate. Alternatively, finish those prerequisites separately and consolidate
only the seven later scopes. The approved full/verify controller is hard-pinned
to 901; a common-candidate run needs a correctly scoped, reviewed evidence route,
not an ad hoc pin edit or a mislabeled old record.

The legitimate saving is one full run on one final, jointly covered source tree.
It is not acceptance of old SHAs from a descendant's result, erasure of earlier
failures, or a waiver of any dependency. It also does not establish that a longer
run will avoid the execution-session disconnection observed on 901.

## Why the repository permits this, and what remains mandatory

The saved original request selects per-chapter `implement`, the shared review
procedure, statement review and independent axes. The selected skill replaces
`implement-spec`'s ticket/scheduling/integration machinery with a whole-task
loop; the presence of local tickets does not by itself select an additional
merger workflow. Real dependencies remain authoritative in the local tracker.
If an implementation explicitly uses `implement-spec`, its reviewed-merge and
dependency rules still apply; this report does not grant an exception to them.
Sources: [REQUEST](../requirements/REQUEST.md), Operational interpretation;
[implement](../../conaled/.agents/skills/implement/SKILL.md), lines6–21,58–68;
[tracker policy](../tracker/README.md), lines3–9;
[implement-spec](../../conaled/.agents/skills/implement-spec/SKILL.md), lines34–40.

The [shared review procedure](../../conaled/docs/agents/review-loop.md) pins
immutable candidates **per round** and retains original full-spec bases
(lines13–22). It explicitly allows changed candidates while requiring both axes
to reassess the full task, carrying earlier findings and matching analysis
(lines37–65,96–110). Validation may be reused only for matching source,
dependencies, configuration, relevant inputs and coverage (lines69–85). The
[code-review skill](../../conaled/.agents/skills/code-review/SKILL.md), lines70–76,
also directs reviewers not to repeat successful mechanical checks unnecessarily.
These rules permit several newly retargeted reviews to cite the **same literal
candidate's** full record; they do not transfer old review approvals to it.

The stock command still needs a clean, stable isolated candidate, genuine
complete build and exhaustive audit, matching `.lake/verification.json`, actual
terminal success, separately applicable test evidence, both independent axes,
and immediate stock `--verify-candidate` before exact delivery. Required fresh
mode is unchanged. The record cannot be copied, rewritten, inferred from partial
output or counted for another commit. Sources: [README](../../conaled/README.md),
lines155–198,204–242; shared procedure lines75–92,105–110.

### Hard saved obligations that consolidation must satisfy separately

| Scope | Binding requirement |
| --- | --- |
| 10002, Chapter2 | Original base 825 is retained; 10013 remains separately unaccepted until its own full verification/reviews; Chapter2 needs complete source/statement coverage and exact isolated validation. [chapter02](../requirements/chapter02.md), lines6–10,60–67. |
| 10014, suspension foundation | Original base 69f is retained; Chapter2 and import-prerequisite acceptance remain separate; both axes and validation must cover the same complete candidate. [suspension-foundation](../requirements/suspension-foundation.md), lines7–10,82–89. |
| 10019, pure recursive forcing | Its separately owned obligation requires immutable complete-candidate validation, exhaustive audit, final verification and both axes. [pure-recursive-forcing](../requirements/pure-recursive-forcing.md), lines25–29. |
| 10020, cache-write counts | Original base ea8 is retained; 10019/10014/Chapter2 are independent dependencies with exact gates. Do not retroactively attribute its write-count result to 10019 or rewrite that old review's ownership boundary. [pure-cache-counts](../requirements/pure-cache-counts.md), lines11–15,59–67. |
| 10021, persistent accounting | Original base 3dd is retained; acceptance cannot precede satisfaction of applicable dependency/integration gates. Its full check, audit, record, both axes and immediate verification remain required. [persistent-debit-foundation](../requirements/persistent-debit-foundation.md), lines17–30,167–173. |
| 10022, body-entry counts | Original base 577 is retained; its own exact candidate gate and all predecessor gates remain. [body-entry-counts](../requirements/body-entry-counts.md), lines28–32,153–158. |
| 10023, signed potential | Original base 5e is retained; its own exact full/audit/review/verify and earlier gates remain binding. [signed-potential](../requirements/signed-potential.md), lines24–31,148–154. |
| 10013/10018, if replacing the 901 run | Preserve their separate complete scopes and bases. Import repair remains an import-only owned change; unrelated declarations belong to their actual other scopes. Full compilation/audit and both reviews remain required. [shared-persistence](../requirements/shared-persistence.md), lines3,34–47; [import-footprint](../requirements/import-footprint.md), lines9–23. |

The old dispatches' sequential runner recipes describe the then-current
candidates and scheduling. They are not a user instruction requiring seven
distinct future compiler executions after every affected scope has genuinely
acquired a new common candidate. Nevertheless, until a new round is recorded,
their current blockers remain unresolved. Historical Blocked reports and failed,
lost or interrupted runs must stay unchanged.

## Verified ancestry and the larger review obligation

Proposed common commit:
`3cf3de4fbc24c1a144353ae64b13b72f5ead54a5`.
Read-only `git merge-base --is-ancestor`, `git merge-base`, `git diff` and
`git rev-parse` confirmed every historical tip and both recorded bases below
are ancestors of this commit. Each original full base is its actual merge base
with 3cf. No path was deleted between these tips and 3cf.

| Ticket | Historical tip | Bounded ticket base | Original full-review base | Full-base diff files: old → 3cf |
| --- | --- | --- | --- | ---: |
| 10002 | `99a29dcd02eb529fbefbb675e244a8c47b78cdef` | `82501d108f33c62d21b5e0d0f7d2376b902d8d49` | same 825 | 42 → 162 |
| 10014 | `a3feaff319ad5fad912fb8bdc113f33fea4e2a60` | `99a29dcd02eb529fbefbb675e244a8c47b78cdef` | `69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4` | 42 → 125 |
| 10019 | `361f5f3f6bb3de1974510ce355883dac2bf25333` | `a3feaff319ad5fad912fb8bdc113f33fea4e2a60` | `b422800fb5b6dc1253823057c0ea71644274d77c` | 58 → 94 |
| 10020 | `3dd930c3e3989f3e5530463f3ac937a629551335` | `361f5f3f6bb3de1974510ce355883dac2bf25333` | `ea8afa12706d30cdc69ece1a172d5f21a3ea1809` | 14 → 39 |
| 10021 | `577be121e074ddb5de6727a7481c115cb61b3b27` | `3dd930c3e3989f3e5530463f3ac937a629551335` | same 3dd | 11 → 26 |
| 10022 | `5e048f781aa04be9ce993f1e7455bdc82df22bff` | `577be121e074ddb5de6727a7481c115cb61b3b27` | same 577 | 11 → 16 |
| 10023 | `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` | `5e048f781aa04be9ce993f1e7455bdc82df22bff` | same 5e | 6 → 6 |

The saved bases are documented in the corresponding dispatch files under
`session/reviews/`: `chapter02-99a29dc-dispatch.md`,
`suspension-a3feaff-dispatch.md`, `pure-suspension-361f5f3-dispatch.md`,
`pure-cache-counts-3dd930c-dispatch.md`, `persistent-accounting-577be12-dispatch.md`,
`body-entry-counts-5e048f7-dispatch.md`, and
`signed-potential-3cf-dispatch-r3-042.md`.

This is an expanded integration assessment, not seven old source approvals
plus a compiler result. Earlier scoped paths changed later: all earlier ranges
include a subsequently changed `SquareApplications.lean`; 10014 additionally
includes later changes to `Applications/Suspensions/Recursive.lean` and its
source-map document; 10019 includes the later pure-suspensions document change.
The signed-potential generalization also affects shared interfaces/consumers
beyond the scope of its six-file diff. Reviewers must account for the complete
new full-base ranges and cross-scope interactions, using prior analysis only
where identities and context match. The Chapter2-base union is 162 files with
27,850 insertions and 28 deletions, not its old 42-file round.

**901 is not an ancestor of 3cf.** Their merge base is
`70a1477d822efd4fdcec2007280f650bb4695eda`. All six import-repair file blobs
at 901 do match 3cf, but that observation does not transfer acceptance or establish
the entire prerequisite scope. If those loops also retarget, preserve 10013's
base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` and 10018's base 70a; both are
actual ancestors of 3cf. Their full-base-to-3cf ranges contain 170 and 164 changed
files respectively. Keep separately attributed mathematical/import ownership
and explicitly cover all other delivered changes in the combined assessment.

The inspected README, AGENTS and implement/implement-spec/code-review/review-loop
blobs are identical at the current main checkout and 3cf. Thus the cited rules
are actually the candidate's rules, not guidance from another revision.

## Concrete prerequisites before choosing a common-candidate full run

1. **Record a retargeting manifest** in the existing retained loops: exact common
   SHA, all affected tickets, original/bounded bases, old→new full file/commit
   scopes, requirements, owner boundaries, every finding and every prior outcome.
   Preserve all old refs and evidence. Include 10013/10018 explicitly if their
   separate 901 acceptance is to be replaced; otherwise retain that dependency.
2. **Establish the complete review coverage.** Assign coverage and record the
   new rounds before the run; final review outcomes await its actual evidence.
   Reuse matching analysis, not old approvals. Both independent axes must reassess every delivered scope and
   interface on the common candidate, including statement review and source
   coverage. Distinct ticket dispositions can cite shared reports/evidence with
   an explicit coverage matrix; no obligation or finding may disappear into an
   unqualified aggregate pass.
3. **Provide the exact validated command/evidence route.** The currently approved
   `session/validation/run-native-validation.py` binds full/verify to 901 and
   `import-correction-r3` (lines26,151–193,240–249). Its focus override cannot
   retarget full. Preserve its old behavior/evidence; review any new operational
   route with exact candidate, private outputs, locks, frozen input snapshots,
   genuine terminal logging and stock-record checks. Do not alter guards or
   fabricate a missing terminal result.
4. **Actually validate common C.** Run the stock full check and exhaustive audit
   in a clean isolated C, using fresh mode while its required runtime-transition
   validation remains unsatisfied. Preserve its own genuine completion and
   verification record. Retain applicable stock regressions with exact coverage
   and inputs; a common full record covers only build/audit. Focused successes,
   native version smokes and current 901 regressions are not automatic replacements.
5. **Close dependencies and deliver exactly C.** No dependent is accepted merely
   because its predecessor source occurs in C. Record the separate prerequisite
   decisions in dependency/chapter order only when their full requirements and
   both axes are satisfied. Immediately verify C before its acceptance/delivery;
   if decisions are separate acceptance actions, reverify at those actions as
   necessary. No old tip is declared accepted. Any new source correction changes
   C and triggers applicable new rounds/evidence. Preserve checkpoint obligations.

These are conditions for an authorized future plan, not actions performed by
this report. If the complete scope/ownership/controller plan cannot be made
clear, retaining the existing sequential plan is the supported fallback.

## Separate fallback: serial reuse of one private validation checkout

**Also conditionally permitted after the prior acceptance/freeze obligations
have ended.** README lines156–168 expressly retain normal Lake outputs for later
guarded incremental reuse; lines197–198,220–225 require stable private checkouts
during validation/acceptance and forbid sharing writable outputs across active
checkouts. They do not permanently reserve one directory per historical commit.

After a candidate is fully accepted, all users/writers have ended, its immutable
Git refs and validation/review evidence are preserved, and the next exact
candidate is deliberately frozen in that same private checkout, ordinary stock
Lake/guard scheduling can decide what to rebuild. That is not cross-checkout
artifact migration. Starting the new candidate check clears the previous live
success record; only new successful validation creates its own record (README
lines185–198). Old approval does not transfer.

Do not apply this to a current pending/frozen review materialization:
pure-cache-counts.md line62 explicitly preserves those candidates. An in-place
move must occur only after all such obligations end and the command controller
is legitimately configured for the next candidate. No current checkout move is
authorized here. Required fresh checks still ignore ordinary project outputs
and delete their temporary project build (README lines204–218), so directory
reuse cannot avoid a mandatory fresh rebuild or turn its deleted outputs into
a normal incremental cache.

## Current limits

The latest 901r2 disconnection is not terminal success, a source failure, or an
OOM diagnosis. The reported later successful next-module probes do not provide
the missing whole-run outcome. This analysis supplies no acceptance, no source
or compiler change, and no instruction to launch a run. It identifies a legitimate
future consolidation option with explicit conditions, and preserves the current
sequence wherever those conditions are not met.
