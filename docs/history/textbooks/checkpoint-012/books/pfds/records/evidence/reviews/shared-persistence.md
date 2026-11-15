# Local #10013 implementation/review loop

Current continuation (2026-11-03, after checkpoint 042): coordinator takeover
and native validation preparation are recorded at the end of this existing
record and in
[`prerequisites-901f734-coordinator-takeover-042.md`](prerequisites-901f734-coordinator-takeover-042.md).
The older status sections below retain their original historical time frames.

## Latest continuation status — round 5 static assessment complete, Blocked

The current successor is `901f734161920a76f3b399a575805b9a1d31e971` in the
clean isolated `import-correction-r3` checkout. #10013 round 5 keeps the fixed
base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`; linked #10018 round 3 keeps
`70a1477d822efd4fdcec2007280f650bb4695eda`. The full fourteen-file/five-commit
scope and all saved requirements are retained. The latest commit adds only
the direct `Mathlib.Data.Nat.Size` import for IMPORT-VAL-004.

Checkpoint021 is saved and restore tested; its report-write hold is released.
Both retained independent reviewers completed full-scope static assessments:
Standards has zero code/prose findings, and Spec has zero implementation findings.
Root allowed these assessments before the focused target's terminal evidence
as slots became available. The focused check is still running; full `901f734`
validation has not started under the supplied handoff. Both axes remain
**Blocked**, with no candidate acceptance. Both retain IMPORT-VAL-004 pending
terminal compiler evidence, and the full exact gate remains unavailable.
The partial `324962e` Standards reports,
that candidate's undispatched Spec axis, and every historical finding/outcome
remain preserved. See round 5 and
[`prerequisites-901f734-dispatch.md`](prerequisites-901f734-dispatch.md).

## Round 4 closure status — historical

The current linked candidate is
`324962e733886e66d6cd92af6cb68627ed4c8f1d` in the isolated `import-correction`
checkout. #10013 retains its original fixed base
`cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`; #10018 round 2 retains its own
fixed base `70a1477d822efd4fdcec2007280f650bb4695eda`. The prior candidate's
full run exposed IMPORT-VAL-001 through IMPORT-VAL-003 and never produced
acceptance. The new candidate supplies import-only repairs; both independent
axes must assess the entire updated scope and all retained findings.

The retained independent Standards reviewer paused at a read-only boundary
after the running full check exposed IMPORT-VAL-004 in
`Examples/IndefiniteService.lean`. Its assessment is partial; Spec has not
resumed on this candidate and is held pending root's corrected immutable
successor. The full check remains live under root ownership with no acceptance
result. No new source is being guessed or reviewed. The
preparation, evidence and continuation instructions are in round 4 below and
[`prerequisites-324962e-dispatch.md`](prerequisites-324962e-dispatch.md).
Earlier round outcomes remain historical; no static-clear report is promoted
to approval. PERSIST-VAL-001 retains its fixed-with-compiler-evidence disposition.
Requirements, all mandatory gates and the chapter boundary are unchanged.

## Round 3 closure status — historical

The current review candidate is
`226ebaef53b9eba97bef4b3b6ca364fdea488c69`, with the original #10013 fixed base
`cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`. It incorporates the import-only
prerequisite #10018, whose linked round-1 record is
[`import-footprint.md`](import-footprint.md). The round-1 and round-2 reports
below remain historical outcomes; neither passed, and neither approves the
current candidate. PERSIST-VAL-001 remains fixed with the evidence already
recorded. No requirement for #10013 has changed.

The user's book-and-thesis union clarification is saved in
`../requirements/REQUEST-union-v2.md`. Both full sources are now available;
historical source-availability statements below describe their earlier rounds.
Source availability does not establish source inspection or chapter acceptance.
This linked prerequisite review accepts neither Chapter 2 nor any other chapter.

Both independent axes completed full-scope static review of this new candidate
with zero unresolved code/prose or implementation findings. The exact full
check is still running, so both outcomes are **Blocked**. Neither may pass
before successful full validation, the matching `.lake/verification.json`,
and final candidate verification. See round 3 below for the reports, pinned
evidence and continuation instructions.

## Scope and stable base

- Full user requirements: `../requirements/REQUEST.md`.
- Bounded cross-cutting prerequisite: `../requirements/shared-persistence.md`, version 2.
- Requirement fingerprints: `REQUEST.md` SHA-256 `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499`; `shared-persistence.md` v2 SHA-256 `177e80e0beda3ec144279c104d2fa3b968e916b0104db7f2e5d3c7c81a4bec76`.
- Base: `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- No unrelated user changes or exclusions.
- Chapter source acceptance stays blocked separately; this loop cannot accept a book chapter.

## Intended mathematics and cases

The source implementation note `docs/research/pfds-shared-persistence.md` gives
the per-family statement review, public contracts, assumptions and connected
examples. The independent source-to-statement assessment is
`../research/shared-persistence-statement-check.md`. It is useful evidence,
not either required acceptance review.

The assessment found a real gap: distinct roots with the right suffix values
need not enumerate all reachable cells. The implementation adds actual-tail
`SuffixChain`, `ClosedRoots`, independent `Reaches`/`ReachableFrom`, and a proof
that successful enumeration lists all reachable addresses; non-null root
distinctness prevents overcounting. The counterexample is retained in
`Examples.SharedList.equal_suffix_values` and its two reachability/closure tests.
`suffixes_storage` connects the strengthened public results to the count.

Raw operations are traversals on represented inputs, not validators of
untraversed roots. Missing reads/non-null fuel exhaustion fail. Zero-fuel null
cases still count one structural visit. These clarifications resolve an
overbroad initial internal requirement without changing the source algorithm.

## Round 1

- Candidate: `ad730010ab1929bbd7a16a035c7990a6f328b178`.
- Confirmed merge-base: `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Full review diff: `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...ad730010ab1929bbd7a16a035c7990a6f328b178`.
- Commit list: `ad73001 feat(persistence): model shared lists and path copying (#10013)`.
- Isolated validation checkout: `/workspace/scratch/ca9a61d0bf30/validation-persistence`.
- Exact sources tracked; clean candidate at creation.
- External dependency sources/caches reused from this task's pinned, clean
  `.lake/packages` only; project build directories are distinct. No other
  workspaces or project outputs are used.
- Focused development builds have compiled Basic, Copy, strengthened Suffixes
  and the resource module. Adapter linter/deprecation errors were corrected;
  final Examples check is pending at capture, so this is not complete validation.
- Required command started in the isolated checkout through the real Nix shell:
  `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`.
- Command log: `../validation/persistence-ad73001-check.log`.
- Complete candidate build/axiom audit: **not completed**. Root intentionally interrupted the original full run for resource sequencing; its log is retained. No success record or final verification exists for this candidate.
- Focused terminal feedback later found a fatal unused-tactic linter error in `Observation.updateSquare`; see validation finding PERSIST-VAL-001 and round 2 below.
- Standards: **Blocked pending validation**, full static review complete with zero code/prose findings. Independent reviewer `/root/architecture_inventory/chapter01_standards`; complete report `shared-persistence-standards-r1.md`.
- Spec: **Blocked pending validation**, full static review complete with zero implementation findings. Independent reviewer `/root/architecture_inventory/chapter01_spec`; complete report `shared-persistence-spec-r1.md`.

Reviewers may inspect the fixed source while validation runs, but neither may
pass without completed applicable validation. They must not compile or mutate
the isolated checkout during its stable validation window. Previous Chapter 1
review outcomes do not approve this separate formal candidate.

## Standards findings and outcome

No implementation/prose findings or heuristic change requests. The independent
review checked the full eight-file diff, applicable repository standards,
unchanged reused interfaces, and statement/connected-example evidence. Actual
heap traversal, old-root retention, modeled allocation counts, partial failure,
fuel sufficiency, suffix closure/reachability/distinctness, public integration
and documented runtime limits were assessed. No finding ID was allocated.

**Current Standards outcome: Blocked** because the required exact-candidate
integrated build, exhaustive audit, success record and final verification have
not yet completed. Source review alone is not approval.

## Spec findings and outcome

No implementation findings. The independent review checked each version-2
contract against actual recursion, semantic predicates and retained applications,
including independent source list material, the strengthened suffix-space proof
and the unshared-equal-values counterexample. No finding ID was allocated.

**Current Spec outcome: Blocked** because exact-candidate full validation and
final verification are pending. Partial/focused builds cannot substitute for
the required gate.

## Round 1 follow-up (superseded by correction)

If candidate `ad730010ab1929bbd7a16a035c7990a6f328b178` remains unchanged, supply
the terminal integrated command result, its `.lake/verification.json`, and final
`./check.sh --verify-candidate HEAD` evidence to both existing reviewers. They
may reuse completed static analysis and assess the new validation evidence.
Any source correction requires a new immutable candidate and both axes to
review the full change against the fixed base, carrying any later findings.

Both axes must assess the full candidate and keep unresolved findings with
stable IDs. Missing or failed required validation blocks approval. Final source
must match the jointly reviewed and validated candidate.

## Validation finding

### PERSIST-VAL-001 — Redundant adapter tactic rejected by the linter

- Origin: focused Lean compiler feedback after round-1 static review.
- Candidate affected: `ad730010ab1929bbd7a16a035c7990a6f328b178`.
- Location: `Applications/Sequences/SharedList/Observation.lean`, `updateSquare` success branch, original line 47.
- The `change (optionalRepresentation α).Rel _ _` tactic had no effect and was rejected by `unusedTactic` under the source's warning policy. Static reviews had found no implementation discrepancies; that did not establish compilation.
- Root removed only that redundant success-branch tactic. The failure branch and all statements/operations are unchanged; no linter was weakened.
- Status: **fixed by compiler evidence** in `70a1477d822efd4fdcec2007280f650bb4695eda`. The focused closure including `Observation` and `Examples.SharedList` completed successfully; full integrated acceptance remains pending.

## Round 2

- Fixed base and confirmed merge-base: `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Candidate: `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/validation-persistence`, confirmed exact HEAD and clean worktree at dispatch.
- Full review diff: `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...70a1477d822efd4fdcec2007280f650bb4695eda`.
- Commits: `ad73001 feat(persistence): model shared lists and path copying (#10013)`; `70a1477 fix(persistence): remove redundant adapter tactic (#10013)`.
- Eight-file scope retained; 939 additions. No exclusions. Requirements version 2 and original fingerprints unchanged.
- Correction relative to round 1: single redundant tactic removal documented as PERSIST-VAL-001; no definition/theorem statement or runtime-operation change.
- Focused compilation: all six added Lean modules and connected examples passed, 664 jobs; root directly observed exit 0. Log `../validation/persistence-focused-r2.log` ends with `Build completed successfully (664 jobs)`.
- Focused success is not integrated acceptance. Required exact-candidate Nix command `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD` is running anew, log `../validation/persistence-70a1477-check.log`.
- Full integrated build, exhaustive audit, candidate verification record and final `./check.sh --verify-candidate HEAD`: pending.
- Existing independent reviewers completed full fixed-base scope again, using unchanged-content analysis as evidence and inspecting the correction and affected adapter. Reports `shared-persistence-standards-r2.md` and `shared-persistence-spec-r2.md` are complete.
- Standards round 2: **Blocked pending integration validation**, zero unresolved code/prose findings. The fatal lint issue is verified fixed; no semantic change or new assumptions were found.
- Spec round 2: **Blocked pending integration validation**, zero implementation findings. Contracts, operation, hypotheses, partial-result semantics and connected examples remain faithful to v2.
- Reviewers may not compile or mutate the stable isolated candidate while validation runs.

## Current acceptance status

Both independent static reviews cover candidate
`70a1477d822efd4fdcec2007280f650bb4695eda` against the same fixed base and
unchanged requirements. Neither axis has an unresolved implementation finding;
both are **Blocked** by the incomplete integrated validation gate. The 664-job
focused run used the live implementation checkout and is development/compiler-fix
evidence, not clean isolated acceptance.

If this candidate stays unchanged, provide terminal full-check/audit output,
the matching verification record and final verify result to the existing
reviewers. No chapter acceptance or source-coverage resolution follows from
this prerequisite even if its own validation later passes.

## Root execution update for checkpoint005

Candidate remains 70a1477 and requirements remain version2. Both round2 static
reviews are complete with zero implementation findings. The supported pinned
runtime worker setting was raised from1 to2 after read-only diagnostics; the
current full incremental check is running in the same isolated checkout and
reuses its own completed outputs. The current command is
`env LEAN_NUM_THREADS=2 ./check.sh --candidate HEAD`. No acceptance gate changed.
Its source/coverage/version checks passed; terminal build/audit/record/final
verify evidence is still pending. The frozen checkpoint log and live log are
distinguished in STATUS.md and validation/execution-record.json. Do not read an
older interrupted log or the focused success as the full candidate result.

## Round 3 — linked import-only prerequisite

### Pinned scope

- Coordinator: `/root/prerequisite_review`; this continues the existing loop
  and is not a third Standards or Spec review.
- Stable #10013 base and confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- Candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Prior #10013 candidate and #10018 fixed base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`, confirmed an ancestor of the candidate.
- Isolated read-only review/validation checkout:
  `/workspace/scratch/ca9a61d0bf30/validation-imports`.
- Observed checkout `HEAD` equals the candidate; `git status --porcelain=v1`
  returned no entries at preparation.
- Full review command:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Full commit list:
  `ad73001 feat(persistence): model shared lists and path copying (#10013)`;
  `70a1477 fix(persistence): remove redundant adapter tactic (#10013)`;
  `226ebae refactor(frp): import only the required mathematics and tactics (#10018)`.
- Ten changed files, 951 insertions and 2 deletions; no unrelated changes or
  exclusions. The eight #10013 files are unchanged from round 2. The only
  candidate-to-candidate changes replace the aggregate `Mathlib` import in
  `Applications/FRP/Spec.lean` and `Applications/FRP/Equivalence.lean` with
  direct providers. The independent reviewers will verify the preservation
  requirement and affected integration scope.
- The concurrently edited `conaled` checkout and Chapter 2 implementation
  worktrees are outside this frozen candidate. No review outcome here approves
  that work or a later integration tip.

### Saved requirements and retained evidence

| Requirement | Version / SHA-256 |
| --- | --- |
| `../requirements/REQUEST.md` | Original request; `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `../requirements/REQUEST-union-v2.md` | Union clarification v2; `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `../requirements/shared-persistence.md` | Unchanged bounded prerequisite v2; `177e80e0beda3ec144279c104d2fa3b968e916b0104db7f2e5d3c7c81a4bec76` |
| `../requirements/import-footprint.md` | Linked prerequisite v1; `cf8fb3133b83ac59fdf6fd46b818d8b279d96385f5de50da843ef9b7fd62444d` |

All four prior axis reports remain preserved. Their unchanged-content analysis
and the fixed disposition of PERSIST-VAL-001 are evidence for this round, not
reuse of approval. Both new axes must cover the full fixed-base candidate,
including the unchanged SharedList contracts, statements, connected cases,
new import lists, affected dependencies, and the exhaustive integration gate.
The source-to-statement note remains background evidence, and the implementation
note must be read from the frozen candidate, not the live implementation tree.

### Validation status at preparation

- Root owns the single running full check and its monitoring (`functions` cell
  41); the coordinator and reviewers must neither compile in nor mutate this
  checkout or its dependencies.
- Live log: `../../active-validation/import-footprint-226ebae-full.log`.
- Terminal execution record:
  `../validation/import-footprint-226ebae-full.json` currently reports
  `status: running`, candidate `226ebaef53b9eba97bef4b3b6ca364fdea488c69`,
  and `acceptance: false`.
- The saved argv uses the already pinned Nix closure offline with evaluation
  cache disabled and runs `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`.
  No toolchain, dependency pin, guard, source policy, audit root or acceptance
  mode has been relaxed.
- Full integration still covers all 957 project modules and the exhaustive
  proof audit. Partial build progress and focused compilation are development
  evidence, not acceptance. Earlier interrupted candidates supply no success
  record for this candidate.
- Successful terminal output, matching `.lake/verification.json`, and immediate
  `./check.sh --verify-candidate HEAD` evidence are still required.

### Independent axes and continuation

Root initially released one reviewer slot after the map/ordered implementation
agents finished. Independent Spec reviewer `/root/prerequisite_review/spec`
completed the full frozen-scope static assessment and returned Blocked on
validation. Its released slot allowed independent Standards reviewer
`/root/prerequisite_review/standards` to perform its separate full assessment,
also completed and Blocked on validation. The reviewers were sequenced
because only one slot was available, rather than omitting either axis.
Report writes were paused during checkpoint009 capture; root confirmed the
checkpoint was saved and restore tested, then released that hold. The shared handoff is
[`prerequisites-226ebae-dispatch.md`](prerequisites-226ebae-dispatch.md).

- Standards round 3: **Blocked — required exact-candidate validation incomplete.**
  Static review complete with 0 unresolved code/prose findings, no worst
  severity and no heuristic-only change request. Complete report:
  `shared-persistence-standards-r3.md`; linked #10018 result:
  `import-footprint-standards-r1.md`. The reviewer independently inspected
  architecture, statements, connected cases, exact import-only preservation,
  provider paths and direct consumers. PERSIST-VAL-001 remains fixed. No
  correction is requested by this axis.
- Spec round 3: **Blocked — required exact-candidate validation incomplete.**
  Static review complete with 0 unresolved implementation findings and no
  worst severity. Complete report: `shared-persistence-spec-r3.md`; linked
  #10018 result: `import-footprint-spec-r1.md`. The reviewer independently
  reread the full SharedList claims/cases, checked exact non-import-byte
  preservation and direct providers/consumers, and retained PERSIST-VAL-001's
  fixed disposition. No correction is requested by this axis.

Any concrete finding is returned to root for correction without coordinator
source edits. If static review completes while validation is running, retain
continuation-ready Blocked reports. Once root supplies terminal validation,
record and final-verify evidence, re-engage both existing reviewer children on
the unchanged candidate. If a source correction or integration changes the
candidate, pin a new round with both axes against the same #10013 base and carry
every finding forward.

### Round 3 coordinator reconciliation

Both complete reports cover the same exact ten-file candidate, fixed #10013
base, saved requirements, applicable standards and acceptance gate. Their
linked #10018 reports preserve that ticket's narrower fixed base. No unresolved
finding was reranked, merged away or omitted; there are no new code/prose or
implementation findings to return for correction. PERSIST-VAL-001 retains its
original identity and fixed-with-compiler-evidence disposition. All four
historical reports remain unchanged with their original Blocked outcomes.

At coordinator closure of static review, the candidate checkout still resolved
to `226ebaef53b9eba97bef4b3b6ca364fdea488c69` with empty porcelain status. The
execution record still reported `running` and `acceptance: false`. The exact
remaining blocker for both axes is successful terminal full build and exhaustive
audit, matching `.lake/verification.json`, and final
`./check.sh --verify-candidate HEAD` evidence. No acceptance is inferred from
the clean checkout, partial log or completed source review.

Re-engage the same two reviewer children with those three evidence items if
the candidate stays unchanged. This round is continuation-ready and **Blocked**,
not Passed. The coordinator made no source, dependency, build-output or
requirement changes and ran no compilation or competing validation.

## New full-build findings — 2026-11-02

The unchanged resumed full check has reported two concrete source compilation
errors while continuing other modules: IMPORT-VAL-001 at FRP/Demand.lean:139
(`le_rfl` versus the required strict successor inequality), and IMPORT-VAL-002
at FRP/Finite.lean:72 (`s.biUnion` resolves a Finite class without that field).
The run has not yet returned its overall terminal status, and no audit success
or verification record is inferred. Exact diagnostics and discovery metadata
are in validation/import-footprint-226ebae-observed-errors.json.

Root prepared isolated import-correction/pfds/import-footprint-r2 at the same
226ebaef53b9eba97bef4b3b6ca364fdea488c69 for investigation. The active frozen
validation-imports checkout remains unchanged. Map investigates actual provider
requirements and whether either error already needs a proof correction;10018
retains its import-only scope. Any necessary proof fix will receive a separate
local prerequisite instead of silently changing those requirements. No final
candidate/acceptance decision or fix disposition is recorded yet.

Both prior static axis reports remain historical evidence for their exact
candidate. Required validation is now blocked by these observed errors as well
as the missing terminal gate; a changed candidate needs the existing linked
review loop's next round, preserving the fixed bases and prior finding history.

## Corrected candidate prepared — round2 inputs

The three findings now have import-only corrections at 324962e733886e66d6cd92af6cb68627ed4c8f1d,
clean isolated import-correction/pfds/import-footprint-r2. Manifest:
validation/import-footprint-candidate-r2.json. Existing #10013 and #10018 bases
and requirements are unchanged. The complete linked diff has
13 files; #10018's narrow diff has 5 files.

IMPORT-VAL-001 is repaired by Mathlib.Order.SuccPred.Nat in Demand;
IMPORT-VAL-002 by Mathlib.Data.Set.Finite.Lattice in Finite; additional
IMPORT-VAL-003 by Mathlib.Algebra.Order.Archimedean.Real.Basic in Examples/FRP.
All non-import bytes equal226ebae. Existing Examples.FRPDemand and Examples.FRP
pass the focused r2 batch: exit0,1134jobs, unchanged closure. Reports and exact
source comparison are retained in research/import-footprint-r2*.

These are focused repairs, not final reviewer dispositions or acceptance.
The original frozen full226ebae run continues other modules after its failures.
After its terminal status, reuse completed ordinary outputs in the corrected
private checkout, then run the complete stock candidate check. Both independent
axes must review this full next candidate within the existing linked loop.
No old success record or static-only report approves the corrected candidate.

## Corrected-candidate full validation and review continuation

The obsolete226 resumption lost its execution session; read-only exact-checkout
inspection found no surviving matching compiler/wrapper. Its terminal status is
interrupted, not a Lean failure or integrity defect. Cause unknown; complete
retained evidence: validation/session-disconnection-20261102-2141.json and
import-footprint-226ebae-resumed-r1.{json,log}. No approval existed or was copied.

Corrected324's stock full check is now running, started2026-11-02T21:44:59Z.
Its exact status/evidence and next full linked review scope are recorded in
prerequisites-324962e-dispatch.md. Reuse this loop and earlier findings/analysis.
Both ordinary axes must assess the complete changed candidate; all mandatory
validation and immediate final verification remain pending. No acceptance yet.

## Round 4 — direct-consumer import corrections

### Frozen candidate and whole scope

- Coordinator: `/root/prerequisite_review`, continuing the existing loop.
- #10013 fixed base and independently confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- #10018 fixed base and independently confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Candidate: `324962e733886e66d6cd92af6cb68627ed4c8f1d`.
- Prior candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
- Isolated checkout: `/workspace/scratch/ca9a61d0bf30/import-correction`,
  branch `pfds/import-footprint-r2`. Coordinator preparation observed exact
  candidate `HEAD` and empty porcelain status.
- Full diff:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...324962e733886e66d6cd92af6cb68627ed4c8f1d`.
- Linked narrow diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...324962e733886e66d6cd92af6cb68627ed4c8f1d`.
- Full scope: 13 files, four commits, 954 additions and 2 deletions. The
  #10018 scope is five files and two commits. No exclusions or unrelated changes.
- Commit history: `ad73001` SharedList implementation; `70a1477` redundant
  adapter-tactic correction; `226ebae` direct imports in FRP Spec/Equivalence;
  `324962e` direct providers in affected FRP consumers. The complete titles and
  full SHAs are retained in the dispatch and candidate manifest.
- The candidate-to-candidate delta contains exactly one import addition in
  each of `Applications/FRP/Demand.lean`, `Applications/FRP/Finite.lean`, and
  `Examples/FRP.lean`. The earlier SharedList files are unchanged. Both axes
  still assess the entire fixed-base candidate, related definitions/consumers,
  preserved statements/cases and mandatory integration coverage.
- Main `conaled`, Map CachedClosure, Shared ValuePersistence and other Chapter 2
  work are outside this candidate. This prerequisite accepts no chapter.

### Requirements and retained evidence

All four saved requirement hashes match the round-3 table:
`REQUEST.md`, `REQUEST-union-v2.md`, unchanged `shared-persistence.md` v2,
and unchanged `import-footprint.md` v1. No acceptance scope was broadened or
narrowed. Both full sources remain available; this fact alone establishes no
source coverage or chapter completion.

The manifest is `../validation/import-footprint-candidate-r2.json`; its
capture-time "full validation not started" value is historical and superseded
by the running full-check record below. The implementation investigation is
`../research/import-footprint-r2.md`, and its exact non-import-byte comparison
is `../research/import-footprint-r2-source-comparison.json`.
The focused run `../validation/import-footprint-r2-focused-r2.json` records
exit 0 for `Examples.FRPDemand` and `Examples.FRP`, 1134 jobs in its log, and
unchanged recorded inputs. It ran on the then-uncommitted correction before
capture; the reviewers must relate its hashes to this candidate before using
it as evidence for a particular repair. It is not integrated acceptance.

### Stable findings carried forward

| Finding | Prior observed failure / current evidence | Disposition at dispatch |
| --- | --- | --- |
| PERSIST-VAL-001 | Unused success-branch adapter tactic; correction retained in `70a1477` and focused compiler evidence already reviewed. | Fixed with compiler evidence; preserve and reassess retained correction. |
| IMPORT-VAL-001 | `Demand.pending_registered` retained `n < n + 1` where `le_rfl` supplied non-strict reflexivity after missing simp/instance context. Candidate adds `Mathlib.Order.SuccPred.Nat`. | Candidate import repair and focused success supplied; independent disposition pending. |
| IMPORT-VAL-002 | `Finite.finiteHistory` could not resolve the finite union theorem through `s.biUnion`. Candidate adds `Mathlib.Data.Set.Finite.Lattice`. | Candidate import repair and focused success supplied; independent disposition pending. |
| IMPORT-VAL-003 | `Examples.FRP.ticks_finiteHistory` could not find `exists_nat_gt`. Candidate adds `Mathlib.Algebra.Order.Archimedean.Real.Basic`. | Candidate import repair and focused success supplied; independent disposition pending. |

The original diagnostics remain in
`../validation/import-footprint-226ebae-observed-errors.json`, and the first
focused correction's failure remains recorded. The obsolete full run's later
session interruption does not erase its concrete source diagnostics or turn
it into successful validation. Prior static review did not establish the
compilation compatibility that those diagnostics disproved.

### Exact validation gate and ownership

Root owns the running full check (execution session 4737 at dispatch). Its
record is `../validation/import-footprint-324962e-full-r1.json`; live log is
`../../active-validation/import-footprint-324962e-full-r1.log`. The record
identifies the exact candidate, start time `2026-11-02T21:44:59Z`, `running`
status and `acceptance: false`. The command uses the pinned offline Nix closure
and `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`.

The separately recorded ordinary-output copy is
`../validation/import-footprint-r2-cache-copy.json`: 599 modules selected from
identical source bytes with no existing destination outputs, complete saved
output sets, no source inconsistencies, and no copied approval record. This
is build-input provenance, not acceptance evidence. Stock Lake invalidation,
the integrity guards, all 957 integrated modules and the exhaustive proof audit
remain required. No toolchain, dependency pin, source policy, audit root or
allowlist changed.

The coordinator and reviewers must not compile in or mutate this checkout,
external dependencies or build outputs. A pass requires successful terminal
full build/audit, the matching `.lake/verification.json`, and final
`./check.sh --verify-candidate HEAD` evidence for this exact candidate. Root
supplies those items and repeats final verification immediately before
acceptance. Neither the focused result nor copied ordinary outputs replace them.

### Independent axes and continuation

The shared dispatch is
[`prerequisites-324962e-dispatch.md`](prerequisites-324962e-dispatch.md).
Reuse the existing independent Standards and Spec reviewer children and their
analysis, while reviewing this changed candidate over the entire fixed-base
scope. Root initially had two active implementation agents occupying the
remaining slots. Shared completed and released one slot, so
`/root/prerequisite_review/standards` resumed first. Spec awaits Map's completion
or the Standards reviewer's release. This sequencing follows available slots;
it does not omit either required axis.

- Standards round 4 / linked #10018 round 2: **Blocked — partial assessment
  paused after new full-check failure IMPORT-VAL-004.** The full-scope assessment
  and IMPORT-VAL-001..003 dispositions are incomplete. This is not a static-clear
  review of `324962e`.
- Spec round 4 / linked #10018 round 2: **Blocked — not resumed on this candidate;
  startup held for root's corrected successor and exact validation.** No Spec
  conclusion or new finding disposition is established for `324962e`.

Expected complete reports: `shared-persistence-standards-r4.md` and
`shared-persistence-spec-r4.md`, with linked ticket reports
`import-footprint-standards-r2.md` and `import-footprint-spec-r2.md`.
Preserve separate outcomes, stable finding IDs and all earlier reports.
Return concrete findings to root; do not self-fix. Static-clear reports remain
Blocked if required validation is unfinished and must be ready to continue on
terminal evidence. A further changed candidate requires another full-scope
round with both axes and the same fixed bases.

### IMPORT-VAL-004 — additional full-check failure and review hold

- Affected candidate: `324962e733886e66d6cd92af6cb68627ed4c8f1d`.
- Origin: root's ongoing full-candidate build; coordinator confirmed the exact
  text in `../../active-validation/import-footprint-324962e-full-r1.log`.
- Location: `Examples/IndefiniteService.lean:104:6`:
  `Unknown constant Nat.size_pow`.
- Associated diagnostic: unsolved goals at `Examples/IndefiniteService.lean:101:56`,
  with `bound : ℕ`, `h : ∀ (n : ℕ), n.size ≤ bound`,
  `large : (2 ^ bound).size ≤ bound`, and goal `False`.
- Status: **unresolved required-build blocker**. Root is investigating an
  import-only provider correction in a separate candidate. No provider or fix
  is presumed verified by this coordinator record.
- The full run continues other modules; no overall terminal result, exhaustive
  audit success or matching verification record is inferred from partial output.
- Root requested Standards to hold at a natural boundary and Spec not to start
  on the now-obsolete candidate. Standards acknowledged a read-only pause:
  candidate/ancestry/scope, the three-import delta and part of the correction
  evidence were checked, but the full assessment and finding reconciliation
  are incomplete. Its assigned reports must retain this partial/Blocked state.
- No candidate, dependency, build output, toolchain or gate was mutated by
  coordinator/reviewers. The active frozen `324962e` checkout remains untouched.

Await root's exact diagnostic handoff, new isolated immutable candidate and
full-scope manifest. Continue the same linked loop with new pinned round(s),
the existing independent reviewers, unchanged fixed bases/requirements, and
all four import findings plus PERSIST-VAL-001 preserved. Neither the partial
Standards work nor the earlier candidate's static-clear reports approve the
successor.

## Round 5 — natural-size provider successor

### Immutable scope and requirements

- Coordinator: `/root/prerequisite_review`, continuing the same linked loop.
- #10013 fixed base and confirmed merge base:
  `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
- #10018 fixed base and confirmed merge base:
  `70a1477d822efd4fdcec2007280f650bb4695eda`.
- Candidate: `901f734161920a76f3b399a575805b9a1d31e971`.
- Previous candidate: `324962e733886e66d6cd92af6cb68627ed4c8f1d`.
- Checkout: `/workspace/scratch/ca9a61d0bf30/import-correction-r3`, branch
  `pfds/import-footprint-r3`. Coordinator observed exact HEAD and empty
  porcelain status at preparation; both merge bases match the fixed bases.
- Full diff:
  `git diff cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833...901f734161920a76f3b399a575805b9a1d31e971`.
- Narrow #10018 diff:
  `git diff 70a1477d822efd4fdcec2007280f650bb4695eda...901f734161920a76f3b399a575805b9a1d31e971`.
- Full scope: fourteen files, five commits, 955 additions and 2 deletions.
  Narrow scope: six files, three commits, 16 additions and 2 deletions.
  No exclusions or unrelated changes.
- Commit sequence: `ad73001`, `70a1477`, `226ebae`, `324962e`, `901f734`.
  The dispatch and `../validation/import-footprint-candidate-r3.json` contain
  full SHAs, titles, file lists and exact candidate file hashes.
- The latest delta is one line in `Examples/IndefiniteService.lean`:
  `import Mathlib.Data.Nat.Size`. The full #10018 scope also retains the earlier
  changes in FRP Demand, Equivalence, Finite, Spec and Examples/FRP.
- Saved requirements are unchanged: original `REQUEST.md`, union clarification
  `REQUEST-union-v2.md`, SharedList v2 and import-footprint v1. Their exact
  fingerprints match the retained round-3 table and current manifest.
- Main `conaled`, Chapter 2 implementation and Chapter 3 readiness research
  remain outside this candidate and its acceptance. No chapter or implementation
  frontier advances through this prerequisite review.

### Finding history and available evidence

PERSIST-VAL-001 keeps its prior fixed-with-compiler-evidence disposition. All
four IMPORT-VAL findings retain their identities and observed diagnostics.
IMPORT-VAL-001..003 have the earlier three direct-provider repairs and focused
1134-job success; the partial round-4 Standards assessment did not finalize
their dispositions, and Spec did not start on `324962e`. No missing axis result
is manufactured or reused as approval.

IMPORT-VAL-004 is recorded in
`../validation/import-footprint-324962e-observed-errors.json`. The successor
adds `Mathlib.Data.Nat.Size`, whose pinned source declares `Nat.size_pow`.
The proposed repair and intended unchanged example are documented in
`../research/import-footprint-r3.md`. Full fixed-base source preservation for
all six import consumers was independently checked by the implementation
worker; its evidence is currently
`../../active-validation/import-footprint-r3-fixed-base-comparison.json` and
`../../active-validation/import-footprint-r3-source-comparison.json`, to be
retained under validation after terminal collection. These are source/evidence
checks, not either independent acceptance axis.

The focused target `Examples.IndefiniteService` is still running under root
ownership. Current record/log:
`../../active-validation/import-footprint-r3-focused-r1.{json,log}`. The record
identifies exact candidate `901f734`, sixty source/config/provider input hashes,
the pinned Nix command and private project outputs. It has no terminal result
at preparation. Do not treat it as green, close IMPORT-VAL-004, or infer a
runtime/resource improvement from its progress.

### Required full validation and reviewer scheduling

Full `901f734` validation has not started. The obsolete `324962e` check remains
live after its known source failure and cannot approve this successor. Root
will retain its terminal outcome and arrange any recorded ordinary-output reuse
without copying an approval record, then run the stock complete candidate gate
on `901f734`. All 957 integrated project modules, source/coverage and integrity
checks, exhaustive proof audit, exact `.lake/verification.json` and immediate
final `./check.sh --verify-candidate HEAD` remain required. The toolchain,
dependency pins, policies, guards, allowlist and scope are unchanged.

Reviewers and coordinator must not compile, mutate the frozen source, external
dependencies or build outputs, or start a competing validation process. Root
supplies focused and full terminal evidence. The focused run is development
evidence only, even if successful.

Initially both axes awaited Map's terminal focused evidence and released slots.
Ordered completed its bounded read-only readiness pass first. Root then
expressly superseded the wait-for-focused scheduling instruction, authorizing
`/root/prerequisite_review/standards` to resume full static review while that
build continues. Spec awaits Map's slot release. Only one reviewer slot is
available, so the axes are sequenced without omitting either or substituting a
coordinator assessment. All acceptance gates are unchanged. Both reviewers
must cover the full fixed-base
candidate, including SharedList statements/connected cases, all six changed
import consumers, affected unchanged dependencies/uses and every stable finding.

- Standards round 5 / #10018 round 3: **Blocked — full-scope static assessment
  complete, with 0 new or unresolved Standards code/prose findings and no worst
  code/prose severity.** IMPORT-VAL-001..003 are fixed with focused compiler
  evidence on independently matched inputs. IMPORT-VAL-004 remains statically
  supported but pending terminal compiler evidence; full exact-candidate
  validation, matching record and final verify remain unavailable. Complete
  reports: `shared-persistence-standards-r5.md` and
  `import-footprint-standards-r3.md`.
- Spec round 5 / #10018 round 3: **Blocked — full-scope static assessment
  complete, with 0 new or unresolved Spec implementation findings and no worst
  implementation severity.** IMPORT-VAL-001..003 are fixed with independently
  matched focused compiler evidence. IMPORT-VAL-004 remains unresolved pending
  terminal compiler evidence; full exact-candidate validation, matching record
  and final verify remain unavailable. Complete reports:
  `shared-persistence-spec-r5.md` and `import-footprint-spec-r3.md`.

Expected reports: `shared-persistence-standards-r5.md`,
`shared-persistence-spec-r5.md`, `import-footprint-standards-r3.md`, and
`import-footprint-spec-r3.md`. Preserve separate findings, exact SHAs, complete
evidence and prior outcomes. Static review may finish while the full gate is
pending, but no axis may pass without exact terminal success, matching record
and final verify. Return corrections to root and pin any further changed
candidate in another round against the same bases.

### Independent finding reconciliation

Standards independently confirmed both bases, exact candidate, all fourteen
manifest hashes, and fixed-base non-import-byte preservation for all six
consumers. It matched all 23 before/at-start/after hashes in the successful
1134-job focused correction record to committed `901f734`, inspected the
actual providers and completed the full SharedList/consumer assessment.

| Finding | Standards disposition on `901f734` | Spec disposition on `901f734` |
| --- | --- | --- |
| PERSIST-VAL-001 | Retained fixed with prior 664-job compiler evidence. | Retained fixed with prior compiler evidence. |
| IMPORT-VAL-001 | Fixed with focused compiler evidence; full gate pending. | Fixed with independently matched focused compiler evidence; full gate pending. |
| IMPORT-VAL-002 | Fixed with focused compiler evidence; full gate pending. | Fixed with independently matched focused compiler evidence; full gate pending. |
| IMPORT-VAL-003 | Fixed with focused compiler evidence; full gate pending. | Fixed with independently matched focused compiler evidence; full gate pending. |
| IMPORT-VAL-004 | Proposed repair statically supported; terminal focused/full compiler evidence pending. | Unresolved pending terminal compiler verification; proposed repair statically supported. |

At the Standards final status check, 22:18:05 UTC, the focused record had no end
time, exit code, final input snapshot or unchanged-input result. The candidate
verification record was absent. Standards returned to free its slot. Root then
explicitly lifted the Map-release scheduling hold and authorized retained
reviewer `/root/prerequisite_review/spec` to resume in that slot. The coordinator
has not converted Standards conclusions into Spec conclusions. Spec subsequently
completed its own full assessment and independently matched all fourteen
candidate hashes, four requirement hashes, six non-import comparisons, the 23
earlier focused input hashes and the sixty current before/at-start inputs.
At its 22:20:51 UTC status check, the focused terminal/after evidence and the
candidate success record were still absent.

### Round 5 coordinator closure of static review

Both complete axis reports cover the same immutable candidate, fixed bases,
requirements and full acceptance scope. Each records zero new or unresolved
findings within its source-review axis and no worst source-finding severity.
They retain the separate unresolved validation finding IMPORT-VAL-004; neither
the zero source counts nor the provider's static correctness closes it. No
concrete source correction or requirement change is currently requested.

The coordinator reread all four current reports and preserved the independent
dispositions above without reranking or merging away findings. Historical
reports, original diagnostics, failed/interrupted runs, and the partial
`324962e` Standards result remain unchanged. There is no Spec report or claimed
Spec assessment for `324962e`.

At coordinator closure, `import-correction-r3` still had exact `901f734` HEAD
and empty porcelain status; `.lake/verification.json` was absent. The focused
record still had only a start time and `acceptance: false`, with no terminal
exit/after result. Root's supplied handoff still records full successor
validation as not started. Both outcomes are **Blocked** until root supplies:

1. Terminal focused evidence or matching successful exact full-build coverage
   resolving IMPORT-VAL-004 with unchanged inputs.
2. Successful full `./check.sh --candidate HEAD` on `901f734`, covering all
   957 integrated modules, mandatory checks and the exhaustive proof audit.
3. The matching `.lake/verification.json` and immediate final
   `./check.sh --verify-candidate HEAD` evidence on that candidate.

Re-engage the same independent reviewers on those evidence items if the source
candidate is unchanged. A further changed candidate requires new full-scope
rounds with all IDs and bases retained. Coordinator/reviewers ran no compiler
and changed no candidate, dependency, build output, requirement or gate. The
four current axis reports and this final reconciliation postdate checkpoint021
and are ready for the next checkpoint.

## Native continuation takeover — 2026-11-03, after checkpoint 042

Root assigned `/root/direct_toolchain_validation_plan` to continue this existing
linked loop after the earlier coordinators became unavailable. The complete
prior preparation and four independent reports remain unchanged. Candidate
`901f734161920a76f3b399a575805b9a1d31e971`, both fixed bases, the fourteen-file
and six-file scopes, and all historical finding dispositions are retained.

Read-only identity reconciliation matched all fourteen candidate sources,
four original requirements, fourteen applicable guidance files and all four
frozen axis reports. The three later user clarifications authorize the direct
native launch route while retaining the formal gates. Current dependency and
runtime/controller identities match the start record of the fresh native run.
The receipt is
[`prerequisites-901f734-continuation-identity-042.json`](../validation/prerequisites-901f734-continuation-identity-042.json).

The complete takeover, regression applicability decision and remaining closure
sequence are in
[`prerequisites-901f734-coordinator-takeover-042.md`](prerequisites-901f734-coordinator-takeover-042.md).
Root agreed to retain all three documented regression suites for this native
runtime transition, with separate actual evidence and genuine prerequisites.
This does not require rerunning all suites after every later proof edit.

Planned replacement Standards and Spec owners are `/root/recovery_audit` and
`/root/chapter02_continuation_plan`; both confirmed independence from the
prerequisite implementation. They have received preparation questions only.
Acceptance review remains held until root supplies actual full, applicable
regression, matching success-record and stock verification evidence. Both
scopes remain **Blocked**; IMPORT-VAL-004 is still awaiting explicit independent
reconciliation. No chapter acceptance or third code review is introduced.

## Common-candidate continuation 045 — pending

Root explicitly retargets scope10013 to `{'commit': '3cf3de4fbc24c1a144353ae64b13b72f5ead54a5', 'tree': 'd3dcf94916de5ccaf3df357e06192e69c4e0cf33', 'preserved_branch': 'pfds/signed-potential', 'planned_isolated_checkout': 'validation-pfds-integration', 'restored_main': '76d77a107deb37c30e0b061c30b03a3f8c6aa12c'}` from historical `901f734161920a76f3b399a575805b9a1d31e971`. Original full base `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833` remains fixed; the complete delivered range has 170 files/68 commits. Existing requirements, source ownership, findings and prior outcomes remain above. Full matrix and independent dispatch: `common-integration-scope-matrix-045.md`, `common-integration-dispatch-r1-045.md`. Both current independent axes, actual fresh full/audit, applicable regressions and immediate verification are pending. No acceptance or old-SHA approval is inferred.
