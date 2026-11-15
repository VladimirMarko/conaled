# FDSA-001 — Chapter 1: Basics

State: **accepted and integrated locally at 07e480f6ec9958d4975bb90151005b84f2907614**. Both final axes and full native validation passed; immediate verification passed before fast-forward. Acceptance checkpoint next.
Triage: ready-for-agent. Parent: FDSA-000.

Source: pinned July 27, 2026 PDF, printed pages 1–10.
Depends on: FDSA-ENV, FDSA-SOURCE.

## Acceptance checklist

- [x] Map the source's total functional language, types, notation, pattern
  matching, coercions, function update and multisets to existing Lean/Mathlib
  interfaces. Check meaningful examples, including truncated natural subtraction
  versus integer/real subtraction and multiplicity-sensitive operations.
- [x] Connect append equations and associativity to standard Lean List results.
- [x] Establish the stated gcd computation-induction schema with its nonzero
  branch premise and termination argument; retain a meaningful specialization.
- [x] Represent the source's call-count rules for values/primitives, calls,
  conditionals, case and let using existing compositional measured operations.
  State the bounded scope and the optional omission of a nonrecursive call tick.
- [x] Match append call-count recurrence; prove exact cost length + 1.
- [x] Instrument naive reverse according to the source recurrence, prove erasure
  to List.reverse, prove the quadratic upper bound, and solve the exact-count
  exercise (triangular count).
- [x] Reuse or implement accumulator reverse, prove arbitrary-accumulator
  correctness, exact cost length + 1, and empty-accumulator refinement.
- [x] Connect both realizations to conaled's resource and semantic interfaces;
  retain a client that compares their distinct counts for the same output.
- [x] Prove the qualified coarse/fine tariff, entry-tick and shared-demand
  comparisons in the frozen cost-model addendum. Preserve the source's
  conditional runtime boundary without dismissing these mathematical claims.
- [x] Complete per-claim statement review and meaningful checked examples,
  including the reopened cost-model obligations.
- [x] Integrate modules into public import coverage and exhaustive proof audit.
- [x] Capture immutable candidate and pass applicable project verification.
- [x] Independent Standards review: no unresolved findings.
- [x] Independent Spec review: no unresolved findings.
- [x] Verify accepted candidate identity, update local tracker, create/upload
  checkpoint, then advance to Chapter 2.

## Reuse assessment (provisional)

`Resources.Measured`, `Resources.bind`, `Resources.pure`,
`Resources.erasureSquare` are the existing observation/composition vocabulary.
`Resources.SymmetricCosts.reverseRun` appears to implement the exact accumulator
reverse and call-count recurrence. The tree-flattening append helper counts
copied cells rather than calls, so its raw cost cannot substitute for the book's
length + 1 count.

## Validation and review

Previous candidate: `1aabd512284fe86254278ac631eda061d311050b`.
Its focused algorithm/example builds pass, but its routine guarded incremental
full check exited 120 with disk exhaustion and a truncated log. Independent Spec review has reopened completeness
with major findings SPEC-001, SPEC-002 and SPEC-003. This candidate cannot close
the chapter merely by passing validation. Standards remains validation-blocked;
the old assessments and attempts are preserved in `../reviews/chapter01-round1.md`.

The exact repair requirements are in
`../reviews/chapter01-cost-model-requirements.md`, SHA-256
`1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1`.
Development worktree: `conaled-ch01-cost-models`, branch
`work/fdsa-basics-cost-models`. Focused results are recorded below; no full repair
validation or acceptance is claimed.

The repair is now committed as
`a14977b9e316cc484ffad8a470d26b15615956c0`. It supplies the three requested
model comparisons and connected cases. Author-side statement review and a
bounded architecture/API source preflight found no mathematical blocker;
these are not independent final approvals or Lean validation. See
`../reviews/chapter01-cost-models-candidate.md` and
`../reviews/chapter01-cost-models-author-review.md`.

The retained independent Spec reviewer subsequently inspected the actual
committed repair against the frozen addendum and found no new statement/source
problem. Its narrow assessment is
`../reviews/chapter01-cost-models-spec-preflight.md`. This is not final approval:
SPEC-001/002/003 and SPEC-V001 remain unresolved until matching validation and
the retained final review are complete. No source or candidate changed.

## Failed old gate and direct repair recovery

Session 80227 exited 120, observed 2026-11-02 at 15:44:10 UTC. The old source
was clean and no success record exists. The log and surviving affected-module
families were copied with exact identities before any invalidation to
`../provenance/chapter01-enospc-20261102/`. Space was recovered only from
verified durable checkpoint duplicates and recorded disposable outputs.
FDSA-INC01 tracks this local event and its recovery.

The retained Standards disposition at
`../reviews/chapter01-enospc-recovery-standards.md` permits proceeding directly
to a14977b after evidence preservation and adequate capacity. Every focused,
guarded full-build/audit, independent-review and final-verification obligation
remains. Explicit ENOSPC alone does not establish the documented GraphEmission
stale-artifact recurrence or require fresh mode; any new stale or unexplained
integrity evidence must be investigated under the runbook. No acceptance is claimed.

Focused attempt 1 at a14977b exited 1. The SharedDemand core compiled, while
CallComparison and the SharedDemand examples had ordinary proof-script
errors. See `../reviews/chapter01-repair-compiler-findings.md` and the complete
log/provenance. C1-ELAB-001/002 are implemented in proof-only correction
`057e07cd0bd16c7877967aedc46aeefaca01a7a6`, with all statements, hypotheses,
definitions and cases preserved. The isolated checkout is clean at 057e07c.
The same focused retry and complete guarded gate remain pending; no finding
or chapter is accepted by this correction. Checkpoint 0040 is saved successfully.


Focused attempt 2 at 057e07c exited 1. CallComparison compiled, while the examples
reported one residual reduction error and two linter errors. Proof-only commits
94d9af5 and 503081d address them; exact identities and C1-ELAB-003 are in the same
compiler-findings record. The isolated checkout now validates committed candidate
503081dccdbe64188eceb6524724fc445c840d68 in focused attempt 3. Definitions,
statements, hypotheses, expected cases and warning policy remain unchanged.
The full guarded build/audit, both final reviews and immediate verification
remain pending; no chapter or shared unit is accepted.


Focused attempt 3 confirmed CallModels, with one final unnecessary-simpa diagnostic
in the cache example. Commit 07e480f6ec9958d4975bb90151005b84f2907614 resolves it,
and focused attempt 4 passed all four targets with exit 0 and clean matching source.
C1-ELAB-001/002/003 have focused compiler confirmation. Their full final-review
confirmation and every whole-candidate acceptance gate remain required. The next
action is the full guarded candidate check, with exact evidence retained for both
independent axes. The original base and all requirements/findings remain unchanged.

Checkpoint 0041 is saved successfully for the focused-pass candidate, compiler
records and all earlier source/history/control work. No acceptance is implied.

## Full attempt terminal outcome unavailable — FDSA-INC02

Session 83124's tool handle was unavailable on 2026-11-02 at 20:17 UTC.
The default PID probe lacked /proc and was inconclusive. Qualified elevated
host checks subsequently found no established chain or exact-review-cwd
process. The unchanged candidate is clean at 07e480f, but no actual or copied
verification record exists. The original running metadata and complete partial
log are preserved under `../provenance/chapter01-repair-interruption-20261102/`.
The 185,588-byte log SHA-256 is
`a3ea7d678554d2d8b746f41f0ffcd47c4b91d99dbd12f7e8315185ba822ef899`.
No terminal exit code or cause is invented. This is separate from INC01's
known ENOSPC exit; no new cache mechanism is established. Retained Standards
is assessing continuation before any new compiler/checker. Original scope,
requirements, findings and focused evidence remain unchanged; no checklist
item is closed by the interruption or its preservation.

The retained session-recovery Standards report now confirms ordinary full
candidate-mode eligibility without a fresh trigger or extra generic preservation
pass from the supplied interruption evidence. Its exact identity is in INC02.
Root has read the full report and will save checkpoint 0051 before a new full
attempt. No reviewer executed validation or granted final acceptance.

### Separate guarded retry after preserved session loss

INC02 records attempt 1's unknown terminal outcome without overwriting its
log or raw metadata. Retained Standards permits the unchanged ordinary route;
checkpoint 0051 was saved first. Attempt 2 on clean 07e480f began at
20:37:50 UTC, session 61365. Source/coverage/compiler and the prebuild guard
have passed; the full integrated build remains in progress. Its separate log
and atomic metadata are in `chapter01-repair-incremental-attempt2.log` and
`chapter01-repair-guarded-attempt2.json`. All four retained findings and final
review/verification requirements remain open. No chapter is accepted.

## Current recovery before attempt3

The repaired candidate remains exact clean07e480f. Full attempts1 and2 both
have unknown terminal outcomes, with separate preserved logs/process evidence;
neither produced a success record. Retained Standards assessed the second
interruption and concrete unexecuted external launcher, with no blocking
finding or new fresh-mode trigger. Root read the complete report and helpers.
Checkpoint0054 and immediate no-writer/candidate checks precede any new full
run. All original scope, open Spec findings and final acceptance gates remain.

## Attempt3 continuity before checkpoint 0056

The reviewed single launch occurred at 22:08:37 UTC after saved checkpoint0054.
The 23:02:32 host observation confirms the same wrapper/checker/Lake identities
and clean immutable 07e480f; Lean was compiling Examples.FRP after successful
Applications.FRP.Finite completion. The recorder remains running, without a
terminal result or verification copy. See
`provenance/chapter01-attempt3-progress-before0056.json`.

The filesystem reported 3,018,862,592 free-block bytes and zero unprivileged
available bytes to effective UID0. The latter alone is not a new ENOSPC error
or failed exit. The earlier genuine INC01 failure and both unknown repaired-run
outcomes remain unchanged. Full-check success, both retained final review axes
and immediate verify-candidate are still required before any acceptance.


## New-workspace recovery, 2026-11-03

Candidate 07e480f and the full original/addendum scope are preserved. The old
full attempt 3 has unknown terminal outcome; no verification record was in
checkpoint 0065. Its running metadata is historical. A clean isolated checkout
is restored, but the current pinned environment cannot be bootstrapped under
this session's observed restrictions. No new compilation or final review ran.
All four Spec findings and both final axes remain pending. See CURRENT.md and
FDSA-ENV.md; no mathematical requirement or chapter dependency was changed.


## Direct-toolchain exception and smoke result — 2026-11-03

Nix is no longer mandatory under the explicit user instruction. Exact official
Lean/Lake and all nine dependency source revisions have been acquired. Lean
startup still fails on the unavailable own-process `/proc/<PID>/exe` path, so
no repaired full attempt 4, project compilation, audit or final review has begun.
All original formal requirements and acceptance gates remain. See FDSA-ENV.

## Unified native recovery and actual full validation — 3 November 2026

Recovered exact clean07e480f with complete14-path scope, both unchanged frozen
requirements and all existing findings. Exact book PDF independently reacquired.
The supplied unified kit and complete environment passed setup; checkpoint0070
was saved successfully and blank-restored with all45refs and both worktrees.

Fresh full attempt4 is running through the unchanged project checker with
`--candidate HEAD --fresh --jobs 1` and one compiler thread. Source/coverage/
compiler checks passed; compilation and exhaustive audit are not yet complete.
The owned recorder is provenance/chapter01-unified-fresh-attempt4. Both final
independent review axes are inspecting the stable candidate and must reconcile
the actual terminal result and matching verification record before approval.
All SPEC-001/002/003/V001 and final acceptance gates remain pending.

## Accepted candidate — 3 November 2026

Both independent final axes passed the complete fourteen-path scope against
original base 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd. SPEC-001/002/003 are
fixed with source and matching compiler/audit evidence; SPEC-V001 is resolved.
The unchanged candidate 07e480f passed fresh attempt 4 (actual exit 0; all 961
modules; exhaustive allowed-axiom audit). Immediate --verify-candidate HEAD
passed at 21:16:48 UTC, then work/fdsa-book fast-forwarded to exactly that commit.
The earlier provisional text is retained as history, not current limitations.
Evidence and exact report hashes are in provenance/chapter01-acceptance-20261103/.
Acceptance checkpoint 0077 is the immediate next action before Chapter 2.

Acceptance checkpoint 0077 saved successfully: libfile_3fcaa777fa608191a548f5de4b791fe5, 13,907,578 bytes, SHA-256 2ebfde2183f9fdf8da0fa8e8e32ecf138f0eff95b82366d091b336bb5c2372a9. Chapter 2 is now active.
