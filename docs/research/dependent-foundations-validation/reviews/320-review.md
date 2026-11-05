# #320 independent review record

Status: round 1 complete. Standards and Spec both passed on the exact candidate
with zero findings. Matching validation and final candidate verification passed.
This record is outside the source diff and belongs to the existing implementation
loop. `/root/trial320` owns corrections; root owns dispatch provenance, shared
synthesis, tracker operations and merge.

## Pinned requirements and prospective evidence

- Full acceptance: `/tmp/conaled-314-320/specs/320.json` and
  `/tmp/conaled-314-320/specs/orchestration.md`.
- Dispatch constraints: `records/320-dispatch-preparation.md` and
  `records/320-dispatch-approval.md` in the same workspace.
- Expected review base: `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96`.
- Source workspace: `/tmp/conaled-314-320/320`; this mutable checkout is not
  itself the review candidate.
- Interface freeze: `dbf56af4845f954cf6ebdcf8bc3faeed268f5ce0`, approved at
  `2026-11-05T02:32:57.493576+00:00`; interface source is the expected base.
- Held-out selection record: `2026-11-05T02:34:14.491324+00:00`.
- Prospective round snapshot: `6ace04de2582151dccfb8005e0f17fd604c1033b`,
  approved at `2026-11-05T02:55:47.065767+00:00`.
- Prospective manifest SHA256:
  `8f5f37605c0df1a57cc4b79c1189bc5646ccb085da33f1e59895b9bfce7805a0`.

These values were read from the supplied records and source freeze. Final review
must check retained immutable inputs and author dispatch chronology against them.
The prospective approval is permission to conduct the trial, not acceptance of
its outcome.

## Candidate handoff required before dispatching review axes

1. Supply the exact candidate SHA and stable isolated checkout. Resolve base,
   candidate and merge base; establish ancestry and a nonempty full diff using
   `git diff <base>...<candidate>`, with `git log <base>..<candidate> --oneline`.
   Record scope, exclusions, and incorporation of the approved integration tip.
2. Supply the final report, complete author evidence and evaluation inventory,
   accepted source hashes, replay results, coverage/statement review, exhaustive
   author audit, integrated validation and four audit fixture results. Retain
   failed attempts and diagnostics. Identify source files that are exact author
   submissions separately from reference solutions and coordinator additions.
3. Preserve exact spec contents and candidate identity in the round record.
   Provide immutable candidate source access via `git show` or an isolated
   checkout; reviewers must not inspect a moving working tree as their candidate.
4. Supply `./check.sh --candidate HEAD` command, result, log, candidate identity
   and `.lake/verification.json`. Full builds use the shared build lock and
   documented Nix/direnv environment. Explain whether README requires `--fresh`.
   Required validation must cover this tree and relevant inputs.
5. Immediately before acceptance, run `./check.sh --verify-candidate HEAD` in
   that isolated checkout and retain its exact candidate and result. A successful
   author elaboration or reference audit does not replace integrated validation.

## Whole-trial evidence checklist

- Recompute interface and prospective manifest hashes, allowed source closures,
  public archives/manifests and prompt identities. Verify no later support or
  interface edits were silently folded into the approved round.
- Verify selection after interface approval and dispatch after complete round
  approval. Verify fresh fork-none authors, no private solutions or other-arm
  work in public source/history/compiled modules, and disclosed common support.
  Preserve instruction-based exposure limitations and unavailable telemetry.
- Check calibration preceded held-out work and used separate immutable checked
  source. Account for commands, timestamps, exit codes, stdout/stderr, assistance,
  reported exposure and stopped/failed attempts. Preserve preparation failures.
- Match accepted source bytes to author archives, replay sources and integrated
  copies. Attribute any coordinator repair separately; do not substitute private
  reference results for missing accepted author coverage.
- Check the shared arbitrary full contextual model class with Stable Sigma,
  including judgmental eta, and the same arbitrary dependent tail, Q and p.
  Reject silent native-only specialization or added final alignment premises.
- Check the exact selected J certificate and reflexivity branch conversion,
  arbitrary two-substitution source typings, value and certificate equations,
  both family equations and composite-family conversion. Retain source typing
  and semantic validity, rather than accepting raw evaluation equalities alone.
- Check constructed dependent weakenings and their generic witness: the second
  family's dependence on the first identity witness must remain explicit, and
  the instance must use the generic result without assuming substitution typing.
- Check generic value/certificate/type interpretation and exact reduct recovery.
  Candidate Sigma source embedding and validity must be explicit. Baseline
  unchanged-reduct interpretation must not be described as source Sigma support.
- Assess separate constructor formation, dependent elimination, computation and
  eta evidence. Keep that capability assessment distinct from annotation effort.
- Assess remaining caller obligations by mathematical requirement, model-builder
  coherence, interface/presentation burden, host encoding and documentation.
  A record demanding the old alignment equalities does not establish removal.
- Separate preparation, references, support/model engineering, measured author
  work, assistance and coordinator repair. Assess the decision against observed
  obligations and failures; preserve precise limitations and owned continuation.
- No causal productivity, human-usability or higher-adoption claim. Preserve
  #107/#108 ownership and theorem gate; no #260 activation. Repairs to tested
  interfaces require a new prospective round and fresh held-out work.

## Independent review dispatch and correction procedure

Use `.agents/skills/code-review/SKILL.md` with
`docs/agents/review-loop.md`. Dispatch fresh independent Standards and Spec
reviewers only once the candidate and validation handoff is available. Supply
the same exact SHAs, full diff, commit list, exclusions, saved requirements,
whole-trial evidence and this finding record to both. Both reviewers apply
example-driven-development statement review to all new or changed formal claims,
including references, cases and accepted submissions.

Standards reviews applicable candidate AGENTS guidance, README, architecture and
language direction, glossary/ADRs, code-review heuristics, experimental protocol,
provenance and validation requirements. Spec reviews full #320 acceptance,
matching mathematical contracts, declaration coverage, assumptions, definitions,
selected-data observations, inhabited cases and justified decision scope.

Keep findings separate, with stable IDs `320-STD-001` and `320-SPEC-001` onward.
Route corrections through `/root/trial320`. A changed candidate needs both axes
again on full task scope; carry prior findings and evidence forward. The
coordinator reconciles reports and does not add a third review axis. No source
edits, merge, push or issue closure are authorized for this review coordinator.

## Standards

Outcome: Passed. Findings: 0. Worst severity: none. Complete independent report:
[320-standards-round1.md](320-standards-round1.md).

## Spec

Outcome: Passed. Findings: 0. Worst severity: none. Complete independent report:
[320-spec-round1.md](320-spec-round1.md).

## Validation

Matching replay, statement coverage, proof audit, integrated validation, four
audit fixtures and candidate verification passed. See the round 1 evidence below.

## Round 1 pinned scope

- Base and merge base: `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96`.
- Candidate: `c32057aac5bb1da88b110e99db50093a23f783f4`.
- Candidate checkout: `/tmp/conaled-314-320/320`; clean at dispatch.
- Diff: `git diff 7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96...c32057aac5bb1da88b110e99db50093a23f783f4`.
- Full scope: 422 changed files; no exclusions. Whitespace in immutable raw
  evidence remains within review scope and must retain its original bytes.
- Commits in scope, oldest first: `dbf56af`, `6ace04d`, `0df02a3`, `90e6af5`,
  `2aff085`, `86a5470`, `c32057a`.
- Saved requirement contents remain `specs/320.json` and `specs/orchestration.md`.
- Fresh Standards reviewer: `/root/review320/standards`, fork-none.
- Root reports full 1091-module build and exhaustive 54315-logical-declaration
  audit succeeded with the standard three axioms. This report is provisional
  until the matching final handoff and receipt are supplied and inspected.

### Round 1 validation and reviewer assignments

Fresh Spec reviewer: `/root/review320/spec`, fork-none. Both reviewers received
the complete scope and the finalized handoff at `reviews/320-handoff.md`.
Matching evidence is under `/tmp/conaled-314-320/records/320-c32057a-*`:
`validation.json`, `candidate.txt`, `audit-fixtures.txt`, `verify.txt`, and
`verification.json`. Commands in the isolated checkout used direnv and the
shared `build.lock`. Full candidate validation, all four fixtures and immediate
candidate verification exited zero. The saved receipt matches the live receipt
and names `c32057aac5bb1da88b110e99db50093a23f783f4`, incremental mode. No build
tooling, dependency or toolchain change or stale-artifact suspicion requires
fresh mode. The coordinator will verify again immediately before acceptance.

## Round 1 accepted outcome

Both independent axes passed on base
`7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96` and candidate
`c32057aac5bb1da88b110e99db50093a23f783f4`, each with zero findings and no
worst severity. Their complete reports are linked above and remain separate.
No correction round was required. Both reviewers independently assessed the
whole trial, exact evidence and applicable formal statements. Their findings
records contain no unresolved findings.

After both reports were received, the coordinator ran
`direnv exec . ./check.sh --verify-candidate HEAD` in the isolated candidate
checkout. It exited zero and matched the approved candidate in incremental
mode. `320-review-final-verify.json` preserves that result. Root must retain
exact candidate identity through integration and any later verification.

Approval covers the restricted selected-data author trial, its report and
evidence. It does not establish productivity, human usability, higher-model
adoption or broad migration. Separate successor #323 owns the proposed facade
repair and a fresh retest; its root-owned record adds no source change here.
No source edits, merge, push or tracker operations were performed by this review
coordinator. Final full-spec integration review remains root's next stage.
