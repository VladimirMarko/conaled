# Receiving validation handoff

## Delegated gate and ongoing work

The user explicitly delegates the final whole-library build and exhaustive axiom
audit to the receiving integrator's normal development environment. A completed
local full build is therefore **not a prerequisite for further mathematical
development or a durable checkpoint**. Do not restart a full build after every
resume merely to recover that prerequisite.

Continue focused checking of changed modules and affected clients, statement
review of new or changed mathematical claims, and independent Standards and Spec
source review within the existing implementation/review loop. Record the exact
candidate, inputs, commands, coverage and results. If the local compiler is
unavailable, mark new work source-reviewed or uncompiled as appropriate; preserve
it without claiming a checked result.

The final receiving gate still blocks acceptance or merge into `conaled`.
**`INT-SP-001` remains open as that receiving gate**, linked to `INT-090`;
delegation does not resolve the finding or supply either final review approval.
Carry its history, all other findings, and prior validation failures forward.

## Identity and authority

| Binding | Required identity |
| --- | --- |
| Fixed full-spec integration review base | `9175737c2b14ef738cfb6c2cdc68d885c0805ddd` |
| Pinned upstream master incorporated by this handoff | `04514fc144dcebdd2b6d4aea5faf2f9cbf229362` |
| Delivered candidate | `18235331da1fe343d09080ca4c41173f9b4d9963` |
| Captured candidate tree | `63205d8a3ff27deb3680c613b70085163f289b83` |
| Candidate snapshot receipt | `books/common/evidence/integration-candidate-r4.json` |
| Review scope manifest | `books/common/evidence/integration-scope-20261114-evening.json` |

These are this handoff's immutable bindings; a later candidate requires updated
receipts and review in the same loop.
`source/refs.json` and `source/integration.json` at the checkpoint root own source identities; [REVIEW.json](REVIEW.json) owns the
review record and [ISSUES.json](ISSUES.json) owns local issue state. Preserve the
original full-spec base across upstream incorporations and corrections.
Earlier approvals and historical successful book builds do not approve a later
candidate.

Follow the actual pinned checkout's `AGENTS.md`, skills, README and
`docs/agents/review-loop.md`. The user's exceptions remain: issue/spec tracking
is local and checkpoint-persisted; Nix is optional, while the prescribed pinned
inputs remain required. [RESUME](../../docs/RESUME.md) owns setup; this document
does not create a second setup procedure.

## Receiving procedure before acceptance or merge

1. Restore and verify the delivered source and review receipts. Prepare a clean,
   isolated checkout of the exact candidate with pinned dependencies, compiler
   and configuration. Keep these inputs stable throughout validation and
   acceptance. If applying the patch requires conflict resolutions or other
   task changes, capture and review the resulting candidate in the same loop;
   retain the fixed full-spec base and all findings. Applying a standalone patch
   and making a new commit also creates a new candidate identity, even when its
   tree matches this handoff. Record that identity and reuse prior analysis only
   where the review procedure permits; validate the actual receiving commit.

2. In the configured development environment, run the normal full gate:

   ```sh
   ./check.sh --candidate HEAD
   ```

   Require an observed successful terminal result, all integrated-module
   coverage, successful integrity guards, the exhaustive axiom audit, and the
   matching `.lake/verification.json`. Preserve complete terminal evidence,
   resolved candidate and input identities, and the verification record in
   the receiving review evidence. Only `propext`, `Classical.choice` and
   `Quot.sound` remain permitted.

3. Add `--fresh` only when the checkout's README requires it, including build
   tooling, toolchain or dependency changes, suspected stale project outputs,
   or another applicable fresh-validation trigger. A restored workspace or a
   desired concurrency setting alone is not a trigger. Fresh mode's
   `--jobs N` controls concurrent compiler processes; it is rejected for the
   normal incremental check.

4. Supply the successful exact-candidate evidence to the existing independent
   Standards and Spec reviewers. Both must approve the same candidate and
   versioned full requirements with no unresolved findings. Have the review
   coordinator reconcile `INT-SP-001` against that evidence; retain its stable
   identifier and history.

5. Immediately before acceptance or merge, run in that isolated checkout:

   ```sh
   ./check.sh --verify-candidate HEAD
   ```

   Confirm the resolved commit is the approved candidate. Run
   `scripts/review_snapshot.py compare` with the approved receipt, explicit
   scope/exclusions, and the actual commit or paused checkout being accepted.
   Preserve both successful results. A changed candidate, failed verification,
   comparison mismatch or new integration resolution requires applicable
   revalidation and another review round.

The receiving integrator owns troubleshooting of a failed full gate in its
normal environment. Keep the gate open and preserve the actual failure; return
source corrections through the same review loop. An interrupted process, old
success message, missing receipt, setup smoke or focused build cannot close it.

## Standalone patch

The separately delivered `conaled-textbooks-012.patch` applies to the pinned
upstream above. It is a byte-identical re-export of the historical009 patch.
Its fresh private-index application reconstructs exactly the delivered candidate
tree; `evidence/patch-export-012.json` records the hash, base, candidate and
reproduction command. The historical009 receipt remains unchanged. The source bundle remains the complete
history and recovery owner. The patch can be regenerated from its recorded two
commits using `git diff --binary --full-index`; no earlier archive or separate
patch file is required to restore this checkpoint. Patch application checks are
source checks, not Lean compilation or axiom-audit evidence.

## Resource settings

The requested unrestricted local attempt and its single retry have been spent.
`STATUS.md` owns their disposition. The user now requests a receiving handoff;
do not start another local attempt or setup campaign on resume. The instruction
to remove agent-imposed resource caps still supersedes earlier1/2/4 guidance.
The receiving full gate above is the remaining execution assignment. Any future
successful result belongs to its actual candidate and must be reconciled through
the existing review loop.

[Current native command settings](EXECUTION.md) is the single current
owner of the launcher prefix and its acceptance-command examples. Use that prefix
for the checker commands above; do not recover a fixed thread count from an old
receipt or the immutable kit's historical examples. It removes the launcher's
injected `LEAN_NUM_THREADS` in the child, supplies no numeric replacement, and
distinguishes setup's detected CPU count from full-build settings. The protected
kit remains unchanged. Pinned inputs, platform controls and every validation
check remain in force; this resource instruction is not a fresh-mode trigger.

Preserve the launcher's pre-child metadata unchanged and supplement it with the
exact argv and the effective environment of the process that execs the checker.
The launcher receipt alone does not describe the child after `env -u`.

Keep source and configuration stable throughout receiving validation. Record success,
source failure, external termination or incomplete execution according to actual
evidence. No timeout, OOM diagnosis or compiler success may be inferred merely
from elapsed time, a missing handle or an old success record. `INT-090` owns the
actual outcome; `analysis/consolidation-next-20261114.md` owns the proposed scope
boundary and subsequent mathematical slices.

## Durable continuation

The root coordinator owns canonical checkpoint updates, source merge and snapshot
capture, review reconciliation, and upload. This handoff does not itself record
a full-check success or permission to publish externally.

[DURABILITY](../../docs/DURABILITY.md) remains binding: after a wipe or missing
authoritative source, explicitly request and wait for the latest archive before
project work resumes. A checkpoint is complete only after verified recovery and
an observed successful owner-root `create_library_file` upload. If that upload
is unavailable, fails or is uncertain, report promptly and stop further project
work. Preserve this receiving gate and useful unfinished mathematics in each
subsequent checkpoint.

