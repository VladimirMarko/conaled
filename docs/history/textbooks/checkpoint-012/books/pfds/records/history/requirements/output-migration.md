# Accepted ordinary-output handoff — operational requirements v1

Source: the user's local-only conaled/PFDS request, the project's implementation
and review rules, root's 2026-11-03 assignment to output_migration_author, and
research/ordinary-output-handoff-design.md (SHA256
08d3cad5cc7cf01fd6ca35d699242ad74d6efa2370960f4dda80006e0ff9d197).
This is an operational subtask of local10000, not a new formal acceptance scope.

## Complete intended scope

Implement a bounded copy/verify/retire handoff of ordinary completed compiler
outputs between two inactive, exact local candidates. Preserve all source,
dependencies, setup files, approval records and own-candidate acceptance gates.
The three delivered files are session/validation/migrate-accepted-outputs.py,
session/validation/test-output-migration.py and the complete implementation
handoff in session/research/output-migration-implementation.md. No exclusions.
Do not run a real transfer until this operational loop passes and the actual
donor has passed its full independent acceptance workflow.

## Preconditions and identity

1. Require an actual accepted donor: its own terminal full stock candidate
   build, exhaustive audit and matching verification record; both independent
   review axes reconciled for every acceptance scope; immediate final stock
   verification and recorded local acceptance. Keep separate10013 and10018
   report identities for donor901. Metadata binds evidence; it does not prove
   that a human-readable review really passed. Root must assess those reports.
   Never fabricate a successful receipt or migrate from the running901 build.
2. Freeze source and target. Require exact clean heads, pinned configuration,
   tooling and dependencies; private ordinary build directories and no active
   compiler/writer users. Use the established full/focused lock discipline and
   pinned Nix environment. Do not modify process or resource settings.
3. Reuse the unchanged stock expected_artifacts/inspect_outputs implementation
   and hash adapter. Their fixed identities, and the existing warmer's identity,
   are in the handoff report. Do not edit traces, repair a guard failure, replace
   the hasher, copy approval, or bypass a check. Keep the public fixture verifier
   seam separate from the production CLI; it is not real output validation.

## Selection, transfer and retirement

4. Retain the existing identical-source and complete-group selection policy.
   Skip a whole module when any pre-existing target output is present; preserve
   existing focused outputs. Do not overwrite or mix generations. Changing
   selected inputs or unexplained parser/hash errors stop with retained evidence.
5. Use at most64MiB per batch, minimum320MiB free reserve, and explicit additional
   journal headroom. Root chose320MiB instead of the assessment's provisional
   lower256MiB because recovery capture and compilation need space. Never lower
   the reserve or change expectations to make a run fit. Refuse before copying
   if measured free space cannot cover the next complete batch and reserve.
6. Check selected source hashes. Copy artifacts and corresponding sidecars into
   private target files, with each module's trace last. Keep exact descriptors,
   size and SHA256; check source stability and destination bytes. Independently
   run unchanged stock target verification for the fixed batch. Durably record
   complete verified target success BEFORE starting source retirement.
7. Retire only corresponding verified source files. Recheck source and target
   identities; remove and sync the source trace first, then its captured ordinary
   sidecars/artifacts. Leave source code, configuration, dependencies, generated
   setup, skipped groups and verification records intact. No whole-directory
   move, rename migration, hardlinks, reflinks, approval copy or trace rewriting.
8. The target still needs its own unchanged full gate, proof audit, matching
   verification record, both independent review axes and immediate final check.
   A successful handoff is neither a Lean theorem nor a candidate acceptance.

## Failure, recovery and validation

9. Journal planned, copied, target-verified, retirement-started and retired
   progress durably. Preserve each failed attempt. A pre-verification failure
   leaves the complete donor and diagnostic target partial; a retirement failure
   leaves the complete verified target and identifies known retirement progress.
   Existing journals and partial target files cannot be silently skipped by a
   new attempt. Require explicit reconciliation, never automatic destructive
   repair or erasing evidence. Disk refusal retains completed prior handoffs.
10. Test meaningful disposable filesystem success/failure paths: source/target
    verifier rejection, partial copy, retirement failure, pre-existing target
    outputs, reserve refusal, source change, symlink refusal, missing/mismatched
    acceptance and separate review scopes, strict plan parsing, prior journal,
    and CLI refusal before any external runtime or real output change. Tests
    must not run a compiler, real stock hash subprocess or real migration.
11. Capture an immutable complete review scope with exact artifact hashes and
    repository guidance. Keep separate independent Standards and Spec outcomes
    and all findings across fixes. Validate the captured bytes with the fixture
    suite; no full Lean gate is needed for these outside-repository operational
    files. Verify delivered bytes still match before declaring helper readiness.
    Preserve everything in an immediately exposed recovery checkpoint.
