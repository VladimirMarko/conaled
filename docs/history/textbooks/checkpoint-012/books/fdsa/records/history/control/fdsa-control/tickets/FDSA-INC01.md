# FDSA-INC01 — Chapter 1 validation disk exhaustion

State: evidence preserved and initial space recovered; repaired-candidate validation pending.
Parent: FDSA-001. Local tracker only; no GitHub comment or remote write.

## Event

Old candidate: `1aabd512284fe86254278ac631eda061d311050b`.
Command: pinned Nix shell, `env LEAN_NUM_THREADS=1 ./check.sh --candidate HEAD`.
Parent session 80227 exited 120, observed 2026-11-02 15:44:10 UTC.
The filesystem was full; the log has explicit ENOSPC and failed `.olean` writes,
then truncation. No verification record, successful full build or audit exists.

## Preserved evidence

`provenance/chapter01-enospc-20261102/manifest.json` records the clean old
candidate, task-local quiescence, truncated-log hash, configuration and all
surviving files from 19 reported failed-module families. Forty-six files and
the log were copied before any guard/manual artifact invalidation. Missing
evidence is not reconstructed and the log cannot exclude lost errors.
The current public issue 272 record is saved alongside this evidence.

The known GraphEmission occurrence is not matched by the observed ENOSPC
diagnostics or established artifact identities. This is an explicit resource
failure, not a claimed second Lake reuse defect. The user was informed of
the actual failure in the active conversation.

## Recovery and remaining gate

- Verified SHA-256 identities against durable receipts, then reclaimed local
  archive duplicates 0001–0038 while retaining 0039 and all checksums/receipts.
  A later observation found 0001 present again; its origin is unestablished
  and it was not repeatedly deleted.
- Removed only the exact stopped fresh-check output directories and completed
  baseline recovery fixture, after confirming the restored checkout was clean
  at the original base and all original extracted payload hashes matched.
- Retained normal Lake outputs, dependency sources/artifacts, all development
  source/history, toolchains and control records. Exact cleanup identities are
  in `provenance/storage-recovery-*-20261102.json`.
- Retained Standards permits direct guarded incremental validation of repaired
  `a14977b9e316cc484ffad8a470d26b15615956c0` after sufficient space and stable
  isolation; see `reviews/chapter01-enospc-recovery-standards.md`.

Close only after the new guarded run establishes its own matching successful
build/integrity/audit evidence. This does not retroactively pass the old run,
accept the chapter or close SPEC-001/002/003/V001. Any new unexplained integrity
failure or suspected stale output retains the existing runbook obligations.


### Guarded repair pre-build observation

The repaired candidate's pre-build pass reported 547 rebuilds, all for missing
files. None overlaps the 398 modules reported Built/Replayed in the surviving
old log; that old log is truncated and supplies no complete historical proof.
No nonmissing-file reason or output mismatch was reported by this pass. Exact
diagnostics and the bounded comparison are saved in
`../provenance/chapter01-repair-prebuild-recovery.json`. This is consistent with
the recorded incomplete build and does not establish a new unexplained reuse
incident. Full build, post-build integrity and audit still must finish; INC01
remains open and no cache-soundness or acceptance conclusion is inferred.

### Continued duplicate-archive space recovery

After successful checkpoints 0043 and 0044, four older local archive copies
0039–0042 were matched to their retained successful receipts, byte sizes and
ordinary SHA-256 identities, then removed as local duplicates. Their durable
copies and every receipt/checksum remain. Latest local 0043/0044 are retained.
The exact event and its 294,313,245 apparent bytes are recorded in
`../provenance/storage-recovery-checkpoint-duplicates-20261102-round2.json`.
No build artifact, dependency, source/history/control record, reappeared0001
or unrelated main-worktree artifact was removed. This continues the established
capacity-recovery procedure; it supplies no gate success or incident closure.

## Recovery established — 3 November 2026

A separately recorded native fresh attempt 4 on exact clean 07e480f completed
with actual exit 0, full build and exhaustive audit. Both independent final
review axes passed; immediate verification passed before local integration.
The recovery blocker is resolved by this new matching success. No failed or
unknown historical outcome is relabelled and no cache defect is inferred.
See provenance/chapter01-unified-fresh-attempt4/ and
provenance/chapter01-acceptance-20261103/ for the current evidence.
