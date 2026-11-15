# Concrete recovery pair: source023 and optional cache001

Whole-book formalization remains in progress. No chapter is accepted. The
current clean source candidate is
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`.

## Saved artifacts

| Artifact | Exact bytes | SHA-256 | Persistent file |
| --- | ---: | --- | --- |
| Complete source/history/tracking checkpoint023 | 145936501 | `92dc6cc6a95847c3cafd21087ca8c2fa8f6d515a28d9eb8db28680a6a5d3ed17` | [conaled-vfa-checkpoint-023-reviewed-cache-recovery.tar.gz](https://chatgpt.com/library?file_id=libfile_34c277ab17e08191a7e09db07802c467&account_id=personal) |
| Optional cache companion001 | 81938603 | `d368761921b3919844fd3c964ded7fd42e2f5ff25ec5f13d24707d8fbd01dc1c` | [conaled-vfa-cache-001-candidate-3279bac.tar.gz](https://chatgpt.com/library?file_id=libfile_92fa73b259e4819190db24b064241592&account_id=personal) |

Checkpoint023 is complete without this optional cache. Companion001 contains
504 checked module families, 249142110 payload bytes, and no verification
success record. The capture omitted 449 families; those numbers are neither
build completion percentages nor evidence of chapter acceptance. Its raw
traces and source/environment checks permit ordinary consistent older outputs;
they do not prove every output was freshly compiled from the candidate.

Checkpoint024 is intended to preserve this guide, the companion's exact
creation/upload evidence, source binding and current local tickets. A later
complete source checkpoint may contain newer source or workflow state; inspect
its STATUS and evidence before using the older cache. This guide does not
claim checkpoint024 is uploaded until its actual receipt exists.

Companion001 remains bound to checkpoint023. Checkpoint024 preserves its
receipt and the latest tracker state; never rewrite the cache binding to
checkpoint024. Recover the named checkpoint023 source and exact candidate for
cache installation, retaining the latest complete checkpoint's work-state
records as the authoritative task history.

## Resume steps

1. Obtain and hash-check the complete source checkpoint and follow its root
   RESTORE.md / restore.py instructions in a fresh destination. Read restored
   work-state/STATUS.md, REQUIREMENTS.md, AMENDMENTS.md, tickets.json and the
   source AGENTS.md. Source progress and local ticket history do not depend on
   obtaining the optional cache.
2. Recreate the pinned environment and dependency checkouts as documented in
   work-state/environment.md. For this companion, use a separate clean, idle
   isolated checkout at the exact commit above. Its writable build directory
   must be absent or empty. Do not share writable outputs or hardlink them
   between checkouts.
3. Verify the companion's full digest and exact bytes above. Use the saved
   validation/cache-companion001-source-binding.json with the accepted utility
   in work-state/cache-companion. Follow that utility's README recovery command,
   substituting this archive name, this exact digest and this binding filename.
   `verify` checks without installation. `restore --idle-checkout` verifies and
   installs only into the compatible idle destination. The flag is an explicit
   idleness assertion, not automatic process detection.
4. If starting from checkpoint023 alone, it predates the first capture. Rebuild
   the binding JSON from the exact source023 identity above: filename, sha256,
   size_bytes, library_file_id and source_commit. Companion001 repeats that
   binding in its manifest. Checkpoint024 and later records can supply the
   saved JSON and returned upload receipt directly.
5. Run the unchanged full candidate check, managed +ProofAudit prerequisite,
   proof-audit regression, both independent review axes and final
   --verify-candidate step, in the exact order documented in STATUS.md and the
   utility README. Resume Preface/Perm acceptance only after all actual gates
   pass. Then continue with Sort and the remaining book in chapter order.

The original captured checkout path was
`/workspace/scratch/0c54f2db1fdf/vfa-validation`. Raw trace captions retain
absolute paths, so changed-root reuse is not guaranteed; Lake may rebuild
normally. If exact identities or a compatible environment cannot be recovered,
skip the optional cache and rebuild from the complete source checkpoint.
Never install it into the currently running validation checkout.
