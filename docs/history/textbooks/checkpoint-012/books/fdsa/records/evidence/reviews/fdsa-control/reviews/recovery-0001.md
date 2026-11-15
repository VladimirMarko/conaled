# Durability checkpoint 0001 recovery review

Date: 2026-11-02. Reviewer: independent architecture/recovery agent.

Archive: `checkpoints/conaled-fdsa-0001-baseline.tar.gz`.
Saved Library identity supplied by the coordinator:
`libfile_2d4f0d5afa34819192f73ea4a2e07c79`.

## Outcome

The checkpoint successfully restores the intended baseline source checkout and
local task state without GitHub access. Its bundle is self-contained and passes
Git integrity checks. One recoverability issue remains for preservation of all
Git ref names across restore followed by a later checkpoint; see RECOVERY-001.
This issue does not prevent recovery of the current active work branch.

No Lean compilation, proof audit, or mathematical acceptance is claimed by this
recovery test. Original source files and the archive were not modified or deleted.

## Executed verification

The archive was extracted to a fresh directory:

`fdsa-recovery-0001/extracted/conaled-fdsa-0001-baseline/`.

From there:

1. `sha256sum -c SHA256SUMS` passed for all 14 payload entries.
2. `python3 fdsa-control/restore.py /workspace/scratch/845aa1048b05/fdsa-recovery-0001/restored`
   exited successfully under Python 3.12.14. The target did not exist beforehand.
3. The restored repository has `HEAD` exactly
   `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` and branch `work/fdsa-book`.
4. Restored `git status --short` is empty, as expected: the sole original
   unrelated untracked file is deliberately omitted and the baseline has no
   task source edits.
5. Both fetch and push origin URLs are the recorded public conaled repository.
   No network operation was performed by restoration.
6. `git bundle verify <included conaled.bundle>` passed and explicitly reported
   complete history, 19 advertised entries (18 named refs plus HEAD), SHA-1 object
   format, and no prerequisite commits.
7. `git fsck --full` in the restored checkout passed with no output.
8. Restored `REQUEST.md`, `STATUS.md`, ticket index and FDSA-001 ticket are present.
   All eight control files are byte-identical to the extracted checkpoint copies.

The checkpoint explicitly records that zero chapters are accepted and that
environment setup, source inventory and Chapter 1 development remain active.
This status survives recovery. The PDF is intentionally absent; its source URL,
version date and SHA-256 are present in `STATUS.md`.

## Finding RECOVERY-001 — Original named refs are not fully restored

Status: correction approach tested successfully in the disposable restored
checkout; the coordinator will carry the corrected restore script in a future
checkpoint. The original archive and script remain unchanged.

The included bundle advertises 18 named refs. After plain
`git clone --branch work/fdsa-book`, the restored repository has only:

- `refs/heads/work/fdsa-book`
- `refs/remotes/origin/HEAD`
- `refs/remotes/origin/master`
- `refs/remotes/origin/work/fdsa-book`

Of the 18 original named refs, 15 are absent. These include `refs/heads/master`
and remote-tracking integration, reconstruction and research branches. For
example, the original bundle has
`refs/remotes/origin/reconstruction/adwh-154` at
`c12296f63c656737d07325e9d8e8e16d6976d099`; the restored ref does not exist.

The original archive still contains every ref and the full object graph, so
current work is recoverable. However, `checkpoint.py` subsequently bundles
`--all` from the restored repository. Tips existing only under lost ref names can
then be omitted from the next supposedly self-contained checkpoint and eventually
be pruned. This falls short of preserving complete Git history and refs through
repeated recovery cycles.

Recommended correction: after cloning, restore all advertised `refs/*` from the
bundle to the same original ref names, then verify each ref and object ID. Preserve
the requested active branch and restored origin URL. Test a restore followed by
a new bundle and compare the retained ref/commit set with the original bundle.
An equivalent mirror/import strategy is acceptable if its checkout result and
full ref preservation are verified.

### Correction test

The coordinator proposed enumerating `git bundle list-heads` and applying
`git update-ref <ref> <sha>` for each advertised `refs/*` entry. This was tested
in the disposable restored checkout. Every one of the 18 original named refs
then had exactly its original object ID; HEAD and active branch were unchanged.
The clone retained one additional generated ref,
`refs/remotes/origin/work/fdsa-book`. That extra does not lose source history.

For exact set equality and robustness to existing symbolic refs, the test then:

1. Updated each original named ref with `git update-ref --no-deref`.
2. Deleted only clone-created refs absent from the original bundle, also using
   `--no-deref`.
3. Compared all 18 restored ref names and object IDs with the original bundle;
   equality passed.
4. Created a new `--all` bundle from the corrected restored checkout; its full
   named-ref map exactly equalled the original bundle's map.
5. Verified the new bundle, which again reported complete self-contained history.

The source archive's complete history remains recoverable throughout. The
limitation is the original convenience restore script's incomplete recreation
of named refs, not missing contents in checkpoint 0001. Bundle files record
advertised target IDs rather than symbolic-ref metadata; the recommended
normalization preserves all recorded names and targets.

## Scope limits

The baseline contains empty staged and unstaged patches and no task-related
untracked files. This test verifies recovery for that actual checkpoint; it does
not test future recovery of nonempty index/working-tree patches or new source
files. Such a round trip should accompany the first checkpoint containing them.
`STATUS.md` points ahead to a `provenance/` directory that is not yet present, but
its immediate source URL/version/hash are recorded directly, so that omission is
not a blocker to this baseline recovery.
