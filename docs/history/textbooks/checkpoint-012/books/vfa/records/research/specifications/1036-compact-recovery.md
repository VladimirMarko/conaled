# Local #1036: compact latest-state recovery and supplied native kit

## User steering and scope

The user supplied checkpoint 042 and the unified native Lean 4.35.0 kit and said:

> Keep creating durability checkpoints and uploading them to space / library. You have my file permission to do so. Durability checkpoints exist for recovery just like the one we are currently exercising. Their purpose is not to allow us to reconstruct previous project states. And they should be kept small if possible, to allow frequent uploads. Integrate the updated environment setup into the next one.

For compact recovery this supersedes the earlier interpreted requirement to
repeat complete source/history in every standalone archive. The recovery unit
is exactly **one fixed immutable base companion plus one latest cumulative
checkpoint**. No previous rolling checkpoint is needed. Current mathematical
claims, review evidence, local tickets, exact source/index state and setup
instructions must remain recoverable. This changes no formal acceptance gate,
chapter order, exact compiler/dependency pin, or prohibition on GitHub writes.

The original `tools/checkpoint.py` remains unchanged. The separate
`tools/checkpoint_compact.py` implements this two-artifact format. Root owns
coordinated independent Standards/Spec review in the existing operational loop;
tool implementation or a successful restore does not itself approve the tool
or a formal chapter.

## Fixed base and cumulative snapshots

The supplied 042 `conaled-history.bundle` is an appropriate immutable base
payload. It already includes the exact fixed formal review base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` and current candidate history. Package
that bundle once with its manifest and base identity, verify it, then upload it.
Record its real filename, SHA-256, size and Library ID in each current checkpoint.

Each current checkpoint contains a cumulative Git bundle of all current reachable
work after the fixed review base, not a delta against an earlier checkpoint. It
also contains an exact dirty-source overlay, index patch, diagnostic working
patch, all saved work-state, the complete supplied native kit, checksums, and its
own restore entrypoint. Operational repositories under work-state retain their
accepted candidate identities and evidence. The large unchanged upstream source
archive is retained once in the base, not deleted from the source candidate.

Current checkpoint metadata records current refs, symbolic or detached HEAD,
source byte hashes, executable modes, symlink targets, ordinary index contents,
Git status, and the immutable base binding. The restore must reproduce them
exactly in a previously absent destination. Unmerged indexes, submodule work
trees, special index flags and unsupported filesystem entries are rejected.
Failed smoke checks leave no published checkpoint. No existing checkout is
overwritten; an interrupted explicit restore can leave its new partial destination
for inspection.

Build caches, compiler/dependency installations, earlier output checkpoints,
Python bytecode, credentials and downloaded textbook bodies are not recovery
payloads. Known cache directories and Python bytecode are excluded from the
work-state/kit copy. Credential-like path components stop capture for investigation
in every selected tracked or untracked source path, before its file-state read,
and in the work-state/kit trees. Required work-state/kit roots must be directories;
root symlinks and enumeration errors abort capture instead of omitting evidence.
The operator remains responsible for keeping credentials out of task state and logs.
Historical setup JSON, proof fixtures and reviewed evidence are retained.

## Active validation and capture discipline

Pause source, tracker, requirement, review and tool writers during capture.
Declare each live recorder directory with repeatable `--active-attempt
validation/<attempt>`. The current attempt is
`validation/1002-candidate-c988f18-unified-fresh1`.

Only these explicit validation directories are excluded from workflow stability
comparison. Their files are copied at the opened file's observed size; append-only
logs are bounded prefixes. JSON records and logs need not represent one coordinated
instant. The checkpoint marks all such observations as incomplete operational
state, never as terminal success or acceptance. Saved PIDs/handles are historical
after restore. Files outside those directories, Git state and the kit must stay
unchanged through capture and its restore smoke.

## Commands

Run from the restored recovery root, substituting the actual output filenames and
actual returned base Library ID. These paths are examples, not upload receipts.

```sh
python3 -B work-state/tools/checkpoint_compact.py create-base \
  --bundle conaled-history.bundle \
  --base-commit 7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd \
  --output checkpoints/conaled-vfa-immutable-base.tar.gz

python3 -B work-state/tools/checkpoint_compact.py capture \
  --workspace . --kit ../conaled-native-kit-4.35.0 \
  --base checkpoints/conaled-vfa-immutable-base.tar.gz \
  --base-library-id ACTUAL_RETURNED_LIBRARY_ID \
  --active-attempt validation/1002-candidate-c988f18-unified-fresh1 \
  --output checkpoints/conaled-vfa-checkpoint-043-compact-recovery.tar.gz
```

The base must be uploaded and its actual identity retained before the dependent
current checkpoint is delivered. Upload each successfully created artifact
immediately; do not wait for the next formal result. Future captures use the same
base and the then-current active attempt flags, if any. Do not invent Library IDs
or mark uploads successful before the actual tool result.

For recovery, extract the current checkpoint and run:

```sh
python3 -B checkpoint/restore.py restore \
  --base /path/to/conaled-vfa-immutable-base.tar.gz \
  --checkpoint /path/to/latest-checkpoint.tar.gz \
  --destination /path/to/new-absent-recovery-directory
```

Read the restored `work-state/STATUS.md`, `AMENDMENTS.md`, tickets, reviews and
`tooling/UNIFIED-NATIVE.md`. The intact kit is restored at `native-kit/`.
No previous runtime/build state or successful `.lake/verification.json` is
installed by recovery. Source evidence is kept with its recorded limitations.

## Validation and completion criteria

Each archive has an exact manifest; unsafe paths, duplicate members, links and
special archive entries are rejected. The latest snapshot binds the whole base
archive by SHA-256 and size. Capture must restore from the actual produced
archives, compare source/index/status and refs, run `git fsck --full`, compare
copied workflow/kit bytes, run the kit's own `verify`, and recheck live input
stability before publishing the output filename.

Focused regression tests cover cumulative recovery with the previous checkpoint
absent, dirty staged versus unstaged binary content, deletions, executable modes,
file/directory/link transitions, ignored caches, refusal to overwrite, corruption,
wrong base, unsafe archive paths, concurrent stable-state edits and explicitly
declared active-log prefixes. Review regressions also require capture to publish
no archive for credential filenames or ancestors in tracked/untracked source,
a missing or symlink work-state root, a symlink kit root, or an injected subtree
enumeration error. Run:

```sh
python3 -B work-state/tools/test_checkpoint_compact.py
```

Both independent operational review axes and root's comparison against the
approved snapshot remain required before relying on this new tool. Review
records and exact validation outcomes belong to root's operational record.
