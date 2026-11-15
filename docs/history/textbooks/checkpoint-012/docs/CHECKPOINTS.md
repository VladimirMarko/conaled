# Checkpoint mechanics

[DURABILITY.md](DURABILITY.md) owns all blocking input/save/failure gates. This file
owns the mechanical procedure. Every coordinator/delegate, including during
cleanup, must checkpoint a substantial milestone before another extended phase.
`checkpoint.json` owns the current serial. Planning an archive name is not a
completed upload. Do not start a successor merely to polish an unsaved predecessor.

## Prepare and verify

Pause writers. Preserve committed mathematical source in the common Git store;
keep useful paper mathematics/uncompiled drafts at the appropriate book's `work/`.
Do not reset or discard dirty source. Record honest statuses in STATE; preserve
original requirements/review bases, failures and incomplete terminal outcomes.

```sh
python3 -B tools/checkpoint.py --root . verify --deep
python3 -B tools/checkpoint.py --root . pack --next --output ../conaled-textbooks-NEXT_SERIAL.tar.xz
```

Replace `NEXT_SERIAL` with the actual next zero-padded serial after the current
`checkpoint.json` value; it is a filename placeholder, not a literal command
argument. An ordinary resumed checkpoint already has a manifest and uses `--next`.
The current archive must have a confirmed delivery record or verified attached
input adopted before successor packing or source capture.

Only the one-time initial assembly of a new series, before a manifest exists, uses
`pack --output ../conaled-textbooks-001.tar.xz` without `--next`. That bootstrap
command is not the ordinary resume procedure.

The packer verifies its payload and source recovery. Its `completed:false` and
`durable_uploaded:false` are deliberate: local verification is not delivery.
Restore only to a fresh external destination when a separate rehearsal is needed.
The shared full source bundle makes this independent of earlier project archives.

After actual authorized source work, capture a clean candidate without losing
old refs:

```sh
python3 -B tools/checkpoint.py --root . capture-source --book fdsa --repo /absolute/worktree --candidate-ref refs/heads/work
```

Use the actual book/ref, not these placeholders. Capture rejects dirty inputs;
use the repository's ordinary workflow to preserve edits or save explicit drafts
in `work/`. Copying files does not make the original checkout clean. Preserve exact
diffs and all useful untracked/ignored mathematics with hashes; if needed, capture
committed refs from a separate clean mirror while leaving the original dirty tree
untouched. Do not force a commit, reset or deletion merely for capture. A capture
preserves source locally. Durable saving still requires a verified archive and an
observed successful owner-root upload. Capture also grants no review or
mathematical acceptance.

## Required upload route

Use `create_library_file` for the exact verified archive, with `directory_id`
omitted so the save is to the owner's root. Observe the successful tool result.
Do not substitute a sandbox link, Space page, old receipt, different directory,
publication service or an inferred save. Keep returned identity, bytes and SHA256
with the actual archive and supply the user an actual saved file link.

An absent/failing/uncertain capability triggers the immediate stop/report gate.
A single bounded capability check and one retry addressing a concrete failure are
permitted. Resolve an uncertain create before another create; do not duplicate a
known successful save because a local metadata step failed. Do not install or
troubleshoot upload infrastructure. Preserve exact local bytes while blocked.

After observing success, save the actual receipt to an external JSON record with
`method: create_library_file`, `destination: owner-root`, returned `library_file_id`,
`archive_sha256` and `archive_bytes`, then:

```sh
python3 -B tools/checkpoint.py --root . record-upload --archive /absolute/ACTUAL_ARCHIVE_PATH --receipt /absolute/ACTUAL_RECEIPT.json
```

Use the exact archive path returned by the successful pack command and the
actual observed receipt path in place of these placeholders. This is bookkeeping
of observed success, not a way to manufacture it. The receipt follows creation of
the immutable archive and need not be inside that same archive. For the next
substantive successor use the ordinary `pack --next` procedure above.

The delivery serial increases. Do not reset it or silently weaken an upload gate.
After a wipe, a currently attached verified durable archive is sufficient:

```sh
python3 -B tools/checkpoint.py --root . adopt-input --archive /absolute/reattached-checkpoint.tar.xz --library-file-id SERVER_PROVIDED_ID
```

Use the actual attachment identity. No old sidecar receipt is required. The tool
checks the archive against the current extracted manifest; it does not excuse a
missing/corrupt input or authorize selecting an older checkpoint silently.

## Prevent recurring bloat and drift

One shared Git store, one native kit, one current state per book, one payload
manifest. No nested new checkpoints, prior archive copies, partial downloads,
installed compilers, caches, repeated whole-repository snapshots, recursive capture
inventories or duplicate documentation. Frozen historical mathematical evidence
and exact alias maps are retained once; do not regenerate accumulating inventories.
The package policy explicitly lists the identity-bound inherited archive blobs inside
exact recorded upstream Git history and the pinned native-kit exceptions. They are immutable
exceptions, not a route for adding new recovery archives or runtime installations.

Do not alter checksums, archived evidence, source identities or policy guards to
force a pass. Correct an actual packaging error while preserving mathematical
bytes, document the reason, verify the correction and complete its durable save.
