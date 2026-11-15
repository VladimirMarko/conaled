# Checkpoint tool interface

`docs/DURABILITY.md`, the root `AGENTS.md`, and the current guides own the workflow.
This file documents the metadata tool interface. It does not authorize Lean
execution, change mathematical acceptance, or provide another setup route.
The tool needs Python 3.9+ and Git. Invoke Python with `-B` to avoid bytecode
cache files in the payload.

## Commands

```sh
python3 -B tools/checkpoint.py --root . verify --deep
python3 -B tools/checkpoint.py --root . restore-source --to /new/outside/directory
python3 -B tools/checkpoint.py --root . restore-source --to /new/outside/directory --all-saved-worktrees
python3 -B tools/checkpoint.py --root . pack --output ../conaled-textbooks-001.tar.xz
python3 -B tools/checkpoint.py --root . pack --next --output ../conaled-textbooks-002.tar.xz
python3 -B tools/checkpoint.py --root . capture-source --book pfds --repo /outside/worktree --candidate-ref refs/heads/work
```

`verify` checks every payload path, byte hash, size, mode and protection.
`--deep` additionally reconstructs the complete Git object store offline,
verifies every advertised/required ref and commit, runs Git integrity checks,
and inspects source-history objects for prohibited archives/artifacts.

`restore-source` always performs the deep source checks before creating its
destination. The result has `repository.git`, three detached candidate
worktrees under `worktrees/`, and optionally the recorded historical worktrees.
It never runs a compiler, build, project script, Git hook or checkout filter.

`pack` creates the initial serial only when there is no previous manifest.
`pack --next` reads the current release manifest in place, requires unchanged
checkpoint metadata and recorded delivery of that release, and derives the
next serial and parent manifest hash. The output must be outside the payload,
must have the exact serial filename, and must not exist. Packaging verifies a
fresh extraction and source restoration before publication. Only the current
manifest is included. The reported local result has `completed: false` until
the required actual upload is recorded.

### One-time pinned-source and setup amendment

The user-directed 001 → 002 amendment brings in the complete newly pinned master
and corrects setup guidance to permit the verified native route while retaining
the pinned inputs. It uses an explicit, narrowly checked form:

```sh
python3 -B tools/checkpoint.py --root . pack --next --contract-update-from /outside/actual-conaled-textbooks-001.tar.xz --output ../conaled-textbooks-002.tar.xz
```

This is not the ordinary successor command. The supplied previous archive must
match the recorded durable/adopted input and the retained previous manifest.
The tool freshly verifies that previous archive, preserves every prior source
ref, required commit, mathematical/evidence payload, native-kit byte and frozen
reference tree, and permits only named operational files to change. Historical
book STATE fields remain identical; only a new top-level `integration` pointer
may be added. The durability policy and `docs/DURABILITY.md` cannot change.

`policy.source_import_amendment` binds the previous archive/manifest hashes,
from/to serials 1/2, exact master commit, exact source-bundle hash/byte count,
added inherited archive blob identities, and a preserved rationale document.
Each added archive blob must occur in that exact master's reachable Git history.
This retains immutable upstream history; it does not allow arbitrary new archives.
Only the precisely identified bundle's increase is exempt from the usual growth
calculation. Other growth still obeys the unchanged ratio/byte limits. The archive
cap can rise only as far as 128 MiB; all other source/payload limits remain fixed.

The amendment never waives integrity, self-contained recovery, observed durable
upload, or mathematical validation. Later generations use ordinary `pack --next`;
the one-time option refuses any starting serial other than 001. Its retained
policy record cannot grant another exceptional growth allowance.

`capture-source` preserves all previous source refs and objects, adds new refs
under an append-only capture namespace, and updates the selected book's
candidate role. It never promotes mathematical acceptance or changes the main
role. It refuses dirty tracked files, untracked files, and all ignored files
outside the named dependency/build locations, including other registered worktrees.
Preserve that work explicitly under `books/BOOK/work/` or finish the normal
repository workflow before retrying. Do not reset or delete it to clear the
guard. Capture does not package or upload the resulting checkpoint.

## Delivery bookkeeping

The tool does not upload files or authenticate a remote API response. Use the
live `create_library_file` capability to the owner's root, omitting
`directory_id`, and retain the actual successful response. A small receipt
wrapper must bind that real response to the released archive:

```json
{
  "method": "create_library_file",
  "destination": "owner-root",
  "library_file_id": "THE_SERVER_RETURNED_LIBFILE_ID",
  "archive_sha256": "SHA256_OF_THE_EXACT_UPLOADED_ARCHIVE",
  "archive_bytes": 0
}
```

Replace all illustrative values with observed values; never fabricate a
receipt. Then record it:

```sh
python3 -B tools/checkpoint.py --root . record-upload --archive ../conaled-textbooks-001.tar.xz --receipt /outside/actual-receipt.json
```

The bookkeeping record is one small `.conaled-textbooks.delivery.json` beside
the payload. It is deliberately outside the immutable release. A loss of that
local receipt does not make a saved checkpoint dependent on another archive:
after a wipe, obtain the user's latest saved archive and its server-provided
Library file ID, restore/verify that exact input, and adopt it:

```sh
python3 -B tools/checkpoint.py --root . adopt-input --archive /supplied/conaled-textbooks-001.tar.xz --library-file-id libfile_SERVER_RETURNED_ID
```

Adoption verifies the supplied archive's exact current manifest and its source
integrity. It neither asks for another human confirmation nor invents upload
history. An unavailable or uncertain upload remains the blocking condition
defined by the root durability contract.

## Metadata contract

`checkpoint.json` has schema 1, `series`, positive integer `serial`,
`policy_sha256`, and `parent_manifest_sha256` (null for the first release).
`MANIFEST.json` has schema 1, the same series/serial, and `files` mapping each
relative POSIX file path to `{bytes, sha256, mode}`. Mode is a four-character
octal string, normally `0644` or `0755`. The manifest excludes itself.

`policy.json` binds `protected_files` by SHA-256, `initial_refs` by Git object
ID, `required_commits`, the fixed `native_kit` file map, the enumerated inherited
archive blobs by Git ID/size/SHA-256, and payload/archive/growth limits.
`frozen_trees` maps an immutable tree root to the SHA-256 of its file metadata
dictionary, keyed relative to that tree root and encoded with
`json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)`
as UTF-8, with no trailing newline. This protects additions as well as
changes/removals without duplicating entire imported inventories in policy.

The source catalog is `source/refs.json` schema 1: `base_commit`,
`external_archive_dependencies: []`, `baseline_refs`, and three `books`.
Each book has `refs` entries with `original_ref`, `stored_ref`, `object`, and
`roles.main` / `roles.candidate` pointing to stored refs. Historical symbolic
targets can remain metadata; stored refs are direct namespaced refs. Capture
adds `capture_count`. `source/saved-worktrees.json` holds a `worktrees` array
with book, name, commit and optional historical metadata.

The default Git object bounds are 128 MiB per expanded object and 2 GiB total;
policy may provide `max_git_object_bytes` and `max_git_expanded_bytes` under
`limits`. Growth permits the greater of the configured ratio allowance and
absolute byte allowance. No allowance permits nested/new archive artifacts.

The one-time `source_import_amendment` object has exactly these fields:
`schema: 1`, `from_serial: 1`, `to_serial: 2`, `previous_manifest_sha256`,
`previous_archive_sha256`, `master_commit`, `source_bundle: {bytes, sha256}`,
`added_archive_blobs: {GIT_BLOB_ID: {bytes, sha256}}`, and `rationale_path`.
It records the already authorized pinned upstream import; adding it alone does
not relax the ordinary pack command.

## Metadata regression tests

```sh
python3 -B tools/test_checkpoint.py
```

The portable suite uses disposable Git repositories and inert source fixtures.
It executes no Lean or project code. Its temporary runtime is
`.checkpoint-tests/` beside the checkpoint root, outside the payload, and each
test removes its own fixture directory. Do not include that runtime or test
logs in a checkpoint. The suite verifies packaging/recovery guards; it supplies
no mathematical acceptance or remote-delivery evidence.

## Interrupted operations

A POSIX advisory lock serializes tool operations. Publication uses a small
transaction directory beside the payload. The next locked invocation checks
its identities and either completes an already published verified release or
rolls back an unpublished metadata/source update. Unexpected concurrent bytes
are preserved and cause a refusal. Do not put that transaction directory,
lock, local receipt, runtime or previous archive into the checkpoint.

An integrity result concerns source recovery and packaging only. A completed
delivery record concerns observed file saving only. Neither is a mathematical
acceptance decision.
