# Cross-cutting recovery review

Reviewer: independent `reuse_survey` agent, 2026-11-02.
Scope: checkpoint001 and checkpoint generator; separate from chapter review.

## Current archive evidence

Checkpoint001 SHA256:
`e523a24cc822189e971d5dddff0de27d24ff67b344f8c1cca0e68af6b600275a`.
Reviewer verified all 39 manifest entries, cloned the bundle, checked out
142adf21f0dc3c5f26658d5f4a5854bd8fd8f2ec, extracted 1574 source files,
compared every regular file's bytes, observed clean Git status, and passed
`git fsck --full`. That actual checkpoint is recoverable.

## Findings and corrections

- REC-1: staged-only bytes could be absent from both history and working tree.
  Correction: raw `git diff --cached HEAD --binary --full-index` is captured as
  index.patch and restored with `git apply --cached`. Its hash, source state and
  final Git status are compared in a real restore. No whitespace stripping.
- REC-2: tracked unstaged deletion caused the original member-count assertion
  to fail. Correction: archive only existing entries, record deleted paths,
  apply deletions during restore, compare the reconstructed source inventory.
- REC-3: original built-in restore check only cloned the bundle and counted
  members. Correction: execute the exact shipped restore.py, restore index and
  working files, compare bytes/modes/symlinks/index patches/status and run fsck.
- REC-4: sequential capture could observe changing source/tracker state.
  Correction: compare source/index/HEAD and workflow fingerprints before and
  after capture; fail on a changed snapshot. Writers should remain paused.
  In-progress validation logs are explicitly allowed as prefix snapshots and
  cannot independently establish acceptance.

These corrections are implemented and independently rechecked below under
cross-cutting local ticket1000. REC-1 through REC-5 are resolved within the
documented ordinary-index and paused-writer scope; follow-up evidence is below.
Support for unmerged indexes or special index flags is not claimed. Unmerged
indexes produce an explicit error rather than silently losing conflict stages.

## Meaningful recovery regression

2026-11-02: created an independent temporary Git repository with committed
content A, uniquely staged content B, and working content restored to A;
an unstaged tracked deletion; an untracked file; a symbolic link; and an
executable file. Included a separate local-ticket JSON.

The corrected generator created its archive and its built-in restore passed.
A second independent extraction/restore then checked B through `git show :path`,
A through the working file, the absent deleted path, the untracked content,
symbolic link, executable mode, and ticket value. Every assertion passed.
Temporary fixture data was removed. This tests the actual loss scenario behind
REC-1/REC-2, rather than checking source-code syntax.

## Remaining source-recovery limitation

Exact original VFA bytes are not bundled because ADR0001 excludes research
copies from the deliverable. No immutable official URL was verified. The full
source identities and chapter hashes survive; a changed moving download must
be rejected or reviewed through a local source-version-migration ticket.
See ../source/SOURCE-RECOVERY.md. Existing Lean code needs no textbook download
to compile; continued new source coverage needs the matching reference bytes.

## Independent format-2 follow-up

Reviewer: `reuse_survey`, 2026-11-02. Reviewed generator SHA-256:
`28a58ef8fe0a1c30160dec17c548125c7691d058f746f3630f5bd1e5f1dd5f84`.
This includes the fresh `local/vfa-recovery-N` branch-name correction made after
checkpoint002. It is not a new inspection or acceptance of chapter code.

Independent temporary fixture results:

- Captured uniquely staged B with working A, an unstaged tracked deletion,
  untracked content, a relative symbolic link, an executable-mode change, and
  local-ticket JSON. The shipped restore recovered each exactly; `git show
  :index-file` retained B while the working file retained A.
- Recaptured that restored checkout and restored the second archive. Index,
  working files, deletion and local ticket survived the second generation.
- A separate repository whose only branch was already `local/vfa-recovery`
  exercised the actual branch-name collision. Restore selected
  `local/vfa-recovery-1` and passed its full source/index comparison.
- The generator's actual shipped-restore test, state comparison and fsck passed
  for those fixtures. Temporary fixtures were removed; no dependencies copied.

Disposition:

- REC-1 fixed: the raw full-index binary patch retains staged-only content, and
  reconstruction is checked against the exact captured index-patch hash.
- REC-2 fixed for ordinary file deletions: missing paths are explicitly removed
  and deletion survives independent restoration.
- REC-3 fixed: the exact delivered restore program is executed and its restored
  source/index/status is compared with the captured state, followed by fsck.
- REC-4 fixed within the stated stable-capture discipline: code, index, HEAD and
  non-log tracker fingerprints are compared across capture. This is not a claim
  of an atomic snapshot against transient concurrent edits; writers stay paused.
  Explicitly permitted active-log prefixes are not acceptance evidence.

### REC-5 — File/directory path transitions fail capture or restoration

Status: fixed with independent follow-up evidence below. Original tests found
two ordinary refactor states
outside the tool's effective support, although the documentation currently
excludes only unmerged indexes and special index flags:

1. Commit a regular file `entry`; replace it in the working tree with directory
   `entry/child`. `source_state` calls `file_state` on the old cached path and
   rejects the directory as `Unsupported non-file source entry`.
2. Commit `entry/child`; replace the directory with regular file `entry`.
   Capture reaches its shipped restore, which fails while overlaying the source
   archive onto the clone's still-existing directory. The recorded deletions
   are applied only after the overlay.

Both cases return an error before publishing a checkpoint, so they do not
silently corrupt a successful archive. Clean checkpoint002 is unaffected.
Resolve by restoring from an explicitly cleared/reconstructed working-source
tree and representing obsolete indexed paths correctly, or explicitly reject
and document such path transitions as an unsupported capture state. Do not
discard their edits merely to make the checkpoint pass.

### REC-5 correction verification

Reviewer: `reuse_survey`, 2026-11-02. Corrected generator SHA-256:
`deeb1cfc3255bff5d4f493d8906c821751006eadd0f1e88583f12f1ff0d4eece`.

Both original minimal reproductions now pass capture, the shipped restore smoke
test, and independent extraction/restoration:

- File to directory: committed/indexed `entry` retains its old bytes in Git's
  index while restored `entry/child` contains the new working bytes.
- Directory to file: committed/indexed `entry/child` retains its old bytes in
  Git's index while restored regular file `entry` contains the new working bytes.
- Both restorations exactly match the original porcelain status including
  tracked deletions and untracked additions.

Destination-clearing safety was inspected and exercised. `restore.py` rejects
an existing destination before cloning. The clearing loop is reached only
after its own successful clone, checkout and index restoration; it preserves
`.git`. It unlinks symbolic links rather than recursively following them and
recurses only into real directories within the new clone. Independently
rerunning restore against each existing restored checkout returned the explicit
refusal and left an added sentinel file's bytes unchanged.

Directory entries at obsolete tracked paths are now represented and archived.
Git submodules are explicitly rejected rather than silently capturing only
their directory entry. The correction does not claim preservation of unmerged
indexes, special index flags, or externally changing state. Fixtures were
temporary and were removed; no project sources or dependencies were copied.

REC-5 is resolved. No remaining error was found within this correction's scope.

## Checkpoint006 recovery handoff review

Reviewer: `environment`, 2026-11-02. The reviewer streamed the actual
checkpoint006 archive read-only and compared selected recovery, metadata,
tracker, source-recovery, review, and validation-log members with their manifest
hashes. All inspected members matched. This bounded check supplements the
generator's complete shipped-restore/hash/fsck smoke check; it does not claim a
second full reconstruction or chapter validation.

The captured state consistently identifies candidate
`cba657b43ed57e15962858713b819058e7d3c3ca`, a clean main source tree, and no
accepted chapter. The old validation log ends in KeyboardInterrupt and the
restart record identifies exit 130. The corrected-candidate log is a progress
prefix, without a final PASS or acceptance record. The source recovery URL and
exact archive hash, pending gates, and chapter dependencies are coherent.

Two small wording corrections were proposed and applied by root:

- The round-2 review now explicitly describes its round-1 build observation as
  historical and points to the later restart record.
- STATUS now distinguishes the recorded validation attempt from a surviving
  process. After workspace loss, a fresh pinned isolated build is required;
  neither the running process nor build caches are restored by the archive.
  Its next steps name evidence closure of the already completed source
  reviews, the regression, final verification, sequential Preface/Perm
  acceptance, uploaded checkpoint, and then Sort.

These are handoff clarifications, not code or validation changes. The embedded
checkpoint ledger ending at 005 in archive006 is expected: capture preceded
006's successful upload. Archive metadata identifies the captured archive, and
the live ledger records its upload receipt for subsequent checkpoints.
