# Checkpoint recovery assessment

Date: 2026-11-02. Reviewer: development-environment subagent.

## Follow-up verification of repaired script

The root coordinator supplied a repaired script with SHA-256
`617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab`.
Five isolated fixture scenarios against that exact revision passed their
expected outcomes. The reusable harness is `checkpoint-fixture.py`; run
`python3 checkpoint-fixture.py /absolute/path/to/checkpoint.py SCENARIO`, where
SCENARIO is one of the names below. Results are retained in
`checkpoint-fixture-evidence-r2.json`.

| Scenario | Observed result |
| --- | --- |
| `dirty` | Exact staged/unstaged text, binary, deletion, and untracked recovery succeeds. The restored ref inventory equals the original, including a custom review ref pointing to a commit outside branch history, a symbolic review ref, a remote-tracking ref, and an annotated tag. |
| `race` | The injected session update aborts capture with `Task record changed during capture: tracker/tickets.json`; no completed archive is created. |
| `selection` | A session `.lean` marker is retained, and an ignored repository log explicitly listed in `checkpoint-includes.json` is retained and verified after restore. Source and custom-ref checks also pass. |
| `credential` | A fake `auth.json` marker aborts capture before archive creation. No real credential is used. |
| `symlink` | A session file symlink aborts capture before archive creation. |

CP-01, CP-02 and CP-04's demonstrated failures are repaired for these cases.
CP-03's session credential-filename and symlink cases are repaired. The privacy
filter remains a bounded filename/location policy: it is not content-aware,
and nonignored repository files are still selected by Git rather than the
session credential denylist. Inspect the concrete archive file inventory and
keep credentials/downloaded manuscripts out of task source locations. This
assessment observed no actual credential exposure and identifies no such file
in the pending work.

The stable-writer capture discipline and explicit include registry remain part
of the recovery contract. These fixture results verify the repaired tool's
specified cases; they do not constitute the chapter's Standards/Spec review,
proof audit, or acceptance. The original findings and checkpoint 001 evidence
below are retained as the review history.

## Scope and disposition

This is a bounded read-only assessment within the root implementation workflow,
not a substitute for its independent Standards and Spec reviews. The live
repository, index, branch, and checkpoint script were not modified. Tests used
disposable directories under this conversation's workspace. No files were
uploaded and no other workspace or Library content was read.

Reviewed script: `session/checkpoint.py`, SHA-256
`98fc039e21b07ff42cf08ea4bfbf163d59884d3b2fa0fd996eb525cd318bd0dd`.
The requirements are the checkpoint recovery policy in
`session/requirements/REQUEST.md`. Subsequent script fixes require their own
verification; this assessment does not approve an uninspected revision.

Checkpoint 001 restores its stated clean baseline and local ticket records.
The script also restores representative dirty/index/untracked source states.
However, its original success result does not ensure that session records form
a consistent snapshot, and its selection rules silently omit some task files.
Those are concrete gaps against self-contained recovery of all progress.

## Evidence

### Existing checkpoint 001

Archive `conaled-pfds-checkpoint-001.tar.gz` has 71,851,746 bytes and SHA-256
`f4db5d8f707399e597e94279dd5068d4a688d092f691b70a6dbd0b581bb40525`, matching
`session/checkpoints.json`. All 18 manifest member checksums matched.

I extracted the existing archive into a new temporary directory and ran its
own `restore.py` into another new directory. It exited 0 and recovered:

- HEAD `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.
- Branch `pfds/local`.
- A clean worktree/index, as recorded in the manifest.
- Byte-identical `session/tracker/tickets.json`.

The checkpoint explicitly says no chapter is accepted and bootstrap is in
progress. It contains requirements, status, tickets, architectural notes, and
then-available environment logs. Its own upload receipt is naturally absent:
the receipt can only be recorded after creation/upload and is retained for the
next checkpoint. This is not a recovery defect.

Machine-readable evidence is in `checkpoint001-review-evidence.json` beside
this report. The archive remains the authoritative snapshot; this smoke check
does not establish that any formal development has passed its required gates.

### Disposable dirty-source and concurrency fixture

The harness copied the reviewed script unchanged into a temporary root with
its own `conaled` Git repository and `session` directory. The temporary repo
had a committed baseline on `pfds/local`, then:

- A tracked text file with distinct staged and unstaged changes.
- A staged binary change containing NUL/non-UTF-8 bytes.
- A deleted tracked file.
- New untracked text and binary files.
- A task-evidence marker `ignored-proof.log`, ignored by `*.log`.

The temporary session held status/tickets at epoch 0, a scratch Lean marker,
and an `auth.json` containing only the literal fake test marker
`FAKE_TEST_MARKER_NOT_A_SECRET`. The harness wrapped `shutil.copy2` in memory:
immediately after the script copied `STATUS.md`, it changed both live status
and tickets to epoch 1. The script source was not edited.

Capture and its built-in restore comparisons succeeded for all staged,
unstaged, deleted, binary, and untracked source states. Nevertheless, the
resulting archive contained **status epoch 0 and tickets epoch 1** and reported
`restore_test: passed`. The ignored log and session Lean file were absent;
the fake `auth.json` was present. The temporary repo/archive were then removed.
Exact observed outputs and the reviewed script hash are in
`checkpoint-fixture-evidence.json`.

## Findings and recommendations

### CP-01 — Inconsistent session snapshot can pass (high)

The session copy loop (reviewed lines 97–107) does not freeze or fingerprint its
inputs. Post-restore checks cover Git state and source files only. The fixture
demonstrates that a ticket transition and its status/review records can be
captured from different moments without failure.

Pause all task writers during capture. Record the complete selected path set
and content hashes before copying; require both copied/restored records and
the live path/hash inventory afterward to match that recorded snapshot. The
comparison must cover additions/deletions as well as changed bytes, and must
compare the actual captured bytes with the initial snapshot, not merely compare
two live scans. Record the capture policy and its trusted-writer limitation.
The root coordinator has proposed this repair; it was not yet verified here.

The same stable-writer discipline applies to source, index, and Git refs.
The final HEAD/status comparison alone cannot detect every same-status content
mutation or ref change. The source restoration checks are useful evidence but
do not replace a stable capture window.

### CP-02 — Needed ignored/session files can be silently lost (high)

`git ls-files --others --exclude-standard` omits ignored files. In this repo,
`*.log` and `*.bundle` are ignored as well as reproducible build outputs.
The session loop also silently drops unlisted extensions and files above
10 MiB. The fixture's ignored validation marker and session `.lean` marker
were both omitted. Current session inventory had no unexpected extension/size
omissions at the time of this review; the finding concerns a demonstrated
selection failure for legitimate future task artifacts, not a claim that
checkpoint 001 lost an actual proof.

Use an explicit task-owned include registry for needed ignored repo artifacts.
Treat all ordinary task-owned session files as candidates, with documented
explicit exclusions for reproducible caches, downloaded manuscripts, helpers,
and temporary process state. Record included and excluded names/reasons in the
manifest. Fail or obtain an explicit disposition for unexpected omissions;
do not silently infer that a large log or unfamiliar extension is expendable.
Keep candidate verification records and validation logs in the included session
tree. Any uncommitted work in additional worktrees or scratch directories must
be covered explicitly before checkpoint creation.

### CP-03 — Privacy exclusion is not enforced by type filtering (medium)

The comment promising credential/manuscript exclusion is stronger than the
selection rules. Nonignored repository files are copied wholesale; session
`.json`, `.txt`, `.log`, and `.sh` files are copied based on extension, and
file symlinks are followed by the session copy. The fixture proves inclusion
of a conventionally named `auth.json` containing fake data. No actual
credential exposure was observed or tested.

Reject symlinks or require explicit, safe ownership/routing treatment. Maintain
an explicit privacy exclusion policy for credential/config locations and
downloaded third-party sources, and inspect the concrete included-file inventory
before uploading. Extension filtering is not a credential detector. The root
coordinator's proposed symlink rejection addresses one part of this finding.

### CP-04 — One-command restore does not recreate all bundled refs (medium)

Checkpoint 001's bundle advertises 19 refs, while its restored checkout has
only four refs: the task head and three clone-created origin refs. Ordinary
`git clone` does not recreate the bundle's original remote-tracking/custom
namespaces. Thus the archive retains the omitted history through its complete
bundle, but the documented restored repository is not an exact ref recovery.
The restore comparison does not check this.

Record the full ref inventory and recreate/verify required refs explicitly
during restoration, without re-enabling remote pushes. Keep every review
candidate and other needed commit reachable through a retained ref before
bundling; reflog-only/dangling commits are not covered by `--all`. If exact
namespace recovery is intentionally out of scope, document the extra command
needed to recover those refs from the bundle and the distinction clearly.

## Useful existing protections

The script refuses an existing output filename, verifies the Git bundle,
stores binary patches separately for the index and worktree, hashes packed
members, restores into a fresh directory, uses tar's data extraction filter,
and disables pushes on the recovered origin. Final archive publication uses
a temporary file followed by rename, so a normal failed capture does not leave
an apparently finished numbered archive. These are useful protections and
should be retained through repairs.

The manifest hashes detect accidental member corruption; they do not certify
mathematical acceptance, authenticate an adversarially rewritten manifest, or
establish that concurrent source state was atomic. The existing scope language
correctly distinguishes a recovery checkpoint from a proof-completion record.
