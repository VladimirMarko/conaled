# Bootstrap Spec review — local ticket #10000

Date: 2026-11-02. Independent reviewer: `/root/source_gate_check`.

**Outcome: Passed. Findings: 0 unresolved; worst severity: none.**

This outcome covers the pinned-environment and durable-recovery bootstrap only.
It does not accept #10013, any book chapter, a Lean candidate, or the whole-book
request. Those gates retain their separate requirements and evidence.

## Scope and identity

Requirements are the original user request in `requirements/REQUEST.md`
(SHA-256 `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499`)
and local #10000's three acceptance statements in `tracker/tickets.json`:

1. The required Nix development shell runs pinned Lean/Lake.
2. Requirements, tickets and full repository history restore from a
   self-contained checkpoint.
3. The checkpoint is uploaded and its exact saved identity exposed.

The concrete recovery implementation reviewed is `session/checkpoint.py`,
SHA-256 `617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab`.
This is identical to the script embedded in checkpoint003 and the revision
exercised by all five repaired recovery fixtures. The reviewed checkpoint is:

- Filename: `conaled-pfds-checkpoint-003.tar.gz`.
- SHA-256: `37a8dc11bdb3899f1dbbc7c411f4c011c31d45e06eb941567022e603f45bc107`.
- Size: 71,921,373 bytes.
- Repository HEAD: `ad730010ab1929bbd7a16a035c7990a6f328b178`.
- Branch: `pfds/local`; captured index/worktree status: clean.
- Manifest creation time: `2026-11-02T03:03:52.851401+00:00`.

The bootstrap tools and task records live outside the repository source diff.
The script and archive hashes identify this review's actual artifact scope;
the repository HEAD above identifies restored source, not a formal-development
approval or a substitute Git review candidate.

## Requirement assessment

### BOOT-SPEC-A — Required pinned environment: satisfied

I read the repository's environment/build guidance, actual `lean-toolchain` and
`flake.nix`, then checked the retained environment evidence. The documented
noninteractive route is `nix develop --command ...`. Bootstrap uses the real
installed Nix binary with container-specific build-user/sandbox options; it
does not replace the flake or alter its pins. The installer profile-activation
failure is disclosed rather than reported as a successful complete install.

The retained `environment/lean-version.log` records the actual pinned Lean
4.35.0 smoke-check output, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The environment summary records
Lake 5.0.0-src+eb6cafb, Nix 2.35.4, successful cache retrieval, and nine clean
dependency checkouts matching the manifest. `environment/README.md` preserves
the exact usable invocation and recovery instructions. It explicitly separates
environment bootstrap from a successful full build/proof audit.

### BOOT-SPEC-B — Recoverable work and local tracking: satisfied

I read the complete checkpoint and restore implementation and fixture harness,
not only their status summaries. Capture creates a no-prerequisite Git bundle,
records all refs, stores binary staged and unstaged patches separately, and
archives relevant untracked files. Restore recreates direct and symbolic refs,
removes clone-created extras, checks HEAD, reapplies the index/worktree patches,
restores untracked files and session records, and disables origin pushes.

Creation performs a real fresh clone/restoration before publishing the archive.
Its comparisons cover Git status, exact binary diffs, source bytes/deletions,
explicit ignored artifacts, session snapshot consistency, full ref identity and
unchanged live HEAD/status. The repaired fixture harness supplies meaningful
distinct states: staged versus unstaged text, binary content, deletion,
untracked files, an off-branch review commit, symbolic refs and an annotated
tag. Retained results confirm recovery of those states. The race fixture
rejects a mixed status/ticket snapshot; selection, credential-name and symlink
fixtures exercise the specific repaired failure modes. The tested script hash
matches the currently reviewed implementation. I did not rerun those successful
fixtures without a new unresolved defect.

I independently inspected checkpoint003's actual member inventory, manifest,
README and selected required records. It contains 37 session records, including
the full request, tickets, source/review records, environment evidence and
then-available validation logs, alongside the bundle, both patches, untracked
archive and recovery program. The Git bundle header contains no prerequisite
exclusions. The reviewed required member checksums match the manifest, and the
actual archive SHA-256/byte size match the recorded receipt. Checkpoint003's
creation/restore success is recorded by the coordinator and the creator's
successful completion is gated on its restoration comparisons.

The fixed source and session selection policies meet the task's recovery scope:
required evidence belongs under `session/` or the explicit ignored-artifact
registry; reproducible toolchains/caches and downloaded manuscripts are
excluded. The archive README explains those boundaries and how to resume
without the original chat. No chapter acceptance is inferred from recovery.

### BOOT-SPEC-C — Immediate saved identity and exposure: satisfied

`receipts/checkpoint003-upload.json` preserves the exact successful Library
create response: `status: succeeded`, size 71,921,373, version 0,
`file_00000000938481f4a5882256a99d4b5f`, and
`libfile_a79c7eb64c94819192677e0c9b485bd6`. These values agree with
`checkpoints.json` and the inspected archive size.

For timing/exposure, the coordinator supplied a separately labeled attestation
from its direct conversation evidence: the successful capture was followed by
the upload, and the next assistant commentary exposed the exact native Library
link. This reviewer did not directly observe that parent-only tool exchange;
the saved structured response and coordinator exposure attestation are
distinguished rather than conflated. No unsupported upload timestamp is claimed.
Earlier saved checkpoints and their identities are also retained in the tracker.

Checkpoint003 contains receipts for checkpoints001–002. Its own receipt was
necessarily created after its capture and is preserved for the next checkpoint;
that ordering is not a recovery defect.

## Findings and limits

No new Spec finding is identified. The earlier recovery-assessment defects
CP-01 through CP-04 have concrete repaired-code and matching-fixture evidence
for the required cases; their historical reports remain available. This does
not assert an atomic snapshot against hostile writers, recovery of dangling
unreferenced Git objects, or a content-aware credential detector. The documented
stable-writer capture discipline and task-owned file inventory apply. None of
those limits currently omits identified task progress in the reviewed archive.

Reviewed evidence: `checkpoint.py`, `checkpoint-includes.json`,
`requirements/REQUEST.md`, `tracker/tickets.json`, `tracker/README.md`,
`environment/README.md`, `environment/summary.json`, the retained Lean smoke log,
`research/checkpoint-review.md`, `research/checkpoint-fixture.py`,
`research/checkpoint-fixture-evidence-r2.json`,
`research/checkpoint001-review-evidence.json`, `checkpoints.json`,
`receipts/checkpoint003-upload.json`, and the actual checkpoint003 archive.

No repository edits, remote writes, additional compilation or repeated fixture
runs were performed for this review. **Current bootstrap Spec outcome: Passed.**
