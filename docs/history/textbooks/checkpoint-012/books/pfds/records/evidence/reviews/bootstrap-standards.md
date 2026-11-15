# Local #10000 — independent Standards review

**Outcome: Passed. Unresolved findings: 0; worst severity: none.**

Reviewer: `/root/validation_health`, 2026-11-02. This review covers the local
environment/recovery bootstrap only. It does not approve #10013, any Lean
candidate, any book chapter, or whole-book completion.

## Immutable scope

The bootstrap files are task records outside the repository. Accordingly the
immutable candidate is the relevant file set in checkpoint 003, SHA-256
`37a8dc11bdb3899f1dbbc7c411f4c011c31d45e06eb941567022e603f45bc107`.
All reviewed live files listed below matched their archived bytes. Historical
baseline: checkpoint 001, SHA-256
`f4db5d8f707399e597e94279dd5068d4a688d092f691b70a6dbd0b581bb40525`.
This is an artifact comparison, not an invented Git diff for untracked session
files. Repository baseline is `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`;
checkpoint 003's repository HEAD is
`ad730010ab1929bbd7a16a035c7990a6f328b178`, whose formal changes are excluded here.

Key SHA-256 identities:

| File under `session/` | SHA-256 |
| --- | --- |
| `checkpoint.py` | `617c14ed63170ee39a8ac1df2eb4cc20b1b509ebd5f1d4c16ae4e469b7ed51ab` |
| `checkpoint-includes.json` | `45bef2dc87e891011fb40113e545bc84e893e1d60ea9a612f27027d232b8073c` |
| `environment/README.md` | `888565fca99dd532325b2212d0129ac4be696a15efa03e9ce618af373990edb9` |
| `environment/summary.json` | `a110aaac4ff36354220c0618ba2428b5eca1d0ed42aab4b256b1a343ca76a24f` |
| `requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `research/checkpoint-fixture.py` | `3273411d423de7205da610ea328389822200204eeedd278552c05468fd0a231f` |
| `research/checkpoint-fixture-evidence-r2.json` | `183ef5dc715afe7bafdd88df6e6203a342200a9920a74d7c97521cd5e5a3dad5` |

The supplementary post-upload receipt file `checkpoints.json`, including the
receipt for checkpoint 003 itself, had SHA-256
`e77d6570eb7e89e5fcb4eb2ad03e7c1b1ce7d9229f0aacd9e76bebc121fbc816`.
Its newest receipt necessarily postdates the archive it describes.

## Standards and validation evidence

Applied `AGENTS.md`, README environment/validation rules, the independent
review procedure and code-review heuristics, with the user's explicit local
tracking and checkpoint-upload instructions. No repository tooling or pin was
changed by bootstrap; a baseline-to-HEAD diff for `.envrc`, `flake.nix`,
`flake.lock`, `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` was empty.

The environment note accurately distinguishes the installer's failed profile
activation from the working real Nix binary. The retained smoke log reports
the pinned Lean 4.35.0 compiler; the cache log ends successfully. All nine
recorded dependency revisions match the actual manifest, and the recorded Lean
pin matches `lean-toolchain`. The note expressly excludes full project/proof
acceptance. No new Lean compilation was required or performed for this review.

Inspected the complete checkpoint generator, its embedded restore program,
fixture harness and original/repaired evidence. The five repaired fixtures
exercise dirty index/worktree/binary/deletion/untracked recovery, task-record
race rejection, explicit ignored-file selection, credential-name rejection,
symlink rejection, and exact custom/symbolic/remote/tag ref recovery. Their
script hash matches the candidate. These meaningful recorded tests were reused;
no expensive fixture was rerun without a remaining defect to investigate.

Independently verified archive 001–003 sizes and SHA-256 values against receipts.
For archive 003, all 43 manifest member hashes matched, its embedded restore
program exactly matched the reviewed generator, and its full file inventory
contained the expected task records with no downloaded manuscript or helper
credential material. The untracked-source archive was empty at this committed
checkpoint. All three receipt Library IDs matched the files' local upload
metadata; no remote operation was performed. Saved-upload receipts are evidence
of the completed writes, not a new live availability test.

## Prior findings retained and resolved

| Prior ID | Disposition and evidence |
| --- | --- |
| CP-01, inconsistent session snapshot | **Resolved for the documented trusted-writer workflow.** `records()` fingerprints the selected path set, copied bytes are compared immediately, and the live inventory is compared again. The injected update fixture now aborts without a completed archive. Writers must still pause; hashes do not create an atomic hostile-writer snapshot. |
| CP-02, omitted needed files | **Resolved.** Ordinary session files are included regardless of extension/size; reproducible exclusions are documented. An explicit ignored-artifact registry and restoration comparisons cover needed ignored repo files. The selection fixture retains both its session Lean file and opted-in log. |
| CP-03, privacy/symlink policy | **Resolved within the bounded task-owned policy.** Session symlinks and conventional credential filenames are rejected; corresponding fixtures abort. The archive inventory was inspected. This is not a content-aware secret detector, and arbitrary future source files still need normal ownership/content review before upload. |
| CP-04, missing restored refs | **Resolved in the current candidate.** The restore program unbundles, recreates direct/symbolic refs and removes clone-created extras; capture checks exact restored refs. The fixture includes an otherwise unbranched review commit, symbolic ref and annotated tag. This does not retroactively change checkpoint 001's older restore behavior. |

## Acceptance limits

Restoration is for a new destination with Python 3.12+ and Git; caches/toolchains
are intentionally recreated through the pinned project environment. The
complete bundle preserves reachable history/refs, not arbitrary dangling or
reflog-only objects. A required review commit must remain reachable through a
retained ref. The checksums detect accidental corruption and the restore test
checks captured state; neither is a mathematical proof certificate or hostile
archive authentication. These limits are compatible with this bounded bootstrap.

The scoped bootstrap has no remaining Standards findings. Required formal
builds, audits, final candidate verification, source completeness and both
formal review axes remain separate gates and must not inherit this approval.
