# Environment recovery instructions: bounded review

Recorded 2026-11-02 by the independent environment reviewer.

## Scope and frozen input

Reviewed `work-state/environment.md` at SHA-256
`d84706a93940c1115e7ff230519fd70a10520344fca036c48d6a633560bb1345`.
The repository inspected was at commit
`1da24c77d10fe03296dbf117e4249283139f5021`.

This was a read-only comparison of recovery prose with the pinned README,
configuration, validation scripts, checkpoint restore implementation, and
existing operational evidence. It did not run recovery, a compiler, a build,
a cache command, a process probe, an advisory operation, or a remote upload.
Only this review file was written. It is not candidate or chapter acceptance.

## Finding ER-1: misspelled cache-control variable (open)

The committed-acceptance command sequence currently spells the prerequisite's
environment variable `LEAN_ARTIFACT_CACHE=false`. The intended variable is
`LAKE_ARTIFACT_CACHE=false`, as recorded in
`validation/1002-audit-regression-prerequisite.md` and used by
`conaled/scripts/check.py:293–295`.

Root should change that command to:

```bash
LAKE_ARTIFACT_CACHE=false nix develop --command lake --no-cache --rehash build +ProofAudit
```

The preceding `export LEAN_NUM_THREADS=1` remains in effect. The explicit
`--no-cache` and `--rehash` flags are already correct; this spelling error is
not evidence that an executed guarded gate was weakened. Root confirmed the
documentation typo and that the prerequisite has not run on this candidate.
No documentation correction was made by this reviewer. Recheck the exact
corrected document hash before closing ER-1.

## Assessment of the remaining instructions

**Command order is consistent.** The sequence performs the complete candidate
check, then the managed `+ProofAudit` target, the unchanged regression, and final
candidate verification. The text requires success at each step and both
independent review axes before final verification/acceptance. In incremental
mode `check.py:296–311` excludes `ProofAudit` from the explicit module targets
and executes its source without an output flag. The regression imports
`ProofAudit` and invokes its command on each fixture
(`scripts/test-proof-audit.py:18–52`). `lakefile.toml` includes `ProofAudit` in
the library globs, so the prerequisite is a normal managed target. Fresh mode
also removes its private outputs, so it does not supply a persistent import
artifact. The prerequisite record's instruction to preserve the matching
verification first remains applicable through the explicit cross-reference.

**Pins and fresh restore layout are consistent.** The recorded Lean version and
Mathlib revision match `lean-toolchain` and `lake-manifest.json`; the Nix shell
provides the tools used in the recipe. `tools/checkpoint.py:69–102,119–164`
restores `conaled/` and sibling `work-state/`, selects the captured commit, and
restores index/working-source state. It does not restore a `vfa-validation/`
cache. From the stated clean-main prerequisite, creating
`../vfa-validation` before running `lake exe cache get` in that worktree is a
valid fresh layout and avoids deliberately populating a second main cache.
Restored uncommitted work must be handled before that clean-main recipe; the
document does not claim every checkpoint is clean. The historical dependency
copy remains explicitly optional, capacity-dependent, and separate from mutable
project outputs.

**Concurrency claims retain their evidential limits.** The restart record
documents four-thread pressure and a later single-thread run. The revised prose
describes observed progress without claiming a controlled speed comparison or
normal performance. Fresh-mode scheduling is a separate Python worker limit:
the referenced README:205–218 gives `--fresh --jobs 1`; merely exporting
`LEAN_NUM_THREADS=1` does not set that fresh-mode `--jobs` value. The document
delegates fresh-mode conditions and invocation details to that README.

**Storage and cache claims are appropriately qualified.** The prose no longer
asserts that the main Mathlib cache remains absent. It distinguishes the initial
reclamation from later unexplained inactive-path recreation and requires actual
artifact inspection for subsequent checks. Cache-download success is not
presented as complete artifact coverage. The local-retention record supports
the limited retirement of copies 012–014 after their recorded hash/size/Library
binding checks. The advisory record reports 74,135 successful requests, with
no active-cache file advice, and explicitly does not measure reclaimed pages
or a speedup. The text preserves those limits. The #1025 disposition remains
open and nonblocking unless concrete active-input or integrity evidence changes
it; no absence-of-writer guarantee or acceptance substitute is introduced.

No additional concrete command-order, restore-layout, or unsupported-claim
finding was identified within this bounded comparison. ER-1 remains open.

## Principal evidence identities

| Input | SHA-256 |
| --- | --- |
| `conaled/README.md` | `3f3a7d6e7c77bfd923998c2b297931d92fade83d2be266cd9a0feb3ee6d82030` |
| `conaled/scripts/check.py` | `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29` |
| `conaled/scripts/test-proof-audit.py` | `72e8f1c06ad1ca427b6b2edb914cbf4c36b028a381a205be047f5792fcb1f839` |
| `conaled/ProofAudit.lean` | `8099f95ca5886ced6b0f3be7793dce5e348a4a3a855732549446c645fb3fe6fd` |
| `work-state/tools/checkpoint.py` | `deeb1cfc3255bff5d4f493d8906c821751006eadd0f1e88583f12f1ff0d4eece` |
| `validation/1002-audit-regression-prerequisite.md` | `047a35a2bf54eee4bcd6c58d196e369a9f5be4e5ec7a0f4e2c8d955bc08550b2` |
| `validation/1002-build-restart.md` | `fa11c514149b99a50edf8163f91840809bcc8de21f79e5cba11522d9b62b6183` |
| `validation/1025-proportional-disposition.md` | `153f92a98a6a211407300deee2653f18e8af5056812f683ed9ecdf78bdabf999` |
| `validation/20261102-checkpoint-local-retention.json` | `c9ddfb2d2266fb248eb9ebc672e2829397b86d9715c20f44a6768db2b6814edd` |
| `validation/20261102-inactive-cache-advisory.json` | `13e219f364db646febd0bcbfa1f3737e7d5bad524dcc5e9a87725508c4415a2c` |

Paths beginning `validation/` in this report are relative to `work-state/`.

## ER-1 resolution: narrow recheck

Root corrected the documentation. The current `work-state/environment.md`
SHA-256 is
`0053f41cceb625fba92bad9dc7430ce343fdd5881f2351603c0be83a12651380`.
The preserved pre-correction file,
`validation/environment-recovery-before-ER1.md`, matches the originally reviewed
SHA-256 `d84706a93940c1115e7ff230519fd70a10520344fca036c48d6a633560bb1345`.

A byte comparison verified that the current file is exactly the original with
its single `LEAN_ARTIFACT_CACHE=false` token replaced by
`LAKE_ARTIFACT_CACHE=false`. All other bytes are unchanged. This fixes ER-1;
the earlier open-finding statements above describe the preserved original
review. There are no unresolved findings within that bounded review's scope.

This recheck compared only the two document versions and appended this
resolution. No compiler, build, monitoring, source, cache, or environment change
was performed by the reviewer. The reviewed instructions remain recovery
guidance, not candidate or chapter acceptance evidence.
