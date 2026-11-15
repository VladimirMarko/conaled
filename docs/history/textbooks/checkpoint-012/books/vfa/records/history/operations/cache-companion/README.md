# Optional cache recovery companion

This local utility preserves completed project compilation that would be
expensive to repeat after workspace loss. It saves **unaccepted cache data**.
It does not accept a chapter or replace the complete source/history/ticket
checkpoint, guarded build, proof audit, regressions or independent reviews.

Read `AMENDMENT.md` and the external specification
`work-state/specs/1027-cache-companion.md`. Real capture is permitted only after
`work-state/validation/1027-acceptance.json` records both passing review axes
and exact delivered-candidate verification. Historical requirements remain
unchanged; this explicit amendment supplies the narrow exception.

## Capture and publication

First create, restore-check, expose and upload a complete source checkpoint
containing the accepted utility and review evidence. Construct a binding JSON
from that checkpoint's verified creation result and successful upload receipt:

```json
{
  "filename": "conaled-vfa-checkpoint-NNN-description.tar.gz",
  "sha256": "THE_EXACT_64_LOWERCASE_HEX_DIGEST_FROM_THE_RECEIPT",
  "size_bytes": 123,
  "library_file_id": "libfile_EXACT_RETURNED_ID",
  "source_commit": "THE_EXACT_40_LOWERCASE_HEX_COMMIT"
}
```

The values above are placeholders. Use the real byte size and identities;
never manufacture a successful upload record. Keep the binding in local
validation evidence. The companion's manifest repeats it, and the next complete
source checkpoint preserves its own creation/upload receipt and this binding.

Use the project's pinned Nix environment. The source checkout may be running
the existing build; capture reads it conservatively without writing its cache.
The output directory must already exist **outside** that checkout:

```bash
nix develop /absolute/workspace/conaled --command python3 -B \
  /absolute/workspace/work-state/cache-companion/cache_companion.py capture \
  --repo /absolute/workspace/vfa-validation \
  --binding /absolute/workspace/work-state/validation/cache-source-binding.json \
  --archive /absolute/workspace/checkpoints/conaled-vfa-cache-NNN.tar.gz
```

The CLI publishes the final name only after a private archive extraction check.
It prints the path, complete SHA256, size, module count, omitted count and check
outcome. **Expose and upload that completed archive immediately**, then record
the actual receipt in the next complete source checkpoint. A failed capture
does not produce a final archive and does not authorize a retry that interrupts
the build or changes its configuration. Diagnose the concrete failure first.

The Python API allows replacing the external Lake runtime for synthetic tests.
The CLI always uses `PinnedLake`; synthetic fixture archives are disposable
test data and must never be uploaded as actual compilation recovery.

## What is saved and checked

The tool inventories tracked root, SquareKit, Applications and Examples Lean
modules, excluding ProofAudit. It checks the source commit/tree, full integrated
source digests, configuration/toolchain/Nix files, all resolved Git dependency
pins and actual compiler/platform identity before and after capture. The
manifest records where the cache was captured. It does not claim that every
entry was compiled from that candidate; consistent older entries are allowed.

For each supported trace, it copies the complete declared artifact family:
olean parts, ilean, generated C, and any declared IR, bitcode or ltar outputs.
Raw trace bytes retain their original inputs, depHash and captions. An artifact
is read through ordinary directories without following symlinks, must be a
singly linked regular file, and must have stable device/inode/size/mtime/ctime
and link count across the read. Copying and SHA256 use a streaming pass. The
trace and live family identities are checked again after cohort hashing.

Missing, malformed, mismatched, linked or racing families are omitted whole,
with reasons in the manifest. No final archive is produced if none survive.
Setup JSON, `.hash` sidecars, native object/shared-library facets, undeclared
files, external dependency caches and `.lake/verification.json` are excluded.

The unchanged Lake helper hashes the fixed private copies in one invocation,
with one worker and a 60-second timeout. It imports installed Lake and elaborates
the small executable helper; it does not compile project formal modules or
produce compiler artifacts. Each file is read into a ByteArray by Lake, so the
tool limits individual artifacts to 128 MiB and the cohort to 750 MB. Python
copying, archive hashing and extraction are streamed. Capture reserves capacity
for staging, packing and extraction plus 500 MB; extraction checks its own
reserve. Root capacity uses `f_bfree`, other users use `f_bavail`.

Every retained output must match its trace's pinned Lake hash. The archive
check then compares exact members, regular-file types, safe fixed paths, sizes,
SHA256 digests and complete family/trace descriptions. Hashing and parsing use
the same anchored archive descriptor. These checks address accidental mismatch
and ordinary concurrent build writes. They do not certify source provenance,
authenticate hostile substitutions, establish dependency-cache integrity, or
prove that no transient writer exists. #1025 remains a separate investigation.

## Recovery

Restore the named complete source checkpoint first and read its `STATUS.md`,
requirements, review record and `conaled/AGENTS.md`. Recreate the pinned Nix,
Lean and external dependency environment as documented in `environment.md`.
Use a separate isolated checkout at the companion's exact source commit. Do
not share writable build directories or hardlink outputs between checkouts.

Obtain the companion's full SHA256 and source binding from the saved creation/
upload evidence. If those identities are unavailable, or the compatible pinned
environment cannot be recreated, skip this optional cache and rebuild from the
complete source checkpoint. Source progress and tickets remain recoverable.

To inspect all bytes against an actual clean checkout without installing:

```bash
nix develop /absolute/recovered/conaled --command python3 -B \
  /absolute/recovered/work-state/cache-companion/cache_companion.py verify \
  --repo /absolute/recovered/vfa-validation \
  --binding /absolute/recovered/work-state/validation/cache-source-binding.json \
  --archive /absolute/recovered/checkpoints/conaled-vfa-cache-NNN.tar.gz \
  --sha256 EXACT_DIGEST_FROM_THE_SAVED_RECEIPT
```

Installation uses the same arguments with `restore` and `--idle-checkout`.
That flag acknowledges that no build/editor process is writing the isolated
checkout; it is not automatic proof of idleness. The project build directory
must be absent or empty. Links, incompatible inputs and nonempty destinations
are refused. Installation uses independent ordinary files, never merges into
an existing cache, and never installs a validation success record. Keep the
checkout stable during the operation. Raw absolute trace captions are retained;
reuse after changing root paths is not guaranteed. Lake may rebuild normally.

Then run the complete existing acceptance sequence from that checkout:

```bash
LEAN_NUM_THREADS=1 nix develop --command ./check.sh --candidate HEAD
LEAN_NUM_THREADS=1 LAKE_ARTIFACT_CACHE=false nix develop --command \
  lake --no-cache --rehash build +ProofAudit
LEAN_NUM_THREADS=1 nix develop --command \
  lake env python3 scripts/test-proof-audit.py
```

Continue only after each command actually succeeds. Obtain both independent
review outcomes on the exact candidate and complete evidence. Immediately
before chapter acceptance, run:

```bash
nix develop --command ./check.sh --verify-candidate HEAD
```

Use fresh verification whenever the repository's README requires it. This
companion changes none of those conditions. Later source changes follow the
ordinary incremental invalidation and acceptance workflow.

## Validation and adapter provenance

Run synthetic public-interface tests from the frozen operational checkout:

```bash
nix develop /absolute/workspace/conaled --command \
  python3 -B -m unittest discover -s /absolute/operational-checkout -v
```

They cover complete round trips and declared output variants, omitted partial
or changed families, source/environment mismatch, malicious archive paths and
members, non-overwrite behavior, explicit idle acknowledgement, and a bounded
Python memory case. Only the external Lake process is substituted; files and
small Git checkouts are real private fixtures. Test artifacts are deleted.

For the required single real-helper smoke check, run `check_pinned_runtime.py`
in that same pinned environment, supplying `--repo` for the conaled checkout
and `--work-dir` for a private temporary-directory parent. It hashes two literal
files in one bounded invocation, checks result shape and repeated-input
consistency, records actual hashes/compiler identity, checks no compiler
artifacts appeared, and removes its temporary directory. Do not run it as an
unnecessary repeated benchmark beside the primary build.

The two files in `vendor/` are exact source copies from conaled candidate
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`:

| Source file | SHA256 |
| --- | --- |
| `scripts/lake_integrity.py` | `293c1e5bbf1a818b9fa49455194afc6e58d28b4194d5f6d2b7a2948f7894d90f` |
| `scripts/lake-output-hashes.lean` | `fd6de36b9f4065af286332c9058ad220f4ca74c4d0aecf29ab5779f2cc96689b` |

The utility checks both copies and the source checkout's adapters before use.
Changed layouts, schemas or toolchains require a separately reviewed adapter;
there is no fallback parser, hash implementation, cache repair or build.
