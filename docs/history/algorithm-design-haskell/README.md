# Algorithm Design with Haskell: preserved source snapshots

This collection preserves the supplied textbook formalization while conaled
reconstructs it under [#149](https://github.com/VladimirMarko/conaled/issues/149).
The compressed snapshots are immutable reference evidence, outside the public
library and normal source build. Read the
[assessment](../../research/adwh-preview-233-assessment.md) before selecting
code, and use the [library inventory](../../research/adwh-preview-233-inventory.json)
to locate main-library modules and their original hashes.

## Current reference

| Snapshot | Artifact | Provenance and file checksums | State at receipt |
| --- | --- | --- | --- |
| `adwh-checkpoint-233` | [checkpoint-233.zip](checkpoint-233.zip) | [Metadata](checkpoint-233.json), [member manifest](checkpoint-233.files.sha256) | Uncleaned preview; textbook chapters complete within their recorded scopes except the stock sixteen-queens numeral. Kernel integration and some experimental selections remain unfinished. |

The archive is the **complete original ZIP**, copied byte-for-byte from the
owner's supplied
`adwh-lean-233-transposition-accepted-and-strong-csp-producer.zip` on 2026-10-26.
It contains 10,463 files and occupies 67,920,919 bytes. Its SHA-256 is:

```text
8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63
```

The original Downloads path in the metadata records provenance only. Restoring
this snapshot requires the repository copy, not Downloads or a previous
checkpoint. Keeping the whole compressed artifact preserves proofs, coverage
ledgers, source corrections, accepted and failed experiments, review records
and recovery mappings without selecting away evidence needed later.

The archive excludes compiler binaries, prepared build objects, the full
textbook PDF and complete upstream kernel metatheory builds. Rebuilding needs
the pinned toolchain and any dependencies required by the selected experiment.
Integrity checks establish byte preservation; they do not establish new
mathematical acceptance. The assessment records the separate fresh 20-module
sample and audit, and distinguishes it from supplied full-library evidence.

## Find the right material

Paths in this table are relative to the ZIP root.

| Purpose | Location |
| --- | --- |
| Main mathematical library | `project/adwh-lean/ADWH/` and `project/adwh-lean/ADWH.lean` |
| Build and proof-audit controls | `project/adwh-lean/scripts/`, `lean-toolchain` and Lake files |
| Chapter scope and corrections | `project/BOOK-COVERAGE.md`, `project/docs/`, `project/adwh-lean/CURRENT-STATUS.md` |
| Source-to-declaration correspondence | `project/adwh-lean/correspondence/` and `project/adwh-lean/reports/` |
| Latest queens/kernel handoff | `next-iteration/checkpoint233-current-state.md` |
| Experiment sources and evidence | `next-iteration/` and `project/experiments/` |
| Historical restoration context | Root `RESTORE.md`, `CONTINUATION.md` and `CHECKPOINT-POLICY.md` |

Instructions inside the archive describe the producing session. They are
historical material, not current conaled agent instructions. Preserve the
original sources and reports; record corrections and new validation in current
conaled documents. Selecting a module for reuse does not accept its surrounding
experimental directory or imply a decision to replace Lean's kernel.

## Verify and restore

From the repository root, this checks the archived bytes, extracts to a fresh
system temporary directory, and verifies every member against the manifest.
It does not run any archived code.

```sh
direnv exec . python3 - <<'PY'
from pathlib import Path
import hashlib, json, tempfile, zipfile

base = Path('docs/history/algorithm-design-haskell')
meta = json.loads((base / 'checkpoint-233.json').read_text())
archive = base / meta['archive']
manifest = base / meta['member_manifest']
def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()
assert sha(archive) == meta['archive_sha256']
assert sha(manifest) == meta['member_manifest_sha256']
restored = Path(tempfile.mkdtemp(prefix='conaled-adwh-233-'))
with zipfile.ZipFile(archive) as source:
    source.extractall(restored)
rows = manifest.read_text().splitlines()
assert len(rows) == meta['regular_files']
for row in rows:
    expected, name = row.split('  ', 1)
    assert sha(restored / name) == expected, name
print(f'Verified {len(rows)} files in {restored}')
PY
```

The SHA-256 manifest uses archive-relative paths in sorted order and the
standard `sha256sum --check` format. It can also be checked from an already
extracted directory. Keep extraction and build outputs outside production
source paths. Use the repository's direnv environment when checking selected
Lean modules, as required by the root README.

## Adding the later completed formalization

1. Add the later archive under its own checkpoint identifier. Never replace
   `checkpoint-233.zip` or rewrite its manifest. Record its original filename,
   receipt date, archive hash and the predecessor snapshot in a new metadata
   file. Preserve the complete original unless a reviewed essentials selection
   also records what was omitted and why.
2. Generate a sorted per-file SHA-256 manifest using the same archive-relative
   paths. Add the snapshot to the table above and identify the preferred source
   for new work. Keep earlier snapshot references valid.
3. Compare the old and new manifests first. Equal path/hash pairs need no
   source-content reconciliation; changed, added or removed files need review.
   Distinguish main-library changes from experiment-only changes. A moved file
   with the same hash is a source relocation, not a new proof.
4. For changed families, compare the source and its import/dependency changes,
   statements, examples, toolchain and audit controls. Unchanged source bytes
   do not guarantee unchanged elaboration or proof dependencies. Revalidate
   the affected closure under conaled's pinned environment.
5. Connect each reconstruction slice to a **snapshot identifier, member path,
   declaration name and member hash** in its issue or migration record, alongside
   the conaled destination declaration. Record whether the result is retained,
   adapted, replaced with a proved equivalence, or deferred. This allows a later
   source change to be reviewed without replacing the reconstructed interface.
6. Treat a newly completed queens proof as a new source result to inspect and
   reproduce. Preserve the earlier unfinished status and separate native
   execution, stock Lean proof and validating-kernel integration evidence.

For example, a provenance reference can name
`adwh-checkpoint-233:project/adwh-lean/ADWH/Chapter10/Thinning.lean`
and `foldWithThinning_refinement`, with its file hash from the member manifest.
A successor snapshot can change that file while the original reference remains
resolvable. The existing module inventory supplements this with source imports;
it is not a substitute for statement and dependency review.

To produce a matching manifest for a future ZIP, run this from the repository
root, substituting the new archive path. The output goes beside that archive;
`'x'` prevents overwriting an existing manifest.

```sh
direnv exec . python3 - docs/history/algorithm-design-haskell/checkpoint-NNN.zip <<'PY'
from pathlib import Path
import hashlib, sys, zipfile
archive = Path(sys.argv[1])
with zipfile.ZipFile(archive) as source:
    names = sorted(i.filename for i in source.infolist() if not i.is_dir())
    assert len(names) == len(set(names))
    assert all(not any(c in n for c in '\n\r\\') for n in names)
    with archive.with_suffix('.files.sha256').open('x') as manifest:
        for name in names:
            with source.open(name) as stream:
                digest = hashlib.file_digest(stream, 'sha256').hexdigest()
            manifest.write(f'{digest}  {name}\n')
PY
```

A plain `diff -u` between manifests identifies path/content changes without
extracting either snapshot. Extract the relevant sources for semantic review.
Keep at least every snapshot used by reconstruction provenance; completion of
the migration does not itself make its historical evidence disposable.
