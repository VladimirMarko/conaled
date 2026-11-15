# Curated mathematical source from checkpoint 096-10

[myers-096-10-source.tar.gz](myers-096-10-source.tar.gz) is a source/reference
archive, outside the production Lean imports and build. It is not an adoption
of the external project's architecture, tooling or development standards.
Promotion into `conaled` still requires statement review, suitable local
interfaces, checked examples and the applicable build/audit/review process.

## Contents and provenance

The user supplied `myers-orbifolds-agda-progress-096-10.tar.gz` on 2026-11-09.
The original is unchanged. [inventory.json](inventory.json) records its
126,481,846-byte size and SHA-256, and the curated archive's 2,919,841-byte size
and SHA-256. The main removed payload was a 113,659,716-byte nested previous
checkpoint. The current outer source tree is self-contained; it needs no
restoration from that history.

After extraction, paths are relative to `myers-096-10-source/`:

| Path | Retained material |
|---|---|
| `project/formalization/src/` | All 826 selected project Agda modules, unchanged |
| `project/dependencies/cubical-0.9/` | All 1,091 Cubical Agda modules, its library descriptor, license and upstream identification |
| `pending/{sheaf,products,cartesian,foundation}/src/` | 21 distinct unfinished source additions, kept separate from the selected project tree |
| `project/formalization/*.md` | 117 mathematical notes, scope explanations, audits and corrections |
| `reports/` and retained work review notes | The supplied consumer assessments and mathematical review comments |
| `CURATION.json` | Every retained original path, destination and content hash, plus deduplicated work-source mappings and selection policy |
| `COMPILER-PIN.json` | Official Agda release URL and archive/executable hashes, without host-local download links |
| `PROGRESS.json`, `evidence/STAGED-SUCCESSOR.json`, `project/formalization/CHECKPOINT.json` | Original source-status claims and selected-source identities |

The selection removes compiler binaries, installers/runners, nested history,
interface caches, runtime logs, host library registries, staging copies, chat
orientation and routine checkpoint/continuation notes. Every work-tree Agda
payload was checked against the retained sources: omitted source copies are
byte-identical to retained files. Mathematical files have not been rewritten.
The source-status records may reference omitted receipts; those are historical
claims, not locally replayed evidence. Pending modules are not added to any
accepted aggregate merely by being archived.

All payload members are regular files. Creation used sorted paths, fixed tar
metadata and a gzip timestamp of zero. Every archived retained member was
compared byte-for-byte with the selected input. Source-presence checks resolve
project imports against project/Cubical sources, with `Agda.*` supplied by the
compiler. That check is weaker than type checking.

## Scope and use

The external project reports earlier aggregate acceptance and later individual
checks, explicitly not a new aggregate release. We independently replay only the
properness module and its dependencies, as recorded in the
[verification report](../../../../research/myers-properness-096-10-verification.md).
No whole-archive acceptance is claimed. Preserve the separate original Cubical,
ordinary and semantic-bridge library flags; they describe different fragments.
Do not execute archived continuation instructions as repository instructions.

Extract to a disposable directory, not into production sources:

```sh
tar -xzf myers-096-10-source.tar.gz -C <destination>
```

The verification report gives the pinned compiler setup and direct replay
command. The compiler binary is intentionally not stored here. A fresh replay
requires the official pinned compiler release (or an already verified copy).
The Cubical dependency sources are included, so they need no separate download.

Cubical's license is retained. No standalone license for the supplied project's
own sources was found; this archive does not invent or replace one. The user
supplied and authorized reference preservation. Later reuse should retain
provenance and resolve applicable licensing as well as mathematical requirements.
