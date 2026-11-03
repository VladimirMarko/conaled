# Historical square-compiler artifacts

These are preserved records of earlier deliveries, not current project
requirements or validation evidence. The three archived files are unchanged;
their relative source paths and command examples describe the original tree.

| Artifact | Provenance and limits | Current entry point |
|---|---|---|
| [DESIGN.md](DESIGN.md) | Original `foundation-v1` design, including Lean 4.19.0 and the original dependent-family model. Later library developments exceed this scope. | [Architectural requirements](../../agents/architectural-quality.md), [ADRs](../../adr/README.md), and [language direction](../../language-direction.md). |
| [verification.txt](verification.txt) | Historical output for 52 local modules, last updated in `d5149c323ba09530c3b5125979ebab4592324880` (the Lean/Mathlib 4.35.0 upgrade). It is not evidence that the current checkout passes. | [Build and audit instructions](../../../README.md#build-and-audit); run the applicable checks on the candidate being assessed. |
| [SHA256SUMS](SHA256SUMS) | Historical manifest last updated in the same upgrade. Its paths are relative to the old repository root, not this archive directory; its hashes do not describe today's checkout. | Git revisions identify source snapshots; current validation follows the [build instructions](../../../README.md#build-and-audit). |

`DESIGN.md` is byte-identical to the file at `foundation-v1`. The log and
manifest are byte-identical to their versions at the upgrade commit above.
Their SHA-256 digests at archival are:

```text
2a9947eaa88587866bacc57ce30cedfe0770f3fe69f0926af362173721a7b291  DESIGN.md
28e2c30a5fd96545584ae0af083274e2da09a7757d07c5a27e07ebbdeae57f6d  verification.txt
d924af248155e60c572bad41bc6b11cb2ad83606b7c2bea138708cbc160199ca  SHA256SUMS
```

[APPLICATIONS.md](../../../APPLICATIONS.md) remains a maintained coverage
document at the repository root. It includes later additions and is not frozen
with these artifacts. See the [project map](../../../README.md#what-is-in-the-library)
for developments beyond its selected coverage.
