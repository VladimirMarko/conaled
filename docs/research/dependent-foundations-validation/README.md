# Dependent foundations validation records

These records retain the reviewed component candidates for #314–#319 under
[#289](https://github.com/VladimirMarko/conaled/issues/289). They accompany the
[architecture reassessment](../dependent-architecture-reassessment.md).
#320 and final integration acceptance are still pending. A component approval
covers its recorded commit, not later source changes.

| Issue | Accepted candidate | Review record |
| --- | --- | --- |
| #314 | `3484ce523bf23524f715a3a2029c290a2d43c4c0` | [Both axes and validation](reviews/314-review.md) |
| #319 | `f0773fee8fa40214c67606c46ba8c41eed8e674b` | [Both axes and validation](reviews/319-review.md) |
| #316 | `d7d2beeea699bccc2f7eb0fee7f8fa52e6718186` | [Both axes and validation](reviews/316-review.md) |
| #318 | `de2b1987e2f2caaad83ecddedb05c3ccded5bfff` | [Both axes and validation](reviews/318-review.md) |
| #315 | `bb77d67171e6cb610e43149394c8a9b9a0deab3f` | [All rounds and finding disposition](reviews/315-review.md) |
| #317 | `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96` | [Both axes and validation](reviews/317-review.md) |

The reports, receipts, acceptance logs, substantive statement-review notes and
failed full candidate checks are copied without modification. The
[manifest](manifest.json) records their SHA256 hashes. Saved issue bodies in
`specs/` record the reviewed requirements; GitHub owns their current status.
Formal component acceptance includes exhaustive proof audit, the four audit
regression fixtures and immediate candidate verification. #316 instead has
source-only Agda validation; its [experiment](../../../experiments/dependent-higher-identity/README.md)
retains source, import closure, check log and receipt. #318 is a documentation
assessment with artifact-specific validation. Neither counts as a new Lean
model construction.

Absolute `/tmp/conaled-314-320/` paths in these historical records identify the
original isolated checkouts and evidence. Archived `reviews/`, `specs/` and
`records/` paths are relative to this directory. Repository source paths refer
to the recorded commits. Development-only focused build logs and temporary
statement-query files are not all archived; their absence does not erase the
retained full acceptance or failure logs. Scripts in this archive preserve the
commands used and their original paths; they are not portable replay tools.
These are trusted local validation records, not cryptographic provenance of
compiler execution. Hashes identify the retained files, not the truth of their
contents.
