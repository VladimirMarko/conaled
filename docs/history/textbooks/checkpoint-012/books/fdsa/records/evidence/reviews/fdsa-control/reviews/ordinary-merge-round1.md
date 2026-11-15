# Ordinary merge: independent review round 1

Updated 4 November 2026. One existing XM01 implementation/review scope;
no new shared unit or reduced Chapter 2 scope.

Base: `07e480f6ec9958d4975bb90151005b84f2907614` (accepted Chapter 1).
Candidate: `72a0951aee406f7db67998d2a3bf8810f4e1bccc` (clean immutable source).
Merge base equals the fixed base. Full diff: `git diff 07e480f6ec9958d4975bb90151005b84f2907614...72a0951aee406f7db67998d2a3bf8810f4e1bccc`.
The exact six paths, commits, source hashes and frozen requirement identity
are in ordinary-merge-round1-identity.json. There are no source exclusions.
Read all ordinary-merge-requirements.md (SHA-256
b54e2b332cc31c04ac12fb5b19cc96fa494a80e1455fcfc173f59b6fe340d3d9), the original
candidate/source assessments, applicable AGENTS/standards/review-loop and
example-driven statement-review instructions. The frozen mathematical and
source/license requirements remain unchanged.

## Implementation and actual validation

Original source draft 5f409e71bb068e3b8cc133226046ce8bbe29d982 is retained.
57a7d338dedb53a5526bbbc05f7be5fd83443d03 corrected resource proof rewriting;
72a0951aee406f7db67998d2a3bf8810f4e1bccc corrected connected example proofs.
No algorithm, theorem statement, assumption, cost convention or independently
expected example value changed. Patches and dispositions are in
provenance/ordinary-merge-focused-20261104-proof-corrections/.

Focused attempts 1 and 2 failed, and their complete closed logs/actual exits
are retained. Attempt 3 passed all three requested modules, exit 0 in 31.376 s:
Applications.Sorting.Merge, Applications.Resources.ListMerge, Examples.MergeCosts.
The complete source note/public import/map remain in review scope despite not
being separate Lean targets. The necessary 17-declaration elaborated-type
inspection passed, exit 0 in 28.112 s, including raw sublists, arbitrary-relation
converse, input-local keyed iff, full measured map transport across independent
universes, comparison/entry bounds and the actual value-dependent clients.
No payload order/equality/inhabitance assumption was introduced in raw claims.

Every focused attempt retains its qualified native command result and closed
log. One Lean thread and a real private development dependency/output tree were
used; the separate foundation candidate is untouched. Import-module advisories
remain visible in logs; no source linter or proof guard was disabled.

These focused results are not a full integrated check or exhaustive audit.
The exact first foundation candidate f17cc6b is undergoing its own full gate.
Only after that candidate is accepted will root incorporate that exact accepted
tip, record the new base/candidate and integration resolutions, and run XM01's
full candidate check. The complete 112-obligation Chapter 2 review retains its
original accepted Chapter 1 base. Both XM01 axes must assess the final full
scope and terminal evidence, followed by immediate candidate verification.

## Existing findings and dispositions

- XM01-DOC01/02: original source provenance and cost-coordinate wording were
  corrected before 5f409e7. Preserve their historical assessment and verify the
  final candidate wording under the full source scope.
- XM01-DOC03: original notice whitespace normalization was explicitly disclosed;
  attribution, conditions and disclaimer were retained. Preserve the original
  before-correction notice evidence.
- XM01-ELAB-001: resource-proof API normalization now passes the focused library
  build. Whole-candidate confirmation remains pending.
- XM01-ELAB-002: connected-example proof elaboration now passes the focused build
  and required type readback. Whole-candidate confirmation remains pending.

## Independent axes

Standards: the complete independent six-path source assessment is finished,
with zero concrete unresolved findings. The report is ordinary-merge-standards.md
(30,495 bytes; SHA-256
c5dded3c7b52fc1b0978b2ec8b13abcb17d2b7c047c5c83981f8a9c7d56e7992).
Overall outcome: Blocked pending full integrated candidate validation.

Spec: the complete independent frozen-scope source assessment is finished,
with zero concrete unresolved findings. The report is ordinary-merge-spec.md
(28,222 bytes; SHA-256
bc4999120b89f330b57641543070cf34a34f8bc207fd004b09aa14ef4125fe09).
Overall outcome: Blocked pending full integrated candidate validation.

Each axis wrote its own new report, retained stable finding identifiers and
stated source assessment separately from missing terminal validation. Both
historical and new findings remain in this one scope record. Root coordinates
findings and evidence, without performing a third final review axis.

## Acceptance remains pending

No XM01 ticket closure, accepted-branch update or whole-sort count claim follows
from this round's focused success. In particular, the queue example observes
one raw list merge after child enumerations; it does not measure child traversal,
a whole tree, compiled runtime or binomial carry propagation. All remaining C2,
C14 and binomial obligations retain their original scopes.
