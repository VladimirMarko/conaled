# FDSA-XT02 committed source-draft handoff

Recorded 2026-11-02. **Committed uncompiled draft; not accepted.**

- Fixed initial base: `64c6b777d828ecfe83234fc2aed94600a1f24297`.
- Candidate: `974a97321a8ec174b56104c7e6efaaca881b6639`.
- Branch: `work/fdsa-tree-shape`.
- Worktree: `/workspace/scratch/845aa1048b05/conaled-tree-shape`.
- Requirements: `tree-shape-requirements.md`, version 1, SHA-256
  `50d11472d8380fb3458a3ea71aba3d1104886f676a7b1cec578c0557a6979e91`.
- Commit: `feat(trees): add shared sharp shape bounds (#174)`.
- Scope: six files, 838 insertions; clean index and working tree after commit.

The exact initial state remains in `tree-shape-start.json` and its handoff.
Checkpoint 0029 retained that clean pre-code branch and frozen requirements.
`tree-shape-source-identities.json` records every current file's bytes, lines
and SHA-256. The corrected example source is part of this committed candidate;
its earlier preflight version is retained separately, never substituted for
the current source.

## Implemented draft and intended connections

`Applications/Trees/Shape.lean` supplies the minimum external-leaf height as
an ordinary fold, independent recursive completeness, almost completeness
with the source subtraction equivalence, map laws and immediate-child closure.
It establishes the two power bounds, both strict incomplete variants and
both equality characterizations, then derives the natural log/clog bounds,
exact almost-complete formulas and cross-universe height optimum. The natural
module has no real-analysis import.

`Applications/Trees/ShapeLog.lean` supplies the actual real sandwich, strict
incomplete bounds, complete height/log equality and almost-complete natural
floor/ceiling formulas, using the pinned real-power/cast/log APIs and positive
external-leaf count. Nil has one external leaf throughout.

`Examples/TreeShape.lean` consumes these public results with the independently
expected empty, singleton, complete, skew and right-heavy shapes. It reuses
XT01's asymmetric sample, noninjective relabelling and actual cached trees,
including malformed size annotations. A new ordinary minimum-height cache
specialization consumes `Cached.read_eq_fold` and actual `annotate`, with no
new tariff. A Boolean-labelled optimal-height counterexample is compared to
the natural-labelled sample and to arbitrary later competitors. The all-node
sibling-height-balance counterexample has seven nodes, eight leaves, minimum
height two and maximum height four.

`SquareApplications.lean` imports `Examples.TreeShape`, whose imports reach
both new domain files. The reconstruction note and existing map state the
exact partial/shared source correspondence and all remaining chapter scope.
No source chapter or inventory row is marked complete by this commit.

## Source assessment and retained finding

The implementation-side statement assessment is in
`docs/research/fdsa-tree-shape.md`. It retains leaf/node offsets, independent
universes, the empty domain, recursive meanings, strict versus rounded claims,
actual public-result connections and nonconverse witnesses.

`tree-shape-source-preflight.md` retains the independent architecture/API,
source-correspondence and client readings. Those readings supplied no concrete
mathematical/API finding, but the client pass reported **XT02-SP01**, a minor
docstring that described recursive cache validity as necessary rather than
sufficient for root correctness. The theorem was already correct. The
wording was changed and the same reader confirmed the exact correction in
a narrow recheck. The original file and both hashes remain recorded. Final
review confirmation is pending; this finding is not erased by the commit.

## Actual validation and limits

The pinned Nix shell's Git confirmed the exact base, previously empty index
and six owned changed paths. The tracked unstaged whitespace check and the
complete staged `git diff --check` passed. All six files were committed, and
the resulting index/working tree were clean. Ordinary cryptographic identities
of the three reviewed Lean files matched their held source versions, including
the corrected example docstring.

**No Lean compiler, focused build, project checker/hash helper, complete gate,
exhaustive audit or independent final review was run for this unit.** The
old Chapter 1 candidate gate remains active in its separate unchanged checkout.
Source readings and whitespace checks do not establish elaboration or proof
acceptance. No older candidate result applies to this new commit.

## Resumption and acceptance boundary

1. Let the existing old-candidate gate finish unchanged and preserve its actual
   historical outcome. Its open Chapter 1 source findings still prevent that
   old candidate's acceptance, regardless of build outcome.
2. Validate and accept the repaired Chapter 1 through the retained procedure.
   Integrate/accept XT01 through its own matching gates before this unit.
3. Incorporate the exact accepted prerequisites into the XT02 candidate,
   preserving this original base/history, full frozen scope and XT02-SP01.
   Record any changed review base and conflict resolutions explicitly.
4. In an isolated stable checkout, run focused compilation and the applicable
   complete candidate build/guards/audit. Preserve actual output and the success
   record. Any compiler correction creates a new candidate.
5. Obtain both independent final review axes on the same candidate and full
   scope, carry all findings forward, and immediately verify that exact
   candidate before acceptance. Save/upload the accepted checkpoint.

Neither this draft nor its source-only preflights changes chapter order.
Boolean completeness checking, general subtree results, constructor exercises,
Braun/weight-balance and leftist representation/algorithm/cost obligations
remain mandatory in their owning chapter or shared follow-up. Checkpoint 0030
is intended to preserve this committed draft and all local records; its receipt
is recorded only after successful creation and upload.
