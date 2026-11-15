# Shared binary-tree observations: committed draft handoff

Recorded 2026-11-02. Local scope: FDSA-XT01.

## Immutable source identity

- Fixed initial base: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Draft candidate: `64c6b777d828ecfe83234fc2aed94600a1f24297`.
- Branch: `work/fdsa-tree-cache`; worktree: `conaled-tree-cache`.
- Commit: `feat(trees): add shared cached-fold observations (#174)`.
- Seven changed files, 894 insertions. The index and working tree were clean
  immediately after the commit.
- Exact requirements: `binary-tree-cache-requirements.md`, version 1,
  SHA-256 `81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce`.
- Per-file SHA-256, byte and line identities:
  `binary-tree-cache-source-identities.json`.

The pre-code starting record and checkpoint 0027 retain the clean original
branch and requirements. This candidate is a descendant of the unaccepted
Chapter 1 repair, not a substitute for its acceptance. No tree implementation
is present on the main old-candidate branch or active validation checkout.

## Implemented draft and intended public connections

`Applications/Trees/Observations.lean` uses Mathlib's existing BinaryTree for
an ordinary branching fold, explicit map/fusion laws, canonical size/height
specializations, inorder, its length/map laws, and shape preservation. Payload,
source-summary and target-summary universes remain independent. There is no
new carrier, algebra record, order or inhabited-payload requirement.

`Applications/Trees/Cached.lean` keeps erasure, root reading, the smart node,
recursive validity and the independent structural fold separate. Its smart
node is valid exactly when its children are valid. Bottom-up annotation is
an ordinary fold, with separate validity, erasure and root-observation laws.

`Applications/Resources/TreeCache.lean` reuses the ordinary measured interface.
The named local tariff charges two actual root reads and one constructor entry,
plus the actual reached combine callback. The returned tree stores the callback
result. Value correctness requires only the reached-call equation; validity
additionally requires both child invariants. The exact count is callback+3,
and its bound only assumes a bound on that reached call. No subtree fold,
erasure pass or annotation pass occurs in this local execution.

`Examples/TreeCache.lean` supplies universal size/height readers, pair
projection fusion, the asymmetric size-4/height-3 fixture, existing ordered
sequence-summary composition with a noncommutative word, repeated and empty
labels, shape loss under inorder, the corrupted descendant boundary, and
actual measured size/height/append clients. The valid chain family obtains
local count n+4 from the existing recursive append, public annotation/read
laws, inorder length and canonical node count. Its local value is the next
annotated chain. Preparation of those cached inputs is explicitly separate.

`SquareApplications.lean` imports the example module, whose transitive imports
include every new module. The source/statement note is
`docs/research/fdsa-tree-cache.md`; the reconstruction map records this bounded
uncompiled support without closing any chapter obligation.

## Statement assessment and bounded checks

The implementation-side statement assessment in the source note covers the
full declaration groups, independent expected cases, actual public connections,
minimal assumptions and semantic/cost distinctions. Root did not change the
frozen expectations to fit an implementation result.

The two retained bounded contributors read the stable core/resource/example
sources and found no concrete semantic or pinned-API mismatch. Their report
is `binary-tree-cache-source-preflight.md`. It explicitly excludes final
review, compiler evidence, integration and documentation assessment. The four
formal source hashes there match this candidate. The source report preserves
the distinct source leftist zero-helper tariff and the unresolved literal
two-append timing adapter; neither is silently replaced by this local model.

Using the project's pinned Nix shell, root checked the exact initial base,
empty index, and that only the seven owned files changed. Both unstaged and
staged `git diff --check` passed before the commit, followed by a clean-status
check. These are Git/whitespace observations only. They do not check Lean
elaboration, source policy, full import coverage or proof axioms.

## Required next steps and preserved boundaries

No compiler, focused build, project checker, project hash helper, exhaustive
audit, final Standards review, final Spec review or candidate verification has
run for this unit. Do not run another compiler while old Chapter 1 gate
session 80227 is active. Preserve that gate's actual outcome first, then
validate and accept the repaired Chapter 1 candidate through its retained loop.

After the prerequisite and an explicitly recorded integration/base decision,
use the applicable isolated candidate checks, including focused core/examples,
complete build/guards/exhaustive audit, both independent axes and immediate
`--verify-candidate`. A correction or integration conflict creates a new
candidate requiring matching evidence. Preserve this draft's exact history.

This tree draft is not needed for the initial Chapter 2 foundation prefix;
its existence does not alter the retained smallest-integration plan or force
it into that candidate. Whole-fold resource execution, actual chapter-specific
traversals/balancing/search, raw maximum-cache representation and the existing
leftist adapter stay in their later source obligations. No chapter is advanced
or accepted by this handoff.

Checkpoint 0028 is intended to retain this committed source, its records and
all earlier refs/tickets. Its creation/upload receipt is recorded separately
after success. Ordinary durability checkpoints remain cache-free.
