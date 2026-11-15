# Shared binary-tree cache: preimplementation handoff

Recorded 2026-11-02, before source edits.

- Local scope: FDSA-XT01, requirements version 1.
- Frozen requirements SHA-256:
  `81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce`.
- Fixed initial base/head:
  `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Branch: `work/fdsa-tree-cache`.
- Worktree: `/workspace/scratch/845aa1048b05/conaled-tree-cache`.
- Machine-readable baseline: `binary-tree-cache-start.json`, SHA-256
  `1782fab514df5533469afc8769843d7f5cb9813243a33fda8a8da7c2c08dfb69`.

Root verified the repaired-base checkout's exact head and clean index/working
tree, confirmed the new branch and destination were absent, then created the
isolated worktree using the pinned Nix shell's Git. The new checkout has the
same exact head and a clean index/working tree. There are no included unrelated
edits. Only the pinned dependency directory is linked; project outputs remain
worktree-local. The root AGENTS applies, and no nested AGENTS governs the
proposed Applications, Examples or research-document paths.

Root owns the source implementation. The architecture and source contributors
have stopped their permitted control-report writes. No one may edit the active
Chapter 1 validation checkout or run another compiler/checker/project hash
helper while its old-candidate gate continues. This branch contains no tree
implementation at this handoff.

This is a cross-cutting draft on an unaccepted repair, not an accepted chapter
base. All repair findings and dependencies remain open. The new unit cannot
be integrated or accepted until repaired Chapter 1 is accepted and its own
matching-candidate validation and both independent final review axes pass.
Preserve the full requirements, original review base and every later candidate.

Checkpoint 0027 is intended to preserve this pre-code state and the new tree
preflights, together with the post-0026 treap assessment and prior records.
The receipt is recorded only after creation and successful upload.
