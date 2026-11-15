# FDSA-XU05 starting state and coordination

Recorded 2026-11-02 before Lean source edits.

## Clean baseline

- Checkout: `/workspace/scratch/845aa1048b05/conaled-permutation-joint`.
- Branch: `work/fdsa-permutation-joint`.
- HEAD/base: `11923e9ffd17246b6f22c5594002a1ba0434e43c`.
- The new branch and worktree were created from that exact committed draft
  through the required pinned Nix shell. Existing branch/path checks refused
  accidental reuse. `git status --porcelain=v1` returned the empty string
  after setup: no staged, unstaged or nonignored untracked changes.
- `.lake/packages` points only to the existing unchanged pinned dependency
  packages. `.lake/build` did not exist; project outputs are separate.
- No compiler, project hash helper or gate ran in this checkout. No source
  or configuration in the active Chapter 1 checkout was changed.
- There are no unrelated files in this new checkout to exclude. The main
  checkout's unrelated historical ZIP remains preserved and excluded only
  from the authorized task recovery payload, as previously recorded.

## Frozen inputs

Requirements: `permutation-joint-requirements.md`, 14,845 bytes, SHA-256
`a80952af26c830231070feb9305f7c678277349c95861b39826edc9297486325`.
The exact source/API preflight and independent-calculation fingerprints are
recorded there. Root read both completed preflights and checked the named
calculation results before freezing this scope. No prior requirement,
inventory or candidate commit was rewritten.

The core extends the existing relative-order module and reuses its private
extension/relabeling helpers. The final three public calls are:

```lean
uniformOn_restrictedOrder_pair_eq positions hnd hcomplete A B hAB xs ys
map_restrictedOrder_pair_uniformOn positions hnd hcomplete A B hAB
hasLaw_filter_pair positions hnd hcomplete S hY A B hAS hBS hAB
```

The third is the frozen shorter name for the preflight suggestion. There
is no alias or independent framework. The scalar statement uses equality
of actual pairs; component conjunctions are equivalent client syntax.
The old public interfaces and all prior cases are retained unchanged.

## Source ownership

After the pre-code checkpoint is saved, root releases non-overlapping work:

- `/root/architecture`: only
  `Applications/Probability/PermutationOrder.lean`, its added imports/header
  and new joint-law proof section. Preserve prior public statements; record
  any necessary prior private-proof edit. Do not import PermutationTail.
- `/root/book_inventory`: only `Examples/PermutationJointBoundary.lean`,
  including unequal/proper-union, empty/full, Empty generic endpoint and
  actual overlap counterexample. Do not import the new main module.
- Root: `Examples/PermutationJoint.lean`, the public root import, the new
  source-use document and reconstruction-map section, and local control
  coordination. Main examples cover Fin4 joint/marginal/IndepFun and the
  actual Fin5 conditional-tail composition and projection bridge.
- A separate contributor can assess the completed stopped draft read-only;
  that is not a final Standards/Spec gate.

Contributors read the complete frozen requirements and this start record,
coordinate the exact public calls, stop before handing source back, and
report file identities plus limitations. They do not run compilers, project
hash helpers, Git mutations or gate/cache/configuration actions while the
Chapter 1 gate is active. No control files are delegated to source authors.

## Acceptance boundary

This unit and all its predecessor shared drafts are unvalidated. Chapter 1
is still active with no accepted chapter or appendix. The old Chapter 1
candidate check continues unchanged; a pass there cannot validate the
repair or this extension. The source-only deliverable retains all applicable
focused/full build, integrity, audit, independent review and immediate
candidate-verification gates. Root must commit additional-worktree source
before a durability checkpoint, because patch capture covers only main.
