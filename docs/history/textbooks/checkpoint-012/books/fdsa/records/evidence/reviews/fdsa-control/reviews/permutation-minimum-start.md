# Permutation-minimum draft: starting state

Recorded 2026-11-02 before any repository implementation for FDSA-XU01.

- Frozen requirements: `permutation-minimum-requirements.md`, SHA-256
  `59e2ff6ff66dd39b6151a42b501bcc22e86eb593a9b854b532f97bc45fdd7686`.
- Worktree: `conaled-permutation-minimum`.
- Branch: `work/fdsa-permutation-minimum`.
- Starting HEAD: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Index, tracked worktree and nonignored untracked status: clean.
- This is the unvalidated Chapter 1 repair, not an accepted base.
- Only `.lake/packages` points to the existing pinned dependency directory.
  The project output directory is separate; no compiler was started.

The main theorem is the fixed-subset minimum probability under one uniform
permutation. The event's membership conjunct, injective priorities and the
single common law are explicit. The expected preceding count and full
relative-order restriction are not part of the frozen unit. The requirements
preserve their distinct future semantic/probabilistic obligations.

Root owns the connected examples, documentation, public imports and commits.
The architecture contributor will own only
`Applications/Probability/PermutationMinimum.lean`, with proposed namespace
`Applications.Probability.PermutationMinimum`, event `minimumEvent`, and
theorem `uniformOn_minimumEvent priority hinj S a ha`.
These are coordination names, not inspected elaborated signatures.

The independent calculations exhaustively checked 50,363 permutation/subset
pairs for universe sizes zero through six, using exact rational arithmetic.
They preserve the expected overlap masses 1/2, 1/2 and 1/3, plus membership,
tie and empty boundaries. They supply no kernel-validation or acceptance
credit. The existing old Chapter 1 check remains untouched; no additional
compiler may run concurrently under this assignment.

After the starting-state capture and checkpoint 0015, root assigned the
separate `Examples/PermutationMinimumBoundary.lean` file to the source
contributor for the empty-index, outsider and tied-priority cases. Root
retains the main overlapping-subset/Int example, integration and commits.
This division does not change the frozen mathematical scope.
