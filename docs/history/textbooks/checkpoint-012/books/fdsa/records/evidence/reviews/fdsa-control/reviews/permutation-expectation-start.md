# Preceding-count draft: starting state

Recorded 2026-11-02 before source implementation for FDSA-XU04.

- Requirements: `permutation-expectation-requirements.md`, SHA-256
  `926fddbeb2d20b45842416b90ba96c78dbeaa84064d5d135cf3bb5b2d620624a`.
- Worktree: `conaled-permutation-expectation`.
- Branch: `work/fdsa-permutation-expectation`.
- Starting HEAD: `a0597381f02eddd074ee96cabaa974f2062285f8`.
- Index, tracked worktree and nonignored untracked status: clean.
- This is the unvalidated conditional-tail draft; its predecessor chain,
  including the Chapter 1 repair, is also unaccepted.
- Only `.lake/packages` points to the unchanged pinned dependencies. No
  project build directory existed at this record and no compiler was started.

The API/source notes and independent expectation files are pinned in the
requirements. All preflight writers have stopped. The core depends on
the actual XU01 minimum law and ordinary count/integration APIs; only the
conditional-placement example needs XU02/XU03. The global mean is not
claimed for an arbitrary relative-order HasLaw or adaptive subset.

## Coordinated source interfaces and ownership

The API preflight proposed, and the requirements now approve, namespace
`Applications.Probability.PermutationExpectation` and these explicit calls:

- `beforeCount priority S π`.
- `beforeCount_empty priority π`.
- `beforeCount_le priority S π`.
- `lintegral_beforeCount_uniformOn priority hinj S`.
- `integral_beforeCount_uniformOn priority hinj S`.
- `beforeCount_rank_eq rank S hS π`.
- `integral_firstPosition_uniformOn rank S hS`.

The rank bridge gives the actual finite-image minimum's zero-based value;
the final integral displays its one-based position. hS is S.Nonempty and
rank is an equivalence to Fin U. Other required assumptions and the exact
casts are frozen in the requirements. These are coordinated source-level
interfaces, not elaborated declarations.

Architecture will own only `Applications/Probability/PermutationExpectation.lean`.
The source contributor will own only `Examples/PermutationExpectationBoundary.lean`
for empty/singleton/full, ties, adaptive-singleton and actual conditional-
placement cases. It may use preceding core/example modules but must not
import the new main example. Root owns `Examples/PermutationExpectation.lean`,
including the main means, nonidentity rank and actual numeric-minimum bridge,
plus documentation, public imports, local tracking and commits. The main
example will import the boundary module.

No implementation is released before the pre-code recovery checkpoint is
saved. Thereafter all contributors stay in the existing book implementation
loop, write only their assigned source files, and keep compilation/final
review pending. The old Chapter 1 candidate and gate remain unchanged; no
additional compiler, project hash helper or cache/configuration edit is
permitted while it runs.
