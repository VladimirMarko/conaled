# Permutation-order draft: starting state

Recorded 2026-11-02 before repository source implementation for FDSA-XU02.

- Frozen requirements: `permutation-order-requirements.md`, SHA-256
  `f473f593bf4a7ef75dcf2f3163440db6fe187b3b9983f87254d2ddfa8191982d`.
- Worktree: `conaled-permutation-order`.
- Branch: `work/fdsa-permutation-order`.
- Starting HEAD: `ff3dd88082c6283df40bcd86a4363841a0360b12`.
- Index, tracked worktree and nonignored untracked status: clean.
- This is the unvalidated minimum-law draft, itself based on the unvalidated
  Chapter 1 repair. No accepted dependency is claimed.
- Only `.lake/packages` points to the unchanged pinned dependency directory.
  Project output paths are separate. No compiler was started.

The bounded API/source preflights and independent exact calculations are
pinned in the requirements. The intended operation is the ordinary inverse
map followed by stable filtering. Its pointwise mapped-sublist and
filter-composition laws accompany the whole-output probability and existing
Measure.map meaning. No conditional-history, expected-position or algorithm
cost claim is included.

Proposed namespace: `Applications.Probability.PermutationOrder`.
Proposed operation: `restrictedOrder positions S π`.
Proposed law names: `uniformOn_restrictedOrder_eq` and
`map_restrictedOrder_uniformOn`. Complete public argument orders are being
coordinated before code. These proposals are not elaborated signatures.

Root will own the main Fin 4 examples, source-use documentation, public
integration and commits. The architecture contributor will own only the
new core module. A separate contributor may own the boundary example module
after its file assignment is recorded. All remain in the existing book
implementation workflow, with final review pending matching validation.
The active old Chapter 1 checkout and gate remain unchanged. No additional
compiler may run under these assignments while that gate is active.

## Coordinated API and final file ownership before implementation

The contributor confirmed these names and explicit argument orders after
checkpoint 0017 was captured, before editing source:

- `restrictedOrder positions S π`; `orders positions S`.
- `mem_restrictedOrder positions S π a`.
- `mem_restrictedOrder_of_complete positions hcomplete S π a`.
- `restrictedOrder_nodup positions hnd S π`.
- `restrictedOrder_toFinset positions hcomplete S π`.
- `restrictedOrder_length positions hnd hcomplete S π`.
- `restrictedOrder_perm positions hnd hcomplete S π`.
- `map_restrictedOrder_sublist positions S π`.
- `filter_restrictedOrder positions S T π`.
- `filter_restrictedOrder_of_subset positions S T π hTS`.
- `mem_orders positions S xs`; `orders_nonempty positions S`.
- `restrictedOrder_mem_orders positions hnd hcomplete S π`.
- `orders_card positions hnd hcomplete S`.
- `uniformOn_restrictedOrder_eq positions hnd hcomplete S xs`.
- `map_restrictedOrder_uniformOn positions hnd hcomplete S`.

Here `hnd` is positions.Nodup and `hcomplete` is membership of every index
in positions. The fiber formula uses membership in `orders positions S`
and reciprocal ENNReal factorial S.card. Its source-event theorem has only
sample measurability; the map theorem additionally has List I measurable
singletons. These are agreed source interfaces, not elaborated signatures.

Architecture owns only `Applications/Probability/PermutationOrder.lean`.
The source contributor owns only `Examples/PermutationOrderBoundary.lean`
for the frozen empty, cycle, numeric-priority and invalid-enumeration cases.
Root owns `Examples/PermutationOrder.lean`, docs, public imports and commits.
No source implementation existed in checkpoint 0017.
