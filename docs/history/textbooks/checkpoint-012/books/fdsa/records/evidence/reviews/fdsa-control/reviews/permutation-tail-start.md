# Conditional-tail draft: starting state

Recorded 2026-11-02 before repository source implementation for FDSA-XU03.

- Frozen requirements: `permutation-tail-requirements.md`, SHA-256
  `80323e579fe63419a10d7b26eb55f7ac540fea98a8a7c9c4efe36dce5f088b9c`.
- Worktree: `conaled-permutation-tail`.
- Branch: `work/fdsa-permutation-tail`.
- Starting HEAD: `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`.
- Index, tracked working tree and nonignored untracked status: clean.
- This is the unvalidated whole-order draft, based on the unvalidated
  minimum-law draft and Chapter 1 repair. No accepted dependency is claimed.
- Only `.lake/packages` points to the unchanged pinned dependency directory.
  No project build directory existed at capture and no compiler was started.

The API/source preflights and independent exact calculations are pinned in
the requirements. All preflight contributors have stopped editing. The
proposed event is `firstEvent Y a`; the generic head, tail and filtered-tail
contracts use existing HasLaw and ordinary conditioning. Actual global
permutation source-fiber and map specializations retain their separate
measurability requirements. Arbitrary histories, algorithm correspondence
and cost claims remain outside this bounded unit.

Proposed namespace: `Applications.Probability.PermutationTail`.
Agreed generic argument prefix: `positions hnd hcomplete S a ha hY` for
`head_mass_of_hasLaw` and `hasLaw_tail_cond_first`, followed by `T hT` for
`hasLaw_filter_tail_cond_first`. Ω, μ and Y are implicit in hY. Exact
remaining names and argument orders will be coordinated before source edits.

Root owns the main example module, source-use documentation, public imports,
tracker and commits. The architecture contributor will own only the new
core module; the source contributor will own only the boundary module after
those assignments are issued. All work stays inside the existing book
implementation workflow. Final review remains pending matching validation.
The active old Chapter 1 checkout and gate remain unchanged. No additional
compiler may run while that gate is active.

## Coordinated API and file ownership before implementation

After checkpoint 0019 was saved, and before source edits, root and the
architecture contributor agreed these source interfaces (not elaborated
signatures):

- `firstEvent Y a`, with no equality or measurable instances.
- `firstEvent_inter_tail Y a xs`.
- `cons_mem_orders positions hnd S a haPositions ha xs`.
- `tail_restrictedOrder_eq positions hnd S a π hfirst`.
- `filter_tail_restrictedOrder_eq positions hnd S a π hfirst T hT`.
- `head_mass_of_hasLaw positions hnd hcomplete S a ha hY`.
- `hasLaw_tail_cond_first positions hnd hcomplete S a ha hY`.
- `hasLaw_filter_tail_cond_first positions hnd hcomplete S a ha hY T hT`.
- `uniformOn_firstEvent positions hnd hcomplete S a ha`.
- `cond_tail_eq positions hnd hcomplete S a ha xs`.
- `map_tail_cond_first positions hnd hcomplete S a ha`.
- `map_restrictedOrder_cond_first positions hnd hcomplete S a ha T hT`.
- `cond_uniformOn_firstEvent positions hcomplete S a`.
- `firstEvent_restrictedOrder_of_not_mem positions S a ha` for a∉S.
- `cond_firstEvent_restrictedOrder_of_not_mem positions S a ha μ` for a∉S.

Here hnd is positions.Nodup; hcomplete enumerates every index; haPositions
is a∈positions; hfirst is membership in the actual first event; and hT is
T⊆S.erase a. Positive laws use ha:a∈S; the last two helpers explicitly use
nonmembership instead. Source scalar laws use only permutation sample
measurability; the map and generic HasLaw contracts add List measurable
singletons. The conditional-uniform identity needs neither hnd nor ha.

Architecture owns only `Applications/Probability/PermutationTail.lean`.
The source contributor owns only `Examples/PermutationTailBoundary.lean`,
which may import previous examples but not the new main module.
Root owns `Examples/PermutationTail.lean`, docs, public imports and commits.
The new main example imports the boundary module. All contributors are
released to write their assigned uncompiled source only after this record.
