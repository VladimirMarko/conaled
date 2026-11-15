# Conaled reuse reconnaissance for VFA

This preserves the earlier read-only survey and its important limitations.
It is not a fresh build, a final architecture review, or a declaration-level
claim that any VFA chapter has already been covered. Initial checkout HEAD:
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

Repository guidance read during reconnaissance: `AGENTS.md`,
`docs/agents/architectural-quality.md`, `docs/agents/domain.md`, `GLOSSARY.md`,
`docs/adr/README.md`, ADR 0001, and the README's architecture, development,
build/audit, and proof/execution-boundary sections. Local tickets replace GitHub
tracker writes under the user's instruction.

## Directly inspected sorting evidence

`Applications/Sorting/Sort.lean` already supplies generic key-based sorting.
Operations `sortBy`, `sortOn`, and `insertionOn` are separated from correctness
and stability contracts. Reusable results include:

- `sortBy_perm`, with no comparator-order assumptions.
- `sortBy_sorted_compatible_on`, requiring comparator compatibility only on
  the input domain, and its global specialization.
- `sortOn_correct`, `sortOn_stable`, and `sortOn_spec`.
- `sortOn_sorted_fixed` and `insertionOn_spec`.
- `sortOn_eq_insertionOn`, via the independent stable-sort specification.
- `mergeBy_eq_sortOn` and `sortOn_map`, which express composition and transport.

`Examples/StableSorting.lean` directly exercises these interfaces with signed
keys and string payloads. It checks stability among equal keys, empty and
already-sorted inputs, merging sorted blocks, successive payload maps, and a
comparator whose contract holds only on nonnegative keys. Its negative example
shows that sortedness plus permutation does not imply stability.

Relevant neighboring modules are `Stable.lean`, `Merge.lean`, and
`SourceMerge.lean`. Existing definitions distinguish `KeySorted`, equal-key
observation `Stable`, and `StableSort`. Source-merge bridges and the stable-sort
uniqueness/map theorems are reusable seams, not reasons to assume source VFA
merge sort is stable. VFA's alternating split creates a material difference.

## Directly inspected queue evidence

`Applications/Search/LeftistQueue.lean` contains an actual leftist heap with
cached ranks, structural size, occurrence-list observation, and distinct
rank/heap invariants. It retains the smart constructor, right-spine merge,
root removal and rebuilding rather than defining operations by sorting a list.

Inspected results include `fork_entries`, `rank_paths`, `rank_size`, `rank_log`,
`combineQ_entries`, `combineQ_ranked`, `combineQ_heap`, `combineQ_valid`,
`insertQ_entries`, `insertQ_valid`, `deleteQ_spec`, `makeQ_spec`,
`toListQ_perm`, and `toListQ_sorted`. These cover finite semantic and structural
contracts. A rank logarithm is not automatically a measured wall-clock bound.

`Applications/Search/PrioritySearchQueue.lean` uses a keyed uniqueness invariant,
retains a best-priority representative when keys coincide, and supplies a
leftmost-minimum removal primitive with permutation and minimality proofs.
Its `keyed` value implements `PriorityInterface.Queue`. These observations
differ from VFA's occurrence-preserving maximum-priority queue interface.
Reusing them needs an explicit adapter or a separate suitable realization;
key deduplication cannot be hidden by a generic queue name.

## Existing survey and shared interfaces to consult

The repository's `docs/research/functional-data-structures.md` and
`docs/research/data-structure-architecture.md` were read as existing research
evidence. Their conclusions distinguish actual accepted code from proposed
toolkits and historical source material. In particular, the VFA table interface
has natural-number keys and a default-valued total observation, not optional
finite-map lookup.

The survey points to the following reusable families. These pointers do not
claim a new exhaustive re-audit of every listed implementation:

| Family | Existing seam | Relevant boundary |
|---|---|---|
| Representation and relational refinement | `Squares.Rep`/`Square`, `Relational.RelRep`/`RelSquare` | Exact equality and a chosen relational observation preserve different information; neither proves cost improvement alone. |
| Finite list fusion | `SquareKit.ListFusion` reachable fold/scan laws | Reuse under explicit local commuting laws; no runtime allocation or lazy/infinite semantics follows automatically. |
| Measured workloads | `Applications.Resources.Measured` and `Workload` | Value and observation are separate; `run_append`, invariant propagation and value fusion compose actual state trajectories. |
| Potential accounting | `Applications.Resources.Potential` | `run_potential`, exact/constant-charge variants and initial-potential boundaries apply to specified trajectories, not arbitrary reuse of persistent versions. |
| Existing sequence representations | Symmetric and random-access sequence families | Ordered observations, canonicality, cached-rank correctness, and representation validity are separate obligations. |
| Optimization transport | Existing minimizer/Pareto/admissibility interfaces | Semantics alone does not select a cheaper representation; objectives, workload, coverage and cost laws are explicit. |

`docs/research/data-structure-target-capabilities.md` and
`docs/research/data-structure-resource-contracts.md` provide the current broader
toolkit direction. Their citations and earlier acceptance records are useful
context, but no historical validation record substitutes for the current
chapter's applicable build/audit and independent reviews.

## Consequences for the new work

Preserve each VFA source algorithm or prove a clearly stated bridge to an
existing implementation. Use generic local contracts where their hypotheses
fit, with checked natural-number/source specializations. Keep operations,
observations, invariants, and laws separate, and demonstrate composition with
existing consumers. Do not equate a related pre-existing data structure with
chapter completion, or introduce a natural-number-only parallel abstraction
when the existing generic one provides the needed contract.
