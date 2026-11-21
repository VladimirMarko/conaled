# Interval-list sets: unqualified Chapter 6 preparation

CTB-25, FDSA-6-20 to FDSA-6-33 remain open. This note preserves the useful surviving
paper preparation for Exercise 6.1 and one separate FDSA-6-60 map-interface
observation. It adds no implementation, measured result, source qualification,
or receiving acceptance. The [Chapter 6 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter06-obligations.md)
owns the complete 74-row chapter scope and exact requirements. CTB-78 receiving
integration and validation precede resumed book formalization.

## Source and recovery limits

The immediate source is the conversation-recovery draft `future-preparation.md`
secured in checkpoint058, 24,521 bytes, SHA256
`57583f5331151320ded976122dbbbee8339517bf8014d7f0d69eeb371f30803c`.
This was a new curation after an environment loss, not recovered original proof
files. The independent interval-list author reported a 31,540-byte, 399-line
paper, SHA256
`1433fc9c6b9f5ec04e16dbb6559f46a930e7c63e8c4c365b7a41af83f065a18d`,
and a 3,791-byte companion record, SHA256
`5c062d46c15263d507679a9097e1994680a3445161d3f4ac956120f927f5e0cc`.
Their full contents, branch tables, tariffs and sharp witnesses were unavailable
to that recovery. Those identities do not make the missing bodies available.

The child credited its parent's authenticated PDF and companion reading; it did
not inspect those binaries independently or the interrupted interval-tree code.
The parent reported Chapter 6, printed pp.77–83 / PDF pp.83–89, and the sources
`Map_Specs.thy`, `Tree_Map.thy` and `AList_Upd_Del.thy`. Only partial theory hashes
survived the relay, so they cannot serve as complete integrity identities. The
complete planned 74-row reuse map and parent reading log were never materialized;
the separately reported map-case paper was not recovered either. No Lean,
prototype evaluator, case enumerator or build ran for the retained interval-list
paper. This curation claims no new primary-source inspection.

## Representation and single-point operations

Use a list of inclusive natural-number intervals. The minimal validity invariant
requires nonempty intervals, ascending order and no overlap. It **permits
adjacency**, such as `(0,0)` followed by `(1,1)`. Requiring coalesced maximal runs
would be an additional design choice with additional preservation obligations.
Semantic equality of represented sets does not establish representation validity.

The planned single-point development covers all seven Set laws and early exit,
including zero and singleton boundaries, interior deletion, both input
orientations, and nested or chained overlap cases. Do not substitute repeated
point insertion/deletion for the required binary stream algorithms. Natural
predecessor expressions require guards proving positivity and a nonempty
residual interval; zero is a mathematical boundary, not an implicit convention.

## Union: keep an active interval separate from both valid suffixes

A tempting recursive transformation invalidates its own stream invariant.
For valid inputs

```
xs = [(0,0),(2,2)]
ys = [(0,3)]
```

merging the heads and putting the result back into the first stream produces
`[(0,3),(2,2)]`, whose intervals overlap. A proof cannot recursively assume that
both transformed streams remain valid.

The retained repair uses **two untouched valid suffixes and a separate active
interval**. The active interval may overlap either suffix, and its lower endpoint
bounds the remaining lower endpoints. The invariant must support three actions:
absorb an overlapping next interval; emit the active interval when future overlap
is impossible; or return an unaffected suffix directly. This keeps the invalid
merged head out of the hypothesis that each original suffix is valid.

The exact original branch table is unavailable. Reconstruct and prove the actual
algorithm and its invariant before freezing implementation expectations. The
counterexample and invariant above are useful preparation, not a completed union
correctness or termination proof.

## Difference: targets minus cutters and a cursor-count measure

The specified call is `del cutters targets`, representing **targets minus
cutters**. Preserve that orientation in any adapter. The retained paper partition
has five kinds of recursive transition:

| Relative endpoint situation | Required progress |
| --- | --- |
| Cutter lies wholly below the current target | Drop that cutter. |
| Target lies wholly below the current cutter | Emit that target. |
| Cutter ends before the target | Consume the cutter and retain the shortened target. |
| Target ends before the cutter | Consume the target and retain the longer cutter. |
| High endpoints agree | Consume both. |

For the full guarded branch system, each recursive transition decreases
`length cutters + length targets`, including branches retaining one residual
interval. Residual endpoints and emitted pieces need their own validity and
set-difference equations. The table identifies progress obligations; it does not
supply missing guards, overlap subcases, or a ready-to-run definition.

## Proposed cost and output bounds

The surviving paper reports bounds of at most `n + m + 1` calls and at most
`n + m` emitted intervals for its proposed union and difference branch systems,
under an explicitly stated tariff that is **not present in the surviving relay**.
These remain unqualified paper claims. Later work must instrument the actual
chosen recursion, state the tariff and prove its constants. Call count is not a
substitute for all selected operation costs, and no bit-time result for arbitrary
natural endpoints follows from a scalar endpoint tariff.

The missing original paper reportedly included width-independent families and a
sharp difference output-size family. Its precise witnesses and tables are not
recoverable from this note and must be transparently rederived or independently
recovered. Preserve the canonical linear-in-interval-count goal; never obtain it
by enumerating all represented natural numbers.

## Separate FDSA-6-60 map-interface observation

This observation concerns ordered-map list update, not the interval-list
algorithm. Its current owner is
[`Applications/Search/OrderedMap/Enumeration.lean`](../../Applications/Search/OrderedMap/Enumeration.lean).
The recovered preparation identified the unused right-separator premise in
`kvsInsert_split`. The current integration exposes its actual weaker result as
`kvsInsert_split_of_left`: only the left keys must lie below the pivot; the right
suffix is arbitrary. The source-facing `kvsInsert_split` keeps its original
signature as a wrapper, and existing enumeration correctness uses the weaker
law. [SearchTrees](../../Examples/SearchTrees.lean) includes an arbitrary-suffix
client, an unsorted duplicate-bearing witness that violates the old extra premise,
and a counterexample showing why the left separator is still needed.

The surviving Chapter 6 preparation says FDSA-6-60 permits an arbitrary right
suffix. Reconcile its exact canonical statement and remaining exercise proof
with this shared theorem when formalizing that row. This interface improvement
does not by itself qualify FDSA-6-60 or complete its chapter; receiving compilation
and review remain pending.

[`SourceModel.listObserve_kvsInsert`](../../Applications/Search/OrderedMap/SourceModel.lean)
already supplies unconditional observation of ordered-list update. Historical
insertion-only gap descriptions therefore cannot define the current scope.
Existing keyed deletion, strict-list composition, AbstractSet delete laws and
mixed traces must be inventoried before replacements are designed. The old
preparation's remaining general role schema, modify translations and composition
work were prospective claims requiring current-source review; this note does not
claim a complete Chapter 6 reuse audit or classify any of those rows as done.

## Next action and qualification

Recover or rederive the missing complete branches, cases and tariff, then compare
them with the canonical FDSA-6-20 to FDSA-6-33 requirements and current shared interfaces.
Implement and prove actual operations, all required laws, early termination,
validity and measured linear bounds. Keep the FDSA-6-60 weakening under its map
owner. None of the retained paper work closes a canonical row.
