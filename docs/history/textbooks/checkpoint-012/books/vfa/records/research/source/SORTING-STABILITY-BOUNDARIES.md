# Shared sorting observations and source recurrence boundaries

Read-only planning, 2026-11-02. No later chapter algorithm has been implemented
or compiled here. The tagged calculations below are hand unfoldings of the
source recurrences after the explicitly described key generalization; their
future Lean examples remain obligations. No chapter acceptance follows.

## Pinned evidence

VFA 2.1 sources under `reference/vfa/vfa/`:

| Source | SHA-256 | Relevant source lines |
| --- | --- | --- |
| Sort.v | `aeaf646d3b7e4dd88cb5d6dba9d35ae5714e5451c154d90de499bb09a32a7d33` | insert 30; tail-first sort 36; ordinary sorting contract 157 |
| Selection.v | `ff343099ae0fd551648a8fa2bf0adfe32bf5fb158389cee211ff8d1b32c28e11` | select 41–50; fuelled selsort 77–84; selection_sort 102–103; contract 126 |
| Merge.v | `090c5afc3a95750336b8b57ed2169b8d77c790266f231bf096be55761c20378b` | alternating split 47–54; left-tie merge 209–217; mergesort 358–364 |

Conaled was inspected at candidate `777bab9b2510deab54603c3df267e5c134a3e1e0`:
`Applications/Sorting/{Stable,Merge,Sort,SourceMerge}.lean`. Mathlib is pinned
to `56a005855ea17e0b0958f73ec801ae140b0a1679`; the relevant library source is
`.lake/packages/mathlib/Mathlib/Data/List/Sort.lean`.

## Three observations that must stay separate

`KeySorted key ys` observes pairwise key order. `ys.Perm xs` preserves records
with multiplicity. `Stable key xs ys` additionally requires each equal-key
filtered list of records to retain its original order. `StableSort` packages
these three fields; ordinary VFA sorting contracts require only permutation
and sortedness, in input-to-output permutation orientation.

The source Sort, Selection and Merge algorithms sort natural numbers. For
reuse on records, explicitly replace each source comparison by key comparison
and preserve all source branches and reconstruction order. Different records
with equal keys then reveal behavior that erasing them to Nat values hides.
Do not attribute a tagged-record claim to the source's original Nat type.

## Insertion: source tail-first recursion is material

The source sorts the tail before inserting the head, inserting before equal
keys. After a recurrence bridge, existing `insertionOn_spec` establishes the
stronger stable-record contract. `sortOn_eq_insertionOn` then provides equality
with conaled's stable merge sort under its stated key-order assumptions.
Replacing the right fold by a left fold with the same left-tie insertion would
reverse an all-equal two-record input; it is not the same source recurrence.

## Selection: an equal comparison does not ensure stable sorting

Let A = (2, "a"), B = (2, "b"), C = (1, "c"), comparing first components.
Unfolding the exact source select recurrence gives:

| Call | Branch and result |
| --- | --- |
| select C [] | (C, []) |
| select A [C] | false branch because 2 > 1; result (C, [A]) |
| select A [B, C] | true first branch because 2 ≤ 2; prepend B to the returned remainder, obtaining (C, [B, A]) |
| selsort [A, B, C] 3 | C followed by sorting [B, A], hence [C, B, A] |

The key-2 filtered output is [B, A], while the input observation is [A, B].
Thus the intended record generalization cannot satisfy `StableSort` in general.
Its Nat erasure [1,2,2] remains a correct ordinary sorting output. Retain this
as a future negative stability case alongside the source fuel examples and
the positive permutation/sortedness cases. The example does not refute the
separate fixed-point property on already key-sorted inputs; that property
needs its own recurrence proof.

## Alternating merge sort: stability, fixed points and idempotence

Take three distinct records A, B, C, all with key 0. Source split gives
([A,C],[B]). Sorting the left pair preserves [A,C], and left-tie merge then
returns [A,C,B]. The original equal-key observation [A,B,C] has changed even
though the input already satisfied `KeySorted`.

Applying the same recurrence to [A,C,B] splits it into ([A,B],[C]) and returns
[A,B,C]. Therefore the proposed tagged operation has a two-cycle on this case:
it is neither fixed on every key-sorted input nor idempotent in general.
All three Nat keys are identical, so Nat erasure conceals both differences.
Future Merge examples must check these precise tagged calculations in Lean.

Existing `mergeBy_stable` and `mergeBy_spec` establish stability relative to
the concatenation of the two sorted input blocks. For alternating split that
concatenation is [A,C,B], not the original [A,B,C]. Those correct library
theorems cannot supply the missing source-input stability premise. Likewise,
`sourceMerge_eq_merge` proves the merge primitive's recurrence bridge; it does
not identify the entire source mergesort with the standard contiguous split.

## Lawful reuse without strengthening the source claims

Keep ordinary permutation and `KeySorted` conclusions for generic Selection
and alternating Merge. Use `StableSort` only where its additional field has
actually been proved. Do not use `StableSort.unique`, `sortOn_sorted_fixed`,
or stable-sort idempotence to infer false tagged source equalities.

For Nat outputs, sortedness plus permutation can still prove agreement with
the standard sort: pinned Mathlib's `List.Perm.eq_of_pairwise'` at Sort.lean
303–305 requires antisymmetry of the element relation. It also supports a
future equality after mapping arbitrary record outputs to ordered keys.
Antisymmetry of key order does not imply antisymmetry of its pullback to
distinct equal-key records. An equality of key lists is a weaker observation,
not an equality of full outputs or a resource/algorithm identity claim.

These are reuse constraints for chapters #1003, #1006 and #1007. The shared
specification draft and existing sorting interfaces suffice; no new sorter
hierarchy is proposed. Keep chapter-order implementation and all gates intact.
