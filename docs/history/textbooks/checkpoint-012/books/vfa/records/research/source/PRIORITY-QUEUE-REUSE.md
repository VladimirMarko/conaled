# VFA maximum priority queues: bounded reuse investigation

Date: 2026-11-02. Read-only investigation; no adapter, algorithm, or theorem was
implemented or compiled. No chapter acceptance follows from this note.
Repository inspected: `conaled` commit `777bab9b2510deab54603c3df267e5c134a3e1e0`.
Pins: Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries
`66e469188fe07963e5cf666c7d4433f45b8131c5`; Lean 4.35.0.
VFA 2.1 source paths are under `reference/vfa/vfa/`:

| Source | SHA-256 |
| --- | --- |
| `Priqueue.v` | `e4dc740bf2c3f338dedae3e6544a8d94d58fd80f810472610122b9ccc4866b9d` |
| `Binom.v` | `f73f18cac4c3a6a38a0e83d4194429eb7ab684ee68068a88025610a13d5c31ed` |

Read `AGENTS.md`, architectural-quality/domain guidance, `GLOSSARY.md`, and
ADRs 0001/0002: reuse operations/observations/laws separately; preserve source
relations and executable recursions; introduce no universal container hierarchy.
Project paths below are relative to `conaled`; dependency paths beginning
`Mathlib/` or `Batteries/` are under its corresponding `.lake/packages/` checkout.

## Source contracts that must survive

| Source location | Required observation or distinction |
| --- | --- |
| `Priqueue.v:66–101`, `PRIQUEUE` | Nat keys; empty, single insertion, maximum deletion and native merge; `priq` guards source laws. `can_relate` gives an abstraction witness and `abs_perm` makes witnesses unique up to permutation. Source signature axioms must become proved law fields. |
| `Priqueue.v:85–100` | None iff the abstract list is empty; successful deletion preserves validity and removes exactly one occurrence, with every residual key ≤ returned key; merge preserves the concatenated occurrences. |
| `Priqueue.v:129–157,170–199` | The actual list realization uses maximum-select recursion, cons insertion, append merge, trivial validity, and an identity abstraction relation. That relation is not permutation-closed merely because the interface is occurrence-sensitive. |
| `Binom.v:48–136,143–170,228–254` | Retain smash/carry/join/unzip/find/delete recursions and their malformed-input branches, rank-indexed validity, and permutation-closed tree/forest abstraction. `priqueue_elems` is an exercise placeholder, not an existing proved implementation. |

## Smallest proposed lawful adapter

Reuse `Search.PriorityInterface.ExactQueue Unit (OrderDual Nat)`; encode a key
as `((), OrderDual.toDual k)` and decode its priority with `OrderDual.ofDual`.
Unit avoids a redundant payload-key/priority consistency invariant. The dual
turns minimum priority into maximum Nat without negation or a bounded-key trick.
`Mathlib/Order/OrderDual.lean:51–98,136–166` supplies dual order/decisions,
`toDual`/`ofDual`, and `toDual_le_toDual`; `Mathlib/Order/Defs/LinearOrder.lean:88`
supplies the standard-order instance used by the existing queue realizations.
This is a proposed instantiation, not an elaborated adapter in this task.

**Validity boundary:** `ExactLaws.add_exact` and `remove_none` quantify over
all carriers (`Applications/Search/ExactPriority.lean:12–20`), whereas the
source laws require `priq`. For Binom use carrier `{q // priq q}` and lift the
unchanged source operations using their closure proofs; `Valid := True` then
suffices. Do not claim exact insertion on malformed raw trees: smash's fallback
can discard their contents. Batch `add` can fold the proved source insertion.

Supply a concrete finite observation `observe q` with `Abs q (observe q)`;
`abs_perm` transports every other abstraction witness to it. Keep the source
relation too, especially the list identity relation. Encode observations into
Unit/dual-priority entries. Source deletion's residual bound plus reflexivity
and permutation yields ExactLaws' bound on every original entry, including
the returned entry. Preserve ties as occurrences; neither contract adds stability.

`Operations` has no meld (`PriorityInterface.lean:18–22`). Keep the actual
source `merge` and separately prove validity closure and
`entries (merge p q) ~ entries p ++ entries q` on valid inputs. These two laws
need no new hierarchy. Replacing native merge with insertion of decoded entries
would change its algorithm and costs; semantic observations need not be efficient.

## Existing local proofs and standard facts

| Verified declaration path | Existing result and appropriate reuse |
| --- | --- |
| `Applications/Search/ExactPriority.lean:12–68` | `ExactLaws`, `ExactQueue`, `ExactQueue.keyed`, `exactLeftist`: exact batch occurrences, validity and minimum deletion. Conversion to the weaker keyed contract is one-way. |
| `Applications/Search/PriorityInterface.lean:26–39`; `Applications/Search/PrioritySearchQueue.lean:21–31,108–114` | `Laws.add_covers/add_length` and actual same-key replacement permit loss of duplicate occurrences. They cannot replace the source maximum-queue contract. |
| `Applications/Search/ExactPriority.lean:74–138` | `listRemove_none`, `listRemove_spec`, `exactList` give a second exact realization, sorting at deletion. Dualization gives a useful maximum specification client, not VFA's selection algorithm or its linear traversal bound. |
| `Applications/Search/PrioritySearchQueue.lean:162–196` | `takeMin_perm`, `takeMin_le` are reusable selection facts with only decidable LE plus a linear preorder for the bound. Its tail-first recursion differs from VFA's accumulator-select; dualizing it alone is not a source-recursion proof. |
| `Applications/Search/LeftistQueue.lean:182–193,257–285` | `combineQ_entries`, `combineQ_valid`, `insertQ_entries`, `deleteQ_spec` prove native leftist meld/insert/delete laws, including one-element size loss. They can exercise the common semantics; they do not implement binomial carry/join. |
| `Applications/Huffman/Priority.lean:54–72,214–223` | `delete_size`, `two_deletions`, `huffman_correct` demonstrate an actual exact-occurrence client. Huffman's Nat minimum-weight arithmetic is not transported to maximum queues by renaming the order. |
| `Mathlib/Data/Multiset/Defs.lean:100,221–225`; `Mathlib/Data/Multiset/Count.lean:127–189` | `Multiset.coe_eq_coe`, `coe_card`, `coe_count`, `count_cons`, `ext`: List.Perm is exactly finite-multiset equality; lawful counts retain duplicates. Finset/membership alone loses this information. |
| `Mathlib/Data/Multiset/AddSub.lean:58,124–175` | `coe_add`, `count_add`, `card_add`, `erase_cons_head`, `cons_erase`: meld adds multiplicities; deletion erases one copy. These are semantic consequences, not executable source substitutes. |
| `Mathlib/Data/List/MinMax.lean:113–127,254–275,325–327` | `List.argmax_mem`, `argmax_eq_none`, `le_of_mem_argmax`, `maximum_append`, `maximum_eq_coe_iff`, `Perm.maximum_eq` give independent extremum observations; append/count laws are still needed for multiplicities. |

## Pinned Batteries binomial heap: real reuse, explicit gaps

`Batteries/Data/BinomialHeap/Basic.lean` contains a distinct existing binomial
implementation, unlike conaled's leftist queue. Namespace
`Batteries.BinomialHeap.Imp` has `HeapNode` (28), `Heap` (75), `combine` (124),
`Heap.merge` (131), `HeapNode.toHeap` (152), and `Heap.deleteMin` (196).
The public `Batteries.BinomialHeap` is a WF subtype (495), with merge/insert/
deleteMin at 521–538 and `toListUnordered` at 588.

`HeapNode.WF` (336–338) has the same child/sibling shape as source `pow2heap'`:
child recursion changes the parent bound to the child root; sibling recursion
retains the old parent bound. `Heap.WF` (346–348) instead stores occupied trees
at explicit, strictly increasing ranks; VFA stores every slot, including Leaf.
A future recursive tree map plus omission of empty slots can connect these
predicates, but needs proved contents/WF transport and does not preserve cost.

Existing Basic proofs: `Heap.WF.merge` (410), `HeapNode.WF.rank_eq` (413),
`HeapNode.WF.toHeap` (417), `Heap.WF.deleteMin` (453), `Heap.realSize_merge`
(209), `HeapNode.realSize_toHeap` (246), `Heap.realSize_deleteMin` (251).
`Batteries/Data/BinomialHeap/Lemmas.lean:15–35` adds `Heap.findMin_val`,
`Heap.deleteMin_fst`, `HeapNode.WF.realSize_eq` and `Heap.WF.size_eq`.
The latter size facts can support a proved source bridge; they do not prove
contents permutation, maximality, or a primitive-work bound. No such stronger
heap theorem was found in these two files or their Mathlib/project consumers.

WF's edge property is conditional on `Batteries.TotalBLE` (BinomialHeap Basic:338;
`Batteries/Classes/Order.lean:31`). Use a proved lawful non-strict comparator
`decide (b ≤ a)` and Nat transitivity before deriving maximum bounds. Source
smash uses strict `x > y`, choosing the second root on ties; Batteries combine
with this non-strict comparator chooses the first. Tree equality/tie behavior
cannot be inferred from multiset agreement, and a strict comparator is not total.

## Remaining source and resource obligations

Prove `pow2heap'` has `2^n−1` nodes and `pow2heap n` has `2^n`; retain shape,
parent-bound order, forest rank and contents as distinguishable obligations.
Leftist `Ranked`, `rank_size`, `rank_log` (`Applications/Search/LeftistQueue.lean:37,116–128`)
concern shortest/right paths and an inequality, not binomial rank-size equality.
Prove the source validity/contents/deletion exercises (`Binom.v:182–218,263–377`),
including optional ones; source admissions are not Lean proof dependencies.

Charge actual comparisons, carry/join slots, root scans and unzip work before
using `Nat.le_log_iff_pow_le`/`le_log_of_pow_le` (`Mathlib/Data/Nat/Log.lean:157–169`).
`priq` permits arbitrarily long all-Leaf queues: zero live elements do not bound
`find_max`'s scan (`Binom.v:104–116,162–170`). Deletion retains holes; require a
proved trimming invariant, historical rank bound, or explicit slot-length bound.
Sparse Batteries representations discard those holes, so their complexity prose
cannot certify the source algorithm. Reuse `Resources.erasureSquare`, `run`,
and potential laws only with proved source instrumentation; value equality is
not cost equality. See `RESOURCE-AND-EXECUTION-OBLIGATIONS.md` for exact obligations.

Future checked cases: duplicate maxima with exactly one removed; duplicate-rich
meld; zero key versus empty; equal-root smash tie; a rank-i full tree; all-Leaf
padding; malformed raw smash rejection. Preserve `binom_measurement`
(`Binom.v:391–396`) as a separate executable, bounded-integer comparison task.
