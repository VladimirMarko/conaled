# Ordinary list merge: value laws and two declared observations

This shared source draft connects FDSA's ordinary merge to the existing
`List.merge`, sorting contracts and measured composition. It adds the missing
input-sublist/converse facts and one execution that records both head
comparisons and recursive merge invocations. **Compilation, the full candidate
gate and independent final reviews are pending.** This note describes the
draft's mathematical contracts; it does not record chapter acceptance.

## Source and reuse boundary

The prescribed source is Chapter 2 §2.4, printed pp.17–18 of
[*Functional Data Structures and Algorithms: A Proof Assistant Approach*](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
July 27, 2026. Its PDF SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The companion Isabelle equations and proofs are in Tobias Nipkow's
[`Sorting.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Sorting.thy):
merge at lines79–82, multiset/support and sortedness at94–128, comparison
recurrence/bound at147–155, and output length at168–169. Its SHA-256 is
`dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`.
This pinned companion revision postdates the manuscript; it is not asserted
to be the manuscript's generation revision. The equations were compared
directly. The applicable Isabelle notice is retained below.

The pinned Lean verification operation is
[`Init.Data.List.Sort.Basic`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/List/Sort/Basic.lean),
with its laws in
[`Sort.Lemmas`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/List/Sort/Lemmas.lean).
These are the project's Lean4.35.0 revision; the source files identify Lean
FRO and the Apache2.0 license. Existing imported dependencies retain their
own notices. The corresponding local source bridge remains
[`Sorting.SourceMerge`](../../Applications/Sorting/SourceMerge.lean).

Ordinary merge is also a useful component of chosen solutions to Chapter14
Exercises14.1 and14.3, printed pp.180–181. A sorted-list queue may use it as
its merge operation; the existing `LeftistQueue.toListQ` uses root followed
by merge of its two child enumerations. Those exercises leave the algorithm
choice open. This shared component supplies their merge ingredient, not the
complete queue implementation, ordinary-tree correspondence or enumeration
cost theorem. The abstract heap source is
[`Heaps.thy`](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Heaps.thy),
SHA-256 `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe`.

## Existing values and the small converse extension

[`Sorting.Merge`](../../Applications/Sorting/Merge.lean) continues to use
ordinary `List.merge`, with `mergeBy` pulling comparison back from keys.
Its permutation, forward sortedness, equal-key filter, stability and combined
specification remain unchanged. The new value declarations are:

| Declaration | Contract and assumptions |
| --- | --- |
| `sublist_merge_left`, `sublist_merge_right` | Each input remains an ordered sublist of the output, for every Boolean comparator. No order, equality decision, inhabitant or sortedness is needed. |
| `pairwise_of_merge` | Any pairwise relation on the output holds on each input. The relation is independent of the comparator; the proof uses the two sublists and existing `List.Pairwise.sublist`. |
| `merge_sorted_compatible_on_iff` | Combines that converse with the existing forward law under precisely its key preorder and comparison compatibility on actual cross-input members. |

The identity-key/source specialization gives the book's sortedness equivalence,
equation(2.12). The reverse direction is more general than that ordered
specialization. Permutation or membership alone would not justify it: these
facts preserve each operand's occurrence order.

Stability retains its separate hypotheses. The actual key comparator takes
the left element on an equal-key comparison. The existing filter/stability
theorems require both blocks to be sorted and the key comparison/equality
capabilities they state, without ordering or comparing payloads. Sortedness
compatibility alone permits choosing the right equal-key record first.

## One execution, two observations

[`Resources.ListMerge`](../../Applications/Resources/ListMerge.lean) defines
one `run cmp xs ys : Measured (List α) (Nat × Nat)`. The cost coordinates are
**(comparisons, entries)**. An empty-side branch returns the other input with
observation `(0,1)`. A nonempty branch tests the actual two heads, executes
only the selected smaller recursive call, and constructs its output cons
from that call's returned list while adding `(1,1)` through existing `bind`.
The sum of input lengths is the decreasing measure.

`comparisons` and `entries` are transparent projections of that same result.
They are not separate recursive executors. The whole-pair equations,
`run_value` and scalar projection equations connect the actual returned value
and observations. In particular:

| Public fact | Meaning |
| --- | --- |
| `run_nil_left`, `run_nil_right`, `run_cons_cons` | Actual returned-list and observation recurrence, including exactly one invocation for two empty inputs. |
| `run_value` | The actual returned list is `List.merge xs ys cmp` for arbitrary lists and Boolean comparison. |
| `comparisons_nil_left/right`, `comparisons_cons_cons` | Exactly the handwritten Chapter2 `C_merge` equations: zero bases and one head comparison plus the chosen recursive count. |
| `entries_nil_left/right`, `entries_cons_cons` | Separately declared invocation equations: one at the base and one for each nonterminal entry. |
| `run_entries_cons_cons` | The scalar projected execution is the existing `CallCount.tick` around the selected projected child and an uncharged cons of its actual returned value. |
| `entries_eq_comparisons_add_one` | One merge has exactly one terminal invocation with no head comparison. |
| `comparisons_le`, `entries_le` | Bounds by the input-length sum and that sum plus one, respectively. |
| `comparisons_cons_pos` | Two nonempty inputs necessarily cause the first comparison. |

These bounds require no sorting, comparator law, distinctness, payload equality
or inhabitant. They are the deliberately loose source bounds, not tight
worst-case formulas. The operation supports every payload universe, including
an empty payload type.

The comparison projection counts calls to the supplied comparator, not the
work inside an arbitrary comparator or key function. Cons, lengths, external
preparation and traversal of an untouched suffix have no additional charge in
this model. The entry projection counts the logical merge's invocations,
including initial and terminal calls. It does not count every Lean helper.
The source comparison counter is handwritten; it is not a recovered generated
`time_fun merge` theorem. Computing an observer program has no inferred cost
from its returned observation.

Lean replaces its verification-oriented merge at runtime with a proved-equal
tail-recursive implementation. That value theorem does not identify either
declared observation with compiled calls, allocation, stack use or elapsed
time. The present mathematical statements make no such runtime claim.

## Exact key transport and actual composition

`run_map` takes a possibly noninjective map `f : α → β`, allowing independent
universes, and comparison agreement only on actual cross-input members:

```text
∀ a ∈ xs, ∀ b ∈ ys, cmp a b = cmp' (f a) (f b).
```

It relates the entire mapped-input execution to the mapped output of the
original execution with **both observations unchanged**. Each recursive branch
agrees. This supplies the tagged-record/key-only connection without payload
equality or injectivity. Existing `List.map_merge` alone proves only values.
The theorem does not declare the work of performing a caller's maps free.

The examples use ordinary `Resources.bind` for two merges, with the second
receiving the first run's actual list. If its operands are `zs` and that result,
the comparison bound is `2*(length xs + length ys) + length zs`. Total entries
equal total comparisons plus **two**, since each merge has its own terminal
invocation. The two coordinate additive homomorphisms and existing
`reweight_bind` connect scalar projections of this same execution. The affine
single-merge shift by one is not an additive homomorphism.

The selected small pipeline first merges `[2]` and `[0]`, then merges `[1]`
with the actual `[0,2]`. It returns `[0,1,2]` with totals `(3,5)`. Feeding the
original concatenation `[2,0]` into the continuation instead returns `[1,2,0]`
with `(2,4)`. Thus the case distinguishes actual intermediate-value sequencing
in both value and work; no enclosing wrapper entry is silently charged.

## Connected examples and boundaries

[`Examples.MergeCosts`](../../Examples/MergeCosts.lean) retains the frozen
independent expectations and applies the public facts to them. The ordinary
merge laws supply length, occurrences, support and order after actual erasure.

- Empty sides return the remaining list with `(0,1)`, including arbitrary
  lists over `Empty`.
- The singleton witnesses `[0]`/`[1,2]` and `[2]`/`[0,1]` have the same sorted
  output but observations `(1,2)` and `(2,3)`.
- Interleaving `[0,2,2]` and `[1,2,3]` retains all three occurrences of2 and
  gives `(4,5)`. Generic always-true/false clients retain arbitrary payloads.
- Equal-key operand swaps can retain the same unlabelled output while changing
  comparisons. Generic tagged records map to keys through actual `run_map`.
- The signed-record client reuses the existing stable-sorting expected value
  and specification, together with the new erasure/counts and existing merge
  contracts. It does not define a parallel stable-sort specification.
- Arbitrary comparators cannot sort away the retained unsorted sublist
  `[3,1]`. Actual unsorted tagged inputs also show why left ties alone do not
  remove the sorted-block premise of the equal-key filter theorem.
- On distinct tags with equal keys, always-false comparison can preserve
  sortedness and occurrences while violating the stable-filter observation.
- Both nonempty inputs give `C ≤ E ≤ 2*C` through the existing C1
  `cost_le_add_entry`/`add_entry_le`. An empty side gives `C=0,E=1` and
  `zero_cost_entry_matters` refutes `E ≤ K*C` for every natural coefficient.

The independent queue client measures one ordinary priority merge of
`toListQ l` and `toListQ r`, followed by an uncharged root cons. Its value is
the existing raw `toListQ` node body, with no heap/rank invariant. Existing
`toListQ_perm.length_eq` and `entries_length` turn the local bounds into
`C ≤ size l + size r` and `E ≤ size l + size r + 1`.

The concrete raw node has cached rank99, priority9 and raw rank-zero singleton
children with priorities1 and2. The body returns priorities `[9,1,2]` with
**merge-only** counts `(1,2)`; the result is unsorted. Neither child enumeration
nor the enclosing tree entry is charged by that local observation. A complete
measured enumeration must sequence and count those computations separately.

## Remaining book obligations and validation

This unit supplies only the ordinary merge portion of the Chapter2 map:
C02-025, C02-027's merge termination, C02-028/029/031/033/035/037. It leaves
all actual floor-left sorter definitions, decreasing halves, sorted-child
cost composition, stability, printed power-of-two and all-length/real-log
bounds, bottom-up/natural algorithms, scanner/builder observations and
exercises to their retained chapter scope. The original107 and reconciled112
inventory records, including C02-108–112, are unchanged. Standard ceil-left
sort value equality supplies no source-cost equality.

Chapter14 still needs its concrete sorted-list representation, direct minimum
and deletion costs, full ADT laws, ordinary-tree/carrier correspondence,
complete measured enumeration and quadratic theorem, and all other exercises.
Binomial merge additionally links equal-rank roots and carries through the
recursively merged forest; its Chapter17/AppendixB.7 tariff and coupled
work/output-length argument are not specializations of this ordinary merge.

The local draft uses the existing public entrypoint and unchanged pinned
environment. Acceptance requires the applicable complete candidate build,
both integrity passes, source/coverage checks, exhaustive transitive axiom
audit, both independent review axes and immediate candidate verification.
Author source readback and finite hand calculations are preparation only.

## Isabelle notice

The following complete notice is retained from the pinned Isabelle source
distribution (`ISABELLE-COPYRIGHT`, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`).

```text
ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are 
met:

* Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer in the 
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS 
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED 
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A 
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT 
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, 
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY 
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```
