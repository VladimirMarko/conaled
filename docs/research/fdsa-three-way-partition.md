# Shared three-way partition values and source execution

This cross-cutting draft makes the existing ordered partition interface
available to both sorting and selection, then supplies a separately measured
one-pass source realization. The shared value operation retains its existing
two-stage implementation and Selection-facing compatibility. The draft is
uncompiled and unaccepted; its source statements and connected clients still
require the complete immutable-candidate validation and review workflow.

## Source correspondence

The source is the July 27, 2026 edition of
[Functional Data Structures and Algorithms](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
PDF SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Exercise 2.3 on printed p.28 specifies three-way partitioning by the ordered
filters for values smaller than, equal to and greater than a supplied pivot.
It then asks for correctness of the separate three-way quicksort algorithm.
Chapter 3 uses the same partition observations in selection on pp.34–35 and
in the selector's time composition on pp.40–41. Appendix B.2, printed p.348,
gives the partition time recurrence and its exact `length+1` solution.

The exact single-tail-recursion implementation is supplied by
[`partition3_code` in Selection.thy](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Selection.thy),
SHA-256 `c2e5970bcdc9430ef802a6612381fdd3820a02bc796d20f4a202060f3f00b4e8`.
The companion first defines the three filters, then proves the code equations
and explicitly selects them for its timing command before proving
`T_partition3`. The one-pass implementation is not a separately displayed
Chapter 3 code block in the inspected manuscript. The companion revision is
recorded separately from the manuscript version; it is not claimed to have
generated that PDF.

The companion theory names Manuel Eberl, TU München. Its applicable Isabelle
source notice is reproduced below. The existing conaled value operation and
proof interfaces are reused, and the new Lean resource realization connects
its own actual recursion to those values.

## Shared values and compatibility

`Sequences.Partition.partition3` retains the existing implementation: first
partition the input by `< pivot`, then partition the first pass's rejected
list by `= pivot`. The result is the standard right-associated product
`List α × List α × List α`, with fields `.1`, `.2.1`, `.2.2`. The ordered
filters are the semantic interface:

| Component | Exact observation |
| --- | --- |
| Lower | Every input occurrence strictly below the pivot, in input order. |
| Equal | Every input occurrence equal to the pivot, in input order. |
| Upper | Every input occurrence strictly above the pivot, in input order. |

Their concatenation is a permutation of the input and their lengths sum to
its length. The buckets need not be sorted, and their concatenation need not
be the original sequence. Set-only equality would lose the required order
and duplicate occurrences.

The shared module owns `partition3_eq_filters`, `partition3_perm`, the three
membership equivalences, `partition_lengths` and `partition_strict_sizes`.
`Applications.Selection.partition3` remains a same-signature definition
wrapper, and all seven old theorem names remain direct adapters. The old/new
operation connection is definitional. This preserves current consumers while
allowing sorting clients to use partition semantics without depending on the
selector's rank, policy and recursion machinery.

The selection-specific source beginning with `sorted_partition` remains in
its original module. Rank, Consumers and existing RankSelection examples are
unchanged. Their ordered-list, equal-block indexing, pivot-policy, fuel,
zero-based internal and one-based public contracts remain independent of the
new resource program. The existing selector is not changed to execute that
program by this extraction.

The shared value and resource modules do not import Selection or Examples.
The new examples provide the compatibility and sequencing clients. No new
partition carrier, classifier record, keyed API, syntax or executor is needed.

## Source equations and actual measured recursion

The shared nil and cons theorems expose the companion's equations as value
laws of the existing operation. For a returned tail triple `(ls,es,gs)`, a
head `y` is added according to this order:

```text
if y < p then (y :: ls, es, gs)
else if p = y then (ls, y :: es, gs)
else (ls, es, y :: gs).
```

Equality symmetry reconciles `p = y` in the code equation with `y = p` in the
filter specification. Linear-order laws identify the final case as `p < y`.
The cons equation does not define a second pure algorithm and does not assign
a one-pass cost to the unchanged two-stage value operation.

`Resources.Partition.partitionRun` supplies the actual measured execution.
Its empty case has one entry tick and the empty triple. Its cons case calls
itself once on the tail, binds the actual returned triple, reconstructs the
selected bucket using those returned lists, and adds one entry tick. It uses
the existing ordinary `Measured`, `bind`, `pure` and `CallCount.tick` interfaces.
No separately computed value is paired with a desired cost formula.

Two independent contracts connect this execution to the source:

```text
(partitionRun p xs).1 = Sequences.Partition.partition3 p xs
(partitionRun p xs).2 = xs.length + 1.
```

The value proof consumes the actual tail result and the shared cons equation.
The work proof follows the program's own empty/cons count recurrence. It
counts one per invocation, including the final empty call, and gives primitive
comparison, equality, projection, tuple and cons operations zero additional
observation. There is no extra wrapper-entry charge or executed length pass.

This is the book's mathematical call observation. It does not assert a machine
comparison, allocation, garbage-collection, stack or physical-runtime bound.
The source reconstructs after its recursive call; one traversal alone does
not establish tail recursion or constant stack use.

## Pivot domains and recursion boundaries

The value/filter/permutation/length laws and exact work quantify over every
finite list and every supplied pivot, with the existing universe-polymorphic
`[LinearOrder α]` interface. They do not add pivot membership, `Nodup`, input
sortedness, `Inhabited`, a finite universe or top/bottom elements. Empty lists
still receive an explicitly supplied pivot; no default value is manufactured.

Membership of the pivot in the full input is a separate sufficient condition
for both strict buckets to be smaller: it gives a nonempty equal bucket.
An outside-range pivot can leave an entire strict bucket unchanged. Conversely,
an absent interior pivot can still produce two smaller strict buckets, so the
membership condition is not characterized as necessary.

Three-way quicksort partitions the tail after removing its head pivot. That
pivot need not occur again in the tail. The buckets are bounded by the tail's
length, which is already smaller than the original nonempty input; the later
termination proof must use that fact rather than a false membership premise.

Selection's semantic recurrence permits arbitrary pivots. Its middle branch
requires the reached index bounds to establish an equal occurrence. An
arbitrary equal bucket can be empty, so neither a nonempty bucket nor direct
return of its pivot follows from the partition interface alone. The required
middle-index bridge and full selection algorithms remain Chapter 3 work.

Existing noninjective monotone selected-value transport also remains separate.
A map that merges values can turn a strict comparison into equality and move
an occurrence between buckets. No blanket monotone bucket-transport law is
asserted here. Equal external keys on distinct records likewise require an
explicitly stated keyed interface, beyond literal equality in this operation.

## Connected cases and independent expectations

The compact examples use public value, filter, permutation, length, strict-size
and cost interfaces, with hypotheses justified in each consequential use.

| Input / composition | Independent expected result | Expected work |
| --- | --- | ---: |
| Empty list, supplied pivot | `([],[],[])` | `1` |
| `replicate n p`, pivot `p` | `([], replicate n p, [])` | `n+1` |
| `[4,1,2,0,3,2,1,4]`, pivot `2` | `([1,0,1],[2,2],[4,3,4])`; lengths `3,2,3` | `9` |
| `[3,1,3]`, absent pivot `4` | `([3,1,3],[],[])`; lower side unchanged | `4` |
| `[3,1,3,1]`, absent pivot `2` | `([1,1],[],[3,3])`; both strict sides smaller | `5` |
| Bind the mixed partition to partitioning its actual lower bucket around `1` | Second input `[1,0,1]`, result `([0],[1,1],[])` | `9+4=13` |

The generic equal-block family includes zero and singleton inputs; strict
shrinking is used only after establishing positive length and pivot membership.
The mixed fixture has visible nonsorted order within both strict buckets and
repeated values. It distinguishes the full occurrence contract from set or
sorted-output observations.

The composition uses the same measured operation twice and ordinary bind.
Its continuation receives the first actual triple, and its first field is
the second input list. This is distinct from passing the original input or
the entire value/cost pair, and it introduces no new executor or outer tick.
The old Selection names are exercised by compatibility uses while the existing
complete RankSelection examples remain in the public import/audit closure.

## Distinct cost interpretations and remaining coverage

The value specification, existing two-stage implementation and new one-pass
realization have explicitly different roles. Output equality supplies no
`n+1` count for the old uninstrumented operation. It also does not replace
Exercise 2.4's two-filter quicksort observation. There, each filter on a tail
of length `m` has charged predicate work and total `2*m+1`; the two filters
and current-call entry contribute `4*m+3`, in addition to the recursive calls.
The supplied metric omits append traversal. Its later worst-case and average
proofs retain that execution and tariff.

This unit supplies shared partition semantics behind C02-102 and C03-011/013,
and the new one-pass realization required by C03-031 and B-018/019, subject
to its validation gates. Complete quicksort3 correctness, rank/dispatch
bridges, actual selection and median-of-medians recursion, random policies,
whole-algorithm costs and all other book obligations remain in their original
chapters. No whole chapter or appendix is accepted by this shared draft.

## Statement assessment and validation status

The source review keeps exact tuple order and multiplicity, arbitrary-pivot
correctness, qualified strict decrease, actual returned-tail sequencing,
independent work and value laws, and the unchanged old interface separate.
The API/source/case preflights and original byte identities are retained in
the local review evidence. They are preparation rather than compiler results.

The draft starts from the focused-pass but unaccepted Chapter 1 repair.
Accepted repaired Chapter 1 remains required before integration or acceptance;
the initial Chapter 2 foundation prefix is unchanged. New and existing affected
modules require focused compilation, the full applicable candidate build and
exhaustive audit, both independent review axes and immediate candidate-record
verification. Source authoring and independent expected calculations do not
supply those results.

## Referenced companion source notice

The following notice accompanies the pinned Isabelle source equations:

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
