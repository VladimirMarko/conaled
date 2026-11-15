# Chapter 2 Exercise 2.2: accumulator quicksort source readiness

Prepared 2026-11-03 for the existing C02-101 obligation. **Report-only
preparation, not an implementation, new shared unit, scope freeze, final review
or chapter acceptance.** Chapter 1 remains the active prerequisite. The saved
initial Chapter 2 prefix is still
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`; this note does not change its history,
acceptance status or integration order.

## 1. Bounded conclusion and preserved scope

Exercise 2.2 has a small, concrete remaining value-level task: implement the
actual append-free accumulator recurrence and prove its equality to the
ordinary source quicksort followed by an **arbitrary** suffix. The source does
not prescribe a numerical running-time theorem for this variant. Its reason
for avoiding append is retained, without turning that motivation into a new
measured executor or an unsupported asymptotic, allocation or stack claim.

Ordinary first-pivot quicksort, C02-017–023, is an earlier implementation
prerequisite and already has retained implementation/probability preparation.
This note fills the less-developed C02-101 exercise route; it does not move
that exercise ahead of the ordinary sorter or require a separate library unit.
When Chapter 2 is activated, use the accepted/integrated initial prefix and the
actual ordinary quicksort implementation. No such integration is performed here.

The frozen Chapter 2 requirements still refer to their original **107-row**
inventory, SHA-256
`edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d`.
The explicit reconciliation of C02-088 subsequently appended C02-108–112;
the current inventory contains **112 obligations**. Read that reconciliation
alongside the unchanged requirements. C02-101 is present in both scopes, and
none of the other 111 current rows is weakened or discharged by this report.

## 2. Primary evidence and exact source positions

The actual retained PDF was read at physical pages 22 and 34 using text
extraction to standard output, alongside the saved Chapter 2 reading copy and
the formal companion. No new source was retrieved. Extracted comparison glyphs
are resolved through the companion's explicit Isabelle symbols, not guessed
from the PDF extraction's control characters.

| Source | Exact identity and relevant passage |
| --- | --- |
| Official FDSA book, version July 27, 2026 | <https://fdsa-book.net/functional_data_structures_algorithms.pdf>; `book-source/functional_data_structures_algorithms.pdf`, 1,742,029 bytes, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. Chapter 2 by Tobias Nipkow and Christian Sternagel. Ordinary ordering convention: printed p.13; quicksort and its correctness: p.16 / PDF p.22; Exercise 2.2 and adjacent exercises: p.28 / PDF p.34. |
| Chapter 2 reading copy | `book-source/chapter02.txt`, 28,337 bytes / 562 lines, SHA-256 `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1`. Lines 1–28 give order assumptions; 98–126 give ordinary quicksort; 508–512 give Exercise 2.2; 513–542 separate Exercises 2.3/2.4. This is a locating aid, not another edition. |
| Isabelle companion, author Tobias Nipkow | [Sorting.thy at the retained revision](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Sorting.thy). Local `book-source/Sorting.thy`, 14,846 bytes / 435 lines, SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. Lines 327–329 define ordinary quicksort; 331–339 prove multiset, set and sortedness observations. |
| Retained provenance manifest | `fdsa-control/provenance/source-inventory.json`, SHA-256 `4d71f3750c0cab3213bbf768a53fb1c18210ccb85a022afb107bd5d416e625e4`; records the book edition, exact source URL/revision and the separate source-license identity. |
| Applicable Isabelle notice | `book-source/ISABELLE-COPYRIGHT`, 1,673 bytes / 36 lines, SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`; exact URL <https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/COPYRIGHT>. Full notice retained below. |

The book and companion have distinct pinned identities. This inspection does
not establish that the companion revision generated the July manuscript.
A bounded search of the entire retained `Sorting.thy` finds no `quicksort2`
definition or proof and no `time_fun quicksort` declaration. Its only
`time_fun` declarations are for insertion. Therefore neither an accumulator
implementation nor a generated accumulator timing equation can be attributed
to this inspected companion.

## 3. Ordinary algorithm and the literal exercise target

Here `#` is cons and `@` is ordinary list append. With source notation
normalized for readability, the companion gives:

```text
quicksort [] = []
quicksort (x # xs) =
  quicksort (filter (fun y => y < x) xs)
  @ [x] @
  quicksort (filter (fun y => x ≤ y) xs)
```

The first occurrence is the pivot and only the **tail** is filtered. Both
filters retain their input order. Equal elements go to the right child;
there is no deduplication, equality block, reversed partition or random pivot.
The chapter assumes a linear order even when the printed type omits its class;
`Sorting.thy:327` explicitly says `('a::linorder) list`.

The companion proves `mset (quicksort xs) = mset xs`, then set preservation,
and `sorted (quicksort xs)`. The book's supporting pairwise-append and
complementary-filter statements remain C02-018–023 obligations. They establish
the ordinary sorter; the accumulator law is an additional relation to that
actual definition, not a substitute for those proofs.

Exercise 2.2 requests a function with two list arguments, accumulating through
cons in its second argument while avoiding append, and this exact target:

```text
quicksort2 xs ys = quicksort xs @ ys
```

Both lists are unrestricted. In particular `ys` is the **suffix**, not a list
to merge or sort with `xs`, and not a reversed accumulator that must later be
reversed. The empty-suffix specialization returns ordinary quicksort, but that
specialization alone does not satisfy the universal exercise target.

## 4. Smallest proposed solution and proof route

The following is a proposed solution of the exercise, already sketched in
C02-101 and the reuse plan. It is **not** a supplied source solution or an
existing Lean declaration. Abbreviate the literal filters by `less x xs` and
`greaterEq x xs` only in this mathematical presentation:

```text
less x xs      = filter (fun y => y < x) xs
greaterEq x xs = filter (fun y => x ≤ y) xs

q2 [] suffix = suffix
q2 (x # xs) suffix =
  q2 (less x xs) (x # q2 (greaterEq x xs) suffix)
```

The executable body has no append. The actual result of the right recursive
call is prefixed by the pivot and passed to the left recursive call. It is
not permissible to replace that body by `quicksort xs @ suffix`, a call to
an unrelated library sorter, or a suffix-sorting operation simply because one
can arrange a selected final-value theorem.

The first list argument supplies a termination measure, independent of the
suffix. Each filtered child has length at most `xs.length`, hence strictly
less than `(x # xs).length`. The right result can enlarge the left call's
second argument without affecting this measure. The all-suffix induction
hypothesis is essential for exactly that dependent argument.

For `L = less x xs` and `R = greaterEq x xs`, the nonempty proof calculation is:

```text
q2 (x # xs) suffix
= q2 L (x # q2 R suffix)
= quicksort L @ (x # q2 R suffix)
= quicksort L @ (x # (quicksort R @ suffix))
= (quicksort L @ [x] @ quicksort R) @ suffix
= quicksort (x # xs) @ suffix.
```

The induction must quantify `suffix` after choosing the smaller input list,
so the hypothesis for `L` applies to `x # q2 R suffix`, not just to the
original suffix. The empty case is `suffix = [] @ suffix`. These steps use
matching recursive filters, filter-length bounds and ordinary cons/append
identities. Associativity here is a **value** identity, not a resource transfer.

The source specialization keeps its linear order and decidable comparisons.
The simulation calculation itself needs no sortedness, distinctness, suffix
ordering, disjointness or equality decision on whole lists; it does not use
complementarity of the filters to perform the append calculation. Complementary
partitions and order laws are instead needed for the ordinary sorter's
permutation and sortedness. There is no reason to add `Inhabited`, `Fintype` or
a default element. An empty payload type has only empty lists and is supported.
This observation about weak proof premises does not propose a new comparator
record, generic partition framework or additional public abstraction.

The nested recurrence is not a proof of tail recursion or constant stack use:
the right recursive call occurs inside the argument to the left call. The
exercise asks for append-free accumulation, unlike the explicit tail-recursion
wording in the separate Exercise 2.6.

## 5. Arbitrary suffix, sortedness and meaningful observations

An arbitrary suffix is preserved in its original order, including multiplicity
and values that compare below the sorted prefix. For example, the proposed
recurrence has the mathematically expected result

```text
q2 [3,1,3,2] [9,0] = [1,2,3,3,9,0].
```

The result is not sorted; this is consistent with the exercise. Even a sorted
suffix is insufficient without the cross-boundary order: `q2 [2] [1]` is
`[2,1]`. Conversely, the empty-suffix specialization is sorted once the
ordinary quicksort theorem is established. More generally, the book's
pairwise-append law characterizes sortedness by sortedness of both pieces
and every prefix element being at most every suffix element. After ordinary
quicksort correctness, that cross condition can be expressed using members
of the original `xs`. This is an explanation of the semantic boundary, not
a newly frozen requirement to add a general suffix-sortedness API.

A future connected exercise example should invoke the actual accumulator and
the universal source correspondence with a nonempty suffix, as the frozen
Chapter 2 requirements already demand. Empty and singleton inputs expose the
base and pivot-cons cases; duplicates expose the unchanged right-tie branch.
The independent case preparation owns the eventual compact expected-case
selection. This report supplies no executed test, Lean proof or extra case
acceptance gate.

## 6. Costs and adjacent obligations remain separate

Exercise 2.2 motivates the change by the linear work of appending an ordinary
list in its first argument. That mathematical source assertion remains covered
by the existing append/call-model obligations. The new requirement in this
exercise is an actual append-free recursive implementation and the value law.
There is no displayed `Tquicksort2`, comparison recurrence, exact improvement
constant or new asymptotic target on printed p.28 or in the inspected companion.

The following already-retained work therefore stays separate:

| Existing obligation or preparation | Relation to C02-101; preserved boundary |
| --- | --- |
| C02-017–023, ordinary quicksort and helper facts | The actual first-pivot definition and termination anchor the correspondence. Its content/order correctness remains separate and supplies the sorting corollary; those theorems are not logical premises of the value simulation itself. A stable-sort library result does not identify this recursion. |
| C02-024, `quicksort-average-proof-plan.md` and `quicksort-conditional-mean-preflight.md` | Uniform distinct-key input average and conditional child-law/actual-cost bridges remain required. An arbitrary-suffix value equality supplies neither a distribution nor an expected-work theorem. |
| `random-pivot-api-preflight.md` | Fresh uniform input-occurrence selection, pivot removal, actual recursive execution and its expected work remain a distinct source assertion. None is a dependency forced by this deterministic accumulator exercise. |
| C02-102 / Exercise 2.3 | Three-way partitioning and its duplicate behavior remain a different algorithm. Do not replace the two-way recursion by it to implement C02-101. |
| C02-103 / Exercise 2.4 | The separately supplied tariff has empty cost 1, two full filters with predicate cost 1, and no append charge. Its exact sorted worst case and global bound remain `2*n^2 + 2*n + 1`; no equality with a future `q2` counter follows from this value law. |
| Literal append-inclusive ordinary quicksort | The frozen requirements separately retain both append occurrences and the actual tariff/association bridge. This source-cost proof is neither removed nor discharged by producing an append-free variant. |
| All remaining C02 rows, including C02-108–112 | Insertion, all merge/natural-run variants, stability helpers, exercises and separate builder/scanner operational claims remain unchanged. No builder-application contract is newly required for `q2`. |

In particular, avoiding append does not make two-way quicksort linear or
establish a duplicate-uniform expected `O(n log n)` bound. The ordinary pivot
and partition recursion is still present. This note does not specify a new
cost model, measured executor, runtime/compiler claim or mandatory performance
comparison for the accumulator. It also does not transfer counts through the
value associativity used in Section 4.

## 7. Retained planning identities and handoff

The preceding planning pass read the complete current inventory/reuse plan,
requirements and prefix reconciliation/compatibility. This bounded follow-up
reread the exact exercise/ordinary passages, full frozen requirements and
conditional-mean plan, and the relevant existing scope/proof-plan passages.
Ordinary file identities below were read directly; no project hash helper,
compiler, checker, Git command, active-output or cache inspection was used.

| Existing record under `fdsa-control/` | SHA-256 |
| --- | --- |
| `research/chapter02-obligations.md` | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| `research/chapter02-reuse-plan.md` | `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a` |
| `reviews/chapter02-requirements.md` | `f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36` |
| `research/scope-reconciliation.md` | `21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87` |
| `research/quicksort-average-proof-plan.md` | `ca2090accf91ac662f2738486f7590e8b29968be524794e9356257d5f918dc46` |
| `research/quicksort-conditional-mean-preflight.md` | `464af5974d485823b7ecb76b7546ad793ed860fbf947afdb03ef11d91b25b66c` |
| `research/random-pivot-api-preflight.md` | `91d34b4c86d315935f0df98023cf382fe3d141e8ab7d748baf9fdc64738a0ed0` |
| `reviews/chapter02-prefix-source-reconciliation.md` | `a563f8001a86326ed124ad0097aab0ea6b652e21ddfbc9e7203a3c934158dd1a` |
| `reviews/chapter02-prefix-source-compatibility.md` | `0c1945c23f9d3374cda1a4f98083fc2c31309e1310486e2fb8ea9ae150fd1577` |

The existing prefix remains the original insertion/list/notation sequence.
Its reconciliation preserves both that history and the repaired Chapter 1
history; it does not include an accumulator quicksort implementation. This
preparation creates no branch, implementation unit, new requirement or review
loop. All code and chapter transitions await the coordinator's existing
workflow and applicable acceptance. The only authored artifact is this report.

## 8. Attribution and license

The book chapter is by Tobias Nipkow and Christian Sternagel, edited within
FDSA by Tobias Nipkow. The ordinary theory header attributes its formal source
to Tobias Nipkow. The exercise solution recurrence above is a proposed Lean
reconstruction, not a claim that an omitted Isabelle exercise solution was
recovered. No long book prose or whole manuscript is incorporated here.

The separately pinned Isabelle source uses the following BSD notice. Preserve
it and the attribution if the source recurrence/proofs are adapted. This is
not a claim that the book itself has the Isabelle software license or that
a separate AFP probability development is required to solve this exercise.

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

No concrete source inconsistency was found in this bounded reading. The
remaining work is the actual Chapter 2 implementation, its universal proof,
connected cases and the existing validation/review gates. Source reasoning in
this report is not checked Lean evidence, and no obligation is accepted here.
