# Chapter 2 Exercise 2.3: three-way quicksort source readiness

Prepared 2026-11-03 for existing obligation **C02-102**. This is bounded,
Chapter 2-local source preparation, not implementation, a new shared unit,
a requirements freeze, final review or acceptance. Chapter 1 remains active;
root retains the sole full validator at the immutable candidate
`07e480f6ec9958d4975bb90151005b84f2907614`. This report did not inspect that
validator's outputs or change its state.

## 1. Conclusion and unchanged chapter scope

The book prescribes the three-way quicksort recurrence, including a pivot
followed by the complete equal block and recursive sorting of only the strict
sides. The exercise asks for correctness: nondecreasing order and preservation
of the entire input multiset. It does not supply a separate time function,
expected-work bound, keyed-stability target or tail-recursion requirement.

The source-specific sorter is still the relevant implementation gap. Existing
partition mathematics is substantial, and a separate shared extraction has
already been drafted as XQ01. No second extraction unit, generic partition
framework, sorting specification or measured executor is justified by this
readiness note. The remaining source obligations belong to Chapter 2 after
its accepted prerequisites and existing integration/review workflow.

Both the unchanged historical **107-row** inventory and current **112-row**
inventory contain exactly the same C02-102 row. The current additional
C02-108–112 rows explicitly unpack C02-088; they neither replace the frozen
snapshot nor change this exercise. The original initial Chapter 2 prefix
`c80eec92f5458eccfd1c34c8314d666c2a1e3847` remains intact and unaccepted.
Nothing here activates Chapter 2 or closes any of its 112 obligations.

## 2. Primary evidence, attribution and provenance

The retained PDF's physical page 34 was read directly by text extraction to
standard output. The saved chapter extract supplies the surrounding order
convention and ordinary quicksort. The complete current Selection.ThreeWay
source and relevant Rank prefix were read as ordinary text. No remote source,
Git operation, compiler, checker, project hash helper or cache was used.

| Evidence | Exact identity and location |
| --- | --- |
| Official FDSA book, July 27, 2026 edition | <https://fdsa-book.net/functional_data_structures_algorithms.pdf>; `book-source/functional_data_structures_algorithms.pdf`, 1,742,029 bytes, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. Chapter 2 by Tobias Nipkow and Christian Sternagel. Order convention: printed p.13; ordinary quicksort: p.16; Exercise 2.3: p.28 / PDF p.34. |
| Retained Chapter 2 extraction | `book-source/chapter02.txt`, 28,337 bytes / 562 lines, SHA-256 `d020b485c3a50e70809d449ef0dc05828500172b1809777861173b274b4fe4c1`. Lines 1–29: implicit linear order; 98–126: ordinary sorter and its claims; 513–525: Exercise 2.3; 526–542: the different Exercise 2.4 tariff. |
| Isabelle companion | [Sorting.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Sorting.thy), revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`; local 14,846 bytes / 435 lines, SHA-256 `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`. Header credits Tobias Nipkow. Ordinary quicksort and proofs are at 327–339. |
| Existing integrated comparison source | `conaled/Applications/Selection/ThreeWay.lean`, 10,489 bytes / 226 lines, SHA-256 `bd72ca5f11d028cde9420ae42f9a9f1f84d6cfc00bf02bd528a61fd00f586d52`. Definition and independent partition laws: 12–60; `sorted_partition`: 62–88; selector dispatch and recursion follow. |
| Existing value baseline used by Selection | `conaled/Applications/Selection/Rank.lean`, 3,713 bytes / 91 lines, SHA-256 `4a82df75593d909e2968bf1e27cbfea52c9795abfe81250bb2385e7dfc16f965`. The `ordered` abbreviation is `Sorting.sortOn id`, with permutation and pairwise laws; it is not the source quicksort. |
| Applicable Isabelle notice | `book-source/ISABELLE-COPYRIGHT`, 1,673 bytes / 36 lines, SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`; [exact pinned COPYRIGHT](https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/COPYRIGHT). Full notice retained below. |

The manuscript and companion are separately pinned. This report does not
identify the source revision as the manuscript's generating revision. The
entire retained `Sorting.thy` was searched for the relevant names: it contains
ordinary `quicksort`, but no `quicksort3`, `partition3`, or generated quicksort
timing declaration. Its only `time_fun` declarations are for insertion.
The three-way recurrence below is **printed in the exercise**; its forthcoming
Lean correctness proof is reconstruction work, not an inspected Isabelle
exercise solution. This is a provenance distinction, not a defect in the book.

## 3. Exact exercise semantics

With typography normalized, the printed operations are:

```text
partition3 x xs =
  (filter (fun y => y < x) xs,
   filter (fun y => y = x) xs,
   filter (fun y => x < y) xs)

quicksort3 [] = []
quicksort3 (x # xs) =
  let (ls, es, gs) = partition3 x xs
  in quicksort3 ls @ x # es @ quicksort3 gs
```

The last expression has the value of concatenating the sorted left block,
`x # es`, and the sorted right block. Explicit parentheses such as
`quicksort3 ls @ ((x # es) @ quicksort3 gs)` express that value grouping.
No cost equality is inferred from rearranging append parentheses.

Consequential details of the actual source are:

- The first occurrence is the pivot. All three filters inspect **the tail
  `xs`**, not the complete `x # xs`.
- The left and right predicates are both strict. Equality belongs only to
  the middle list; in the ordinary two-way version it belonged to the right
  recursive child instead.
- Each filter preserves input order and multiplicity. The middle list is
  not a set, a Boolean test of membership or one representative value.
- The pivot occurrence is inserted exactly once, **before** the complete
  equal block. It is not already included by the tail filters.
- Only `ls` and `gs` are recursive arguments. The equal block is returned
  directly, although its elements still participate in ordinary list output.

Chapter 2's implicit domain is a linear order, including its compatible
strict comparison and decidable equality/comparisons. The three predicates
are exhaustive and mutually exclusive on that domain. An arbitrary strict
relation does not justify that coverage: incomparable elements can satisfy
none of `<`, `=`, `>`. No weaker arbitrary-comparator claim is supplied here.
There is no `Nodup`, nonempty-tail, finite-payload, `Inhabited`, default-element
or externally valid pivot-policy premise. Empty input returns empty output.
For an empty element type, this remains the only possible list input.

## 4. What correctness must establish

The exercise's correctness request refers to the chapter's existing sorting
specification, C02-003. For every finite source-domain list `xs`, retain both:

```text
sorted (quicksort3 xs)
mset (quicksort3 xs) = mset xs
```

In Lean, ordinary `List.Pairwise (· ≤ ·)` and `List.Perm` can witness those
observations with the standard multiset bridge. Set equality alone loses
multiplicity; sortedness alone admits the empty output. Replacing the actual
recurrence by a library sort would miss the prescribed algorithm even if its
final list has both properties.

The source-level proof obligations are small and concrete:

1. **Termination.** For `x # xs`, both strict-side lengths are at most
   `xs.length`, and therefore smaller than the full input length. Repeated
   keys do not compromise this argument. The equal block does not recurse.
2. **Occurrence preservation.** The three tail buckets concatenate to a
   permutation of `xs`. Apply the recursive permutation results to the strict
   buckets and insert the one pivot occurrence in the displayed middle place.
   This retains every equal-tail occurrence in addition to the pivot.
3. **Ordering.** The recursively returned strict blocks inherit their source
   bucket membership through their content theorem. Every left value is below
   the pivot, every middle value equals it, and every right value is above it.
   Reflexivity sorts the equal block; the usual pairwise cons/append facts
   and transitivity connect the three blocks.

These are proposed proof connections, not new obligations beyond C02-102.
Existing ordinary sorting uniqueness may subsequently connect the result to
other correct sorters, but output uniqueness is not a source-recursion or
cost proof. No additional equality theorem is made mandatory by this note.

## 5. Existing Selection reuse and the exact premise boundary

The inspected `Applications.Selection.partition3` uses two stable partitions:
first split by `< p`, then split the first operation's upper remainder by
`= p`. Its theorem `partition3_eq_filters p xs` identifies the returned triple
with the exercise's three literal filters on **every** list and pivot under
its `LinearOrder` assumption. Thus the value observations agree without a
pivot-membership or distinctness premise; the executed traversal structures
remain different.

| Existing fact | Useful source connection and limit |
| --- | --- |
| `partition3_eq_filters` | Exact `<`, `=`, `>` bucket value correspondence, preserving order and all equal occurrences. It proves no cost equality. |
| `partition3_perm`, `partition_lengths` | Concatenated tail content and total length. Add the separately held pivot when connecting to `x # xs`. |
| `partition_left_mem`, `partition_equal_mem`, `partition_right_mem` | Exact member predicates for the three buckets; usable in the ordinary correctness induction. |
| `partition_strict_sizes p ys hp` | Assumes `hp : p ∈ ys` and proves both strict sides shorter than **that** `ys`. It is not the needed unconditional tail-shrinkage theorem. |
| `sorted_partition p ys` | Relates the existing `ordered ys` to sorted strict buckets and the unchanged equal bucket. This is a value theorem about a standard sorting baseline, not a definition of `quicksort3`. |

In the exercise, `x` belongs to the full input but may not belong to its tail.
For example, partitioning `[2,1]` around the held pivot `0` yields the entire
tail as the greater bucket. Its length equals the tail length and is still
strictly less than the full input `[0,2,1]` length. The correct termination
measure is the full input length, using the filter bound on its tail. Adding
`x ∈ xs` to make the Selection strict-size theorem apply would reject valid
exercise inputs.

Another legitimate value-proof route can use `sorted_partition` on the full
`x # xs`, after proving its buckets are `(ls, x # es, gs)` when the tail's
buckets are `(ls, es, gs)`. Together with the recursive value identities,
this yields agreement with `ordered (x # xs)` and hence its correctness.
That is a proof route only: it does not authorize partitioning the full input
in the executable source body and then adding another pivot.

The old reuse plan proposed extracting an independent partition fragment if
needed. That extraction has **already been drafted**, so the proposal must
not be mistaken for a new missing shared component. The retained XQ01 records
identify candidate `de5410286bbefd841dff50bef55c2e52d2ebbd2a`, based directly on
`07e480f6ec9958d4975bb90151005b84f2907614`, with frozen requirements SHA-256
`b1f55911c44a11def3498484787fcb04972398ec040bf1bd65c75796c116d541`.
They record an eight-declaration fragment moved unchanged to
`Applications/Sequences/Partition.lean`, same-signature Selection adapters,
and the entire `sorted_partition` suffix retained unchanged.

This source pass read the complete candidate/addendum/compatibility records,
not that candidate through Git. Its recorded shared-core identity is
3,840 bytes / 87 lines, SHA-256
`c83144cda94133662be7537fa9c2e8e7870f4959c55c78526d1a62e11fe1f56b`.
The parallel API assessment owns direct retained-candidate source inspection.
XQ01 remains **uncompiled and unaccepted**; its source record is not a theorem
that can bypass integration or validation. Preserve the existing initial
prefix and shared integration addendum. No new extraction, import dependency
or source change is selected by this report.

## 6. Duplicate behavior and the limits of an optimization claim

On a nonempty all-equal list, both strict buckets are empty and the middle
block contains every tail occurrence. The displayed root therefore combines
two empty recursive results with the pivot and that entire block. This is
an exact control/value consequence of the printed recurrence, not a proved
numerical runtime formula. Mixed inputs exercise both strict branches and the
whole middle block; the independent case report derives the compact values.

The following distinctions matter even before a cost model is chosen:

- Filtering the full input and then adding the pivot again duplicates an
  occurrence; omitting the explicit pivot from tail-only buckets loses one.
- Replacing the middle block by a single representative loses duplicates.
- Recursively sorting `es` can preserve the final ordinary value but changes
  the prescribed recursion. It is not the source's direct middle-block step.
- Recursing on `x # es` can fail to decrease at all on an all-equal input.

The exercise describes three-way partitioning as an optimization because it
removes equal values from further recursive subproblems. That source mechanism
is retained. It does not assert pointwise lower runtime under every possible
primitive tariff, a worst-case `O(n log n)` bound on every input, or a new
randomized duplicate theorem. Three filters, the current two-partition pure
operation and the separately measured one-pass source realization need their
own execution/cost connections whenever costs are actually claimed.

The source here concerns ordinary ordered elements. A later keyed extension
must retain distinct payloads and establish any promised stability separately.
The stable partition comment alone is not a complete stable-sort theorem.
C02-107's existing selected non-insertion stable-sort solution is not expanded
to require keyed three-way quicksort merely because this algorithm is present.

## 7. Adjacent obligations and chapter-local completion

| Retained work | Boundary preserved by this report |
| --- | --- |
| C02-017–024 and the average/conditional/random-pivot plans | The ordinary first-pivot sorter uses `<` and `≥` tail buckets. Its actual execution, content/order proofs, duplicate qualifications and stated probability claims all remain. Three-way behavior cannot certify its distinct algorithm or cost. |
| C02-101 and the saved accumulator packet | The all-suffix cons-only worker remains a separate two-way exercise. Exercise 2.3 supplies no accumulator, append prohibition or tail-recursion requirement. |
| C02-103 / Exercise 2.4 | The printed tariff belongs to the two-way recursion, excludes append and charges its two full filters. It is not a `Tquicksort3` definition. Exact quadratic and asymptotic obligations keep their own scopes. |
| Existing XQ01 and Chapter 3 selection preparation | Shared partition values may be reused after their gates. The one-pass `length+1` invocation theorem belongs to its actual measured recurrence; it must not be assigned to the three-filter or two-partition program through output equality. Selector pivot policies, dispatch/rank and median-of-medians remain outside this exercise. |
| Other C02 rows, including C02-108–112 | All insertion, merge, natural-run, stability, builder and exercise obligations remain mandatory. No inventory row is rewritten, accepted or narrowed. |

After accepted Chapter 1 and the retained initial Chapter 2 sequence, the
existing chapter workflow can connect the actual prescribed sorter, termination,
content/order proof and small public-theorem cases. Shared source dependencies
must have their own matching acceptance evidence. Preserve original histories
and Selection's established interface; do not import the complete selector
merely to reuse an independent partition fragment.

The same eventual immutable Chapter 2 candidate still needs the applicable
focused/full guarded validation, exhaustive audit, independent Standards and
Spec review, and immediate candidate verification before acceptance. This is
not a new review loop or an additional gate. The source assessment found no
printed defect requiring a correction or weakened mathematical statement.
Ordinary elaboration, actual public-API use and integration are future work.

## 8. Exact preserved planning records

All paths below are relative to `fdsa-control/`. Ordinary byte identities were
read directly; prior records were not edited. The original/current C02-102 row
was additionally compared as text and found byte-identical.

| Record | SHA-256 |
| --- | --- |
| `reviews/source-inventories-before-scope-repair/chapter02-obligations.md` | `edba53049bb481f2fe21805f6e8a4ccc46ffec1e9b5fa8cb16b7804e446c832d` |
| `research/chapter02-obligations.md` | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |
| `research/chapter02-reuse-plan.md` | `ad652aa94f5cb4e0d00db58ffc8a7411c41deb582f35979a860a25c7d3c3454a` |
| `reviews/chapter02-requirements.md` | `f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36` |
| `research/quicksort-average-proof-plan.md` | `ca2090accf91ac662f2738486f7590e8b29968be524794e9356257d5f918dc46` |
| `research/quicksort-conditional-mean-preflight.md` | `464af5974d485823b7ecb76b7546ad793ed860fbf947afdb03ef11d91b25b66c` |
| `research/random-pivot-api-preflight.md` | `91d34b4c86d315935f0df98023cf382fe3d141e8ab7d748baf9fdc64738a0ed0` |
| `research/quicksort-accumulator-source-readiness.md` | `ce8c019bfe437bbdb71e5863119469a67c0f0d1a7961a3c0f879566731025eba` |
| `research/quicksort-accumulator-api-readiness.md` | `aeec34427e96f45ede40f9631a201a443f1eded796abf49a04fd861d17f4572f` |
| `research/quicksort-accumulator-case-readiness.md` | `6251ba2623d7988496be3e54dbdea8085f878810db276f7fec673429319f09f0` |
| `reviews/three-way-partition-candidate.md` | `96264044d5adef8a13f771d84a2153ae753c0b0e855d9306ed0f9e3409460d7c` |
| `reviews/partition-shared-integration-addendum.md` | `99a64a6db17c7114e98cca6087e440af4b4e9872962c6df6885ba0b8e1e4f3e2` |
| `reviews/three-way-partition-source-identities.json` | `c65556b40f31c48cc3df3321e02256a007cd8c1b3dea571b7b3ec7e1ac1dc1c3` |
| `reviews/three-way-partition-compatibility-reading.json` | `e5ba9687cc5215090d252d09cb1a7ed113381a7d05b0c6dd39303c0cd8a0faea` |

## 9. Applicable notice and final limits

Attribute the printed exercise and chapter to Tobias Nipkow and Christian
Sternagel, and the inspected ordinary Isabelle sorting source to Tobias Nipkow.
The exercise equations are source evidence, while the proof routes above are
reconstruction proposals. No whole book or long prose extract is incorporated.
The following exact notice accompanies the separately pinned Isabelle source
used for the ordinary-algorithm comparison and future source reuse. It is not
an assertion that the book itself is distributed under that software license.

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

Only this assigned source-readiness report was authored. No Lean source,
previous report, requirement, inventory, tracker, ref, worktree, compiler,
checker, project hash helper, active output, cache or remote item was changed
or operated on beyond the permitted static source/control text reads. No
algorithm has been implemented or validated by this preparation, and no
chapter or shared unit is accepted.
