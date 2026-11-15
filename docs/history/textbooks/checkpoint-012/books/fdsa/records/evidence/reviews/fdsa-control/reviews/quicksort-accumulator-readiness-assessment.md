# C02-101 accumulator quicksort — bounded readiness assessment

Recorded 2026-11-03 UTC. This assesses three stopped planning reports. It is
not a source implementation, new shared unit, scope freeze, final Standards
or Spec review, chapter activation or acceptance.

## Complete reports and root readback

| Report under research/ | Bytes / lines | SHA-256 |
| --- | ---: | --- |
| quicksort-accumulator-source-readiness.md | 18,282 /294 | `ce8c019bfe437bbdb71e5863119469a67c0f0d1a7961a3c0f879566731025eba` |
| quicksort-accumulator-api-readiness.md | 21,912 /341 | `aeec34427e96f45ede40f9631a201a443f1eded796abf49a04fd861d17f4572f` |
| quicksort-accumulator-case-readiness.md | 19,851 /363 | `6251ba2623d7988496be3e54dbdea8085f878810db276f7fec673429319f09f0` |

All three authors completed full final report readbacks and stopped. Root
read all294 source-report lines and all341 API-report lines. Root read the
complete358-line case snapshot at SHA-256
`415f4917a8dd28424c723465e9215d47182b0cd74e5c9e0c28a39084fa5f672e`, then every
exact delta to the final363-line report. Those deltas add the stopped API
report identity/correspondence, make the closing action description precise,
and clarify that this proposal is not frozen as the only possible solution.
No case, independent numerical expectation or mathematical claim changed.

Root also read the exact retained Lean filter-length and append declarations,
and the complete existing128-line Sort and37-line SourceMerge modules. The
actual library supports the stated proof route, while the existing sorters
do not supply the source's first-pivot quicksort by renaming. No project
compiler or checker was run for this preparation.

## Findings and disposition

No concrete source-convention, mathematical or inspected-API obstruction was
found. Implementation stays within the existing Chapter2 work after its
prerequisites; no separate shared abstraction or new review loop is selected.

1. Exercise2.2 asks for cons accumulation without append and the universal
   equation quicksort2 xs suffix = quicksort xs ++ suffix. The book does not
   supply the worker recurrence or a numerical cost formula. Sorting.thy
   supplies only the ordinary first-pivot recursion and its correctness.
   The nested worker is a proposed exercise solution, not recovered code.
2. Its filters act on the tail, with strict-less elements left and pivot<=y
   elements right. Equal occurrences remain. Both actual recursive calls
   decrease first-input length by the existing filter bound, independently
   of the suffix. No desired output theorem is needed to justify termination.
3. The induction must quantify every suffix for each smaller input. The left
   IH is instantiated at pivot :: q2 right suffix, then the right IH rewrites
   its occurrence there. Ordinary cons/append/associativity facts complete
   the value calculation. Ordinary sort correctness is separately needed
   for sorting corollaries, not as a premise of this simulation.
4. The independent mixed input [2,1,2,3,0] and suffix [4,0,2] produce
   [0,1,2,2,3,4,0,2]. The literal filters are [1,0] and[2,3]; the actual
   left-call suffix is[2,2,3,4,0,2]. Wrong nesting produces
   [3,2,2,1,0,4,0,2]. The same suffix gives compact empty, singleton and
   all-equal cases. Root checked these exact mathematical calculations.
5. The mixed root/left-call total argument lengths are8 and8, so that sum
   is not a decreasing measure. First-input length decreases5 to2. A base
   equation plus every empty-suffix case is logically weaker than the
   required universal law; the retained countermodel demonstrates it.
6. Defining the desired value using append would pass extensional cases but
   violate the implementation restriction. The eventual actual body and
   connected public equation must be inspected. Arbitrary suffixes remain
   unsorted when supplied that way; even a sorted suffix needs cross-order
   premises for whole-output sortedness. Those premises cannot narrow the
   unconditional exercise value law.
7. The nested right call supplies no full tail-recursion/constant-stack
   conclusion. No additional runtime, allocation, comparison, probability,
   cost-executor or performance-comparison requirement is introduced.
   All separately required ordinary quicksort tariffs and random/average
   execution bridges remain intact.

## Scope and recovery boundaries

The source report retains the exact book/Isabelle identities, distinguishes
their revisions and includes the complete1,673-byte applicable source notice.
Root checked that the current inventory still contains all112 distinct C02
rows and that the historical frozen snapshot still contains107. The original
requirements, reuse plan, scope reconciliation and both exact-prefix reports
retain their recorded identities. No source/inventory/prior report was edited.

The initial integration prefix remains exactly
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`, after repaired Chapter1 acceptance.
The later c28 potential addition is not included by this planning. The actual
ordinary quicksort and its source correspondence must exist before this
exercise worker is implemented against it. All27 chapters and Appendices A–C
remain required; no inventory row or unit is accepted here.

Checkpoint0064 will preserve these preparation records, the successful0063
receipt/content inspection/network-recovery evidence, and all existing source
refs/history/tracking. It will not supply compilation or independent approval.
C1 remains active; its original sole validator and all final gates are intact.
