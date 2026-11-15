# C03-057 generic pivot applications — source and case assessment

Candidate: `9cf01df8f01eb73ec5a2020995d90bb6b6eaba84`.
Tree: `4a04531393a50206cb1fe73cfbcc77511172ceeb`.
Stage base: `7758fdcd1d46cee392eee155d74311aeb45322a5`.
Whole Chapter 3 review base remains `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

## Scope and validation status

This bounded C03-057 continuation adds only `Examples.GeneralMedianBounds`, consuming the existing general theorem in `Applications.Selection.MedianOfMedians`. The complete requirement is Exercise 3.8(1), p.44, in `fdsa-control/research/chapter03-obligations.md`, frozen SHA-256 `eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed`. All 83 rows remain the joint Chapter 3 scope.

The mathematical general theorem is already present and focused-checked as `Applications.Selection.medianOfMedians_count_bounds`. This slice connects it to actual partition bucket lengths and exercises its arbitrary-size contract through concrete and parameterized applications. It introduces no alternate chunking, median policy, counting convention, scalar recurrence, or source-cost observation.

There are 27 new public declarations and one named private proof helper. All previous 14 source files and 323 author public headers are byte-identical. The prior counterfamily focused pass was fully read at `319267` and recorded in `counterfamily-focused-success.json`; all its failure/correction history remains preserved.

This successor has not been compiled by the author. No coordinator terminal result has yet been received for it. The complete source, every public/private source header and every example expectation have been assessed, but actual elaborated types, focused compilation, full composed candidate check/audit, independent Standards and Spec reviews, and immediate verification before integration remain pending. The 27-name explicit-@ program is preparation, not emitted-type evidence. Its lexical source-context inventory deliberately does not assume that every declared variable survives as a parameter.

## General contract reused

For any `LinearOrder α`, any natural group size d>0, any input xs, and any actual successful result `medianOfMedians d xs = some p`, each strict occurrence count is bounded by

`(d/2)*m + (d-d/2)*(m/2)`, where `m = xs.length ceilDiv d`.

Both divisions by two are natural floors and the chunk-count division is the existing natural ceiling. The theorem has no distinctness, oddness, parity, full-final-chunk, or d<=length hypothesis. The count is over occurrences, so repeated equal values belong to the equal bucket and do not enter either strict side. A successful result already supplies input membership; the new existence application makes that successful premise available on every nonempty input with positive d.

The d=1 specialization and d=5 source ceiling applications already have connected cases in the preserved `Examples.MedianOfMedians`. They are reused as existing evidence rather than duplicated here. The new d=3,4,6 declarations only evaluate literal group-size coefficients in this same bound; they make no recurrence or runtime claim. Root owns the separate C03-058 scalar argument.

## Complete source statement assessment

| Declaration(s) | Intended mathematics, hypotheses and connection |
|---|---|
| `partition_bounds` | Bounds the lengths of the actual `partition3` lower and greater buckets by exactly the same q*m+(d-q)*(m/2) expression. The public partition/filter equality and count/filter-length law transport the existing occurrence theorem. The equal bucket remains separate. |
| `nonempty_input_has_bounded_pivot` | For every positive size and nonempty input, provides an actual successful pivot, its input membership, and both partition bounds. `medianOfMedians_pivot_valid` supplies the witness; `partition_bounds` supplies the bounds. No default inhabitant or supplied pivot is required. |
| `three_group_bounds` | Literal d=3 specialization: q=1, so each strict side is at most m+2*(m/2). The original successful-pivot premise remains explicit. |
| `four_group_bounds` | Literal even d=4 specialization: q=2, so each strict side is at most 2*m+2*(m/2), using the existing lower-median convention. No odd-size strengthening is introduced. |
| `six_group_bounds` | Literal even d=6 specialization: q=3, giving 3*m+3*(m/2). This is a value/count upper bound, not a claim about sufficient recurrence contraction. |
| `constant_input_pivot` | For every positive d and n, the actual pivot of n copies of a is a, over arbitrary `LinearOrder α`. The proof uses successful input membership and membership in a replicated list; it does not assume all chunks are full. The supplied element a is the data value, not a global bottom/top or default inhabitant. |
| `constant_input_strict_counts` | Both strict counts about a in n copies of a are zero, including n=0. Unlike the successful-pivot theorem, this count equality needs no positivity premise. |
| private `chunkMedians_eq_heads` | A proof adapter only: if the actual payload median agrees with `headD 0` on every actual nonempty chunk, the attached map equals the ordinary head map. The hypothesis is explicitly proved for every chunk in both finite uses. The helper does not claim that arbitrary medians equal heads and does not replace the public pivot algorithm. Its complete type/body are included in source review and full audit scope. |
| `oddInput`, `evenInput` | The explicit seven- and nine-element inputs given below. Both contain duplicates and have a singleton final chunk for the stated size. |
| `odd_chops`, `even_chops` | Exact outputs of the existing `chop` operation on those inputs. The proofs use kernel computation on concrete ordinary list data. |
| `odd_chunk_count`, `even_chunk_count` | The exact natural ceiling chunk count is three, derived from the actual chop equality and public `length_chop`. This retains the short chunk instead of replacing ceiling division by truncating division. |
| `odd_medians`, `even_medians` | Exact payload median lists. Each actual chunk is classified from the proved chop equality; the known payload median follows from duplicate-aware occurrence-rank uniqueness and concrete count bounds. The private attach-map helper then transports those local equalities. No reduction through an opaque payload median is assumed. |
| `odd_pivot`, `even_pivot` | The actual mathematical pivots are respectively two and three. Each proof uses the public median-of-medians/rank equivalence with the corresponding exact median list. |
| `odd_strict_counts`, `even_strict_counts` | Exact occurrence counts about those already identified pivots, independently computed from the concrete original input values. |
| `odd_bound_from_general`, `even_bound_from_general` | The displayed numerical upper bounds five and eight follow from the general group-size theorem with actual pivot evidence and exact ceiling chunk count. These proofs do not use the finite exact side counts as a substitute for exercising the general theorem. |
| `odd_partition_values`, `even_partition_values` | Exact lower/equal/greater list outputs of the existing stable partition value operation. Equal occurrences are visibly retained twice. These equations concern values, with no one-pass execution-cost claim. |
| `odd_partition_bounds`, `even_partition_bounds` | The same bounds five and eight are applied through the new general partition-length theorem and the checked numerical chunk-count facts. |
| `integer_ties_with_short_chunk` | Over Int, seven copies of -4 with group size six produce actual pivot -4, a six-element block plus a final singleton, and two zero strict counts. This instantiates the arbitrary-type, arbitrary-size constant-input results and computes the actual chop. |
| `integer_tie_bound` | Applies the d=6 generic bound to that actual negative-Int pivot. Here m=2 and the conservative bound is nine. This can exceed the input length seven on such a small input; the exact zero counts and generic upper bound are compatible. |

## Independent finite expectations

For the odd case, input `[0,0,1,2,2,3,9]` is chopped into `[0,0,1]`, `[2,2,3]`, and `[9]`. Its chunk medians are `[0,2,9]`, hence the pivot is 2. Three original entries are below 2, two equal 2, and two are above 2. Since m=ceil(7/3)=3, the general bound is 1*3+2*floor(3/2)=5 for each strict side.

For the even case, input `[0,0,1,2,3,3,4,5,9]` is chopped into `[0,0,1,2]`, `[3,3,4,5]`, and `[9]`. The lower medians of the size-four blocks are 0 and 3; the third median is 9, so the pivot is 3. Four entries are below it, two equal it, and three are above it. Here m=ceil(9/4)=3 and the general bound is 2*3+2*floor(3/2)=8.

In either case, dropping the final singleton would change the median list and its lower central value, so the exact chop and pivot cases genuinely expose retention of the short final chunk. The even case also exposes the lower-median convention inside size-four blocks. The numerical bound proofs retain their connection to the public general theorem even though the concrete side counts are separately available.

## Remaining boundaries and integration preparation

There was no static mathematical correction to the expected statements in this slice. Actual Lean elaboration remains the next source of diagnostics; no success is inferred from source inspection. No original source, header, type input, completed record or accepted branch was changed.

The only new root import/reconstruction-map entry to compose is `Examples.GeneralMedianBounds`. No shared root or global control/ticket/review file was edited. The sole focused target is this module. Existing six type programs remain bound by unchanged source identities; the new public program brings this author's inventory to 350 public names. Seven named private helpers now remain in the combined audit scope. These are author-source counts, not whole-project audit counts.

C03-055 and the algorithmic part of C03-058 await the exact checked nested-worker handoff. Root's C03-058 scalar work is excluded. Root has additionally planned C03-078/080 deterministic policy work after this candidate is focused and explicitly released; neither later assignment was started, and no unpublished worker or other-branch source was imported. Every whole-Chapter-3 gate and the complete 83-row scope remain mandatory.
