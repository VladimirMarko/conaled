# Uniform concatenation and full-fold consumers

Issue #468 implements the uniform-concatenation part of #459 residual R1.
The [native contract](uniform-concatenation-contract.md) was frozen before the
new theorem layer. Current executing list operations remain unchanged.

## Executions and observations

`Resources.ListFusion.concat1` appends each block to the recursively flattened
suffix. `concat2Acc` appends the next block to the current accumulator, and
`concat2` starts that accumulator empty. Both use the actual shared
`Resources.ListAppend.weighted 1 1` recursion. Their value theorems preserve the
ordered flattened list; `prefixMass` records the lengths of the left operands
that are copied. The new theorems derive costs from these existing executions.

For m blocks each of length n, the producer equations are:

| Observation | Exact equation |
| --- | --- |
| Flattened length | m*n |
| Prefix mass starting at k | 2*prefixMass + m*n = 2*m*k + m*m*n |
| Right producer work | 2*m*n + 2*m + 1 |
| Left producer work | work + m*n = m*m*n + 2*m + 1 |
| Left producer with accumulator length k | work + m*n = 2*m*k + m*m*n + 2*m + 1 |

The additive form avoids truncated natural subtraction and covers zero
parameters. `concat1_uniform_theta` supplies bounds with constants 2 and 5
for m,n at least one. `concat2_uniform_theta` supplies the multiplied lower
bound m*m*n ≤ 2*work and upper bound 3*m*m*n for m at least two and n at least
one. These are explicit finite inequalities uniform in both parameters,
not a separately introduced asymptotic relation or an optimal-constant claim.

`foldLeftConcat` adds only a composition: existing `concat2` followed through
`Resources.bind` by the existing full `ListExecution.foldr`. The original
right pipeline is `ListFusion.foldConcat`. Their values equal the independent
fold of `xss.flatten`; both producer and consumer costs are included. At
combining price c, the right pipeline costs (3+c)*m*n+2*m+2 and the left
pipeline costs (m*m+c*m)*n+2*m+2. `uniform_fusion_saving` consumes the existing
`fold_concat_fusion_saving` theorem to retain the saved 2*m*n+1 work without
reproving its induction.

[The importing example](../../Examples/UniformConcatenation.lean) folds cons
over [[1,2],[3,4]] to recover [1,2,3,4] in order. Its bills 22 and 18 follow
through the general pipeline theorems. The same client consumes the fusion
saving and the arbitrary-accumulator equation. `uniform_bounds` instantiates
both general bounds together while quantifying both sizes.

## Boundaries and counterexamples

Empty outer input costs one. Empty blocks retain the outer bill 2*m+1. A
single left block costs three independent of its size; the multiplier-indexed
Nat-list witness refutes an unrestricted positive lower bound proportional to
payload length. The full fold after that producer still costs (1+c)*n+4.
This boundary does not imply that consuming the entire payload is constant work.

Length patterns [1,3] and [3,1] have identical block count and flattened length
but left work 7 and 11. `size_summary_cannot_recover` proves there is no function
of just those two summaries giving the left bill for every finite block list.
It keeps the existing executor and both concrete inputs. Three length-two
blocks tie at producer work 19; neither association is a strict improvement on
every finite input.

All counts concern declared dispatch, copy and combining work. The interface
does not measure callback execution, arithmetic instrumentation, physical
allocation, GHC demand or runtime. The bound constants have no machine-time
interpretation.

## Selected-source dispositions

The recovered external source commit is
`059fccc9b409d7ce01361daef9ca17483a343218`. The inspected archive member is
`project/adwh-lean/ADWH/Chapter02/UniformConcatenation.lean`, SHA-256
`e0b8754811dd560e6cf804b4cc5320639ae1306f5d5779c2e096dff3eafee5c9`. The source is evidence for useful mathematics rather than
an authority for current interfaces. Its theorem proofs are adapted to the
existing native owners; no second list executor or mass definition is added.

| Recovered declaration | Current disposition |
| --- | --- |
| `Uniform` | Same finite equal-block-length predicate in `Resources.UniformConcatenation`. |
| `mass_uniform` | `length_flatten_uniform` uses native flattened length rather than a parallel mass recursion. |
| `prefixMass_uniform` | Retained against existing `ListFusion.prefixMass`, including arbitrary starting k. |
| `concat1_uniform_exact` | Retained against existing right executor/work theorem. |
| `concat2Acc_uniform_exact` | Retained with arbitrary actual accumulator. |
| `concat2_uniform_exact` | Retained as the empty-accumulator specialization. |
| `concat1_uniform_theta`, `concat2_uniform_theta` | Retained finite uniform inequalities with explicit domains. |
| `empty_blocks_exact` | Retained and used by the public example. |
| `concat2_single_block`, `single_block_lower_obstruction` | Retained, with Nat witnesses for the obstruction; extended by the full-fold contrast. |
| Source examples, three blocks of size two and three empty blocks | Retained through `association_tie` and the generalized `empty_payload`. |

The maintained implementations and proof dependencies are
`Applications/Resources/UniformConcatenation.lean`, existing
`ListFusion.concat1_work`, `concat2Acc_work`, `concat1_value`, `concat2_value`,
`ListExecution.foldr_work`/`foldr_value`, and `fold_concat_fusion_saving`.
New pipeline proofs use measured bind and those public results. The source
prefix-mass induction and finite arithmetic proofs are adapted locally; no
new shared measurement or growth framework is needed.

The preserved Haskell source `project/sources/adwh/code/part0/chap1.hs`,
physical lines 41–43 under LINE 194, gives foldr/foldl append definitions.
[Accepted source validation](adwh-useful-coverage-validation.json) records
its official-code correspondence and archive hashes. This task inspected the
preserved bytes rather than performing another web verification. Full printed
Chapter 1/2 evidence remains incomplete. The chosen cost prices and derived
uniform equations are checked formal-model claims, not independently verified
quotations of unseen book text. Licensing and whole-book coverage remain #149.

## Validation and remaining ownership

The focused example build checks the new producer theorem layer and actual
pipeline clients using private project outputs and pinned dependency packages.
Parent orchestration owns the exact integrated full build, exhaustive proof
audit and independent Standards/Spec review. Focused compilation is not a
substitute for those gates.

Statement review checks arbitrary element/accumulator domains, joint size
quantification, nondegenerate lower-bound hypotheses, both execution bills,
and the distinction between producer and consumer demand. Uniform blocks give
inhabited examples; nonuniform lists and single blocks reject stronger claims.
The order-sensitive value result is independent of cost summaries.

Best/worst takeWhile, reverse/head growth and all other #459 families remain
with that issue. This task closes neither R1 nor Chapter 2. No major
architectural adoption or migration is proposed.
