# Median reduction: source assessment and bounded handoff

Candidate `24b74c65e2b907f1a4cd8b8c72e22bba8f315eea`, tree
`1a412f79a46a2850a199a6a8d8c88c4826e589ec`, is an **uncompiled development
candidate** for C03-053–054. The fixed stage base is
`979c4fcb1719a779ffda7462a6df385e876b7d4c`; the original whole-Chapter-3 review
base remains `2da5708478a1d943a9214b5b386ec2db16cd9eca`. All 83 frozen
requirements remain in scope. C03-055–058 remain assigned for later work.

Only the three approved new modules changed: `Applications.Selection.MedianReduction`
(21 public names), `Applications.Resources.MedianReduction` (17), and
`Examples.MedianReduction` (27). There are 65 new public declarations and no
new private helpers. All nine earlier source files remain byte-identical to the
new starting-state manifest, including root's three proof-only FixedRank fixes.
No accepted branch, shared imports/docs, canonical controls, tooling or
dependency files changed. This slice imports no pending XR, scalar-F or nested
selector source. The old FixedRank source pass is retained as a focused result,
not full Chapter 3 acceptance or validation of these new modules.

## Construction and mathematical statement assessment

For nonempty `xs` of length `n`, `reduceToMedian k xs` computes both actual input
extrema, then builds

```
A = n - 1 - 2*k
B = 2*k + 1 - n
replicate A minimum ++ (xs ++ replicate B maximum)
```

Subtraction is natural subtraction. The zero-based rank `k` is unchanged at the
input interface. `extrema` reuses the proven actual minimum loop twice, with the
order reversed on the second traversal. Its specification includes both
membership and bounds, and `extrema_eq_of_bounds` identifies concrete results
from independently checked extrema. No sentinel, `Inhabited`, distinctness,
global minimum or global maximum is assumed. Generic padding and replication
require no order; the rank and extrema laws use `LinearOrder`.

`ranked_padExtrema` is the central value bridge. It requires an original
`RankedAt xs k a`, a lower padding value at most `a`, and an upper padding value
at least `a`. It proves rank `k+A` after padding. The proof uses strict counts:
padding may equal `a`, so it contributes at most its count to a strict side.
There is no false claim that every minimum copy is strictly smaller. The actual
input extrema supply the two inequalities using the selected occurrence's
membership. The selected value is not assumed to be a median.

The arithmetic lemmas prove `A+n+B = 2*(k+A)+1` and, for `k<n`, `A+B ≤ n-1`.
The construction consequently has odd length, central index `k+A`, and valid
output length at most `2*n-1`. Nonempty input gives nonempty output for every
rank. The arithmetic identity itself also holds at `n=0`; the actual algorithm
separately extends empty input to empty output, so its nonempty/odd/center
theorems retain their nonempty-input premise.

The rank-shift theorem connects to the central lower-median rank. For valid
`k`, `reduceToMedian_value` equates the existing optional lower-median result
under any valid pivot policy with the actual fixed-rank selector. Its proof
obtains a ranked occurrence from `selectFixed_spec`; it does not assume an
output exists. The payload adapter uses the established proof-carrying
`lowerMedianValue`. The final `reduceToMedian_spec` combines nonemptiness with
the unchanged public one-based rank `k+1`. These bridges cover duplicates and
both padding directions without strengthening the book's domain.

## Actual source costs and quantifiers

The measured reduction executes the following work with the Chapter 1
recursive-entry convention. Primitive arithmetic, comparisons and min/max
carry zero observation; each declared source function entry costs one.

| Component | Actual source count on nonempty input |
|---|---|
| Original length traversal | `n+1` |
| Both extrema traversals and extrema helper | `2*n+1` |
| Build both pads, append upper pad to input, prepend lower pad, helper | `2*A+B+n+5` |
| Reduction entry | `1` |

Replication is an actual recursive measured implementation with erasure to
`List.replicate` and exact cost `count+1`. Both appends reuse the existing
measured append with its own traversal charge. The association in the pure
constructor matches this execution. Extrema search and length are not assigned
zero cost based on known specifications.

The total nonempty count is exactly `4*n+2*A+B+8`. Under `k<n`, the padding
bound gives `6*n+6`, with explicit witnesses 6 and 6 preceding both input and
rank quantifiers. This is reduction preparation cost, before a subsequent
median invocation, and does not claim Lean runtime, allocation, or the total
cost of the eventual median solver. Empty preparation returns `([],1)`.
Validity matters: the retained singleton invalid-rank example costs 14 rather
than the valid-domain bound 12. A general rank-zero example shows that the
displayed affine bound is attained on every nonempty input in this model.

## Connected cases and independent expectations

| Cases | Intended fact and connection |
|---|---|
| `extrema_mixed`, `extrema_tied`, `extrema_integer` | Input extrema are (1,7), (3,3), and (-2,7). Use the public bounds/membership characterization with independently checked finite inequalities. Negative integers expose reliance on actual input values. |
| `extrema_execution`, `replication_execution` | The mixed extrema search costs 9; three copies cost 4. Use exact measured identities. |
| `tied_padding_rank` | Seven equal values have the original second occurrence shifted to index 3, although the strict lower count stays zero. Uses the generic rank-shift theorem. |
| `first_padding`, `last_padding`, `lower_middle_padding`, `upper_middle_padding` | For [4,1,7,1], requested ranks 0,3,1,2 add respectively three minima, three maxima, one minimum, one maximum. These cases connect the actual constructor to the established extrema result. |
| `already_central`, `singleton_unchanged`, `empty_median_failure` | A central odd rank needs no padding, any singleton remains itself, and empty preparation preserves optional median failure. These expose actual constructor and existing failure semantics. |
| `lower_middle_median`, `upper_middle_payload` | The duplicate lower middle value is 1 and the upper middle value is 4. Use the reduction's policy-independent value theorem and its proof-carrying payload adapter. |
| `reduction_shape` | Combines nonemptiness, odd length, bounded length and exact center for arbitrary valid input; discharges nonemptiness from the valid-rank premise. |
| `padding_execution`, `first_execution`, `last_execution` | Padding alone costs 15 in the first-rank case; full preparation costs 30 for the first rank and 27 for the last. Use measured erasure and exact cost identities. |
| `central_execution`, `singleton_execution`, `empty_execution` | No-padding preparation still costs 20 on [4,1,1]; singleton costs 12; empty input costs 1. These prevent treating omitted padding or known extrema as free preparation. |
| `first_rank_attains_bound` | Every nonempty rank-zero input costs exactly `6*n+6`, independently of values and duplicates. Derives the family from the exact cost and positive length. |
| `measured_reduction_contract` | Composes measured erasure, public selection correspondence and the uniform source bound in one application for arbitrary valid pivot policies. |
| `invalid_rank_values`, `invalid_rank_cost_exceeds_valid_bound` | Rank 1 of [7] is invalid: the padded list has median 7, the original selector returns none, and preparation costs 14 > 12. These preserve the necessity of the valid-rank hypotheses. |
| `uniform_reduction_constants` | Specializes the same two globally quantified witnesses to Nat; they remain independent of rank and input. |

Every source claim and these case connections has received this author-side
statement assessment. Elaborated types and independent Standards/Spec review
are still pending; source-header inspection does not replace them.

## Evidence and next gate

Full source readbacks: `fcb9d0`, `219ab0`. The precommit record and actual
commit output were fully read in `8797de`. Static checks verified exactly the
three assigned new files, all nine old source identities, absence of forbidden
proof constructs in new source, and `git diff --cached --check` exit zero.
No Lean/Lake, cache, environment, or GitHub action occurred.

`MedianReductionStatements.lean` queues every new public name with explicit
`#check @`; `median-reduction-inventory.json` retains every source header and
context. Root should compile the three exact module targets in dependency
order, preserve actual terminal evidence, and return any concrete correction
under the same scope. The shared public imports and reconstruction-map entries
remain integration-owner follow-ups. Full composed candidate validation,
exhaustive audit, both review axes and immediate verification remain mandatory.
