# C03-056 infinite counterfamily — source and case assessment

Candidate: `cafc71bef2e2779407944cb04089b9b3b14a13dc`.
Tree: `8ede72c00df8a44b50fcedb49c219d9090c7df26`.
Stage base: `11480d46b4f8f99eb33bdc4b34759031af17c9f0`.
Whole Chapter 3 review base remains `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

## Scope and status

This bounded candidate addresses C03-056, Exercise 3.7, p.41, in the frozen 83-row inventory at `fdsa-control/research/chapter03-obligations.md`, SHA-256 `eda51a6cd8bac41df1f97ab03386b003e1cae5ed0db5320414265027074360ed`. The constructive plan is also recorded in `research/selection-proof-plan.md`, section 10. The requirement explicitly permits the equivalent integer inequality in place of dividing by the input length.

Only two new source modules are added: `Applications.Selection.MedianCounterfamily` and `Examples.MedianCounterfamily`. Their 25 and 17 public names respectively are exhaustively inventoried. There are no new named private helpers. The local `hm` argument in `chunkMedians_family` remains part of that proof and is in review scope. All previous 12 source files and every prior candidate/failure record are preserved.

This is an uncompiled development candidate. No author Lean/Lake, emitted-type capture, cache action, full candidate check, proof audit, independent review, acceptance or integration has occurred for this slice. Static source/header review and `git diff --cached --check` are preparation evidence only. Root owns the qualified serial check. The explicit-@ input includes all 42 names; its source-header list is not a claim about elaborated types.

The preceding 65-name MedianReduction slice passed the three requested focused targets at the stage base. Its actual closed result is preserved separately in `median-reduction-focused-success.json`. That success does not qualify this new slice or satisfy whole-Chapter-3 acceptance.

## Construction and independent calculation

For every natural index i, take i copies of the block `[0,0,0,1,1]`, then i+1 copies of `[1,1,1,1,1]`, flatten those full blocks, and append `[0]`.

There are 2*i+1 full blocks. Each has length five, so their combined length is 10*i+5; the final singleton produces input length 10*i+6. Each low block contains two positive entries and each high block contains five. The final singleton contributes none, giving 2*i+5*(i+1)=7*i+5 greater-than-zero entries.

The actual chunk list consists of exactly those full blocks followed by the singleton `[0]`: the full prefix length is divisible by five. The low-block median is zero, the high-block median is one, and the singleton median is zero. The median list is `replicate i 0 ++ replicate (i+1) 1 ++ [0]`. It contains i+1 zeros and i+1 ones; its length is 2*i+2 and its lower central index is i. The rank contract therefore selects zero. This retains multiplicities, the lower-median convention, and the short final chunk.

Finally, 10*(7*i+5)=7*(10*i+6)+8. The integer comparison is strict at every index, including zero. Positive length is proved separately at every index, and length is strictly monotone over all pairs of increasing indices. This supplies an infinite family, not a finite experiment or an existential choice of unrelated inputs.

## Complete core statement assessment

All types here are natural-indexed lists of natural values; no ambient arbitrary ordered type, distinctness, or nonempty-input premise is smuggled into the universal family claim.

| Names | Intended statement and assessment |
|---|---|
| `lowBlock`, `highBlock`, `fullBlocks`, `family` | Concrete source data construction, with block order and the final singleton retained. These definitions have no selector or supplied pivot hidden in their input. |
| `fullBlocks_length`, `mem_fullBlocks_length`, `flatten_fullBlocks_length` | Exact full-block count, size of every member block, and flattened-prefix length. Membership is used only to establish the size of an actual block; this supports alignment rather than postulating it. |
| `family_length`, `family_positive`, `family_ne_nil`, `family_lengths_strictMono` | Exact length 10*i+6, universal positive length/nonemptiness, and strict growth for every i<j. There is no lower cutoff on i and no finite upper bound. |
| `chop_family` | Equality for the existing `chop 5` operation, proved via aligned append, full-block flatten reconstruction, and the positive-size singleton law. It does not define an alternative chop. |
| `lowBlock_median`, `highBlock_median`, `singleton_zero_median` | Payload medians of the three actual nonempty shapes. Their nonemptiness proof arguments are satisfiable concrete-list facts. Duplicate-aware rank/count bounds identify the payload by uniqueness; kernel computation is used only for those concrete count bounds. |
| `chunkMedians_family` | Exact list of payload medians of the actual chopped input. Its local head-value comparison is proved only for the three known nonempty shapes, then erased through the existing attach/map law. `headD` is merely an intermediate proof expression; it does not change the median policy or introduce an empty-chunk fallback into the public algorithm. |
| `chunkMedians_family_length`, `chunkMedians_family_count_lt`, `chunkMedians_family_count_gt` | Exact median-list length 2*i+2, zero entries strictly below zero, and i+1 entries strictly above zero. The lower strict count is zero for natural values; the greater count exercises the explicit median list and multiplicities. |
| `family_pivot` | Actual `medianOfMedians 5 (family i) = some 0`. It uses the public median-of-medians/rank equivalence and both strict count bounds, including the even-list lower central occurrence. Successful output is proved, not assumed. |
| `family_count_gt` | Exact count of entries strictly greater than zero in the original input. The proof counts the actual flattened blocks and the final singleton. |
| `family_excess`, `family_strict_seventy` | Exact equality with numerator excess eight, then the strict integer comparison 7*length < 10*greaterCount. Equality is used without truncated subtraction. |
| `family_pivot_strict_seventy` | The comparison for any p returned by the same deterministic pivot operation. Its successful-output premise is witnessed by `family_pivot`, so it is not vacuous. Option injectivity transports the proved pivot zero to p. |
| `infinite_family` | One explicit function witnesses strict monotone lengths and, for every index, positive length, a successful actual pivot, and the strict comparison against it. The existential function is `family`, not a choice axiom selecting unconnected examples. |

## Complete connected-case assessment

| Example names | Expected mathematics and public connection |
|---|---|
| `first_input` | At i=0 the low-block prefix is empty and the actual input is `[1,1,1,1,1,0]`; ordinary kernel computation checks the explicit construction. |
| `first_chops`, `first_medians`, `first_pivot` | Chunks `[[1,1,1,1,1],[0]]`, medians `[1,0]`, lower median zero. Direct applications of `chop_family`, `chunkMedians_family`, and `family_pivot` establish the connections. |
| `first_counts`, `first_strict_percentage` | Length six, greater count five, and the strict comparison. These consume the universal length/count/strict theorems. |
| `second_chops`, `second_medians`, `second_pivot` | At i=1 there is one low block, two high blocks, and a final singleton. Medians are `[0,1,1,0]`; the lower middle occurrence after ordering is zero. The same three public family theorems are instantiated. |
| `second_counts`, `second_has_duplicates` | Length sixteen and greater count twelve follow from the public count formulas. The explicit list is not distinct, checked by kernel reduction, making the lack of a distinctness premise visible. |
| `third_counts` | At i=2 the length is twenty-six and greater count nineteen, using the same formulas. No finite set of cases is used to justify the universal theorem. |
| `growth_at_every_index`, `positive_denominator_at_every_index` | Universal successor growth and nonzero denominators follow from the full strict-monotonicity and positivity results. |
| `book_ceiling_still_bounds` | The existing proved five-group ceiling bound is applied to every family member with `family_pivot`; the source's additive allowance remains valid. |
| `dropping_allowance_fails` | The unrounded exact 70-percent ratio bound fails strictly at every index. This is not a claim that the integer ceiling of 0.7*n fails. |
| `actual_pivot_comparison` | For any actual returned pivot, positivity and the strict comparison hold together, connecting the count to the operation's result. |

## Static review correction and semantic limits

The initial draft contained the word “ceiling” in a comment about the exact unrounded ratio bound. That wording was inaccurate: this family does not refute the rounded ceiling of 0.7*n. The comment was corrected before commitment, with unchanged mathematical propositions, and the exact diff is saved in `counterfamily-precommit-review-corrections.diff`. An unnecessary unformalized limit comment was removed at the same review. The record also preserves minor proof-form preparation changes; no compiler failure or successful elaboration is asserted for them.

This slice proves no execution-cost claim and does not substitute the mathematical pivot for the actual nested selection implementation. C03-057 still needs its connected generic-group applications assessed; C03-055 and the algorithmic part of C03-058 await the exact generalized worker handoff. Root separately owns C03-058 scalar group coefficients and sufficient affine majorants. No other branch was incorporated.

## Integration preparation and pending gates

Root should compose imports for both new modules and the reconstruction-map entry in the shared roots when assembling Chapter 3. Those shared files were intentionally left to their owner. Exact targets for development validation are `Applications.Selection.MedianCounterfamily` and `Examples.MedianCounterfamily`.

All 42 new names, all previous 281 author names, and six previous named private helpers remain in whole-scope review/audit coverage. The frozen 83-row Chapter 3 scope, actual emitted-type inspection, full composed candidate check and exhaustive audit, independent Standards and Spec assessments, and immediate candidate verification before local integration remain mandatory. No row is marked accepted by this source handoff.
