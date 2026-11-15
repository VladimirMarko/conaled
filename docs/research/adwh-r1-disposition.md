# R1 list-cost disposition

The selected recovered R1 family under #459 is accounted for by #468, #469 and
stronger existing generic head/reverse contracts. This disposition preserves the
useful mathematics without recreating historical wrapper names. R2–R7 remain
open under #459; whole-book evidence and licensing remain #149.

| Selected source claims | Current basis |
|---|---|
| Uniform concatenation equations, joint-size bounds and boundary obstructions | #468: [uniform-concatenation report](uniform-concatenation.md), actual executors and fold consumer. |
| Fixed-predicate takeWhile best/worst witnesses, attained extrema and eventual lower obstruction | #469: [takeWhile report](takewhile-extrema.md), actual producer and ordered prefix-fold consumer. |
| `head_theta` for any list family | Exact `ListExecution.head_work`, with no size or nonempty premise. |
| `reverse_all_input_bounds` and `reverse_theta` for a size-indexed family | Exact `ListExecution.reverse_work`, with the explicit size premise for the family comparison. |
| Head empty/nonempty observations | `ListExecution.head_value`; `Examples.ListFusionCosts.empty_selectors` and `source_selectors`. |

## Exact contracts and growth consequences

[The native executor module](../../Applications/Resources/ListExecution.lean)
already proves `(head xs).2 = 1` via `head_work`, and
`(reverse xs).2 = 2*xs.length+1` via `reverse_work`. Its value theorems retain
ordinary `head?` and list reversal.

For any given family `inputs : Nat → List α`, head work is exactly one at every
index. Positive coefficient one and inclusive threshold zero therefore witness
both comparisons with the constant-one function.

For positive list length, reverse's exact formula implies
`2*length ≤ work ≤ 3*length`. For a family explicitly satisfying
`(inputs n).length = n`, its work is `2*n+1`. Coefficient three from threshold one
witnesses `work ≤ 3*n`; coefficient one from threshold zero witnesses `n ≤ work`.
No replicate restriction or hidden dependence on list values enters this argument.

[Resources.isBigO_natCast_iff](../../Applications/Resources/Growth.lean) is the
checked bridge from eventual natural-count inequalities with a positive natural
coefficient to Mathlib Big O of their real casts. The checked
`Examples.ResourceGrowth.nat_upper_iff_isBigO` makes the inclusive `atTop`
threshold convention explicit. Applying those bridges to the displayed
arithmetic witnesses gives the two Big O directions; pairing them gives the
corresponding native Theta statement.

This last paragraph records a mathematical implication of checked general
results. The reconciliation introduces no newly compiled named generic
`head_theta` or `reverse_theta` wrapper. The exact contracts are the existing
Lean evidence; their displayed specialization and arithmetic explain why no
selected source mathematics remains missing.

## Consumers and boundaries

[ResourceGrowth](../../Examples/ResourceGrowth.lean) already checks actual
reweighted reverse executions, returned values, finite bounds and Theta through
`half_reverse_value`, `half_reverse_work`, `half_reverse_bounds` and
`half_reverse_theta`. Those examples use replicate inputs; generic coverage
comes from `reverse_work`, not from broadening their stated domain.
`half_reverse_nil` and `half_reverse_no_global_linear_bound` retain the terminal
charge and reject an all-index homogeneous linear upper bound.

[Examples.ListFusionCosts.reversal_digits](../../Examples/ListFusionCosts.lean)
is an order-sensitive reverse/fold consumer with value 2718 and bill 18.
`ListExecution.foldlViaReverse_work` and `foldlViaReverse_extra` include reversal
in the composed bill. [GuardedBuild](../../Examples/GuardedBuild.lean)'s
`buildHead_value` and `buildHead_work` retain the actual builder followed by head:
its work is the complete builder bill plus one. Constant head observation work
therefore does not imply constant work for producing its argument.

Empty reverse costs one, so `work ≤ C*n` cannot hold at n=0. Head still costs
one on an empty list and returns `none`. A size-n input family is an explicit
premise, not an existence claim over an empty element type. These source counts
exclude input construction unless explicitly composed, physical callback time,
GHC allocation and wall-clock performance.

## Provenance and scope

The recovered `ADWH/Chapter02/BestWorst.lean` member has SHA-256
`7e2398bfa506958644543e9dfddd827ae356731cfd5aa06c5645ba4baf1473c1`;
`ADWH/Chapter01/StructuralCosts.lean` has SHA-256
`19de70c91c4f64db5137b6ea3cdc12917021201c75418d6a58cffc4b012daba1`.
Both are under `project/adwh-lean/` in the preserved
[checkpoint-233 archive](../history/algorithm-design-haskell/checkpoint-233.zip).
The head branches and foldl-based reverse prices match the current native
execution contracts. Historical asymptotic wrappers are comparison evidence,
not an additional interface requirement.

The original #458 [validation record](adwh-useful-coverage-validation.json)
retains its historical baseline and checks. This subsequent reconciliation is
source/declaration review with explicit mathematical consequences, not a claim
of fresh Lean compilation or renewed source certification. The #468 and #469
reports preserve their own implementation scopes. Printed chapter evidence and
licensing remain incomplete under #149; accounting for R1 neither closes #459
nor certifies unseen book passages.
