# Exact takeWhile extrema and an executed prefix fold

[TakeWhileExtrema.lean](../../Applications/Resources/TakeWhileExtrema.lean)
derives sharp fixed-length producer bounds and an ordered downstream consumer
from the existing `ListFusion.takeWhile`, `Resources.bind` and
`ListExecution.foldr`. It supplies the takeWhile portion of #459's residual R1
under #469. [Uniform concatenation](uniform-concatenation.md) was delivered by
#468. At this child’s acceptance, generic head/reverse growth remained assigned
to #459. The subsequent [R1 disposition](adwh-r1-disposition.md) accounts for it
through stronger existing exact contracts; R2–R7 remain open. The source table
below preserves the child’s original scope.

## Fixed predicate, different demands

Every empty input costs one. A nonempty input costs at least two, and every
input of length n costs at most `3*n+1`, under unit dispatch/cell/test prices.
`full_upper` derives the sharp bound from the native work theorem and the
partition into accepted prefix and remaining suffix. A failed next element
cannot also be counted as an accepted cell.

One fixed predicate, Bool identity, attains both extrema at every size:

| Input | Returned value | Producer work |
|---|---|---|
| n copies of false | [] | 1 at n=0, otherwise 2 |
| n copies of true | n copies of true | `3*n+1` |

`best_minimum` and `worst_maximum` compare these witnesses with **every** Bool
list of the same length. They do not change the predicate to obtain each bound.
`best_positive` gives exact constant cost two; `worst_positive_bounds` gives
`3*n ≤ work ≤ 4*n` for n>0. The constants and threshold are explicit and uniform.
`positive_bounds` also supplies the finite upper bound for arbitrary predicates
and arbitrary input values of positive size.

An all-passing worst case does not supply a lower bound on all inputs.
`best_eventual_lower_obstruction` proves that for every natural multiplier C
and threshold N there is n≥N with `n > C*bestWork(n)`. It chooses
`max N (2*C+1)`, so the counterexample can occur arbitrarily late.
The importing example `rejects_eventual_lower` negates the corresponding
existential multiplier/threshold claim. Empty input also refutes an unqualified
zero-threshold upper bound `work ≤ C*n`.

## The consumer executes both stages

`foldPrefix c p f e xs` is the measured bind of the existing takeWhile executor
and the existing full fold. For arbitrary element/result types and combining
function, its value is the ordinary ordered expression
`(xs.takeWhile p).foldr f e`. With accepted-prefix length k, its work is

```text
(4+c)*k + 2 + (if xs.dropWhile p = [] then 0 else 1).
```

The producer contributes `3*k+1+failure`; the full fold contributes
`(1+c)*k+1`. The formula is proved from those actual executions, not used as
the execution definition. False replicate returns the seed, costing two for
empty input and three otherwise. True replicate returns the full ordinary
fold and costs `(4+c)*n+2`. At c=1 and n>0, that all-true witness lies between
`5*n` and `7*n`. These last bounds describe the all-true pipeline witness;
there is no separate claim of pipeline maximality here.

[The importing examples](../../Examples/TakeWhileExtrema.lean) use cons as an
order-sensitive fold. Predicate <3 over [1,2,9,4] produces [1,2] with bill 13;
exhausted [1,2] produces the same list with bill 12. The extra test of 9 explains
the difference. Empty input costs two and a false-first input costs three.
`foldPrefix_suffix_independent` preserves the **full measured pair** after an
all-passing prefix and an actual failed next element. It reuses native
`takeWhile_suffix_independent`, including both hypotheses, and transports the
equality through bind. Arbitrary changes beyond the failed element cannot
change either the folded value or its modeled bill.

These counts price declared source dispatch, produced cells, predicate calls
and fold steps. They do not measure physical predicate/function time, input
construction, GHC allocation, wall-clock time or general lazy semantics.

## Source dispositions

The recovered source is member
`project/adwh-lean/ADWH/Chapter02/BestWorst.lean` of the preserved
[checkpoint-233 archive](../history/algorithm-design-haskell/checkpoint-233.zip).
Its actual member SHA-256 is
`7e2398bfa506958644543e9dfddd827ae356731cfd5aa06c5645ba4baf1473c1`.
The prior external source revision is recorded in
[the recovered handoff](adwh-recovered-handoff.md). The following table accounts
for every selected takeWhile declaration and its examples.

| Recovered declaration | Current disposition |
|---|---|
| `takeWhile_full_upper` | `full_upper`, derived from current `takeWhile_work` and ordinary prefix/suffix partition. |
| `takeWhile_nonempty_lower` | `nonempty_lower`; current executor's true and false branches. |
| `takeWhile_linear_upper` | `positive_bounds`, with uniform constant 4 and threshold 1 for every actual input; a size-indexed family can specialize it. No historical `NatO` framework is restored. |
| `bestInput`, `worstInput`, `witness_lengths` | Same finite witness families and explicit length theorem over current lists. |
| `best_witness_run`, `worst_witness_run` | `best_run`, `worst_run`, retaining full measured pairs and zero-size behavior; worst uses existing value/work laws. |
| `best_is_minimum`, `worst_is_maximum` | `best_minimum`, `worst_maximum`, quantified over every same-length Bool input under the fixed identity predicate. |
| `best_theta_constant` | `best_positive` gives exact cost 2 at every positive size, preserving the useful uniform finite content without another asymptotic definition. |
| `worst_theta_linear` | `worst_positive_bounds` gives explicit constants 3 and 4 with threshold 1. |
| `best_not_linear_lower` | `best_eventual_lower_obstruction` plus importing `rejects_eventual_lower`; preserves the threshold quantifier rather than only a finite small counterexample. |
| Five-element best/worst examples | Native frozen fixtures and importing examples use `best_run 5` and `worst_run 5`: bills 2 and 16. |
| `head_theta` and head boundary example | Outside this selected slice. Current `ListExecution.head_work`/`head_value` retain constant work and Option empty behavior; generic growth remains #459. |
| `reverse_all_input_bounds`, `reverse_theta` | Outside this selected slice. Current `ListExecution.reverse_work` gives `2*length+1`; `Examples.ResourceGrowth.half_reverse_bounds` and `half_reverse_theta` retain actual reweighted replicate consumers. The generic size-indexed residual remains #459. |

The new prefix-fold consumer extends the selected source with ordered values,
composed bills and first-failure suffix independence. It preserves useful
mathematics and current interfaces rather than historical wrapper names.
No book correction is inferred from a naming or API difference. Complete printed
chapter evidence and source licensing remain provenance obligations under #149;
this result does not certify unseen textbook passages or all of R1/Chapter 2.

## Contract and verification

The [native contract](takewhile-extrema-contract.md) and
[direct executor fixtures](../../Examples/TakeWhileContract.lean) were committed
before adding the theorem layer. Their independently calculated values and bills
remain unchanged. Importing consumers then recover those conclusions through
public general theorems, with satisfied hypotheses and retained negative cases.

Focused verification uses `lake build Examples.TakeWhileExtrema` inside the
repository's Nix shell. The public entrypoint imports the consumers and frozen
fixtures, so the standard guarded check and exhaustive proof audit include all
new formal declarations. Runtime timing tests would not validate these symbolic
cost claims; no new external runtime or tooling is introduced.
