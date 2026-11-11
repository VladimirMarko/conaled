# Whole-list trim through an ordered consumer

Issue #470 implements the single whole-list trim operation selected from #459 R3.
[WholeListTrim](../../Applications/Resources/WholeListTrim.lean) tests a nonempty
list, returns it when accepted, and otherwise recurses on `dropLast`. Empty
exhaustion returns `[]`. Its pure `trim` is the first projection of this measured
runner. [The frozen contract](whole-list-trim-contract.md) and
[independent fixtures](../../Examples/WholeListTrimContract.lean) preceded runner
development.

`Spec` requires a prefix, empty-or-accepted output, and maximal length among all
admissible prefixes. `run_spec` proves this for arbitrary whole-list Boolean
predicates; `Spec.unique` proves uniqueness independently of the runner. There
is no monotonicity or tail-closure assumption. `value_of_spec` connects an
independently certified answer to execution. `trim_prefix`, `trim_length_le`,
`trim_accept` and `trim_of_accept` expose its pure consequences.

The selected abstract prices charge k for a successful nonempty guard and 2k
for a failed guard plus `dropLast`, with zero at empty. `work_exact` proves
`work + k*k = n*(n+1)` for input/output lengths n/k. This identity describes the
recursive execution; it does not define its work retroactively. `work_upper`
and `work_quadratic_upper` give the finite upper bounds. `all_false_run` and
`all_false_bounds` exhibit the quadratic rejecting family; `all_true_run` costs
n, and `quadratic_lower_obstruction` defeats every proposed eventual bound
`n*n ≤ C*work` on that family. These are selected prices, not physical costs of
arbitrary predicates or the separate `ListExecution.init` schedule.

`foldTrim` uses existing `Resources.bind` and `ListExecution.foldr`.
`fold_value_of_spec` proves the ordinary fold of any independently specified
output, for arbitrary function and seed. `fold_work_of_spec` gives
`total + k*k = n*(n+1) + (1+c)*k + 1`, retaining the fold's empty dispatch.
[Importing examples](../../Examples/WholeListTrim.lean) apply these general laws:

| Predicate/input | Output | Trim work | Cons-fold work, c=1 |
| --- | --- | --- | --- |
| Pairwise nondecreasing `[3,7,8,2,3]` | `[3,7,8]` | 21 | 28 |
| Pairwise distinct `[1,2,1]` | `[1,2]` | 8 | 13 |

Adjacent inequality accepts the entire second input, yielding a different
answer. The predicate accepting only `[1,2]` is not tail closed but returns
`[1,2]` on `[1,2,3]`. Empty, immediately accepted and wholly rejected executions
are checked too. These are Lean theorem applications, not runtime benchmarks.
The public `SquareApplications` entrypoint imports the client.

## Source dispositions and remaining work

The selected archive member is
`project/adwh-lean/ADWH/Chapter02/Prune.lean` in
[checkpoint-233.zip](../history/algorithm-design-haskell/checkpoint-233.zip),
SHA-256 `5d563ac9dd02d8c3b8e430251f54ca92416f1a303453ed8ac6c323547b853845`.
Proof arguments for recursive prefix maximality and the exact identity were
adapted to current native lists and the existing measured layer.

| Selected recovered declaration | Current disposition |
| --- | --- |
| `Accept`, `TrimSpec` | `Accept`, independent `Spec` |
| `prefix_dropLast_of_lt` | Private native prefix lemma |
| `trim`, `trim_spec` | Projection `trim`, theorem `trim_spec`; one measured recursion |
| `trim_prefix`, `trim_length_le`, `trim_accept` | Corresponding native consequences |
| `trim_unique` | `Spec.unique` proves uniqueness for any two specified outputs |
| `trim_of_accept` | `run_of_accept` and its pure projection |
| `trimRun`, `trimRun_value` | `run`, with projection definition and `value_of_spec`; no duplicate pure recursion |
| `trimRun_potential_exact` | `work_exact`, with upper bounds and explicit accepting/rejecting families |

This accounts for the selected single-trim slice only. `cut`, folded `prune`,
its specification and execution, `TailClosed` equivalence, cumulative potentials
and positive-dispatch variants remain R3 under #459. Existing Workload/Potential
owns future sequence accounting. R5 is untouched. Existing `SuffixTrim` remains
an element-predicate shortest-prefix operation and is unchanged. No equivalence
between folded prune and trim for arbitrary predicates follows here. Printed
chapter coverage and licensing remain open under #149; the recovered member is
source evidence, not proof of complete printed-book coverage.
