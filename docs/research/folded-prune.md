# Folded whole-list prune

[#471](https://github.com/VladimirMarko/conaled/issues/471) extends the
[single trim](whole-list-trim.md) with tail-first execution and native workload
accounting. [FoldedPrune](../../Applications/Resources/FoldedPrune.lean) reuses
WholeListTrim unchanged. A cut conses one element, executes trim, and adds one
cons unit. The runner first prunes the tail, then cuts the head into that result;
empty execution costs zero. The pure prune is its first projection.

The [frozen contract](folded-prune-contract.md) and
[ordinary-list fixtures](../../Examples/FoldedPruneContract.lean) preceded runner
development. Recursive `Spec` requires the tail's specified output and the
single-trim longest-prefix specification at the next stage. `run_spec`,
`value_of_spec` and `Spec.unique` prove realization and uniqueness for arbitrary
Boolean whole-list predicates. `run_prefix`, `run_length` and `run_accept` retain
prefix, length and empty-or-accepted guarantees.

`TailClosed` requires an accepted nonempty list to have an admissible tail.
Under precisely this premise, `run_longest_prefix` recovers the original input's
longest-prefix specification and `prune_eq_trim` proves equality of values.
`pairwise_tailClosed` covers any decidable relation without transitivity. This
does not identify the two measured executions.

## Workload and consumer

Let l be the incoming state length and k the cut output length. `cut_exact`
derives `work+k*k=l*l+3*(l+1)` from single trim's exact identity. `charge` is
3*(length+1), and `potential` is length squared. `workload_exact` instantiates
existing `Resources.run_potential_exact` for arbitrary commands and initial
state, retaining both potentials and the native trajectory-dependent budget.

`run_eq_workload` identifies the **entire measured pair** with
`Resources.run (cut p) xs.reverse []`. Reverse describes command order and is
not an executed, charged reversal. `work_exact` specializes the native identity
from empty. `budget_bound` proves the native budget is at most 3*n*n for arbitrary
predicates; `work_bound` then bounds actual work. There is no duplicate recursive
charge sum or new generic accounting layer.

`foldPrune` uses existing bind and ListExecution.foldr. `fold_value_of_spec`
retains ordinary ordered fold of any independently specified output for arbitrary
function, seed and price c. `fold_value_of_longest` adds longest-prefix recovery
under tail closure. `fold_work_of_spec` gives
`total+k*k=budget+(1+c)*k+1`, including the final fold's empty dispatch.

[The importing client](../../Examples/FoldedPrune.lean) checks actual transitions
and uses these public laws:

| Pairwise predicate/input | Returned prefix | Prune work | Final cons-fold work |
| --- | --- | --- | --- |
| Nondecreasing `[3,7,8,2,3]` | `[3,7,8]` | 24 | 31 |
| Distinct `[1,2,1]` | `[1,2]` | 14 | 19 |

The first trajectory executes commands 3,2,8,7,3, reaches states `[3]`, `[2,3]`,
`[8]`, `[7,8]`, `[3,7,8]`, and incurs work 2,3,12,3,4. Its native budget is 33
and final potential is 9. Single trim returns the same value but costs 21, with
consumer cost 28. Adjacent inequality returns the wrong full distinctness input.
Acceptance only of `[1,2]` violates tail closure: prune returns empty at work6,
where single trim returns `[1,2]` at work2. The recursive Spec still applies;
the original longest-prefix claim fails. Empty, all-accept and all-reject pairs
are checked. A nonempty initial-state example proves the native potential
identity and rejects omission of the initial potential.

These are selected cons/length prices. They do not measure arbitrary predicate
runtime, allocation or physical performance, and supply no general lazy model.

## Recovered-source dispositions

Source: `project/adwh-lean/ADWH/Chapter02/Prune.lean` in
[checkpoint-233.zip](../history/algorithm-design-haskell/checkpoint-233.zip),
SHA-256 `5d563ac9dd02d8c3b8e430251f54ca92416f1a303453ed8ac6c323547b853845`.
The native proofs adapt its prefix-maximality and cost arguments while reusing
current workload accounting. Historical interfaces are evidence, not authority.

| Selected source | Native disposition |
| --- | --- |
| `cut`, `cutRun`, `cutRun_value` | Measured `cut`, `cut_value`; no duplicate pure cut runner |
| `prune`, `pruneRun`, `pruneRun_value` | `run`, projection `prune`, ordinary `run_value_fold` |
| `cutRun_length`, `cutRun_potential_exact` | `cut_length`, `cut_exact` |
| `PruneSpec`, `pruneRun_spec`, `pruneRun_unique` | Independent `Spec`, `run_spec`, `value_of_spec`, `Spec.unique` |
| `pruneRun_prefix`, `pruneRun_length`, `pruneRun_accept` | `run_prefix`, `run_length`, `run_accept` |
| `TailClosed`, `pruneRun_longest_prefix`, `prune_eq_trim` | Corresponding closure and recovery results |
| `pairwise_tailClosed`, `prune_pairwise_longest_prefix` | Arbitrary-relation closure plus `run_longest_prefix`; ordered and distinct callers |
| `arbitrary_predicate_not_longest` | Actual measured `closure_required` and `nonclosed_not_longest` |
| `charges`, `charges_quadratic_bound` | Existing native `budget`, explicit `budget_bound`; no second sum |
| `pruneRun_potential_exact`, `pruneRun_work_le` | Native `workload_exact`, `work_exact`, `work_bound` |
| `pruneRun_eq_run_reverse` | Full measured `run_eq_workload` |

The single-trim declarations remain covered by #470. Positive-dispatch and
arbitrary guard-dispatch variants remain #459 R3. R5 is unchanged. Existing
SuffixTrim and Workload/Potential ownership are preserved. This does not close
R3 or Chapter 2; printed-book evidence and licensing remain #149.
