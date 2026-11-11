# Constant guard-dispatch prices for trim and prune

[#472](https://github.com/VladimirMarko/conaled/issues/472) implements the
constant-price continuation of [single trim](whole-list-trim.md) and
[folded prune](folded-prune.md). [PricedPrune](../../Applications/Resources/PricedPrune.lean)
adds actual trim recursion parameterized by g:Nat. Empty dispatch costs g and
does not evaluate p[]. Nonempty acceptance costs length+g; rejection costs
twice length+g plus recursion. Cut keeps one cons unit, and tail-first prune
has zero empty cost. The [contract](priced-prune-contract.md) and
[independent price fixtures](../../Examples/PricedPruneContract.lean) preceded
implementation.

`trim_zero`, `cut_zero` and `prune_zero` recover the existing complete measured
pairs at g=0. Value equalities hold for all g, so existing WholeListTrim.Spec and
FoldedPrune.Spec retain their independent meaning and uniqueness. `trim_spec`,
`prune_spec` and `prune_longest` transport correctness; the last still requires
TailClosed. Pricing neither changes raw list answers nor repairs missing
closure. Pairwise closure remains valid without transitivity, and adjacent
inequality remains an insufficient distinctness test.

## Exact execution and native accounting

For input length n, output length k and incoming cut-state length l:

| Result | Equation |
| --- | --- |
| `trim_extra` | Wg+g*k=W0+g*(n+1) |
| `trim_exact` | Wg+k²+g*k=n*(n+1)+g*(n+1) |
| `cut_extra` | Wg+g*k=W0+g*(l+2) |
| `prune_extra` | Wg+g*k=W0+2*g*n |

These are theorems of the executed recursions, not definitions of their bills.
The generic runner covers g=0 and g=1; no separate positive-only executor was
added. Existing zero-price APIs remain unchanged.

Potential Ψg(s)=|s|²+g*|s| and charge3*(|s|+1)+2*g give `cut_exact`.
`workload_exact` uses native run_potential_exact for arbitrary commands and
initial state. `workload_value` proves the shared state trajectory, and
`budget_exact` identifies the priced native budget with the existing zero-price
budget plus2*g*commandCount. `prune_eq_workload` identifies the full measured
pair with reverse-order commands. No charged reversal or extra prune dispatch
is introduced. From empty, `prune_exact` gives Wg+Ψg(out)=B0+2*g*n.

`foldPrune` composes through existing bind/foldr for arbitrary function, seed and
combine price c. Its ordinary-fold value follows from an independently supplied
recursive Spec, or the original longest-prefix Spec under closure.
`fold_work_of_spec` gives total+Ψg(out)=B0+2*g*n+(1+c)*k+1, retaining the final
fold's empty dispatch. Workload, Potential and both old algorithms are unchanged.

`trim_bound` is n*(n+1)+g*(n+1). Prune's bounds are3*n²+2*g*n and(3+2*g)*n²,
including empty prune. The latter recovers5*n² at g=1. These are finite
inequalities with explicit price dependence. `no_uniform_finite_coefficient`
refutes one coefficient bounding every g and n by using an all-reject singleton
of cost3+2*g. It does **not** reject an eventual asymptotic estimate with a
threshold depending on g. Positive empty trim also refutes a pure finite
quadratic bound including n=0, not an eventual estimate.

## Importing uses and boundaries

[Examples](../../Examples/PricedPrune.lean) connect the independently specified
ordered output to extra-work, native budget, workload and consumer laws.
Nondecreasing [3,7,8,2,3] keeps [3,7,8]; at g=1, cut costs3,4,15,4,5 yield prune31,
priced budget43, final potential12 and cons-fold38. At g=2, prune38/consumer45.
Direct trim at g=1 has the same output but work24/consumer31. Pairwise distinct
[1,2,1] gives [1,2], prune18/consumer23. Adjacent inequality gives the wrong full
list. Acceptance only of[1,2] still gives empty prune at10 and single trim[1,2]
at3, and the longest-prefix claim for that prune is explicitly refuted.

Empty trim costs g, empty prune0, empty consumer1. Checked all-accept length3
trim/prune costs are3+g and9+3*g; all-reject costs12+4*g and9+6*g. A nonempty
initial-state workload checks5+12=6+11 under the native exact potential law.
These are selected source-level costs, not measurements of predicate runtime,
allocation, physical performance or general lazy semantics.

## Provenance and selected R3 disposition

The recovered source is project/adwh-lean/ADWH/Chapter02/Prune.lean in
[checkpoint-233.zip](../history/algorithm-design-haskell/checkpoint-233.zip),
SHA-256 5d563ac9dd02d8c3b8e430251f54ca92416f1a303453ed8ac6c323547b853845.
Its positive-price section proves g=1. The arbitrary-natural-g contract was a
proposal recorded in [recovered research](adwh-recovered-research.md); it is
proved here, not retrospectively attributed to the archive. The original
generic draft was not newly recovered during this task.

| Selected positive declaration | Native coverage |
| --- | --- |
| trimPositiveRun, trimPositiveRun_value | `trim 1`, `trim_value` |
| trimPositiveRun_extra, trimPositiveRun_work_le | `trim_extra`/`trim_bound` at1; checked importing specializations |
| cutPositiveRun, cutPositiveRun_value, cutPositiveRun_extra | `cut 1`, `cut_value`, `cut_extra`; unit-price specialization |
| prunePositiveRun, prunePositiveRun_value, prunePositiveRun_extra | `prune 1`, `prune_value`, `prune_extra`; unit-price specialization |
| prunePositiveRun_potential_exact | `prune_exact` at1, expanded importing cumulative identity |
| prunePositiveRun_work_le | `prune_quadratic_bound` at1, checked5*n² specialization |

Together with #470/#471, this accounts for the selected archived R3 trim/prune
semantics, closure, zero/positive cumulative costs and proposed constant guard
price extension. It supports a later parent reconciliation; it does not itself
close #459, certify every printed R3 statement or complete Chapter2. Printed-book
evidence/licensing remains #149. SuffixTrim and other families are unchanged.
No varying callback-cost framework or other architectural adoption was made.
