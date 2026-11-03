# Complete immutable-array knapsack workload (#162)

The immutable workload now returns the exact source `Selection`, including
names in original item order, cached value and cached weight. It executes and
accounts for initialization, every item row, the final capacity read and the
full returned-name traversal. The source fold evaluates the item-list tail
first. At each capacity it compares skipping the current item with taking it
once; equal values retain the skip alternative.

`Applications.Resources.KnapsackSemantics` uses the existing
`Optimization.KnapsackThinning.Item`, `Selection`, `add`, `Feasible` and
`Optimal`. Its recursive `select` is the source selection specification.
`select_feasible` and `select_value_bound` prove the independent input-sublist
contract without requiring labels to identify occurrences. Positive zero-weight
items, zero capacity, repeated labels and zero values are permitted. No equality
or order on labels is required. `select_frontier_value` applies the existing
pruned optimizer's `solve_optimal` to connect the two implementations' optimum
values; their tie-selected names are not equated.

The array implementation reuses `Resources.Knapsack.step`, whose writes use
`DynamicProgramming.arrayAssign`. `step_entry` invokes the shared distinct-index
update theorem. `table_size`, `table_entry`, `table_read_bounds` and
`answer_eq_select` prove size preservation, every valid capacity entry, bounds
for both old-row reads, and complete final `Selection` equality. All associations
read the unchanged previous row. Neither ascending writes nor zero-weight
items allow reuse of the current occurrence.

## Execution and observations

`Applications.Resources.KnapsackWorkload.rowsMeasured` composes the already
accepted `stepMeasured` through `Resources.bind`. The empty case initializes
`capacity+1` selections and charges `3*(capacity+1)+3`; each item adds one unit
of source fold overhead. `runMeasured` performs the final indexed read at
charge 3 and calls `observeMeasured`. That observation recursively traverses
and rebuilds the complete names list, charging three units per name and four
for its terminal case and selection reconstruction. It does not merely return
an untraversed shared tail with a computed length charge.

The first three observations remain weight tests, value comparisons and array
replacement calls. They omit initialization, arithmetic, allocation-model
charges, final reads and output traversal. The fourth component contains the
source's conservative scalar tariff, including all those operations. These
are distinct mathematical observations of the same execution.

Write `N = capacity+1`, `n = items.length`,
`C = sum (N - item.weight)` using truncated Nat subtraction, and
`L = (select capacity items).names.length`. The checked exact equations are:

- `rowsMeasured_exact`: counts `(n*N, C, n*N)` and scalar work
  `n*(23*N+10) + 23*C + 3*N + 3`.
- `runMeasured_exact`: the same three counts and scalar work
  `n*(23*N+10) + 23*C + 3*N + 3*L + 10`.
- `observeMeasured_exact`: scalar work `3*L+4`, with the unchanged full selection.

The row coefficient follows from the accepted row equation:
`21*N + 23*fittingCapacities + 2*old.size + 9`. Reachable old rows have size
`N`, and each item adds one fold unit. `comparisons_bound` proves `C ≤ n*N`;
feasibility proves `L ≤ n`. `rowsMeasured_bound` recovers the source row-fold
bound `n*(50*N+11)+3*N+3`. `runMeasured_bound` recovers `80*(n+1)*N`.

`copyCharges` records the charge of the existing `copy` operation at each
actual old array reached by the fold. Its sum is `n*(2*N+1)`:
`immutable_copy_slots` separates `2*n*N` slot-copy units from one administrative
unit per batch. `copies_charged_in_run` proves these charges are included in the
complete scalar work. These equations neither identify repeated immutable API
calls with physical in-place mutation nor establish copy elimination, peak
memory, bit complexity or wall-clock performance.

## Source scalar recovery and consumers

`sourceRowsRun` and `sourceRun` retain the literal source recurrences on top of
the existing `sourceStepRun`. `sourceObserve` uses the already reconstructed
`sourceMapRun` at per-element charge one; this specializes the source's
constant-tariff identity map and retains its terminal and cons charges.
`rowsMeasured_sourceScalar` and `runMeasured_sourceScalar` prove full pair
projection equality, including selection values. The source value, whole-row
bound, complete-run bound and array component of `complete_variants_optimal`
follow through that projection. Recursive and list-workload scalar models are
not introduced.

Two consumers use public results in `Examples.KnapsackWorkload`:

1. `selection_consumer` and `zero_capacity_optimal` obtain independently defined
   feasible-sublist global optima from `runMeasured_optimal`. `frontier_consumer`
   crosses to the previously reconstructed dominance-pruned optimizer.
2. `reweighted_consumer` assigns tariff `(2,3,5,0)` to the three primitive counts,
   obtaining 54 for the repeated-label workload; the scalar projection gives
   275. `reweighted_pipeline` uses `runMeasured_reweight`, which follows from
   the generic additive-homomorphism `reweight_bind` law through the actual
   row, read and output-traversal stages. Values remain unchanged.

The retained cases have independently specified selections and charges:

| Case | Expected selection | Counts and scalar work |
|---|---|---|
| Empty input, capacity 2 | Empty | `(0,0,0,19)` |
| One value-7, weight-0 item, capacity 0 | That item once | `(1,1,1,72)` |
| Distinct occurrences both named `same`, values 3 and 4, capacity 2 | Two `same` names, value 7, weight 2 | `(6,4,6,275)` |
| Two value-5 items, capacity 1 | Later occurrence `b`, because skip wins the tie | `(4,2,4,177)` |
| Weight-4 item, capacity 2 | Empty; copying and all guards still charged | `(3,0,3,98)` |
| Two weight-1 items valued 5 and 7, capacity 3 | `a,b`, value 12, weight 2; one capacity unit remains unused | `(8,6,8,370)` |

Other cases check an interior capacity entry, two copied rows costing 14 units,
returned-name observation costing 10 units, literal scalar projection and the
source workload bound. Concrete reductions occur after applying the public
value/count theorem or scalar projection, so examples test those connections.

## Statement review and provenance

The initial missing connection was exact selected names across all array rows;
the accepted row instrumentation alone did not establish a knapsack optimum
or selected-name agreement. The tie case expected `b`, and the repeated-label
case expected two names with value 7. These expectations drove the recursive
selection and all-capacity invariant before the whole measured workload.
The scalar expectations were then calculated from initialization, row, fold,
read and traversal tariffs and retained through the public exact theorem.

Statement review covered every new definition and theorem. Quantifiers range
over arbitrary finite item lists and all Nat capacities, with no positive-weight
or unique-label premise. Feasibility tracks a sublist of occurrences and all
cached fields. The recursive specification retains source skip-on-tie behavior;
value equality is explicitly weaker than full selection equality. The array
invariant applies only at `j ≤ capacity`; size and old-read bounds justify every
reachable lookup and write, so default reads do not influence the answer.
Measured recursion follows source suffix-first evaluation. Every row's three
counts and scalar tariff are added exactly once. Full name traversal occurs
once after final selection; it is absent from the three primitive counts but
present in scalar work. Bounds use proven comparison/name inequalities, not an
assumed optimum or assumed work bound.

The [declaration ledger](adwh-knapsack-workload-provenance.tsv) contains 177
rows: all explicitly named declarations in checkpoint233's `Chapter13/Knapsack`,
`KnapsackArray` and `KnapsackWork`, plus two selected `BankPrimitiveCosts` helper
anchors. Constructors, generated declarations and anonymous examples are not
separate rows. Each row records immutable snapshot, member, SHA-256, source
name, destination and scope. Source bytes were rechecked against the preserved
manifest and the extracted files used for inspection. Existing #151/#153/#154
contracts are distinguished from new proofs. The 83 deferred declarations
include list-table bridges, enumeration/maxima contracts, unrelated helper
properties, and recursive/list scalar models. The only retained component of
`complete_variants_optimal` is the array workload. No entire source module or
knapsack family is marked complete.

Targeted validation is `direnv exec . lake build Examples.KnapsackWorkload`.
The public entrypoint imports these examples for the full fresh build and
exhaustive audit. Independent reviews and fresh integration remain the
coordinating session's acceptance gates.
