# Executed counter prefixes and token output

Issue #505 supplies the remaining selected counter-output contract under #459
(R6). The executor observes the initial seed and performs only the increments
needed for the requested prefix. A separate renderer emits explicit line tokens
and counts them. Transition writes and emitted symbols remain different
observations. This is neither an IO driver nor a physical allocation/time model.

## Source and current owners

The preserved archive
`docs/history/algorithm-design-haskell/checkpoint-233.zip` has SHA256
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
Its `project/sources/adwh/code/part0/chap2.hs` (SHA256
`38c84bad66b25307ca01864d0b50048c640a763ff1732361749704592c41a8ea`)
contains `bits n = take n (iterate inc [])` at LINE directive 586. These are
source coordinates, not printed-book page numbers. The inspected recovered
`project/adwh-lean/ADWH/Chapter02/CounterOutput.lean` has SHA256
`727f608f2de75d759d66da83dae2beab150574bd370953813c1bf185957647db`.
Its explicit token convention is useful recovered mathematics; it is not
attributed to the book or to a particular Haskell Show byte representation.
No historical proof replay is claimed.

The implementation retains
[BinaryCounter](../../Applications/Resources/BinaryCounter.lean),
[CounterGeometry](../../Applications/Resources/CounterGeometry.lean),
[Measured](../../Applications/Resources/Measured.lean) and
[StructuredLinear.Costs](../../Applications/Linear/StructuredCosts.lean).
Those files are unchanged. The counter still executes `incWithCost`, and the
renderer uses the actual existing `traverse`. The insertion observer uses
[Permutations.insertsWith](../../Applications/Sequences/Permutations.lean).
No shared traversal owner or framework is introduced.

## Execution and output contract

[CounterOutput](../../Applications/Resources/CounterOutput.lean) provides:

| Result | Contract and source disposition |
| --- | --- |
| `prefixRun_eq` | Full pair equals the independent seed-inclusive prefix and `totalCost (n-1) seed`, for every natural count and Boolean-list seed. Recovers both archived prefix projections. |
| `prefixRun_bills` | The write total is the sum of existing ordered actual transition bills. Reuses #479 rather than deriving geometry again. |
| `renderDigits_eq`, `renderState_eq` | Actual recursive emissions equal the independent token specification and exact charge. |
| `lineSpec_decode`, `renderStates_decode` | Projecting digits recovers the exact original representation, including noncanonical zeros. |
| `renderStates_native` | Full executable renderer is a scalar observation of the unchanged native varying-callback traversal. |
| `renderStates_eq`, `renderStates_actual_symbols` | Full ordered output, digit mass plus three tokens per state, and equality with actual produced line lengths. |
| `traversal_reweight` | Any supplied additive map on the existing work vector preserves full values and maps summed callback observations. No new execution syntax or arbitrary-effect fusion law. |
| `prefix_digitMass_bound` | Arbitrary-seed digit mass is at most `n*seed.length + ∑ i<n, i`. Replaces archived recursive `triangleBefore` with native finite sums. |
| `printCounter_states`, `printCounter_values` | Arbitrary-seed representation recovery, and zero-seed numeric output `List.range n`. |
| `printCounter_transitions`, `printCounter_transition_bound` | Exact transition charge and existing zero-seed bound `2*(n-1)`. |
| `printCounter_symbols`, `printCounter_actual_symbols` | Explicit output charge and its connection to returned lines. |
| `printCounter_symbols_upper`, `compute_and_output_upper` | Recovered loose bounds `n*n+3*n` and `6*(n*n)` for zero seed. |

`renderDigits` charges one per digit emission. `renderState` adds one for each
of the left delimiter, right delimiter and line-end token. `outputCallback`
puts that bill in the existing `outputWrite` coordinate; `renderStates` reads
that coordinate after the native traversal. Traversal bookkeeping, list
allocation, append traversal and physical output delivery are not charged by
this symbol-count convention. The actual token values and their lengths are
proved together, so the count is not a detached estimate.

The decoder filters digit tokens. Its theorem is a left inverse on produced
lines, not a claim that malformed input is rejected. Least-significant-first
order and line boundaries are retained. For n=0 the prefix performs no
increment or output; for n=1 it renders the seed without incrementing it.
`printCounter` accepts arbitrary seeds and imposes no canonicality premise.

The digit-mass estimate uses the elementary length increase of at most one per
increment. Bounding the finite triangular sum by n² deliberately loses
precision; the combined bound also uses `n ≤ n²`. These bounds recover useful
archived guarantees without asserting tight asymptotics. Existing potential
and exact geometric bounds remain available under their original interfaces.

## Checked distinctions

[Examples.CounterOutput](../../Examples/CounterOutput.lean) applies the public
theorems to independently specified fixtures. Five zero-start states have digit
mass 8 and line lengths `[3,4,5,5,6]`: **23 emitted tokens**. The four transition
bills are `[1,2,1,3]`: **7 writes**. Summing these two selected tariffs gives 30.

The #477 comparison tariff charges callbacks `1 + digit length`, totaling 13,
and separately adds `2*n+1` structural units, giving 24 for five states. It does
not count literal tokens. Adding those same 11 structural units to the literal
renderer gives 34. Native `traverse` itself adds no structural tariff. The
example keeps the comparison as an explicit separate formula, not a claim
that the renderer executed those additional operations.

`[]` and `[false]` both denote zero but render different lines, with 3 and 4
symbols respectively. Both decode exactly. Carry-extension and arbitrary
nonempty-seed applications retain the full pair and bound. Reweighting is
exercised on the actual output callback, using `outputCharge`.

The second observer traverses actual `insertsWith id 1 [1,2]` outputs:
`[[1,1,2],[1,1,2],[1,2,1]]`. Its `head + 2*second` bills are `[3,3,5]`.
The returned ordered pairs retain both equal occurrences and their bills.
Generation work is not included. An earlier external preparation's distinct
full-selection fixture claimed 27 for `head + second` on permutations of
`[1,1,2]`; its actual bills are `[2,3,2,3,3,3]`, giving 29 with the stated 13
structural units. That erroneous preparation is not used as this test oracle.

## Statement review and validation

The universal statements quantify arbitrary seeds, including redundant high
zero bits; numeric equality is not substituted for representation equality.
Prefix count is the number of observed states, not the number of increments.
`prefixRun_eq` connects both components of actual execution to the retained
source specification. Decoding and the exact-symbol law observe returned
lines, not separately recomputed oracle output. Reweighting requires an additive
map and does not promise ordered-effect interchange or sharing. The work vector
is the existing commutative event inventory; output and duplicate occurrence
order are retained in the values. No new order-polymorphic traversal is claimed.

The module and connected examples pass focused Lean compilation. The public
[runtime driver](../../scripts/CounterOutputTest.lean) checks literal lines,
separate bills, noncanonical representations, carries, duplicate observations
and 85 numeric prefixes from five seeds, against addition-based expected values.
The initial missing-module runtime failure was retained before implementation.
Run through the repository development shell:

```sh
lake build Examples.CounterOutput
lake env lean --run scripts/CounterOutputTest.lean
```

The public entrypoint imports the examples. Integrated candidate build, full
axiom audit and independent Standards/Spec acceptance belong to the coordinator's
final acceptance record; focused checks do not replace those gates.

This accounts for the selected recovered output obligations when combined with
#479 and the existing counter contracts. R2 demand/sharing, R4 arrays and R7
measured recursive permutation generation remain separate. In particular, this
observer establishes no removal/append/generation cost or fuel correspondence.
Printed-book completeness and licensing remain #149; neither Chapter 2 nor the
whole-book umbrella is closed by this delivery.
