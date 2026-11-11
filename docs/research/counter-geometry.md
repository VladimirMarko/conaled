# Binary-counter finite geometry (#479)

[CounterGeometry](../../Applications/Resources/CounterGeometry.lean) derives the
zero-start write count from the existing increment executor. For every Boolean
tail, the even and odd branch laws count the low-bit writes and the recursive
high-bit increments. They require no canonical representation. Empty zero and
one redundant false bit have equal costs, although their zero-step states differ.

Writing `C(n) = totalCost n []`, the branch laws give `C(n) = n + C(n/2)`.
`floorSum n k` is the native finite sum over `Finset.range k` of `n / 2^j`.
All division here is natural division. `remainder` proves
`C(n) = floorSum n k + C(n/2^k)` for every `n,k`; `exact_cutoff` requires a
zero quotient, and `exact_of_lt` uses `n < 2^k`. Exponent zero is included.
For four increments, two terms give six and leave one write; three terms give
seven. A longer cutoff still gives seven.

`floorSum_bound` and `lower` establish `n ≤ C(n) ≤ 2*n`; `theta` uses the
existing growth interface and Mathlib's real-cast `IsTheta`. This derivation
uses the branch equations and finite natural arithmetic. It does not invoke
`totalCost_potential` or `totalCost_from_zero`. Those existing arbitrary-seed
potential results remain available. `power_two_exact` includes exponent zero;
`extending_carry` records the final write when an all-true seed grows.

`advance_exact` supplies the complete measured pair, including the actual final
state. `observed_states_exact` uses `n-1` increments for the seed-inclusive
`bits n`, including zero and one observed state. Five observed states therefore
mean four increments and seven writes. The zero-start floor formula is not
claimed for arbitrary seeds.

The counter-specific `recordStep` records the cost returned by each actual
`incWithCost` call in an additive free monoid. `trace` specializes the existing
`Resources.run`; it does not introduce a second counter executor. `trace_state`,
`bills_length`, `bills_entry` and `bills_append` retain the state trajectory,
order and concatenation boundary for arbitrary seeds. `trace_reweight` applies
native additive reweighting; `bills_sum` recovers `totalCost`. These bills are
aggregate writes per increment, not individual bit-write tokens or rendered
output. The first three bills are `[1,2,1]`, so a literal exact-half frequency
claim fails for this finite prefix.

[Checked callers](../../Examples/CounterGeometry.lean) apply these public results
and retain the rejecting boundaries. The
[independent contract](counter-geometry-contract.md) and its
[Lean fixtures](../../Examples/CounterGeometryContract.lean) preceded the theory.

## Recovered source disposition

The inspected source is `project/adwh-lean/ADWH/Chapter02/CounterGeometric.lean`
inside [checkpoint-233.zip](../history/algorithm-design-haskell/checkpoint-233.zip).
The archive SHA256 is
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`;
the member SHA256 is
`ebb959504e97f34e0302c7d14380ea61e3be2dbb058b2413e4c3e931c1fa55c0`.
Names below are in the recovered `CounterGeometric` namespace on the left and
the native `Resources.CounterGeometry` namespace on the right.

| Recovered claim | Current disposition |
| --- | --- |
| `even_from_zero_bit`, `odd_from_zero_bit`, `empty_zero_padding`, `zero_even`, `zero_odd` | Same-named native execution lemmas, using `BinaryCounter.totalCost_succ`. |
| `totalCost_halving` | `halving`. |
| `floorSeries`, `floorSeries_halving` | Standard finite `floorSum`, `floorSum_succ`, `floorSum_halving`; no second recursive sum. |
| `totalCost_floorSeries`, `totalCost_floorSeries_of_lt` | `exact_cutoff`, `exact_of_lt`; `remainder` also retains the arbitrary-cutoff residual cost. |
| `floorSeries_bound`, `geometric_counter_bound`, `totalCost_lower`, `totalCost_theta` | `floorSum_bound`, `geometric_bound`, `lower`, `theta`; standard real-cast asymptotics replaces the local relation. |
| `power_two_exact` | Same-named theorem plus actual `extending_carry` execution. |
| `observed_states_floorSeries` | `observed_states_exact`, applied alongside native `bits_values`. |
| `transitionCosts`, `transitionCosts_sum` | Existing workload runner specialized to ordered `bills`; `bills_sum` follows by additive reweighting. |
| `finite_frequency_rounding` and concrete examples | Checked public callers for the three-transition frequency, four/five costs and observation indexing. |

The recovered `CounterOutput` member was inspected to separate state-prefix
observation from rendering. Its prefix executor, token alphabet, renderer,
decode laws, digit-mass and output-size accounting remain separate R6 obligations
under #459. This slice does not adopt a shared traversal architecture or close
R6. The archive's comments attribute an informal frequency picture to the book;
the full printed book is unavailable here. The finite counterexample and corrected
floor arithmetic are checked independently, without claiming printed-book or
licensing completion.
