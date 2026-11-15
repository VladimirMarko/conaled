# Normalized prepared rows and linear selection

Issue [#544](https://github.com/VladimirMarko/conaled/issues/544) adds an LCM
preparation and a carried-total selector. The product-denominator preparation
and its measured selector remain available as comparison baselines.

## Representation and execution contracts

`NormalizedWeights.common` computes the LCM by a reverse finite fold and
records its number of LCM applications. `dvd_common` and `common_dvd` prove
that the result is a common multiple dividing every other common multiple.
For positive rational denominators it is positive and divides the original
product. `denominator_le_product` proves the numerical size comparison.
`weight_cast`, `sum_weight` and `weight_mass` establish exact rational
multiplicities, including zeros. `Table.prepareNormalized` stores these
multiplicities in an array and satisfies `prepareNormalized_returns_mass`.

The selector reads weights from the last index toward the first. It carries
the already available remaining total, subtracts one weight to obtain the next
cut, and either selects the last interval or recurses into the prefix. No
prefix sum or cumulative cache is built during a lookup. `select_encode` and
`select_value` prove exact equality with the existing `finSigmaFinEquiv`
interval decoder. `sum_rowSelect` then recovers its multiplicity law for any
outcome observation, including duplicate outcomes.

For a fixed prepared row, `OptimizedRowWork.measuredStep_eq` identifies the
new executable step with metering of the existing sampler. Both directions of
`measured_evaluates` retain the output, cursor and transition count.
`workload_value` preserves the complete finite workload result, including an
unfinished block, when only the selector changes. This is stronger than a
probability-law comparison.

Changing denominators has a different contract. The row `(0,1/3,2/3)` changes
from total 9 and weights `(0,3,6)` to total 3 and weights `(0,1,2)`. The law is
the same, but the block widths change from four to two bits. Checked tapes
separate finite-fuel success, values, returned cursors and rejection patterns.
The deterministic row has total 1 in both representations. The mixed row
`(1/2,1/3,1/6)` changes from product 36 to LCM 6.

## Producer and stationary-law reuse

`RowChain.rows_path_mass` and `rows_final_mass` use the supplied row return law;
the original table theorems wrap these proofs. The same contract feeds
`TableProducer.prefix_mass_rows` and `stationary_blocks_rows`.
`InitializedProducer.stationary_blocks_rows` allows an independently prepared
initial row and transitions, using the actual returned initialization cursor.
Its general `almostSureProductive_rows` needs only countably many states and
positive prepared rows. Existing table-facing statements remain available.

The normalized specializations prove complete ordered-prefix and endpoint
laws, productivity, joint initialized output laws and stationary blocks.
`FiniteMH.normalized_stationary_blocks` supplies the MH specialization through
the existing stationarity theorem. All these probability proofs retain the
existing stopped-cursor argument. A checked dependent two-draw example uses
`PreparedRow.joint_mass` directly; no new independence assumption is introduced.

The representation is chosen before execution. The delivery and productivity
contracts do not authorize replacing a row while it has an unfinished draw.

## Declared costs and workload comparisons

The source-operation model retains `SamplerWork.Tariff`. LCM has its own
explicit price, independent of operand size, just as the existing model prices
natural arithmetic and logarithm. Structural recursion, proof casts and
instrumentation bookkeeping are outside the model. This establishes no
arithmetic bit-complexity or machine-time claim.

For `m` entries, measured normalization charges

```
m*lcm + 3*m*arithmetic + 3*m*(entry + projection) + m*store.
```

The three arithmetic operations per weight are numerator conversion, quotient
and multiplication. Rational callbacks/projections are charged on each use.
Compiling all `m` rows adds their preparation charges and `m` outer-array
stores and `m` input-enumeration evaluations at the `entry` tariff; each later
load pays `lookup`, including inverse enumeration. The
storage measure follows the actual array and prepared-row sizes: `m*m+m`
weight/reference entries, excluding immutable closures.

For each accepted ticket, the linear selector costs at most

```
m*(lookup + 2*arithmetic) + arithmetic + outcome.
```

It charges a lookup, subtraction and comparison per visited entry, and one
final ticket-offset subtraction. This replaces the previous conservative
quadratic selector bound; it does not assert lower cost for every individual
ticket or tariff. For the normalized sparse row under unit tariffs, ticket
zero costs 8 rather than 10 in the existing selector.

`OptimizedRowWork.workload` executes the existing eager-prefetch policy with
the new measured step. It retains partial block states, bit charges, rejected
blocks, initialization, every load after emission (including the final
observed emission), output accumulation and chronological output handling.
Compilation setup is added explicitly to the observed workload charge.

The checked constant three-state chain uses the sparse row at every state.
All existing tariffs are one, and LCM costs ten. Normalized preparation costs
60 per row versus 33 for the product baseline. Compiling the normalized rows
costs 186, and retains 12 weight/reference entries. On the all-false tape:

| Observation | Product, prepare per load | Normalized, prepare per load | Normalized, compiled once |
|---|---:|---:|---:|
| One output | 106 | 146 | 214 |
| Four outputs | 319 | 398 | 289 |

These comparisons charge `n+1` loads for `n` outputs. Four outputs use sixteen
bits in the product implementation and eight in the normalized implementation.
The checked output lists agree on this tape; no same-tape coupling is claimed
for arbitrary tapes. Short workloads can lose despite a smaller denominator.

## Checked evidence and limits

`Examples.OptimizedRows` consumes the public arithmetic, selector, preparation,
workload and producer theorems. Closed computations provide the separating
tapes and exact workload bills. Existing `Examples.TableSampler`,
`Examples.TableProducer`, `Examples.SamplerWorkload` and
`Examples.InitializedProducer` retain the original implementations' contracts.

The work does not prove entropy optimality, universal speedup, bounded machine
integers or an adaptive representation change. General linear expected-work
composition belongs to [#578](https://github.com/VladimirMarko/conaled/issues/578).
