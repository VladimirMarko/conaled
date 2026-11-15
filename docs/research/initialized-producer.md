# Initialization and Markov prefixes on one coin tape

Issue [#552](https://github.com/VladimirMarko/conaled/issues/552) turns the
independent initial mixture in the existing stationary-block theorem into an
executed rational draw. `InitializedProducer` first runs a prepared row, emits
its accepted state, and starts `TableProducer` at that draw's actual returned
cursor. A pause retains the initial row's cursor, remaining block width and
accumulator; after acceptance it retains the original producer state.

## Joint observations and stationarity

`joint_mass` uses `PreparedRow.stopped_mass` to separate the accepted initial
value from the fresh tape suffix at its random stopping cursor. For a rational
initial table and transition table, `rational_joint` gives

```
Pr(initial = a, subsequent outputs = ys) = initial(a) * pathMass(a, ys).
```

`joint_eq_delivery` identifies this event with delivery of `a :: ys` by the
actual initialized producer. It preserves the whole ordered list, including
self-transitions. The theorem is not inferred from equal one-step marginals.

`stationary_blocks` executes invariant initialization and recovers the existing
mixed block law after every finite shift. `targetInitial` builds the rational
initial table from the existing finite MH target, and `mh_stationary_blocks`
discharges invariance with the existing MH stationarity theorem.

The initialized producer's first output is the initial sample. `blockEvent`
omits that sample and then skips `n` transition outputs. `block_eq_delivery`
therefore drops `n + 1` initialized-producer outputs. The separate joint law
covers observations that include initialization.

## Operational cases

`Examples.InitializedProducer` uses initial weights `false ↦ 1/3` and
`true ↦ 2/3`, and continuation rows with those same weights. The existing row
preparation uses total nine, so each trial block has four bits. The tape
`1111 0000 0110 ...` rejects its first block, initializes `false` at cursor
eight, then emits `true` at cursor twelve. Checked cases retain a partial
initialization block and its exact resumption state.

The ordered pair `(false, true)` has probability `2/9`. Incorrectly restarting
the identical continuation row at the original consumed cursor makes that
pair impossible. This is a joint-law control even though the individual rows
have the right distribution. For the existing asymmetric MH model, every
shifted ordered block `(false, true)` has probability `1/4`.

The all-true tape rejects every initial four-bit block. The code proves that
it cannot emit its first output, alongside almost-sure productivity. No total
termination assertion discards this exceptional execution.

## Work and resumption

`InitializedProducerWork` presents the same execution to the existing #543
measured workload using an `Option` phase index: `none` selects initialization,
while `some a` selects the continuation from `a`. Outcome tagging preserves
row size, multiplicities, total, selected ticket, every partial block and bit
cursor. The state encoding has an explicit inverse. Its step equation is
pointwise on tapes; the delivery comparison retains the ordered output list,
final state and exact number of bit steps.

The loader executes the supplied measured initial-row construction or the
existing continuation loader. The workload charges initial preparation and
width computation, every consumed bit, branch-specific rejection/selection
work, output handling and next-row preparation. It retains the next row even
after the final observed output, matching #543. Setup is explicit. A requested
prefix of `n` transitions contains `n + 1` draws because initialization counts.

With unit tariffs, the checked twelve-bit example costs 161: initial setup
24, initialization bit work 56, continuation bit work 29, two next-row
loads, initializations and emission charges costing 50 (two times 22 + 2 + 1),
and final output handling costing two.
A checked one-bit pause costs six after the initial setup and retains state
`(cursor=1, remaining=3, accumulator=1)`.

The phase constructor is part of the declared outcome interpretation tariff;
this is the existing source-operation model, not a host allocation or
bit-complexity result. Pausing reuses the existing measured executor's append
law and preserves the cached row and partial state without loading the initial
row again.

The previous expected-work proofs depended on prepared-row normalization and
termination, but their public entry points required literal `Table.prepare`
rows. The implementation exposes those same proofs for arbitrary
`PreparedRow` families, retaining the old table-specific statements as
specializations. This permits the phase presentation without re-preparing a
larger table or changing the sampled tape. `expected_bound`,
`expected_finite` and `budget_risk` apply the shared bounds to the complete
initialized workload. Divergent initialization remains infinite completion
work, even when all tariffs are zero.

## Scope

The distribution is an explicitly supplied finite rational table, using an
executable enumeration and the existing exact sampler. This does not prove
mixing or convergence from another initial state, supply a physical random
source, or establish general QBS operational adequacy. Expected-work bounds
are conservative finite-prefix bounds under the fair-coin measure, not a
comparison of runtime speed.

The implementation sources are
[`InitializedProducer.lean`](../../Applications/Probability/InitializedProducer.lean),
[`InitializedProducerWork.lean`](../../Applications/Probability/InitializedProducerWork.lean)
and the [checked cases](../../Examples/InitializedProducer.lean).
