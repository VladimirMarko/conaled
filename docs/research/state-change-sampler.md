# State-change sampling (#553)

`TableProducer.changes` retains only transitions whose returned state differs
from the current state. For a finite rational transition table with positive
exit probability at every state, the actual filtered producer is almost surely
productive. Its ordered output law is the jump kernel
`J(x,x) = 0`, `J(x,y) = P(x,y) / (1 - P(x,x))` for distinct states.

The proofs are in
[StateChangeSampler.lean](../../Applications/Probability/StateChangeSampler.lean).
`ChangeTrace` records every suppressed row, partial row state, returned cursor
and bit count. Its equivalence with actual filtered evaluation connects the
matrix calculation to execution on the original coin tape. The renewal proof
uses stopped-cursor freshness for the prepared rows. `prefix_mass` proves the
ordered finite law; `change_stopped_mass_evaluates` also preserves an arbitrary
measurable observation of the suffix after an actual change. Repeated filtered
observations therefore use their returned cursors, without assuming fresh
independent tapes.

If `pi` is invariant for `P`, the jump chain has normalized invariant weights
proportional to `pi(x) * (1 - P(x,x))`. Positivity of the normalizer is proved.
`initialized_stationary_blocks` includes actual evaluation of the initial
sampler and then the filtered execution at its returned cursor. The initial
hidden state is not counted as a changed output.

[StateChangeSampler examples](../../Examples/StateChangeSampler.lean) check
exits `1/2` and `1/4`: the original invariant distribution is `(1/3, 2/3)`,
whereas the alternating jump chain has weights `(1/2, 1/2)`. They also check
partial-row resumption, exact output laws and suffix observations. The absorbing
singleton fails the exit premise and is not productive after filtering. An MH
self-proposal can be accepted; suppressing unchanged states does not recover
latent acceptance flags.

## Measured execution and deadlines

[StateChangeWork.lean](../../Applications/Probability/StateChangeWork.lean)
uses the existing measured row step and loader. Every completed row pays for
loading and initializing its successor, including suppressed transitions and
the final eager prefetch. Each completed row pays an explicit comparison cost;
only changed outputs pay emission and final output-handling costs. Erasure
recovers `TableProducer.changes`, including partial execution state. The
workload is measurable and has a deterministic bound at any actual finite
delivery.

[StateChangeDeadline.lean](../../Applications/Probability/StateChangeDeadline.lean)
adds quantitative bounds for the waiting needed to obtain changes. Let `W` be
the maximum prepared-row width and choose `r < 1` bounding all self-transition
probabilities. Such an `r` exists for every supported finite positive-exit
table. With `a` raw-row attempts per change and `b` rejection blocks per row,
the probability of failing to produce `n` changed outputs within
`n * a * W * b` bits is at most

```
n * (r^a + a * (1/2)^b).
```

The first term accounts for repeated self-transitions; the second accounts for
raw-row rejection sampling. Composition uses the actual filtered stopping
cursor. `workDeadline_bound` transfers this bound to a charged budget of

```
setup + initialLoad + initialization
  + (n * a * W * b) * (perBitCap + loadCap + initialization + comparison + emit)
  + n * finish.
```

Failure includes non-delivery even when all tariffs are zero. These are costs
in the declared tariff model, not CPU timings or integer bit-complexity bounds.
They are conservative deadlines, not expected-work estimates.

[StateChangeWork examples](../../Examples/StateChangeWork.lean) use an asymmetric
MH table and an actual tape with one suppressed transition followed by a change.
Full row preparation costs 135 units; compiled lookup costs 118 including its
setup. Both retain all three row preparations or lookups. A separate checked
specialization bounds failure to deliver two changes within 640 bits, or within
33,306 charged units, by `2 * ((2/3)^8 + 8 * (1/2)^8)`.

## Scope and reuse

The probability interfaces accept any prepared family with the required exact
row law. The measured interfaces accept any loader returning that family, with
explicit load and per-bit bounds. This permits normalized or compiled rows
without changing the filtered observation contract.

The results cover finite positive-exit rational tables. They do not prove
mixing, convergence, productivity with absorbing states, general predicate
filtering, or accepted-proposal execution. Expected work at filtered stopping
times remains separate from these deadline bounds and from #578's ordinary
producer expectation work.
