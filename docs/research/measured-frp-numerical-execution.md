# Measured FRP and numerical executions

[#193](https://github.com/VladimirMarko/conaled/issues/193) exercises the existing
resource interfaces on source-window processing and checked numerical motion.
Both adapters instrument executed branches and erase to their existing
references. They share measured pairs and additive observations, while retaining
their different failure policies.

## Independent specifications and observations

FRP's reference is `Trace.process`, which calls `Frontier.advance` and keeps
the previous state on rejection. Its finite-list behavior is `foldl process`;
`sourcePrefix` supplies the original stream-prefix formulation. Rejection
consumes a message and processing continues. State validity, completed source
knowledge and source honesty retain their original meanings. Finite input
lists are an execution boundary for the adapter, not a restriction on the
mathematical event/source specification.

The numerical reference is `Numerical.run`. On success it returns the exact
final packet, ordered endpoint samples and accumulated command duration.
The first failed `checkedStep` rejects the whole run. Failure to certify a
proposed step does not prove that physical motion is impossible. The existing
`Approx`, sample-domain, error-budget and clock contracts remain unchanged.

[AttemptCounts](../../Applications/Resources/AttemptCounts.lean) is the product
`Nat × (Nat × Nat)`, read as `(attempted,(accepted,rejected))`. An accepted
transition emits `(1,(1,0))`; a rejected transition emits `(1,(0,1))`. The two
additive tariffs are attempt projection and `2*attempted+accepted+3*rejected`.
These coefficients are illustrative logical prices, not measured machine costs.
The product order makes both tariffs monotone for transporting bounds.

An attempt may perform substantial validation, list traversal or rational
arithmetic. Those operations, arithmetic bit complexity, allocation, retained
or peak space, scheduler overhead and physical runtime are not counted here.
Numerical `Result.elapsed` is command time, not the attempt tariff. Numerical
error follows the native budget recurrence and is not an additive operation count.

## FRP adapter

[MeasuredTrace](../../Applications/FRP/MeasuredTrace.lean) branches on the actual
result of `advance` once per message. It records acceptance independently of
whether the final state changed: an accepted empty window at the old frontier
can stutter just as a rejected message does. `step_erases` proves agreement
with `process`.

The list executor is the existing `Resources.run`. `run_erases` uses its state
law, `run_append` uses its sequential composition law, and `reweight_run` uses
its additive observation change. `run_valid` transports the existing semantic
invariant through `run_invariant`. Knowledge refinement and agreement with
`sourcePrefix` are proved separately. Completion follows from the original
path-specific honesty and prefix-soundness premises, with no new global
honesty requirement on arbitrary stored states.

Every supplied message is attempted, so attempts equal list length and
accepted plus rejected equals that length. This is a whole finite-workload
count, not a bound on per-message validation or indefinite retained space.

## Numerical adapter

[MeasuredNumericalExecution](../../Applications/Orbifold/MeasuredNumericalExecution.lean)
has result type `Measured (Option Result) AttemptCounts`. Putting `Option`
outside the measured pair would discard spent work on failure. Its recursion
calls `checkedStep`, returns immediately on rejection, and recurses only after
acceptance. Successful prefixes retain their counts even when a later step
fails. No recursive call is made for the unused suffix.

`run_erases` proves equality with the native success/failure result. The native
`run_correct`, `run_error` and `run_clock` theorems then supply the same endpoint,
sample, error and clock conclusions on measured success. These are reused
analytic guarantees, not new numerical estimates inferred from event counts.

`run_append` expresses composition through `Resources.bind` and a local
`continueWith`. Failure has a zero-cost continuation. Success runs the next
segment and joins samples and elapsed duration only when the whole execution
succeeds. `reweight_append` follows from the existing `reweight_bind` law.

On success all supplied ticks are accepted and no ticks are rejected. After a
successful prefix of length `k` followed by a rejected tick, the exact counts
are `(k+1,(k,1))`, independently of the unused suffix. In every run, attempts
are at most input length, rejections at most one, and attempts equal accepted
plus rejected. These bounds count actual checked-step invocations.

The existing measured Dijkstra executor has a different contract: each already
failed suffix iteration incurs an administrative unit, and its fixed iteration
list is still consumed. Reusing that failure policy would overcharge numerical
attempts. A zero-cost absorbing step through `Resources.run` could preserve the
same event counts but would still traverse the host suffix. The local recursion
makes this adapter's short-circuit behavior explicit.

## Checked uses and executable evidence

[MeasuredFRPTrace](../../Examples/MeasuredFRPTrace.lean) accepts a window with
ordered fragments `[3,4,3]`, rejects a late message and then accepts an empty
window advancing the frontier. Its counts are `(3,(2,1))`; tariffs give 3 and 11.
A rejected suffix preserves final knowledge but increases work. An accepted
same-frontier empty window retains its acceptance label despite leaving the
state unchanged. Examples exercise erasure, prefix agreement, validity,
refinement, append, reweighting and monotone bound transport.

[MeasuredNumericalMotion](../../Examples/MeasuredNumericalMotion.lean) reuses
the native move–turn–move word, including its exact result and mathematical
contracts. All three steps succeed. A separate velocity `(2,0)`, duration-zero
tick fails because its squared velocity exceeds one, independently of the
current packet. Following one accepted move with that tick yields whole-run
failure and counts `(2,(1,1))`; tariffs give 2 and 8. Immediate rejection has
the same failure result but different counts. The arbitrary-suffix theorem
proves that no later checked steps contribute attempts.

The standalone [runtime checks](../../scripts/MeasuredExecutionTest.lean) execute
both adapters against their native references, compare full outputs and event
counts, test branch combinations, and retain the same numerical counts with a
10,000-tick suffix after failure. Changing tariffs uses the stored measured
result. This is executable agreement evidence, not a CPU-time benchmark.

```sh
direnv exec . lake build Examples.MeasuredFRPTrace Examples.MeasuredNumericalMotion
direnv exec . lake env lean --run scripts/MeasuredExecutionTest.lean
direnv exec . ./check.sh --candidate HEAD --fresh
direnv exec . ./check.sh --verify-candidate HEAD
```

## Reuse and next consumers

Callers reuse `Measured`, `bind`, erasure squares, additive `reweight_bind`,
`reweight_bound`, and the workload executor's append/invariant/reweight laws.
They still supply a domain-specific instrumentation step, its erasure proof,
its branch-accounting proof and any progress assumptions. Numerical execution
also needs its local short-circuit recurrence and sample/clock reconstruction.
No repeated obligation here requires a new exception transformer, potential
function, common runner or resource hierarchy.

For #113 retained-state composition and #177 data-structure workloads, this
adds two consumers of the existing contracts without changing them. #31's
request machine and #49's subdivision/retry driver can add their own events
and account for retries before reusing these observation laws. The numerical
adapter does not implement that driver. #232 lifecycle identifier bits and
retention, #234 indefinite-service bounds and #233 bounded-driver observations
still need their own space and progress models. A single high-water-mark Nat
is not a constant-bit bound.

The result establishes two measured cross-domain executions. It does not
establish a complete FRP runtime, numerical simulator, automatic optimizer,
physical memory bound or wall-clock guarantee.
