# Probabilistic termination and finite delivery

The bounded implementation for [#198](https://github.com/VladimirMarko/conaled/issues/198)
uses one probability space for an entire execution. It proves almost-sure
termination, coherent finite-output delivery, and deadline statements without
requiring a uniform runtime bound or finite expectation. The checked consumers
are in [ProbabilisticProgress.lean](../Examples/ProbabilisticProgress.lean).

## Operational paths and result measures

`ProbabilityProgress.Execution Ω S A` supplies a deterministic
`Progress.Machine S A` for each environment `ω`. The environment can be an
infinite random tape, with the current cursor retained in the state. A return
is `Sum.inl a`; `Sum.inr s` is one silent transition. Every transition costs one.
The existing inductive `Progress.Evaluates` and `Progress.Delivers` judgments
define finite executions, independently of fuel search or certificate finding.
The environment remains fixed throughout each trace.

The measurable fragment has countable states and outputs and measurable
one-step equality fibers (`MeasurableSteps`). `measurable_evaluates` derives
measurability by induction over the transition count and countable unions over
intermediate states. Termination, bounded return, and finite prefix-delivery
events follow by further countable unions. Random initial states require
measurable fibers too; `measurable_evaluates_start` gives that extension.
No standard Borel randomization theorem or Markov assumption is needed for
this supplied-environment fragment. It does not construct arbitrary kernel
trajectory measures or prove adequacy for a probabilistic programming language.

`outcome` selects the unique returned value and exact transition count when a
finite evaluation exists, and records divergence otherwise. Its choice is
mathematical, not a termination decision procedure. `results` first restricts
the original measure to finite termination and then pushes it forward through
`outcome`. The sum carrier retains a divergence tag for the total observation,
but that tag has zero mass in the restricted result measure. No inhabited
output type is required.

The comparison theorems establish:

- `results_some`: each value/cost atom has exactly its operational event's mass.
- `results_mass`: total result mass equals probability of finite termination.
- `results_mass_le_one`: a probability execution law yields a subprobability.
- `divergence_mass`: missing result mass is probability of actual divergent paths.

Thus this measure is a result subprobability for a specified operational model.
An arbitrary s-finite kernel, unnormalized weight, or discarded output has no
such interpretation by itself. The checked partial-return fixture terminates
on one fair bit and loops on the other: returned mass and divergent mass are
both `1/2`. Immediate explicit failure retains unit result mass because it is
a returned value. Failure is neither divergence nor an expired deadline.

## Hitting times and coherent productivity

`hittingTime` is the unique evaluation count in `WithTop Nat`, with infinity
for divergence. Its finite sublevel event is exactly the complement of
`timeout`. A deadline counts atomic transitions, including the returning step.
`SearchObservation` separately proves that an operational timeout agrees with
`Progress.search = none`; search is a finite observer of the semantics.
Divergence is timeout at every finite deadline. One timeout never establishes
divergence.

For a producer, `prefixDelivered step s n budget` records delivery of `n`
outputs by the transition budget, including silent steps. These measurable
events give the finite-prefix hitting-time distributions. `AlmostSureProductive`
requires almost-sure delivery for each natural-number length under the same
execution law. `almostSureProductive_iff` uses countability of the lengths to
intersect their conull sets. `ae_coherent_prefixes` then uses pathwise
`Progress.Delivers.coherent` to obtain one coherent family of prefixes on that
conull set. There is no claim that the infinite stream itself terminates,
that all sample paths are productive, or that the finite delivery times have
finite expectation.

## Composition and shared randomness

`sequential_ae` lifts `Progress.sequential_evaluates` through one joint
execution law. The first stage supplies an intermediate postcondition, a
feeding premise puts its returned value in the second stage's domain, and the
second stage terminates on that domain almost everywhere. All three premises
may have null exceptions; their finite intersection remains conull. No new
independence assertion is introduced. The first stage's `results` measure
records its intermediate value and count; the downstream obligation remains
coupled to the environment that produced that value.

`sequential_tail_le` bounds sequential deadline risk by first-stage timeout
risk plus `downstreamTimeout`, the joint event that the actual returned value
starts a downstream computation missing its deadline. It adds transition
budgets and uses a union bound. Replacing the latter event by a product of
marginal probabilities would require a separate independence or conditional-law
argument. The two checked consumers are consecutive waits on the same tape and
a retry followed by a countdown initialized from its random return cursor.
`retryThenCountdown_tail` also uses the tail composition theorem.

`deterministic_dirac_iff` recovers exactly the existing deterministic termination
contract. Guarded producers and producers with one inserted silent step per
output recover the productivity contract through the existing delivery proofs.
The existing deterministic contracts and #197 kernel semantics are unchanged.
This is an application-library extension using their operations and laws, not
a new global effect hierarchy or a compiler for recursion.

## Checked cases and limits

`CoinPaths` uses Mathlib's countable product of fair Boolean measures. The
finite-cylinder theorem proves the probability of any assignment to distinct
coordinates, including noncontiguous ones. A retry inspects successive bits,
emits on true, and advances its cursor on either result. Its exact timeout
probability after `n` inspections is `2⁻ⁿ`. Every finite deadline has positive
risk. Almost surely every tail contains a true bit; this simultaneous
all-cursor statement can be used after a random wait. It proves indefinitely
many emissions despite silent steps. The all-false path diverges and cannot
deliver its first output.

`HeavyTail` samples a natural number `N` from the fair geometric distribution,
then executes a decrementing machine starting at `2^N`. Every sample returns
in exactly `2^N+1` transitions, as proved by `Evaluates`; uniqueness identifies
that count with any other derivation. The nonnegative extended integral of
this actual count is infinite. The calculation uses a strictly positive
geometric parameter. Mathlib's separate `p=0` convention is not interpreted
as a never-successful retry. Initial sampling cost is outside the countdown
model, so the infinite expectation already holds before charging that cost.

Ordinary MH rejection returns the current state. Observing each update has
one output per completed MH transition, including rejections. The guarded
reject-only fixture remains productive; its accepted-only filter does not.
A proposal implemented by an internal rejection sampler has its own progress
obligation. These facts do not turn the exact tables in #197 into a random-bit
implementation of MH, or prove mixing or finite-budget statistical accuracy.

Resource counts become random observations once a common execution law is
specified. Nonnegative extended integrals express expectation, including
infinity; probabilities of exceeding a threshold express tails. The ordinary
Bochner integral is not used to encode infinite expected cost. Nonnegative
integrals need no integrability premise to be defined, but a finite-expectation
claim must establish finiteness. Our unit transition counts do not measure
allocation, wall-clock time, or hardware reliability.

[#196](https://github.com/VladimirMarko/conaled/issues/196) may consume the
termination, prefix-delivery and deadline events under an explicit joint law
for randomness and faults. It must supply its own fault, recovery, scheduling
and resource assumptions. Marginals alone cannot justify their independence.
Nondeterministic scheduler choices are outside this fragment; there is no
universal-scheduler progress claim. There is no physical error rate, automatic
termination decision, lazy runtime, or general Monte Carlo accuracy guarantee.
The [model comparison](research/probability-model-comparison.md) explains why
higher-order probability and internal valuations remain separate experiments.
