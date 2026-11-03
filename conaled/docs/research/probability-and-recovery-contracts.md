# Probability and recovery contracts

Research for [#196](https://github.com/VladimirMarko/conaled/issues/196),
2026-10-28, after inspecting
[#197](https://github.com/VladimirMarko/conaled/issues/197),
[#198](https://github.com/VladimirMarko/conaled/issues/198) and
[#199](https://github.com/VladimirMarko/conaled/issues/199).
Baseline: [`840b9ac8b0ba3291cd9ee718aa8cc3c795b8ba55`](https://github.com/VladimirMarko/conaled/tree/840b9ac8b0ba3291cd9ee718aa8cc3c795b8ba55).
The probability integration was initially on a separate local branch and was
merged into `master` at the owner's request during this investigation. The
source links below are therefore available locally. This note inspects existing
proofs; it introduces no Lean claims or fresh runtime measurements. Worked
calculations and proposed recovery laws are labeled separately from checked results.

**Use #198's joint execution law and operational deadline events for the next
recovery experiment.** Reuse #197's kernel interpretations where distribution
transport is needed, but do not interpret stationarity as recovery. #199's
optional models identify future comparison obligations; none blocks a bounded
evidence-observation experiment. The remaining work is to connect an actual
recovery transition and its costs to those probability contracts, including
the assumptions about which observations are truthful and when attempts run.

## Reusable contracts and their restrictions

[`AcceptReject`](../../Applications/Probability/AcceptReject.lean) operates on
arbitrary measurable state spaces. A Markov proposal, a jointly measurable
acceptance function bounded by one, and symmetry of the accepted flow yield a
normalized, reversible transition and then invariance. `complete` puts rejected
mass on the current state. This is a specified transition with an output, not
a claim that a stalled external attempt made progress. Applying that completion
operation to operational divergence mass would change the semantics.

[`FiniteMH`](../../Applications/Probability/FiniteMH.lean) proves the accepted-flow
condition for positive rational target weights and finite stochastic proposal
tables. Zero forward and zero reverse support have explicit conventions.
[`FiniteKernel`](../../Applications/Probability/FiniteKernel.lean) provides
`Table.kernel_comp`, `tableMeaning_laws` and `table_steps_meaning`: exact rational
composition and finite iteration agree with their kernel interpretations through
the existing `RawMap`/`MapLaws` architecture. The finite representation is a
realization of probability laws. It neither restricts the general accept/reject
specification to finite states nor supplies a random-bit sampler.

For #196, these interpretation laws can preserve a chosen stochastic recovery
transition. Its safety conditions, reachable states and resource observations
must first be defined and proved. `invariant_comp` preserves a common invariant
measure under composition, not necessarily reversibility, safety from every
initial state, or convergence. The identity and periodic examples in
[`ProbabilityCorrelation`](../../Examples/ProbabilityCorrelation.lean) prevent
those stronger readings. Existing cartesian compiler frontends also cannot
interpret arbitrary stochastic arrows: their `pair_eta` would identify distinct
joint distributions with equal marginals. See the
[probability interface record](../probability.md#composition-and-interpretation).

The more direct recovery interface is
[`ProbabilityProgress.Execution`](../../Applications/Probability/Execution.lean).
One environment `ω` determines an ordinary machine for the entire execution.
It can encode a random tape, correlated failures and observations; state can
retain the cursor. The underlying operation is arbitrary, but the proved
measurability fragment uses countable state/output spaces and measurable
one-step equality fibers. Random starts need their own measurable fibers.
These are restrictions of this current operational comparison, not restrictions
on all mathematical recovery specifications. No general kernel-to-machine
realization or trajectory-adequacy theorem connects #197 to #198.

| Existing declaration | What #196 can reuse | Obligation retained by the caller |
|---|---|---|
| `sequential_ae` | Almost-sure termination of a sequential machine. | One joint law, first-stage postcondition, feeding into the downstream domain, and downstream termination on that domain on a common conull set. |
| `sequential_tail_le` | Deadline risk bounded by first-stage timeout plus a downstream timeout event. | Preserve the actual intermediate value and its original environment; establish probabilities of these events. |
| `results_mass`, `divergence_mass` | Result mass equals operational termination probability; missing mass equals divergence probability. | Measurability/countability and a probability execution law for the latter formula. |
| `hittingTime_le_iff`, `timeout_iff_search_none` | Mathematical hitting times and executable finite search observe the same deadline event. | Atomic-transition cost model; no wall-clock conversion is supplied. |
| `almostSureProductive_iff`, `ae_coherent_prefixes` | All finite output lengths coexist almost surely with coherent prefixes. | A single execution law and pathwise deterministic delivery; no fixed deadline or finite expectation follows. |

Sources: [`Execution`](../../Applications/Probability/Execution.lean),
[`Results`](../../Applications/Probability/Results.lean),
[`HittingTimes`](../../Applications/Probability/HittingTimes.lean),
[`SearchObservation`](../../Applications/Probability/SearchObservation.lean),
[`Productivity`](../../Applications/Probability/Productivity.lean).
The countable-intersection step concerns output lengths, not every conceivable
policy. In `sequential_ae`, the downstream premise is
`∀ᵐ ω, ∀ t, dom ω t → Terminates (g ω) t`; it covers the state selected by
the first stage in that same environment. Replacing it with unrelated
fixed-input assertions without a common conull set would lose this guarantee.

## A useful composition and a correlation counterexample

The checked [`retryThenCountdown_tail`](../../Examples/ProbabilisticProgress.lean)
uses a retry's returned tape cursor to initialize a countdown. It applies
`sequential_tail_le` under `CoinPaths.law`, the countable product of fair-bit
measures, and retains the joint downstream event. Its two stages are not
independent: a longer retry produces a larger countdown.

Here is a further **mathematical specialization, not a new Lean theorem**.
Starting at cursor zero, let `T` be the number of inspected bits up to the first
true bit. On return the cursor is `T`; the countdown requires `T+1` transitions.
If `T≤k`, the second stage therefore finishes within `k+1`, making
`downstreamTimeout` empty for those budgets. The existing union bound yields

```text
Pr(total transition count > 2k+1) ≤ Pr(T>k) = 2^(-k).
```

This calculation uses the concrete retry and countdown operations, the
operational composition theorem, and the specified independent tape law.
It does not multiply two marginal success probabilities. The exact tape
cylinder and timeout probabilities are already proved in
[`CoinPaths.cylinder_mass` and `timeout_mass`](../../Applications/Probability/CoinPaths.lean).
It is a useful template for an observation stage followed by cleanup whose
cost depends on the number of interrupted attempts.

A constructed counterexample changes only the joint law. Sample one fair bit
`B` and use it for every probe. Every individual probe still has success
probability `1/2`, but for every positive `n`,

```text
Pr(first n probes all fail) = 1/2,
```

whereas the independent law gives `2^(-n)`. With the shared law, an initial
failure makes the conditional probability of the next failure one. This
infinite-tape extension is a paper calculation; the repository already checks
the underlying distinction through `shared_first`, `shared_second`,
`independent_first`, `independent_second`, and `joint_distributions_differ` in
[`ProbabilityCorrelation`](../../Examples/ProbabilityCorrelation.lean).
Equal marginals cannot justify a recovery tail bound or independent redundant
checks. A kernel that omits a shared latent failure state may likewise model
fresh draws when the intended system repeatedly observes the same cause.

Conditional information matters even without repeated trials. In the existing
[`Evidence`](../../Applications/Interaction/Evidence.lean) model, both the
no-effect world and the already-effected world observe silence. In a proposed
two-world prior assigning probability `p` to the latter, conditioning on that
certain silence leaves probability `p` of an effect. It never proves absence.
This finite calculation needs a specified prior; no prior is inferred from the
observation alone. General regular conditional laws need further hypotheses,
and conditioning on a null observation is not an ordinary positive-probability
ratio. Keeping the whole joint law often avoids needing a new conditioning API.

## Probability transport adds obligations to relational transport

Current [`RelationTransport`](../../SquareKit/RelationTransport.lean) and
[`Interaction.Refines`](../../SquareKit/InteractionContracts.lean) describe
possible behaviors and universal requirements. They do not specify weights.
Two measures on the same two possible outcomes can assign different failure
probabilities while satisfying identical behavior-set refinements.
Nor does a value-only interpretation preserve a cost distribution.

A sufficient **proposed comparison contract** is a measurable map `d : T → S`
with `d_* μT = μS`, together with observation preservation. For a measurable
source event `E`, target event `d⁻¹(E)` has exactly the same probability. For
nonnegative measurable cost `cS`, if `cT=cS∘d` then its extended expectation
is preserved; an almost-everywhere inequality gives an upper-bound comparison.
Mathlib already supplies pushforward evaluation and
[`lintegral_map`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean).
For a relational observation, a coupling with the stated marginals, almost-sure
relation and event/cost implication can replace the map. Existence of that
coupling is an additional theorem, not a consequence of `Refines`.

An expectation transformer `Q ↦ (x ↦ ∫ Q(y) κ(x,dy))` averages outcomes;
the Boolean `requirement` quantifies over every related outcome. A probability-one
property still permits exceptional paths. These operations should retain their
different meanings rather than be called interchangeable probabilistic pullbacks.
For compilation or recovery, identify the events to preserve, including
termination and deadline events, before choosing a comparison. Equality of
successful return values alone loses timing and divergent mass.

## Progress, resources and policies

[`ProbabilisticProgress`](../../Examples/ProbabilisticProgress.lean) checks that
an explicit failure return retains unit result mass, while a partial-return
machine has returned and divergent masses `1/2`. An expired finite deadline
is a third observation. `CoinPaths` proves almost-sure retry termination while
the all-false path diverges and every finite deadline retains positive risk.
[`HeavyTail.lintegral_cost_eq_top`](../../Applications/Probability/HeavyTail.lean)
proves infinite expected *actual* transition count despite termination for
every sample: sample `N` with mass `2^(-(N+1))`, then count down from `2^N`.
Thus almost-sure termination, bounded work, finite expectation and a small
deadline tail require separate arguments.

The progress model counts atomic transitions, including silent steps and the
return. [`Resources.Measured`](../../Applications/Resources/Measured.lean)
and [`Workload`](../../Applications/Resources/Workload.lean) can account for
other named observations, but no existing bridge charges recovery allocation,
probe latency, persistence, cleanup or scheduler delay. Nonnegative extended
integrals allow infinite expectation; a finite bound must be proved. General
signed expectation calculations need the appropriate integrability hypotheses.
Rejecting an MH proposal returns the old state; filtering away every rejected
output can destroy productivity. Neither operation models a lost acknowledgment
without an explicit interpretation.

The supplied environment resolves all choices mathematically. It does not
by itself restrict a policy to information available so far. An executable
recovery policy needs a causal information boundary, and a strategic fault
model needs permitted strategies and a law for any remaining randomness.
For example, `∃ policy, ∀ allowed adversaries, Pr(success)≥1−ε` is stronger
than a claim for one fixed scheduler; `∀ environment, ∃ policy` permits choosing
after the environment is known. A theorem under one distribution also does
not imply success against every allowed fault sequence. These strategy and
causality requirements are absent from #198's bounded fragment and remain #196
obligations.

## Optional models from #199

The [model comparison](probability-model-comparison.md) is research, not an
implemented QBS, valuation or probability-sheaf library. Its implications for
recovery are selective:

- **Random functions and reusable policies.** QBS supplies function spaces
  compatible with continuous probability, unlike arbitrary measurable spaces.
  A fixed recovery controller and explicit latent state can already use the
  first-order execution model. Returning arbitrary admissible random functions
  would justify the additional comparison. See
  [Heunen et al.](https://arxiv.org/abs/1701.02547) and
  [Ścibior et al.](https://arxiv.org/abs/1711.03219). A higher-order denotation
  still needs operational and information-flow contracts.
- **Random-variable context and conditioning.** Stein's construction starts
  with a Markov category *with conditionals* and retains sample-space context.
  That could help track shared causes and observation extensions, but ordinary
  Markov structure does not supply those conditionals. The paper leaves
  expectation and conditional-expectation development for future work.
  [Stein, §§II, VI](https://arxiv.org/html/2503.02477v1).
- **Internal lower information.** Vickers' valuations concern opens and
  nonnegative lower reals. The local comparison's Sierpiński example has a
  lower-semicontinuous success parameter `p(b)=1` for `b>0`, zero otherwise;
  `1−p` is not lower semicontinuous. Classical complement-based risk subtraction
  therefore cannot be transported into that setting without extra structure.
  [Vickers, §§1–2](https://sjvickers.github.io/Riesz.pdf). The current classical
  execution theorems keep their existing meaning.

None of these optional models removes the need to prove fault probabilities,
independence, safe retry or runtime adequacy. They should remain separate
experiments with explicit interpretations, as required by the
[shared language direction](../language-direction.md).

## Revised smallest recovery-resource experiment

Start with **observation of one already-published obligation**, using the
existing effect-preserving recovery example. Do not repeat the external effect.
This studies recovery of evidence after publication, not an exactly-once
external-effect protocol.
Keep the initial effect count one and charge every unsuccessful observation,
including an interruption modeled as a failed probe. A probe either obtains
truthful evidence and acknowledges, or leaves the obligation unresolved.
An implementation that can hang inside a probe needs a richer transition
model; the initial experiment must say that every probe completes as a bounded
atomic operation. For elapsed-time claims, additionally bound scheduling,
probe duration and terminal recording. A bound on fault count alone supplies
none of these.

The following are **proposed acceptance criteria**, not delivered theorems:

1. **Pathwise accounting first.** Define the policy independently of probability.
   Let `T≥1` be its first successful probe, or infinity. A cap `B` yields
   `min(T,B)` probes, acknowledging exactly when `T≤B` and otherwise returning
   an explicit unresolved result. State the exact additional machine transitions
   for the cap and terminal record. With fixed finite nonnegative overhead `c₀`
   and per-probe cost `c`, prove `W=c₀+c·min(T,B)` in that resource interpretation.
   Here `min(T,B)` denotes the finite natural probe count, including when
   `T=∞`; the display is mathematical notation, not a proposed Lean signature.
   Preserve effect count one through each transition, not as a final assumption.
2. **Hard fault-budget guarantee.** Define `F_f` independently on the supplied
   Boolean outcome sequence: among its first `f+1` entries at most `f` are
   failures. It does not assume an evaluation or successful return. If every
   requested probe completes, interprets its entry truthfully, and `B≥f+1`,
   derive a successful probe by `f+1`, acknowledgment, and
   `W≤c₀+c(f+1)`. Retain an all-failing counterexample: uncapped recovery can
   diverge; capped recovery still terminates within its cap but cannot promise
   acknowledgment. Retain the existing duplicate-effect and delayed-attempt
   counterexamples to reject silently substituting an effect-repeating retry.
3. **Lift the same model under specified laws.** Relate probe success to
   `CoinPaths.retry` and its operational timeout event. Under the independent
   fair tape, unresolved probability after `B` probes is `2^(-B)`; contrast the
   shared-bit law's `1/2` for positive `B`. Check measurability and the actual
   state/cost interpretation. Do not merely assign these tails to a new counter.
4. **Expose assumption violations.** For a broader execution law, let `G`
   express the non-budget assumptions and `F_f` the allowed failure budget.
   The pathwise proof should yield
   `{W>c₀+c(f+1)} ⊆ F_fᶜ ∪ Gᶜ`, and a corresponding inclusion for failure
   to acknowledge when the cap is sufficient. Lift by measure monotonicity and
   a union bound. Distinguish an operational timeout from an explicit unresolved
   return. No independence is required for this upper bound.

The first stage depends on current interaction/progress and measured-resource
interfaces; the probabilistic stage now has #198's merged event and tape laws.
No QBS or general conditioning framework is needed. Conditional per-history
failure bounds could later replace iid trials, but require an explicit observed
history and conditional-law theorem. Likewise deadline composition can use
`sequential_tail_le` once cleanup is an actual downstream machine.

Compare the proof effort with the existing direct recovery contract and report
what the shared accounting removes. Preserve mathematical specifications
independently of finite tables or executable adapters. New formal work requires
checked specializations, statement review, fresh compilation, exhaustive axiom
audit and independent review. This research milestone selects the next bounded
test; it does not establish a physical failure model or complete #196.
