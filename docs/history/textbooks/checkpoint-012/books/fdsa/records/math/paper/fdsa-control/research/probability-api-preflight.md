# Probability APIs for FDSA: source and architecture preflight

Prepared 2026-11-02. **Read-only preparation; no frozen specification, Lean
implementation, compilation, review acceptance, or chapter acceptance.**
The inspected repository is `../../conaled`; Mathlib is pinned by its
manifest to `56a005855ea17e0b0958f73ec801ae140b0a1679`. The investigation
read `AGENTS.md`, architectural/domain guidance, relevant ADRs, local
probability modules and connected examples, and the actual dependency
sources. It did not change sources, Git, caches, or the running gate.

## Recommendation

Keep the existing probability carriers and execution semantics. Conaled
already interprets finite rational tables in Mathlib kernels and already
has joint random-environment executions with operational return counts.
Mathlib supplies finite uniform measures, PMFs, conditional expectation,
finite/history-dependent kernel trajectories, nonnegative integration,
geometric series, and Markov's inequality. There is no foundational
probability-interface gap here.

The smallest useful analytic addition is a **theorem family about an
ordinary sequence of nonnegative observations on one measure**: integrated
one-step contraction gives geometric means, a bound for accumulated and
remaining work, and an excess-work tail bound when the earlier work has
an explicit pathwise bound. No new probability record, expectation
operator, stochastic executor, filtration wrapper, or resource monad is
needed. Section 5 proposes the precise statement sequence, including the
zero boundaries. The algorithm's conditional choice law remains a
separate premise to prove before applying this analytic result.

A separate combinatorial gap is uniform **relative-order restriction of a
global finite ranking**, including a fixed subset's first-ranked element.
Quicksort and treaps can reuse that mathematics. It should remain distinct
from the accumulated-work unit and from the substantial algorithm-specific
distribution/cost correspondences. See the coordinated
`probability-source-preflight.md` for the source-model analysis.

## 1. Existing local interfaces suffice for the semantic layer

All names below were inspected in source, not inferred from documentation.

| Local module and declarations | Existing contract and relevant limits |
|---|---|
| `Applications/Probability/FiniteMH.lean`: `Applications.Probability.Table` | A row-normalized nonnegative rational table: `entry : α → β → ℚ`, `nonneg`, `sum_row`; only the carrier declaration requires `Fintype β`. Evaluating a table is not drawing random bits. The MH-specific fields/laws are irrelevant to sorting or selection. |
| `Applications/Probability/FiniteKernel.lean`: `Table.comp`, `Table.deterministic`, `Table.kernel` | `comp g f` executes `f` then `g`; the interpretation is a sum of weighted Dirac measures. The inspected composition/interpretation API uses finite carriers; kernel construction also has measurable spaces and measurable singleton classes. An arbitrary payload type need not be made finite: randomness can live on a finite index or ranking space for a fixed input. |
| Same: `Table.lintegral_kernel` | Exactly `∫⁻ y, F y ∂t.kernel x = ∑ y, mass (t.entry x y) * F y`, for any `F : β → ℝ≥0∞`. This already connects exact rational finite arithmetic to nonnegative expectations. |
| Same: `Table.kernel_comp`, `Table.kernel_deterministic`, `Table.steps`, `kernelSteps`, `table_steps_meaning` | Interpretation preserves pure maps, composition and finite iteration. `kernelSteps k 0 = Kernel.id`; its successor composes `k` with the previous iteration. These give endpoint laws, not automatically the law of an accumulated path observation. Retain the cost/history in the state or use an existing trajectory law when that observation is needed. |
| Same: `tableMeaning`, `tableMeaning_laws`, `tableCategoryLaws`, `tableEquiv` | Existing `SquareKit.RawMap`/`MapLaws` transport; semantic equivalence retains the full kernel. Do not add a new category hierarchy for the book. |
| `Applications/Probability/Execution.lean`: `ProbabilityProgress.Execution`, `MeasurableSteps`, `measurable_evaluates`, `measurable_termination`, `measurable_timeout` | `Execution Ω S A = Ω → Progress.Machine S A`. One environment resolves the whole execution. Measurable equality fibers and `Countable S` give measurable finite derivations; termination/deadline results also use `Countable A`. Every atomic machine transition costs one. This is not the book's comparison, scan-volume, or recursive-call tariff without an explicit correspondence. |
| Same: `AlmostSureTerminates`, `sequential_ae`, `downstreamTimeout`, `sequential_tail_le` | Sequential stages retain the actual intermediate value and original environment. The tail theorem is a union bound involving the downstream joint event, not multiplication of unrelated marginals. It supplies no geometric drift or expected accumulated variable work. |
| `Applications/Probability/Results.lean`: `outcome`, `results`, `results_some`, `results_mass`, `divergence_mass` | `outcome` records an actual value/count or a divergence tag; `results` restricts to termination before pushing forward. The sum carrier avoids an inhabited-output assumption. Integrating only successful-result costs would omit divergence; it is not automatically an unconditional expected resource cost. |
| `Applications/Probability/HittingTimes.lean`: `hittingTime`, `hittingTime_eq_nat_iff`, `hittingTime_eq_top_iff`, `hittingTime_le_iff`, `hittingTime_sublevel` | The operational return count is in `WithTop Nat`, with infinity on divergent paths; its finite sublevels agree with deadline success. This is separate from Mathlib's first-hitting-time/stopping-time APIs and from a weighted scan sum. |
| `Applications/Probability/CoinPaths.lean`: `fairCoin`, `law`, `cylinder_mass`, `timeout_mass`, `retry`, `operational_timeout_eq`, `ae_terminates` | An existing genuine product law and a connected retry machine. `timeout_mass s n = (2⁻¹ : ℝ≥0∞)^n` includes zero inspections. It is a potential later consumer of accumulated-work reasoning, without constructing another random process. |
| `Applications/Resources/Measured.lean`, `Workload.lean`: `Resources.Measured`, `bind`, `reweight`, `run`, `run_append`, `reweight_run` | Ordinary value/observation pairs and deterministic execution can be evaluated at each sample. Their cost projections can then be integrated under the supplied law. The sample law, measurability, and actual tariff correspondence are independent obligations; equality of returned values is insufficient. |

Existing connected evidence is useful rather than incidental:

- `Examples.ProbabilityCorrelation.joint_distributions_differ`,
  `copy_after_draw`, and `draw_twice` distinguish shared and fresh sampling.
  Their equal marginals cannot justify substituting independent joint laws.
- `Examples.ProbabilisticProgress.retryThenCountdown_tail` uses the actual
  random return cursor; `partial_result_mass`/`partial_divergence_mass`
  distinguish returned mass from divergence.
- `ProbabilityProgress.HeavyTail.actual_cost` and
  `lintegral_cost_eq_top` identify an actual terminating countdown's count
  and prove infinite expectation. Almost-sure termination alone is not a
  usable integrability premise.

## 2. Finite sampling and conditioning at the actual Mathlib pin

The safest direct finite law is `ProbabilityTheory.uniformOn s`, from
`Mathlib.Probability.UniformOn`. It is counting measure conditioned on `s`.

- `isProbabilityMeasure_uniformOn hs hne` requires a finite, nonempty set
  and measurable singletons. The primed version accepts measurability of
  the set explicitly. `instIsProbabilityMeasure_uniformOn_univ` already
  supplies normalization for a finite nonempty carrier.
- `uniformOn_univ [Fintype Ω]` states
  `uniformOn Set.univ s = Measure.count s / Fintype.card Ω`.
- `uniformOn_apply_finset` gives the cardinality ratio for two finsets;
  `uniformOn_inter` factors an intersection through the conditional law
  on `s ∩ t`; `uniformOn_add_compl_eq` is the corresponding two-part law
  of total probability.
- `ProbabilityTheory.sum_meas_smul_cond_fiber`, in
  `Mathlib.Probability.ConditionalProbability`, decomposes a finite measure
  into conditional measures on the fibers of a measurable finite-valued
  random variable. Its target has `Fintype` and `DiscreteMeasurableSpace`.
  A zero-probability fiber contributes zero; do not infer a meaningful
  normalized posterior there without a positive-mass premise.

**Pin-specific naming hazard.** In the inspected
`Mathlib.Probability.Distributions.Uniform`, the actual constructors are
`MeasureTheory.Measure.uniformOfFinset` and `MeasureTheory.Measure.ofMultiset`.
Their singleton formulas are `uniformOfFinset_apply_singleton` and
`ofMultiset_apply_singleton`; the latter has mass `count a / card` and
therefore retains multiplicity. The old `PMF.uniformOfFintype` name is a
deprecated alias to the measure constructor with a changed signature. The
file's introductory prose still mentions old PMF names. Do not copy those
remembered constructors or use deprecated aliases under `warningAsError`.

PMFs themselves remain available, if an algorithm-specific well-founded
recursive law is most naturally expressed that way:

| Module | Exact usable declarations |
|---|---|
| `Probability.ProbabilityMassFunction.Monad` | `PMF.pure`, `bind`, `bind_apply`, `support_bind`, `mem_support_bind_iff`, `bind_bind`, `bindOnSupport`, `mem_support_bindOnSupport_iff`. The support-dependent bind can retain a proof-domain recursive decrease without inventing a value for an impossible branch. |
| `Probability.ProbabilityMassFunction.Constructions` | `PMF.map`, `map_apply`, `support_map`, `ofFinset`, `ofFintype`, `map_ofFintype`. `ofFintype f h` takes explicit nonnegative extended weights with finite sum one. This is already a normalized discrete law, not a reason for a local replacement record. |
| `Probability.ProbabilityMassFunction.Basic` | `PMF.toMeasure`, its probability-measure instance, `PMF.support_countable`; `Measure.toPMF` on a countable measurable carrier with measurable singletons and a probability measure; `Measure.toPMF_toMeasure`. |
| `Probability.ProbabilityMassFunction.Integrals` | `PMF.integral_eq_tsum p f hf` needs real-vector-valued integrability and measurable singletons. `PMF.integral_eq_sum` needs a finite carrier and has automatic finite-law integrability. Both use real scalar weights `(p a).toReal`. |

Choosing a uniform occurrence of a nonempty length-`n` list can use the
uniform law on `Fin n` followed by the index-to-value map; it needs no
probability distribution, decidable equality, or inhabited instance on
arbitrary payloads. `Fin 0` is not a sampling space: the algorithm must
take its base/invalid-input branch before drawing. In contrast,
`Equiv.Perm (Fin 0)` has its one empty permutation and is a valid normalized
sample space for the empty-input average.

## 3. Existing expectation, trajectory and conditional APIs

All nonnegative sums can stay in `ℝ≥0∞`, including infinite expectations.
Only convert to a real expectation after its finite/integrable meaning has
been established. In particular, `toReal ∞ = 0` and the totalized Bochner
integral of a nonintegrable function is not an infinite resource count.

### Exact signatures needed by the proposed analytic unit

The following are existing declarations, with irrelevant universe notation
omitted; they are not proposed new wrappers.

```lean
-- Mathlib.MeasureTheory.Integral.Lebesgue.Add
MeasureTheory.lintegral_tsum
  [Countable ι] {f : ι → Ω → ℝ≥0∞}
  (hf : ∀ i, AEMeasurable (f i) μ) :
  ∫⁻ ω, ∑' i, f i ω ∂μ = ∑' i, ∫⁻ ω, f i ω ∂μ

MeasureTheory.lintegral_finsetSum' (s : Finset ι)
  {f : ι → Ω → ℝ≥0∞}
  (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
  ∫⁻ ω, ∑ i ∈ s, f i ω ∂μ = ∑ i ∈ s, ∫⁻ ω, f i ω ∂μ

-- Mathlib.Analysis.SpecificLimits.Basic
ENNReal.tsum_geometric (q : ℝ≥0∞) :
  ∑' j : Nat, q ^ j = (1 - q)⁻¹

-- Mathlib.MeasureTheory.Integral.Lebesgue.Markov
MeasureTheory.meas_ge_le_lintegral_div
  {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ)
  {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
  μ {ω | ε ≤ f ω} ≤ (∫⁻ ω, f ω ∂μ) / ε
```

These need no probability, finite-measure, sigma-finite, independence, or
integrability assumption on `μ`. The geometric identity is also valid when
`q ≥ 1`, when its right side is infinity. The useful finite-work conclusion
must impose `q < 1` and a finite initial bound. The division form of Markov
requires both displayed denominator conditions. Its nondivided sibling
`mul_meas_ge_le_lintegral₀ hf ε` has no such conditions.

`ENNReal.tsum_mul_left`, `tsum_mul_right`, `tsum_le_tsum`, `sum_le_tsum`,
and `summable` are in `Topology.Algebra.InfiniteSum.ENNReal`. In this
codomain, `Summable` does not assert that the sum is finite. For prefix-tail
decomposition use the additive theorem generated as
`Summable.sum_add_tsum_nat_add'` in `Topology.Algebra.InfiniteSum.NatInt`
(it needs summability of the shifted tail, supplied by `ENNReal.summable`),
or `ENNReal.sum_add_tsum_compl` and the range-complement equivalence.
The nonprimed group-valued theorem is not the right route for `ℝ≥0∞`.

For measurability of total/shifted sums, use `AEMeasurable.tsum` from
`MeasureTheory.Constructions.Polish.Basic`, generated by `to_additive`
from `AEMeasurable.tprod`. Its codomain assumptions specialize to
`ℝ≥0∞`; the summation index is countable. The older
`AEMeasurable.ennreal_tsum` is deprecated. `measure_mono_ae` supports the
almost-everywhere event inclusion in the tail proof.

Other exact reuse, kept outside that unit's core:

| Purpose | Existing theorem and hypotheses |
|---|---|
| Finite nonnegative expectation | `MeasureTheory.lintegral_fintype` (`Integral.Lebesgue.Countable`) gives `∫⁻ x, f x ∂μ = ∑ x, f x * μ {x}` under `Fintype` and measurable singletons; no integrability assumption. |
| Finite real expectations/indicator counts | `MeasureTheory.integral_finsetSum` requires each summand integrable; `Integrable.of_finite` needs a finite carrier, measurable singletons and a finite measure. `integral_fintype` still has an explicit integrability premise. `integral_indicator_one` and `lintegral_indicator_one` turn indicator expectations into event masses. |
| Nonnegative/real bridge | `ofReal_integral_eq_lintegral_ofReal hfi hnonneg` (`Integral.Bochner.Basic`) explicitly requires integrability and almost-everywhere nonnegativity. |
| Kernel expectation recursion | `ProbabilityTheory.Kernel.lintegral_comp η κ a hg` (`Kernel.Composition.Comp`) integrates a measurable `γ → ℝ≥0∞` against the composite as an iterated integral. `Kernel.lintegral_compProd` retains both intermediate and final values and requires s-finite kernels; Markov kernels supply this. These already give the law-of-total-expectation mechanism for a concrete transition. |
| Measure bind | `MeasureTheory.Measure.lintegral_bind hκ hf` (`Measure.GiryMonad`) requires the measure-valued function almost-everywhere measurable and the observable almost-everywhere measurable under the bound measure. |
| Finite history laws | `Kernel.partialTraj`, `partialTraj_succ_of_le`, `partialTraj_comp_partialTraj`, `map_partialTraj_succ_self` (`Kernel.IonescuTulcea.PartialTraj`) already compose history-dependent transitions. The input to `κ n` is the entire prefix `Π i : Finset.Iic n, X i`. Markov normalization is preserved. No replacement trajectory datatype is needed. |
| Infinite history laws, if eventually needed | `Kernel.traj`, `trajMeasure`, `condExp_traj` (`Kernel.IonescuTulcea.Traj`) construct and analyze the law from supplied Markov kernels. `condExp_traj` uses an integrable observable and the existing `Filtration.piLE`. The separate `condDistrib_trajMeasure` theorem adds `StandardBorelSpace` and `Nonempty` for the next state; do not propagate those requirements into a finite expectation lemma that does not use regular conditional distributions. |
| Conditional drift to integrated drift | `MeasureTheory.integral_condExp hm`, `condExp_mono hf hg hle`, `condExp_finsetSum`, `condExp_smul`, `condExp_condExp_of_le` (`Function.ConditionalExpectation.Basic`). The conditioning sigma algebra must be below the ambient one, and the relevant trimmed measure sigma-finite; probability measures provide the finite-measure case. Source real observations must be integrable. A conditional expectation is totalized to zero when its definitional premises fail. |
| Stopping/martingale reasoning, when actually required | `MeasureTheory.Filtration.natural`, `Filtration.piLE`, `supermartingale_nat`, `hittingAfter`, `hittingAfter_eq_top_iff`, and `hittingAfter_le_iff` already exist. `supermartingale_nat` needs a finite measure, strong adaptedness, integrability at every time, and the one-step conditional inequality. Selection's pathwise bound of at most `n` active calls makes optional-stopping machinery unnecessary for the proposed finite-source result. |
| Treap Jensen step | `ConcaveOn.le_map_sum` (`Analysis.Convex.Jensen`) is a finite weighted inequality; `ConcaveOn.le_map_integral` (`Analysis.Convex.Integral`) additionally needs a probability measure, a continuous concave function on a closed carrier, and integrability of both observables. `Real.strictConcaveOn_log_Ioi` supplies log concavity. For a positive bounded rank, restrict to a closed positive interval such as `Icc 1 U`; do not supply open `Ioi 0` to the closed-carrier integral theorem. |

## 4. What remains specific to the three chapters

**Quicksort.** The finite law must describe actual pivot choices or actual
uniform input permutations. The expected source recurrence includes the
precise filter/recursive-call/append tariff being claimed. The existing
`quicksort-average-proof-plan.md` distinguishes that recurrence from the
comparison-count recurrence. Linearity needs the two recursive marginal
laws, not their independence, but those marginals still need proof.
The source two-way algorithm is quadratic on all-equal inputs, so distinct
keys are a real hypothesis for the usual average formula.

**Selection.** A valid rank gives a nonempty input and every selected
strict block is shorter, even with duplicates. A finite recursive law can
therefore terminate constructively, followed by zero observations. Uniform
occurrence choice, conditional on the full past, must give the actual next
state law. Counting refined occurrence ranks yields the upper bound
`E[next size | history] ≤ (3/4) * current size`. The larger-side formula is
only a majorant for a fixed requested rank. Once integrated under the same
law, the generic analytic result applies to scan volume. A comparison or
call-count claim still needs its own pathwise resource bridge.

**Treaps.** A fixed finite global priority ranking retains the common
randomness of overlapping operands; its restrictions are not independent.
Uniform numeric-priority marginals alone do not establish a uniform joint
ranking. Expected height/depth/ancestor claims use finite indicator sums;
the bulk-operation proof additionally needs the source's conditional
cluster/charging argument. An unconditional bound on one random factor
cannot be multiplied by a correlated work factor. Geometric work analysis
could serve a cluster-continuation result only after its actual conditional
progress law is established; it does not prove the bulk bound by itself.

The relative-order restriction/minimum law is not already packaged in the
inspected local probability modules or Mathlib probability/permutation
sources. Its finite counting ingredients include `Fintype.card_perm`,
`Fintype.card_congr`, `List.length_permutations`,
`Finset.card_eq_sum_card_fiberwise`, and the uniform/conditional APIs above.
Filtering an order and standardizing its ranks must be defined/proved;
restricting a permutation as a self-map of an invariant subset is a
different operation. The source-common subset minimum-rank expectation
and the quicksort conditional restriction laws remain mathematical work,
not consequences of these cardinality declarations alone.

## 5. Proposed minimal accumulated-work statement sequence

These are proposed mathematical statements, not existing declarations or
a frozen public API. Use an ordinary `μ : Measure Ω` and observations
`X : Nat → Ω → ℝ≥0∞`. Write `E_t = ∫⁻ ω, X t ω ∂μ`, solely as explanatory
notation. Let `q,N : ℝ≥0∞`. Nonnegativity is intrinsic to the codomain.

1. **Iterated mean bound.** From `E_0 ≤ N` and
   `∀ t, E_(t+1) ≤ q * E_t`, prove `∀ t, E_t ≤ q^t * N` by induction.
   No measurability, measure normalization, strict contraction, finite
   bound, or independence is needed for this ordered-integral inequality.
   Avoid publishing a duplicate elementary scalar recurrence lemma if
   its useful statement can directly be the observation result.

2. **Remaining-work integral.** Add
   `∀ t, AEMeasurable (X t) μ`. For each `w`, prove

   ```text
   ∫⁻ ω, (∑' j, X (w+j) ω) ∂μ ≤ q^w * N / (1-q).
   ```

   The proof is `lintegral_tsum`, termwise domination from step 1,
   `pow_add`, `ENNReal.tsum_mul_left/right`, and
   `ENNReal.tsum_geometric`. For useful finite bounds impose `q < 1`
   and `N ≠ ∞`; then the right side is finite. The `w=0` specialization
   is the total-work bound `E[W] ≤ N/(1-q)`. Ordinary finite accumulated
   costs follow by `sum_le_tsum` or by proving that an absorbed source
   has `X t = 0` after its pathwise horizon. The theorem must not equate
   this sum with an algorithm's cost merely by naming it work.

3. **Excess-work tail.** In addition require `N ≠ 0`, `N ≠ ∞`, `q < 1`,
   and an almost-everywhere prefix bound. A simple reusable sufficient
   premise is `∀ t, X t ≤ᵐ[μ] (fun _ => N)`; for a single `w` the weaker
   premise `∑ t<w, X t ≤ᵐ[μ] (fun _ => w*N)` suffices. Then prove

   ```text
   μ {ω | (w : ℝ≥0∞)*N + N/(1-q) ≤ ∑' t, X t ω} ≤ q^w.
   ```

   Split the sum at `w`. The prefix bound gives an almost-everywhere
   inclusion in the event that the remaining sum is at least
   `B = N/(1-q)`. Use `AEMeasurable.tsum`, `measure_mono_ae`, then
   `meas_ge_le_lintegral_div` on that remaining sum. Prove `B ≠ 0` and
   `B ≠ ∞` from the stated hypotheses before cancellation. Finite prefix
   bounds are also needed for extended-real addition/cancellation in
   the event argument. No independence or probability normalization is
   needed: all required mass information is already in `E_0 ≤ N`.

The source-facing conditional-law proof should remain separate. On a
probability space, `X 0 = N` gives the initial integral. A concrete
history-dependent kernel plus `Kernel.lintegral_comp`/`compProd` can give
the integrated drift. Alternatively use integrable real observations,
the actual filtration, `integral_condExp` and integral monotonicity, then
the nonnegative/real bridge. The analytic lemma does **not** prove that
these transitions choose uniform pivots, nor identify conditional laws
from scalar mean recurrences.

### Boundaries to keep explicit

- `N=0`: the mean/remaining-work conclusions still give zero. The displayed
  non-strict tail formula is false on a probability space with `X≡0`,
  `w>0`, and `q<1`: its threshold is zero, so its event has mass one.
  A separate positive-threshold zero-work corollary is possible; do not
  hide this boundary by dividing by zero.
- `q=0`: this is allowed. All positive-time means vanish; the remaining
  integral is zero for `w>0`, while `q^0=1`. Never divide by `q` or impose
  `0<q` solely to make the proof convenient.
- `q=1`: deterministic constant positive observations satisfy integrated
  drift but have an infinite total sum (or arbitrary linear growth with
  a finite horizon). Contraction is essential to a finite total bound.
- The prefix premise is independent of the mean recurrence. For example,
  with `q=0`, `N=1`, `X_0=3` on an event of probability `1/3` and zero
  otherwise, and all later observations zero, the mean recurrence holds.
  At `w=1`, however, the claimed threshold is two and its probability is
  `1/3>0=q^1`. The pathwise prefix cap cannot be dropped.
- A supplied scalar integrated drift is enough for this analytic theorem
  but says nothing about the correctness of the algorithm's random
  sampling model. Full conditional laws and costs remain distinct proof
  obligations. No global `Countable`/`Fintype`/`Inhabited` assumption on
  payloads belongs in this theorem family.

## 6. Connected cases and likely module placement

**Accumulation case proposed by root.** Take
`μ = ProbabilityTheory.uniformOn (Set.univ : Set (Fin 8))`.
Use the actual deterministic `Resources.run` or `bind` computation at
sample `ω` to charge four stages: one always; one if `ω.val < 4`; one
if `ω.val < 2`; one if `ω.val < 1`; then zero. Preserve an independently
specified returned value. The stage means are `1,1/2,1/4,1/8`; their
integrated drift has `q=1/2`, including the transition to zero.
The total mean is `15/8 ≤ 2`. At `w=1`, total at least three occurs
exactly on `ω.val<2`, giving `1/4 ≤ 1/2`. These stages are dependent,
and the tail event is nonempty.

No custom distribution record is needed. The existing uniform-on-universe
probability instance applies. Express each threshold set as the coercion
of `Finset.univ.filter`; `uniformOn_apply_finset` gives its cardinality
ratio. `lintegral_fintype` and singleton mass `1/8` give exact means.
These small computations are mathematical preflight targets, not checked
Lean examples. Separate `q=0` and zero-work cases exercise the boundaries.
Root's exact rational preparation is recorded in
`probability-work-calculations.json`; it also records the connected affine
observation `2*W+3`, whose mean is `27/4 ≤ 7` under this probability law.
That calculation is independent preparation, not formal validation.
The already connected `CoinPaths.retry` offers a later reuse case: prefix
indicators of `timeout 0 t` count actual inspected bits, with exact means
`2⁻ᵗ`; no new retry machine is needed.

**Separate finite-order case.** A uniform order of `{a,b,c}` restricts to
each two-element subset uniformly. For `A={a,b}` and `B={b,c}`, the
probability that `b` is first in both is `1/3`, while the product of the
marginals is `1/4`. This checks both the marginal restriction theorem and
its refusal to erase shared randomness. A source client can then use the
minimum of a fixed subset of a uniform global ranking for treaps, and
conditional relative-order restrictions for quicksort. This is a separate
combinatorial unit, not part of the first accumulation implementation.

Suggested location for the analytic theorems is
`Applications/Probability/AccumulatedWork.lean`, with connected consumers
in `Examples/AccumulatedWork.lean`. Focused candidate imports are
`Mathlib.MeasureTheory.Integral.Lebesgue.Markov`,
`Mathlib.Analysis.SpecificLimits.Basic`,
`Mathlib.MeasureTheory.Constructions.Polish.Basic`, and the natural-index
infinite-sum module if not transitively supplied. Keep kernel, PMF,
conditional-expectation, finite-uniform and resource imports in the
consumers or concrete law bridges unless the shared statements use them.
The exact minimal import closure has not been compiled. A later
finite-order unit belongs beside the probability applications; no global
effect or categorical interface change is justified by these needs.

## 7. Inspection receipts

Paths are relative to `../../conaled`. These identify inspected source,
not newly compiled artifacts. Mathlib sources are also recoverable at
<https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib>.

| Source | SHA-256 |
|---|---|
| `Applications/Probability/FiniteKernel.lean` | `0c1c75a3a5896b91daabb78115f577da3fd45693f521f5a1d0ab91c431d4f7d6` |
| `Applications/Probability/Execution.lean` | `a86b3ffaf21a6bb2a59ecc9cb105235bedfe17a2e01c0214d3e8fcdcec701b65` |
| `Applications/Probability/Results.lean` | `6dd293d87c63b8468312ece915db5bf3ae47373e556404320a91ae7eee1a6d5a` |
| `Applications/Probability/HittingTimes.lean` | `4f9100ef305208c5d03d502ac529524d994081494301a60f4a7897a500c52e6e` |
| `Applications/Probability/CoinPaths.lean` | `f8880ba5d62c62cd64f406b4e61be30e824b7d7f140935dd4b8f10fe6bf44850` |
| `.lake/packages/mathlib/Mathlib/Probability/Distributions/Uniform.lean` | `19b53a1140fb5a29373ddecd3550a07020da16b6f1f9118827ea85a67c752f20` |
| `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean` | `3da8d17447de38c759359878227ca2ddedb046d0c233ea82ab630d5f5114e3b6` |
| `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean` | `41d852f6c850f8b2a6e726065a970d5aa840dbd4db0ec8b8a5a42faf460edfa7` |
| `.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean` | `7a5d61c23552efa7618812a47172581188948b067b59ec581f18e517b819c969` |
