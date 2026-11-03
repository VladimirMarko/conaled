# Probability, Metropolis-Hastings and probabilistic progress

Research date: 2026-10-28. This is a research recommendation, not an adopted
ADR or a claim of newly checked Lean theorems. Mathematical examples below
are paper calculations proposed for subsequent formalization. Concurrent
research and implementation for #196 are outside this change.

## Recommendation and usefulness

Integrate probability through the existing categorical foundation, using
Mathlib's measure theory and stochastic kernels as the first concrete model.
Develop Metropolis-Hastings (MH) as a reusable kernel construction with an
independent executable realization. Preserve room for other probability
models by exposing the operations and laws each argument needs. Do not make
higher-order probability, a new topos model, or a full probabilistic compiler
prerequisites for this first construction.

This would extend the present plan in useful ways:

| Existing effort | Proposed contribution and limitation |
|---|---|
| Felix extensions, #8, and compilation/recursion, #109 | A stochastic interpretation tests whether composition and transport require only the laws they use. Existing cartesian compiler interfaces need a different effectful fragment before compiling arbitrary sampling programs. |
| Progress and codata, completed #146 under #131; FRP #27/#31 | Almost-sure finite delivery extends the deterministic progress contracts. Randomized producers and filtered streams are concrete tests; probability does not supply missing environmental fairness. |
| Resource contracts, #193 | Expected work and tail bounds could interpret measured executions. Additive pathwise counts alone do not provide expectations, integrability, or deadline guarantees. |
| Faults and recovery, #196 | A probabilistic contract can express randomized recovery or reliability under a stated distribution. The present research owns probability semantics and sampler examples; #196 owns environmental/fault assumptions and recovery comparisons. |
| Shared internal language, #36 | Probability supplies another test of reusable proofs across settings. Higher-order and constructive internal probability require separate comparison theorems. |
| Orbifold simulation, #34/#49 | Sampling initial conditions, uncertain parameters, or a stated equilibrium measure is a possible future consumer. Current motion simulation has no identified requirement for MH. A quotient-space sampler would also need a target measure and representative-invariance contract. |

These are architectural opportunities, not evidence that existing applications
need MCMC. A small finite-state MH example is justified now as a discriminating
library application. A general inference engine or stochastic geometric
simulator needs a separate consumer specification. The scope assessment uses
the [workstream index](../../README.md#workstreams-and-shared-components), the
linked GitHub issues, and current code rather than historical roadmap claims.

## What already exists

The inspected Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in
[lake-manifest.json](../../lake-manifest.json). It already provides:

| Facility | Source and reuse |
|---|---|
| Measurable transition kernels and normalization | [Kernel.Defs][kernel]: `ProbabilityTheory.Kernel`, `IsMarkovKernel`. |
| Categorical probability | [MarkovCategory.Basic][markov] and [Stoch][stoch]: an abstract Markov category and its measurable-space/Markov-kernel model. |
| Weighted kernels | [SFinKer][sfinker]: s-finite kernels with symmetric monoidal copy-discard structure. Natural discard cannot be assumed for arbitrary mass. |
| Detailed balance and stationarity | [Invariance][invariance]: `Kernel.IsReversible.invariant` and `Invariant.comp`. |
| Infinite stochastic trajectories | [IonescuTulcea.Traj][traj]: `traj` and `trajMeasure`. A path distribution is not an executable producer. |
| Discrete probability | [ProbabilityMassFunction.Monad][pmf]: `PMF` and its monadic operations. A PMF is not automatically a finite executable table. |
| Randomization representation | [Kernel.Representation][representation]: a Markov kernel into a nonempty standard Borel space can be represented using a measurable function and ideal uniform randomness. The existence theorem is not an exact sampling algorithm. |
| Measure bind/join | [GiryMonad][giry]. This file uses all measures; its name must not be read as an automatic mass-one invariant. |

A targeted search of the pinned Probability and CategoryTheory trees found no
Metropolis-Hastings or quasi-Borel implementation. This is a bounded inventory,
not a claim that no Lean formalization exists elsewhere. The presence of
martingale, disintegration, or strong-law results does not itself establish an
MH ergodic theorem.

Locally, [CategoryOps and ofCategory](../../SquareKit/Category.lean),
[RawMap](../../SquareKit/CategoryMap.lean), and
[comma constructions](../../SquareKit/Comma.lean) supply reusable composition
and transport. The [Felix implementation record](felix-parity-implementation.md)
identifies their provenance at Felix revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490`. The inspected upstream
[raw operations][felix-raw], [homomorphisms][felix-maps], and
[comma type][felix-comma] support category-level reuse with stronger structure
supplied separately; this is not an upstream MH implementation claim. Retain the distinction between raw
operations, semantic equivalence, and laws. Mathlib's existing category can
enter through `ofCategory`; probability does not require replacing this core.

[Progress.Evaluation](../../Applications/Progress/Evaluation.lean) and
[Progress.Streams](../../Applications/Progress/Streams.lean) instead describe
deterministic transitions, finite evaluation evidence, and delivery of every
finite prefix. They neither assign execution probabilities nor establish
almost-sure progress. Existing [relational contracts][relations] preserve
relations, not probability weights or joint distributions.

## The architectural constraint: correlation

A product of state spaces is available for stochastic kernels, but it is not
a categorical product of arbitrary stochastic arrows. For a fair Boolean
sample, sampling once and duplicating produces only `(false,false)` and
`(true,true)`, each with probability 1/2. Two independent samples give all four
pairs with probability 1/4. Both have the same marginals.

Consequently, the current `ProductLaws.pair_eta` cannot hold for stochastic
pairing: marginals do not determine a joint distribution. Likewise, duplicating
or discarding an effectful source expression requires a justified law. This
is an explicit counterexample to reusing every cartesian compiler law, not an
obstacle to the general categorical architecture. The categorical treatment
is developed in [Fritz's Markov-category paper][fritz] and already represented
in the pinned Mathlib structures.

Use symmetric monoidal composition and explicit copying/discarding, with
copy preservation required only for arrows satisfying that law. Keep pure
values and effectful computations distinct in any later compiler fragment.
The direct kernel library can precede that frontend. A new SquareKit interface
is justified only where adapting Mathlib structures and existing maps fails
to remove repeated caller obligations. Do not create a second Markov-category
hierarchy just to rename the existing one.

Exact realization can be expressed by a measurable decoding map `d` and a
commuting kernel equation: pushing the implementation transition forward
along `d` equals the specification transition at `d x`. Composition should
then transport finite-step laws. For approximate implementations, a relation
on values alone loses probability mass and correlation; use a stated distance,
coupling, or expectation contract and prove its composition rule. Almost-everywhere
equality must name its reference measure and prove compatibility with the
compositions used. It is not a universal substitute for pointwise kernel equality.
These are proposed integration contracts, not implemented declarations.

## A reusable MH construction

[Tierney's general-state-space treatment][tierney] provides the appropriate
mathematical specification. For a proposal kernel `Q` and a measurable
acceptance function `a(x,y)` in `[0,1]`, define the next-state kernel as

```text
K(x, A) = integral_A a(x,y) Q(x,dy)
        + indicator_A(x) * (1 - integral a(x,y) Q(x,dy)).
```

The rejected probability stays at the current state. Start with that general
accept/reject construction and prove normalization. Then prove reversibility
under symmetry of the accepted proposal flow
`pi(dx) Q(x,dy) a(x,y)`. Reuse Mathlib's existing reversibility-to-invariance
theorem. This separates the reusable balance argument from a chosen formula
for computing acceptance probabilities.

For a nonempty finite state space with positive finite unnormalized target
weights `w`, normalize by their finite positive sum. The
usual off-diagonal choice is
`a(x,y) = min(1, w(y) q(y,x) / (w(x) q(x,y)))` whenever `q(x,y)>0`.
Choose and document a harmless value when `q(x,y)=0`, since that proposal has
zero mass. A proposal with zero reverse probability must be rejected. Allowing
zero target weights requires a stated support policy and separate cases;
Lean's totalized division must not choose that policy accidentally.

General measurable MH uses forward/reversed proposal measures and
Radon-Nikodym/support arguments; a pointwise density ratio does not cover every
kernel. Abstract Markov-category axioms alone do not provide densities,
conditioning, division, or ergodic convergence. Expose additional assumptions
at the construction that uses them.

A first implementation should connect two views of the same construction:
finite rational weights and proposal tables with exact computations, and the
Mathlib kernel interpretation. Exercise generic balance and composition
through this bridge. Ideal randomness belongs to the specification; a finite
random-bit interpreter can expose fuel exhaustion or residual computation.
Composition of kernels preserving the same target reuses `Invariant.comp`;
reversibility of each factor does not in general make their composite reversible.
An arbitrary rational Bernoulli probability cannot always be implemented
exactly by a fixed number of fair bits. A seeded PRNG is deterministic, so
sampling correctness must state a seed/input distribution or a separate
approximation assumption.

Keep the resulting claims separate:

- **Stationarity:** starting at `pi` leaves `pi` unchanged.
- **Convergence:** approaching `pi` from other initial states needs hypotheses
  such as irreducibility and aperiodicity in the finite case; general spaces
  require an appropriately stated ergodic theorem.
- **Estimation:** convergence of empirical averages, error bounds, and confidence
  statements need their own integrability and dependence assumptions.
- **Execution:** finite budgets, proposal termination, PRNG behavior, arithmetic
  approximation, and physical faults need realization contracts.

As simple counterexamples, the identity kernel preserves every distribution
but never approaches a different initial law. Deterministic alternation on two
states preserves the uniform law but oscillates from a point mass. They prevent
stationarity from being mistaken for convergence. A fixed burn-in count is not
an accuracy certificate. [Tierney’s convergence treatment][tierney-convergence]
provides the general-state-space reference for selecting later ergodic and
estimator contracts.

Finite-horizon approximation can later compose one-step kernel errors under
an explicit metric and hypotheses. A useful candidate is total variation:
if every state has one-step error at most `epsilon`, Markov contraction and a
telescoping argument give an error at most `n*epsilon` after `n` steps with the
same initial law. This proposed finite-horizon argument neither bounds the
stationary-law perturbation nor proves numerical correctness of an acceptance
test. Rounding a density or threshold needs its own error analysis.

## Nontermination, productivity and faults

Probabilistic algorithms belong in the library even when some ideal random
tapes diverge. Represent their operational steps, finite observations and
probability measures explicitly in Lean; do not ask Lean to accept an
unrestricted recursive function as a total one. Subprobability semantics can
record missing termination mass. Unnormalized weights, explicit failure,
timeout, and divergence need distinct interpretations even when all are
represented using measures. A mass-one denotation alone does not connect a
particular executable implementation to almost-sure termination.

Ordinary MH emits the current state on every completed iteration, including
rejection. A bounded number of MH iterations terminates when its primitive
operations do. Waiting until a proposal is accepted changes the progress
question; removing rejected steps also changes the sampled chain and generally
biases occupancy statistics unless holding times or the new invariant law are
accounted for. Rejection samplers inside proposals and adaptive stopping rules
are separate possible sources of nontermination.

For a measurable execution model and finite-output hitting times `T_n`,
almost-sure productivity asks for `P(T_n < infinity)=1` for every natural `n`.
Countable intersection then gives probability one of producing every finite
prefix. This does not assert a uniform finite bound or finite expectation.
[Aguirre, Barthe, Hsu and Silva][asp] develop almost-sure productivity explicitly,
including silent steps and probabilistic streams/trees. Their paper is a
semantic and verification reference, not a local implementation.

A useful hierarchy of separate contracts is:

| Contract | What it does not establish |
|---|---|
| Every admissible execution terminates | A uniform runtime bound across inputs. |
| Termination has probability one | Termination on every random tape or finite expected runtime. |
| Expected runtime is finite | A hard deadline. |
| `P(T > b) <= delta` | Certain completion by `b`, or output accuracy. |
| Output is statistically accurate under stated hypotheses | Termination, independence of repeated outputs, or fault-free execution. |

A fair-coin retry until success has an infinite all-failure tape of probability
zero, while its probability of needing more than `b` trials is `2^(-b)`.
Almost-sure termination can also have infinite mean runtime. Expected-runtime
reasoning therefore needs more than a Boolean termination certificate;
[Kaminski et al.][runtime] provide a compositional expectation-based calculus.
Per-input finite expected runtimes of two stages do not alone establish a
finite expectation for their composition: the first stage can produce a
heavy-tailed input to the second. State integrability under the intermediate
output law.

The repository already models alternatives through relations, including
[optimization thinning](../../Applications/Optimization/Thinning.lean); the
missing work concerns stochastic semantics and probabilistic progress.
Nondeterminism specifies alternative behaviors without assigning probabilities.
Probability specifies a law. Mixed models must quantify over the permitted
schedulers or policies, their information, and fairness assumptions. A result
for one randomized scheduler is not a guarantee against all schedulers.
[McIver et al.][ast] give almost-sure termination rules that explicitly account
for demonic choice. Likewise, correlating two random sources or faults cannot be dismissed by
assuming independence from their marginal distributions.

The comparison with machine error needs the same observation and time horizon.
An ideal nontermination event may have probability zero while missing a useful
deadline has substantial probability. Conversely, a model may allow positive
nontermination mass. No hardware error rate has been supplied here. A common
model could combine statistical, timeout, numerical, and fault error budgets;
a union bound needs no independence when each bound holds in that same model.
But no probability argument repairs a wrong specification or eliminates the
trusted execution of Lean's checker. #196 should own the fault/environment
assumptions; the probability library should express them without choosing them.

## Which probability formalization?

There is no single best foundation for all the intended settings. The following
choices address different requirements.

| Approach | Best fit | Limitation or integration obligation |
|---|---|---|
| Classical measures and kernels; Markov categories | Immediate first-order MH, composition, statistical mathematics. Already checked in pinned Mathlib. | Measurable spaces are not cartesian closed. Markov laws alone do not supply every analytic construction. |
| Quasi-Borel spaces (QBS) | Higher-order functions with continuous probability. | Requires a Lean model and comparison to kernels; does not by itself solve arbitrary recursion or constructive topos transport. |
| Quasi-Borel predomains | Higher-order statistical programs with recursion and partiality. | Substantially larger semantic development; not needed for finite-step MH. |
| Valuation locales and constructive integration | Probability in constructive/internal settings, with behavior under changes of base made explicit. | Values on opens, lower reals, continuity and integration principles differ from classical measurable-set interfaces. |
| Probability sheaves | Random variables varying over sample spaces; categorical independence and probability constructions. | Requires a selected site and a proved interpretation/comparison. It is not supplied by the repository's existing geometric sheaves. |

[Heunen, Kammar, Staton and Yang][qbs] give the higher-order QBS model.
[Ścibior et al.][inference] are especially relevant to this repository: they
organize inference by representations and semantics-preserving transformations,
and prove a synthetic MH-Green theorem. This is a closer design reference for
an eventual inference compiler than treating MH as an opaque primitive.
[Vákár, Kammar and Staton][domains] add domain structure for recursion.

These semantic papers should be distinguished from checked libraries.
Isabelle's Archive of Formal Proofs includes both
[Quasi-Borel Spaces][afp-qbs] and an
[S-Finite Measure Monad on Quasi-Borel Spaces][afp-sfinite]. Their formalized
function spaces, probability/measure machinery and examples are porting
references; they are not Lean dependencies or imported proofs.

For the user's question about other topoi, [Vickers][valuations] constructs a
valuation-locale monad with Fubini/Riesz results under geometric constraints.
[Coquand and Spitters][integrals] give a constructive relation between integrals
and valuations. [Simpson's probability sheaves][sheaves] generalize Giry in a
sheaf setting. [Stein (2025)][stein] connects Markov categories **with conditionals** to
sample-space categories and probability sheaves. This suggests a direct route
from kernels to sheaf-based probability; an arbitrary Markov category alone
does not discharge the conditional-existence assumptions. These are ongoing
mathematical developments, not identified Lean implementations.

These are substantive alternatives, not reasons to discard
classical measure theory for the first implementation. They do not establish
that classical Mathlib proofs automatically transport into every sheaf model.

The comparison experiment should distinguish two questions: a higher-order
semantic category, and probability proved internally in varying settings.
Choose a small integration/expectation argument, list its actual assumptions,
and test two interpretations with a comparison on their common fragment.
A distribution of functions tests QBS; a valuation on opens tests constructive
internal probability. Requiring either to satisfy the other's entire interface
would hide precisely the distinctions the shared-language programme seeks to
express. No global foundational choice or ADR is settled by this research.

## Follow-up scope

1. **Kernel-backed stochastic composition and finite MH.** Reuse Mathlib and
   the general SquareKit category/map infrastructure. Prove the general
   accept/reject normalization and balance contract; recover finite rational
   MH through a proved interpretation, including asymmetric proposals and
   zero reverse probability. Show finite-step composition, shared versus
   independent sampling, and invariance without convergence. Keep a full
   effectful frontend, general ergodic theorem, and floating-point sampler
   outside this bounded delivery.
2. **Probabilistic partiality and finite delivery.** Extend the question
   addressed by #146 with explicit execution probability, silent steps, and
   probability-one progress. Compare a subprobability result semantics with
   a path/hitting-time semantics. Require a compositional progress result,
   a fair-coin retry example, an infinite-expectation limitation, timeout
   semantics, and scheduler quantifiers if nondeterminism is included.
   Coordinate with #109/#131/#193/#196; do not duplicate their ownership.
3. **Higher-order and internal probability model comparison.** Research a
   bounded QBS/inference-transformer example and a valuation/probability-sheaf
   example for #36's shared-language objective. Inventory checked external
   artifacts, exact hypotheses, and comparison obligations. The deliverable
   is a justified next experiment or an explicit unresolved obstruction,
   not a complete new probability foundation.

Each implementation follow-up needs checked specializations, statement review,
fresh source compilation, the normal proof audit, and independent Standards
and Spec review. This note changes documentation only; it introduces no formal
claims into the Lean kernel and requires no Lean rebuild.

[kernel]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Defs.lean
[markov]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/MarkovCategory/Basic.lean
[stoch]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Category/Stoch.lean
[sfinker]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Category/SFinKer.lean
[invariance]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Invariance.lean
[traj]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean
[pmf]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/ProbabilityMassFunction/Monad.lean
[representation]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Representation.lean
[giry]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/GiryMonad.lean
[relations]: ../../SquareKit/RelationalCategory.lean
[fritz]: https://arxiv.org/abs/1908.07021
[tierney]: https://www2.stat.duke.edu/~scs/Courses/Stat376/Papers/TransdimMCMC/TierneyAAP1998.pdf
[asp]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.113
[runtime]: https://arxiv.org/abs/1601.01001
[qbs]: https://arxiv.org/abs/1701.02547
[inference]: https://arxiv.org/abs/1711.03219
[domains]: https://arxiv.org/abs/1811.04196
[afp-qbs]: https://isa-afp.org/entries/Quasi_Borel_Spaces.html
[afp-sfinite]: https://isa-afp.org/entries/S_Finite_Measure_Monad.html
[valuations]: https://sjvickers.github.io/Riesz.pdf
[integrals]: https://arxiv.org/abs/0808.1522
[sheaves]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CALCO.2017.1

[felix-raw]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda
[felix-maps]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda
[felix-comma]: https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda
[tierney-convergence]: https://www.ma.imperial.ac.uk/~das01/MyWeb/SCBI/Papers/Tierney94.pdf
[ast]: https://arxiv.org/abs/1711.03588
[stein]: https://arxiv.org/abs/2503.02477
