# Higher-order and internal probability: a bounded comparison

Research for [#199](https://github.com/VladimirMarko/conaled/issues/199),
2026-10-28. Baseline: `c914bbf2631593b4236defa2f70cde16672bdff8`;
Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The [initial probability note](probability-and-monte-carlo.md) motivates the
kernel work. This comparison constrains that work before implementation.
Its examples and proposed signatures are mathematical designs, not checked
Lean declarations. It adopts no ADR and does not complete #36.

**Proceed with ordinary kernels for #197 and execution measures for #198.**
Keep optional models behind interpretations. Two additional requirements are
worth testing separately: returning and consuming random functions, and
integrating observations whose probability is only locally approximable from
below. Neither requires a new universal interface before finite MH.

## Available foundations and checked artifacts

The pinned [Stoch source][stoch] defines probability kernels as a wide
subcategory of s-finite kernels and supplies positive Markov structure.
[Invariance][invariance] defines `Kernel.Invariant` as `μ.bind κ = μ`, proves
`Invariant.comp`, and proves `IsReversible.invariant` with an
`IsMarkovKernel` assumption. These are checked Mathlib dependencies. The
[representation theorem][representation] assumes a standard Borel target
when representing a kernel by a measurable randomization. These hypotheses
must survive any wrapper.

Local [Category](../../SquareKit/Category.lean) already has `ofCategory`;
[CategoryMap](../../SquareKit/CategoryMap.lean) separates `RawMap`, `MapLaws`,
and reflection. Its composition and transport lemmas are the starting point
for interpretation reuse. No additional stochastic hierarchy is justified
merely by introducing another semantic model. The
[Felix implementation record](felix-parity-implementation.md) records the
inherited operations/laws/maps architecture; this note proposes no upstream
probability capability. Current geometric sheaves are not probability sheaves.

| Source inspected | What is available | Status for this repository |
|---|---|---|
| [Heunen–Kammar–Staton–Yang][qbs] | QBS, cartesian closure, continuous distributions, comparison with measurable spaces. | Mathematical reference; no imported QBS model. |
| [AFP Quasi-Borel Spaces][afp-qbs] | Function spaces, measure/QBS adjunction, probability monad, Bayesian regression. | Isabelle/HOL porting reference, not a Lean dependency. |
| [AFP Exponent_QuasiBorel][afp-exp] | Inspected `exp_qbs`, `qbs_eval_morphism`, `curry_morphism`, `uncurry_morphism`. | Checked source declarations in AFP; not rebuilt here. |
| [AFP S-Finite Measure Monad][afp-sfinite] | S-finite kernels, QBS measure monad, morphism automation and examples. Entry records a measure-definition update on 2025-01-26. | Consult current definitions when porting; do not assume the older probability API is identical. |
| [AFP Montecarlo][afp-mc] | Inspected `montecarlo`, `montecarlo_qbs_morphism`, `montecarlo_integrable`, and expectation reasoning under probability/integrability hypotheses. | Example source, not evidence for all MH or convergence claims. |
| [Vákár–Kammar–Staton][domains] | Quasi-Borel predomains combine order and random elements; adequate semantics includes recursion, continuous sampling and soft constraints. | Mathematical reference, not an installed Lean implementation or a prerequisite for #198. |
| [Vickers][valuations], [Coquand–Spitters][integrals] | Valuation/integration mathematics described below. | No checked Lean realization identified in the inspected sources. |
| [Simpson][simpson], [Stein][stein] | Probability sheaf mathematics described below. | Papers; no imported probability-sheaf implementation identified. |

This inventory distinguishes inspected source from proofs rerun in our build.
It is not a claim that no other formalization exists.

## Higher-order experiment: sample a function once, use it twice

QBS specifies admissible random elements `ℝ → X`, closed under constants,
measurable reparameterization and countable measurable case splits. A map
preserves those elements. Function spaces then support evaluation and currying;
standard Borel spaces embed with their usual probability interpretation.
This addresses the absence of cartesian closure for arbitrary measurable
spaces. It does not make every set-theoretic function admissible. See
[the QBS construction][qbs] and the [checked exponential definitions][afp-exp].

Use this worked fixture, with independent uniform `A,B` on `[0,1]`:

```text
make : P (Real ⇒ Real)
make = do a ← uniform01; b ← uniform01; pure (fun x => a*x + b)

observe : (Real ⇒ Real) → Real × Real
observe f = (f 0, f 1)

shared = map observe make
fresh  = do f ← make; g ← make; pure (f 0, g 1)
```

The returned value really has function type: it can be passed to a consumer
before selecting evaluation arguments. The law of `shared` is the pushforward
of the uniform square by `(a,b) ↦ (b,a+b)`. Its two coordinate means are
`1/2` and `1`; their covariance is `Var(B)=1/12`. For `fresh`, independently
sampled coefficients make the covariance zero with the same marginals.
These numbers follow from integrating `b`, `b²` on `[0,1]`; all variables
are bounded, so the needed integrals exist. This is our proposed test fixture,
not a theorem claimed from the cited papers.

A classical kernel implementation can retain the coefficient pair as a
closure environment and implement this particular observation exactly.
Thus this fixture does **not** prove that first-order kernels cannot represent
its output law. The extra requirement appears when a reusable consumer
accepts arbitrary admissible functions rather than this fixed pair encoding.
Finite kernels do not supply that exponential. Requiring preservation of
`eval` and `curry` tests the distinction; merely computing the two numbers does
not establish a higher-order model.

The smallest proposed higher-order signature is a cartesian closed **value**
category with a commutative strong probability monad `P`, the real object,
measurable arithmetic and `uniform01 : 1 → P Real`. Its computation arrows
are Kleisli arrows. Monad unit/bind laws and strength connect environments to
sampling; commutativity permits reordering independent samples. It does not
permit replacing `shared` with `fresh`. Cartesian value copying is compatible
with this design; cartesian laws on arbitrary effectful arrows are not.
Recursion and weighting are absent from this signature.

Candidate comparison: for standard Borel `X,Y`, identify the QBS probability
arrows on their embeddings with ordinary kernels. Prove preservation of
Dirac, bind and independent product, then prove that pushing `make` through
`observe` agrees with the classical coefficient kernel. Do not require the
whole exponential `Real ⇒ Real` to be a standard Borel object. The checked
AFP adjunction is a porting reference, not that Lean comparison theorem.

## Internal experiment: an open observation with only lower information

A continuous valuation assigns nonnegative extended lower-real values to
opens, is strict at the empty open, modular, and preserves directed joins.
Probability valuations additionally have total mass one. Vickers constructs
a commutative strong valuation monad with integration/Fubini under geometric
constraints. Coquand–Spitters relate integrals on a Riesz space to valuations
on its spectrum through geometric theories. These are not unrestricted
identifications of arbitrary measures with valuations.
[Vickers][valuations]; [Coquand–Spitters][integrals].

Here is a worked varying-parameter example. Let `S` be the Sierpiński locale,
whose external opens are `∅`, `{⊤}`, `S`. For an ordinary number `p ∈ [0,1]`,
set `νp(∅)=0`, `νp({⊤})=p`, `νp(S)=1`. Modular identities follow by checking
the three comparable opens. For the lower-semicontinuous observation
`h=1_{ {⊤} }`, lower integration gives `∫h dνp=p`.

Now vary over the base `B=ℝ` with

```text
p(b) = 1 if b > 0, otherwise 0.
```

This is lower semicontinuous: for rational thresholds between zero and one,
`{b | p(b)>r}` is `(0,∞)`. It gives a continuous family of valuations when
the valuation space is tested by lower bounds on open probabilities.
As an internal lower real in sheaves over `B`, its positive evidence becomes
available locally. There is no corresponding continuous Dedekind-real
function with these values, since it jumps at zero. Also `1-p` is not lower
semicontinuous: its positive locus is `(-∞,0]`, which is not open.

The proposed internal result is the integral equation for that open
observation and its compatibility with restriction to open subsets of `B`.
It exposes a limitation a finite stochastic matrix with ordinary real entries
hides: the complement observation is not an open of `S`, and its probability
cannot be manufactured as a lower real by subtraction. Normalization alone
does not supply locatedness. Giving both complementary probabilities, or a
Dedekind-real parameter, is an additional requirement.

This example describes the external family and a proposed internal
interpretation. Internally, one must use the frame presentation generated by
an open, including joins indexed by internal truth values; it is incorrect
to declare that its internal frame has only three elements. A formalization
must prove extension from generators and compatibility with these joins.

The smallest proposed valuation signature has a frame presentation,
nonnegative lower reals, a normalized continuous valuation, lower integrals
of nonnegative lower-semicontinuous observations, and pushforward along
locale maps. The one-observation calculation needs only its indicator
integral law. Bind/Fubini is added when composing valuation kernels. No
Boolean complement, arbitrary measurable predicate, real division or
conditioning operation is implicit.

For a comparison experiment, restrict first to finite **discrete** spaces
with specified nonnegative rational masses summing to one. Every subset is
open and `ν(U)=Σ_{x∈U} w(x)` equals the corresponding kernel measure; for
nonnegative rational observations, both integrals are the same finite sum.
Prove Dirac, bind and product compatibility there. This common fragment
does not establish a measure extension theorem for general locales. The
Sierpiński family tests precisely the additional lower-information behavior.

For general changes of base, transport geometric presentations and their
interpretations with explicit comparison isomorphisms. Applying inverse
image to a frame's underlying object does not preserve its entire power
object or supply all joins in the new topos. Consequently the proposed
restriction theorem cannot be replaced by a blanket claim that classical
Lean proofs transport. This distinction is explicit in
[Vickers, §2][valuations].

## Probability sheaves: a separate route to random-variable context

Stein starts with a Markov category **with conditionals**, forms state-bearing
objects, quotients state-preserving arrows by the source state's almost-sure
equality, and selects almost-surely deterministic arrows for sample spaces.
Sections IV–V establish independence and sheaf conditions. Standard Borel
kernels are a relevant example; arbitrary measurable-space kernels do not
supply the required conditionals merely by being Markov. The paper leaves
expectation/conditional-expectation development as future work.
[Stein, §§II, IV–VI][stein]. Simpson's earlier construction connects probability
sheaves to Giry. [Simpson][simpson].

A bounded proposed example uses a fair-bit sample space `Ω`, its product
`Ω×Ω`, and the two projections. Pulling one random variable along the first
projection twice retains equality; using both projections yields independent
bits. Both laws are computable in finite kernels, but the sheaf experiment
also tracks which sample-space extension supplies the variables and whether
compatible observations descend. Equality in distribution alone forgets
that context. Its acceptance must include a selected site, the random-element
presheaf's action, and the sheaf/descent proof, not just the four-entry table.

This is a possible later bridge from #197. It does not replace the valuation
experiment: a sheaf topos of random variables and a valuation internal to a
varying base answer different questions. Neither follows from the repository's
existing Sierpiński geometric examples without a new interpretation.

## Modular inference and the exact MH-Green obligation

Ścibior et al. separate an inference representation `T` from its meaning
`mT : T X → M X`; transformations preserve meaning, and transformers build
representations compositionally. Their Theorem 7.1 uses QBS and a proposal
whose meaning `k` is Markov. Writing
`μ = [ρ≠0] · (mT(a) ⊠ k)`, it requires: reciprocal densities
`(ρ ∘ swap)*ρ=1` μ-almost everywhere; `ρ·μ=swap_*μ`; and the pointwise
symmetric zero condition `ρ(x,y)=0 ↔ ρ(y,x)=0`. The accept/reject update
preserves `mT(a)`. The paper's synthetic absolute continuity is defined by
existence of a weighting morphism, so a general classical Radon–Nikodym
existence theorem is not obtained for free. [§§3, 4.2.3, 7.1][inference].

Our architectural inference is to use that representation/meaning pattern
immediately, while leaving its full QBS implementation optional. An exact
rational proposal table and its kernel meaning can share one acceptance
construction and one balance proof. A transformation certified once by
`meaning (transform t) = meaning t` can compose with another such transform
by equality transitivity. This reduces repeated integration proofs at call
sites; it does not eliminate proposal-specific support and normalization
obligations. Existing map laws can express compositional interpretations;
representation transformations need not themselves be categorical functors.

For #197, an accepted-flow symmetry theorem is a smaller initial contract
than the full synthetic theorem. The latter additionally needs weighting,
joint measures, swaps, almost-everywhere predicates, and density witnesses.
Lean would need their QBS interpretation and compatibility proofs before
claiming synthetic MH-Green. Reversibility/invariance says nothing about
mixing time, estimator accuracy, termination or random-bit realization.

## What transports, and what must remain explicit

| Principle | Proposed transport contract | Boundary |
|---|---|---|
| Sequential composition and finite iteration | Preserve Dirac and bind; use existing category/map laws. | Equality of outputs alone does not preserve elapsed time. |
| Independent product | Preserve strength/product and its commutativity law. | Equal marginals do not determine joint laws. |
| Function application | Preserve the chosen exponentials and evaluation. | The standard Borel common fragment is not closed under all function spaces. |
| Finite discrete expectation | Preserve finite sums, scalars and observation decoding. | Extending to all integrals needs continuity/integrability theorems. |
| Internal restriction | Interpret a geometric presentation and prove coherent base-change comparison. | Classical choice, complements and full power objects are not supplied by this contract. |
| Density-based acceptance | Preserve weighting, joint flow, support conditions and density witness. | Markov structure alone supplies none of density existence or division. |
| Conditional probability | Supply disintegration/conditionals for the selected model. | Not automatic for all measurable spaces or all higher-order objects. |
| Almost-sure delivery | Preserve execution law and measurable finite-output hitting events. | A result-measure comparison alone cannot distinguish delay schedules. |

## Next experiment and constraints on #197/#198

The next higher-order formal experiment should implement the probability-only
QBS fragment and the random-affine-function comparison. Acceptance is:

1. Checked admissibility of `make`, `observe`, evaluation and currying, using
   reusable function-space and monad laws rather than a special closure encoding.
2. A proved interpretation of its finite observations into ordinary kernels,
   preserving unit/bind/product on the stated common fragment.
3. Checked shared/fresh covariance results and a negative equality example.
4. Ordinary kernel callers remain direct clients; no global model switch or
   new axioms. Fresh compilation, statement review and proof audit apply.

That is substantial model work. Before funding a whole QBS port, a smaller
closure-environment prototype may validate the comparison diagram, but must
be labelled a first-order prototype and cannot satisfy item 1.

The separate internal experiment should first prove the finite-discrete
valuation/measure comparison, then the Sierpiński-family integral and
restriction theorem with a geometric presentation. Require an explicit
failure/extra-obligation case for complementary lower probabilities. Stop
at that obstruction if the available internal-language fragment cannot
express the required joins; do not encode them as unexplained axioms.

For the already authorized implementation sequence:

- **#197:** keep pure maps distinct from kernel arrows; use Mathlib kernels,
  generic accepted-flow balance, and an exact finite interpretation. Preserve
  joint distributions and leave target/support assumptions visible. Do not
  require QBS, global conditionals, or an executable sampler for ideal laws.
  Start with pointwise kernel equality; an almost-everywhere quotient needs
  a named source measure and congruence proofs. Finite rational tables are
  a realization, not a restriction on the general semantic interface. Impose
  standard Borel assumptions where randomization or conditioning uses them,
  not on every basic composition theorem. Arbitrary `Stoch` arrows are not
  cartesian, even though their state spaces have ordinary products.
- **#198:** model path probability, silent transitions and finite observations
  separately from output subprobability. Its semantic comparison must connect
  mass loss to actual divergent paths. Preserve hitting-time events when
  claiming progress; bind of result laws alone does not do this. Plain QBS
  closure supplies no recursive operational adequacy theorem. Missing
  termination mass is distinct from discarded output, explicit failure and
  unnormalized likelihood weight. Discarding a normalized result retains
  unit mass; discarding a subprobability result retains its termination
  probability. Conditioning/renormalization would erase that missing mass
  and needs a positive finite normalizer and a separate contract.
- **#196:** retain ownership of faults/environment assumptions. A common
  probability space may later combine them with timeout events; this note
  supplies no hardware failure rate or independence assumption.

These constraints allow #197 then #198 to proceed without committing to a
full higher-order or constructive foundation. The additional experiments
would justify their own optional models through checked comparisons.

[stoch]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Category/Stoch.lean
[invariance]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Invariance.lean
[representation]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Representation.lean
[qbs]: https://arxiv.org/abs/1701.02547
[afp-qbs]: https://isa-afp.org/entries/Quasi_Borel_Spaces.html
[afp-exp]: https://isa-afp.org/browser_info/current/AFP/Quasi_Borel_Spaces/Exponent_QuasiBorel.html
[afp-sfinite]: https://isa-afp.org/entries/S_Finite_Measure_Monad.html
[afp-mc]: https://isa-afp.org/browser_info/current/AFP/S_Finite_Measure_Monad/Montecarlo.html
[domains]: https://arxiv.org/abs/1811.04196
[valuations]: https://sjvickers.github.io/Riesz.pdf
[integrals]: https://arxiv.org/abs/0808.1522
[stein]: https://arxiv.org/html/2503.02477v1
[simpson]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CALCO.2017.1
[inference]: https://arxiv.org/html/1711.03219v1
