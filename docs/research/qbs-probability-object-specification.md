# QBS probability objects and general sequencing

[#438](https://github.com/VladimirMarko/conaled/issues/438) can proceed to a
bounded implementation of the probability object and strong bind. The missing
step is the construction of probability-valued random curves, including their
common representations. Existing represented-sampler substitution supplies
part of the integration argument, but does not supply this object.

This is a mathematical specification and implementation decomposition, not a
new Lean theorem or an architecture decision. Repository declarations were
inspected at `e6fc65e542ee90a2d5bb1552db3d905a70f7b4d6`; Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679` and Lean to `v4.35.0`. The proposed
names below are targets, not declarations already exported by the library.

## Sources and existing capabilities

The primary construction is Heunen, Kammar, Staton and Yang,
[*A Convenient Category for Higher-Order Probability Theory*,
arXiv:1701.02547v4](https://arxiv.org/html/1701.02547v4), dated 20 November 2020.
Sections V-C/D define the quotient by induced measure and its random curves;
Theorem 21 supplies strong bind. Proposition 22 records commutativity and the
standard-Borel comparison, and Proposition 23 allows other standard-Borel
seed spaces. The discussion after Proposition 19 explicitly excludes a general
product-preservation law for the generated sigma algebra. These are published
results, not imported axioms. The construction steps and client below are our
proposed local proof obligations and paper derivations.

| Inspected file | Existing checked interface and limit |
|---|---|
| [QuasiBorel.lean](../../Applications/Probability/QuasiBorel.lean) | `Space` has real random curves, constants, measurable reparameterization, and countable measurable selection. `prod`, `exp`, `eval`, `curry`, `uncurry`, `uncurry_curry`, and `curry_uncurry` construct binary products and exponentials. `sigma`, `random_measurable`, `Hom.measurable`, `Hom.measurable_source`, and `Hom.measurable_observer` connect these to measures. There is no probability object. |
| [RandomFunction.lean](../../Applications/Probability/RandomFunction.lean) | `law`, `law_probability`, `law_map`, `law_observe`, and `law_dirac` concern actual pushforward measures. `deterministic_bind` is Dirac sequencing. `independent_observations` uses separate standard-Borel seeds. Random affine and polynomial functions are actual admitted function values. |
| [SamplerSubstitution.lean](../../Applications/Probability/SamplerSubstitution.lean) | `seeded` requires a supplied `Hom (prod X (ofMeasurable T)) Y`. `event_measurable` proves parameterized event probabilities on `sigma X`; `seeded_apply` gives their integral. `law_substitution`, `retained_law_substitution`, `two_stage_substitution`, and `seeded_deterministic` preserve represented laws. They do not quantify over `Hom X (P Y)`. |
| [SamplerClient.lean](../../Applications/Probability/SamplerClient.lean) | `transition`, `secondTransition`, `kernel_pair`, and `kernel_three` give ordinary finite Markov-kernel comparisons. `copied_not_fresh` and `reused_seed_wrong` retain correlation and seed-reuse controls. |
| [Represented-sampler report](represented-sampler-substitution.md) and [examples](../../Examples/SamplerSubstitution.lean) | Existing semantic records, coupling and complemented-seed examples distinguish equal laws from selected realizations. None claims quotient construction or general bind. |

Reuse Mathlib's measure operations rather than introducing a second integration
library. At the pinned revision,
[GiryMonad.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Measure/GiryMonad.lean)
exports `Measure.measurable_of_measurable_coe`, `measurable_map`,
`measurable_dirac`, `bind_apply`, `measurable_bind'`, `bind_map`, `map_bind`,
`bind_bind`, `dirac_bind`, and `bind_dirac`.
`bind_apply` requires an a.e.-measurable measure-valued continuation;
`bind_bind` requires the corresponding a.e.-measurability at both stages.
Global measurability constructed below discharges these hypotheses.
`measurable_bind'` varies the input measure with a *fixed* kernel; it alone
does not prove joint measurability when the kernel varies too.
[MeasurableLIntegral.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/MeasurableLIntegral.lean)
provides `Measurable.lintegral_kernel_prod_right` for that parameterized step.
These are source-inspected reuse candidates; the new compositions have not
been elaborated in Lean.

## Carrier, equality, size and empty spaces

Stay with the existing `Space.Carrier : Type` and real seed type. For X define

```text
Rep X := { a : ℝ → X // X.random a } × ProbabilityMeasure ℝ
Rep.law (a, μ) := (μ : Measure ℝ).map a : Measure (sigma X)
r ≈ s := r.law = s.law
Prob X := Quotient (the setoid ≈)
toMeasure : Prob X → Measure (sigma X)
```

`Measure (sigma X)` here means measures on X with the explicitly supplied
`sigma X` instance, not Lean's literal type syntax. Each `Rep.law` is a
probability measure by `random_measurable`. The equality is equality on every
measurable event, not equality of selected seeds, finitely many moments, or
pointwise sample outputs. `toMeasure` descends and is injective precisely
because the setoid uses that equality. Surjectivity onto all measures on an
arbitrary X is neither required nor claimed. An equivalent subtype of
representable measures could replace this quotient, but must prove the same
random-curve and bind obligations; that representation choice is local.

No universe increase through a type of *all* seed spaces is needed: Rep and
Prob remain small carriers in `Type`, while their bundled spaces inhabit the
same level as existing `Space`. A universe-polymorphic QBS library is separate
work. Avoid a new `Nonempty X` premise on the public construction. If X is
empty there is no real-to-X map, so `Rep X` and `Prob X` are empty; unit has
empty domain. Extracting a point of a seed space from a probability measure
is valid, but must be proved rather than installed as an unexplained instance.
Classical representative choice is allowed in the noncomputable semantic
construction. It supplies no executable sampler or extraction algorithm.

## Random curves: a fixed map and varying seed law

Define the proposed QBS structure `P X` on `Prob X` by

```text
(P X).random p ↔
  ∃ a : ℝ → X, X.random a ∧
  ∃ g : ℝ → ProbabilityMeasure ℝ,
    Measurable (fun r => (g r : Measure ℝ)) ∧
    ∀ r, p r = classOf (a, g r).
```

Using measurable coercion to `Measure ℝ` avoids conflating the evaluation
sigma algebra with any separately inferred topology on probability measures.
A local wrapper may bundle g as a normalized kernel. Every family uses one
map a, while its measure g r varies measurably. Requiring only
`∀ r, ∃ a μ, p r = classOf (a, μ)` would admit arbitrary nonmeasurable families
and would not justify bind. Conversely, no global measurable selection of a
representative for every quotient element is assumed.

The following constructions must establish the three `Space` fields.

- Constants: choose a representative `(a, μ)` of the given quotient element
  and use the constant kernel μ. This construction has no empty-space case
  needing an invented inhabitant, since the element itself supplies one.
- Reparameterization: retain a and precompose g with the measurable real map.
- Countable selection: from representations `(a_n, g_n)` and measurable
  `i : ℝ → ℕ`, construct one map on `ℕ × ℝ`, `(n,s) ↦ a_n s`. Encode this
  standard-Borel space into ℝ with a measurable retraction, obtaining a single
  random map a*. Push `g_n r` along `s ↦ encode(n,s)`, then select the resulting
  probability measure using i r. Measurability follows from countable
  selection and measurable pushforward. Its law under a* is the selected
  original law. The a* randomness proof uses `Space.select` after decoding,
  including measurable tag and seed projections.

Required seed-encoding helper: for nonempty standard-Borel S, choose measurable
`encode : S → ℝ`, `decode : ℝ → S` with `decode (encode s) = s`.
[Mathlib's EmbeddingReal.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Constructions/Polish/EmbeddingReal.lean)
supplies `measurableEmbedding_embeddingReal`; the existing
`Hom.measurable_source` already uses its measurable inverse function and left
inverse. Probability on empty S is impossible, so that general lifting case
is discharged separately. No measurable bijection with all of ℝ is needed.

A second helper packages the point of these encodings:

```text
standardFamilyRepresentation (h : Hom (ofMeasurable S) (P X))
  [StandardBorelSpace S] [Nonempty S] :
  ∃ a g, X.random a ∧ Measurable (measureCoercion ∘ g) ∧
    ∀ s, h s = classOf (a, g s)
```

Proof plan: apply `h.preserves` to the measurable decode curve, obtain its
common representation, and precompose its kernel with encode. This is a
representation of a family indexed by S, not a selection theorem for arbitrary
families indexed by X. In particular use S = ℝ × ℝ in the strong-bind proof.

## Measurable event probabilities and descent

For E measurable in `sigma X`, prove
`p ↦ toMeasure p E` is a QBS morphism from `P X` into `ofMeasurable ℝ≥0∞`.
On a random curve represented by a,g it is
`r ↦ g r (a ⁻¹' E)`. The preimage is measurable by `random_measurable`, and
evaluation on a measurable set is measurable by GiryMonad's `measurable_coe`.
`Hom.measurable_observer` then gives measurability on `sigma (P X)`.
Eventwise measurable extensionality gives measurability of `toMeasure` itself.
For `f : Hom X (P Y)`, therefore `K_f x := toMeasure (f x)` is an ordinary
measurable probability kernel on `sigma X` to `sigma Y`.

For `p = classOf(a, μ)`, use `f.preserves ha` to obtain a common representation
`f (a r) = classOf(b, g r)`. Define a candidate output by

```text
bindRep (a, μ) f := classOf (b, μ.bind (measureCoercion ∘ g)).
```

Normalize the mixed seed measure using `bind_apply` at the whole real line;
every g r has mass one. The main calculation, for each E in `sigma Y`, is

```text
toMeasure (bindRep (a, μ) f) E
  = ∫ r, (g r) (b ⁻¹' E) dμ
  = ∫ r, K_f (a r) E dμ
  = ∫ x, K_f x E d(toMeasure (classOf(a, μ)))
  = ((toMeasure (classOf(a, μ))).bind K_f) E.
```

All integrals here are nonnegative extended integrals. There is no integrability
premise hidden behind finite real integration. Measurability of the middle
integrand follows from the preceding event-observer theorem. Thus the output
law is independent of b,g, of the chosen representative a,μ, and of pointwise
equal quotient-valued continuations. Injectivity of `toMeasure` turns these law
equalities into quotient equalities and permits `Quotient.lift` for `bind`.
For continuations presented by different samplers, pointwise *law* equality
first gives pointwise quotient equality; no pointwise equality of samples is
needed. An optional a.e. continuation-congruence theorem follows on a fixed
input law via `Measure.bind_congr_right`; it is not a prerequisite for the
pointwise public interface.

This proves a well-defined operation on elements. A separate proof must make
it an admitted operation, as the next section specifies.

## Unit, strong bind and laws

Use `unit x = classOf(const x, dirac 0)`. Its law is `dirac x`, independent
of the fixed probability seed law. For any random a, the curve `unit ∘ a` has
common map a and kernel `r ↦ dirac r`. This proves unit is a Hom.

For fixed f, a random curve `p r = classOf(a, g r)` has bind output represented
by one b and measures `g r >>= k`, where b,k represent f∘a. Fixed-kernel
measurability gives `bindHom f : Hom (P X) (P Y)`.

For strong bind, prove the larger target

```text
bindOperation : Hom (prod (P X) (exp X (P Y))) (P Y)
bindOperation (p,f) = bind p f
```

On a random curve `(p r, f_r)`, write p using a,g. The map
`(r,s) ↦ f_r (a s)` is a Hom from `ofMeasurable (ℝ × ℝ)` into P Y, by the
existing exponential's joint-randomness condition. Obtain one b and a jointly
measurable kernel `k(r,s)` from `standardFamilyRepresentation`. The output has
common map b and seed measures `h r = (g r).bind (fun s => k(r,s))`.
For any real measurable E,
`h r E = ∫ s, k(r,s) E d(g r)`. Construct the kernel g and use
`Measurable.lintegral_kernel_prod_right`, followed by eventwise measurable
extensionality, to prove h measurable. Prove each h normalized. This gives
joint randomness, rather than attempting an unjustified global measurable
representative choice for arbitrary f or arbitrary X. Currying the resulting
Hom gives the strong Kleisli-extension form in the paper.

Use injectivity of `toMeasure` and the constructed comparison with ordinary
measure bind to prove the following targets for all X,Y,Z, p, x and admitted
f,g. The nested continuation is admitted using `bindOperation` and the existing
product/exponential operations.

```text
unit_bind       : bind (unit x) f = f x
bind_unit       : bind p unitHom = p
bind_assoc      : bind (bind p f) g = bind p (fun x => bind (f x) g)
map_eq_bind     : map h p = bind p (unitHom.comp h)
bind_congr      : p = q → (∀ x, f x = g x) → bind p f = bind q g
```

Here lambda notation in `bind_assoc` stands for the constructed Hom, not an
arbitrary unbundled function. `dirac_bind`, `bind_dirac`, and `bind_bind` reduce
the three monad laws after all global kernel measurability obligations above
are available. Define `map h` by postcomposition of representatives and prove
its descent/randomness; alternatively derive it from bind and unit after those
are constructed.

A retained joint law uses `bind p (fun x => map (pairWith x) (f x))` in
`P (prod X Y)`. Admission of this continuation requires the *joint* map
`(x,y) ↦ (x,y)` with the retained parameter, supplied by strong bind/map, not
only fixed-f `bindHom`. Keep the resulting measure on `sigma (prod X Y)`.
The ordinary product sigma algebra embeds into it because projections are
measurable; the converse is not part of this specification. Eventwise bind
and parameter encodings above only use ordinary products on standard-Borel
seed spaces. They never transfer ordinary product measurability wholesale to
arbitrary QBS products.

## Recovery of represented sampling and finite kernels

For standard-Borel S and probability μ on S, construct `fromSampler μ a`
using encode/decode. Prove its `toMeasure` equals existing `law μ a` and prove
independence of the encoding. For probability ν on standard-Borel T and
`k : Hom (prod X (ofMeasurable T)) Y`, define
`representedContinuation ν k x = fromSampler ν (k at x)` and prove it is a
Hom into P Y. On any input random curve c, encode the standard-Borel seed
space `ℝ × T`; use the fixed map `(r,t) ↦ k(c r,t)` and the varying seed law
`dirac r × ν`. Establish measurability of the latter through eventwise
integration/pushforward. Pointwise representations alone would not prove this
admission claim.

The comparison target is

```text
bind (fromSampler μ a) (representedContinuation ν k)
  = fromSampler (μ.prod ν) (seeded a k).
```

Compare event probabilities via `seeded_apply` and the new `toMeasure_bind`,
then use injectivity. Input law substitution, retained substitution and
iteration now follow through the public general operation. This recovers the
**probability specialization** of the existing results; those results allow
arbitrary μ,μ' and merely s-finite ν and must remain available unchanged.
A probability monad does not subsume that larger measure scope.

For a finite discrete target B, every probability measure is representable by
encoding B (the empty case has no probabilities). For a finite source A and
ordinary Markov kernel K, `a ↦ classOfLaw (K a)` is admitted: encode B once,
use its decoding map and the pushed-forward family K a. Prove
`toMeasure (bind p Kqbs) = (toMeasure p).bind K` and, separately, retained
`compProd` agreement on finite products. All sigma algebras in that finite
comparison coincide by finite discreteness, not by a theorem about arbitrary
QBS products. In particular recover `SamplerClient.kernel_pair` and
`kernel_three`, alongside the existing higher-order realization examples.

## A new higher-order sequencing client and independent joint law

The following finite model tests functions *returning probability values*.
It is an independently specified client, not a rephrasing of the existing
fresh XOR noise example. Let B = {0,1}; let C be its fair law; independently
define ordinary kernels

```text
K_b(x) = dirac b   if x = b
         C         otherwise.
```

Sample b from C once and retain the probability-valued function `F_b : B → P B`
representing K_b. Draw y from `F_b(0)`, then z from the *same* `F_b(y)`.
The semantic output retains `(F_b,y,z)` in the QBS product. The independent
finite joint specification is the following measure on `(b,y,z)`:

| Triple | Mass |
|---|---:|
| (0,0,0) | 1/2 |
| (1,0,0) | 1/8 |
| (1,0,1) | 1/8 |
| (1,1,1) | 1/4 |
| Every other triple | 0 |

Derivation: when b=0 both transitions force 0. When b=1, y is fair; y=0
causes a second fair draw and y=1 forces z=1. Equivalently the joint mass is
`C{b} * K_b(0){y} * K_b(y){z}`. This independently specifies every atom and
normalization without invoking QBS or the implementation of bind.

Implementation targets are an ordinary `compProd` proof of this table and a
QBS theorem equating the full semantic output law to its pushforward under
`(b,y,z) ↦ (F_b,y,z)`. A further observation recovers b: F_0(0) assigns mass
one to {0}, whereas F_1(0) assigns mass 1/2. Evaluation followed by event-mass
observation is admitted; testing equality to one is measurable. Thus the
comparison retains the function and its correlations, rather than checking
only y,z marginals. The function space is the existing `exp B (P B)`; the
returning functions use the proposed probability object. General sequencing
at the client API consumes F directly and never asks its caller for fresh
noise or a representation witness.

Required controls:

- Replacing the second F by a newly sampled independent F changes the mass of
  `(b,y,z)=(0,0,1)` from zero to 1/8. The retained original function therefore
  distinguishes shared function sampling from resampling.
- Keep existing `copied_marginals`, `fresh_marginals`, `copied_not_fresh` and
  `reused_seed_wrong` as checked controls against inferring joint equality
  from marginals or reusing a selected seed.
- Encode the initial fair b alternatively as `not c` with c fair. The semantic
  law is unchanged, while at the same selected seed 0, F_0 and F_1 differ.
  Coupling c=not b can align semantic values, but does not identify the selected
  seed fields. No recovery of a sample from quotient equality is exported.
- All three monad laws receive finite positive specializations, and the empty
  carrier receives the construction check above. Reject a nonmeasurable family
  of Dirac laws: for a nonmeasurable A⊆ℝ, r↦dirac(1_A(r)) cannot be a random
  curve in P B, since evaluating {1} would make 1_A measurable. This paper
  separator catches the incorrect pointwise-existence definition of randomness.

The table and separator calculations are paper mathematics, not new checked
Lean results. A finite diagnostic enumeration can check the arithmetic, but
cannot validate the generic quotient, measurability or strong-bind proofs.

## Declaration obligations and implementation order

Names in this table specify new theorem targets and ownership. Each phase
belongs to the QBS successor work of [#200](https://github.com/VladimirMarko/conaled/issues/200),
coordinated with [#36](https://github.com/VladimirMarko/conaled/issues/36) and
[#235](https://github.com/VladimirMarko/conaled/issues/235). They are proposed
implementation children, not already approved architecture or completed work.

| Phase / proposed module | Required declarations and acceptance | Dependencies |
|---|---|---|
| A. `ProbabilityRepresentation` | `Rep`, its setoid, `Prob`, `toMeasure`, `toMeasure_injective`, `toMeasure_probability`; `fromSampler` and `toMeasure_fromSampler`; encoding independence and empty-carrier case. Equal-law/different-seed positive specialization. | Existing QBS/law API; standard-Borel encoding. |
| B. `ProbabilityObject` | Construct `P : Space → Space`; prove constant/reparameterization/countable-selection fields; `standardFamilyRepresentation`; event-observer Hom and `toMeasure_measurable`; `unitHom`, `mapHom`, their measure comparisons. Prove the Dirac-family measurability characterization to exclude the nonmeasurable separator without adding an axiom. | A; countable selection and kernel measurability. |
| C. `ProbabilityBind` | `bindRep_law`, independence of representation/witness/continuation, descended `bind`, `toMeasure_bind`, fixed-continuation `bindHom`, joint `bindOperation`, three monad laws and congruence. Check joint parameter integration explicitly. | B; Giry operations and parameterized kernel integrals. |
| D. `ProbabilityBind` specializations and examples | `representedContinuation`, represented-bind comparison, recovery of existing probability substitution cases, finite-kernel/retained `compProd` comparisons, independent table and full semantic law for the F_b client, resampling and seed controls. | C; existing native `SamplerClient`, without replacing it. |

Start A and B with finite and empty cases before C. B's common representation
on ℝ² is the gate for joint bind, not an assumed field supplied by clients.
D must exercise C's public operations, not prove a standalone table and call it
a monad client. Each phase requires statement review and the repository's
applicable candidate build and exhaustive proof audit when implemented; proof
holes or new axioms do not discharge these obligations.

If B cannot yet be completed, the useful fallback is A plus an explicit
`RepresentedFamily` API with the common map and measurable kernel supplied.
That would extend the current fixed-fresh-noise route to varying seed kernels
and prove their descent by `bindRep_law`. It must be named represented bind,
not general bind, and leave B/C open under the named QBS successor owner.
No failed Lean attempt or mathematical obstruction was established here:
this fallback is a delivery boundary, not a claim that the published
construction is impossible or needs stronger foundations.

Compared with the incumbent route, A/B add quotient descent, real encodings,
countable packing, and probability-valued curves; C adds uniform parameter
integration and admitted bind. These setup costs remove representation
obligations from clients accepting arbitrary `Hom X (P Y)`, including functions
returning computations and repeated sequencing. An explicit one-off sampler
still has less setup using `seeded_apply` and native kernels. No author-time,
runtime or productivity advantage was measured. Preserve these useful native
interfaces and the broader s-finite substitution theorem.

Conditioning, recursive probability, internal valuations, general universe
lifting, executable sampling adequacy and replacement of native kernels are
outside this specification. Commutativity and the full standard-Borel Giry
isomorphism are additional published targets; the finite comparison above does
not establish either general theorem. The recommended first implementation
ends after A–D with strong bind and the stated recoveries. Independent review
of this specification authorizes no universal probability architecture.
