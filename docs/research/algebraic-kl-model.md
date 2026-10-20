# A small algebraic site for the first KL construction (#73)

## Current higher/differential decision (#96)

The [finite-quotient tangent investigation](myers-tangent-integration.md)
selects a first-order consequence of Myers Proposition 4.3.5 after #95. It
recommends testing finite torsor invariance under the existing dual extension,
with quotient tangent transport and KL comparison in the same model. General
transverse-pullback preservation is deferred as the next task. The dated
assessments below remain historical evidence; the new note audits current
capabilities and states the missing compatibility theorems.

After accepted #99, the [#97 decision gate](transverse-pullback-decision.md)
keeps general transverse-pullback preservation deferred. The selected quotient
tangent comparison is constructed; its next identified gap is source-language
interpretation and soundness. The gate records the pinned ordinary APIs and
the additional all-stage comparison a future preservation theorem would need.


Inspected 2026-10-18 at Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. This continues the
[internal-language assessment](internal-languages-lean.md#pinned-mathlib-model-constructions)
and the [sheaf implementation record](sheaf-local-images.md). It selects a
bounded algebraic milestone for [#36](https://github.com/VladimirMarko/conaled/issues/36).
The #73 slice did not establish KL. The
[#74 construction](#categorical-kl-and-a-polynomial-consumer-74) below proves
first-order categorical KL and one polynomial analytic comparison.
A well-adapted smooth model remains open.

## Recommendation and source evidence (#73)

The #73 recommendation was to construct the first categorical KL isomorphism
on the small algebraic site implemented below, starting from its checked
universal dual-number stage. This avoids introducing smooth-ring presentation
and descent machinery before the
first internal infinitesimal calculation. A later smooth model needs a richer
site and scalar; there is no claimed equivalence with this algebraic model.
The generic sheaf, exponential and dependent-product infrastructure remains
usable for that later construction.

Anders Kock's *Synthetic Differential Geometry*, second edition, author PDF
marked March 2006, III.1, Lemma 1.1 and Theorem 1.2, calculates functor-category
exponentials using algebra coproducts and Yoneda. III.5, Proposition 5.1,
identifies free smooth algebras. III.8 constructs well-adapted models.
III.3, Theorem 3.2, compares synthetic and ordinary derivatives using a smooth
Hadamard remainder; Theorem 3.3 treats several variables.
These are mathematical references, not local Lean theorems.
[Author's second-edition text](https://users-math.au.dk/kock/sdg99.pdf).

Dubuc's original 1979 paper, *Sur les modèles de la géométrie différentielle
synthétique*, Proposition 4.4, identifies the square-zero object. Theorems 4.5
and 4.6 prove properties of Weil prolongations, open covers and transverse
pullbacks. Theorem 4.10 constructs a well-adapted sheaf model; its final
paragraph explains the reduction to a small site using Euclidean opens and
Weil algebras. This includes obligations absent from an ordinary ring category.
[Original paper, volume 20(3), pp. 231–279](https://www.numdam.org/item/CTGDC_1979__20_3_231_0/).

The following restricted-site calculation is our specialization of the
algebraic method. It does not require all finitely presented rings or all their
coproducts. It needs the particular extensions `A ↦ A[ε]`.

## Concrete size, variance and topology

[`AlgebraicStage.lean`](../../SquareKit/AlgebraicStage.lean) defines a finite
expression type `Stage` with constructors `integers`, `polynomial A`, `dual A`.
`algebra` interprets these as bundled commutative rings `ℤ`, `Polynomial A`,
and `DualNumber A`. Every carrier is in `Type 0`. Arrows are **all** unital ring
homomorphisms between the interpreted carriers. Different codes can describe
isomorphic rings; no skeleton or uniqueness claim is made.

Both objects and hom types are in `Type 0`. The larger universe of the bundle
`CommRingCat` is only the codomain of the interpretation, not the site object
type. Using all of `CommRingCat.{0}` directly would instead put site objects
in `Type 1`, whereas the current `SheafFunction` requires section universe
`max(object universe, hom universe)`. No lift comparison or smallness assumption
is hidden in the selected construction.

Write `A` for the code category and `C := Aᵒᵖ` for the site. Its topology is
bottom: only maximal sieves cover. A presheaf is covariant in algebra maps,
written in Lean as `Cᵒᵖ ⥤ Type`. At the double opposite of a code `B`, the
scalar `R` has sections `Carrier B`; a ring map `B → T` acts by that ring map.
`D(B) = {d : B | d*d = 0}` has the induced restriction. Both sheaf obligations
are discharged by `Presheaf.isSheaf_bot`. This is explicitly a presheaf model,
with no open-cover smooth descent built in.

The scalar addition, multiplication and negation are natural sheaf arrows.
`integer n` supplies natural constants, including zero and one; the stage
`CommRing` instances supply the ring laws. `scalar_ringMap` checks preservation
of the operations by every stage arrow. This is an internal ring with natural
operations, not an `IsKockLawvere_one` instance on a Lean type. `inclusion`
forgets the square-zero proof component. In particular the scalar at the dual
integer stage has a nonzero square-zero element, checked by `epsilon_nonzero`.

## Exact KL target and the remaining calculation

Set `E := SheafFunction.exponential D R`, the already constructed categorical
exponential. The retained `affineBody : D × (R × R) → R` sends
`(d,(a,b))` to `a+b*d`. `affine : R × R → E` is its actual `curry`.
`affine_evaluation` proves the expected ordinary evaluation equation at every
stage. `affine_parameters` proves substitution along every map `X → R × R`
from every parameter sheaf `X`. Neither theorem asserts invertibility.

The intended first KL statement is that this particular `affine` is an
isomorphism. Equivalently, for every parameter sheaf `X` and every natural
`h : D × X → R`, there are unique natural `a,b : X → R` such that, at every
stage `B`, every `x : X(B)` and every `d : D(B)`,

```
h_B(d,x) = a_B(x) + b_B(x)*d.
```

All these maps respect every ring-map restriction. It is not a statement about
the set of all external functions `D(B) → B` at a fixed stage. At `B=ℤ`, for
example, the only square-zero element is zero, so ordinary stagewise functions
cannot recover the slope. The exponential retains behavior at further stages.

Here is the proposed proof, with the missing categorical adapters explicit.
Let `yB(T) = Hom(B,T)`, the site representable at `op B`. The checked equivalence
`dualLift B T` identifies

```
Hom(B,T) × {d:T | d*d=0} ≃ Hom(DualNumber B,T).
```

Its map is `(φ,d) ↦ (z ↦ φ(z.fst)+φ(z.snd)*d)`. Both inverse laws are proved
using Mathlib's `DualNumber.lift` and `ringHom_ext`; `dualLift_natural` proves
compatibility with every target ring map. The source product order must be
swapped to obtain a natural isomorphism `D × yB ≅ y(dual B)`.
After packaging that isomorphism, the existing exponential adjunction and
Yoneda should give

```
E(B) ≃ Hom(yB,E) ≃ Hom(D×yB,R)
     ≃ Hom(y(dual B),R) ≃ DualNumber B ≃ B×B.
```

Coefficient extraction evaluates the natural family at the universal pair
`(ε, B → DualNumber B)`, then takes its two coordinates. Reconstruction at
arbitrary `T`, `φ:B→T`, `d*d=0` is `φ(a)+φ(b)*d`. Verify that reconstruction
is precisely the existing `affine`, and prove coefficient extraction natural
in `B`. That yields an inverse sheaf arrow, not merely bijectivity at global
points. Arbitrary parameter uniqueness then follows by transposition.
At the #73 baseline these final isomorphisms and inverse comparisons remained unproved; the #74 construction below supplies them.

## Pinned API inventory and local boundaries

The links below all use the inspected Mathlib revision. Searches covered
category/site, ring/algebra, polynomial/dual-number, and smooth/manifold files;
relevant definitions were then read, rather than treating one unsuccessful
name search as evidence of absence.

| Needed operation | Reusable API and remaining adapter |
|---|---|
| Small stages and scalar | Local `Stage`, `algebra`, `scalarData`, `scalar`, `infinitesimal`; all elaborate at universe zero. `CommRingCat.of` is used only to bundle the recursive interpretation. |
| Trivial topology | [`Presheaf.isSheaf_bot`, `sheafBotEquivalence`][sheaf] prove the sheaf obligations and identify this model with presheaves. |
| Representables | [`yonedaEquiv`][yoneda] identifies transformations out of a representable with a section. Package `dualLift` into the product-representable isomorphism, including the double-opposite adapters. |
| Dual extension | [`DualNumber.lift`, `lift_apply_apply`, `lift_apply_eps`, `lift_comp_inlHom`, `ringHom_ext`][dual] provide existence, coordinates and uniqueness. Local `dualLift` removes the redundant commutativity side condition for these commutative stages using integer-algebra maps. |
| Polynomial line | [`Polynomial.eval₂RingHom`][poly] constructs evaluation. To identify `R` as represented by `polynomial integers`, prove the natural evaluation-at-X equivalence and uniqueness from coefficients and X. The first KL calculation above does not require this additional representability. |
| Existing exponential | Local `SheafFunction.exponential`, `curry`, `uncurry`, `beta`, `eta`, `curry_parameter`, `evaluation_curry_apply` construct and compute the actual internal functions; the retained affine map uses them. |
| Dependent functions | Local `SheafDependentProduct.pi`, `evaluation`, `baseChange` provide arbitrary-map right adjoints and canonical BC. `SplitSheafPi.pi`, `substitution`, `lam_substitution`, `app_substitution` give equality-level formation and term transport. None constructs KL coefficients. |
| Source boundary | `Internal.DependentFunctions` has independent rule-restricted syntax and constructed sheaf soundness, but its admitted function domains are primitive bases, results primitive indexed families. There is no source infinitesimal axiom or scalar-calculus interpretation yet. Semantic KL should be constructed before adding one. |
| External polynomial derivative | [`Polynomial.hasDerivAt`, `hasFDerivAt`][deriv] identify derivatives with evaluated formal derivatives over a normed field. Map integer coefficients to ℝ for a first ordinary consumer. This alone does not interpret all real smooth maps. |
| Smooth functions and sheaves | [`ContMDiffMap.evalRingHom`, `restrictRingHom`][smooth-algebra] and [`smoothSheaf`, `smoothSheafCommRing`][smooth-sheaf] supply smooth function rings and gluing on opens of a fixed manifold. They do not by themselves construct a formal-manifold site with Weil directions. |

Bounded source searches for `CInfinityRing`, `Cahiers`, `WeilAlgebra` and
`IsKockLawvere`, followed by the smooth-function and sheaf inspections above,
did not locate an assembled well-adapted KL model in the pinned library.
The inspected Taylor and manifold derivative modules provide analytic
ingredients; this is not a claim that no additional useful lemma exists.
No dependency, toolchain, trust or heartbeat setting changed.

## Checked evidence and statement review

The two experimental modules are aggregate imported and covered by the normal
source check and axiom audit. `affine_at_epsilon` consumes the actual exponential
evaluation theorem and recovers both arbitrary integer coefficients at the
nonzero dual stage. `extension_at_epsilon` independently exercises the checked
universal ring map on both coordinates. `square_expansion` verifies the
expected slope `2*x` in every stage ring under the explicit `d*d=0` assumption.
It is an algebraic prerequisite, not a derivative obtained from a KL inverse.

Statement review checked the universes, covariant algebra-map orientation,
product order, all target restrictions, all parameter sheaves, and the actual
exponential codomain. The universal property assumes only a ring map and a
square-zero element, not KL. Its inverse laws cover every ring hom out of the
dual stage. Initial scratch diagnostics showed that defining unbundled carriers
before recursive ring structures cannot elaborate the polynomial constructor;
the retained bundled recursion resolves that dependency. The diagnostics and
review evidence are retained in `/tmp/conaled-73`, outside the source diff.

## One next construction, and the smooth risk

The #73 recommendation was **the categorical KL inverse on these
stages**, with the representable comparison, coefficient naturality, both
inverse equations for `affine`, and arbitrary-parameter uniqueness described
above. Its checked consumer should transpose `(d,x) ↦ (x+d)*(x+d)`, use that
constructed inverse to recover derivative `x ↦ 2*x`, and compare evaluation of
an integer polynomial instance in ℝ with `Polynomial.hasDerivAt`. Include the
nonzero dual stage and a nonidentity restriction. This would advance from the
present algebraic prerequisite to actual internal KL and an ordinary polynomial
consumer. It would still leave interpretation of an imported synthetic proof
and an arbitrary smooth-map comparison open.

For a well-adapted smooth candidate, use formal manifolds `U × ℓW` with `U` an
Euclidean open and `W` a Weil algebra, smooth-algebra morphisms, and covers from
open covers of `U`. The scalar is the represented smooth line. A checked small
encoding, its topology, scalar sheafness, Weil extension calculations and KL
are still construction obligations. Ordinary ring homs between smooth-function
rings cannot simply replace the required smooth-algebra morphisms.

Our polynomial-site scalar can at most support polynomial natural maps once
its line-representability theorem is supplied: Yoneda then identifies
`R→R` with integer polynomials. Thus the algebraic site must be supplemented or
replaced for arbitrary smooth geometry. No unproved functor preserving
exponentials is being used to transfer its KL theorem to the smooth candidate.

The analytic bridge will need a faithful smooth-map interpretation, preservation
of relevant products and ring operations, a Mathlib Taylor/Hadamard remainder
comparison, transport of that equation into the model, and KL uniqueness to
identify the interpreted derivative. External equality requires a proved
faithfulness or points comparison. Polynomial coefficient extraction supplies
none of those general smooth obligations.

Finally the [Myers obligation table](myers-orbifold-assessment.md#theorem-correspondence)
requires higher identities and universes, crisp/modal structure, Weil-general
KL, tiny infinitesimals and the Covering Property, crystalline preservation of
crisp pullbacks, and interval compactness. A set-valued first-order KL model
does not discharge those axioms or the orbifold descent and presentation
comparisons. The remaining stages stay provisional.

[sheaf]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Sheaf.lean
[yoneda]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Yoneda.lean
[dual]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/DualNumber.lean
[poly]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Polynomial/Eval/Defs.lean
[deriv]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean
[smooth-algebra]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/Algebra/SmoothFunctions.lean
[smooth-sheaf]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/Sheaf/Smooth.lean

## Categorical KL and a polynomial consumer (#74)

[`AlgebraicKL.lean`](../../SquareKit/AlgebraicKL.lean) now constructs `kl`, whose
forward arrow is exactly #73's `AlgebraicStage.affine`. Its inverse `extract`
is an actual sheaf morphism. This proves first-order categorical KL in the
selected small algebraic presheaf model, without an external-function KL class.

`dualRepresentable A` packages `dualLift` as `D × yA ≅ y(dual A)`, with the
infinitesimal first and actual site representables on both sides. Its arrow
naturality uses `dualLift_natural`; `dualLift_source` and
`dualRepresentable_parameter` prove the parameter-stage comparison along every
ring map, using the constructed `dualMap`. No general coproduct closure of the
code category is required.

For `h : D × X → R`, `universalValue h A x` evaluates at epsilon after
restricting `x` along the constant inclusion `A → DualNumber A`.
`universalValue_yoneda` identifies this exact operation with Yoneda evaluation
through `dualRepresentable`. Its two coordinates give `coefficients h`.
`universalValue_natural` and `dualMap_coordinates` prove that these coordinates
form a natural sheaf arrow. Naturality along `dualLift(id,d)` gives
`universal_reconstruction` at every stage and every parameter section.

`affine_extract` and `extract_affine` prove both inverse equations with the
existing affine map using the ordinary exponential's curry, beta and eta.
`extract_curry` connects this inverse with coefficients of arbitrary operations.
`coefficients_unique` uses the resulting isomorphism and transposition;
`allParameters` gives unique natural maps `a,b : X → R` for every parameter
sheaf `X`, with the affine equation at every stage and every square-zero input.
`coefficients_parameter` proves compatibility with every parameter substitution.

[`AlgebraicDerivative.lean`](../../SquareKit/AlgebraicDerivative.lean) defines
`derivative f` for any natural `f : R → R` by currying `(d,x) ↦ f(x+d)`,
applying `kl.inv`, and projecting the slope. `intercept` recovers `f` as the
constant coefficient; `taylor` proves the first-order equation. The parameter
version and `derivative_parameters` allow any sheaf `X → R`.
`derivative_unique` identifies any natural slope satisfying that equation at
all stages. The definition does not refer to a formal polynomial derivative.

[`Examples/AlgebraicKL.lean`](../../Examples/AlgebraicKL.lean) then proves
`derivative_square` through this uniqueness theorem, using #73's
`square_expansion` for the expected slope. `square_at_epsilon` consumes Taylor
at the nonzero dual-integer infinitesimal. `flip` fixes integer constants and
negates epsilon; `flip_not_identity` proves it is nonidentity, and
`derivative_flip` checks derivative preservation along it.

The regression separates external stage functions from internal functions.
`integers_infinitesimal_zero` proves that integer-stage D has only zero;
`same_integer_evaluation` shows that slopes zero and one have the same values
there. Nevertheless `internal_slopes_distinct` distinguishes their actual
exponential sections using `extract`, and `slope_observations_distinct`
distinguishes their evaluations after restriction to the dual stage. These
are comparisons involving the actual exponential and its evaluation, not a
separate calculation on standalone functions.

For the ordinary consumer, `square_polynomial` identifies the scalar map with
evaluation of the integer polynomial `X^2` at every stage.
`coefficient_polynomial` identifies the KL-derived slope with its formal
derivative. `modelSlope` observes the synthetic derivative at the polynomial
stage's universal variable; `modelSlope_eq` recovers the formal derivative
polynomial from that observation. Finally `analytic_square` maps the original
polynomial and this model-derived coefficient to ℝ and invokes Mathlib's
`Polynomial.hasDerivAt`. Thus its analytic coefficient comes from the constructed
KL inverse. ℝ is an external evaluation target, not an object of this site.
This proves one polynomial comparison, not an embedding of arbitrary smooth maps.

Statement review checked the opposite adapters, both naturality directions,
all-parameter quantifiers, actual inverse equations, derivative dependency on
KL, and the model coefficient in the analytic statement. The experimental
modules are aggregate imported and covered by fresh source checking and the
exhaustive axiom audit. Ordinary clients and earlier source fragments remain
available; no foundational, toolchain or heartbeat changes were needed.

One next bounded slice is to interpret the surveyed synthetic first-order
product-rule proof using this scalar and KL uniqueness, and compare a polynomial
instance with ordinary differentiation. This would add interpreted synthetic
reasoning beyond the present semantic squaring calculation. Imported-source
proof interpretation is not established here. The formal-manifold/smooth site,
arbitrary smooth derivative comparison, higher/cohesive structure and the
Myers/orbifold obligations above remain unconstructed. #74 does not complete #36.

## Interpreted synthetic product proof (#75)

The source-to-model link now includes the first-order synthetic product argument
from Brasca and Clemente's SDG repository, revision
`e4cd622492aba9be421ec0abcf152f58a0ee98df`.
In [`IsKockLawvere_one/Deriv.lean`][sdg-product], the `leibniz'` field of `deriv`
uses two Taylor expansions, a ring expansion retaining the quadratic cross
term, its vanishing for square-zero inputs, and `derivative_unique`.
`deriv_mul` then exposes the resulting product rule. The argument is
re-expressed as a source derivation here; no upstream Lean code is copied or
imported. The inspected original credits Riccardo Brasca and Gabriella Clemente
and carries Apache-2.0 licensing.

The same revision's [`Basic/Alpha.lean`][sdg-alpha] proves equivalence between
unique affine expansion and bijectivity of its native affine function. Our
interpretation uses the categorical affine isomorphism already constructed in
#74. We do not import the upstream native-function KL typeclass, custom kernel
or unique-choice axiom. In particular, this is not an instance asserting that
arbitrary external functions on ordinary real infinitesimals satisfy KL.

[`Internal/SyntheticScalar.lean`](../../SquareKit/Internal/SyntheticScalar.lean)
provides a bounded model-independent language. `MapExpr n` contains formal
function parameters, addition, multiplication and derivative symbols.
`Expr n` is an integer ring-expression syntax whose atoms are base values,
shifted values and one infinitesimal. It imports no sheaf model. Its admitted
`Derives` constructors are exactly:

- Reflexivity, symmetry, transitivity and addition/multiplication/negation
  congruence.
- A ring certificate: equality of the two encoded expressions in the free
  `MvPolynomial (Atom n) ℤ` ring. This is a checked syntactic normalization
  certificate, not arbitrary equality supplied from a target model.
- The nilsquare equation and a first-order Taylor rule for each formal function.
- Structural equations for base addition/multiplication and shifted
  multiplication, expressing the declared pointwise operations.

`product_cross` produces the expansion with an explicit
`(df*dg)*(epsilon*epsilon)` term. `remove_cross` uses the nilsquare constructor
to discard precisely that term. `product_expansion` combines these derivations
with Taylor and structural rules. The separate judgment `Slope f g` has one
unique-slope inference from a source expansion; `product_rule` applies it to
`product_expansion`. The product rule is not a primitive constructor. This
fragment has no binders or general substitution calculus: the derivation is
parametric in arbitrary `MapExpr n` inputs, so it can be instantiated with
compound source expressions without adding a semantic-equality rule.

[`Internal/SyntheticScalarSheaf.lean`](../../SquareKit/Internal/SyntheticScalarSheaf.lean)
constructs an interpretation from any assignment of natural scalar maps to
function parameters. Formal derivatives become `AlgebraicDerivative.derivative`.
`sound` covers every `Derives` constructor: polynomial certificates are evaluated
by the ring homomorphism justified by `Expr.eval_polynomial`; nilsquare comes
from membership in D; Taylor is #74's theorem. `slope_sound` interprets the
unique-slope inference using `derivative_unique`, hence the constructed KL
inverse. Callers supply no product-rule validity or derivative correctness
field. The proof quantifies every stage, scalar parameter and infinitesimal;
it never cancels an individual d. `sound_parameters` also accepts any sheaf
parameter assignment `X → R`.

[`SyntheticProductRule.lean`](../../SquareKit/SyntheticProductRule.lean) is an
optional adapter. Its `product` theorem for arbitrary natural `f,g : R → R`
invokes `product_rule` through `slope_sound`. Its right-hand side uses the
existing natural ring operations and the KL derivatives of f and g.
`component` exposes the ordinary component equation and `parameters` exposes
composition with any sheaf parameter map. The generic model and derivative
modules do not import the source syntax or this adapter. No global proof
notation is installed.

[`Examples/SyntheticProduct.lean`](../../Examples/SyntheticProduct.lean)
instantiates that same source consequence at two ordinary squaring maps.
`derivative_fourth_apply` obtains `4*x^3` from the source-derived product theorem
and the earlier ordinary squaring derivative. `fourth_at_epsilon` uses this
coefficient in Taylor at a nonzero dual epsilon. `fourth_flip` checks its
preservation along the existing, proved nonidentity epsilon-negating map.
`mixed_styles` uses direct maps and the source-derived derivative together.

`fourth_polynomial` identifies the ordinary map with evaluation of integer
`X^4`. `modelCoefficient` observes the derivative at the polynomial stage's
universal variable; `modelCoefficient_eq` recovers the polynomial derivative
from the source-derived result. `analytic_fourth` then applies Mathlib's
`Polynomial.hasDerivAt` with the externally evaluated model coefficient.
The dependency therefore runs from source derivation, through model soundness
and the actual KL inverse, to an ordinary real analytic statement. Real numbers
remain external evaluation targets; no general smooth embedding is asserted.

The boundary example `boundary_source` derives the truncated expansion using
nilsquare. `boundary_no_ring_certificate` proves that its two sides are unequal
as free polynomials: evaluation at epsilon=1 gives a counterexample. Thus plain
ring normalization cannot justify discarding that cross term. The existing
integer-stage versus internal-function regression remains intact.

Statement review inspected the complete constructor list, all-stage uniqueness,
parameter scope and the analytic coefficient's source dependency. A wrapper
initially made elaboration unfold the model while solving finite assignment
indices; simplifying only the source interpretation first resolved that
regression. Explicit stage arguments likewise avoid expensive inference in the
restriction client. No heartbeat or trust settings changed. The experimental
modules are aggregate imported and covered by fresh checking and the exhaustive
axiom audit.

One next bounded construction is functorial first-order prolongation of smooth
maps between finite real coordinate spaces: send `(x,v)` to `(f(x), Df(x)v)`,
prove identity and composition using Mathlib's derivative rules, and compare
its polynomial instance with the coefficients already recovered here. This is
a concrete prerequisite for giving smooth maps an action on real dual stages;
it would not itself construct a formal-manifold site or prove smooth KL.
The present result interprets this product argument only. Arbitrary smooth
representation, Weil-general KL, higher/cohesive structure and orbifold
comparisons remain open, and #36 remains incomplete.

[sdg-product]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/SDG/IsKockLawvere_one/Deriv.lean
[sdg-alpha]: https://github.com/riccardobrasca/SDG/blob/e4cd622492aba9be421ec0abcf152f58a0ee98df/SDG/Basic/Alpha.lean

## Smooth operations on the real dual stage (#76)

`Applications/AD/SmoothDual.lean` constructs an experimental finite-arity
smooth operation structure on Mathlib's `DualNumber ℝ`. An operation is an
ordinary function `(Fin n → ℝ) → ℝ` with `ContDiff ℝ ∞`; equality is
extensional equality of that function. Its action sends a tuple `x + ε v` to
`f(x) + ε Df(x)(v)`. `act_projection` and `act_substitute` prove the projection
and arbitrary simultaneous-substitution laws for every pair of finite arities,
including zero. `act_constant`, `act_addition` and `act_multiplication` recover
the existing ring operations, including their square-zero cross term.

The construction reuses `Applications/AD/Core.lean`: the small `Smooth`
module supplies `DMap.ofSmooth` and finite tuple assembly; `act_substitute`
uses `tangent_comp`. `act_coordinates` identifies the dual action with that
same tangent implementation. `act_of_dmap` uses `DMap.ext`, whose derivative
uniqueness proof prevents choosing another tangent for the same primal map.
These ordinary modules import no source syntax. The inspected pinned APIs are
Mathlib's `ContDiff.differentiable`, `hasFDerivAt_pi`,
`ContinuousLinearMap.proj`, `Real.hasDerivAt_exp`, and the existing
`DualNumber`/`TrivSqZeroExt` ring and coordinate operations.

`Examples/SmoothDual.lean` checks an arbitrary nullary operation, nullary
substitution, epsilon squared, and the nonpolynomial exponential, including
`exp(0 + 2ε) = 1 + 2ε`. Its optional algebraic comparison constructs an actual
ring map from integer dual numbers to real dual numbers and polynomial
extension by evaluation. `fourth_extension` compares the old fourth-power
operation with the new one. `fourth_model_coefficient` consumes
`SyntheticProduct.analytic_fourth`, which depends on `modelCoefficient_eq`
and hence on the interpreted source derivation. `coefficient_extension`
then identifies extension of that model coefficient with the real dual tangent.
The comparison does not assert a functor preserving sheaf exponentials or KL.

The source boundary remains the one described above. Kock's I.16 treats real
dual numbers as one Weil algebra; III.5 and III.8 discuss the stronger smooth
algebra and model constructions. This slice checks the finite-operation laws
for that one algebra. It constructs neither a formal-manifold site nor smooth
categorical KL. The broader smooth embedding, descent and analytic comparison
obligations from the earlier sections remain open. #36 remains incomplete.
[Author's text, I.16 and III.5–8](https://users-math.au.dk/kock/sdg99.pdf).

One next bounded construction is the same smooth action on finite-dimensional
square-zero extensions `ℝ ⊕ V`, with naturality under linear maps of tangent
spaces and recovery of this one-dimensional case. That would provide a family
of compatible first-order stages before addressing higher nilpotence and a
smooth site.

## Compatible square-zero stages (#77)

`Applications/AD/SmoothSquareZero.lean` extends the smooth-operation interface
to `TrivSqZeroExt ℝ V`. For inputs `(xᵢ,vᵢ)`, the nilpotent coordinate is
`∑ i, Df(x)(eᵢ) • vᵢ`. The standard vectors `eᵢ` belong to the finite input
space of the ordinary function; no basis of `V` is selected. Only this finite
real input space is differentiated. `V` needs an additive commutative group
and a real module structure, with no norm or topology. Consequently the
construction covers every finite-dimensional real vector space and also
works without a finite-dimensionality hypothesis. The ring/map results use
Mathlib's right real scalar action and `IsCentralScalar ℝ V`, requiring it
to agree with the ordinary real action.

`coefficient_sum` identifies the finite coefficient formula with the original
analytic derivative when `V=ℝ`. `act_real` therefore recovers every operation
from #76 exactly. Linear maps commute with the finite sum, giving `map_act`.
Scalar linear observations separate vectors, so `observations_ext` transports
the already proved dual projection, substitution, constant, addition and
multiplication laws to these stages. In particular, arbitrary substitution
uses the existing analytic chain rule through #76, with no new assumed rule
for vector-valued nilpotents.

The morphisms are precisely real algebra homomorphisms between these stages.
`map` reuses Mathlib's `TrivSqZeroExt.map`, including its identity/composition
laws. Conversely, any such homomorphism sends an element `(0,v)` to another
square-zero element; its real coordinate must vanish because ℝ has no
nonzero square-zero element. Restriction to that ideal followed by the second
projection defines `linearPart`. `homEquiv` proves the two constructions
inverse, and `hom_act` proves that every real algebra homomorphism preserves
every smooth operation. This characterizes all maps of the family, not only
chosen coordinate transformations.

`Examples/SmoothSquareZero.lean` checks two independent nonzero directions in
`V=Fin 2 → ℝ`, their vanishing pairwise products, a nonidentity doubling map
preserving the exponential, zero arities, and recovery of the previous dual
exponential client. `mixed_term_lost` shows that multiplying the two independent
infinitesimals gives zero, while `ordinary_mixed_derivative` proves the ordinary
mixed derivative of multiplication is one. These stages retain only first-order
information. The ordinary API remains independent of source syntax.

This is a compatible family of first-order smooth algebras in the sense of the
finite-operation laws checked above. It does not exhaust the Weil algebras
in Kock I.16, and supplies neither the higher nilpotence nor the smooth site,
descent and well-adaptedness discussed in III.5–8 and Dubuc's construction.
Smooth categorical KL, the analytic embedding, cohesion and the orbifold
comparisons remain open; #36 is incomplete.

One next bounded construction is a second-order real truncated-polynomial
stage with smooth operations, substitution and projection to the present dual
stage. A checked nonzero quadratic term and a Hessian comparison would test
the new information before constructing a smooth site.

## A second-order smooth real stage (#78)

`Applications/AD/SecondStage.lean` realizes the truncated polynomial algebra
`ℝ[ε]/(ε³)` as a concrete subalgebra of `DualNumber (DualNumber ℝ)`. Its
members satisfy `z.fst.snd = z.snd.fst`. The element with coordinates `(a,b,c)`
is `((a,b),(b,2c))`; thus epsilon is the sum of the two ambient dual directions.
The inherited ring operations, `coeff_mul`, `coeff_ofCoeff`, `ofCoeff_coeff`
and `normal_form` prove the unique representation `a+bε+cε²`.
`epsilon_cube` proves epsilon cubed zero; `epsilon_sq_ne_zero` proves its square
nonzero. `evaluate` and `universal` give the defining universal property:
for every commutative real algebra and every element with cube zero there is
exactly one real algebra homomorphism sending epsilon to that element. This
justifies the truncated-polynomial presentation without postulating ring laws.

The ordinary analytic work lives in `Applications/AD/SecondOrder.lean`.
Before choosing it, the existing `Jets.lean` polynomial tower and `HigherOrder.lean`
curve relation were inspected, along with Mathlib's polynomial Taylor/Hasse
coefficients, iterated derivatives, smoothness of `fderiv`, and differentiation
of continuous-linear-map application. The polynomial tower covers all orders
for polynomials, but does not supply arbitrary smooth substitution. The new
module applies the existing certified `DMap` tangent twice. `lift_comp` uses
`tangent_comp` and derivative uniqueness; `twice_comp` applies that same law
again. `twice_formula` differentiates evaluation using `HasFDerivAt.clm_apply`
and smoothness of the derivative. Restricting to `((x,v),(v,2w))` gives `jet_comp`
with quadratic coordinate `Df(x)(w) + ½ D²f(x)(v,v)`. Here `D²` is literally
`fderiv ℝ (fderiv ℝ f)`, applied to both directions. Smoothness discharges the
analytic hypotheses; no second-order chain rule is assumed.

`Applications/AD/SmoothSecondStage.lean` uses the existing finite-arity
`Operation` interface. `quadratic_coefficient` exposes the analytic formula;
`act_substitute` combines `jet_comp` and finite tuple assembly. Projection,
constant, addition and multiplication laws recover the actual stage algebra,
for all arities including zero. `project_act` proves that discarding the
quadratic coordinate preserves every smooth operation and recovers #76.
`reparam a b` is the actual algebra endomorphism sending epsilon to `aε+bε²`.
Its coordinate formula is `(x,v,w) ↦ (x,av,bv+a²w)` and `reparam_act` proves
smooth-operation preservation for all real `a,b`, including noninvertible
choices. All three ordinary modules remain independent of source syntax.

The checked clients in `Examples/SecondStage.lean` recover a stored coefficient
of one for epsilon squared, while the ordinary second derivative of the square
is two. That analytic calculation consumes the existing polynomial jet theorem.
For the exponential, `exp_jet` differentiates the actual analytic derivative;
`exp_analytic_coefficient` compares the stored coefficient with one half of
`deriv (deriv Real.exp)`. At epsilon the coefficients are `(1,1,½)`.
`projection_loses_quadratic` proves that the nonzero epsilon square becomes
zero in the first-order projection. A nonidentity reparameterization and a
nullary client exercise the general laws.

This adds one higher-nilpotence algebra to the earlier first-order family.
It does not construct the general Weil algebras or their smooth-operation
extension, the formal-manifold site and descent, or the well-adapted model
from the primary sources discussed above. Smooth categorical KL, the general
analytic embedding, cohesion and the orbifold comparison remain open. #36
is incomplete.

One next bounded construction is a two-generator second-order stage retaining
mixed products, with smooth operations, compatible maps to the present stage
and an explicit mixed Hessian comparison. That would test multivariable
quadratic information before moving to arbitrary Weil presentations.

## Free finite-coordinate smooth algebras (#79)

Kock III.5, Proposition 5.1 identifies the smooth functions on `ℝⁿ`, with
coordinate projections as generators, as the free algebra for the theory of
smooth operations. The proof uses the theory's actual smooth maps. Proposition
5.4 discusses quotients by ordinary ideals using the smooth factorization from
Proposition 5.2. These latter results are prerequisites still to be constructed
locally. [Author's text, III.5](https://users-math.au.dk/kock/sdg99.pdf).

`SquareKit/SmoothOperations.lean` now owns the existing smooth-function subtype
and its projection, constant, substitution, addition and multiplication operations.
The old `Applications.AD.SmoothDual` names remain aliases, preserving clients.
`SquareKit/SmoothAlgebra.lean` defines `Structure` over an existing real
commutative algebra. It requires the two smooth-operation laws and proved
compatibility with that algebra's constants, addition and multiplication. This
choice retains Mathlib's actual stage rings and pointwise function algebra
rather than deriving duplicate ring instances from operation syntax.
Operations are identified by extensional equality of their underlying functions.

`Hom` initially asks only for a function preserving all smooth operations.
Its preservation of scalar constants, sums and products is derived, producing
`Hom.toAlgHom`. Identity, composition, extensionality and associativity are
proved, including compatibility with algebra-map composition. An arbitrary
algebra map is not asserted smooth. The universal property uses this explicit
hom type and its composition laws; it needs no additional bundled-category
construction at this stage.

`Free n` is the actual subalgebra of functions `(Fin n → ℝ) → ℝ` satisfying
`ContDiff ℝ ∞`. Its smooth operations act pointwise by composition.
`freeEquiv n` proves `Hom (Free n) A ≃ (Fin n → A)` for every target structure,
including `n=0`. The inverse interprets a smooth function through the target
operation action. `evaluate_generator`, `evaluate_unique` and
`hom_ext_generators` prove the two inverse laws and uniqueness;
`evaluate_natural` proves naturality in target smooth homomorphisms.
No polynomial or independently generated expression syntax replaces these
smooth functions.

A tuple of smooth coordinates defining `ℝᵐ → ℝⁿ` induces
`pullback : Hom (Free n) (Free m)`. `pullback_apply` is actual precomposition;
the identity/composition theorems have this contravariant direction.
`pullback_generator` identifies the coordinate generators' images, and
`evaluate_pullback` proves interpretation commutes with smooth substitution.

`Applications/AD/SmoothAlgebras.lean` packages the ordinary reals, every
constructed square-zero stage and the second-order stage using their existing
proofs. Real dual numbers use the one-dimensional square-zero instance;
`dual_act` identifies its action with the earlier dual implementation. Existing
linear stage maps, the second-order projection and reparameterizations become
smooth homomorphisms. Neither the general theory nor this packaging imports
source syntax.

`Examples/FreeSmoothAlgebra.lean` uses uniqueness of universal evaluation to
identify any interpretation of the exponential with the earlier dual and
second-order analytic coefficient formulas. It includes a concrete evaluation
at epsilon, nullary uniqueness/constants, and a proved nonidentity exponential
coordinate pullback with its evaluation/substitution comparison.

The result supplies free smooth algebras and their interpretations in the
constructed infinitesimal stages. Quotients/localizations, infinitesimal
coproducts, a formal-manifold site and its topology/descent, and smooth
categorical KL remain open. It does not supply general Weil algebras,
well-adaptedness, cohesion or an orbifold comparison. #36 remains incomplete.

One next bounded construction is the finite-coordinate smooth Hadamard
factorization of `f(y)-f(x)` by the coordinate differences, with smooth
coefficient functions. This is the missing analytic input for proving that
ordinary ideals define congruences for all smooth operations and constructing
quotient smooth algebras.

### Smooth Hadamard factorization and ordinary quotients (#80)

`SquareKit/SmoothHadamard.lean` proves global joint smoothness of the
segment-integral coefficients and the finite-coordinate identity
`f(x)-f(y) = ∑ i, (xᵢ-yᵢ) gᵢ(x,y)`. The empty coordinate set is included.
The analytic module is independent of smooth-algebra structures and source
syntax. Its parameter-integral theorem works on a finite-dimensional real
normed parameter space with a complete real normed codomain.

The pinned Mathlib supports differentiation under interval integrals with a
locally uniform integrable derivative bound. We supply that bound by compactness
of a closed parameter ball times the closed integration interval. Continuity
supplies measurability and interval integrability. Induction on differentiability
order, with continuous-linear-map codomains, proves `ContDiff ℝ ∞` of the
parameter integral. The fundamental theorem of calculus along the segment and
finite linear expansion then prove factorization. The reused APIs are in
[Mathlib's parameter interval integration](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean)
and [fundamental theorem of calculus](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean).

Kock's III.5, Proposition 5.2 gives smooth finite Taylor factorization;
Proposition 5.4 uses its first-order case to show that ordinary ideals respect
smooth operations. The present result implements that first-order analytic
input and quotient construction. It does not yet prove the higher-order Taylor
presentation theorem of Proposition 5.11. See the author's
[Synthetic Differential Geometry, III.5](https://users-math.au.dk/kock/sdg99.pdf),
printed pages 154–156 and 159–160.

`SquareKit/SmoothQuotient.lean` places the two tuples in `Fin (n+n)` and
transports the analytic identity through `evaluate.toAlgHom`. Thus every
ordinary ideal of any `Structure` algebra is stable under all smooth operations.
The actual `Ideal.Quotient` receives its smooth operations, with representative
independence and compatibility with its existing real algebra. The smooth
projection and lift satisfy uniqueness; `homEquiv` characterizes quotient maps
by annihilation of the ideal. `lift_toAlgHom` identifies the underlying map
with Mathlib's ordinary algebra lift. `presentationEquiv` combines this with
`freeEquiv` to describe maps from presented smooth algebras by generator tuples
satisfying the ideal's relations. No properness hypothesis excludes zero rings.

`Examples/SmoothQuotient.lean` proves that the kernel of evaluation at zero on
`Free 1` is neither zero nor the whole ring. Its quotient is isomorphic to ℝ
through smooth maps with proved inverse laws. The forward map uses the general
quotient lift; exponential descends to 1 at zero and commutes with evaluation
on arbitrary quotient elements. The examples also check nullary operations in
the improper quotient and factorization with no coordinates.

This experimental construction supplies ordinary-ideal quotients. Infinitesimal
coproducts, smooth localizations, a formal-manifold site and topology/descent,
smooth categorical KL, well-adaptedness, and higher/cohesive or orbifold
comparisons remain unproved. #36 remains incomplete.

One next bounded construction is to identify the smooth presentation
`Free 1 / (x²)` with the existing real dual stage, using iterated factorization
to identify the universal evaluation's kernel. This would connect ordinary
smooth quotients to a constructed infinitesimal algebra before attempting a
formal-manifold site.

### Smooth dual extensions and their universal maps (#81)

`SquareKit/SmoothTaylor.lean` constructs each partial derivative as an ordinary
smooth operation. Applying the proved Hadamard factorization to coefficient
differences gives `taylor_remainder`: when corresponding entries differ in an
ordinary ideal I, the first-order error belongs to I². The diagonal coefficient
is the analytic partial derivative. For I generated by a square-zero element d,
I² vanishes, proving the exact nilsquare Taylor identity in every smooth algebra.
This also supplies smooth divisibility for the principal presentation below.
No synthetic Taylor rule or model-specific smooth-ideal premise is assumed.

The analytic chain rule becomes an identity in the free smooth function algebra.
Universal evaluation transports it to `differential_chain` over any smooth base.
`SquareKit/SmoothDualExtension.lean` uses these identities to put the smooth action
on the actual `DualNumber A`: its coefficients are `act f x` and
`∑ i, act (derivative f i) x * vᵢ`. Projection, substitution, constants, addition
and multiplication are proved for arbitrary A, without a real-point restriction.

The named `DualExtension.smoothStructure` is installed locally in these modules;
clients can select it with `letI := DualExtension.smoothStructure (A := A)`.
It adds no global instance competing with the earlier square-zero stages.
`Applications.AD.SmoothAlgebras.dual_structure_comparison` proves equality with
the existing real dual structure, and `extended_dual_act` recovers the earlier
analytic tangent action. The real structure now lives in the shared smooth-algebra
module; its previous application name remains an abbreviation.

The inclusion of A is smooth. Given a smooth map h and d²=0, `lift` sends
`(a,b)` to `h(a)+h(b)d`. Its smoothness follows from nilsquare Taylor. The
underlying algebra map equals Mathlib's `DualNumber.lift`; uniqueness uses that
algebraic universal property. `homEquiv` proves both directions of the smooth
mapping property, and `lift_natural` proves compatibility with any smooth target
map. `realHomEquiv` identifies maps from the real dual algebra with square-zero
elements. `coproductEquiv`, `coproduct_left` and `coproduct_right` then give the
coproduct property with both actual inclusions.

This is the dual-number case of the smooth infinitesimal coproduct discussed
in Kock III.5, Theorem 5.3. Its relationship to presentations is described by
Proposition 5.11. See the author's
[Synthetic Differential Geometry](https://users-math.au.dk/kock/sdg99.pdf),
printed pages 154–155 and 159–160. The general Weil-algebra version remains open.

`SquareKit/SmoothDualPresentation.lean` proves that the kernel of evaluation at
ε is exactly the ordinary principal ideal generated by x² in `Free 1`.
`univariate_remainder` supplies the smooth second-order divisibility: after
subtracting value and linear coefficient, the function belongs to that ideal.
The quotient lift and the dual universal map give smooth maps in both directions
between `Free 1/(x²)` and the actual real dual algebra, with inverse laws.

Checked clients evaluate exponential in a dual extension of the real dual stage,
prove its outer infinitesimal generator nonzero, and apply universal-map
naturality to a nonidentity map doubling ε. They compare all real-specialized
coefficients to the analytic Frechet derivative and exercise empty arity and
the trivial quotient algebra.

The smooth coproduct is an algebraic prerequisite for categorical KL. No small
smooth site/topology, sheaf descent, well-adapted manifold embedding, general Weil
KL, cohesion or orbifold comparison is constructed here. #36 remains incomplete.
One next bounded construction is a small category of finitely presented smooth
algebras with the dual-extension endofunctor and its universal maps, preparing
the Yoneda/exponential argument for a smooth presheaf KL model.

### A small smooth presheaf KL model (#82)

`SquareKit/SmoothStage.lean` constructs a small category whose codes include ℝ,
all `Free n`, quotients by finitely many ordinary ideal relations, and an explicit
dual-extension constructor. A code lies in `Type`; its interpreted carrier and
all smooth homomorphisms between two carriers also lie in `Type`. The bundle
holding a carrier with its algebra structures lies in `Type 1`. This does not
assert that every code has a normalized finite presentation, or classify all
smooth algebras. The site is the opposite category, with bottom topology, so its
Type-valued sheaves are the corresponding presheaves. No geometric cover is used.

The scalar is the actual underlying-carrier functor. Every finite-arity smooth
operation gives a natural map from the tuple presheaf; morphisms preserve it
because the category's arrows are smooth homomorphisms. D is the natural subtype
of square-zero elements with injective inclusion. `SmoothKL.dualFunctor`, its
inclusion and the natural infinitesimal generator use the proved smooth dual
universal property. No ring homomorphism is silently asserted smooth.

`dualRepresentable A` proves `D × y(A) ≅ y(Dual A)`. Target naturality is part of
its two natural transformations; `dualRepresentable_parameter` proves source
naturality. Universal evaluation is identified with the Yoneda comparison by
`universalValue_yoneda`. This follows the coproduct/Yoneda method of Kock III.1,
Lemma 1.1 and Theorem 1.2, now using the smooth dual coproduct of III.5,
Theorem 5.3; see the author's
[Synthetic Differential Geometry](https://users-math.au.dk/kock/sdg99.pdf).

The coefficient extraction evaluates an operation at the universal dual stage
after extending its parameter. Natural reconstruction and both coefficient
inverse laws are proved for every parameter sheaf in these universes.
`SmoothKL.kl` is an isomorphism from the scalar pair to the existing categorical
sheaf exponential `R^D`; its forward arrow is the actual affine map.
`allParameters`, `coefficients_unique` and `coefficients_parameter` give affine
existence, uniqueness and substitution for arbitrary parameter presheaves.
They do not quantify over unrelated external functions on one stage's points.

The shared `SquareKit/AffineExponential.lean` converts natural coefficient
reconstruction into the exponential isomorphism. Both the earlier algebraic KL
module and the smooth one use it. Their carrier-specific reconstruction proofs
remain separate, since the stage morphisms have different universal properties.
The new model also reuses the algebraic dual-coordinate reconstruction lemma
and the existing sheaf function-space API. Old algebraic definitions and clients
retain their statements.

`SmoothDerivative.derivative` is defined through `kl.inv`. Its Taylor and
uniqueness theorems hold at every stage; parameter assignments are natural
sheaf arrows. `interpret` maps every ordinary globally smooth unary real
function to a scalar natural map. `derivative_interpret` calculates extraction
at the universal dual stage and proves that the model derivative equals the
interpretation of the ordinary analytic derivative. Its smoothness is proved
from smooth Frechet differentiation. `derivative_real` exposes the real-stage
component as a `HasDerivAt` theorem. The model derivative is not defined by
that analytic formula.

`Examples/SmoothKL.lean` checks exponential, nonlinear parameter substitution,
a nonzero infinitesimal, and restriction along a nonidentity map doubling ε.
A one-relation ordinary presentation stage carries an evaluation map, used to
compute its exponential restriction. At the real stage all external D-points
are zero, so two different affine slopes have equal external evaluations.
The internal functions remain distinct by the constructed inverse. This is the
smooth counterpart of the earlier algebraic boundary example.

The result is smooth first-order categorical KL for this bottom-topology model.
It supplies no geometric open-cover descent, well-adapted manifold embedding,
general Weil KL, cohesion or orbifold comparison. #36 remains incomplete.
One next bounded construction is principal smooth localization for a free
finite-coordinate stage, with its inverse-element presentation and universal
mapping property. That would supply candidate basic-open restriction maps
before a geometric topology is proposed.

### Principal smooth localizations and their points (#83)

Kock, *Synthetic Differential Geometry*, second edition, III.5, pp. 156–157,
constructs smooth localization by adjoining a smooth coordinate and imposing
`bt=1` (equation (5.4)). The same discussion distinguishes smooth localization
from ordinary ring localization and uses partitions of unity for open-set
refinements. Those analytic refinements require additional proofs; the inverse
presentation alone does not supply them. [Author's text](https://users-math.au.dk/kock/sdg99.pdf).

`SquareKit/SmoothLocalization.lean` constructs this presentation from the
existing free smooth algebra and ordinary-ideal smooth quotient. A finite list
of functions shares one presentation and universal property; principal
localization uses one inverse coordinate. For every smooth target algebra,
`homEquiv` identifies smooth maps out with smooth maps from the original free
algebra that send the listed functions to units. `Ring.inverse` supplies the
forced inverse coordinates. The proof uses pinned Mathlib's unit cancellation
and quotient APIs, not an assumed smooth structure on ordinary localization.
Inverting zero gives the improper quotient; inverting one gives inverse smooth
maps with the original free algebra, including arity zero.

Smooth maps compatible with the inverted functions induce localization maps,
with identity and composition laws. The two-function presentation is also a
localization of the first principal localization: `iteratedLift` factors all
smooth maps sending the second function to a unit, and `iterated_unique` proves
uniqueness. It has inverse smooth maps with localization at the product.
`SmoothLocalizationStage` realizes these as actual finite-presentation stages
and exposes coordinate restriction and the same universal property for stage
Homs. The algebra arrows have the opposite direction to geometric maps.

`SmoothLocalizationPoints` identifies real points with tuples where the function
is nonzero and proves this locus open. Dual points are pairs `(x,v)` with the
same condition on the base point. The inverse generator has value `1/f(x)` and
tangent coefficient `-Df(x)(v)/f(x)^2`. This calculation uses the actual dual
smooth operation, the inverse relation and uniqueness of an inverse. Residue
and arbitrary scalar changes of tangent coordinates commute with the point
identification. `Examples/SmoothLocalization` uses exponential localization,
its analytic dual inverse, iterated inversion of exponential and the coordinate,
nullary boundary cases, and a nonidentity tangent scaling. The nilpotent ε has
nonzero tangent but is not a unit.

No identification with the full smooth-function algebra on the open locus has
been proved. Real-point agreement is insufficient for that claim. Cover
descent, well-adaptedness, general Weil KL, and the higher/cohesive target remain
open, and the model still uses bottom coverage. One next bounded construction
is the smooth-algebra comparison between this principal presentation and the
algebra of smooth functions on its ordinary open locus, including the analytic
extension argument needed for surjectivity. This would connect the proved
universal presentation with the open-set geometry before introducing covers.

### Full smooth functions on principal opens (#84)

Kock, *Synthetic Differential Geometry*, second edition, III.6, Proposition 6.4
and equations (6.6)–(6.7), pp. 165–167, identifies smooth functions on a principal
open with the inverse-graph quotient. The proof combines local Hadamard
divisibility with a partition of unity; the same gluing supplies extension from
the closed graph. [Author's text](https://users-math.au.dk/kock/sdg99.pdf).

`SquareKit/SmoothOpenFunctions.lean` defines the full ordinary smooth-function
algebra on a subset using `ContDiffOn` of its zero extension. On an open subset,
`smooth_iff` identifies this with smoothness at every domain point.
`representative_iff` permits any ambient representative agreeing on the subset,
requiring smoothness only there. Consequently the definition imposes no smooth
extension across the boundary. Pointwise ring operations and all finite smooth
operations preserve this condition. The repository's manifold/diffeology bridge
uses the same ordinary calculus through `contMDiff_iff_contDiff`; this construction
does not change that bridge or introduce a competing smoothness axiom.

`SmoothLocalGluing` specializes pinned Mathlib's
`exists_contMDiffMap_forall_mem_convex_of_local` to ordinary finite-dimensional
calculus. It constructs global smooth functions satisfying convex pointwise
constraints, including scalar linear equations and prescribed values on a
closed set. Local candidates need only be smooth on their neighborhoods.
The underlying partition of unity is locally finite; neither the closed set nor
the desired function is required to be compact or bounded.

`SmoothInverseGraph.extension` applies that gluing to the closed zero set of
`f(x)t-1`, inside the open set where `f(x)` is nonzero. The local candidate is
`g(x)`. `divisibility` uses the previously proved smooth Hadamard coefficient
along the added coordinate. Where `f(x)` is nonzero, division by `f(x)` gives a
local quotient by `f(x)t-1`. Off its zero set, ordinary division by the relation
gives a local quotient. Gluing solutions to the scalar equation yields a
globally smooth quotient. This proves exact ideal membership for this relation;
it assumes no general point-detection or radical property of smooth ideals.

`SmoothLocalizationOpen.graphRestriction_kernel` and
`graphRestriction_surjective` produce `openEquiv`, with smooth maps `toOpen` and
`fromOpen` and both inverse laws. The inverse may choose an extension, but
`extension_independent` proves that all representatives of the same function
give the same quotient class. The comparison respects original base functions,
the inverse generator and the real-point universal evaluation from #83.
Restriction to the principal open for a product commutes with the earlier
iterated/product localization maps. The checked clients include `1/x`, which
has no continuous extension at zero but does have an inverse-graph extension,
`exp(1/x)`, empty and whole opens, and restriction to a smaller principal open.

This identifies the full ordinary smooth-function algebra for principal opens
of finite real coordinate spaces. Cover descent for formal stages, localization
base change beyond these free stages, compatibility with infinitesimal
extensions, well-adaptedness, general Weil KL and the higher/cohesive target
remain open. One next bounded construction is principal localization of
arbitrary finite-presentation smooth stages with its universal base-change
square. That would extend the available restriction maps to the formal stages
needed before a geometric coverage can be justified. #36 remains incomplete.

### Formal-stage localization and base change (#85)

`SquareKit/SmoothPresentation.lean` constructs a finite smooth presentation
with one additional coordinate and one additional relation. Original relations
are pulled back along the coordinate inclusion. Its universal map accepts an
arbitrary smooth map out of the original quotient and a value satisfying the
new relation. This common construction supplies both inverse coordinates and
nilsquare coordinates.

`SmoothPresentedLocalization` imposes `p(x)t-1` for any representative `p` of
an element of the original presentation. `At r s` chooses a representative
internally for an arbitrary quotient element `s`; callers supply neither a
coordinate expression nor an inverse. Its `atHomEquiv` classifies maps to every
smooth target algebra by the condition that `s` maps to a unit. The factorization
uses the forced ring inverse and proves uniqueness, both inverse laws and target
naturality. `SmoothLocalizationBaseChange` constructs canonical comparisons
between equal representatives, with both inverse laws and agreement on the
original algebra. Unit localization is unchanged; nilpotent localization is
the improper quotient.

For every smooth map between finite presentations, `atMap` induces localization
at the image element and satisfies identity and composition. `pushout_universal`
constructs and uniquely characterizes the factorization of every compatible pair
of maps to every smooth target. No coordinate presentation of the map is
required. This is the algebra variance of a geometric pullback, consistent with
Kock, III.6, Proposition 6.7, p. 167, which obtains inverse-image open sets from
the localization pushout. [Author's text](https://users-math.au.dk/kock/sdg99.pdf).

`SmoothPresentedDual` gives a finite presentation of the existing smooth
`DualNumber A` by adjoining a nilsquare coordinate. Its comparison maps are
smooth and inverse, and preserve the base and ε. `SmoothLocalizationDual`
then uses #81's dual universal maps to prove that `DualNumber (A{s⁻¹})` is a
localization of `DualNumber A` at `inl(s)`. `dualHomEquiv` quantifies over all
smooth targets. The alternative finite presentation, localizing the presented
dual algebra, has explicit inverse smooth comparisons with this actual dual
extension. Base inclusions and nilsquare generators commute with the comparison.
The inherited dual ring, real algebra and smooth operations are retained.

`SmoothFormalLocalizationStage` packages the ordinary localization, its base
arrow, the universal square and dual comparison in the existing coded stage
category. `SmoothLocalizationFreeComparison` compares the empty-relation case
with the preceding free-algebra localization and composes the comparison with
the full ordinary-open function algebra isomorphism from #84.

The checked nilpotent client is `Free 1/(x²)`. Its ε is nonzero, stays nonzero
when `1+x` is inverted, and makes localization at `x` trivial. A nonidentity
smooth map doubles ε. A nonpolynomial representative `exp(x)` admits evaluation
in the actual real dual algebra; adding `x²` yields the canonical equivalent
localization. Further clients use the arbitrary-target pushout, the dual
factorization and nilsquare-generator comparison, and the empty/improper cases.
These claims retain nilpotent information beyond the real-point locus.

The model still has bottom coverage. No formal cover descent, well-adapted
manifold embedding, general Weil KL or higher/cohesive comparison follows from
these algebra squares alone. One next bounded construction is finite
principal-cover descent for the scalar functor on these presentation stages,
with the cover condition and compatibility equations stated explicitly.
That would provide descent evidence before selecting a geometric coverage.
#36 remains incomplete.

### Finite principal scalar descent (#86)

`PrincipalCover.Covers s` means that a finite ordinary linear combination of the
quotient elements `s i` equals one. It is equivalent to their ordinary ideal
being the whole algebra. For a finite presentation, `covers_iff_zero_locus`
proves equivalence with covering every real point of the relation locus.
`empty_iff` includes the empty cover exactly for a trivial base algebra.
This point criterion concerns covers; it does not identify elements of the
quotient by their real values.

Kock's III.6, Theorem 6.3 (pp. 163–164), proves local determination of finite
smooth ideals with partition-of-unity coefficient gluing. III.7, Definitions
7.1–7.2 and Theorem 7.4 (pp. 168–171), use principal smooth localizations and
point-covering families to obtain a subcanonical open-cover topology. The
finite-presented setting avoids the additional germ-determined reflection
needed for his broader category. Our finite cover result follows this analytic
route while retaining the original ideal. [Author's text](https://users-math.au.dk/kock/sdg99.pdf).

`SmoothIdealLocal.global_iff` proves that local smooth coefficient equations
characterize membership in a finite ordinary ideal. `SmoothLocalizationLocalIdeal`
combines that fact with inverse-graph Hadamard division to characterize zero
in a presented localization. `SmoothIdealGluing.finite_gluing` uses a subordinate
smooth partition of unity to glue local representatives modulo that ideal.
The ambient cover includes the relation-nonzero opens, where the ideal is
locally the whole ring. No bounded-power fraction representation is assumed.

`SmoothElementDescent.atDescentEquiv` identifies the base algebra with **all**
compatible tuples in `At r (s i)`. Its overlaps are `At r (s i * s j)`;
`at_overlap_pushout` constructs the universal smooth algebra square, with
opposite geometric pullback variance. Both directions preserve every finite
smooth operation. Gluing commutes with arbitrary smooth maps of finite
presentations and their transported covers. `SmoothDescentDual` compares this
naturality with the actual dual algebra through the checked dual presentation,
and recovers arbitrary dual elements, including their infinitesimal parts.

The clients cover the free real line by `x` and `1-x`, neither a unit; glue
exponential local data; and glue a nonzero ε in `Free 1/(x²)` whose value is
zero at every real point but whose actual dual coefficient is one. The failed
zero cover loses separatedness. The improper quotient admits empty gluing.

The existing KL model still uses bottom coverage. This result supplies finite
scalar descent, not a constructed geometric topology or a proof that its
representables are sheaves. One next construction is the finite-principal
Grothendieck topology on presentation stages, with its cover axioms and
subcanonicity proved from this descent result. KL in that sheaf model,
well-adaptedness, general Weil KL and higher/cohesive comparisons remain open.
This does not complete #36.

### Finite-principal geometric site and subcanonicity (#87)

`SmoothPresentationSite.Code` is a small category of finite smooth
presentations, with all smooth maps between their actual quotient algebras.
`toStage` is fully faithful into the corresponding presented objects of the
previous coded-stage category. Free finite-coordinate codes represent tuples;
dual codes have inverse smooth comparisons with actual dual numbers. This
category does not claim to classify all smooth algebras or arbitrary manifolds.

The site is the opposite category. `coverage` consists of finite principal
families satisfying #86's ordinary unit-ideal condition. Its refinement axiom
is proved under every smooth arrow. `localization_isPullback` packages the
checked algebra pushout as a categorical pullback, and
`principalSieve_pullback` identifies the pullback of each generated sieve with
the image-element family. `topology` is Mathlib's Grothendieck topology generated
by this coverage. `principal_covering_iff` proves that a principal family
generates a covering sieve exactly when it satisfies the ordinary unit-ideal
condition; `principal_maximal_iff` distinguishes maximal sieves by the presence
of a unit member.

Kock's III.7, Proposition 7.3 and Theorem 7.4 (pp. 169–172), derive open-cover
stability from smooth localization and prove all-representable sheafness via
a smooth-algebra equalizer. Exercise 7.1 distinguishes empty covers of the zero
algebra. Our construction treats the topology generated by finite principal
covers of finite presentations, rather than his broader category and arbitrary
open-cover families. [Author's text](https://users-math.au.dk/kock/sdg99.pdf).

`scalar_principal` turns categorical matching families into #86's scalar tuples
by testing them on the actual overlaps. `isSheaf_iff_principal` applies the
proved coverage generation theorem, including stability under arbitrary arrows,
to obtain the full sieve sheaf condition. `SmoothDescentHom.glueHom` glues maps
from every smooth source algebra and proves preservation of all smooth
operations. `yoneda_principal` uses this map construction for every source
presentation. The resulting `topology.Subcanonical` instance follows from
all-representable sheafness; it is not assumed as the topology's definition.

The actual scalar sheaf is isomorphic to the representable free one-coordinate
object. The tuple sheaves are representable by free finite-coordinate objects,
and `powerIsLimit` proves their finite-product universal property. All finite
smooth operations are sheaf morphisms. Restriction to bottom coverage agrees
with the preceding model on the common presentation category, for scalars,
finite powers and operations. No preservation of exponentials is asserted.

The checked real-line sieve generated by `x` and `1-x` covers and is not maximal.
The topology is neither bottom nor chaotic. A nilpotent matching family on all
arrows of a covering sieve has a categorical amalgamation whose actual dual
coefficient is one, despite vanishing at every real point. The empty sieve
covers the zero presentation and the sheaf condition supplies its unique scalar.
A further client uses the sheaf condition for arbitrary representable matching
families.

One next construction is categorical KL in this geometric sheaf category,
using the represented infinitesimal and the checked dual presentations to
identify the actual sheaf exponential. That comparison has not been proved.
Arbitrary-cover and manifold-embedding results, well-adaptedness, general Weil
KL and higher/cohesive comparisons also remain open. #36 remains incomplete.

## Geometric sheaf KL and an interpreted product proof (#88)

The finite-principal site now supports first-order KL in its actual sheaf
exponential. `SmoothGeometricInfinitesimal` constructs the square-zero subtype
sheaf by scalar gluing and separatedness. `SmoothGeometricRepresentable`
constructs `D × y(A) ≅ y(dual A)` with naturality in both arguments. Its dual
code is the finite presentation from #85; `dualToActual` transports sections
to actual dual numbers. `SmoothGeometricKL.universalValue` evaluates a natural
map at the universal epsilon after extending its parameter to that code.
Reconstruction and recovery feed the shared `AffineExponential.iso` theorem.
The resulting `kl` has the original affine map as its forward arrow, with
both inverse equations and arbitrary sheaf parameters.

`SmoothGeometricDerivative.derivative` extracts through that inverse.
Taylor and slope uniqueness quantify over all presentation stages and all
square-zero elements. `derivative_interpret` identifies it with the analytic
derivative of every globally smooth unary real function. `derivative_real`
observes the resulting coefficient through `realValue` at the actual free
zero-coordinate presentation. `SmoothGeometricComparison` compares universal
values, coefficients and derivatives with #82 on the common category. The
specific restricted infinitesimal function object is proved a sheaf through
its old KL isomorphism to scalar pairs. Its constructed comparison to the
geometric exponential preserves evaluation and currying. No general
preservation of exponentials by forgetting or restriction is used.

The existing `SyntheticScalar` source language and product derivation are
unchanged. `SyntheticScalarSoundness.sound_eval` factors the ring-rule induction
shared by the old algebraic adapter and `SyntheticScalarGeometric`. Each
adapter supplies Taylor from its own constructed model. All admitted source
rules and the separate slope judgment are interpreted. The optional
`GeometricProductRule.product` invokes that source derivation through soundness;
ordinary model modules have no source imports. In
`Examples.GeometricSyntheticProduct`, the coefficient for `exp(x)*exp(x)` comes
from this theorem. Its ordinary `HasDerivAt` consumer uses that coefficient
identity and the analytic chain rule for `exp(x+x)`. The same client uses
ordinary smooth operations, arbitrary parameter substitution, a nonidentity
nilpotent restriction and the earlier internal/external boundary witnesses.
`SmoothGeometricLocality` glues the extracted coefficient using actual sieve
matching and sheaf separatedness; the example instantiates the proper line
cover from #87.

Kock's [*Synthetic Differential Geometry*, II.4–5 and III.7–8](https://users-math.au.dk/kock/sdg99.pdf)
distinguishes generalized-element exponential semantics from the additional
open-cover and smooth-embedding obligations of well-adapted models. The local
construction above establishes the first-order geometric KL chain for the
finite-cover topology. Arbitrary covers, a manifold embedding and its
well-adaptedness properties, general Weil objects, higher identity structure,
cohesion and the Myers orbifold comparison remain unproved. This does not
complete #36.

Recommended next construction: extend scalar descent to arbitrary
point-covering families of principal opens of finite smooth presentations,
retaining quotient/nilpotent information. That would address the finite-cover
limitation before claiming the smooth manifold embedding.

## Arbitrary principal covers on finite presentations (#89)

`SmoothAlgebra.OpenCover.Covers` quantifies over every smooth map from the
presented algebra to ℝ: some member of the family has nonzero image. The
analytic/descent API allows an index type in `Type u`; the generated site uses
indices in `Type`, matching its small presentation category. For `Fin k`
families the condition is proved equivalent to the earlier ordinary unit-ideal
condition. It is stable under every smooth algebra map. The empty family covers
exactly a trivial finite presentation. These statements concern covers; scalar
equality still uses the full quotient ideal.

`SmoothIdealArbitraryGluing.arbitrary_gluing` constructs a subordinate smooth
partition of unity for an arbitrary open cover. Its assembled function is a
locally finite `finsum`. At each point, local finiteness gives one neighborhood
and a finite set containing the supports that meet it. On that neighborhood
the sum reduces to a finite sum of local ideal coefficient equations. The
relation list remains finite; neither the input cover nor its local
representatives have a finiteness or boundedness assumption.

`SmoothOpenDescent` applies this construction to inverse-graph representatives
of arbitrary compatible localized elements. Existence and uniqueness preserve
neighborhood ideal membership, including nilpotents. `SmoothOpenDescentOperations`
proves every finite-arity smooth operation and arbitrary smooth base map
commutes with gluing. The localization overlaps, compatible sections and
transport definitions are shared with the previous finite-family development.
`SmoothOpenDescentHom` glues all smooth maps into the presented algebras.

`SmoothOpenSite.coverage` and `topology` use these actual principal families.
All-arrow pullback/refinement is proved, the finite-principal topology is
contained in it, and `SmoothOpenSheaf` proves scalar and every representable
sheafness on the generated topology. `SmoothOpenScalar` constructs its scalar,
finite powers and smooth operations from the shared coordinate presheaves,
with explicit comparisons under forgetting stronger sheafness.

`Examples.ArbitrarySmoothCovers` uses the smooth functions
`expNegInvGlue((n+1)^2-x^2)` for `n : ℕ`. They cover the line; every finite
subfamily misses a point beyond its largest radius. Actual categorical
matching-family gluing recovers an exponential section. The infinite-family
smooth-operation law is exercised separately. Pulling the same family to the
thickened line gives another family with no finite subcover, and gluing its
epsilon sections retains a nonzero dual coefficient invisible to all real
points. A countable family missing the origin fails the cover condition.

Kock's [*Synthetic Differential Geometry*, III.7, Definition 7.2 and Theorem 7.4,
pp. 168–172](https://users-math.au.dk/kock/sdg99.pdf) defines covers by real-point
surjectivity and proves subcanonicity using locally finite partitions and local
ideal information. The checked construction here restricts objects to finite
presentations and generators to principal localizations, but no longer
restricts those families to be finite. It does not identify arbitrary smooth
algebras with finite presentations.

Recommended next construction: factor the presentation-based first-order KL
argument over the topology's proved scalar/representable sheafness and
instantiate it for this arbitrary-cover topology, with a checked comparison to
#88. KL, its derivative and the synthetic proof interpretation currently remain
objects of the finite-principal sheaf category. This slice does not prove their
upgrade, a full ordinary manifold embedding, well-adaptedness, general Weil
objects, higher identity structure, cohesion or the Myers orbifold comparison.
It does not complete #36.

## Shared KL in the arbitrary-cover model (#90)

`PresentationGeometry` constructs the square-zero subsheaf and affine map for
an explicit topology on the presentation site, using only proved scalar
sheafness. `SmoothGeometricKL`, its derivative, locality and synthetic soundness
now share this parameter. The representable dual-product comparison additionally
uses subcanonicity. Both concrete topologies supply these hypotheses from their
existing proofs. `SmoothOpenKL` instantiates the actual sheaf exponential and
its affine isomorphism in the arbitrary-principal topology.

Coefficient extraction still evaluates on the concrete presented dual extension
and transports to actual dual numbers. Reconstruction and uniqueness quantify
all parameter sheaves and all presentation maps. Differentiation uses the inverse
of that exponential isomorphism; Taylor, unique slope and the ordinary derivative
of every globally smooth unary operation follow from the same construction.
`SmoothTopologyKLComparison` compares the particular exponential, evaluation,
currying and derivative under forgetting stronger sheafness through their shared
coefficient descriptions. It makes no general exponential-preservation claim.

`Examples.OpenSyntheticProduct` specializes the existing all-rule synthetic
interpretation and its derived product proof. The analytic exponential-product
consumer uses that proof's coefficient equality. The inverse-defined derivative
also glues on #89's countable cover with no finite subcover. Nonidentity base
change and a nonzero nilpotent invisible to all real points check the stagewise
content. The finite-topology examples remain checked.

Kock's [*Synthetic Differential Geometry*, III.7–8](https://users-math.au.dk/kock/sdg99.pdf)
connects smooth-site sheafness with well-adapted models. The result here supplies
first-order KL on the constructed arbitrary-principal site of finite
presentations. Ordinary manifold embedding and full well-adaptedness, general
Weil KL, higher identity structure, cohesion and the Myers orbifold comparison
remain unproved. #36 remains incomplete.

Recommended next construction: embed Euclidean principal open loci and all
ordinary smooth maps between them fully faithfully in this sheaf category.
The checked open-locus function-algebra identification from #84 and subcanonicity
supply the algebraic and categorical parts; their compatibility with ordinary
smooth maps is the next concrete prerequisite for a manifold comparison.

## Ordinary principal-open embedding (#91)

`EuclideanOpen.Domain` records a finite dimension and a globally smooth defining
function. Its points are the function's nonzero locus. Morphisms are all maps
between these domains whose coordinates are smooth on the source open set.
`OpenFunctions.Map.smooth_iff` identifies this condition with ordinary local
smoothness; the coordinate representatives have no regularity requirement away
from the source. Empty domains and dimension zero are included.

`SmoothOpenDuality` reconstructs an ordinary map from every smooth homomorphism
between the localization algebras. At a source point it composes the algebra
map with evaluation and uses the existing real-point universal property to
obtain a target point. Images of coordinate generators prove smoothness.
The inverse proofs use #84's bijection with the full smooth-function algebra;
they do not assert point detection for arbitrary presentation quotients.
Pullback preserves all finite-arity smooth operations and contravariant
composition.

`EuclideanOpen.embedding` composes this fully faithful contravariant algebra
construction with the proved arbitrary-cover sheaf Yoneda embedding. The
result is a covariant fully faithful functor. Its map formula is actual
algebraic pullback, and its point formula is ordinary evaluation. Full
Euclidean domains compare to the existing scalar finite powers. Principal
open inclusions recover localization on generators; intersection inclusions
recover the existing product-localization maps. Globally smooth operations
commute with these comparisons.

`Examples.EuclideanOpenEmbedding` recovers reciprocal on the punctured line
through the full-faithfulness inverse and proves that no continuous ambient
extension exists. It checks exponential, its existing scalar interpretation,
composition with reciprocal, arbitrary sheaf-arrow recovery and the absence
of a point from the zero-dimensional full domain into the empty domain.

Kock's [*Synthetic Differential Geometry*, III.5, Corollary 5.8, pp. 158–159,
and III.8, Theorem 8.4, p. 176](https://users-math.au.dk/kock/sdg99.pdf)
reconstructs smooth maps from evaluation after algebra homomorphisms, then
combines algebraic full faithfulness with Yoneda. This development proves that
argument for Euclidean principal opens in the constructed site. A full manifold
embedding, preservation of transversal pullbacks and well-adaptedness remain
unproved, as do general Weil KL and higher/cohesive/orbifold comparisons.

Recommended next construction: prove compatibility of this embedding with
ordinary principal-open cover descent, including overlap maps and gluing of
ordinary smooth maps. This connects the checked local domains to the
arbitrary-cover topology before assembling manifold atlases. #36 remains open.

## Ordinary covers and sheaf descent (#92)

`EuclideanOpen.Covers` says that the nonzero loci of an arbitrary family of
globally smooth functions cover an ordinary principal open domain. Its
`covers_iff_union` and `covers_iff_algebra` identify this with the union of the
subdomains and the actual localization algebra's `OpenCover.Covers` condition.
These statements allow Type u indices. The generated small-site covering
assertion uses Type indices, including the empty family on an empty domain.

`subdomainIso` identifies the presentation of U_(f*g) with localization of the
presentation of U_f at g. Both directions are constructed from the existing
localization universal properties, for arbitrary smooth target algebras.
`baseChangeMap` gives actual base change along every ordinary smooth map.
When its pulled-back defining element has a specified globally smooth
representative on the source, `restriction` constructs the corresponding
ordinary restriction and proves the commuting localization square. Neither
construction requires the ordinary map to extend to the ambient space.

`coverSieve_eq` identifies the ordinary family's generated sieve with the
site's principal sieve. `overlap_universal` proves the all-algebra pushout
property for U_(f*g*h), and `overlap_site_pullback` and
`overlap_sheaf_pullback` give the opposite categorical pullbacks. These
statements quantify all stages, not only ordinary points.

`glue` constructs the unique ordinary smooth map from a compatible family
into any principal-open target. Target membership comes from a local map;
smoothness follows from agreement with that map on an open neighborhood.
There is no finite-subcover, boundedness or ambient-extension assumption.
`sheaf_exists_unique` separately applies the proved covering sieve's actual
sheaf condition and Yoneda equivalence, with the all-stage overlap pullbacks,
to obtain unique descent into every sheaf. `cover_jointly_epic` and
`glue_sheaf_comparison` identify the embedded cover and ordinary reconstruction
with this categorical descent. No general colimit-preservation claim is used.

`Examples.OrdinaryOpenDescent` reuses #89's countable defining functions and
no-finite-subcover theorem. Its exponential family reconstructs through the new
gluing theorem and compares to sheaf descent. A proper, nonempty overlap,
reciprocal base change and the empty cover's initial sheaf object are checked.

Kock's [*Synthetic Differential Geometry*, III.7–8, especially the descent
arguments on pp. 174–175 and the covering assertion on p. 177](https://users-math.au.dk/kock/sdg99.pdf)
uses subcanonical sheaf gluing to pass from local geometric constructions to
global ones, and sends open covers to jointly epic sheaf families. The checked
result here establishes this connection for the constructed principal-open
embedding. It does not assemble manifolds or prove general transverse-limit
preservation, well-adaptedness, all Weil KL, or higher/cohesive/orbifold claims.

Recommended next construction: realize ordinary smooth manifolds by gluing
principal-open charts, with chartwise map descent and independence of common
refinement. The local algebra, overlap and covering comparisons needed for
that construction are now checked. #36 remains incomplete.

## Ordinary atlas realization and refinement (#93)

`EuclideanOpen.Atlas` is a small atlas on a topological type in `Type`.
Its charts are principal open subsets of finite real coordinate spaces,
with open embeddings covering the underlying space. Dimensions may vary.
The transition condition supplies ordinary smooth maps on neighborhoods of
every point in a chart intersection. It requires neither an ambient global
extension nor a sheaf realization. Hausdorffness, second countability and a
fixed dimension are not imposed. Applications can impose these separately.

The underlying `Charts` presentation records the coordinate maps.
`Charts.Relation` consists of all pairs of ordinary smooth maps from a
principal domain into charts that agree in the underlying space. Thus it
includes tests on refinements of arbitrary overlaps. `openDefining_locus`
uses Mathlib's proved smooth-support theorem for Euclidean open subsets;
`inverseRestriction` and `inverse_covers` construct pullbacks of principal
covers along arbitrary ordinary smooth maps. No single-principal-overlap
assumption is made. `Atlas.subdivision` proves that arbitrary principal-cover
subdivision retains the ordinary atlas conditions.

`Charts.realization` is a multicoequalizer in the existing arbitrary-cover
sheaf category. Mathlib constructs its colimits by sheafifying presheaf
colimits. `Charts.homEquiv` identifies arrows into **every sheaf** with chart
maps compatible on every overlap test. `Charts.Map.realize` sends chartwise
ordinary maps to sheaf maps; its identity and composition laws are checked.
Different chart choices for the same underlying function induce equal maps.
This interface requires each source chart to land in a chosen target chart.
It also supports maps after the specified ordinary cover refinements through
`refinement_naturality`.

A `Charts.Refinement` consists of a chartwise identity map and ordinary
principal covers of the old charts with smooth lifts into the refining
charts. Its inverse realization map is constructed with #92's every-sheaf
descent. `section_test` proves its equality on arbitrary ordinary overlap
tests using inverse-image covers; it is the step that makes the descended
chart maps compatible. `Refinement.iso`, `subdivisionIso` and
`overlapRefinementIso` prove replacement of charts and overlap tests by covers
with commuting chart maps. `commonRefinementIso` has reflexivity and
composition coherence. These proofs do not assume that the domain embedding
preserves arbitrary colimits.

`singleIso` recovers an embedded principal domain, and `coverAtlasIso`
recovers it from any ordinary principal cover. The checked application
`Examples.OrdinaryChartRealization` uses the countable cover with no finite
subcover, an atlas whose two coordinate orientations differ by negation,
the induced reflection and its involution law, and an atlas with no charts
on the empty space. The reflection example has a proved nonidentity chart
transition. The universal property is also specialized to arbitrary sheaf
targets on the infinite atlas.

Kock's [*Synthetic Differential Geometry*, III.8, pp. 174–177](https://users-math.au.dk/kock/sdg99.pdf)
uses local sheaf arguments in constructing the manifold model. Theorem 8.4
also requires full faithfulness and transverse-pullback preservation, and
its covering assertion uses jointly epic families. The present construction
supplies atlas colimits and cover comparisons in our finite-presentation
site; it does not identify that site with every model in Kock's theorem.

The bridge from Mathlib's `ChartedSpace` and `IsManifold` structures remains
unconstructed. For ordinary finite-dimensional manifolds without boundary,
chart images are open Euclidean sets; the smooth-support theorem removes
that domain-presentation obstacle. A bridge must still extract the atlas
and its local transition proofs and identify manifold smooth maps with the
supported locally chartwise maps, independently of chart choice. Full
faithfulness for all manifolds, preservation of transverse limits, full
well-adaptedness, general Weil comparisons, and higher/cohesive/orbifold
constructions remain unproved.

Recommended next construction: convert Mathlib's ordinary finite-dimensional
smooth manifold charts and smooth maps into this atlas realization, with
chart-choice independence. This directly tests the remaining interface
between ordinary manifolds and the constructed sheaf model. #36 remains open.

## Mathlib manifold interpretation and arbitrary smooth maps (#94)

`ManifoldRealization.object n M` now constructs the sheaf of an actual Mathlib
manifold with `M : Type`, `ChartedSpace (Fin n → ℝ) M` and
`IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M`. The model is the full finite-dimensional
real space, so this scope excludes boundary charts. Dimension zero and empty
manifolds are allowed. Neither Hausdorffness nor second countability is needed
for the construction. Those assumptions can be added by applications.

`ChartFamily` selects any small covering family of members of Mathlib's
maximal smooth atlas for the fixed charted-space structure. `preferred` uses
Mathlib's actual `chartAt`. `chartDomain` constructs a principal presentation
of each open chart target by the proved smooth-support theorem. `chartPoint`
is the chart inverse on that target. `ChartFamily.atlas` proves the ordinary
open-embedding, cover and local-transition obligations of #93; these are not
extra assumptions supplied by callers.

For `ContMDiff` maps of any two dimensions, `coordinateDefining` describes
the part of a source chart whose image lies in a selected target chart.
`coordinateMap` is the actual composite of chart inverse, ordinary map and
target chart. Its smoothness follows from Mathlib's maximal-atlas smoothness
lemmas and the equivalence between `ContMDiff` and `ContDiff` on vector spaces.
Only smoothness on the coordinate domain is used. No global ambient extension
or whole-source-chart containment is required. Target charts give the proved
principal cover of each source chart.

`Charts.LocalMap` records ordinary coordinate maps on such covers.
Its realization descends the local maps into the target chart colimit;
`section_test` verifies agreement on arbitrary smooth overlap tests.
`realize_eq` removes all local chart and cover choices, and `realize_comp`
compares separately chosen covers for two maps and their composite. The old
`Charts.Refinement` descent now uses this common implementation, preserving
its public interfaces and the #93 isomorphisms.

`ManifoldRealization.map` is defined for every Mathlib `ContMDiff` map in the
stated scope. `map_id` and `map_comp` form a checked indexed interpretation,
with dimensions and manifold types allowed to differ. `atlasIso` and
`atlas_naturality` compare the preferred atlas with any `ChartFamily`.
`commonAtlas`, `commonLeft` and `commonRight` construct an ordinary common
refinement by chart intersections; `comparison_common` identifies its actual
#93 refinement isomorphism with the interpretation of the identity map.
Reflexivity and composition of comparisons are proved. These comparisons
concern families within the fixed maximal smooth atlas, not unrelated
charted-space structures on the same underlying type.

`principalIso` identifies the interpretation of Mathlib's ordinary open
submanifold for any existing principal domain with `EuclideanOpen.embedding`.
It includes empty domains: the local cover is indexed by the points of the
open, so no inhabitant is chosen for an empty open. The existing one-chart
comparison is used in the final isomorphism.

`Examples.MathlibManifoldRealization` checks the identity map from a global
line chart into two overlapping proper target charts. Its
`no_whole_target_chart` proves that neither target chart contains the entire
source chart, while `splitIdentity_local` consumes the new interpretation.
The example also interprets the nonpolynomial exponential and its atlas
transport, the punctured line with Mathlib's inherited open-submanifold
structure and its inclusion, its principal-domain comparison, dimension zero,
and the initial sheaf assigned to the empty manifold.

Kock's [*Synthetic Differential Geometry*, III.8, pp. 174–177](https://users-math.au.dk/kock/sdg99.pdf)
uses local smooth geometry and sheaf descent in the construction of its
manifold model. Theorem 8.4 additionally asserts full faithfulness and
transverse-pullback preservation. The checked construction here uses the
[pinned Mathlib maximal-atlas smoothness results](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean)
and [open-submanifold structures](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/HasGroupoid.lean).
That delivery established choice independence and composition. The following
construction supplies the previously missing full faithfulness.

## Full faithfulness of the manifold interpretation (#95)

`SquareKit/SmoothManifoldFullFaithfulness.lean` constructs
`ManifoldRealization.homEquiv` between all functions satisfying Mathlib
`ContMDiff (Model n) (Model m) ∞` and all arrows
`object n M ⟶ object m N`. Its forward map is the existing `map`.
`reconstruct_map` and `map_reconstruct` prove both inverse laws.
The dimensions may differ. The scope remains Type-sized, finite-dimensional
real boundaryless manifolds, including empty and zero-dimensional manifolds.
No Hausdorffness, second countability, global chart, ambient extension, or
full-faithfulness hypothesis has been added.

The reconstruction has two separate ingredients. `SmoothRealPointCovers`
proves that every covering sieve lifts real points and constructs a point of
the actual generated site. Consequently evaluation at the real stage preserves
sheaf colimits. `SmoothOpenRealSections` identifies real sections of each
ordinary open with its points. `SmoothChartRealSections.realEquiv` then
identifies real sections of a covering chart realization with its underlying
point set. Equal ordinary chart points are related by a zero-dimensional
ordinary overlap test. These results concern real sections only; they do not
identify arbitrary infinitesimal sections by their real-point values.

`SmoothOrdinaryCoverLifting.covering_local_inclusion` proves that every site
cover, tested on an ordinary open, contains ordinary coordinate inclusions
around each source point. The proof uses actual local units in the full
smooth-function algebra and induction on the generated topology.
`SmoothChartLocalLifting.local_chart_principal` combines this refinement with
local surjectivity of sheafification of the chart diagram's presheaf colimit.
It factors any arrow from an ordinary open into a chart realization through a
target chart locally. It does not require the arrow to land in one chart
globally.

`SmoothChartReconstruction` derives local coordinate data for the reconstructed
point function from these factorizations. Descent recovers the original arrow
at all stages. `ChartFamily.contMDiff_of_localMap` proves actual Mathlib
smoothness from the coordinate data, deriving continuity as well. Thus the
all-stage inverse law uses local factorization and sheaf descent, rather than
point detection.

The same equivalence is available for arbitrary covering `ChartFamily`
choices. `reconstruct_comparison`, `reconstruct_atlas`, `reconstruct_id`, and
`reconstruct_comp` prove compatibility with the existing comparisons and
categorical laws. `homEquiv_principal` identifies the correspondence under
`principalIso`; `principalIso_naturality` proves agreement with the existing
algebraic pullback maps. These are ordinary Lean APIs. Source syntax remains
opt-in.

`Examples.ManifoldFullFaithfulness` exercises the inverse on arbitrary arrows,
distinguishes constant maps, and reuses the split target atlas for which
`no_whole_target_chart` excludes a global target-chart choice. The disjoint
union of two zero-dimensional Euclidean spaces supplies an actual Mathlib
manifold with no global Euclidean chart, with a checked proof of that fact.
Its map to the line also tests different dimensions. Further cases recover the
nonextendable reciprocal, compare principal and atlas inverses, check
composition, and cover empty sources and the absence of an arrow from a point
to the empty manifold.

Kock's [*Synthetic Differential Geometry*, III.3 and III.8, pp. 141 and 176–177](https://users-math.au.dk/kock/sdg99.pdf)
uses Hausdorff, countably based manifolds. Theorem 8.4 obtains full faithfulness
through the smooth-function algebra functor and Yoneda, and also establishes
the axioms of a fully well-adapted model. The construction here instead proves
full faithfulness of the existing atlas colimit without those global manifold
restrictions. It does not prove transverse-limit preservation or the remaining
well-adaptedness axioms.

General Weil KL, transverse-limit preservation, full well-adaptedness, and
higher/cohesive compatibility remain separate unproved claims. The next
decision task is the targeted Myers/higher/cohesive requirements assessment
in #96. This result does not complete #36.
