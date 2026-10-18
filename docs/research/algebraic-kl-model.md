# A small algebraic site for the first KL construction (#73)

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
