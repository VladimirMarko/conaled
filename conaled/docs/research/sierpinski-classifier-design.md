# Relative Sierpiński classifier: construction and statement review

Research for [#139](https://github.com/VladimirMarko/conaled/issues/139),
2026-10-25. The construction below is implemented in
`SquareKit/SierpinskiClassifier.lean` and its internal modules. Independent
review and the full fresh validation are recorded separately.
It refines [the classifier assessment](classifier-and-expressive-stress-tests.md).
The inspected interface base is `51ecb90e966a981f76cb921102ddcdedc32ab1ae`.
#138 was accepted and closed after the coordinator validated all 575 modules
and the exhaustive audit at `6b8abd7`; the local base has the same tree.

## Primary evidence and conventions

Johnstone, *Topos Theory* (1977), §4.3, p. 117, example (iii), uses the
walking arrow. Its contravariant diagrams are arrows D₁→D₀; flatness requires
D₀ terminal and the arrow monic. Their category is equivalent to the poset of
subterminals. The covariant functor topos B² is the relative Sierpiński topos.
Example (iv) uses finite sets to construct the object classifier, whose generic
object is the inclusion of finite sets into sets.
[Primary text, p. 117](https://pages.jh.edu/rrynasi1/NewFoundations4Math/Literature/Toposes/Johnstone1977ToposTheory.pdf).

Vickers, *Arithmetic universes and classifying toposes*, §5.2, Proposition 29,
pp. 21–23, reconstructs a unique geometric 2-cell from a model homomorphism.
The proof first treats isomorphisms, then arbitrary homomorphisms using a
cocomma topos. The displayed direction is θ:f₀*NG→f₁*NG and α:f₀→f₁.
Theorems 30–31 give pseudopullback stability/local representability. His
ambient elementary toposes have natural numbers objects; relative classifiers
use bounded toposes. These results support the categorical contract, not a
Lean proof or an unrestricted universe claim.
[Author's preprint](https://sjvickers.github.io/AUClTop.pdf#page=21).

The construction below is explicit. The checked equivalence takes
F = `Sheaf J (Type (max u v))`, for an arbitrary site in universes u,v,
and any base B with finite limits and a strict initial object, with geometric
morphism h:F→B. This is an arbitrary represented sheaf source theorem; it does
not silently quantify over arbitrary elementary toposes or larger value universes. Use S_B=Arrow B, with objects written X→Y. The structural
map π:S_B→B has inverse image Δ:X↦(X→X) and direct image domain evaluation.
Its generic subterminal is G=(0→1) with mono G→(1→1).

The checked statement is

```text
GeometricMorphism.Lift h π ≌ MonoOver (1_F) ≌ Subobject (1_F).
```

Use the first equivalence for actual carriers and inclusions. The second is
Mathlib's existing equivalence with the subobject poset. A model is a mono
P→1_F; a model map is a map of its carriers commuting with these monos.
Transformations α:k⇒l mean α*:k*⇒l*, so generic-model evaluation sends α
to α*.app G in the same direction. Normalize the terminal codomain by its
canonical comparison. Opposite geometric-transformation conventions would
require the opposite hom-category.

## Explicit inverse image and right adjoint

For P↪1 in F, define a functor K_P:Arrow F→F by the pushout

```text
K_P(X --a--> Y) = X ⊔_(P×X) (P×Y),
```

whose legs are projection P×X→X and P×a. The first leg is monic because
P is subterminal. Maps between arrows induce maps of these spans and hence
of their pushouts. A model inclusion P→Q induces K_P⇒K_Q by the same
universal property, keeping the X leg fixed. Check the identity and
composition laws on both pushout injections.

There is an explicit right adjoint

```text
R_P(T) = (T → T^P),
```

where the arrow transposes P×T→T. A map K_P(a)→T consists of X→T and
P×Y→T agreeing on P×X. Currying the second map gives precisely a square
from a to R_P(T). Prove this bijection natural in a and T, then construct
the adjunction. This avoids leaving right-adjoint existence as a premise.

The desired classified geometric morphism k_P:F→S_B has

```text
k_P* = Arrow(h*) ⋙ K_P,
k_P*'s right adjoint = R_P ⋙ Arrow(h_*).
```

Pointwise adjunction supplies Arrow(h*)⊣Arrow(h_*). Prove Δ⊣domain
evaluation and its finite-limit preservation separately. Also prove
K_PΔ≅Id and K_P(G)≅P. These identify the over-B comparison and the
actual generic model.

Left exactness is proved in `ArrowPresheaf`, `ArrowPresheafPushout`,
`ArrowPushoutChange` and `ArrowSheaf`. For a subterminal presheaf P, at each
stage U the interpretation selects Y(U) if P(U) is inhabited and X(U)
otherwise. A restriction crossing from false to true applies the original
arrow X→Y. Thus it is a functor, not an independent choice of stalks.
Each evaluation is naturally domain or codomain evaluation, so the functor
preserves finite limits. Its explicitly proved pushout property identifies
it with K_P. This external classical case distinction does not assert that P
is complemented as a presheaf or sheaf.

For a sheaf P, include the input arrow into presheaves, apply that pushout,
and sheafify. Inclusion preserves limits and sheafification preserves finite
limits. `ArrowPushout.changeCategory` identifies the result with the actual
pushout in sheaves, using product comparisons and preservation of pushouts;
the sheafification counit identifies the parameter with P. Sectionwise
subsingletonness follows from P→1 being mono. No left-exactness or classifier
conclusion is supplied as a caller hypothesis.

## Fullness, faithfulness and the inverse comparisons

Every arrow a:X→Y in Arrow B has the pointwise pushout presentation

```text
       G×ΔX  ----->  G×ΔY
         |             |
         v             v
        ΔX  --------->  a.
```

At the domain this is 0←0→X; at the codomain it is X←X→Y.
For any lift k, k* preserves this pushout and products. Its specified
comparison k*Δ≅h* therefore yields a natural isomorphism
k*≅Arrow(h*)⋙K_(k*G). Establish compatibility with the comparison over B.
Together with K_P(G)≅P this gives the equivalence's two inverse comparisons.

This presentation also proves the hom correspondence. For an over-B
transformation α, its components on ΔX are fixed by the two comparisons;
its component on G is the model map. Naturality with product projections
fixes its components on G×ΔX, and the pushout fixes α at every a. Conversely
a model map builds those components and a transformation by the pushout
property. Prove inverse hom formulas, then identity/composition. An object
bijection or a uniqueness theorem only for natural isomorphisms leaves the
acceptance theorem incomplete.

Thinness is a *derived property of this model category*. Maps between two
subterminals are unique when they exist, but need not be invertible. It is
legitimate to use Mathlib's `MonoOver.isThin` for final equalities of such
maps. Do not impose thinness on `GeometricMorphism`, `Lift`, a general
classifier interface, or arbitrary model categories. In Lean, proof
irrelevance for law fields is harmless; replacing mathematical hom data by
propositions or a discrete category is a separate restriction.

## Source substitution and ambient base change

For f:F′→F, define reindexing on models by f* and the terminal comparison.
The equivalence should have a natural comparison

```text
interpret_h ⋙ pullModel_f ≅ precompose_f ⋙ interpret_(h∘f).
```

On a lift this is the canonical identification f*(k*G)≅(k∘f)*G.
Require its unit and composition diagrams, with associators and terminal
comparisons explicit. For β:f⇒g, evaluation at the actual model carrier
supplies f*P→g*P. Check the transformation square as well as reindexing
objects. Under this convention source 1-cells reverse direction on
categories of lifts; inverse-image 2-cells keep their direction.

For b:B′→B define S_b:S_B′→S_B by Arrow(b*) and Arrow(b_*), with the
pointwise adjunction. Its structural comparison is Arrow(b*)Δ≅Δb*.
Preservation of initial and terminal objects identifies S_b*G_B≅G_B′.
Prove that

```text
S_B′ ----S_b----> S_B
 |                 |
π_B′              π_B
 |                 |
 v                 v
B′ ------b-------> B
```

is a pseudopullback. For fixed source F and h:F→B′ the two lift categories
classify the same subterminals of F. To obtain the *full* pseudopullback,
assemble this into an equivalence with cones whose base leg F→B′ varies,
retaining compatible transformations on that leg and the upstairs leg.
Fixed-leg equivalences alone are insufficient. Check identity/composition
of b, compatibility with generic models, and the mixed square with source
substitution by tracing the same carrier maps through their comparisons.

## Checked examples

Over Set, false P=0 gives K₀≅domain evaluation; true P=1 gives
K₁≅codomain evaluation. Their right adjoints are respectively
T↦(T→1) and T↦(T→T). The noninvertible transformation K₀⇒K₁ has component
a:X→Y equal to a itself. On G it is the empty-to-singleton map. A reverse
transformation would give a singleton-to-empty function at G, so none exists.
This checks the orientation independently of the generic equivalence proof.

`Examples/SierpinskiPoints.lean` checks generic interpretation at both points, the
component formula, its naturality square, the nonexistence of the reverse,
and noninvertibility. `SierpinskiSourceCoherence` and `SierpinskiBaseCoherence` prove source and base
identity, composition, transformation compatibility, and mixed comparison
for actual lifts and models. `Examples/SierpinskiLocal.lean` computes a
restriction from a false stage to a true stage, taking domain witness 3 to
codomain witness 4, and connects this to the categorical pushout comparison.
`Examples/SierpinskiSheaf.lean` specializes the classifier and full cone
equivalence to the existing finite diamond site.
The discrete category on these models and its maximal groupoid both lose
the false→true morphism. Neither is equivalent to this model category.

This example cannot test two different parallel model maps. The next theory
should have one unconstrained sort: its Set models are sets and all
functions. A singleton-to-two-element pair of distinct maps would expose
accidental thinness. Johnstone's next object-classifier example supplies the
literature starting point. It is outside #139 and makes no claim about higher
identity, codata, or classifiers for every theory.

## Local reuse and implementation boundaries

The following names were inspected at the pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. These APIs were subsequently used in the checked implementation.

| Need | Existing source/API |
|---|---|
| Arrow objects, squares and functors | `CategoryTheory/Comma/Arrow.lean`: `Arrow.mk`, `Arrow.homMk`, `Arrow.isoMk`, `Arrow.leftFunc`, `Arrow.rightFunc`, `Arrow.leftToRight`, `Functor.mapArrow` |
| Actual subterminal carriers | `CategoryTheory/Subobject/MonoOver.lean`: `MonoOver`, `MonoOver.homMk`, `MonoOver.isoMk`, `MonoOver.isThin` |
| Poset comparison | `CategoryTheory/Subobject/Basic.lean`: `Subobject.equivMonoOver` |
| Pointwise finite limits | `CategoryTheory/Limits/Comma.lean`, `Limits/FunctorCategory/Basic.lean`, `Limits/Preserves/Finite.lean` |
| Exponential adjunction | `CategoryTheory/Monoidal/Closed/Basic.lean` and cartesian monoidal instances |
| Pushout exactness | `CategoryTheory/Adhesive/Basic.lean`: `Adhesive`, `IsPushout.IsVanKampen`; `Sites/LeftExact.lean`: `SheafOfTypes.adhesive` |

The implementation reuses #138's `GeometricMorphism` and
`GeometricMorphism.Lift` directly. They retain both adjoints, finite-limit preservation, arbitrary
inverse-image transformations and invertible comparisons; they impose no
discreteness. `Lift.precomp` and `Lift.precompFunctor` in
`SliceSourceChange.lean` are already general in the classifier projection.
Their current import path passes through slice-specific material; move only
that generic portion if reuse warrants it. Do not duplicate it in a new
Sierpiński namespace.

The partition, section and complementary-predicate equivalences in #138
are theory-specific. Their model source-change and slice pseudopullback
theorems provide comparison patterns, not ready-made proofs for Arrow B.
In particular, do not transfer their discrete-model conclusion or merely
rename a slice classifier as the Sierpiński classifier.

The implementation separates arrow operations, adjunctions, exactness,
transport, presentation, reconstruction, and coherence. In particular
`ArrowTransformation.naturalTransformation_ext` treats different base legs;
only the fixed-base specialization derives thinness. `coneModels` retains
both the geometric base-map component and the model-map component, and its
fullness constructs their upstairs transformation. `pseudopullback` uses the
actual pointwise arrow base-change functor and canonical cone comparison.

Literature validation: the initial research inspected Vickers's primary PDF
and the primary-text search extraction of Johnstone p. 117. Direct opening of
the latter PDF exceeded the web tool's size limit, and direct download
returned HTTP 403. The page-specific extraction supplied examples (iii) and
(iv); its typography was not visually verified. Network access during this
implementation is unavailable, so these prior findings remain attributed.
Local proof validation and review records are kept with the candidate handoff.
