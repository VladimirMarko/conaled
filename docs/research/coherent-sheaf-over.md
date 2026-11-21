# Coherent decoding for sheaves over a context

`SquareKit.CoherentSheafOver.codeDisplayClassification` constructs a category
equivalence from coherent local section diagrams to sheaf displays over a
represented context. The decoder derives sheafness, retains the projection and
all morphisms, and recovers the original display over the same context. The
construction uses a cover-dense subsite. Subcanonicity alone does not justify
recovery from the represented contexts used by the older coding example.

The implementation is in
[CoherentSheafOver](../../SquareKit/Internal/CoherentSheafOver.lean), with checked
clients in [Examples.CoherentSheafOver](../../Examples/CoherentSheafOver.lean).
It addresses [#652](https://github.com/VladimirMarko/conaled/issues/652) within
the [classification programme](https://github.com/VladimirMarko/conaled/issues/647).

## Base, values and local membership

In `Examples/CoherentRepresentableCoding.lean`, `J` is a topology on
`D = Context.{r} C`, where `C : Type u`, `[Category.{v} C]`, and
`Context.{r} C = Cᵒᵖ ⥤ Type (max r v)`. Its fiber at `Γ : D` is
`Sheaf (J.over Γ) A`. It is not the element-site sheaf category of `Γ` for a
topology on `C`. The new construction fixes the value category to `Type w`.
It does not claim a classification for every value category `A` in that example.

The general interface takes `B : Type u`, `[Category.{v} B]`, `D : Type a`,
`[Category.{b} D]`, and a fully faithful `G : B ⥤ D`. For each context `Γ`, set

```
LΓ = CostructuredArrow G Γ
iΓ : LΓ ⥤ Over Γ
KΓ = iΓ.inducedTopology (J.over Γ).
```

Objects of `LΓ` are actual arrows `G(I) → Γ`, and its maps are the commuting
triangles between them. For the original example, use `G = representables`.
The checked equality `representables_eq_uliftYoneda` supplies full faithfulness
from Mathlib without changing the universe-lifted representables.

For any site `(B, K)`, an object of `Code K` consists of an ordinary functor
`A : Arrow Bᵒᵖ ⥤ Type w` that sends restriction squares with invertible right
edge to isomorphisms. Its additional membership condition is local: for every
root `X : B`, the presheaf `rootView X ⋙ A` on `(Over X)ᵒᵖ` is a sheaf for
`K.over X`. Maps are all natural transformations between these diagrams.
Neither the assembled presheaf's sheafness nor a recovery equivalence is a
field of this contract. `LocalCode G J Γ` applies this definition to `KΓ`.

The construction requires `iΓ.IsCoverDense (J.over Γ)`: every object of the
slice site is covered by represented domains. The comparison lemma also needs
limits of shape `StructuredArrow X iΓ.op` in `Type w`, for every `X : (Over Γ)ᵒᵖ`.
These size conditions are explicit instance arguments; `w` is independent of
the base object and morphism universes. The display equivalence uses values
`Type b`, matching the hom sets of `D` and `yoneda.obj Γ`. The finite-base client
discharges the limit conditions at `Type 0`.

## Construction and recovery

`isSheaf_of_over` proves the local membership step by lifting a matching family
to the slice over its root and gluing there. `rootRecovery` uses the primitive
coherent restriction squares to identify a local diagram with the restriction
of its identity-view evaluation. Consequently `decoded_isSheaf` establishes
sheafness of that evaluation. `classification` gives the resulting equivalence
with `Sheaf K (Type w)`, including its natural unit and counit.

`sheafOverClassification` composes this equivalence with Mathlib's dense-subsite
comparison. Its target is the actual `Sheaf (J.over Γ) (Type w)` fiber of
`J.pseudofunctorOver`. `decodedLocalRecovery` and `rootedLocalRecovery` identify
its restrictions to represented domains with the input local section diagrams,
on sections and maps. This contract presents local section data on the induced
subsite; it does not define the input category as the image of a decoder or
assume that arbitrary raw pseudococones of sheaf categories already classify.

For a subcanonical `J`, `contextSheaf Γ J` packages `yoneda.obj Γ` as a sheaf.
`elementOverEquivalence` identifies its element site with `Over Γ`, and the
proved covering comparisons transport the site topology. `displayEquivalence`
then reuses `SheafSlice.equivalence`. Its total sections are

```
Σ (f : X ⟶ Γ), Q.obj.obj (op (Over.mk f)).
```

The projection returns `f`; restriction along `g : Y → X` sends this pair to
`(g ≫ f, Q.map (Over.homMk g).op a)`. A morphism acts on the second coordinate
using its component map. `display_sections`, `display_projection`,
`display_restriction` and `display_map` check these formulas. The total sheaf
condition is the gluing proof in `SheafSlice`, not a supplied certificate for a
new total presheaf. The final counit recovers a display over its original
`contextSheaf Γ J`; `display_recovery_projection` checks the projection equation.

Context substitution uses the existing `J.overMapPullback`. `reindex` decodes,
pulls back, and returns the local presentation. Thus substitution normalizes a
code through the derived equivalence. `decodeReindex` compares it with the
original sheaf pullback; `reindexId`, `reindexComp`, `decodeReindex_id` and
`decodeReindex_comp` prove the unit and composition comparisons and their
compatibility with decoding. This is an explicit cost of the interface, not a
claim that substitution computes by definitional equality.

## Coverage is a separate hypothesis

`representedTopology` is a topology on the actual presheaf context category:
a sieve covers precisely when it contains every represented generalized
element. Its topology laws, subcanonicity, and the required cover density of
`iΓ` are proved. The subcanonicity proof constructs the amalgamating natural
transformation by evaluating represented local sections at their generic
elements and checks naturality, amalgamation and uniqueness.

The concrete client uses `C = Discrete PUnit` and the constant Boolean context.
The sieve of componentwise constant maps is covering and excludes the identity.
Its lift is a proper cover in the actual slice site. A display with Boolean
fibers has a fiber-collapse endomorphism; `collapse_not_iso` and
`code_collapse_not_iso` show that the decoder keeps this noninvertible map.
Boolean negation gives a nonidentity restriction, checked against the recovered
display's naturality. `doubleNegationComparison` exercises context substitution.

The omitted-density control keeps the same contexts and uses the bottom
topology, which is subcanonical. The subterminal presheaf supported on constant
maps is a sheaf there. Its pullback along every represented generalized element
is terminal (`localBotIso`), but its value at the identity Boolean context is
empty. `original_sheaves_not_iso` proves that this sheaf is not the terminal
sheaf on the original slice. Thus representable local views alone lose data
when they do not cover. This is different from recovering a coherent diagram
from its identity views, and different again from descent along a covering
sieve.

## Direct presentation and remaining boundaries

For an existing display, `SheafSlice.equivalence` is the direct interface. The
new interface is useful when local section diagrams over represented domains
are the input. It adds a membership check, a dense-subsite comparison, and
normalization during substitution. The dense-subsite inverse uses Mathlib's
noncomputable limit construction. No elaboration-time or runtime improvement
is claimed, and no performance benchmark was conducted for this change.
Existing direct clients and the ordinary-family comparison from #651 remain
unchanged; the shared coherent-family evaluation theorem from #645 is reused.

No sheafification is used in the proved subcanonical construction. For an
arbitrary site, the representable context need not be a sheaf. A display theorem
over its sheafification would need a suitable left exact sheafification and a
proved comparison with the slice site. Generic elements of sheafified
representables cannot be treated as definitionally the old generic elements.
This extension remains with #647. It does not by itself activate
[#654](https://github.com/VladimirMarko/conaled/issues/654): that issue concerns
a concrete existing non-sheaf code decoder that must extend across a specified
noninvertible unit with a specified equation and consumer.

When the old represented domains fail density, the general theorem already
allows another fully faithful cover-dense `G`. Constructing a useful enlarged
generating subsite is a consumer-specific question; the bottom-topology control
shows that its additional information cannot be reconstructed from the old
views. No arbitrary weak-pseudofunctor stack theorem or manifold theorem is
asserted here. General covering descent remains in #657, and the original
manifold programme remains in #640.
