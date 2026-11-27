# Alternatives and generality assessment of #729

Recommendation: use a one-object internal groupoid from a group presheaf as the bounded checked case, with its arrow sheaf explicitly identified with locally constant labels, and feed that represented sheaf groupoid to #727. Retain homwise prestackification as the intended general entry point for arbitrary groupoid-valued pseudofunctors. Do not identify the two input contracts or claim the original-site universal property from #727's theorem without an additional site comparison.

This is an independent initial assessment. I read the shared brief, saved issue, relevant repository guidance, current sources, pinned Mathlib, and the primary sources below. I did not read other assessment reports or communicate conclusions to the other assessors. No target files or issues were changed. The only new files are this report and isolated probes under `/tmp/conaled-729`.

## Evidence supporting the bounded represented route

`SquareKit/LocallyConstantSheaf.lean` already constructs the relevant arrow sheaf on any small topological space: `data_isSheaf`, the actual constant-label `unit`, local injectivity and local surjectivity instances, and `constantIso`. The latter proves identification with Mathlib sheafification using local bijectivity. This removes any need to assume that locally constant labels happen to model sheafification. `SquareKit/SmoothLocallyConstantGroup.lean` independently supplies an established group-valued constant-sheaf pattern, including group homomorphisms and unit local comparisons, although its smooth site is unnecessary for this bounded case.

The one-object groupoid preserves a useful distinction: the arrow correction can change labels while the object presheaf remains terminal. Nontrivial isotropy remains visible. The existing action-on-terminal construction can provide `SheafGroupoid.Operations`; the general completion is `SheafGroupoid.Bundle`, not the older action-specific `SheafGroupoidCompletion` namespace. The action-specific completion can then serve as the already-established output comparison using `SheafGroupoidStackificationRecovery.lean`.

For general internal groupoids, Mathlib's `HasSheafify` includes finite-limit preservation, whereas `HasWeakSheafify` promises only the adjunction (`Sites/Sheafification.lean:35–81`). Thus objectwise sheafification can carry source, target, identity, inverse and composition through a proved pullback comparison. One must transport composition from `a(P₁ ×[P₀] P₁)` to `aP₁ ×[aP₀] aP₁`, then transport its laws. Calling that construction merely application of a functor conceals this comparison. It also sheafifies the object presheaf, unlike homwise prestackification, which keeps each fiber's objects.

The existing `SheafGroupoidSections.lean:17–33` supplies the useful representation bridge: maps from `sectionParameter J U = a(uliftYoneda U)` correspond to sections at `U`, naturally in restrictions. No subcanonicality hypothesis is necessary. Its `sectionArrowEquiv` and `SectionArrow.restrict_map` retain endpoints and actual arrows. This is substantial reuse, although it is not yet a theorem transferring the completion's mapping-category universal property between sites.

## Two established pitfalls

### Raw constant presheaves and empty overlaps

For `P(U) = G` on every open, including the empty open, all restriction maps are identities. Distinct labels on disjoint singleton opens are therefore *not* a compatible family in this presheaf: their restrictions to the empty overlap remain distinct. A statement claiming those original labels form a matching family is false.

The raw constant example remains useful. Its empty-open sections are locally identified by sheafification, and its image at the disconnected nonempty top open misses genuinely new locally varying labels. These are two different phenomena. Once the empty-open labels are identified, differing singleton labels can glue.

Executed probe `AlternativeProbe.lean` imports the public `LocallyConstantSheaf.unit` and proves:

- A locally constant Boolean function on the discrete two-point top open is outside the image of that unit.
- The distinct labels `true` and `false` have equal images at the empty open.
- An equality after any raw constant-presheaf restriction is already equality of labels, so empty-overlap compatibility cannot be treated as vacuous there.

The probe uses Boolean labels as a set-valued control. It does not itself package a group, prove a non-sheaf proposition, or construct a groupoid. A two-element group can retain these witnesses in the implementation. If the intended demonstration requires a compatible original family that fails to glue on a nonempty open, instead use the normalized presheaf with terminal value at the empty open and value `G` elsewhere. An alternative encoding is globally constant functions on each open. Prove its unit into locally constant functions locally bijective. This extra control is worthwhile only if that stronger failure claim is part of the report.

### The two sites are different

The original example lives on `(Opens X, Opens.grothendieckTopology X)`. #727's universal theorem instead quantifies over stacks on `(Sheaf J Type, SheafCover.topology)`; see `SheafGroupoidBundlePresentation.lean:61–74`.

`SheafContextTopology.lean:16–18` defines a covering sieve to contain a **single** locally surjective map. In particular an empty sieve is never covering, even at an initial sheaf. `AlternativeSiteProbe.lean` checks this directly for every sheaf parameter. The ordinary open-cover topology has the empty covering family at the empty open. Also, a covering family of proper disjoint subopens need not give a sieve containing any single locally surjective member after passing to sheaf parameters.

Consequently this topology must not silently be called the usual topology of all jointly epimorphic families. Nor can `sectionParameter` plus sectionwise equivalences alone establish equivalence of arbitrary stack targets or their mapping categories. A route through sheaf parameters must state the additional comparison theorem and its target hypotheses. Preservation of coproduct descent and the empty cover are discriminating obligations. The bounded case can be checked with its actual sectionwise unit and #727 completion while explicitly leaving this universal comparison open.

## Comparison of the intended inputs

| Input | Construction and benefit | Obligation before applying #727 |
|---|---|---|
| One-object internal groupoid from a small group presheaf | Sheafify its group arrows; object sheaf is terminal; retain multiplication, inverse and automorphisms | Build the represented operations, actual section unit, and substitution comparison. The locally constant model is already available for the underlying set. |
| Internal groupoid in `Cᵒᵖ ⥤ Type (max u v)` | Apply left-exact sheafification to object and arrow presheaves, including composable pairs | Construct the finite-limit transport and laws. State that strict object gluing can also occur at this intermediate stage. |
| General pseudofunctor with groupoid fibers | Sheafify each `F.presheafHom x y` on `Over U`; preserve objects and assemble composition, inverses and coherent restriction | No automatic pair of global object/arrow sheaves has been supplied. Either add a strictification/internal presentation theorem with universe control, or complete directly by descent data. |
| Pseudofunctor already satisfying `IsPrestack J` | Hom correction should recover its original homs by actual unit isomorphisms | Object descent can still add objects; represented data remain a separate input requirement for #727. |
| Already represented sheaf groupoid | Reuse #727 unchanged | Its universal theorem already lives on the sheaf-parameter singleton-cover site. Original-site claims still need the site bridge. |

Mathlib's terminology is explicit in `Sites/Descent/IsPrestack.lean`: `IsPrestack J` means the hom presheaves on slices are sheaves. A general groupoid-valued pseudofunctor is not automatically a prestack in this sense. The same file already provides `presheafHom`, `presheafHomObjHomEquiv`, and `overMapCompPresheafHomIso`. These are the reusable beginning of route B; reimplementing a strict-only hom presheaf would discard existing coherence work.

Mathematically, route A need not be an expressiveness ceiling: after suitable splitting, groupoid fibrations admit strict presheaf presentations. But that theorem includes recovery comparisons and size conditions; it is not provided by calling the source a pseudofunctor. The Stacks Project's [stackification proof](https://stacks.math.columbia.edu/tag/02ZM), Lemma 8.8.1, explicitly offers both homwise and object/arrow sheafification routes for fibred categories over a site. The latter first replaces the fibration by a split one and still requires effective descent afterward. Its Lemma 8.8.3 gives equivalence of full mapping categories into any stack. These are paper-level support, not checked repository theorems.

## Full universal contract to preserve

Fix one base site `(C,J)` and universes before stating the contract. Let `F` be a pseudofunctor with groupoid fibers, `p : F ⟶ P` the hom-sheafification unit, and `s : P ⟶ S` its object-descent completion. For every stack `T` of the declared target universes, require equivalences

`StrongTrans(S,T) ≌ StrongTrans(P,T) ≌ StrongTrans(F,T)`.

Each forward functor must be actual precomposition, respectively by `s` and `p`. The composite must be naturally isomorphic to precomposition by the actual composite unit. Morphisms in these categories are modifications; full faithfulness must give their bijective recovery, with compatibility with identities, composition, and target postcomposition. State recovery isomorphisms for extended transformations, rather than merely an existence assertion for some extension.

The local hom comparison is an isomorphism between the sheafification of `F.presheafHom x y` and the hom sheaf between the images of `x,y`, commuting with the original unit. It induces local injectivity and local surjectivity of the original arrow map. Global full faithfulness of `p` is false in the chosen control: it identifies empty-open labels and fails fullness at the disconnected top open. The completion unit `s` can be fully faithful after hom sheafification.

The homwise route can derive the second equivalence already for prestack targets, because no new objects are added. The internal-object/arrow route sheafifies objects too, so an arbitrary prestack target need not suffice to extend all maps through it; stack targets supply the relevant object descent. Do not conflate these two intermediate universal properties.

If `S` is instead #727's bundle pseudofunctor on sheaf parameters, the displayed formula is not type-correct until both source and target are put on that same base or a proved change-of-site equivalence is inserted. Record the exact resulting target class. This is a missing theorem, not a demand that the bounded implementation prove arbitrary stackification.

## Universes and smallest useful next steps

The represented interface fixes object and arrow sections in `Type (max u v)` for `C : Type u` and `Category.{v} C`; its generalized objects occupy `Type (max (u+1) (v+1))`. `LocallyConstantSheaf` is currently `TopCat.{0}` and `Type 0`, which fits the proposed small open site. This bounded restriction should be named. Arbitrary pseudofunctors can have object and hom universes different from those of `C`; neither the represented interface nor available sheafification instances justify silently resizing them. Mathlib `LeftExact.lean:308–314` exposes the cover-smallness hypothesis behind the concrete sheafification instance and gives the standard Type `(max u v)` instance.

Recommended implementation sequence:

1. Check the two-point arrow correction and its actual unit, including the empty-open identification, surviving nontrivial top-open labels, and new nonconstant top-open arrow. Add the normalized-presheaf nonempty gluing control if the report claims that stronger failure.
2. Package the group sheaf and represented one-object groupoid. Connect its sections through `sectionArrowEquiv`, construct the regular-bundle composite unit, and prove its restriction square. Recover an already-sheaf group-arrow input with the actual unit comparison.
3. State #727's checked mapping-category theorem on its exact base. Specify the intended original-site composite contract separately.
4. Give named successor ownership to finite-limit internal-groupoid transport, homwise pseudofunctor prestackification with its full mapping-category equivalence, and the original-site/sheaf-parameter comparison including coproduct and empty descent. The strictification/representation route is an alternative to direct general descent, with an explicit recovery contract.

Both probes passed `direnv exec . lake env lean <absolute-probe-path>` against the current checkout and pinned Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. They are isolated checks, not integrated build or exhaustive audit evidence. No general sheafification-of-groupoids construction, pseudofunctor universal equivalence, or site comparison was proved in this assessment. The source inventory is inspected code; proposed constructions above remain proposed mathematics until implemented and validated.
