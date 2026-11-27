# Arrow sheafification before groupoid completion

[Issue #729](https://github.com/VladimirMarko/conaled/issues/729) selects a checked
entry point from constant group arrows to the existing principal-bundle
completion. The construction works for any `X : TopCat.{0}` and `G : Type 0`
with a group structure. The discrete two-point application proves that its
input hom presheaves are not sheaves, that correction changes arrows, and that
nontrivial isotropy survives completion. General internal groupoids and
arbitrary groupoid-valued pseudofunctors remain supported directions with
separate proof obligations below.

The three independent design assessments and their selection rationale are in
[the synthesis](arrow-sheafification-design/synthesis.md). Their initial probes
are assessment evidence; the integrated modules below are the retained formal
results.

## Construction and checked consumer

[`LocallyConstantGroup`](../../SquareKit/LocallyConstantGroup.lean) lifts the
existing locally constant sheaf to `Sheaf (site X) GrpCat`. Restrictions are
pointwise group homomorphisms. `constantIso_unit` identifies the actual constant
presheaf unit with Mathlib's sheafification unit followed by the existing
`constantIso`; this is not an arbitrary isomorphism of the resulting objects.

[`ArrowSheafification`](../../SquareKit/ArrowSheafification.lean) supplies a
second input: `normalized`, the group presheaf of globally constant functions
on each open. It has a unique empty section without choosing a label there.
Its `inclusion` into locally constant functions is locally injective and locally
surjective. `normalizedIso_unit` proves the actual unit comparison with its
sheafification. Thus both inputs have the same corrected arrow sheaf, while
their original restriction and matching behavior differ.

`Completion.action` is the trivial action of that group sheaf on the terminal
locally constant `PUnit` sheaf. The existing `SheafGroupoidAction.operations`
provides the represented groupoid, including all operations and laws. For each
open `U`, `point` represents its unique object via `sectionEquiv`, and
`loopEquiv` identifies **all** automorphisms at that object with locally constant
group labels. `loop_mul` uses the order `g ≫ h = h * g`, matching Mathlib's
`SingleObj` and the existing action interface.

`rawUnit` and `normalizedUnit` are functors from the actual one-object input
groupoids into this represented fiber. `completedUnit` composes `rawUnit` with
`SheafGroupoid.Bundle.regularFunctor`, the unit of the general completion from
#727. `loop_restriction` proves the arrow map's substitution equation for every
open inclusion. `completion_restriction` gives the same square for the
subsequent regular-bundle functor. The existing regular-functor theorem also
covers arbitrary sheaf-parameter maps, beyond represented opens.

The already-sheaf input is the locally constant group itself.
`LocallyConstantGroup.alreadySheaf` is `isoSheafify`, whose forward map is the
actual adjunction unit; `Completion.recovered_loop` proves that following this
unit by its inverse recovers each actual completed arrow. Sheaf-valued arrows
do not assert effective object descent. The latter is the separate
principal-bundle construction.

[`Examples.ArrowSheafification`](../../Examples/ArrowSheafification.lean) uses
`Equiv.Perm Bool` on the discrete Boolean space. Its controls establish:

- `raw_not_sheaf` and `normalized_not_sheaf` refute the actual sheaf predicate.
- `raw_not_injective_empty` shows local identification of distinct raw labels.
  The raw presheaf restricts by identity even to the empty open, so differing
  labels on disjoint singleton opens are **not** a matching raw family.
- `singleton_cover`, `singleton_overlap`, `local_compatible` and
  `no_normalized_amalgamation` exhibit a covering matching family in the
  normalized input with no global amalgamation. `varying_restricts` supplies
  its corrected gluing.
- `completed_distinct` retains the original nonidentity permutation at the
  inhabited top open. `completed_new_arrow` retains the newly glued, varying
  automorphism outside the image of every raw label. Both use
  `completed_loop_injective`, derived from `regularFullyFaithful` and
  `loopEquiv`.

The unit is locally bijective on these arrow presheaves, not pointwise fully
faithful. Newly glued arrows and locally identified arrows occur before
completion adds objects by effective descent. Replacing groupoids by their
sets of isomorphism classes would erase the checked automorphism distinction.

## Existing interfaces and the two input contracts

The inspected Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. `HasSheafify` includes finite-limit
preservation, and `Sites/LeftExact.lean` supplies the standard Type-valued
instance at `Type (max u v)` for a site on `C : Type u` with `Category.{v} C`.
The current `SheafGroupoid.Operations` uses that same section universe. Its
parameter sheaves and generalized objects live in the corresponding larger
object universe. This assessment does not resize arbitrary pseudofunctors or
claim sheafification at every unrelated universe without hypotheses.

An internal presheaf groupoid has object and arrow presheaves, source, target,
identity, inverse, and composition on the composable-pair pullback. Its maps
are internal functors; its 2-cells are internal natural transformations with
actual arrow components. Left-exact sheafification can transport this diagram,
but composition requires the comparison
`a(A ×_O A) ≅ a(A) ×_a(O) a(A)` and the transported laws. These have not been
implemented for general inputs here. If `O` is already a sheaf this is arrow
correction over fixed objects. Otherwise sheafifying `O` also adds object
sections before effective groupoid descent.

For a general groupoid-valued pseudofunctor, Mathlib's
`Sites/Descent/IsPrestack.lean` already supplies `presheafHom` on slices,
`presheafHomObjHomEquiv` and restriction comparisons
`overMapCompPresheafHomIso`. `IsPrestack J` means these hom presheaves are
sheaves; an arbitrary pseudofunctor is not automatically a prestack. Homwise
sheafification keeps objects and must assemble composition, inverses and
restriction coherence. It does not automatically provide the global object
and arrow sheaves expected by `Operations`.

The mathematical alternatives are supported by the Stacks Project's
[stackification construction, Lemma 8.8.1](https://stacks.math.columbia.edu/tag/02ZM),
which describes homwise correction and a split object/arrow route. The latter
requires a splitting comparison; it is not a free identification of arbitrary
pseudofunctors with internal presentations. Its Lemma 8.8.3 states the full
mapping-category comparison. These are external mathematical references, not
Lean results delivered by this assessment.

## Full mapping-category contract and site boundary

Fix one site and explicit universes. For a groupoid-valued pseudofunctor `F`,
the intended homwise unit `p : F ⟶ P` and effective-descent unit `s : P ⟶ S`
should induce, for every stack `T`, equivalences

```text
StrongTrans(S,T) ≌ StrongTrans(P,T) ≌ StrongTrans(F,T).
```

Morphisms here are modifications. The forward functors must be actual
precomposition by `s` and `p`, with their composite compared to precomposition
by the actual composite unit. Require the induced bijection on modifications
for every pair of transformations, extension/restriction isomorphisms, and
compatibility with identities, composition and target postcomposition. On
slice hom presheaves the original unit must be locally bijective and identify
their sheafifications with the corrected homs. Global full faithfulness is
false in the checked example. The homwise intermediate reflection can target
all prestacks because it preserves objects. Sheafifying the internal object
presheaf does not have that same target class: an arbitrary prestack need not
have a sheaf of objects.

The groupoid-valued existence theorem is also stated in the Stacks Project's
[Section 8.9](https://stacks.math.columbia.edu/tag/02ZO). The preceding formula
is the contract for the successors, not a claim that arbitrary same-site
stackification has been formalized here.

What is already checked is `SheafGroupoid.Bundle.universalEquivalence`, with
forward functor `StackLocalGeneration.restriction (Bundle.unit G) T`, and
`modificationEquiv`. Its base is **the category of sheaf parameters**, with
`SheafCover.topology`. Its target is a stack on that site in
`Cat.{max u v, max (u+1) (v+1)}`. It applies to our `Completion.operations`
without extra hypotheses. The input/output arrow comparison in this assessment
uses that actual `Bundle.unit` component.

The original open-cover site is different. `sectionParameter` and
`sectionEquiv` prove representation and substitution, not a universal
change-of-site theorem. In `SheafCover.topology` a covering sieve contains one
locally surjective arrow. Its empty sieve never covers. The original open site
has an empty cover of the empty open; its disjoint singleton inclusions jointly
cover the two-point space. On sheaf parameters, the sieve generated by those
two inclusions contains no locally surjective arrow: each member factors
through one singleton. The coproduct epimorphism does not factor through
either singleton and is not a member of that generated sieve. Accordingly, a
comparison must account for coproduct and empty descent or use direct
original-site descent. The joint-cover argument is mathematical site analysis;
the formal empty-sieve control is retained in the example module.

## Supported inputs and remaining owners

| Input or obligation | Delivered result or concrete owner |
|---|---|
| Constant one-object group on a small topological open site | Actual arrow unit, locally constant correction, represented fiber and principal-bundle composite; checked here. |
| Globally constant functions presheaf on the same site | Locally bijective inclusion and actual sheafification comparison; checked here. |
| Already-sheaf locally constant group arrows | Actual-unit recovery and preservation of completed arrows; checked here. |
| Arbitrary represented sheaf groupoid | Existing #727 completion unchanged on its sheaf-parameter site. |
| General internal presheaf groupoid | [#730](https://github.com/VladimirMarko/conaled/issues/730): finite-limit transport, maps/2-cells, actual units and recovery, including object sheafification. |
| General groupoid-valued pseudofunctor | [#731](https://github.com/VladimirMarko/conaled/issues/731): homwise slice sheafification, coherence and full reflection into prestacks, with a consumer beyond the fixed internal presentation. |
| Original-site effective descent and composite universal property | [#732](https://github.com/VladimirMarko/conaled/issues/732): direct construction or proved site comparison, including empty/joint descent and the full mapping-category contract. |
| Genuinely higher completion | #721; arrow correction does not discharge higher cells or hyperdescent. |

The three successors are under #666/#647. They do not impose new prerequisites
on #728, #700/#701, #654 or the geometric clients. #722's balanced bibundle
product and #724's internal properness/Myers comparison are separate work.

Statement review checked the raw/normalized distinction, actual-unit equations,
multiplication order, all-loop recovery, nonvacuous isotropy at an inhabited
open, and the exact site of every universal claim. Focused builds check the
new modules; completion requires the immutable candidate's integrated build,
exhaustive audit and independent Standards/Spec acceptance.
