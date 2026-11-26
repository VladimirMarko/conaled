# Generalizing representable classification

This assessment separates four changes: independent base universes, a general
category of decoded values, coherent restriction of structured data, and descent
on a site. The first two preserve the shape of the existing evaluation argument.
The latter two require additional mathematical structure and different recovery
statements. They have concrete implementations to build on; they do not require
assuming the final classifier comparison as an adapter field.

The implementation follows [#644](https://github.com/VladimirMarko/conaled/issues/644)
from baseline `290a15d8322cbd8f5ffc6186a589f4bfdec5827a`, with Mathlib pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The checked additions are listed below.
Later sections retain the assessment of stronger contracts; proposals there are
not claims that arbitrary pseudofunctors admit classification or that a stack
instance has been proved. The #645 addition below constructs coherent recovery
for category-valued families; #646 below connects positive gluing and torsor descent.

## Checked additions

- [RepresentableClassification](../../SquareKit/Internal/RepresentableClassification.lean)
  accepts `C : Type v` with `Category.{w} C`. Context and family values live in
  `Type (max u w)` so represented homs fit. Codes live in
  `Type (max v (u+1) (w+1))`. This removes the `Type 0` base restriction; it does
  not resize arbitrary large homs into smaller section universes.
  [Universe examples](../../Examples/RepresentableClassificationUniverses.lean)
  include the category `Type 1` and generic recovery with independent universes.
- [PresheafFamilyClassification](../../SquareKit/Internal/PresheafFamilyClassification.lean)
  constructs ordinary-family codes, a universal decoder, local evaluation laws,
  and recovery. The [non-cubical client](../../Examples/NonCubicalClassification.lean)
  uses the one-object category of multiplicative natural numbers, fibers
  `Fin (n+1)`, nonidentity restriction actions, and composed context substitutions.
  Its cardinality control proves that the fibers at 0 and 1 are not equivalent.
- [RepresentableEvaluation](../../SquareKit/Internal/RepresentableEvaluation.lean)
  derives recovery in any target category from local object and arrow equations.
  `Evaluation.categorical_iso` proves equality with the existing Type-valued
  comparison. The [order-category client](../../Examples/CategoryValuedEvaluation.lean)
  has distinct values and an arrow with no reverse arrow. This is categorical
  evaluation recovery; a universal decoder for arbitrary category-valued data
  is not constructed here.
- [CoherentRepresentableCoding](../../SquareKit/Internal/CoherentRepresentableCoding.lean)
  restricts an actual Mathlib pseudofunctor along representables. The result
  retains morphisms, identity/composition isomorphisms and their coherence.
  `coherentCodeRestriction` derives the local coding comparison from composition.
  `System.data_codes` recovers the strict code functor, and `discreteCoherent`
  embeds strict systems into the coherent interface. The
  [sheaf-over client](../../Examples/CoherentRepresentableCoding.lean) specializes
  to Mathlib's actual sheaf categories and pullback functors. This is a coherent
  code construction, not a proved bicategorical classification equivalence.
- [SheafRepresentableClassification](../../SquareKit/Internal/SheafRepresentableClassification.lean)
  transports total-space sheafness through the derived evaluation comparison.
  `decodeSheafIso` recovers the total as a sheaf, and its projection equation
  retains the display over the original context. The
  [client](../../Examples/SheafRepresentableClassification.lean) applies this to
  arbitrary sheaf displays via their fibers. It also proves `codes_not_sheaf`:
  constant lifted Boolean data satisfies the strict restriction laws but its
  codes fail empty-cover descent on the maximal topology.

Both native cubical classifiers keep their selected fillers, decoder definitions,
and computational specialization choices. Existing clients need no new
hypotheses or higher limits. The ordinary-family adapter supplies its decoder
once; recurring clients use coding and recovery directly. A coherent client
supplies an existing pseudofunctor with coherence, and a sheaf display supplies
actual sheafness. Neither obligation is hidden in a final comparison field.
The [cost report](representable-elaboration-costs.md) assesses the Lean encoding
separately; no author-time improvement was measured.

## Coherent family recovery from #645

[CoherentFamilyClassification](../../SquareKit/Internal/CoherentFamilyClassification.lean)
constructs an equivalence for every category E and target category V. A coherent
code is a functor `A : Arrow E ⥤ V` taking squares with invertible target maps to
isomorphisms. An object `x → y` means a local view rooted at x and evaluated at y.
Morphisms are all natural transformations; neither the local family maps nor
maps between codes must be invertible. The input supplies this local diagram
and its restriction law, not a decoder or a final recovery equivalence.

The decoder evaluates A on identity arrows. Coding a family B uses the target
projection, `Arrow.rightFunc ⋙ B`. Decoding a coded family is definitionally B.
For an arbitrary coherent A, the square `(f, id) : f → id_target(f)` supplies the
recovery component. Its image is invertible by the restriction hypothesis;
functoriality proves naturality, and naturality of code morphisms proves recovery
on morphisms. `equivalence` packages the functors, both recovery isomorphisms and
the triangle law. `reindex` acts by `Functor.mapArrow`; `decodeReindex`, its unit
and composition laws, and `recovery_reindex` retain the substitution comparisons.

[RepresentableCoherentRecovery](../../SquareKit/Internal/RepresentableCoherentRecovery.lean)
specializes E to `Γ.Elements`. `families` and `system` package the actual
context-indexed functor categories as a Mathlib pseudofunctor. `decoder` and
`coder` are Mathlib strong transformations; `classificationUnit` and
`classificationCounit` are invertible modifications. Thus the equivalences are
compatible with context substitution, including its identity and composition.

The arrow-diagram contract is an explicit presentation of the local data used
here. `localArrow` sends an actual represented element to its arrow out of the
named root. `localView` extracts its represented family; `localRestrictionIso`
derives its invertible restriction comparison. `code_localView` identifies
coding with the original `system` restriction functor on objects and morphisms.
`localGenericRecovery` compares each represented generic fiber with the decoder;
`genericRecovery` uses the existing `CategoricalEvaluation.iso` argument.
This does not identify arbitrary pseudonatural cones for arbitrary systems with
these diagrams, or assume that restriction to representables always recovers a
system. A general comparison with such a cone presentation remains a possible
extension under [#647](https://github.com/VladimirMarko/conaled/issues/647).

The [checked clients](../../Examples/CoherentFamilyClassification.lean) include:

- A Boolean-valued family on the natural-number order category with a recovery
  comparison that swaps false and true. This coherent diagram is not merely the
  literal target-projection coding of a family.
- A noninvertible collapse morphism to a singleton, retained by categorical
  recovery, and the earlier order-valued family with a noninvertible arrow.
- The dependent `Fin (n+1)` family with successor and double substitutions;
  their composite takes the fiber at 2 to `Fin 6`.
- A source-projection diagram with no recovery isomorphism at the chosen
  noninvertible arrow. It fails the invertible-restriction condition, exposing
  why arbitrary local diagrams are not classified by the theorem.
- Both native cubical families' represented views and exact existing recovery
  comparisons, including the Type-valued specialization of categorical evaluation.

For ordinary families the adapter is `code`, with no recurring decoder proof.
For independently supplied local diagrams, the builder proves functoriality and
invertibility on restriction squares. The generic recovery and substitution
proofs are shared. Selected cubical fillers remain governed by their existing
native preservation theorems; this change neither reconstructs them from an
unstructured family nor replaces the native computational specializations.
All new definitions and examples elaborate at the existing default budgets.
No comparative timing, allocation or author-productivity measurement is claimed;
[#648](https://github.com/VladimirMarko/conaled/issues/648) retains the four-client
budget experiment. The generic target V is an ordinary category, so choosing
V = Cat does not by itself provide a theorem for pseudofunctor-valued families.

Mathlib's Grothendieck construction supplies a fibred category from a
contravariant Cat-valued pseudofunctor. It is useful when the input is already
such a fibration. Here the arrow-diagram presentation exposes the concrete
restriction squares directly, so the recovery proof needs no chosen cartesian
lifts or a new general Grothendieck-equivalence theorem. This is a choice of
presentation for the constructed family system, not a claim that fibred or
sheaf-over inputs have been classified by it.

## Positive code gluing and effective torsor descent (#646)

[HomRepresentableClassification](../../SquareKit/Internal/HomRepresentableClassification.lean)
constructs `HomSystem.system B` for any presheaf context `B`. Its data over `Γ`
are maps `Γ ⟶ B`, explicitly lifted to the `System.Data` universe. Restriction
is precomposition. `sectionEquiv` evaluates a map from a represented context at
the identity; its inverse is `represented`. `codesIso` packages these maps as
an isomorphism from the code presheaf to `raisedContext B`, and
`codesIso_code` identifies coding an arbitrary map with its raised map.

`codes_isSheaf_iff` proves that these codes are sheaves exactly when `B` is a
sheaf. It transports the sheaf condition through the proved comparison and
Mathlib's universe-lift equivalence. The base may have independent object and
hom universes. No subcanonicity is needed: the system is defined on all
presheaf contexts, including representables that need not be sheaves.

The [finite-site example](../../Examples/ClassifierDescent.lean) uses the
existing diamond site. Its proper cover of `X` consists of `U` and `V` with
overlap `W`. The new `pairs` sheaf has `Bool × Bool` at `X`, `Bool` at each
piece and `Unit` at the overlap. The restriction maps are the two projections.
The code matching family for `(false, true)` has a unique amalgamation, proved
using `codes_isSheaf`; `matching_value` identifies that amalgamation with the
code of the displayed pair. Both projection calculations are checked through
the natural code comparison.

The same example proves the site subcanonical by checking its Yoneda
presheaves. Nevertheless, the existing proper pointwise image of `E → 1`
has local sections over the cover and no section at `X`. Its previously proved
failure of sheafness, transported by `codes_isSheaf_iff`, gives
`bad_codes_not_sheaf` on this subcanonical site. This is an explicit alternative
to the two-point-open-space control described below. The earlier
constant-Boolean empty-cover rejection remains checked.

[TorsorClassifierDescent](../../SquareKit/Internal/TorsorClassifierDescent.lean)
connects the existing constructive torsor descent to the ordinary representable
family decoder. For a torsor `P`, `decoded` uses
`PresheafFamily.decodeSheaf P.family`. Its action is conjugated by the derived
evaluation comparison; the action laws, principality and local existence are
proved, and `comparison` is an equivariant isomorphism. Local existence uses
the sheaf isomorphism over the original display, not a chosen global section.

For any existing `Descent.Datum A P`, `glue` first constructs effective torsor
descent and then classifies and decodes it. `localComparison` recovers `P` on
the entire cover. `mapEquiv` is a bijection between all compatible equivariant
local maps and arrows between decoded glued torsors; `recover_map` and
`map_comparison` retain inverse recovery and its naturality. These are actual
equivariant maps. The torsor theorem that every such map is invertible
justifies the groupoid interface. `projection` retains the original base map,
and `canonicalRecovery` recovers an original torsor from its canonical datum.

The exact hypotheses are a site, a sheaf of groups, a sheaf context, a split
sheaf display whose projection is locally surjective, and a torsor on that
display with natural equivariant transport satisfying identity and cocycle.
Principality and local existence descend by the existing local torsor proofs.
No arbitrary operation is asserted to descend: the selected operation here is
the group action, and both transport and maps must preserve it. This client
uses the existing section universe `Type (max u v)`.

The smooth specialization recovers the quarter-turn clutching torsor through
this construction and proves it remains nontrivializable. A second example
passes distinct regular-torsor automorphisms through local arrow recovery and
classified descent and proves they remain distinct. Thus the client tests
nontrivial objects and maps, rather than only a terminal torsor.

This bounded construction needs no sheafification: the positive code presheaf
is already a sheaf, and torsor descent constructs sheaf total spaces before
classification. It proves neither a decoder extension across a sheafification
unit nor exact recovery for original non-sheaf codes. Those extensions remain
owned by [#647](https://github.com/VladimirMarko/conaled/issues/647), together
with comparison to Mathlib's general stack interface. In the pinned Mathlib,
`IsStack` extends `IsPrestack` and requires essential surjectivity of the
comparison to descent data for every covering sieve. The torsor result here
constructs object and map recovery for locally surjective split displays;
packaging it into that pseudofunctor and sieve-indexed contract remains work.
No `IsStack` premise or blanket stack instance is introduced.

Caller obligations are the existing sheaf, cover and cocycle data. Recovery
and equivariant map reconstruction are shared proofs. No recursion or
heartbeat limit was raised. This work does not measure comparative elaboration
cost or prove descent for the arbitrary coherent family diagrams from #645;
those diagrams do not supply a topology or local sheaf membership by themselves.

## Remaining contracts

The bounded positive code-gluing and effective torsor client from #646 is
implemented above. Further stack packaging and decoder extension across
sheafification remain under #647.
[#647](https://github.com/VladimirMarko/conaled/issues/647) owns additional coherent
systems and presentation comparisons; [#649](https://github.com/VladimirMarko/conaled/issues/649)
owns comparison with natural models, direct families and local universes.
The #645 equivalence above is for category-valued families and coherent local
arrow diagrams. It does not construct a decoder for the previously demonstrated
sheaf-over pseudofunctor or an arbitrary context-indexed pseudofunctor.

Effective descent still needs gluing and map descent, beyond pseudofunctor laws.
Sheafification would require extending a decoder across its unit and proving the
resulting recovery contract. A new cubical type-theory model additionally needs
interval, filling, type formers and their laws; classification supplies none of
those by itself.

## Existing contracts and reusable constructions

The baseline [classification core](../../SquareKit/Internal/RepresentableClassification.lean)
derives codes and coding naturality from restriction identity/composition, then
derives a family comparison from local evaluation equations. Its `System` stores
types of data and strict restriction functions. It has no topology, gluing,
category of data morphisms, or operation-preservation field. Its `Evaluation`
uses equality of fiber types and heterogeneous equality of their values. Moving
the latter argument to an arbitrary target category therefore needs an arrow
equation expressed with transport isomorphisms, rather than a claim about
elements of that category.

The base universe restriction is an encoding choice. The repository already
supports separate object, arrow and section universes in
[ElementFamilies](../../SquareKit/ElementFamilies.lean),
[ElementSheaf](../../SquareKit/ElementSheaf.lean), and
[SheafSlice](../../SquareKit/SheafSlice.lean). The last file proves
`SheafSlice.equivalence : Over Γ ≌ ElementSheaves Γ`: actual section-map fibers
and dependent total spaces recover one another, including maps and projection
equations. These results are available for the sheaf extension without first
building a new cubical model.

There is also an existing comparison between strict and coherent substitution.
[Family](../../SquareKit/Family.lean) uses chosen pullbacks, with identity and
composition comparison isomorphisms.
[SplitSheaf](../../SquareKit/SplitSheaf.lean) uses section-indexed families whose
total presheaves are sheaves; its substitution equations are definitional.
`subPresheafIso` derives the substituted total's sheafness from the ordinary
pullback, and `substitutionIso`, `displayIso`, and `ofDisplay` connect the two
presentations. [SplitSheafCoherence](../../SquareKit/SplitSheafCoherence.lean)
proves triple-substitution comparison and term recovery. Thus strictness is
already a useful presentation of some coherent mathematics, with explicit
recovery rather than an assertion that chosen pullbacks are equal.

## Coherent restriction

For structured data varying with context, use a pseudofunctor

`F : LocallyDiscrete Contextᵒᵖ ⥤ᵖ Cat`.

Its primitive operations are a category `F(Γ)`, restriction functors
`σ* : F(Γ) ⥤ F(Δ)`, and invertible identity/composition comparisons. Their unit
and associativity equations are essential: independently chosen pairwise
isomorphisms do not establish agreement of triple substitutions. Mathlib's
[Pseudofunctor](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/Functor/Pseudofunctor.lean)
already supplies this contract through `mapId`, `mapComp` and the coherence
fields. Using it avoids a second, weaker definition of coherent restriction.

`coherentCodes` constructs the code object as a category-valued pseudofunctor
by restricting `F` along the opposite of the representable embedding. Its value
at `I` is `F(h_I)`, with the original data morphisms retained. Its identity and
composition coherence come from pseudofunctor composition. For `A : F(Γ)`, the
objects assigned to generalized elements would be `(represented x)* A`.
`coherentCodeRestriction` supplies their local restriction comparison from
`mapComp` and represented-map equations. The #645 construction above packages a decoder and recovery for the concrete
category-valued family system using coherent arrow diagrams. For an arbitrary F,
the code pseudofunctor alone is still not a classification theorem; additional
reconstruction hypotheses and a corresponding decoder remain necessary.

Keeping the current strict result as a discrete specialization is appropriate.
For a strict `System`, discrete categories on its data and the existing
restriction equalities supply the coherent structure. The converse does not
follow by replacing an isomorphism with equality of objects. Quotienting objects
by isomorphism discards automorphisms and chosen comparison maps. Strictification
is another possible presentation change, with a recovery equivalence to prove.
The Stacks Project proves every fibred category equivalent over its base to a
split one; it does not assert equality with the original chosen restriction
operations. [Stacks, presheaves of categories](https://stacks.math.columbia.edu/tag/02XU).

The current Mathlib has both relevant presentations:

| Interface | Proved capability and role |
|---|---|
| [`Functor.IsFibered`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/FiberedCategory/Fibered.lean) | Cartesian lifts and `pullbackPullbackIso`; useful when a display category is the starting input. |
| [Pseudofunctor Grothendieck construction](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean) | Constructs a fibred projection from a contravariant category-valued pseudofunctor. |
| [`J.pseudofunctorOver A`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/PseudofunctorSheafOver.lean) | Sends `X` to sheaves on `Over X`; restriction composition and units are natural isomorphisms with proved coherence. |
| [Bicategorical Yoneda](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/Yoneda.lean) | Defines the 2-Yoneda embedding. This inspected file does not supply a general 2-Yoneda equivalence theorem to invoke for recovery. |

`J.pseudofunctorOver A` supplies the checked sheaf-over client. Its construction
proves coherence from actual sheaf restriction functors; the client checks the
object, map and local coding-comparison formulas. The next contextual coding
construction should check the two triple-substitution routes explicitly. A
further client can use ordinary display pullbacks and compare with `SplitSheaf`,
retaining both projection and value maps. A constant category with identity
restriction alone would not assess those transport obligations.

## Sheafness has two different locations

There are separate questions about the *code presheaf* and the *total space of a
decoded family*. The baseline `System` laws imply neither a topology nor code
gluing. Conversely, a recovered family can have a sheaf total even when its code
presheaf is not a sheaf. The following routes keep those claims separate.

For a family comparison `e : D ≅ A` over a sheaf context `Γ`,
`(ElementFamilies.totalFunctor Γ.obj).mapIso e`, followed by `Over.forget`, gives
an isomorphism of total presheaves. Transport sheafness of the total of `A`
through this isomorphism using Mathlib's
[`Presheaf.isSheaf_of_iso_iff`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Sheaf.lean).
Applying this to the comparison *derived* from local evaluation equations
constructs a decoded `SplitSheaf.Ty`, implemented as `PresheafFamily.decodeSheaf`. The final comparison is an intermediate
theorem, not an adapter input. The primitive sheaf evidence belongs to the
original family; the decoder gets its evidence by recovery.

This construction has an existing gluing foundation.
`ElementSheaf.fibers_isSheaf` proves that fibers of a sheaf display glue on the
element site. `ElementSheaf.total_isSheaf` proves that compatible total sections
glue by first gluing the base section and then the fiber section.
`SheafSlice.equivalence` packages their reconstruction. These are proved results,
not generic assumptions that a desired decoder happens to descend.
[ElementSheaf](../../SquareKit/ElementSheaf.lean),
[SheafSlice](../../SquareKit/SheafSlice.lean).

For *codes*, fix a topology `J` and prove the actual matching-family obligations
for `S.Data(h_I)`. Given a covering sieve on `I`, local data must agree after every
further restriction; construct a global datum whose restrictions are those local
data, and prove uniqueness. Mathlib separates the uniqueness and existence parts
as `Presieve.IsSeparated.isSheaf` and provides `FamilyOfElements.Compatible` and
`IsAmalgamation`. A convenient wrapper around these obligations is useful only
when a client derives them from its data construction. Assuming
`Presheaf.IsSheaf J S.codes` and rebundling it proves no new descent result.
[SheafOfTypes](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/SheafOfTypes.lean).

A concrete positive construction is `S.Data(Γ) = (Γ ⟶ B)` for a fixed sheaf
presheaf `B`, with restriction by precomposition. Evaluation at the represented
identity and the ordinary Yoneda argument give `S.codes ≅ B`, up to the explicit
universe lifts. Code sheafness then follows by transport from `B`. A client with
nonconstant sections and nonidentity restriction should verify the natural
isomorphism on values and maps. This connection is now implemented by `HomSystem.codesIso` and
`codes_isSheaf_iff` above; the proof does not assume code descent. [Mathlib Yoneda](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Yoneda.lean).

The representable contexts need attention if `Data` is defined only over sheaf
contexts. On a subcanonical site, Mathlib's `J.yoneda` and `J.uliftYoneda` give
the needed sheaf-valued embedding. On an arbitrary site, use sheafified
representables and the adjunction giving `Hom(a(h_I), B) ≃ B(I)`. The second route
changes the evaluation construction; the old generic-element reduction cannot
simply be asserted unchanged. [Mathlib canonical topology](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Canonical.lean),
[Stacks, representable sheaves](https://stacks.math.columbia.edu/tag/00WO).

## Descent for coherent structured codes

When code values have morphisms, local objects come with overlap isomorphisms,
their cocycle equation, and compatible local arrows. Gluing only isomorphism
classes loses that data. The established mathematical contract is descent in a
fibred category, or its pseudofunctor presentation. [Stacks, descent data](https://stacks.math.columbia.edu/tag/02ZC).

Mathlib already distinguishes the two obligations. `F.IsPrestack J` says that
the presheaves of morphisms are sheaves. `F.IsStack J` adds effectiveness of
object descent; together they imply that `F.toDescentData f` is an equivalence
for covers. `DescentData` is expressed using all comparison objects mapping to
cover members, so this interface does not require chosen pairwise pullbacks in
the base. Its compatibility arrows are proved invertible from identity and
cocycle conditions. [IsPrestack](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Descent/IsPrestack.lean),
[DescentData](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Descent/DescentData.lean),
[IsStack](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Descent/IsStack.lean).

A generic theorem may consume `IsStack` to transport already established descent,
but proving descent for a new classifier must construct it. Start with actual
local sheaf displays: build their glued total space, descend maps using sheaf
uniqueness, and derive the comparison functor's full faithfulness and essential
surjectivity. The existing
[torsor descent](../../SquareKit/SheafTorsorDescent.lean) is a model of this proof
shape: `comparison` constructs effective object recovery under local
surjectivity, while `Map.descend`, `mapEquiv`, and `canonicalRecovery` retain
maps and original objects. The
[action-quotient descent](../../SquareKit/SheafActionQuotientDescent.lean) and
[Čech comparison](../../SquareKit/SheafActionQuotientCechEquivalence.lean) retain
the selected overlap arrows. These are concrete constructions to reuse when
proving a Mathlib stack instance, not evidence that every pseudofunctor already
has descent. The inspected `pseudofunctorOver` file constructs its restriction
coherence but contains no stack instance.

For a structured subclass, first prove its underlying-object descent, then that
the additional structure and its laws are local and compatible with the chosen
gluing. The Stacks Project's full-subcategory criterion makes the distinction
precise: closure under pullback, fullness, and local membership support descent
of the subclass. A category whose arrows must preserve extra operations needs
its own arrow-descent proof when it is not full. [Stacks, stacks and subcategories](https://stacks.math.columbia.edu/tag/0268).

## Controls and next checked cases

The following controls delimit the wider library. The first is now formalized
as `codes_not_sheaf`. The second has a checked diamond-site counterpart
`bad_codes_not_sheaf` above; the two-point presentation below remains a paper example.

1. **Restriction laws do not imply code sheafness.** Take constant `Bool` data
   (lifted to the data universe) and identity restriction. All strict `System`
   laws hold. On a nonempty base
   with the maximal Grothendieck topology, the empty sieve covers each object;
   unique gluing would force `Bool` to have only one element. Mathlib proves the
   general terminal-section consequence as `Sheaf.isTerminalOfBotCover`.
   [Sheaf](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Sheaf.lean).
2. **Subcanonicity does not make every code presheaf a sheaf.** On the ordinary
   open-set site of a two-point discrete space, take presheaf `B` with one global
   section, two sections on either singleton, and one on the empty open, with
   global restrictions selecting `false`. The singleton pair `(true, false)`
   agrees on the empty intersection but has no global amalgamation. The now-implemented
   system `Data(Γ) = Hom(Γ, B)` has codes naturally isomorphic to `B`, giving the
   same failure on a subcanonical site. This calculation distinguishes missing
   object gluing from a merely unusual representation.
3. **Sheafification changes the recovery contract.** It provides a universal
   map into a sheaf; it does not generally recover all original code sections.
   For an already sheaf presheaf, Mathlib proves that unit invertible as
   `isIso_toSheafify` and provides `isoSheafify`. A sheafified classifier needs
   decoder extension and preservation theorems for that map, rather than the
   old exact code recovery by declaration.
   [Mathlib sheafification](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Sheafification.lean),
   [Stacks, sheafification](https://stacks.math.columbia.edu/tag/00W1).

The positive code-gluing and effective torsor-descent sequence is implemented
above. The next extensions are a comparison with the general Mathlib stack
contract and decoder extension across sheafification, with explicit unit and
recovery laws. #647 owns their assessment; #649 coordinates alternative
presentations. A new cubical model still needs its own type formers, filling
operations and any requested univalence proof.
