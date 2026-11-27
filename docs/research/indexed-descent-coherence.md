# Shared coherence for descent and indexed families

[#723](https://github.com/VladimirMarko/conaled/issues/723) adopts two small
proof extractions: fixed-source inverse-square equations use the existing
independently sized construction, and both total-functor adapters use one
cartesian-lift comparison argument. The existing public contracts stay intact.
Descent, refinement and modification constructions retain their own interfaces.

The assessment starts from `9637d09513faa98877b4c2aa82e808899c6f7a67`, with
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The
[brief](indexed-descent-coherence-design/brief.md),
[contract assessment](indexed-descent-coherence-design/contract.md),
[use assessment](indexed-descent-coherence-design/use.md), and
[alternatives assessment](indexed-descent-coherence-design/alternatives.md)
preserve the initial inventory, experiments and recommendations. Their line
references refer to that baseline. Temporary probe paths record assessment
execution; the adopted proofs and their production callers are retained below.

## Equivalence-square specialization

[EquivalenceSquare](../../SquareKit/EquivalenceSquare.lean) already derives an
inverse commuting square, its composition equation and compatibility with the
original equivalence units and counits. Its categories have independent object
and hom universes. It requires equivalences on the vertical edges and an
invertible forward square; neither horizontal functor has to be an equivalence.
The composition theorem requires the actual forward composition equation.

[StackificationUniversal](../../SquareKit/StackificationUniversal.lean)'s
`inverseSquare_spec`, `inverseSquare_comp` and `inverseSquare_canonical` now
specialize those proofs to the identity left edge. The extra left unitor is
local setup for the proof. Callers retain the original names, types and
hypotheses. The definitions of `inverseSquare`, `inverseSquareOver` and
`normalizedSquare` remain unchanged, as do the exact normalization and identity
equations. This preserves the selected isomorphisms used by refinement.

The common construction has distinct mathematical consumers. Effective local
descent uses it to compare realizations under refinement and parameter change.
[CoGrothendieckTransport](../../SquareKit/CoGrothendieckTransport.lean) uses it
to derive inverse substitution and its coherence from forward comparisons
between independently sized indexed categories. The latter supports local-sheaf
totalization. Both use the same chosen recovery maps, rather than an existence
claim about an unspecified inverse.

The change removes separate counit cancellation, naturality and triangle-law
arguments from the three fixed-source proofs. It adds identity-functor/unitor
setup inside those proofs and no obligations at their callers. The same-source
composition and canonical specializations were checked before adoption. Their
production use, including parameter composition and full stackification
recovery, remains in the integrated build.

## Cartesian arrows under a functor over the base

[BasedCartesian](../../SquareKit/BasedCartesian.lean) adds
`CategoryTheory.BasedFunctor.map_isCartesian_of_map_isCartesian`. Given a
Mathlib based functor `T`, two cartesian arrows `φ` and `ψ` over the same base
arrow with the same codomain, and cartesianness of `T.map φ`, it proves
cartesianness of `T.map ψ`. The categories and base have independent object and
hom universes. No full-faithfulness, inverse functor or invertibility of all
arrows is required.

Mathlib supplies the ingredients: uniqueness of cartesian lifts gives a
vertical isomorphism between their domains; a based functor preserves its
verticality; composition with that isomorphism preserves cartesianness. The new
lemma combines this argument without adding a structure or proof fields.

The `map_cartesian` proofs in
[CoGrothendieckMap](../../SquareKit/CoGrothendieckMap.lean) and
[CoGrothendieckTransport](../../SquareKit/CoGrothendieckTransport.lean) instantiate
this lemma with a canonical lift and an arbitrary cartesian arrow. Each supplies
its existing total functor, projection equality, Mathlib's source lift, and the
existing proof for the image of that lift. Explicit projection instances handle
Lean elaboration at the `BasedCategory.ofFunctor` boundary. The clients no
longer repeat the vertical-isomorphism construction or its factorization proof.
This shares a universal-property argument; it does not eliminate the work of
proving that each adapter preserves canonical lifts.

The two adapters alone are not counted as distinct mathematical applications:

- [CoherentFamilyFibration](../../SquareKit/Internal/CoherentFamilyFibration.lean)
  compares coherent family codes with functors on categories of elements of
  presheaf contexts. Its strong transformations and modifications provide both
  total recovery maps. The generic preservation result serves decoding and
  coding under arbitrary context substitutions.
- [CoherentSheafFibration](../../SquareKit/Internal/CoherentSheafFibration.lean)
  compares rooted local sheaf codes with slice sheaves, using density and the
  stated limit hypotheses. Its source and target fibres can have different
  universes. The preservation result feeds the
  [cartesian diagram equivalence](../../SquareKit/Internal/CoherentSheafDiagrams.lean)
  over an arbitrary context diagram.

These applications retain both directions of cartesian transport. Reflection
in `cartesian_of_map` still uses fibre full faithfulness. No assumption that
arbitrary reindexing reflects isomorphisms has been introduced. The category of
cartesian diagrams still admits all vertical natural transformations, including
noninvertible ones; cartesianness restricts its objects' transition arrows.

## What remains specific to each construction

The initial reports contain declaration-level inventories, including variance,
universes, invertibility and equations. Their retained dispositions are:

| Construction | Reason to retain |
|---|---|
| Descent action on objects, arrows, pullbacks and refinements | It establishes overlap compatibility for complete descent data. A total arrow instead relates two fibre objects over one base arrow. |
| Realization, common refinements and parameter/refinement compatibility | These use covering, local generation, full faithfulness and target stackhood to compare actual local presentations. Ordinary equivalence transport supplies only part of the proof. |
| Descent and total actions on modifications | Both retain arbitrary modification components. The small shared component extraction already comes from a Mathlib naturality field; their surrounding compatibility proofs differ. No additional wrapper is adopted. |
| Homogeneous strong transformations and heterogeneous comparisons | The former directly retain Mathlib's modification category; the latter retain independent fibre universes. Replacing either route with the other would require additional recovery or universe machinery. |
| Identity normalization, `unit_of_composition`, `conjugate_map_square` | Selected identity comparisons remain observable. The last two generic statements have no demonstrated second production consumer; a new module would not remove a shared obligation. |
| Full faithfulness and map recovery | Recovering descent compatibility and recovering a total arrow over a fixed base map use different conditions. Both already use Mathlib's full-faithfulness interface. |

A larger displayed-category or heterogeneous transformation framework could be
useful for another capability. Here, Mathlib based functors and ordinary
transport lemmas already express the shared data. Adding fields for the existing
coherence conclusions would transfer proofs to callers. Removing modification,
refinement or universe information would lose used capabilities. Neither change
has demonstrated benefit for the inspected clients.

The adjacent private inverse-square constructor in
`SmoothQuotientCoverPresentationSections` is already a short composition of
Mathlib mate operations. It is retained: adopting a different spelling there
would add no shared coherence proof beyond the selected extraction. This is a
retain decision, not an outstanding defect.

## Checked uses and scope controls

The public theorem statements and definitions used by the existing controls
remain unchanged. The required integrated build and exhaustive proof audit
cover both mathematical families, including:

- [ActionStackification](../../Examples/ActionStackification.lean): `localUniversal`,
  `chartUniversal` and `chartModificationEquiv` retain the #678/#679 equivalences
  of whole mapping categories and their actual restriction functors.
  `not_effective`, `not_isStack` and `chart_not_effective` distinguish prestack
  arrow descent from effective object descent.
- [TorsorStack](../../Examples/TorsorStack.lean):
  `empty_descent_not_faithful` exhibits information loss without covering data.
- [CoherentFamilyFibration](../../Examples/CoherentFamilyFibration.lean):
  noncommuting ordered substitutions, composite cartesian transport, recovery
  naturality, `collapseTotal_not_iso` and `badData_no_recovery` retain arbitrary
  maps and detect loss of restriction coherence.
- [CoherentSheafFibration](../../Examples/CoherentSheafFibration.lean): both
  substitution orders, a nonidentity composite base, a noninvertible composite
  and its recovery equation, and unequal universes.
- [CoherentSheafDiagrams](../../Examples/CoherentSheafDiagrams.lean): a cartesian
  diagram with nonidentity composite transition, noninvertible vertical maps,
  rejection of a nonvertical ambient map, and unequal/reversed universe levels.
  Its equalizer results concern a supplied limiting fork; they assert no new
  limit existence.

The pre-adoption probes checked the fixed-source equations through Across and
both cartesian adapters through the proposed lemma. The cartesian probe reached
an actual coherent-family total category and the sheaf `oppositeComposite`,
using `changingDiagram.property` for source cartesianness. These probes used
existing compiled artifacts. Exact-candidate acceptance separately rebuilds
changed definitions and their consumers and performs the exhaustive audit.
No new law is weakened, so the retained controls suffice for this proof reuse.
The contract report's group-valued failed-composition example remains a paper
argument, not a new checked result.

Three perspectives supplied initial reports. The contract and use assessors
were fresh; the alternatives assessor had earlier #725 review and #726
implementation exposure, disclosed in its report. Reports were not shared
between assessors before completion. Near completion the coordinator told the
alternatives assessor that small specialization and cartesian probes had passed;
that preliminary-result exposure limits independence of its final recommendation.
The initial reports are preserved without rewriting their conclusions. Adoption
rests on the checked contracts and applications, with separate independent
Standards and Spec acceptance reviews.

## Remaining ownership

This assessment found no unresolved mathematical defect needing a new ticket.
#723 owns the two extractions and this inventory. The broader family-adapter
survey remains in [#708](https://github.com/VladimirMarko/conaled/issues/708).
[#235](https://github.com/VladimirMarko/conaled/issues/235) remains the owner for
future architectural reassessment if further consumers expose repeated
obligations. #725/#726 provide delivered totalization and diagram capabilities;
#678/#679 retain their delivered mapping-category universal properties. Retained
domain-specific proofs are not deferred extraction tasks.
