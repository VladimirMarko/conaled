# Original-cover parameter sections

This partial #447 construction defines `CoverSectionFamily f` on the original
sheaf map `f : Y ⟶ X`. It supplies full deformation sections at every parameter
into Y, naturality under further restriction, and matching for maps with equal
composites to X. Its inputs contain no global quotient object or glued section.

`toSplit` and `fromSplit` use the actual `SplitSheaf.displayIso f` and its inverse.
Both round trips recover complete sections, including their context-arrow maps.
`glue` applies the existing split-display theorem only after this transfer.
`recover_local_section` recovers sections on arbitrary local quotient objects,
without assuming they extend globally. `glue_restrict_section` compares the
glued result along the original cover map; `glue_natural_section` retains the
parameter-restriction comparison to the split pullback.

`alongSquare` transfers the entire input family along commuting squares, with
identity/composition laws. `glue_alongSquare_section` proves full-section
naturality when both vertical maps are covers, including covering refinements.
`baseChange` uses the actual categorical pullback of the original map; its
local surjectivity follows from the split pullback. `originalPullbackIso`
retains both chosen projections. `toSplit_alongSquare_sections` compares the
explicit split-presentation map with original-cover transfer. `glue_unique`
transfers uniqueness using the original covering values.

`Examples.ArbitraryCoverSections` constructs the actual coproduct sheaf cover
`X ⨿ X → X`, proves local surjectivity, supplies compatible constant deformations
and exercises full-section recovery and selected-arrow retention. It also uses
the existing nontrivial doubled-origin torsor with ineffective action. The
cover's two inclusions have the same composite to X, and `sheet_matching`
derives equality of their supplied deformation values from the actual input
contract. `Examples.OriginalCoverRejection` instantiates the negative case:
the trivial finite group acts on the scalar sheaf, and the two local chart
deformations have slopes zero and one with the same zero-boundary object.
Coefficient extraction proves that they differ. `no_matching_family` then
uses `sheet_matching` to rule out an input on the actual two-sheet cover that
supplies those values. This is a failure of the overlap contract, with no
assumed inequality or hypothetical cover.

`SheafCoverCech` constructs the original map’s categorical double and triple
pullbacks. `splitDoubleIso` and `splitTripleIso` identify them with the split
overlaps, preserving the diagonal and all three pair projections. `SmoothQuotientCoverMatching.matchingEquivalence` uses those maps to transfer
actual generated local objects, overlap isomorphisms and arrows in both
directions. The identity and composition laws for arbitrary parameter squares
hold on complete matching functors; `matchingEquivalence_natural` compares the
selected split square with the original square. `splitSquareMap_local` checks
that this is the same local map used by parameter-compatible sections.
`restriction_toSplit` identifies the original global restriction followed by
presentation transfer with the existing split restriction functor.

`Examples.OriginalCoverMatching` exercises those results on the actual two-sheet
cover for every supported generated context, on arbitrary local matching data
without a global-extension premise, and on the generated base context of the
nontrivial doubled-origin torsor. Presentation transfer reflects equality of
selected matching arrows. The helper `StrictMap.equalFunctor_map` proves the
canonical-overlap comparison independently of effectivity.

Statement review keeps the fiber boundary explicit: these are discrete
deformation sections. Their equality does not establish equality of arbitrary
groupoid-valued families. Quotient context arrows remain data in the lifted
sections; the examples retain distinct arrows even when they act identically.
Neither a section of the cover nor invertibility of parameter restriction is
assumed.

Focused Lean checking passed for the new library module and its examples using
the pinned shell and unchanged heartbeat/trust settings. Full candidate
validation and independent review remain pending. This is not completion of
#447: effective generated family/section recovery from #445/#446 remains required.
The matching-equivalence construction depends on the checked #445 interface
checkpoints `60b73ac` and `c5a37a9`, incorporated into this worker branch before
final integration. Neither those dependency checkpoints nor these focused
checks constitute full #433 acceptance.
