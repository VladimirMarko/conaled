# Original-cover parameter sections

The #447 construction defines `CoverSectionFamily f` on the original
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
`restriction_square` proves that canonical global restriction commutes with
every original cover square as a complete matching functor, and the actual
two-sheet pullback specializes this equation. `restriction_toSplit` identifies the original global restriction followed by
presentation transfer with the existing split restriction functor.

`Examples.OriginalCoverMatching` exercises those results on the actual two-sheet
cover for every supported generated context, on arbitrary local matching data
without a global-extension premise, and on the generated base context of the
nontrivial doubled-origin torsor. Presentation transfer reflects equality of
selected matching arrows. The helper `StrictMap.equalFunctor_map` proves the
canonical-overlap comparison independently of effectivity.

## Generated dependent families and full sections

`SmoothQuotientCoverMatching.restriction_isEquivalence` discharges the earlier
conditional split-effectivity premise using #445. The only cover hypothesis is
local surjectivity of the original sheaf map. `descentEquivalence` retains the
actual original canonical restriction, and `descentSquare` compares chosen
gluing along arbitrary commuting cover squares by a selected natural iso.
Neither square map is assumed invertible. `descentRecovery_natural` retains
every matching arrow in the chosen counit recovery.
`gluedSectionLift_natural` applies the selected extended-context descent square
to complete supplied matching-section lifts and their local comparison. It
compares whole gluings before normalization of their matching base; normalized
section reconstruction is separately supplied by `sectionDescent`.

The independent `relativeMatchingFamily` stores a local fiber object, actual
total overlap arrows, their Čech laws and their prescribed base projections.
`dependentComprehensionEquivalence` identifies its Grothendieck total category
with matching for the extended typed context. This covers all typed families,
including identities, substituted families and the finite/pulled/path-reindexed
tails discharged by #445. Nonidentity vertical arrows are retained.

`sectionDescent` reconstructs a complete global section from a supplied section
of that independent original-cover matching family. Its `recovery` is a natural
isomorphism of entire lifted sections, `recovery_base` specifies its selected
base component, and `verticalEquiv` gives unique recovery of all vertical
transformations. It assumes no global extension of the supplied local objects.
The earlier discrete deformation-section equalities remain specialized results;
they are not used to identify arbitrary groupoid-valued sections by equality.

`presentationTotalEquivalence` transfers independent relative matching through
the original/split extended-context equivalence. Its projection comparison uses
`toSplit_substitution` specialized to weakening. `presentationSections` and
`inversePresentationSections` transfer whole sections in both directions, with
selected recovery and vertical-transformation bijections. They require no cover
hypothesis because presentation change itself is an equivalence.

`relativeSquareMap` and `familySquare` act on independent relative matching
under arbitrary parameter-cover squares. `relativeSquare_projection` supplies
the actual base square; `familySquare_recovery` and its arrow naturality retain
the full total comparison. Identity/composition are strict at the total matching
functor level, while fixed-fiber normalization uses selected isomorphisms.
`relativeMatchingEquivalence_square` connects this family action to the original
extended-context square. No injectivity or equivalence of parameter restriction
is assumed.

`sourceSection_totalRestriction` connects an interpreted typed term directly to
the original canonical matching restriction, on objects and arrows.
`universalTransfer_restriction` specializes it to the unchanged source proof
used by the classical quarter-turn tangent consumer. The generated examples
also exercise the dependent-tail J caller, full section recovery/vertical
uniqueness on the two-sheet cover, and arbitrary parameter pullback of an
independent matching fiber. The existing nontrivial-torsor, ineffective-arrow,
compatible gluing and incompatible slope-zero/slope-one examples remain part
of this suite.

## Statement review and acceptance

The construction distinguishes canonical restriction equality, presentation
category equivalence and section recovery isomorphism. Cover surjectivity is
used for effectiveness, not presentation transfer or arbitrary-square maps.
Independent matching inputs contain overlap data and do not contain an assumed
global extension or desired equivalence. The negative two-sheet example fails
an actual overlap contract, rather than postulating inconsistency.

Focused checks use the pinned shell and unchanged kernel/trust limits. Final
fresh combined #433 validation and independent review remain required; the
implementation handoff records their status. Earlier conditional #447 and
partial #445 checkpoints are superseded by these actual effectiveness APIs.
This result concerns ordinary Čech descent for the stated generated fragment;
it does not claim hypercover descent or the broader modal/properness programme.
