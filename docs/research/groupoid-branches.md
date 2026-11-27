# Independent branches and the selected smooth groupoid

This development connects [#719](https://github.com/VladimirMarko/conaled/issues/719)
and [#720](https://github.com/VladimirMarko/conaled/issues/720). Its starting
revision is `cf0f33ad7cba53bfdf0a688537dc788d4ad63632`, after the shared-coherence
work in #723. The full geometric and completion requirements remain in the
issues.

## Design selection

The [brief](groupoid-branches-design/brief.md) and independent
[contract](groupoid-branches-design/contract.md),
[use](groupoid-branches-design/use.md), and
[alternatives](groupoid-branches-design/alternatives.md) assessments compare
actual arrow presentations, independent branch diagrams and completion routes.
All three inspect existing code; their proposed new constructions were not yet
Lean-checked. Their original recommendations are retained.

The selected first geometric instance is the trivial `C4` action on the real
line. Independent diagrams change their indexing on different components of
a disconnected endpoint region. This tests a comparison that cannot be
expressed by one global permutation of branch indices. The generic comparison
reconstructs actual arrows and uses no group labels. Noncommutative action
recovery must separately check the existing inverse-label convention.

The contract and alternatives assessments prefer a two-open object-atlas
pullback, which would additionally exercise arrows between distinct atlas
lifts. The use assessment also considers the finite action itself sufficient.
The task permits an action-presentable example and requires independent arrow
charts, so the selected first instance uses the finite action directly. This
does not claim a new result about arbitrary smooth groupoids or about the
nonexistence of global action presentations. Existing atlas clients remain
recovery obligations.

For the selected completion, instantiate the already constructed torsor quotient
and prove its comparison with the actual-arrow presentation at every sheaf
parameter. The quotient's objects, gluing and stack proof come from the existing
torsor development. The new unit must have proved full faithfulness and local
generation before the generic universal theorem applies. The contract
assessment's proposed direct groupoid-principal-bundle category would be a
further construction, not an assumption needed to reuse this selected output.
No such bundle implementation is claimed here.

## Actual arrows and independent coordinates

`SheafGroupoid.Operations` stores object and arrow sheaves, endpoints, unit,
inverse and composition on the categorical pullback of target and source.
Its laws concern those operations on arbitrary generalized arrows. The fiber
groupoids and their restriction pseudofunctor are derived from those laws.
For a site with objects in `Type u` and homs in `Type v`, the sheaves take
values in `Type (max u v)`; the fiber objects use
`Type (max (u + 1) (v + 1))`, matching the existing action presentations.

`SmoothActionGroupoid` constructs the smooth composable-arrow manifold using
`SmoothTransversePullback`. Source étaleness supplies transversality. Its
`realizedComposable_isPullback` proves preservation at every sheaf parameter;
`pairDiffeomorph` also identifies the native pullback with the explicit pair
coordinates. The interpreted unit, inverse and composition agree with the
represented groupoid operations. The generic smooth construction allows a
discrete group; finiteness enters its ordinary properness result.

`SmoothBranchComparison.comparisonIso` assembles an arrow through one diagram
and decomposes it through another. It permits different index types and
domains. `overlapDomain` is the actual intersection of two branch pieces in
source coordinates. Different endpoint rectangles compare after restriction
to their common rectangle. Identity, inverse and triple comparisons and
parameter restriction are proved at the sheaf-map level.

`SheafGroupoid.Chart` specifies coordinates by an endpoint pullback square.
The geometric adapter `SmoothBranchGroupoid.chart` proves that square from
the branch theorem and realization comparisons. Its `comparison_map` identifies
the generic chart comparison with the independent geometric branch comparison.
Unit, inverse and composition in any selected output chart reconstruct the
original operations. Associativity and compatibility with comparison and
parameter restriction follow from actual-arrow recovery.

The retained controls distinguish several possible losses of information.
`Examples.IndependentBranchCharts` changes the C4 indices on the positive
component of the punctured line. Its comparison cannot come from one global
reindexing; even the unit section in the switched coordinates cannot factor
through one global summand. The file also checks empty and proper partial
domains, restriction and ineffective arrows. `Examples.SmoothActionGroupoid`
uses varying labels on a disconnected test manifold and an S3 action to
distinguish the required composition label `h * g` from `g * h`.

## Completion and scope

`SheafGroupoidCompletion` recovers action charts from an actual arrow sheaf
through its proved arrow isomorphism. Its unit maps these charts to regular
torsors in the existing constructed quotient stack. Full faithfulness retains
all arrows, and local generation uses the total-space cover of each torsor.
The source is already a prestack, so no preliminary identification of arrows
is needed. `universalEquivalence` applies the existing full mapping-category
theorem: the forward functor is precomposition, and its hom equivalence acts
on modifications.

An endpoint window need not cover the whole object manifold. In particular,
the punctured window above does not cover the line. The completion of its
branch presentation therefore uses the restricted object space. General
object-atlas completion requires a proved locally surjective atlas map.
This condition belongs to local generation, not to arrow recovery or to the
comparison of independent coordinate choices over a fixed atlas.

`Examples.GroupoidCompletion` retains the nontrivial clutching torsor with a
constant target. Its local actual-arrow data have no global chart. Distinct
ineffective loops survive the completion unit, and every discrete observation
of those loops fails faithfulness. The trivial-group action on the line supplies
an already-stack input: its actual completion unit is an equivalence on every
sheaf parameter. Modification recovery uses the same public completion interface. `Examples.IndependentBranchCompletion`
uses a constant nonzero target in the punctured object space to check the
no-global-chart obstruction through the switched branch unit itself.

For branch charts, `SheafGroupoidChartPresentation.changeTransformation` is
defined by reconstructing actual arrows. Its identity and composition
modifications come from coordinate recovery. `chartUnitComparison` and
`changeChartRestrictionComparison` carry that independently defined map through
the completion unit and the full mapping categories. The resulting comparison
therefore also preserves modifications. Smaller-rectangle comparisons retain
their actual inclusions; shrinking a rectangle is not claimed to give an
equivalence with the completion over the whole original object space.

The actual-arrow presentation also recovers the prior globally trivial
subcategory, atlas presentation and site-change quotient comparison through
`SheafGroupoidCompletionRecovery`, under their original assumptions.
The canonical categorical endpoint pullback supplies the arrow chart for any
atlas map, so this recovery does not ask existing callers for new chart data.
`Chart.atlasMap` also changes the object atlas along a commuting square,
retaining the same actual arrows. Its identity, composition and parameter laws
recover the original `SheafActionRefinement.map` and `refine` comparisons.
`atlasUnitComparison` and `atlasRestrictionComparison` connect it to completion
and full mapping categories. `Examples.GroupoidAtlasComparison` checks both
routes from the original disk common atlas, including their recovered old maps
and their agreement as completion-unit modifications.
The direct action APIs remain available. The selected construction covers
action-presentable groupoids and their independent branch coordinates;
arbitrary higher stackification (#721), bibundles (#722), and the internal
properness/Myers comparison (#724) remain separate work.

## Validation

`SquareApplications` imports the new modules and retained examples, placing
their declarations under the integrated build and exhaustive proof audit.
Acceptance uses an immutable candidate, isolated validation and independent
Standards and Spec reviews against both issue contracts. The design reports
preserve the initial assessments; their proposals are not substitutes for the
checked declarations and cases described above.
