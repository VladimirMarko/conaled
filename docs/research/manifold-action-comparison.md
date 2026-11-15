# Smooth manifold action arrows and sheaf quotient arrows

Issue [#566](https://github.com/VladimirMarko/conaled/issues/566) extends the
C4 disk comparison to smooth actions on the existing manifold realization.
The comparison concerns chart objects, whose torsors are the regular torsors.
It does not choose trivializations for arbitrary torsors.

## Mathematical contract

`SmoothManifoldAction.representation` takes `G M : Type`, `Group G`,
`MulAction G M`, `TopologicalSpace M`, `ChartedSpace (Fin d → ℝ) M` and
`IsManifold (ManifoldRealization.Model d) ∞ M`. Its remaining input is the
smoothness of each actual map `x ↦ g • x`. The representation interprets those
maps with `ManifoldRealization.map`; unit and multiplication follow from its
functor laws. `Representation.action` extends this representation to locally
constant sheaf labels, including labels varying on disconnected parameters.

The external arrow comparison also names a discrete topology on `G` and uses
`FiniteActionPresentation.arrowModel (Model d)`. Finiteness is unnecessary for
the comparison itself. The separately available external `proper_etale`
theorem requires `Fintype G`, `DecidableEq G`, `T2Space M` and
`SecondCountableTopology M`. None of these, nor compactness or effectiveness,
is silently imposed by the core comparison.

For a principal test domain `U`, `hat m hm` is literally
`(principalIso U).inv ≫ ManifoldRealization.map m hm`. `onMap_iff` proves that
its sheaf action equation is equivalent to the pointwise equation
`ordinaryHomLabelEquiv G U k x • n x = m x`. Its proof uses the action at the
real stage, the ordinary label evaluation theorem, and manifold full
faithfulness. It does not take equation reflection as input.

`External.Family U m n` independently specifies a smooth map into `G × M`
with the external source equal to `m` and external target equal to `n`.
`External.smoothChartEquiv` identifies these complete families with actual
quotient arrows. Its inverse equations retain maps and certificates, not just
orbit classes. The forward label is the inverse of the quotient's right
translation label. A forward label `g` followed by `h` composes as `h * g`.

## Correspondence with existing sources

| Construction | Source and use |
| --- | --- |
| Interpreted group action | `SmoothConstantAction.Representation` and `ManifoldRealization.map_id/map_comp` |
| Equation reflection | `SmoothManifoldFullFaithfulness`, `SmoothManifoldPrincipalMaps`, and `SmoothOrdinaryQuotient.homLabel_point` |
| Independent external arrows | `Applications/Orbifolds/FiniteActionPresentation.lean`: `Arrow`, `source`, `target`, product model and operations |
| Complete quotient-arrow equivalence | `SheafActionQuotient.chartArrowEquiv` and `ordinaryHomLabelEquiv` |
| Operation preservation | Generic `SmoothDiskPresentation.ForwardLabel` laws |
| Restrictions | Actual `Arrow.reindex`, `principalIso_naturality`, and explicit endpoint transport |
| Atlas changes | `atlas_naturality`, `atlas_common`, and extension of fixed-label intertwiners to all sheaf labels |
| Canonical recovery | `Descent.recoveryArrowComparison_commutes` for canonical global-chart descent data |
| Cover comparisons | Existing selected base-change and matching/family/section naturality instantiated at the constructed action |
| Disk recovery | `principalIso diskDomain`, `diskMap`, `diskPoints`, and the real-linear `complexCoordinates` equivalence |

The disk recovery compares the chosen forward and inverse maps of the old
`smoothChartEquiv`. It uses a manifold in finite real coordinates and explicitly
converts its arrow maps to the complex disk. The complex model is not identified
definitionally with `Model 2`. The real-line controls similarly use the explicit
continuous linear equivalence `lineCoordinates : (Fin 1 → ℝ) ≃L[ℝ] ℝ`, with
smoothness in both directions.

Admitted domain morphisms include every smooth map between these principal
open submanifolds through `ManifoldRealization.openMapOfContMDiff`; restriction
does not require a global ambient extension.

## Checked controls

`Examples/SmoothManifoldAction.lean` exercises the constructed comparison with
the trivial group and the ineffective trivial S3 action on the noncompact
real line. Distinct S3 labels remain distinct arrows with equal endpoints.
Two transpositions reject reversed composition, and their three-cycle rejects
forgetting the inverse convention. A punctured-line test domain retains
independently defined sign-varying labels. Two nonidentity restrictions obey
the complete composite law. The empty domain admits a family between unequal
constant endpoints; the inhabited line rejects such an arrow through its
target certificate.

## Boundaries

This is a Lean external comparison for the Type-sized, finite-dimensional,
real boundaryless `ManifoldRealization` interface. Arbitrary
`ModelWithCorners` realization, interpretation into Myers's Agda development,
higher or cohesive semantics, general nontrivial-torsor comparison, and the
general proper-étale local finite-bisection construction remain separate.
Mathlib `IsProperMap`, internal `DPProper`, and `Compact.ProperData` remain
different contracts. The comparison adds no implication between them.
