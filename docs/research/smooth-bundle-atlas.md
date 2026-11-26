# Derived smooth bundle atlases and Myers consumers

This construction follows the scope assessment in
[smooth-principal-bundle-scope.md](smooth-principal-bundle-scope.md) and addresses
[#638](https://github.com/VladimirMarko/conaled/issues/638) and
[#639](https://github.com/VladimirMarko/conaled/issues/639), under
[#576](https://github.com/VladimirMarko/conaled/issues/576). The assessment preceded
implementation. No extra geometric restriction was needed for the chart or bundle
construction.

## Ordinary hypotheses

`SmoothPrincipalBundle.Bundle` takes ordinary data on `B E : Type`, both modeled
on `Fin n → ℝ` with their boundaryless real smooth manifold structures. It takes a
group action on `E`, a smooth invariant projection `E → B`, smooth action maps for
each group element, and local sheet trivializations around every base point.
For each such trivialization:

- The base neighborhood is open.
- Each group element indexes an ordinary `OpenPartialHomeomorph E B` whose target
  is that neighborhood and whose forward map is the supplied projection on its
  source.
- The inverse sheet map is smooth on the neighborhood.
- Every point over the neighborhood lies in exactly one sheet source.
- The inverse sheets satisfy `sheet (g*h) b = g • sheet h b`.

These are independent ordinary local product hypotheses. They contain no sheaf
object, represented atlas, `TrivializedOn`, or comparison. `productEquiv` proves
both inverse laws; `productHomeomorph` proves the topological product identification
for a discrete group. Smoothness of the forward sheets follows from the smooth
projection, and smoothness of the inverse sheets is explicit. The action convention
is left multiplication. A conventional right principal action can be converted
by inverse group elements; that conversion is not packaged here.

The requested finite discrete groups are included. Most constructions work for
any Type-sized discrete group, so finiteness is not an implicit requirement. The
finite index in `JointTorsorAtlas` counts the objects being compared, not group
elements, manifold charts, or a compact cover. No Hausdorffness, second countability,
compactness, effectiveness of the target action, or global section is assumed.
Both the total and base manifold use the same dimension `n`, as appropriate for
a discrete principal bundle; a target manifold may have a different dimension.

## Construction and statement review

| Source and declarations | Statement and proof boundary |
| --- | --- |
| `SmoothOpenPullback`: `unit_of_real_points`, `inverse_site_pullback`, `inverse_sheaf_pullback` | Inverse images of ordinary open restrictions are actual pullbacks at every finite-presentation stage. Real points detect units in the stated algebra argument, not general smooth-map equality. |
| `SmoothChartOverlap`: `pair`, `factor`, `compose` | Pair domains are defined by ordinary chart intersections; every relation in the existing chart diagram factors through them. Composition uses the derived inverse-open pullback. |
| `SmoothChartPullback`: `stageSetoid`, `raw_chart_eq`, `raw_pullback`, `chart_pullback` | A quotient-valued cocone detects raw chart equality at every stage. Left-exact sheafification transports the proved pullbacks to the existing realization. This is not a proof by equality on real points. |
| `SmoothManifoldRepresentedAtlas`: `representedAtlas`, `subdivisionAtlas`, `inverseTarget`, `commonRepresentedLeft`, `commonRepresentedRight` | Ordinary charts produce cover, pairs and triples. Ordinary chart restrictions and coordinate maps produce actual refinement and base-change maps. `inverseSecond_base` and `inverseComposite_base` retain the map equations for successive changes of base. |
| `SmoothPrincipalBundle`: `LocalTrivialization`, `Bundle`, `productHomeomorph`, `action_free` | The independent sheet contract gives local products and ordinary freeness. No global trivialization follows. |
| `SmoothBundleRealization`: `baseCharts`, `totalCharts`, `realizedProjection`, `transitionLabel` | Base charts are restricted inside local trivializing neighborhoods. Total charts are the inverse sheets over those charts. Labels are continuous because their fibers are open sheets, hence locally constant for a discrete group. |
| `SmoothBundleRecovery`: `ordinaryDatum`, `descendedObject`, `totalSpaceIso` | The ordinary local sections and transition labels give the forward cocycle. Existing effective descent constructs the torsor. Its target map to the ordinary total-space realization is locally surjective, by the actual total-chart lifts, and monic, by projection preservation, torsor principality and freeness. Its inverse is constructed with `asIso`. |
| `SmoothBundleRecovery`: `act_free`, `constantLabel_eq_of_real_points` | Locally constant labels can be tested after local reduction to constants. A stage with no real points has the empty cover and unique sheaf sections. These results do not discard infinitesimal manifold-valued sections. |
| `SmoothBundleRecovery`: `totalSpaceIso_projection`, `totalSpaceIso_equivariant`, `quotientObject_totalMap` | The comparison retains the actual projection, every group-sheaf label, and the independently supplied smooth equivariant target map. |
| `SmoothTorsorAtlas`: `exists_principal_lift_of_isLocallySurjective`, `TorsorAtlas`, `JointTorsorAtlas` | Local surjectivity produces principal neighborhood lifts over each ordinary chart. Their subdivision has derived represented pullbacks and actual sections; `ofSection` supplies equivariant trivializations. Finite families of objects receive one joint atlas. |
| `SmoothBundleRecovery`: `quotientRecovery`, `derivedRecovery`, `derivedArrowEquiv`, `joint_composition` | These consume #567 extraction and selected recovery. Complete arrows correspond to whole external `Hom` records, whose labels determine full smooth arrow families. Both round trips, identity, composition, inverse and recovery naturality retain the target map. |
| `SmoothBundleRecovery`: `derivedGauge`, `sectionsGauge`, `sectionsGauge_datum`, `sectionsGauge_recovery`, `chartChoiceComparison`, `derivedBaseChange` | The self-overlap gauge and the gauge between two independently chosen local section families are extracted from the identity of the original object on derived local coordinates. Common-refinement and base-change comparisons use the constructed maps and #567 comparisons. Independently selected descents are isomorphic, not identified by fiat. |

`Examples.SmoothBundleAtlas.composite_comparison` displays the `eqToHom` transport
of the complete restricted datum in a composite comparison. The two ordinary base
maps scale by 2 and 3; `scaleTwo_nonidentity` proves that the first interpreted map
is not the identity. `composite_base` identifies their actual composite. The
chart-choice comparison uses the explicit equality transport in `selfCommonRight`.

## Which quotient objects are covered

There are two separate results.

1. An ordinary `Bundle`, together with any smooth equivariant map `E → M`, constructs
   `quotientObject` over its derived base-chart realization. `totalSpaceIso`
   identifies its total sheaf with the existing realization of `E`, and the
   projection theorem identifies the map to `B` through the explicit preferred-atlas
   isomorphism. `quotientRecovery` recovers this full object on the derived ordinary
   atlas. The isomorphism is an output, not an admission hypothesis.
2. Every existing `SheafActionQuotient.Object` for the interpreted smooth action
   over any `ChartFamily.realization` admits a derived section atlas and recovery.
   Taking the preferred chart family includes the preferred manifold object.
   Two such objects receive a constructed common atlas and a complete arrow
   equivalence. A finite family receives a joint atlas for arbitrary composable
   arrows, without requiring the sheaf torsors to come from a separately supplied
   ordinary bundle.

This does not classify arbitrary sheaf bases, arbitrary quotient sheaves, or
arbitrary groupoids as manifold realizations. It does not prove that every admitted
sheaf torsor is the realization of a newly reconstructed ordinary total manifold.
That reverse classification is distinct from recovery of an existing sheaf torsor
and from the proved realization of a supplied ordinary bundle. General transverse
pullback preservation remains in #97. Arbitrary models with corners, infinite
manifold dimensions and larger universes are not admitted by these signatures.

## Examples and controls

`Examples.SmoothBundleAtlas` constructs the identity principal bundle on the real
line, its ordinary-bundle quotient, total-space comparison, recovery, full arrow
round trip, joint composition, chart-choice comparison and successive nonidentity
base changes. Its construction has no compactness hypothesis. The empty-domain
consumer uses the same derived-section API.

`Examples.SmoothFiniteCover.C4Bundle` supplies the ordinary open-sheet contract for
the regular C4 bundle over a point and consumes `totalSpaceIso` and
`quotientRecovery`. This tests a nontrivial finite structure group. It is globally
trivial and is not evidence for a nontrivial covering.

The Hausdorff example is `z ↦ z²` on the punctured complex plane.
`SquareBundle` supplies its independent ordinary sheet contract and consumes
`totalSpaceIso` and `quotientRecovery`. Its structure group is `rootsOfUnity 2 ℂ`,
with checked cardinality 2, acting by complex multiplication. The manifold model
is `Fin 2 → ℝ`, obtained from the explicit continuous linear coordinate equivalence
and the open embedding of the punctured plane into that model.

`SlitRoots` proves that `exp(log z / 2)` and `I * exp(log (-z) / 2)` are real-smooth
square-root branches on the two slit planes, which cover every nonzero point.
The translated branches are open embeddings because they are continuous local
sections of the existing covering map. Their ranges are the actual sheet sources;
fiber principality proves unique group indexing. The sheet inverse smoothness,
projection and equivariance fields are checked before invoking the bundle bridge.

The topological consumer checks surjectivity, finite fibers, and absence of a
continuous global section. A continuous section has open range by local
homeomorphism and closed range as the fixed-point set of `s ∘ square`. Connectedness
would make its range all of the total space, contradicting the distinct points
1 and −1 with the same image. `SquareBundle.no_sheaf_section` transfers this
obstruction through the new total-space and projection comparisons: any section
of the descended sheaf torsor would reconstruct a smooth ordinary section. Thus
this is a recovered smooth finite cover with a checked global obstruction.

`Noncommuting.local_order` and `local_wrong_order` pass S3 arrows through the new
joint derived atlas and distinguish the correct composition from its reverse.
The calculation uses the right translations of the regular torsor; it is separate
from the old external-label inverse convention. `shiftedSections_injective` proves
that different S3 translations give different local section selections.
`changed_recovery` consumes the comparison extracted from two such choices.
These comparison parameters do not become admission hypotheses: `selectedSections`
already supplies a choice for every admitted quotient. `sectionsGauge_datum` and
`sectionsGauge_recovery` compare arbitrary choices on that constructed cover,
after restriction along the two actual common-refinement maps. They do not claim
definitional equality of independently selected descents.

The existing C4 doubled-origin example remains explicitly non-Hausdorff.
`DoubledOrigin.localRecovery` derives fresh local section atlases and recovery for
its two chart restrictions; `no_global_section_despite_local_recovery` retains the
global obstruction. Existing #567 S3 label-convention and ineffective-action
controls are retained alongside the new S3 consumers; local recovery of the C4
restrictions also uses its ineffective target action. No local recovery is promoted
to a global section.

## Separate semantic and properness obligations

No theorem here identifies external `IsProperMap`, unrestricted internal `DPProper`,
and `Compact.ProperData`. In particular, open chart inclusions are not claimed to
be proper. There is no compactness or properness assumption hidden in the covering
arguments. Any bridge between these notions needs its own hypotheses and proof.

Ordinary Agda source admission and higher/cohesive semantics remain separate from
these Lean constructions. This work does not discharge the already-owned
#606, #607, #625, #627 or #631 obligations, nor does it promote the sheaf model to
an unrestricted cohesive interpretation.

## Validation boundary

Focused development builds are not acceptance. Exact-candidate integrated build,
exhaustive axiom audit, final receipt verification, and independent Standards and
Spec review are recorded outside the source tree and reported with the delivered
commit. Development attempts included dependent-rewrite and instance-reduction
failures. A raw-pullback proof exhausted both the default and an experimental
800,000-heartbeat budget; restructuring it around a generic relation proof removed
the escalation. An initial constant-label freeness proof also exhausted the default
budget before explicit group typing removed the elaboration problem. No increased
heartbeat budget or admitted proof remains for these attempts. Review found that
the first candidate retained S3 controls only by import, compared only one selected
section family with itself, and had not attempted the Hausdorff smooth connector.
The new S3, independent-section and square-bundle consumers address those gaps.
The square-bundle development encountered scalar-restriction naming, model
instance inference and projection-rewrite failures before the complete construction
and no-sheaf-section proof compiled.
