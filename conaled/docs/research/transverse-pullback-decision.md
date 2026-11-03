# Transverse-pullback preservation: decision gate for #97

**Verdict: DEFER the proposed preservation theorem.** This resolves the
preimplementation questions in [#97], not its conditional theorem deliverable.
The selected finite-quotient tangent application has now been constructed in
[#99] without general transverse-pullback preservation. Its next identified
gap is source-language interpretation and soundness. No new ordinary-geometry
construction is selected by this assessment.

Baseline: `e532ceea6609c5e74cbd661200ba3243c626080b`, inspected 2026-10-20,
after accepted #99. Mathlib is pinned by [the manifest](../../lake-manifest.json)
to `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0). API availability below
refers to that revision, not current upstream. No Lean source, dependencies or
trust settings change in this gate.

## Which application needs preservation?

The [#96 selection](myers-tangent-integration.md) chose the first-order
finite-quotient consequence of Myers Proposition 4.3.5. The proposition uses
infinitesimal étaleness and coherent lifting to compare pointed tangent
fibers. Myers's Axiom 4 concerns a modality preserving crisp pullbacks; it is
not a theorem about the ordinary manifold interpretation preserving transverse
squares. Interpreting that axiom would therefore require a separate contract.
[Myers, v1, Proposition 4.3.5 and Axiom 4][myers].

The accepted construction proves the particular semantic comparison directly:
[`SmoothQuotientArcs.comparison`](../../SquareKit/SmoothQuotientArcs.lean)
uses the arbitrary-parameter torsor equivalence and an isocomma groupoid.
[`SmoothQuotientTransport.openFixedFiberEquivalence` and
`origin_forward_classical`](../../SquareKit/SmoothQuotientTransport.lean)
then identify the fixed tangent fiber and its actual quotient-arrow transport
with finite real coordinates and `QuarterTurn.disk_tangent`.
[`SmoothOpenArcs`](../../SquareKit/SmoothOpenArcs.lean) supplies the local
open-domain coefficient comparison. These are checked inputs, not requests
for another ordinary fiber-product theorem.

There is consequently no selected application here demonstrating a need for
general transverse pullbacks, or even a new general submersion/étale
preservation theorem. That is a sequencing conclusion from the completed
application, not a claim that such preservation is false or never useful.
For a future proper étale groupoid presentation, first identify the actual
source/target base-change square used by its construction. An open inclusion
or local diffeomorphism case may suffice; the present quotient-torsor proof
does not establish that future dependency.

## What the classical source does and does not supply

Kock's category `Mf` assumes smooth Hausdorff manifolds with a countable
basis. Definition III.3.1 states transversality by joint spanning of the target
tangent space. Axiom A includes preservation of transverse squares and the
terminal object. Theorem III.8.1 proves the smooth-function-algebra result;
its proof uses regular-level local models and gluing. Theorem III.8.4 then
uses this separately from full faithfulness in its well-adapted model.
[Kock, III.3 and III.8, printed pp. 141–142 and 173–177][kock].

These source results provide a candidate proof route. They do not establish
an identification of that model with this repository's presentation site or
chart-colimit interpretation. Their global manifold hypotheses must not be
silently imported into #95 or discarded when reusing their arguments.

## Pinned ordinary APIs

The following are reusable ingredients, with obligations still exposed.
All Mathlib links pin the inspected commit.

| API | What is available | What still needs construction |
| --- | --- | --- |
| [`Manifold.IsSubmersionAt`, `IsSubmersionAt.mk_of_charts`][submersion] | A supplied smooth-chart normal form equal to a linear projection, with a chosen complement. | Deriving that normal form from a surjective derivative. The file explicitly lists this finite-dimensional bridge, composition and the local-diffeomorphism bridge as TODOs. |
| [`HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented`][implicit] | A regular-level local homeomorphism from strict differentiability, surjective derivative and complemented kernel, in complete normed spaces. The finite-dimensional-target specialization removes the explicit kernel-complement input. | Smooth fiber-product charts, transitions and projection laws. This analytic normal form is not an assembled manifold fiber product. |
| [`ContDiffAt.implicitFunction`, `eventually_apply_eq_iff_implicitFunction`, `contDiffAt_implicitFunction`][implicit-smooth] | A smooth local solution and uniqueness in a product domain; inputs include `ContDiffAt`, nonzero differentiability order and an invertible partial derivative. | Choosing the kernel split or invertible minor from transversality and fitting it to the chart model. Finite real coordinates at order ∞ satisfy the ambient completeness/field assumptions. |
| [`IsLocalDiffeomorphAt.localInverse`][local-diffeo] | An actual local inverse with smoothness and inverse laws, and composition of local diffeomorphisms. | A base-change manifold and its sheaf comparison. This is a possible narrower input, independent of the submersion TODO. |
| [`ChartedSpaceCore`][charts], [`isManifold_of_contDiffOn`][is-manifold] | General assembly of chart structures and smooth transitions. | The particular atlas, covering, transition and dimension proofs. |

No ready ordinary transverse fiber-product constructor or `IsTransverse` /
`TransverseAt` predicate was located. Searches covered all pinned
`Mathlib/Geometry/Manifold` paths for transversality, submersion, local
diffeomorphism, fiber/fibre product and pullback; follow-up searches covered
all Mathlib for the named predicates and manifold/fiber-product combinations,
and Geometry/Analysis for derivative-to-submersion bridges. The transversality
hit in `Geometry/Manifold/Bordism.lean` is explanatory prose; inspected
pullback hits concerned bundles/vector fields. This is a bounded search
finding, not a universal assertion that differently named results cannot
exist. The explicit submersion TODOs corroborate the narrower API gap.

The existing local interpretation offers more specific reusable results:

- [`principalIso`](../../SquareKit/SmoothManifoldOpenComparison.lean) and
  [`principalIso_naturality`](../../SquareKit/SmoothManifoldPrincipalMaps.lean)
  compare realized principal opens and their actual maps with the site embedding.
- [`SmoothAlgebra.Localization.openEquiv`](../../SquareKit/SmoothLocalizationOpen.lean)
  identifies principal localization with smooth functions on its nonvanishing open.
  [`pushout_universal`](../../SquareKit/SmoothLocalizationBaseChange.lean)
  gives localization base change against every target smooth algebra;
  [`overlap_sheaf_pullback`](../../SquareKit/SmoothOpenOverlap.lean) proves
  actual principal-overlap pullbacks.
- [`SmoothOrdinaryPullbackCover`](../../SquareKit/SmoothOrdinaryPullbackCover.lean)
  supplies ordinary inverse-image principal refinements. The sheaf
  multicoequalizer in [`SmoothChartRealization`](../../SquareKit/SmoothChartRealization.lean)
  supplies descent and chartwise equality of arrows.
- [`rawMap` local surjectivity and `rawMap_chart`](../../SquareKit/SmoothChartLocalLifting.lean)
  give local chart lifting for arbitrary stage sections. The same file's
  `local_chart_principal` instead starts at an ordinary source point; it
  cannot substitute for arbitrary-stage lifting.

These established localization/overlap cases are useful evidence for a
narrower future theorem. They do not already constitute preservation of
all open-embedding squares or all transverse squares.

## The missing all-stage comparison

Write `ι` for the existing manifold realization. Even after constructing an
ordinary smooth fiber product `F` with projections, the unresolved statement
is a natural bijection, for every presentation stage `A`,

```
ιF(A) → {(u,v) : ιM(A) × ιN(A) | (ιf)(A)(u) = (ιg)(A)(v)}.
```

The map must be induced by those projections and retain their equations.
This would identify the sheaf with the categorical pullback; evaluation only
at the real stage would not. The inverse must exist and be unique for actual
generalized sections, including nilpotent stages, and commute with stage
maps. This is the proposed preservation obligation, not a newly proved API.

Existing full faithfulness
[`ManifoldRealization.homEquiv`](../../SquareKit/SmoothManifoldFullFaithfulness.lean)
compares arrows between realized manifolds. It does not supply the displayed
inverse for arbitrary stage sections. Nor does ordinary transversality alone
discharge a smooth-algebra universal property.

For a coordinate proof, the additional local obligation is to turn a regular
level-set or transverse fiber-product chart into a universal smooth-algebra
presentation: compatible maps into every stage algebra must factor uniquely
through the proposed chart algebra. An ordinary set-theoretic equation or a
calculation of its derivative is insufficient. One can seek a local
normal-form proof, or a smooth-function quotient/pushout theorem, but either
route must connect its algebra to the existing presentation codes and prove
restriction compatibility. Existing localization and descent can then glue
these local inverses; they do not create the missing local inverse.

## Hypotheses and re-entry condition

The current interpretation uses `Space n := Fin n → ℝ`, full-space real
models and Type-sized carriers. Its chart families need not be finite.
[#95's full-faithfulness theorem](../../SquareKit/SmoothManifoldFullFaithfulness.lean)
assumes neither Hausdorffness nor second countability. Preserve that scope.
A future preservation statement has separate obligations:

- **Smoothness and transversality:** use actual `ContMDiff` hypotheses. Specify
  joint spanning in the same target tangent space, transporting along
  `f x = g y`, or prove the equivalent coordinate derivative-surjectivity
  formulation. Do not silently equate surjectivity with the pinned
  normal-form `IsSubmersionAt` predicate.
- **Dimension and charts:** for a nonempty transverse fiber the proposed
  model dimension is `dim M + dim N − dim P`. The available
  [`LinearMap.finrank_range_add_finrank_ker`][rank-nullity] and
  [`Module.finrank_prod`][product-dimension] are linear algebra ingredients,
  not a manifold dimension theorem. Empty fibers have vacuous pointwise
  transversality and do not imply `dim P ≤ dim M + dim N`; assign and verify
  their chart model separately. Boundary/corner cases are outside this slice.
- **Separation and countability:** the existing local normal-form predicates
  do not demand these global conditions. If the future statement adopts
  Hausdorff/second-countable inputs, the fiber-product subtype inherits them
  from `M × N` by the pinned [T2][hausdorff] and
  [second-countability][countability] instances. Target Hausdorffness is useful
  for closedness of the equality locus, not needed for those subtype
  inheritance instances. None of this proves the smooth atlas.
- **Choice of model proof:** Kock's global smooth-function route carries the
  source assumptions stated above. No result here shows they are necessary
  for a local chart/gluing route, or proves that route without them. The
  theorem's final hypothesis list must follow the chosen construction,
  separately from #95; it is not settled merely by citing a well-adapted model.


Return to #97 only with a named application, the precise square it uses,
and a decision whether an open/étale, submersion, or fully transverse case is
needed. Before making it implementation-ready, pin the ordinary pullback
construction, its smooth projection laws, the model-side local algebra
comparison and its hypothesis list. Keep the provisional EDD cases: a
nontrivial selected square, empty and zero-dimensional cases, and a
nontransverse example explaining the hypothesis without a universal failure
claim. None of those conditional theorem obligations is marked complete here.

The next source-to-model construction remains the one identified in the
[#99 record](finite-quotient-tangents.md#remaining-source-to-model-work):
interpret the selected Id/J transport fragment in parameter-indexed quotient
groupoids and fixed tangent families, including substitution, descent and
transport soundness. #102 owns the separate proof-transfer experiment.
Transverse preservation would not by itself supply those rules, dependent
sums over `BG`, universe rules, cohesive modalities, crisp judgments, general
Weil KL, microlinearity or full well-adaptedness. [#36] remains open.

[#97]: https://github.com/VladimirMarko/conaled/issues/97
[#99]: https://github.com/VladimirMarko/conaled/issues/99
[#36]: https://github.com/VladimirMarko/conaled/issues/36
[myers]: https://arxiv.org/html/2205.15887v1#S4.SS3
[kock]: https://users-math.au.dk/kock/sdg99.pdf
[submersion]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/Submersion.lean#L64
[implicit]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/Implicit.lean#L315
[implicit-smooth]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/ImplicitContDiff.lean#L55
[local-diffeo]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/LocalDiffeomorph.lean#L160
[charts]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/ChartedSpace.lean#L626
[is-manifold]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Geometry/Manifold/IsManifold/Basic.lean#L791
[rank-nullity]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean#L173
[product-dimension]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Dimension/Constructions.lean#L161
[hausdorff]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Separation/Hausdorff.lean#L362
[countability]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Bases.lean#L889
