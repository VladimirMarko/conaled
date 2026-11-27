# Proper local branches and their smooth sheaves

For actual maps `s : A → X` and `t : A → Y`, a locally diffeomorphic source,
a smooth target, and Mathlib `IsProperMap (fun a => (s a, t a))` give a finite
smooth branch diagram near every endpoint pair. The diagram covers the entire
preimage of an open rectangle. Its interpretation identifies that arrow sheaf
with the categorical coproduct of its source domains, preserving both endpoints
and restriction to smaller rectangles.

The ordinary theorem is in
[`ProperLocalBranches.lean`](../../Applications/Orbifolds/ProperLocalBranches.lean).
Its chart models are arbitrary real `ModelWithCorners`, with separate models
for `A`, `X`, and `Y`. Beyond those charted-space structures and the stated map
hypotheses, the primary existence theorem requires only `T2Space A`. It does not
require second countability, finite dimension, compact ambient manifolds, or a
locally diffeomorphic target. Thus it covers the requested noncompact,
finite-dimensional real manifold cases. A locally diffeomorphic target is an
additional hypothesis of the bisection theorem.

The proof derives compact discrete anchor fibers, separates their points by
source charts, and uses proper-map closedness to exclude the complement from a
smaller rectangle. The central fiber supplies the index type; callers do not
supply an enumeration. Its finiteness follows from `anchorFiber_finite`.

## Ordinary geometry

Names in this table are in `Orbifolds.LocalBranches`; `Diagram` names are methods
of the actual diagram. Let `R = {a | s a ∈ U ∧ t a ∈ V}`.

| Mathematical statement | Declaration |
| --- | --- |
| Every central anchor fiber is discrete and finite | `anchorFiber_discrete`, `anchorFiber_finite` |
| Open endpoint neighborhoods and a diagram indexed by the central fiber | `exists_diagram` |
| The same existence statement with a derived `Fin n` index | `exists_fin_diagram`; `Diagram.finDiagram`, `Diagram.reindex` |
| Disjoint open pieces cover exactly `R`; source inverses are actual inverse restrictions | `Diagram.piece`, `covers`, `sourceEquiv`, `source_eq`, `assemble` |
| Branch maps are the actual target after the inverse source map | `Diagram.branch`, `branch_smooth`, `source_assemble`, `target_assemble` |
| Complete arrow/source-coordinate equivalence with inverse laws | `Diagram.equiv`, `assemble_decompose`, `decompose_assemble`, `decompose_source`, `decompose_target` |
| The sum carries the coproduct topology and the inherited smooth structure from the discrete product | `Diagram.sumDomain`, `sumCoordinates`, `sumHomeomorph`, `sumInclusion_smooth`, `sumDiffeomorph` in [LocalBranchSum](../../Applications/Orbifolds/LocalBranchSum.lean) |
| Endpoint fiber equivalence retains actual arrows and both endpoint equations | `Diagram.fiberEquiv` in [LocalBranchRestriction](../../Applications/Orbifolds/LocalBranchRestriction.lean) |
| Empty central fiber gives an empty entire rectangle preimage | `exists_empty_diagram` |
| Additional local target inverses give branch diffeomorphisms onto open target images | `exists_bisection_diagram`, `Bisections.branchDiffeomorph`, `branchDiffeomorph_eq` |
| Smaller rectangles restrict the actual pieces and source domains | `Diagram.restrict`, `restrictRegionMap`, `restrictDomainMap`, `restrict_assemble`, `restrict_source`, `restrict_target` |

The sum is the open submanifold `{p : J × X // p.2 ∈ D.domain p.1}`.
`sumHomeomorph` compares it with the ordinary dependent sum, and the smoothness
proofs use its inherited discrete-product charts. Restriction can produce proper,
different, or empty source domains. The existence theorem makes no assertion that
partial domains are unavoidable.

## Interpretation and complete sections

The interpretation uses the existing `ManifoldRealization` interface, with
`Space a`, `Space x`, and `Space y` models, `IsManifold` instances, and types in
`Type`. It imposes no Hausdorff or second-countability hypotheses. For a native
arrow model different from `Space x`,
[`SmoothLocalDiffeomorphModel`](../../SquareKit/SmoothLocalDiffeomorphModel.lean)
constructs `Model s hs` from source-local charts. Its `diffeomorph`,
`toModel_smooth`, and `fromModel_smooth` compare both smooth structures by the
actual identity maps. `diagram` converts a native branch diagram while retaining
its source and target functions. This handles the finite-action arrow model
without equating its product model definitionally with the object model.

Write `j` for realization, `C = ∐ i, j(D.domain i)`, and `S = jU × jV`.
Names below are in `SquareKit.SmoothBranchRealization` unless qualified.

| Mathematical statement | Declaration |
| --- | --- |
| Realization of a disjoint open cover is its genuine sheaf coproduct | `ManifoldRealization.DisjointOpen.assemblyIso` in [SmoothManifoldDisjointOpen](../../SquareKit/SmoothManifoldDisjointOpen.lean) |
| The canonical map `C → jR` uses the actual inverse branches | `assembly`, `inclusion_assembly`, `assemblyIso_hom` in [SmoothBranchRealization](../../SquareKit/SmoothBranchRealization.lean) |
| Assembly is invertible over both endpoints | `assemblyIso`, `decompose`, `assembly_decompose`, `decompose_assembly`, `assembly_source`, `assembly_target`, `decompose_source`, `decompose_target` |
| Complete sections and endpoint fibers agree at every site stage | `stageEquiv`, `ArrowFiber`, `BranchFiber`, `fiberEquiv` |
| Both directions commute with every admitted stage map | `stageEquiv_restrict`, `stageEquiv_symm_restrict`, `fiberEquiv_restrict`, `fiberEquiv_symm_restrict`; stage identity and composition laws with suffixes `_id` and `_comp` |
| An empty index type realizes to the initial sheaf | `branchesIsInitial`, `emptyArrowIsInitial` |
| Smaller rectangles commute with assembly, its inverse, and endpoint maps | `arrowRestriction`, `branchRestriction`, `assembly_restriction`, `decompose_restriction`, endpoint laws in [SmoothBranchRestriction](../../SquareKit/SmoothBranchRestriction.lean) |
| Both the arrow and coproduct restriction squares over `S` are categorical pullbacks | `arrowRestriction_isPullback`, `branchRestriction_isPullback` |

The disjoint-open comparison descends maps into arbitrary sheaves through a
subordinate chart cover. Real-point detection identifies the actual chart maps;
the arbitrary-sheaf descent argument proves the coproduct property. A bijection
of real points alone would not establish this property. Restriction pullbacks
come from the proved open-preimage and open-rectangle comparisons, without a
transversality hypothesis on the anchor.

A section of `C` can have different indices on different members of a cover.
Consequently the stage equivalence does not replace `C(T)` by a global dependent
sum of summand sections. Fiber finiteness gives no bound by the number of branches
on all sections over an arbitrary stage. For empty indices, the categorical
initial sheaf retains its sections at stages covered by the empty family; its
section type is not asserted to be empty at every stage.

This construction supplies ordinary local geometry and its interpretation in the
current smooth sheaf model. It does not construct a general groupoid or
quotient-stack comparison, transfer an Agda proof, or establish a full Myers
orbifold equivalence. Mathlib `IsProperMap`, internal `DPProper`, and
`Compact.ProperData` remain distinct notions. Further comparison obligations
remain under #32.

## Checked applications

| Control | Public construction exercised |
| --- | --- |
| Proper identity source with constant, non-étale target | `Examples.ProperLocalBranches.constant_target_branches`, `constant_target_not_etale` |
| Empty central fiber of the real-line unit anchor | `Examples.ProperLocalBranches.diagonal_empty_branches` |
| Unit branch restricted from `(-2,2)` to target `(-1,1)` | `Examples.ProperLocalBranches.restrictedUnit_domain`, `_domain_nonempty`, `_domain_proper`, `_fiber_roundtrip` |
| Finite actions, the quarter-turn disk, and a noncompact ineffective action | [ProperLocalBranches](../../Examples/ProperLocalBranches.lean), through the proper-anchor theorem and the explicit finite-action diagram |
| Quotient-arrow comparison and ineffective arrows with equal endpoints | `Examples.SmoothBranchAction.quotient_comparison`, `ineffective_distinct`, `ineffective_endpoints` |
| A disconnected test whose section factors through no fixed summand | `Examples.SmoothBranchAction.varying_no_summand` |
| Non-real nilpotent branch section and a stage map changing it | `Examples.SmoothBranchRealization.nilpotentBranch_not_real`, `_kill_changes`, `_endpoints`, `_roundtrip`, `_comparison_restrict` |
| Initial branch sheaf with a section at an empty-covered stage; proper punctured-window restriction | [SmoothBranchRestriction](../../Examples/SmoothBranchRestriction.lean), including `partial_assembly_restriction` |

The action comparison uses the induced finite-real arrow model together with
its proved identity diffeomorphism to the native product model. The quotient
comparison composes the existing `External.smoothChartEquiv`; its inverse-label
convention is therefore retained. Ordinary properness and source étaleness stay
in the geometric theorem, while the interpretation requires the existing
finite-real smooth-manifold interfaces.

## Validation

The implementation uses Lean `v4.35.0` (compiler commit
`eb6cafb`) and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The public entrypoint imports all four consumer modules. Candidate acceptance
uses `direnv exec . python3 scripts/check-candidate.py SHA` followed by
`direnv exec . python3 scripts/check-candidate.py SHA --verify`, including the
exhaustive proof audit. The accepted SHA, command results and independent review
outcomes are recorded in the completion record on
[issue #717](https://github.com/VladimirMarko/conaled/issues/717).

Declaration-level `#print axioms` checks for the proper-anchor existence,
finite-index and bisection theorems, `Diagram.sumDiffeomorph`, the model adapter,
both canonical assembly isomorphisms, the endpoint-fiber equivalence, both
rectangle restriction pullbacks and the principal/action comparison
equivalences report exactly `{propext, Classical.choice, Quot.sound}`. These are
transitive dependencies, not merely axioms mentioned in the declaration bodies.

The same transitive set is reported for the checked consumers
`constant_target_branches`, `diagonal_empty_branches`,
`restrictedUnit_fiber_roundtrip`, `quotient_comparison`, `ineffective_distinct`,
`ineffective_endpoints`, `varying_no_summand`, `nilpotentBranch_not_real`,
`nilpotentBranch_endpoints`, `nilpotentBranch_kill_changes`,
`nilpotentBranch_roundtrip`, `nilpotentBranch_comparison_restrict`,
`empty_fiber_sheaf`, `partial_isPullback`, and `partial_assembly_restriction`
in the example namespaces listed above.
