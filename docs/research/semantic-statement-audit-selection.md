# Prospective semantic statement audit sample

This is the selection checkpoint for
[#432](https://github.com/VladimirMarko/conaled/issues/432), recorded before
the audit's declaration-by-declaration assessment. **The audit is incomplete.**
No new defect, passing semantic review, coverage percentage or repository-wide
assurance is reported here. #235 coordinates continuation and independent
Standards and Spec review.

The inspected baseline for the planned audit is
`0b9a72f58d8fd7476eff6676f88b2690491b5051`. Selection on 2026-11-09 used file
and declaration inventories, associated reports and the live acceptance bodies
of #214, #291, #346 and #372. Primary mathematical texts and proof bodies still
need the detailed checks listed below. Later changes to these inputs must be
identified explicitly rather than silently folded into this baseline.

## Selection and risk strata

The sample deliberately includes an older compiler transformation, dependent
semantic transport, and both quantitative composition and fixed-point
selection. Its small shared modules have named consumers with independent
meaning specifications and negative controls. That makes comparison of the
public theorem with an actual use feasible without pretending a file count is
semantic coverage. Selection is risk-based, not random or statistically
representative. It is not limited to the latest dependent-language work or the
already repaired initializer case.

| Stratum and reason for selection | Planned declaration scope | Intended claim to recover independently |
|---|---|---|
| Substitution/induction: binder extension can invalidate an induction hypothesis stated only for a closed environment. | [`FirstOrderSubstitution.lean`](../../SquareKit/FirstOrderSubstitution.lean): `liftRen`, `rename`, `liftSub`, `subst`, `single`, `eval_rename`, `eval_subst`, `eval_single`; source `Term`/`Var` grammar and the staging use. | [#214](https://github.com/VladimirMarko/conaled/issues/214) requires typing/substitution compatibility and stage-respecting residual correctness. Recover the substitution equation over arbitrary well-typed valuations from source evaluation, then compare the binder case and open replacement example in [`ArithmeticStaging`](../../Examples/ArithmeticStaging.lean). [Staging report](arithmetic-staging.md) is a claim under audit, not independent proof of correctness. |
| Semantic transport: pointwise fibers, coherent transport and one globally selected section are different obligations. | [`RepresentationExtension/Descent.lean`](../../SquareKit/RepresentationExtension/Descent.lean): `DescentData`, `totalSetoid`, `base`, `insert_eq_iff`, `insert_surjective`, `fiberEquiv`, `fiberEquiv_transport`, `Equivariant`, `descend`, `recover`, `section_descends_iff`, with their helper definitions. | [#291](https://github.com/VladimirMarko/conaled/issues/291), item 4, requires coherent-fiber descent and a condition for the chosen section to descend. Start from the [frozen fixture](all-model-representation-fixture.md) and [earlier paper construction](representation-extension-comparison.md), then compare actual quotient equality, empty fibers and the representative-sensitive rejection case. |
| Quantitative composition: intermediate points may leave the next domain, or sensitivity may be confused with additive cost. | [`Numerical/Error.lean`](../../SquareKit/Numerical/Error.lean): `Bound.apply`, `Bound.comp`, `comp_apply`, `comp_assoc`, `mul_apply`, `monotone`, `propagate`, `UniformOn`, `estimate`, `compose`, `compose_three`, `identity_estimate`; [`Examples/NumericalError.lean`](../../Examples/NumericalError.lean) affine controls. | [#372](https://github.com/VladimirMarko/conaled/issues/372) requires selected approximate outputs, uniform errors and explicit closure of both maps at intermediate boundaries. Recover the two-stage inequality from metric triangle inequality and the pinned Mathlib Lipschitz definition. Compare the [ordered-observation paper calculation](ordered-quantitative-observations.md) and [implementation exposition](numerical-error-composition.md). |
| Fixed-point selection: intertwining can preserve fixedness without preserving the selected least solution. | [`SelectedFixedPoint.lean`](../../SquareKit/SelectedFixedPoint.lean): `approximants`, `solution`, `solution_fixed`, `solution_le`, `map_approximants`, `map_solution`; [`IndexedPartialComputation`](../../Examples/IndexedPartialComputation.lean) `approximants_eq_bounded`, `solution_eq_meaning`, `reindex_solution`, `two_reindexings`, observation and rejecting cases. | [#346](https://github.com/VladimirMarko/conaled/issues/346) requires strict continuous intertwining, exact selected value/trace recovery, enabled/disabled behavior and distinction between fuel exhaustion and divergence. Recover the independent countdown graph and least-fixed-point argument from [the pre-implementation contract](context-dependent-partial-computation.md) and its primary domain-theory source. |

These are planned inspection targets, not declarations already approved by this
audit. Related helper definitions will be read to determine the statements'
meaning; expansion beyond this inventory will be logged with its reason.

## Sources and controls to inspect next

For substitution, inspect the actual first-order grammar and evaluator before
reusing any substitution result. The [Davies primary paper](https://www.cs.cmu.edu/Groups/fox/people/fp/courses/15816-s10/papers/Davies96.pdf)
is a source for staging motivation, not a theorem about this repository's
grammar. The intended ordinary substitution equation can also be derived
directly from that grammar and environment interpretation; record that as an
independent paper derivation rather than attribute it to Davies.

For descent, the frozen fixture and earlier report define the selected
contract. Inspect [Barrett–Halvorson](https://arxiv.org/html/1506.04675) only
where the report attributes extension/comparison claims to it; its Morita
results must not be treated as a theorem about arbitrary dependent transport.
Recover the bounded quotient-family argument separately from its stated
identity/composition laws.

For quantitative composition, inspect
[`Mathlib/Topology/MetricSpace/Lipschitz.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/MetricSpace/Lipschitz.lean)
at the pinned revision, and derive the claimed inequality with independently
named exact and approximate intermediate values. For fixed points, inspect
[Abramsky–Jung, *Domain Theory*](https://www.cs.ox.ac.uk/people/samson.abramsky/handbook.pdf),
the cited least-fixed-point result and its hypotheses, alongside the actual
Mathlib iteration/continuity APIs used by the module. These links are a
reading plan; this checkpoint does not report completed source verification.

The known mixed-syntax/initializer repair in the
[first-wave report](semantic-traditions-first-wave.md) and
[control assessment](classical-control-selected-search.md) is calibration only.
Revisit its open continuation parameter and closed saved-stack distinction,
then ask whether any sampled induction has a comparable domain mismatch.
It must not be counted as a newly discovered defect.

Planned false-positive controls include necessary environment-agreement
hypotheses for substitution, equivariance for a *selected* descended section,
strictness for least-fixed-point transport, and unusable negative error radii.
Their presence alone is not a finding. Each needs a comparison with its
independent intended conclusion and a satisfiable positive case. Existing
capture, representative-sensitive, non-strict-map and amplification examples
are candidates for rejection evidence, not substitutes for inspecting the
universal statements.

## Uninspected areas and continuation discipline

No detailed semantic assessment has yet been completed in this checkpoint.
The planned sample excludes higher-order substitution, weak-machine simulation,
the current #107 repair, general sheaf/action-quotient descent, smooth geometry,
discrete approximations, numerical integration's full analytic argument, and
the general internal SDT provider. The numerical disk-motion consumer is
background context rather than a promised full theorem audit. The four chosen
modules cannot certify those areas or the repository as a whole.

The assigned author did not author the sampled Lean code. The preceding #431
research task did inspect and summarize the descent interface; that prior
familiarity is disclosed and is not evidence of an independent passing audit.
The coordinator's starting-path suggestions were used only as candidate
locations, not findings or a prescribed sample.

Continuation will record, for each selected claim, intended versus actual
quantifiers and domains, uniformity, admissibility, intermediate forms,
non-vacuity, equality and selected observations. Suspected gaps require a
specialization, countermodel or precise statement mismatch. Dispositions must
separate exposition error, insufficient theorem strength and erroneous paper
reasoning. A bounded clear defect can be repaired in this workflow; larger or
ambiguous changes need exact successor issues without weakening the intended
specification. False positives remain in the record.

No lint is proposed yet. A heuristic needs a demonstrated recurring pattern
and false-positive controls before implementation; it cannot certify semantic
adequacy. No Lean files, tests or tooling changed at this checkpoint. The
full audit, any necessary proof validation, final recommendations and both
independent review axes remain outstanding. #432 remains open and claimed.
