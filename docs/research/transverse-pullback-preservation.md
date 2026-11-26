# Transverse pullbacks under manifold realization

`SmoothTransversePullback.Realization.isPullback` proves that the existing
smooth sheaf interpretation preserves the ordinary transverse fiber product.
The theorem is in
[`SmoothTransverseRealization.lean`](../../SquareKit/SmoothTransverseRealization.lean).
It takes smooth maps `f : M → P`, `g : N → P` and
`SmoothTransversePullback.Transverse f g`. The latter is ordinary derivative
transversality; #674 proves its equivalence with the coordinate derivative
condition used to construct local normal forms.

## Ordinary object and categorical statement

The source is the actual subtype
`{xy : M × N // f xy.1 = g xy.2}`, with the product/subtype topology.
The #675 construction supplies its charted-space and smooth-manifold
instances with model `Space (m+n-p)`. `Realization.first` and `second` are
`ManifoldRealization.map` applied to the ordinary projections with their
proved smoothness witnesses. The target arrows are `map f hf` and `map g hg`.

`comparison` is the canonical arrow to the categorical pullback, and
`comparisonIso` proves that this same arrow is an isomorphism.
`comparison_first` and `comparison_second` give its two projection laws.
`isPullback` retains these actual arrows. No normal form, factorization,
pullback property or comparison isomorphism is assumed by that theorem.

The manifolds have Type-sized carriers and finite real full-space models.
There is no Hausdorff or second-countability hypothesis. The ordinary
construction separately inherits these properties from the source manifolds
when available. Empty fibers retain the chosen truncated-subtraction model:
vacuous transversality does not imply `p ≤ m+n`. Boundary and corner models
are outside the theorem's inputs.

## Local algebra and global descent

The proof uses the accepted coordinate, analytic and ordinary-manifold
constructions from #673, #674 and #675:

1. [`SmoothNormalFormPrincipal`](../../SquareKit/SmoothNormalFormPrincipal.lean)
   converts the smooth regular-level chart into maps between principal
   domains. `LocalModel.normal_isPullback` transports the proved restricted
   coordinate zero-fiber square through the actual principal isomorphisms.
   Its parameter map evaluates to the ordinary regular-level parameterization.
2. [`SmoothTransverseLocalPullback`](../../SquareKit/SmoothTransverseLocalPullback.lean)
   constructs products of arbitrary principal domains and proves their
   full-algebra universal property. The normal-form ambient maps recover both
   ordinary coordinates. `normalDifference_zero` converts equality of full
   target algebra maps into the zero-fiber equation;
   `normal_factorization` then gives a unique full-algebra factor at every
   presentation code.
3. [`SmoothManifoldChartMono`](../../SquareKit/SmoothManifoldChartMono.lean)
   derives chart monomorphisms from the actual overlap pullbacks. If all real
   reductions of a chart section lie in another chart, `chartSaturation`
   constructs a section in that chart with equality of the complete
   generalized sections. Real reductions establish invertibility of the
   overlap support through the site's existing `unit_of_real_points`; the
   overlap pullback supplies the section and its full equality.
4. [`SmoothTransverseStageCover`](../../SquareKit/SmoothTransverseStageCover.lean)
   and
   [`SmoothTransverseRealizationNaturality`](../../SquareKit/SmoothTransverseRealizationNaturality.lean)
   supply principal-support covers and reusable chartwise descent tests.
   For a compatible pair of sections, the supports of the ordinary
   normal-form neighborhoods cover every real reduction. Localizing at these
   supports retains the original algebra maps. `lift_in_normalOpen` uses
   the local factorization to lift both sections with exact projection laws.
5. `comparison_injective` proves global section uniqueness by chart
   separatedness, chart saturation and local full-algebra cancellation.
   `comparison_locallySurjective` proves local existence after simultaneous
   chart covers and the principal normal-form cover. The sheaf local
   bijectivity theorem gives `comparison_isIso` and hence `isPullback`.

Real points are used to prove cover and unit conditions. They are never used
to infer equality of arbitrary algebra elements or generalized sections.
Full faithfulness is used through the existing interpretation interfaces;
it does not supply arbitrary-stage existence in this proof.

## Public lifts and comparisons

`lift`, `lift_first`, `lift_second`, `lift_unique` and `lift_precomp` expose
the universal property for every sheaf test object. At every site object `V`,
`stageEquiv` identifies sections of the realized fiber product with pairs of
sections whose interpreted images agree. `stageLift` is its inverse, with
both projection equations and uniqueness. `stageLift_restrict` and the
identity/composition laws retain the full sections under arbitrary stage
maps, including maps acting nontrivially on nilpotents.

`atlas_isPullback` gives the projection square for arbitrary covering smooth
chart families on all four manifolds. It uses the existing `atlasIso` and
`atlas_naturality`, whose common-refinement identification is already proved
by `ManifoldRealization.atlas_common`. The named
`sourceChart_comparison_first` and `sourceChart_comparison_second` identify
the global comparison on each regular-level chart with its actual principal
parameter and ambient maps. The local square uses the same
`EuclideanOpen.embedding` and principal-open maps as #673, rather than a new
interpretation of open domains.

The #640 `ProjectionSheets` reconstruction and #641 discrete principal-bundle
pullback APIs and consumers remain in the application build. #675's selected
identity-base-change comparison with the sheet-derived atlas remains
available. The new theorem supplies general positive-dimensional transverse
pullbacks; general local-diffeomorphism packaging can be added when a concrete
consumer needs that interface.

## Checked consumers and cost

[`Examples.SmoothTransverseRealization`](../../Examples/SmoothTransverseRealization.lean)
specializes the general theorem to the nonlinear parabola fiber, the
zero-dimensional transverse axes intersection, and an empty fiber with
`p > m+n`. The parabola consumer uses an actual section of the realized
ordinary fiber product with parameter `1+d`, where `d` is nonzero and
square-zero. Its second coordinate is `1+2d`. The stage lift recovers this
same section from its compatible projections; restrictions double and kill
the nilpotent and include their composite.

The nontransverse control is the particular equation `x² = 0`. Its derivative
at zero is not surjective, while the nonzero square-zero algebra element
solves the equation and cannot factor through the ordinary singleton by the
specified map. This explains the role of transversality without asserting
failure for every nontransverse square.

The focused core and API builds use default recursion and kernel limits.
`lift_in_normalOpen` has a declaration-local `maxHeartbeats 400000`: the
200000-heartbeat trial failed while elaborating its final projection
recovery, and the bounded 400000 trial passed. The complete realization
module, including the public stage API, subsequently built in 23 seconds in
the recorded warm focused runs. This is a measured allowance for the chosen
proof, not a claim of a minimal budget. Local
`backward.isDefEq.respectTransparency false` settings expose dependent
interpretation adapters; they do not change theorem statements or trust.
The implementation evidence retains the exact focused logs and statement
inspection. Candidate acceptance additionally requires independent Standards
and Spec review, full fresh-source verification and an exhaustive axiom audit
on the same frozen source.

## Remaining model obligations

This result replaces the historical #97 DEFER status in the
[decision record](transverse-pullback-decision.md). It establishes the
transverse-pullback component for this presentation site and chart-colimit
interpretation. It does not identify the whole construction with a classical
well-adapted model or prove its remaining axioms.

General Weil KL, microlinearity, full well-adaptedness, higher/cohesive
compatibility and isotropy-preserving orbifold comparison retain their
separate scope under [#36](https://github.com/VladimirMarko/conaled/issues/36)
and the current orchestration in
[#666](https://github.com/VladimirMarko/conaled/issues/666) and
[#647](https://github.com/VladimirMarko/conaled/issues/647). Ordinary Lean use
remains direct; source-language syntax is opt-in. The selected quotient-tangent
and source-language soundness results need their own hypotheses and do not
follow merely from this preservation theorem.
