# Ordinary finite-group bundles and represented smooth atlases

This assessment addresses [#637](https://github.com/VladimirMarko/conaled/issues/637), with construction and consumer contracts for [#638](https://github.com/VladimirMarko/conaled/issues/638) and [#639](https://github.com/VladimirMarko/conaled/issues/639). The inspected repository revision is `b272accf03334ff738288198b761e7736f84fcd4`; its Mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The recommended ordinary class is every independently locally trivial smooth principal bundle for a finite discrete group over the existing Type-sized, finite-dimensional, boundaryless real manifold model. There is no identified need to require compactness, a globally charted base, principal-shaped intersections as an additional geometric hypothesis, or a global section. Hausdorffness and second countability can be imposed by clients, but the proposed chart argument does not use them. This is a mathematical scope conclusion and implementation contract, not a claim that the required all-stage gluing theorem already exists in Lean.

## Ordinary input, independent of the sheaf comparison

Fix `G B E : Type`, a finite group `G` with discrete topology, and a natural number `n`. Equip `B` and `E` with topologies, `ChartedSpace (Fin n → ℝ)`, and `IsManifold (ManifoldRealization.Model n) ∞`. Supply a smooth projection `p : E → B`, a left action `G` on `E`, smoothness of each map `e ↦ g • e`, and `p (g • e) = p e`.

For every `b : B`, require an ordinary open neighborhood `U` containing `b` and a diffeomorphism

`τ : p⁻¹(U) ≃ U × G`

over `U`, satisfying `τ (g • e) = (p(e), g * (τ e).2)`. The open submanifolds carry their inherited structures; `G` has the zero-dimensional discrete structure; the product uses the product model. Equivalent sheetwise data can avoid unnecessary identifications between `Space n × Space 0` and `Space n`, but must include both inverse laws and smoothness of the inverse as an actual map on the open total submanifold. Merely supplying a set-theoretic fiber bijection is insufficient.

This gives a local section `s_U(b) = τ⁻¹(b,1)` and `τ⁻¹(b,g) = g • s_U(b)`. Freeness, fiberwise transitivity and surjectivity follow from this contract. They need not be extra fields. A conventional right principal action converts to this convention by `g • e := e · g⁻¹`. Freed's Definition 6.36 and equation (6.37) supply a primary reference for ordinary principal local triviality, using the right-action convention. [Freed, lecture 6](https://people.math.harvard.edu/~dafr/M392C-2012/Notes/lecture6.pdf).

An equivariant target map is additional ordinary data: a second boundaryless manifold `M : Type` in dimension `d`, a smooth left `G` action, and a smooth `F : E → M` with `F(g • e) = g • F(e)`. The principal action on `E` is free; the action on `M` may be ineffective. No target effectiveness assumption is used.

## Checked declarations at the inspected revision

The following inventory records declarations that exist in source, rather than proposed results. This research pass did not run a new acceptance build.

| Source | Existing contract |
|---|---|
| `SquareKit/SmoothOrdinaryPullbackCover.lean`, `openDefining`, `openDefining_locus` | Every open subset of `Fin n → ℝ` is the nonzero locus of a globally smooth defining function. |
| `SquareKit/SmoothManifoldCharts.lean`, `ChartFamily`, `chartDomain`, `coordinateDefining`, `coordinateMap` | Actual Mathlib charts and smooth maps yield represented coordinate domains and smooth restricted coordinate maps. No Hausdorff/countability field occurs. |
| `SquareKit/SmoothChartRealization.lean`, `Charts.realization` | Realization is the sheaf multicoequalizer of all ordinary smooth overlap tests. Its universal property concerns maps out of the colimit. |
| `SquareKit/SmoothChartLocalLifting.lean`, `rawRealization`, `sheafifiedIso`, `rawMap_chart` | The sheaf realization is the sheafification of the presheaf colimit; sections locally lift to charts. |
| `SquareKit/SmoothManifoldFullFaithfulness.lean`, `ManifoldRealization.homEquiv`, `map_reconstruct` | Full correspondence of smooth maps and realization arrows, including equality of whole sheaf arrows. This is not a pullback-preservation theorem. |
| `SquareKit/SmoothManifoldPrincipalMaps.lean`, `principalIso_naturality`, `openMapOfContMDiff` | Principal-open realizations compare naturally with the Euclidean-open embedding. |
| `SquareKit/SmoothOpenOverlap.lean`, `overlap_universal`, `overlap_site_pullback`, `overlap_sheaf_pullback` | Intersections of two principal restrictions of one domain are pullbacks at every stage. The algebraic proof allows arbitrary smooth target algebras. |
| `SquareKit/SmoothOrdinaryCoverLifting.lean`, `covering_local_inclusion` | Every covering sieve pulled back to an ordinary test contains a coordinate inclusion near each ordinary point. |
| `SquareKit/SheafTorsor.lean`, `Torsor.locallySurjective`, `ofSection` | Local existence is part of a torsor; a selected section gives an equivariant isomorphism from the regular torsor. |
| `SquareKit/SmoothRepresentedCover.lean`, `Atlas` | Requires actual site covering, represented pairs and triples, and their categorical pullback witnesses. These are not yet automatically provided for arbitrary manifold realizations. |
| `SquareKit/SmoothManifoldAction.lean`, `representation`, `hat` | Smooth manifold actions and smooth target maps already have interpretation APIs. |
| `SquareKit/SmoothCechRecovery.lean`, `TrivializedOn.extractedDatum`, `extractedRecovery`, `arrowEquiv`, both roundtrips | Extraction, selected recovery and complete-arrow equivalence are available after a represented atlas and its local trivializations have been constructed. |
| `SquareKit/SmoothCechRefinement.lean`, `AtlasMap`, `restrictComparison`, `commonComparison` | Comparison laws consume actual chart refinement maps; they do not construct arbitrary refinements. |

The corresponding Mathlib sheafification infrastructure is in `Mathlib/CategoryTheory/Sites/LeftExact.lean`, including finite-limit preservation of `plusPlusSheaf` and `plusPlusSheafIsoPresheafToSheaf`. This supplies a route for transferring proved presheaf pullbacks to sheaves. It does not assert that an arbitrary colimit of charts has the desired overlaps without checking its equivalence relation.

## All-stage construction for the current chart colimit

For ordinary charts `e_i`, put `U_i = e_i.target`. In chart `i`, the overlap with chart `j` is

`W_ij = e_i.target ∩ e_i.symm ⁻¹' e_j.source`.

It is open, hence `openDefining` represents it. Its left projection is an inclusion; its right projection is the transition `e_j ∘ e_i.symm`. The reverse transition is smooth and inverse on this domain. Triples are the corresponding intersections in the first chart. These are ordinary constructions with no separation assumptions and no use of a good cover by contractible sets.

The missing reusable result should prove that these represented pairs and triples are the actual pullbacks of chart maps into `Charts.realization`. A concrete proof compatible with the existing colimit is:

1. Define the chosen represented overlap diagram and its reversal, diagonal and composition maps using ordinary chart intersections. Prove their identities as ordinary smooth maps, then use the existing embedding to obtain identities at every site stage.
2. Prove the overlap relation on the presheaf coproduct of chart representables is an equivalence relation at every stage. For transitivity, identify the two overlaps incident to chart `j` with principal restrictions of that chart. Their fiber product is the existing `overlap_site_pullback`. This gives the triple needed to compose transitions. The same argument proves uniqueness, using that principal restrictions are monomorphisms.
3. Form the pointwise quotient presheaf by this equivalence relation. The set quotient's equality criterion proves both that each chart map is monic and that each selected overlap is its actual pair pullback. These statements quantify over every finite-presentation stage, including stages with nilpotents.
4. Compare that quotient with the existing presheaf multicoequalizer. Every chosen overlap is one of `Charts.Relation`. Conversely, every ordinary relation test factors through the chosen intersection, since its coordinate images agree. The factor is a smooth map into an open subdomain. Thus the two diagrams impose the same relations at every stage. Establish the comparison by their universal properties and retain its chart equations.
5. Apply left-exact sheafification to the pullback squares, then transport through `Charts.sheafifiedIso`. Chart covering follows from the quotient coproduct and local surjectivity of the sheafification unit. Transport further through `ManifoldRealization.atlasIso` when using a selected trivializing chart family instead of the preferred family.

This identifies the precise theorem missing from the baseline. Pointwise coincidence on ordinary real points proves ordinary coordinate equations, but cannot replace steps 2–5. In particular, nilpotent sections are retained by the quotient and sheafification argument.

For arbitrary smooth base changes, the related reusable obligation is the all-stage inverse-image-open square for `inverseRestriction f q` over `f`. Its ordinary map and commuting square already exist in `SmoothOrdinaryPullbackCover.lean`; its pullback theorem does not. One algebraic route uses the singleton case of `SmoothAlgebra.OpenCover.finite_iff` and `PrincipalCover.covers_iff_zero_locus`: for a finite-presentation stage, an element nonzero at every real point is a unit. Given a map into `U` and a compatible map into the restriction of `V`, the latter makes the target defining function a unit; hence the source inverse-image defining function is nonzero at every real point of that stage and is a unit. Localization lifting then supplies the unique factor. This uses real points to detect invertibility in this specific finite-presentation algebra argument, not to detect equality of arbitrary generalized points. The hypotheses and proof must be checked explicitly.

Published preservation results support the mathematical expectation but do not discharge this Lean obligation. Theorem 2.3 and Corollary 2.4 of *Gluing Manifolds in the Cahiers Topos* concern the Cahiers embedding, transverse products and its particular site; Proposition 2.5 treats open covers. The repository uses its own finite-presentation site and atlas colimit. There is no justification for replacing the above comparison with a citation to those results. [Primary paper](https://arxiv.org/html/1503.07408v1).

During this assessment the implementing agent compiled a scratch helper with statement `∀ (A : Code) (a : Carrier A), (∀ p : Hom (Carrier A) ℝ, p a ≠ 0) → IsUnit a` using `direnv exec . lake env lean /tmp/conaled-637/UnitProbe.lean`. The supplied proof uses `OpenCover.finite_iff` on a singleton family and `isUnit_iff_exists_inv`. An initial unavailable-lemma-name attempt was corrected. This is focused scratch evidence for the proposed helper, not an integrated or audited library result; it establishes no equality-detection principle.

General transverse-pullback preservation remains owned by #97. Open-chart gluing and inverse images of opens are the demonstrated dependencies here. They do not require completing the broader transverse programme.

## Ordinary bundle realization and all torsors are separate constructions

For the ordinary bundle, first shrink each base chart inside an ordinary trivializing neighborhood. This gives a covering chart family. The sheets `g • s_i` produce ordinary open charts on `E` indexed by `(i,g)`. Their overlaps and transitions derive from the supplied diffeomorphisms. Construct the sheaf projection as `ManifoldRealization.map p`; interpret the action with `SmoothManifoldAction.representation`; use `SplitSheaf.ofDisplay` for its slice family. Prove a comparison with the sheaf glued from the local regular torsors by the sheet atlas universal property. The comparison must preserve the actual projection and action. This establishes the all-stage principal condition and local surjectivity, hence the required torsor. Interpret `F` and retain its equivariance and equality with the original map under the comparison. A torsor obtained from a cocycle without this total-space comparison would not fulfill the ordinary-bundle requirement.

Independently, let `P` be any sheaf torsor over a represented Euclidean open. Apply local surjectivity to the tautological base section, then `covering_local_inclusion` at each ordinary point. Pull the obtained lift back to an actual principal restriction. The resulting functions form an ordinary principal cover; each chosen lift gives a section of the restricted torsor. `SheafTorsor.ofSection` provides equivariant local trivializations. Principal intersections give pair/triple pullbacks at all stages. This constructs a represented atlas and `TrivializedOn` as outputs from `P` alone. It has no ordinary total manifold as an input.

After the manifold-chart gluing result, apply this same argument on every base chart and combine the restrictions. It should admit every quotient object over the realized manifold base, since its torsor is locally surjective and its target map needs no further local existence condition. This remains a proposed theorem until its combined covering and overlap proofs are implemented.

## Refinement and comparison contract

For two selected trivializing atlases, construct the common refinement from their ordinary chart intersections. Its maps to both atlases are the actual coordinate inclusions/transitions. For a smooth `f : B' → B`, cover each source chart by inverse images of target chart/trivialization domains and use `coordinateMap`; if needed, subdivide further by local trivializing neighborhoods of the pulled-back bundle. The source restricted chart cover is proved using ordinary covering, then transferred to the actual site. This admits arbitrary smooth maps between the stated manifold models, conditional on implementing the open inverse-image pullback result above. It does not require arbitrary manifold fiber products.

Only after these constructions should #639 use `AtlasMap`, `extractedRecovery`, `arrowEquiv`, and `restrictComparison`. Preserve selected recovery arrows and explicit equality transports. Independent descents compare by the constructed isomorphisms; they are not definitionally identical.

For left local sections write `s_j = k_ij • s_i`. Then the forward ordinary labels satisfy `k_ik = k_jk * k_ij`, matching `SmoothCech.Datum.cocycle`. The regular-torsor transport label is the inverse, as checked by `TrivializedOn.extractedDatum_transition_apply`. A change of local sections produces a gauge transformation by deriving its labels from the two sections; it must not accept that transformation as an input. Include noncommuting labels in the consumers, since abelian examples do not detect multiplication-order errors.

## Hausdorff nontrivial example and controls

The recommended noncompact Hausdorff example is the double cover `p(z)=z²` of `ℂ \ {0}` by itself, with `C₂` acting by `z ↦ -z`. Transport real coordinates through a continuous linear equivalence with `Fin 2 → ℝ` and use the existing open-submanifold realization. The base is a represented Euclidean open, but the bundle is not globally trivial.

Use the two rotated slit planes `U₀ = Complex.slitPlane` and `U₁ = -Complex.slitPlane`, which cover the punctured plane. Sections are `s₀(z)=exp(log(z)/2)` and `s₁(z)=I * exp(log(-z)/2)`. They square to `z`; their negatives give the other sheets. Prove smoothness on these open domains and construct the equivariant diffeomorphisms, including smoothness of their inverse label coordinate. Available primary API evidence is `Complex.contDiffAt_log` in `Mathlib/Analysis/SpecialFunctions/Complex/LogDeriv.lean`, the complex exponential smoothness API, `Complex.cpow_nat_inv_pow` in `Analysis/SpecialFunctions/Pow/Complex.lean`, and `isPathConnected_compl_singleton_of_one_lt_rank` in `Analysis/Normed/Module/Connected.lean`. These are ingredients; no completed local-trivialization construction for this cover was found in the inspected repository.

A no-global-section proof can avoid fundamental groups. A continuous section of a principal discrete bundle gives a continuous label map `E → G` by `e = label(e) • s(p(e))`; continuity follows in each supplied local trivialization. That map is surjective on any nonempty fiber. Connected `E` and nontrivial discrete `G` contradict this surjectivity. Prove this reusable lemma, instantiate connectedness of `ℂ \ {0}`, and use full faithfulness plus the actual realization comparison to exclude a global sheaf section. A nonconstant cocycle is not the required obstruction.

The circle power cover is another viable candidate, but its native Mathlib chart model is `EuclideanSpace ℝ (Fin 1)`, not the repository's `Fin 1 → ℝ`. Mathlib has `Circle`'s analytic Lie-group structure in `Geometry/Manifold/Instances/Sphere.lean`, path connectedness in `Analysis/SpecialFunctions/Complex/Circle.lean`, and `AddCircle.windingNumberIso` in `Topology/Covering/FundamentalGroupCircle.lean`. None is already a smooth equivariant finite power-cover trivialization with the required model. The punctured-plane candidate also supplies the requested noncompact control.

Preserve `SmoothClutchingPrincipal.no_global_section` and `Examples/SmoothCechDescent.quarterTurn_no_section`, including the `onOne`, `onTwo` and `onCommon` refinements. Their doubled-origin parameter is not a Hausdorff example. Keep empty chart intersections, ineffective target actions and the existing noncommuting-label tests as controls through the newly constructed API. Imports alone do not check this connection.

No argument here proves that open chart inclusions are proper. External `IsProperMap`, unrestricted internal `DPProper`, and `Compact.ProperData` remain distinct. Finite principal bundles over suitable ordinary Hausdorff bases can have proper projections, but such a theorem is neither a hypothesis nor an output of this atlas-admission construction.

## Coverage disposition and completion requirements

| Class | Disposition at the inspected baseline | Proposition needed for the requested result |
|---|---|---|
| Independently locally trivial ordinary finite principal bundles on the stated manifold class | Mathematically admitted by the construction above; not yet a checked bundle-to-atlas result | All-stage open-chart gluing; ordinary total-space/action comparison; derived local torsor trivializations. Owned by #638. |
| Every sheaf torsor/action-quotient object over a represented Euclidean open | No identified obstruction; direct local-surjectivity proof available | Construct a principal section cover and its represented atlas, then output `TrivializedOn`. Owned by #638, consumed by #639. |
| Every sheaf torsor/action-quotient object over a realized manifold in the stated class | No identified additional ordinary hypothesis | Combine chart pullback gluing with the preceding local section construction. Owned by #638/#639. |
| Quotient objects over arbitrary sheaf parameters | Open outside this admitted-base theorem; no checked counterexample supplied by this report | An independent represented-open atlas-admission theorem or an appropriately broader chart class for the parameter, plus its pair/triple pullbacks. Do not infer it from torsor local surjectivity. |
| Globally trivial objects only | Insufficient scope, with an existing checked no-section control | The doubled-origin example already excludes replacing all local triviality by global sections. The Hausdorff punctured-plane control remains to be constructed. |

No narrower geometric class is recommended. The remaining prerequisites are formal constructions, not evidence of a mathematical obstruction. If the all-stage proof attempt fails, record the exact failed proposition and retain the requested ordinary class as unfinished; do not rename a supplied finished `Atlas`, `TrivializedOn`, or comparison as an ordinary input.

This draft is source inspection and a mathematical proof plan. It introduces no Lean declarations and claims no newly checked example. #638/#639 must supply implementation sources, statement review, actual derived-atlas consumers, exact-candidate integrated build, exhaustive proof audit, final verification, and independent Standards/Spec review. Acceptance records should state observed costs and failed attempts. The parent #576 remains open until its agreed request is completed or the user explicitly changes the scope.
