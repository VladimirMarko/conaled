# Contract and foundations assessment

Baseline inspected: `cf0f33ad7cba53bfdf0a688537dc788d4ad63632` (confirmed by `git rev-parse HEAD`). I read both saved issue bodies in full, the shared brief, repository task/domain/architecture/formal guidance, the design-challenge and example-driven-development requirements, and the two cited research documents. I had no prior involvement in these tasks and no exposure to the other assessments. This report contains source inspection and proposed mathematics, not a Lean-checked new construction. No tracked files were edited and no builds or scratch proofs were run.

## Recommendation

Use a sheaf groupoid with represented object and arrow objects as the reusable contract. Derive its groupoids of parameterized sections and branch-coordinate presentations. Select the atlas pullback of a finite ineffective action on the real line, with two overlapping open charts. It exercises object-chart changes, ineffective arrows and arbitrary independent branch decompositions while keeping the geometry explicit. Construct the selected principal-groupoid-bundle category and identify it with the existing torsor quotient by proved descent and recovery. This gives a concrete output construction and lets the existing universal theorem do its intended work.

A finite action itself, equipped with genuinely independent branch diagrams, could also satisfy the literal issue contract. The issue explicitly permits a globally action-presentable example. The atlas pullback adds a useful discriminating requirement: arrows between distinct atlas lifts must remain present. It should be chosen for that additional test, not to claim that a global action presentation is impossible.

The strongest existing evidence is the combination of three APIs. `Diagram` remembers actual open subsets of the arrow manifold and inverse source maps. `SmoothBranchRealization.assemblyIso` identifies its full sheaf coproduct with the actual arrow region. `StackificationUniversal.universalEquivalence` consumes a fully faithful, locally generating unit and constructs the entire mapping-category equivalence. None requires a global choice of branch index at an arbitrary stage.

## Existing guarantees and the missing seam

`Applications/Orbifolds/LocalBranches.lean:55` defines `Diagram` using `piece`, `domain`, `sourceEquiv`, endpoint conditions, disjointness and coverage. It does not require a group or globally labelled arrows. `ProperLocalBranches.exists_diagram` supplies this data from source étaleness, target smoothness and a proper anchor. Its target must remain allowed to be non-étale; `Examples.ProperLocalBranches.constant_target_not_etale` separates that assumption from the groupoid application.

`SquareKit/SmoothBranchRealization.lean:58` defines the actual assembly map, and `assemblyIso` proves its invertibility. `SmoothBranchRestriction.lean:34` currently restricts one chosen diagram, retaining its index. That is the exact missing independent-chart seam. There is already enough information to derive its comparison without introducing a permutation field.

`FiniteActionPresentation.lean` has actual source, target, unit and inverse, a set-level `composableEquiv`, smooth composition in coordinates, and a comparison to Mathlib's `ActionCategory`. It does not yet package the interpreted geometric composable object with its categorical pullback comparison. Reusing those coordinate formulas does not discharge that interpretation obligation by itself.

`SheafActionPresentation.lean:21` and `SheafActionRefinement.lean:20` construct literal chart groupoids. Their arrows retain complete group labels. They use Mathlib `Category`, `Groupoid`, functors, pseudofunctors and strong transformations. A new represented-groupoid presentation should produce these structures, with checked action specializations, rather than build a parallel category or stack hierarchy. My source search found no Mathlib internal groupoid-object structure suitable for this exact sheaf contract; that is evidence for a small local interface, not a claim that all Mathlib alternatives have been ruled out.

## Proposed selected geometry

Take `G = C4`, acting trivially on `M = Space 1`. Use the existing finite discrete smooth group conventions and the locally constant group sheaf. Let `U₀` and `U₁` be the complements of the coordinate values `1/2` and `-1/2`. They cover `M`, have a nonempty overlap, and are principal opens compatible with `SmoothPrincipalAtlas`.

Set `O = ⨿ i, Uᵢ`. Its atlas projection is `p(i,x)=x`. Define the actual arrow space

`A = { (i,g,j,x) | x ∈ Uᵢ ∩ Uⱼ }`.

An arrow has source `(i,x)` and target `(j,x)`. The unit is `(i,1,i,x)`, inverse is `(j,g⁻¹,i,x)`, and composition sends `(i,g,j,x)` followed by `(j,h,k,x)` to `(i,h*g,k,x)`. Define composable pairs as the actual equality fiber of target/source, then prove their equivalence with `(i,g,j,h,k,x)` on the triple intersection. These coordinates retain the intermediate object and both arrow witnesses.

The topology and native smooth structures come from open subsets of finite discrete products with `Space 1`. Both endpoint maps are locally diffeomorphic on fixed discrete components. The anchor is a finite disjoint union of the closed equal-coordinate relation in `Uᵢ × Uⱼ`; use Hausdorffness of `M` to prove closedness, then prove properness of the finite-label projection. Do not infer properness merely from finite fibers. Source-local model transport can put the object, arrow and composable manifolds into the finite-real `ManifoldRealization` models without asserting that product model expressions are definitionally equal.

For interpretation, prove transversality of `t` and `s` from source local diffeomorphisms, then apply `SmoothTransversePullback.Realization.isPullback` (`SquareKit/SmoothTransverseRealization.lean:618`). This theorem proves the all-stage comparison, including nilpotent stages. The explicit composable coordinates must be proved diffeomorphic to its regular-level model, or used through an equivalent smooth universal characterization. Open restrictions and branch overlap regions use `ManifoldRealization.OpenPullback.isPullback` and `OpenRectangle.restriction_isPullback`. An open restriction theorem alone does not identify the unrestricted composable-arrow fiber.

This example has nontrivial ineffective isotropy at every point. It does not exercise a nontrivial action on the base. Retain the existing quarter-turn disk action as a second specialization to test the action convention and nontrivial endpoint motion.

## Primitive contract and derived laws

The reusable sheaf-level data should have object and arrow sheaves `O,A`, endpoint maps `s,t`, unit and inverse maps, and composition on the categorical pullback of `t` and `s`. Include the endpoint, identity, associativity and inverse laws needed to make this an internal groupoid. These are legitimate laws on primitive operations. Do not include independent-chart equivalences, stage naturality, refinement equivalences, stackness or a universal property as fields.

For a parameter sheaf `X`, construct objects `X ⟶ O` and arrows

`{a : X ⟶ A // a ≫ s = m ∧ a ≫ t = n}`.

Composition uses `pullback.lift` and the composition map. Substitution is precomposition. Groupoid laws descend from the primitive laws; substitution compatibility descends from functorial composition and uniqueness of pullback lifts. This produces an ordinary functor into `Cat`, hence the existing pseudofunctor interface. Its input has arrow descent because the arrow fibers are represented by sheaf maps with endpoint equations. Prove that assertion; no prestack step identifying distinct actual arrows is needed.

Keep smoothness, properness and étaleness in the geometric input/realization adapter. The sheaf groupoid and completion arguments do not require these hypotheses. Conversely, a family of groupoids on real points does not suffice: the operation maps and their laws must hold as sheaf maps.

The smooth instance uses `SmoothOpenSite.topology` over `SmoothPresentationSite.Site`; its parameter site is `SheafCover.topology` on `Sheaf SmoothOpenSite.topology Type`, with target `Cat.{0,1}`. A generic sheaf-groupoid contract should match the existing `C : Type u`, `Category.{v} C`, `Sheaf J (Type (max u v))`, and `Cat.{max u v,max (u+1) (v+1)}` conventions. Check any bundle-record universe growth before selecting the public record fields.

## Independent branch comparisons

For diagrams `D` on `U×V` and `E` on `U'×V'`, restrict both to `W=U∩U'`, `Z=V∩V'`. Their actual arrow region is the same subtype of `A`. Define

`transition(D,E) = assembly(D|W,Z) ≫ decompose(E|W,Z)`.

A proof-level identification of the region types may be necessary; its map must be the actual identity on arrows. Derive endpoint preservation and identity, inverse and triple-overlap laws by cancellation of the assembly isomorphisms. Triple-overlap laws compare restrictions to the actual common rectangle, rather than silently composing maps with different domains. Stage naturality follows from sheaf-map naturality; smaller-rectangle compatibility follows from `assembly_restriction` and `decompose_restriction`.

At the ordinary branch level, the intersections `D.piece i ∩ E.piece j` cover each old piece. Their source images are open under the source diffeomorphism and can be empty or proper. They give the required local changes of branch index. One fixed permutation is neither necessary nor justified.

Transport units, inverse and composition through assembly on their actual domains. For inverse, swap endpoint rectangles. For composition, pull back the two branch objects over their common middle endpoint, then restrict the product to where its output lies in the chosen output rectangle. Only there apply the output decomposition. Compatibility with a second chart choice follows from equality after assembly and the actual groupoid law. The resulting comparisons are equalities of sheaf maps on specified restrictions, hence strict at this level. Completion recovery and changes of local descent choices have the natural-isomorphism coherence supplied by the existing stack APIs.

A decisive new control chooses a disconnected overlap and reassigns two branches on only one component. For the ineffective action one may choose the reassignment to agree with the original indexing near the central fiber and swap on a second component. This can still satisfy `Diagram`'s source-equivalence and coverage conditions. Prove that its transition is nonidentity and that no single global index permutation describes it. A mere global `Diagram.reindex` example would not separate the intended result from the old fixed-label API.

## Constructing the output for #720

The selected output can be principal bundles for this concrete atlas groupoid. Define such a bundle using a sheaf `Q` over a parameter `B`, a moment map `Q→O`, a groupoid action and its primitive laws, a locally surjective projection `Q→B`, and the usual principal action-map isomorphism. Its morphisms preserve projection, moment map and action. The principal condition is a torsor requirement, not an assumed completion theorem.

There is a concrete route to reuse the existing action quotient construction. From a `C4`-torsor `P` with invariant map `f:P→M`, form `Q=P×ₘO`. The groupoid action uses the torsor action and changes the atlas lift. Its principal property and local surjectivity follow from the corresponding torsor property and the actual atlas cover. Conversely, a principal selected-groupoid bundle descends along the subgroupoid of arrows `(i,1,j,x)`: these arrows give canonical identifications between atlas lifts, with a cocycle derived from composition. Effective sheaf descent produces `P` with its `C4` action and invariant target. Prove these constructions inverse up to natural isomorphism on all arrows and compatible with parameter substitution.

This is a proposed proof route, not an available theorem. It has a concrete implementation cost: extract and use the existing effective sheaf/family descent machinery for the identity-label subgroupoid. Do not replace it by a field asserting equivalence with the action quotient. The already proved `SheafActionQuotient.Stack.isStack` can then transfer stackness to the constructed principal-groupoid-bundle pseudofunctor through the proved equivalence. Alternatively, explicitly construct the selected descent completion and compare its glue operation with the existing quotient glue; that route must retain the same arrows and recovery evidence.

The unit sends `m:B→O` to its regular groupoid bundle. Prove its full faithfulness by recovering an actual arrow from every regular-bundle map. Prove local generation using the bundle's actual total-space cover and tautological section. Then call `StackificationUniversal.universalEquivalence`. The theorem at line 3356 already gives the whole category of strong transformations and modifications, and its forward functor is restriction/precomposition. No extension of its hypotheses is currently justified. Reuse `extensionRecovery`, `extensionComparison`, `realizationRefinementIso`, and their identity/composition laws instead of taking them as new proof fields.

Independent branch charts compare the same actual arrows and need not change the object atlas at all. Changing the object atlas is a different construction: define the groupoid functor from an actual commuting atlas map and recover arrows over its object endpoints. Prove local generation from that atlas map's local surjectivity. Common refinements come from actual pullbacks/intersection opens. The completed comparison must commute with the unit, parameter restrictions and the retained projection/target maps.

## Acceptance controls and risks

The implementation must exhibit all of the following through public new maps.

- Nonidentity and locally varying independent branch changes, with unit/inverse/composition compatibility and triple overlaps.
- Distinct ineffective arrows with coincident endpoints before and after completion. Orbit-level erasure must fail faithfulness.
- Partial and empty branch domains, and sections at an empty-covered stage. An empty sheaf coproduct must not be asserted to have no sections at every stage.
- A stage-dependent coproduct section and a non-real stage restriction. Existing controls can be transported through the new presentation only with checked compatibility; importing their modules is insufficient.
- Local descent data with no global chart. For the selected trivial `C4` action, reuse the nontrivial `C4` clutching torsor with constant target value, then pass to the new bundle construction. Check the group sheaf comparison explicitly. Alternatively construct an equally strong selected control directly. An absence of a global atlas lift alone is a weaker phenomenon than a nontrivial torsor and should be labelled accordingly.
- The already-stack case, mapping-category equivalence with actual precomposition, and modification recovery.
- Recovery of the old action presentation, original inverse-label convention, atlas refinements and applicable site-change clients under their original hypotheses.

The main mathematical risk is hiding all new work inside a chosen equivalence to the action quotient. The branch transition and operation theorems must be generic in actual diagrams and arrows; the selected quotient equivalence must be proved from concrete bundle or descent constructions. Another risk is assuming source/target endpoint equality determines an arrow; ineffective isotropy expressly refutes that. A third is proving identities only after evaluation at real points: transverse pullback preservation and sheaf-map equalities are required for arbitrary stages.

There is no inspected defect in the existing local-branch or universal-equivalence contracts. The gaps above are new obligations, and the proposed principal-groupoid descent adapter has not been prototyped. Before writing a large completion module, prove the selected arrow-sheaf/pullback comparison and one independent locally varying chart transition, then prototype the identity-label descent reconstruction. Those checks discriminate the proposed route from an unreviewable record of desired results. Full implementation still requires statement review, checked consumers, candidate build/audit and independent Standards/Spec review. This design assessment does not discharge them or establish internal Myers properness.
