# Implementation and use assessment

Baseline: `cf0f33ad7cba53bfdf0a688537dc788d4ad63632`. The checkout was clean when inspected. This is the independent implementation/use report for the brief and the complete saved #719/#720 contracts. No tracked files were changed and no Lean checks were executed.

## Recommendation

Build the public presentation around actual object and arrow sheaves, then derive independent-chart maps through their assembly isomorphisms. Use a finite ineffective smooth action as the first geometric instance, with deliberately independent branch diagrams whose index transition varies on disconnected open regions. This is allowed by #719: the example need not lack a global action presentation. Its public overlap and operation proofs must use actual arrow reconstruction, with labels confined to constructing the selected geometry, a checked action recovery, and separating examples.

For the selected instance, instantiate the existing constructed torsor quotient as the completion after proving its comparison with the new arrow presentation. This satisfies the requested construction route without accepting an arbitrary output stack or universal property as an input. The existing quotient has actual torsors, target maps, gluing, and a stack proof. Prove the new unit fully faithful and locally generating, then use `StackificationUniversal.universalEquivalence` unchanged. A new general theory of principal groupoid bundles is not needed to finish the selected-input task, although it would be one way to extend it later.

The smallest concrete example I recommend is the trivial action of `C4` on `Space 1`. It is proper étale with nontrivial ineffective isotropy at every object. It supports the existing nontrivial `C4` clutching torsor with a constant-zero equivariant target, so the new completion can exhibit object descent that has no global chart. Independent branch charts on a punctured interval can exchange two labels on one connected component and preserve them on the other. This gives a transition that is not induced by one global permutation. If the coordinator prefers an object-atlas pullback, use the two-open atlas `(-∞,1)` and `(-1,∞)` of the same line; its arrows are triples `(u,g,v)` with equal underlying base points. That richer instance is feasible but adds manifold and properness transport proofs which are not needed to meet the stated independent-arrow-chart requirement.

## Strongest existing support

The current code already separates the relevant layers in useful ways.

- `Applications/Orbifolds/FiniteActionPresentation.lean:18` defines actual source, target, unit, inverse and composition. `composableEquiv` at line 37 identifies `(G × G) × M` with the equality subtype of composable arrows. `asHom`, `ofHom` and `homEquiv` connect it to Mathlib's `ActionCategory`. Smoothness and properness are proved at lines 83 and 150–179. This supplies geometry and ordinary laws; it does not yet supply the interpreted composable-object comparison.
- `Applications/Orbifolds/LocalBranches.lean:57` defines a diagram by open disjoint pieces and genuine source diffeomorphisms. It does not require global labels or a comparison permutation. `Diagram.assemble_decompose` and `decompose_assemble` retain the arrow itself.
- `SquareKit/SmoothBranchRealization.lean:66` supplies `assemblyIso` from the categorical coproduct of source domains to the realized full arrow region. Its source, target, complete-stage and restriction results have the right strength for arbitrary sections.
- `SquareKit/SmoothBranchRestriction.lean:94` proves the restriction pullback over both endpoint objects. Its current `branchRestriction` preserves one chosen diagram's indices. This is precisely why independently chosen diagrams need a new comparison theorem, rather than an additional instance of the existing restriction theorem.
- `SquareKit/SheafActionPresentation.lean:21` supplies a tested section-category pattern, strict restriction, a pseudofunctor, the quotient transformation and label recovery. Its Hom representation is specifically a group label, so it cannot itself be the new generic geometric presentation.
- `SquareKit/SheafActionQuotientStackDescent.lean:92` constructs the glue functor from actual torsor-and-target descent. `SquareKit/SheafActionQuotientStack.lean:18` establishes the stack property. These are usable constructions, not axioms asserting a completed target.
- `SquareKit/StackificationUniversal.lean:3356` proves the full equivalence of strong-transformation categories, including modifications; its forward functor is actual precomposition. It requires componentwise full faithfulness and singleton-cover local generation, with the target mapping stack in the same `Cat` universes. It does not require the source to be a stack.

## Public interface and builder obligations

The reusable object should contain object and arrow sheaves, source and target maps, units, inverse, and composition on the categorical pullback of target against source, with the ordinary groupoid equations. Its section category at `X` should have objects `X ⟶ O` and arrows `r : X ⟶ A` with both endpoint equations. Composition uses the pullback lift of the pair of arrows. Restriction is precomposition. Give those categories Mathlib `Category` and `Groupoid` instances and obtain the pseudofunctor using the same existing machinery as `SheafActionPresentation.functor`.

I found no existing internal-groupoid-object interface in the inspected Mathlib/category-theory files or project modules. This is search evidence, not an exhaustive theorem-index result. A small sheaf-groupoid interface connected to Mathlib's fiber groupoids and pseudofunctors has a demonstrated consumer; a record whose fields are the final completion equivalence or desired chart coherence does not.

Keep primitive laws separate from derived chart laws. Builders must prove their geometric operations and the realization comparison. They should not also provide inverse/identity/triple-overlap chart coherence: these follow from assembly and actual groupoid operations. Neither properness nor source étaleness belongs in the abstract categorical completion theorem. They belong to the geometric constructor and the existence of its local branch diagrams.

An atlas-pullback instance has object space `U` and arrow space
`{(u,a,v) | p u = s a ∧ t a = p v}`. Its actual composition is `(u,a,v),(v,b,w) ↦ (u,b∘a,w)`, inverse swaps `u,v`, and the unit uses the actual unit at `p u`. The topology and smooth structure should be constructed from open charts or transverse pullbacks; an equality subtype alone is insufficient. Properness follows by the actual anchor base-change square and must be proved for that topology. This option should not be presented as finished merely from `SheafActionRefinement`, which is currently only the sheaf-label presentation.

## Independent charts: exact construction and controls

For diagrams `D` on `U × V` and `E` on `U' × V'`, restrict both to the actual endpoint intersection `(U ⊓ U') × (V ⊓ V')`. Their arrow regions have the same points and inherited smooth structure. Use a named equality or identity diffeomorphism to identify those regions when Lean does not reduce them definitionally. Define the comparison by

`branches(D restricted) --assembly(D)--> jR --decompose(E)--> branches(E restricted)`.

Identity, inverse and triple-overlap laws follow by cancelling `assemblyIso` and its inverse. Triple comparisons must all be restricted to the common triple intersection. Naturality under stage maps follows from naturality of this sheaf map; compatibility with smaller rectangles follows from `assembly_restriction` and `decompose_restriction`. There is no need to choose one permutation of the two index types, and indeed the index sets can have different cardinalities before empty pieces are removed.

Provide an ordinary geometric description too: the `(i,j)` overlap piece is the intersection of the actual arrow pieces. Its source image is open, and the source-coordinate transition is the identity there because both charts invert the same source map. The branch *index* changes by whatever piece contains that reconstructed arrow. A section may meet several such `(i,j)` pieces. The sheaf comparison already handles that cover refinement without replacing a section by one global summand.

For a concrete discriminating example, let `D` have the usual four action-label pieces over a punctured interval. Build `E` by retaining those pieces on the negative component and exchanging two pieces on the positive component. Each new piece is an open union and its source projection is still a diffeomorphism onto the punctured interval. Prove:

1. The new public comparison reconstructs exactly the same actual arrow.
2. A section of one fixed `D` summand meets two different `E` summands.
3. No single global index permutation describes this comparison.
4. Two ineffective arrows with identical endpoints remain distinct after comparison.
5. Restricting to a component makes the relevant label change visible; restricting to an excluded window can make domains empty.

These are proposed constructions, not checked declarations. The current `Examples.SmoothBranchAction.varying_no_summand` shows the existing coproduct can retain locally varying labels, but does not itself compare two independent diagrams. Likewise, the nilpotent controls in `Examples/SmoothBranchRealization.lean` need to be passed through the new comparison to test its stage behavior.

## Interpreting operations is the main geometric gap

The existing `composableEquiv` is only an equivalence of types. `compose_smooth` is stated on product coordinates. To define the interpreted multiplication on `jA ×[jO] jA`, prove the coordinate model is diffeomorphic to the actual smooth equality-subtype pullback, then use its preserved sheaf pullback square.

`SquareKit/SmoothTransversePullback.Realization.isPullback` is the appropriate complete-stage result. For target/source maps that are local diffeomorphisms, transversality follows from the invertibility of one derivative: solve the tangent equation using that inverse. Its constructor uses finite-real models and a regular-level atlas. `SmoothLocalDiffeomorphModel` can normalize the existing finite-action native product model to `Space d`; keep the resulting identity diffeomorphisms explicit rather than assuming the two models are definitionally equal.

`ManifoldRealization.OpenPullback.isPullback` applies to restriction along an open inclusion. `OpenRectangle.restriction_isPullback` applies to endpoint windows. Neither theorem alone identifies the composition domain, whose defining equation matches the middle endpoints. One may prove the needed comparison locally by bisection charts and glue, but the transverse theorem already supplies the stronger all-stage statement once its hypotheses and atlas comparison are discharged.

Define branch-level operations by actual reconstruction, operation, and decomposition in the output chart. Their domains must remember where the operation lands:

- Units require an object in the intersection of the selected source/target windows.
- Inversion swaps endpoint windows and may require a smaller rectangle shared with the chosen inverse chart.
- Composition requires the middle endpoints to agree and the composite to lie in the selected output rectangle. Use that actual pullback/preimage domain rather than assuming every branch pair produces one globally indexed output branch.

Then operation compatibility with independent-chart changes follows by cancelling assembly around the same actual operation. Associativity remains a consequence of the actual multiplication law on composable triples. This also gives stage substitution compatibility without a second pointwise proof on real points.

## Completion and action recovery

The selected geometric presentation still needs an all-parameter comparison with `SheafActionPresentation`, not just a comparison on ordinary principal tests. `SmoothBranchActionComparison.familyBranchEquiv` and `chartBranchEquiv` currently quantify over principal ordinary domains. They are excellent recovery controls but do not on their own give a transformation on every sheaf parameter.

Construct the actual arrow-sheaf identification for the finite action, including both endpoints and the inverse-label convention. A possible proof route is disjoint-open assembly for the global action sheets together with the locally constant sheaf construction, then product/coproduct comparison in sheaves. Alternatively, glue the principal-chart comparisons using the existing chart presentations and arbitrary-sheaf descent machinery. Verify complete-stage existence and naturality; do not infer an all-stage equivalence from real-point bijectivity. I did not find a ready-made all-stage isomorphism `j(G × M) ≅ G_lc × jM` in the inspected files, so it should be treated as an explicit proof obligation.

Once that is established, the new unit sends an object map to the regular torsor with its target map and sends an actual arrow to the recovered quotient arrow. Full faithfulness follows from the actual arrow comparison and `quotientHomEquiv`. Local generation uses the actual total-space cover and tautological trivialization already proved in `SheafActionPresentationRecovery`. An optional atlas pullback adds the cover lifting in `SheafActionRefinement.localLift`, with its hypotheses proved for the chosen atlas.

Arrow descent then follows from `StackObjectPropertyDescent.isPrestack_of_fullyFaithful`, since the constructed quotient is a stack. Thus no prestack quotient step is needed for this input, and no local arrow identifications are introduced. Prove this fact explicitly rather than merely documenting it.

Apply `StackificationUniversal.universalEquivalence` to this unit. Recover source transformations with its `extensionRecovery`; retain the existing identity, composition, parameter and common-refinement comparison theorems. The new branch/atlas refinement maps must be constructed at the presentation level first, preserving reconstructed arrows, then passed into this theorem. For branch changes alone they should induce equivalences over the same arrow sheaf. For an object-atlas refinement they are fully faithful and locally generating even when no global object lift exists.

The output may be the literal existing quotient pseudofunctor specialized to the selected action. That is a constructed output, with its stack proof inherited from actual torsor descent, provided the new unit and geometric comparison are proved. Avoid a generic `CompletionData` record requiring `[output.IsStack]` plus the desired unit properties as unexplained fields. Such a record would merely package the remaining task.

## Dependency order and acceptance evidence

1. Add the independent-diagram overlap comparison and ordinary overlap pieces using existing assembly, independently of groupoid structure. Prove the varying-index and empty-domain controls first.
2. Add the connected sheaf-groupoid section-category interface, actual unit/inverse/composition and restriction functors. Instantiate existing action presentations as a checked recovery, preserving their label convention.
3. Finish the selected geometric composition object, smooth atlas comparison, all-stage pullback preservation and interpretation of operations. Prove equations for the actual maps, then transport groupoid laws.
4. Connect branch operations to that interpretation and prove independent-chart operation compatibility on precise domains. Run nonidentity transition, ineffective-isotropy, partial/empty and stage-dependent controls through those maps.
5. Establish the all-parameter arrow-to-action comparison and the actual unit into the constructed torsor quotient. Prove full faithfulness, local generation and prestackness.
6. Instantiate the full universal mapping equivalence, including modifications and literal precomposition. Build refinement maps independently; prove identity/composition/common-refinement recovery.
7. Carry the existing nontrivial `C4` clutching torsor into the selected trivial action using constant-zero target. Prove its new local presentation cannot have a global chart by the existing no-section obstruction. Recheck already-stack and orbit-erasure controls through the new unit.
8. Check action and smooth/site-change recoveries under their original assumptions, then run the required exact-candidate build, exhaustive audit and independent acceptance reviews. No claim of an internal Myers bridge follows.

The first decisive implementation test is whether the public independent-diagram map handles the component-dependent exchange without introducing a global permutation parameter. The second is the interpreted composable-object pullback on non-real stages. The third is a full-faithfulness proof for the new unit at an arbitrary sheaf parameter. Passing only principal ordinary clients leaves the second and third obligations unresolved.

## Evidence limits and independence

I read the brief, both complete issue contracts, applicable repository/domain/formal guidance, the two named research records, and the cited Lean declarations and nearby constructors. The source baseline and clean checkout were confirmed. I did not read the other two reports, communicate with the other assessors, perform external research, or run Lean. All new constructions and proof sequences above are mathematical proposals informed by inspected code, not checked results.

This fresh subagent task is my only recorded involvement in this assessment. I had no prior exposure to the coordinator's preferred verdict or another assessor's conclusions. Shared model and repository sources do not constitute model diversity. The report supports a concrete completion route; it does not certify implementation effort, elaboration costs, or that the proposed interfaces have passed the required Standards/Spec review.
