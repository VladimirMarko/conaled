# Alternatives and generality assessment

Baseline: `cf0f33ad7cba53bfdf0a688537dc788d4ad63632` (confirmed HEAD). I read the shared brief and both complete issue contracts, repository guidance, the named research notes, and the source declarations identified below. I have no prior involvement in this implementation or exposure to the other assessments. This is an independent paper-and-source assessment, not a Lean-checked implementation or acceptance review. No tracked files were changed and no Lean builds were run.

## Recommendation

Separate the reusable groupoid presentation and independent branch comparison from the selected completion construction. Use an atlas pullback of a finite ineffective action as the geometric example. Prove the new presentation's recovery of the existing action refinement from the actual object/arrow maps. Then instantiate the existing constructed torsor quotient for this selected presentation, using the recovered full faithfulness and local generation to apply `StackificationUniversal.universalEquivalence`.

This recommendation is conditional on completing the actual independent-chart interface described below. Merely renaming `SheafActionRefinement`, or proving another identity-on-label theorem for fixed summands, would leave #719's principal addition undelivered. The restriction to an action-recoverable example belongs to the completion specialization, not to the generic branch transition API or the definition of groupoid presentations.

The strongest evidence for retaining the existing completion machinery is its precise boundary: `SquareKit/StackificationUniversal.lean` takes a fully faithful, locally generating strong transformation and constructs extension on transformations with modification-level recovery. It does not assume the universal property it concludes. `SquareKit/SheafActionQuotientStackDescent.lean` constructs effective objects, arrows, and local recovery from torsor descent. The requested tasks explicitly permit selecting an example and instantiating an output construction. These are useful checked ingredients, and neither depends on geometric effectiveness.

If the intended output must itself have principal bundles for the new groupoid as its object type, implement the direct groupoid bundle route instead. That is mathematically sound, but it is extra construction work beyond using the already constructed action torsor stack as the associated stack of the selected groupoid. The final documentation must say which object type was constructed; an equivalence of mapping categories alone must not be advertised as a concrete principal-groupoid-bundle implementation.

## A geometric example with explicit obligations

A small proposed example is the trivial `C4` action on the real line, pulled back to the open atlas

- `U₀ = (-∞,1)` and `U₁ = (-1,∞)`;
- object manifold `U = U₀ ⊔ U₁`, with `p : U → ℝ` the inclusion on each summand;
- actual arrow manifold `R = {(u,g,v) | p(u)=p(v)}`, with `g : C4`;
- `s(u,g,v)=u`, `t(u,g,v)=v`, `e(u)=(u,1,u)`, `inv(u,g,v)=(v,g⁻¹,u)`;
- composition `(u,g,v)` followed by `(v,h,w)` is `(u,h*g,w)`.

Its ordinary charts are indexed by `(i,g,j)` on the open set `Uᵢ ∩ Uⱼ` of the real line. The actual source and target include the same coordinate in different atlas summands. The atlas overlap has arrows between distinct objects, and every object has nontrivial ineffective isotropy. This is a proper étale groupoid with noncompact object manifold. Properness can be proved either by base change of the finite-action proper anchor, or directly because the equal-coordinate relation is closed in `U×U` and the label set is finite. The atlas map itself is not proper, and its properness must not be used as a premise.

The finite-action arrow model and its operations already have relevant pieces in `Applications/Orbifolds/FiniteActionPresentation.lean`: `composableEquiv`, `source_etale`, `target_etale`, `unit_smooth`, `inverse_smooth`, and `compose_smooth`. Those do not already prove the displayed atlas-pullback groupoid's composable-pair manifold comparison. That comparison is new work.

The composable-arrow manifold is charted by `(i,g,j,h,k,x)` on `Uᵢ∩Uⱼ∩Uₖ`. Its comparison with the subtype `{(r,q) | t r = s q}` must be a diffeomorphism, not just `Equiv`. Interpret it as the sheaf pullback needed for composition. `SquareKit/SmoothManifoldOpenPullback.lean` supplies `OpenPullback.isPullback` for each open intersection. Alternatively, étaleness supplies the derivative surjectivity required by `SmoothTransversePullback.Realization.isPullback`; verify the finite-real models and the diffeomorphism from the chosen chart model to that theorem's regular-level model. The arrow model adapter is not itself a proof that realization preserves composable pairs.

This fully ineffective example meets the stated ineffective-isotropy requirement. If a separate nontrivial action is desired, replace it by `C4×C2` acting on the disk through the `C4` factor, with the existing principal-open atlases. That adds product-group/torsor setup and disk geometry without changing the required shared arguments. The existing quarter-turn disk by itself is effective despite its nontrivial stabilizer at the origin, so it cannot alone supply the ineffective-isotropy control.

For the no-global-chart control, use the existing nontrivial `C4` clutching torsor with the constant equivariant map to zero in the trivial real-line action. Any realization by a global source chart would trivialize that torsor. The no-section result is already used in `Examples/ActionStackification.lean`, but its current `targetAction` is the action on the clutching total sheaf (`Examples/ActionQuotientStack.lean:16`), not the proposed real-line action. A new constant-target object and its connection to the public completion map are necessary; simply citing the old control does not exercise the new maps.

## Independent charts need a common arrow region, not matching labels

The existing `Orbifolds.LocalBranches.Diagram` already contains enough primitive data. Its fields in `Applications/Orbifolds/LocalBranches.lean:50` are disjoint open arrow pieces, source diffeomorphisms, endpoint membership, and coverage. It has no global-label field. `Diagram.equiv` and `SmoothBranchRealization.assemblyIso` recover actual arrows.

Given independent diagrams `D` and `E` over `(U,V)` and `(U',V')`, restrict both to `(U∩U',V∩V')`. Their realized arrow regions are canonically the same open arrow submanifold (allow a comparison isomorphism when subtype proofs prevent definitional equality). Define the branch transition by

`C_D → R_overlap → C_E`, using `assemblyIso D` followed by the inverse of `assemblyIso E`.

An overlap of individual pieces is `D.piece i ∩ E.piece j`. Pulling it through either source diffeomorphism gives the actual partial source domain of that comparison. Such domains can be proper or empty and can split a single source domain. Identity, inverse and triple-transition laws follow by cancellation of assembly/decomposition; endpoint preservation follows from the existing endpoint laws. Stage naturality follows because these are sheaf maps. Rectangle naturality follows from `assembly_restriction` and `decompose_restriction` in `SquareKit/SmoothBranchRestriction.lean`. These are derivations to implement, not new coherence fields to ask builders to supply.

A decisive proposed control uses a disconnected source window `W₋ ⊔ W₊` inside one atlas chart. In diagram D, use fixed `C4` branches. In diagram E, retain those branches on `W₋` and multiply the branch indexing by a nonidentity element on `W₊`. Each E piece still maps diffeomorphically by source onto the disconnected window. D and E assemble the same arrow region, but their transition cannot be one fixed permutation of the indices: evaluate at one point of each component. A constant actual ineffective arrow has different E indices on the two components. This distinguishes the required construction from a fixed `Diagram.reindex` result and makes the existing stage-dependent controls relevant.

Do not confuse that index change with groupoid multiplication. For example, the unit need not live in the E summand named `1` on both components. Define charted units, inversion and multiplication by assembling the actual arrows, performing the actual operation, and decomposing in the selected output diagram. Prove transition compatibility by cancellation on the relevant pullback/open domain. It is a worthwhile separating test to prove that a naive indexwise unit or multiplication fails for the switched diagram.

The user contract asks for comparisons over actual endpoint overlaps, including further refinements if needed. A theorem only covering equal endpoint rectangles is a useful intermediate lemma, not the public final result. Similarly, finite branch indices do not identify all generalized sections with a global dependent sum. The categorical coproduct construction and its arbitrary-stage sections must remain in this argument.

## Reusable presentation boundary

Use a sheaf groupoid with object sheaf O, arrow sheaf A, source and target, unit and inverse, and composition on the actual sheaf pullback `A ×[O] A`. Require primitive operation laws and prove the categories of generalized elements from them. At parameter X, objects are `X ⟶ O` and arrows are `X ⟶ A` with both endpoint equations. Restriction is precomposition. This gives ordinary Mathlib `Groupoid` fibers and a `Cat`-valued pseudofunctor usable by the existing descent hierarchy.

A search of the installed Mathlib and local SquareKit sources did not locate an existing internal-groupoid-object interface. Mathlib's `CategoryTheory.Groupoid` is the ordinary fiber category interface. This supports a small new sheaf-operation interface, but the search is not proof of global absence. Prefer this interface over a second hand-built stack hierarchy. Keep properness and étaleness in the geometry/application assumptions: arrow descent and completion do not use them.

For the selected atlas groupoid, derive the comparison with `SheafActionRefinement.Object` by evaluating the arrow triple and proving its label/endpoints determine it. The conventional geometric arrow `u → v` has `v=g•u`; the existing action presentation uses a label k satisfying `k•v=u`. Hence the recovery label is `g⁻¹`, even when the trivial action makes the endpoint equations insensitive to the distinction. Check composition against `h*g` and check the inverse-label convention with a noncommutative action specialization or an explicit existing convention theorem. `C4` alone cannot detect multiplication-order reversal.

Arrow descent is expected to hold immediately: the hom presheaf is maps into the arrow sheaf with two endpoint equations, and compatible maps glue uniquely across locally surjective covers. Prove this directly or transfer the property through the constructed fully faithful comparison in the selected case. No arrow-identification prestack step should be invented for an input whose arrows are already sheaves.

## Completion alternatives and exact scope

| Route | Primitive input and construction | Benefit | Obligations and limit |
| --- | --- | --- | --- |
| Selected recovery to action torsors | Actual action, atlas map, proved atlas coverage; construct the groupoid and its comparison; instantiate existing torsor quotient | Reuses existing effective descent, local generation and full mapping-category theorem | Only selected action-recoverable presentations obtain this output. Must prove recovery from actual arrows; an assumed equivalence/fully faithful record is circular evidence |
| Principal sheaf groupoid bundles | Sheaf over X with anchor to O, groupoid action, locally surjective projection, and principal action comparison | Direct geometric output for every sheaf groupoid admitting this construction; anchors and arrows visible | Construct bundle gluing and prove action/principality descend. Existing group torsor proofs need extraction or adaptation. A group torsor has one global group; a groupoid bundle generally does not |
| Explicit descent completion | Prestack plus covers and cocycles; objects are cover-indexed descent data, arrows compatible maps on overlaps | Does not assume action recovery and reuses Mathlib descent data; covers naturally express independent charts | Must define arrows across different covers, composition via refinements, stack gluing, universes and substitution. Merely taking `F.DescentData p` for one fixed p does not complete F |

The general descent alternative is not speculative mathematics. Stacks Project Lemma 8.8.1 describes first sheafifying morphisms, then adjoining cover-indexed descent objects with compatible overlap morphisms. It applies to a fibred category on a site; the sheafified-arrow step is unnecessary for an existing prestack. Its recipe does not remove the Lean obligations for composition and effective descent. [Stacks Project, Lemma 8.8.1](https://stacks.math.columbia.edu/tag/02ZN).

As external context, quotient-stack construction starts from the groupoid-valued functor of generalized points, and action quotients are its special case. This supports retaining an action-independent presentation interface. The cited setting is groupoids in algebraic spaces over B and the fppf site, so it does not itself prove anything about the repository's smooth realization or smooth site. [Stacks Project, Section 78.20](https://stacks.math.columbia.edu/tag/044O).

The action torsor comparison provides a useful independent convention check: the geometrical arrow is sent using right translation by its inverse, preserving the target map. This is an algebraic-space result, not an imported proof for the smooth site. [Stacks Project, Proposition 95.15.3](https://stacks.math.columbia.edu/tag/04WM).

The recommended selected recovery route should leave the direct principal-groupoid and descent routes available. Their mathematical generality is a benefit, not a defect caused by lacking a local adapter. A generic new completion framework is not required to satisfy the selected-example contract, and a selected completion must not be described as arbitrary-input stackification.

## Acceptance sequence and remaining uncertainty

1. Prove the generic two-diagram comparison over intersections, including the switched disconnected control. This settles whether the chosen public interface really goes beyond restriction/reindexing of one diagram.
2. Construct the actual atlas groupoid, its composable-pair manifold and realization comparison. Export its sheaf groupoid and operation-preserving generalized-point presentation. Audit the source/target orientation here.
3. Derive recovery to the existing action refinement, full faithfulness and singleton-cover local generation from the atlas map. Retain an explicit unit into the independently constructed torsor stack. Confirm prestack descent before selecting any prestackification step.
4. Apply `StackificationUniversal.universalEquivalence`; show its forward functor is literal precomposition. Derive identity/composite/common-refinement completion comparisons using the existing refinement and extension recovery machinery, including modifications.
5. Route the new no-global-chart, nonidentity chart transition, ineffective-isotropy, partial/empty-domain, stage-dependent, already-stack and orbit-erasure controls through the public maps. Recover existing action clients under their original assumptions. In particular, generic action recovery must not acquire the example's finite, trivial-action, real-line or atlas hypotheses.

No mathematical obstruction to these steps was found. The new work is substantial and the suggested formulas have not been checked in Lean. The main unresolved implementation risks are manifold/model compatibility for composable arrows, transporting the current action descent API through a new presentation equivalence, and universe sizes for a general descent completion if that alternative is chosen. These are distinct from a demonstrated failure of the mathematics. #723's based-cartesian helper can shorten transport arguments, but it cannot replace these geometric or effective-descent proofs.
