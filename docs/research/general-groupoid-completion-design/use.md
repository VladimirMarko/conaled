# Implementation and use assessment for #727

Recommend principal groupoid bundles, represented by split sheaf families with an anchor and dependent arrow action. Retain `SheafGroupoid.Operations` and its existing `Laws` as the input. Build the new stack and unit from these data, then recover action quotients by comparison. Existing code supports this route more directly than a category of arbitrary cover presentations modulo refinement.

The strongest evidence is `SplitSheafDescent`: it constructs the descended family and maps without assuming effectiveness. Its `family`, `evaluationIso`, `Map.descend`, and canonical recovery cover most of the underlying sheaf work. `SheafActionQuotient.Descent.descendMap` already descends an extra map into a sheaf by effective epimorphisms. `StackificationUniversal.universalEquivalence` already supplies the requested mapping-category equivalence with actual precomposition, once full faithfulness and local generation have been proved. These are concrete reuse opportunities, not merely analogous proofs.

Assessment concerns base commit `48ebca7024a29c8eef8d9452a3854f63d044d082` and the supplied issue snapshot. I read the brief, issue, relevant repository guidance, concrete modules named below, and pinned local Mathlib sources. I did not read other assessments, modify target code, delegate, or execute a Lean experiment. Proposed new proofs below are mathematical construction plans, not checked declarations.

## Input, sections, and sizes

Keep arbitrary `C : Type u`, `[Category.{v} C]`, `J : GrothendieckTopology C`, and sheaf values in `Type (max u v)`, as in `SheafGroupoid.Operations`. The output is a pseudofunctor on the category of those sheaves, with `SheafCover.topology`, whose singleton covers are locally surjective sheaf maps. This is distinct from asserting a stack on the original site. Smooth representability, properness, and étaleness do not belong to the construction's input.

The existing split-family and torsor constructors use this value universe and fibers in `Cat.{max u v, max (u+1) (v+1)}`. A principal-bundle construction should aim to retain those sizes. No skeleton or larger collection of cover presentations is needed. Confirm elaborated universe parameters in a first checked constructor; this report has not run that check.

There is an exact bridge from the existing generalized-arrow laws to the sectionwise groupoids needed by split families. Put `s := max u v` and

```
YJ U := (presheafToSheaf J (Type s)).obj (uliftYoneda.{u}.obj U).
```

Compose `(sheafificationAdjunction J (Type s)).homEquiv` with `CategoryTheory.uliftYonedaEquiv` to obtain `(YJ U ⟶ F) ≃ F.obj.obj (op U)`. The pinned Mathlib `Sites/LeftExact.lean:313` supplies `HasSheafify J (Type (max u v))`. `Sites/Sheafification.lean:80` gives the adjunction; `CategoryTheory/Yoneda.lean:914` gives the lifted Yoneda equivalence, with naturality and composition lemmas at lines 927 and 932. Transfer `G.Object (YJ U)` and its arrows through these equivalences. Apply `G.Laws` to derive sectionwise identity, composition, inverse, and associativity. Restriction is induced by `YJ.map`, and agrees with the original sheaf maps by those naturality lemmas. No new sectionwise laws should be accepted from callers.

Do not use `J.yonedaEquiv` for the general bridge: its declaration in `Sites/Subcanonical.lean:33` uses subcanonicity. That would unnecessarily strengthen the present input. Another valid implementation is pointwise evaluation of the categorical pullback: `Sites/Limits.lean:149` supplies `createsLimitsOfShape` for `sheafToPresheaf`, and `Limits/Types/Pullbacks.lean:70` supplies `PullbackCone.IsLimit.equivPullbackObj`. Categorical laws can first be extracted from `G.Laws` on universal composable-arrow sheaves and then evaluated. The sheafified Yoneda route looks smaller for transferring the already constructed groupoids; the pointwise pullback route may give better reduction behavior. Check the bridge and a regular bundle before choosing between these encodings.

## Concrete construction and obligations

A bundle over `X` consists of a `SplitSheaf.Ty X`, an anchor to `G.objects`, an action by arrows whose source is the current anchor, identity/composition/naturality laws, principality, and local surjectivity of the family display. Principality says that for any two sections `p,q` in the same base fiber, there is exactly one arrow from `anchor p` to `anchor q` sending `p` to `q`. Empty section fibers are allowed. A global section or global chart is not part of the object.

Arrows are all anchor-preserving equivariant family isomorphisms. For a useful builder API, also prove every anchor-preserving equivariant family map between principal bundles is invertible, following the existing torsor `EquivariantMap` route. Supplying an isomorphism as the initial arrow representation is acceptable only if the equivalence with all such maps is proved, so callers do not acquire redundant inverse obligations.

Use split-family reindexing for substitution. This is the existing mechanism behind strict `restriction_id` and `restriction_comp`, and avoids introducing a new layer of chosen pullbacks into each client.

For an object map `m : X ⟶ G.objects`, its regular bundle has sections the arrows `m(x) → n`, with anchor `n`, and action by postcomposition. The unit arrow associated to `f : m → m'` maps `h : m → n` to `f⁻¹ ≫ h : m' → n`. The inverse here matters for compatibility with the existing left-torsor convention: `SheafGroupoidAction.toPresentationArrow` already uses inverse labels. Evaluate an equivariant map on the identity section to recover its unique input arrow. Principality proves that evaluation recovers the whole map, giving full faithfulness. The bundle's own total-space display, with its tautological section, gives singleton-cover local generation and a regular-bundle comparison.

Effective descent proceeds through these specific steps:

1. Forget a bundle descent datum to `SplitSheafDescent.Datum`. Reuse `family` and `evaluationIso` for the descended family.
2. Descend the anchor using `SheafActionQuotient.Descent.descendMap` and the anchor-preserving transition maps. Move this generally useful map-descent helper to a neutral module if importing the action quotient would create the wrong dependency direction; retain compatibility names for existing clients.
3. Define the dependent groupoid action on compatible sections at every restriction stage. The anchor comparison supplies the source equation. Equivariance of transition maps proves compatibility. Derive action laws by evaluation, using the original groupoid laws.
4. Prove principality locally and glue the unique connecting arrows using the arrow sheaf. A cover need not have a section at the current stage, so choosing one cover lift globally is invalid. The existing torsor local-descent proofs show where sheaf separation and local existence enter, but their unrestricted group action does not directly prove the new dependent-action claim.
5. Reuse `SplitSheafDescent.Map.descend` for maps, proving anchor preservation and equivariance locally. Reuse canonical recovery and local evaluation to establish the equivalence with Mathlib descent data.
6. Follow `SheafTorsorStackDescent` and `SheafActionQuotientStack` to pass from split displays to arbitrary locally surjective singleton covers and then `SheafCover.topology`. Derive the source prestack from unit full faithfulness and the proved target stack, as current completion already does.
7. Apply `StackificationUniversal.universalEquivalence` unchanged. Its final declaration proves the forward functor is `StackLocalGeneration.restriction`, which is actual precomposition, and its arrows are modifications. Do not reconstruct that proof.

The new mathematical burden is the dependent action and its principal condition. Copying all torsor descent proofs under new names would obscure the existing reusable family construction.

## Recovery and consumer

For an action groupoid, a principal groupoid bundle becomes an ordinary group-sheaf torsor by letting `g` act through the arrow with source the anchor and label `g`; the anchor becomes the equivariant target map. Conversely, a torsor and equivariant target map define the dependent action. Prove these maps on objects and every arrow, plus reindexing, unit, and mapping-category compatibility. This direct comparison discharges the requirement that original action clients retain their assumptions. It also exposes the inverse-label convention before it becomes hidden in universal-property choices.

For atlas changes, first construct an actual represented pullback groupoid: object sheaf `U`, arrow sheaf the pullback of `(source,target)` along `(atlas,atlas)`, with operations recovered by `Chart.isPullback`. Existing `Chart.canonical`, `arrowEquiv`, `comp_recovery`, `inverse_recovery`, and `ident_recovery` provide the required ingredients. `SheafGroupoidChartPresentation` currently constructs a pseudofunctor of chart objects; it does not itself expose this new represented `Operations` input. Filling that gap is required for the selected consumer.

Construct this input for `Examples.ActionMorita.atlas`, `otherAtlas`, and `commonAtlas`. Feed each represented groupoid to the new general completion before invoking its comparison with the action quotient. Existing common-atlas maps induce actual object and arrow maps through the pullback property. Retain the independent-coordinate change and atlas identity/composition comparisons in `SheafGroupoidChartPresentation`; extend them to the represented inputs and completed stacks through the new units. The existing chart recovery equations and modification comparisons are reusable proofs, but a comparison through the old action completion alone is insufficient input construction.

The consumer has distinguishing observations already available: `originObjects_distinct`, `originArrowEquiv`, `origin_arrow_count`, and `distinct_origin_labels` at `Examples/ActionMorita.lean:98–126`. Preserve the arrows between different lifts and all four origin labels after the new unit. Test ineffective isotropy separately using the action at lines 170–187, since quarter-turn origin isotropy alone does not exhibit a globally ineffective action.

Use the existing nontrivial torsor from `Examples/GroupoidCompletion.lean` or `Examples/IndependentBranchCompletion.lean` through the proved action recovery to obtain local data with no global chart for the new construction. For the already-stack control, use a represented discrete sheaf groupoid, prove its source stack property, and apply `StackificationUniversal.alreadyStackEquivalence` to the actual new unit. Its functor is the unit component, not an unrelated identity functor.

## Alternative, risks, and discriminating checks

A completion whose objects are covers plus `G.pseudofunctor.DescentData` is plausible. Mathlib's `Sites/Descent/DescentData.lean` already supplies objects, cocycles, arrows, and same-sieve comparison. It does not in the inspected files construct stackification over all changing covers. Such a route still needs all arrows between different cover presentations, refinement independence, descent of those objects, and size accounting for the cover choices. Principal bundles turn cover dependence into a sheaf already handled by `SplitSheafDescent`. Keep descent data as an input/output interface rather than the primary global object representation unless a checked trial demonstrates a smaller complete proof.

Established gaps in current code are the action dependency of `SheafGroupoidCompletion`, absence there of a general bundle construction, and lack of a represented atlas-pullback `Operations` constructor in the inspected chart presentation module. These are scope gaps, not unsoundness findings.

Implementation risks are dependent endpoint transports, the left-action inverse convention, and duplicate descent proofs. The first useful checked experiment should prove the general section bridge without subcanonicity, construct regular bundles, and recover arrows by identity evaluation. Follow it with family-plus-anchor descent for a single split cover. These checks distinguish a practical encoding from a plausible paper plan before building full stack packaging.

All new constructors and claims still need statement review, checked applications, integrated build and exhaustive axiom audit, and independent acceptance review. This assessment establishes a reuse plan and its remaining obligations; it does not certify those unimplemented proofs.
