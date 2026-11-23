import SquareKit.Internal.Cubical.ConstructorRecomputation
import Examples.CubicalLargeConstructors
import Examples.CubicalConstructorState

/-! Rebuilt constructor comparisons on varying fibers, two nonidentity
substitutions, and the nonreflexive state universe path. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalConstructorRecomputation
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf SmallUniverse
open CubicalLargeConstructors

example : LargeConstructors.piSubstitution naturalsCode varyingCode (𝟙 context) = Iso.refl _ :=
  LargeConstructors.piSubstitution_id _ _

example : productComposite =
    Functor.isoWhiskerLeft twiceSub.mapElements productSuccessor ≪≫
      LargeConstructors.piSubstitution (successorSub ≫ naturalsCode)
        (liftSub (liftedDecode naturalsCode) successorSub ≫ varyingCode) twiceSub :=
  LargeConstructors.piSubstitution_comp _ _ _ _

/-- A caller uses the comparison-composition law to preserve the whole returned
filler along two independently rebuilt Pi comparisons. -/
example :
    (product.filling.reindex (twiceSub ≫ successorSub)).transport
      (Functor.isoWhiskerLeft twiceSub.mapElements productSuccessor ≪≫
        LargeConstructors.piSubstitution (successorSub ≫ naturalsCode)
          (liftSub (liftedDecode naturalsCode) successorSub ≫ varyingCode) twiceSub) =
    (LargeConstructors.pi ((twiceSub ≫ successorSub) ≫ naturalsCode)
      (liftSub (liftedDecode naturalsCode) (twiceSub ≫ successorSub) ≫ varyingCode)).filling := by
  exact (congrArg (fun e => (product.filling.reindex (twiceSub ≫ successorSub)).transport e)
    (LargeConstructors.piSubstitution_comp naturalsCode varyingCode successorSub twiceSub).symm).trans
      (LargeConstructors.piSubstitution_filling _ _ _)

example : pathComposite =
    Functor.isoWhiskerLeft twiceSub.mapElements pathSuccessor ≪≫
      LargeConstructors.pathSubstitution
        (liftSub (interval context) successorSub ≫ projection (interval context) ≫ naturalsCode)
        ((naturalSection 0).reindex successorSub) ((naturalSection 1).reindex successorSub) twiceSub :=
  LargeConstructors.pathSubstitution_comp _ _ _ _ _

/-- The nonreflexive path supplies the line; a larger context adds the parameter
on which successor and twice act. -/
def stateBase : context ⟶ CubicalConstructorState.Ξ :=
  baseProjection ≫ raisedSub (terminalSub CubicalPresheaf.naturals)
noncomputable def stateLine := liftSub (interval CubicalConstructorState.Ξ) stateBase ≫ CubicalConstructorState.a
noncomputable def stateField :=
  liftSub CubicalConstructorState.A (liftSub (interval CubicalConstructorState.Ξ) stateBase) ≫
    CubicalConstructorState.b
noncomputable def statePair := CubicalConstructorState.initialPair.reindex stateBase
noncomputable def stateFunction := LargeConstructors.functionInitialReindex
  CubicalConstructorState.a CubicalConstructorState.b CubicalConstructorState.initialFunction stateBase

noncomputable def pairSuccessor := LargeConstructors.pairRecomputedComparison stateLine stateField statePair successorSub
noncomputable def pairTwice := LargeConstructors.pairRecomputedComparison stateLine stateField statePair twiceSub
noncomputable def pairComposite := LargeConstructors.pairRecomputedComparison stateLine stateField statePair (twiceSub ≫ successorSub)
noncomputable def functionSuccessor := LargeConstructors.functionRecomputedComparison stateLine stateField stateFunction successorSub
noncomputable def functionTwice := LargeConstructors.functionRecomputedComparison stateLine stateField stateFunction twiceSub
noncomputable def functionComposite := LargeConstructors.functionRecomputedComparison stateLine stateField stateFunction (twiceSub ≫ successorSub)

example : LargeConstructors.pairSection
    (liftSub (interval context) (twiceSub ≫ successorSub) ≫ stateLine)
    (liftSub (liftedDecode stateLine) (liftSub (interval context) (twiceSub ≫ successorSub)) ≫ stateField)
    (statePair.reindex (twiceSub ≫ successorSub)) =
      (LargeConstructors.pairSection stateLine stateField statePair).reindex
        (liftSub (interval context) (twiceSub ≫ successorSub)) :=
  LargeConstructors.pairSection_reindex _ _ _ _

example : LargeConstructors.functionSection
    (liftSub (interval context) (twiceSub ≫ successorSub) ≫ stateLine)
    (liftSub (liftedDecode stateLine) (liftSub (interval context) (twiceSub ≫ successorSub)) ≫ stateField)
    (LargeConstructors.functionInitialReindex stateLine stateField stateFunction (twiceSub ≫ successorSub)) =
      Term.map (piReindexIso (liftedDecode stateLine) (liftedDecode stateField)
        (liftSub (interval context) (twiceSub ≫ successorSub))).hom
        ((LargeConstructors.functionSection stateLine stateField stateFunction).reindex
          (liftSub (interval context) (twiceSub ≫ successorSub))) :=
  LargeConstructors.functionSection_reindex _ _ _ _

/-- The two-step pair client retains all three independently selected transports. -/
noncomputable def pairTwoSteps := LargeConstructors.pairRecomputedComparisonTwice
  stateLine stateField statePair successorSub twiceSub

/-- Both Pi adapters and backwards-argument sections survive two rebuilding steps. -/
noncomputable def functionTwoSteps := LargeConstructors.functionRecomputedComparisonTwice
  stateLine stateField stateFunction successorSub twiceSub

/-- Equal endpoints do not identify independently selected native path bodies.
This control concerns arbitrary selections, not failure of the fixed classifier. -/
theorem independent_bodies_not_equal :
    pathApp CubicalConstructorState.carrierPath ≠
      pathApp (homogeneousRefl (term (CubicalGlue.constantLocal terminal Int).code)) := by
  intro h
  exact CubicalConstructorState.carrierPath_nonreflexive (pathApp_injective h)

end Examples.CubicalConstructorRecomputation
