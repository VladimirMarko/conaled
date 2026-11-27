import SquareKit.StackificationUniversal
import SquareKit.SheafActionStackification
import SquareKit.SheafActionPresentationRecovery
import Examples.ActionQuotientStack

/-! Object completion is necessary, and it retains ineffective stabilizers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ActionStackification
open CategoryTheory Opposite SquareKit SheafActionQuotient
open SmoothTorsors Orbifolds.QuarterTurn
open ActionQuotientStack

abbrev localPresentation := SheafActionStackification.presentation targetAction
abbrev localFamily := SheafTorsor.Stack.singleton cover

/-- The nontrivial clutching torsor is a locally trivializable descent datum. -/
def localDatum : localPresentation.DescentData localFamily :=
  SheafActionStackification.canonicalData genuine

/-- Its image has the original torsor and the original equivariant target. -/
theorem localDatum_image :
    (StackObjectPropertyDescent.forget
      (SheafActionStackification.globallyTrivial targetAction)).obj localDatum =
    ((Stack.pseudofunctor targetAction).toDescentData localFamily).obj genuine := rfl

/-- There is no globally trivializable object realizing this descent datum. -/
theorem not_effective :
    ¬ ∃ N : (SheafActionStackification.globallyTrivial targetAction).Obj
      (.mk (op SmoothClutching.base)),
      Nonempty ((localPresentation.toDescentData localFamily).obj N ≅ localDatum) := by
  rintro ⟨N, ⟨e⟩⟩
  exact nontrivialTorsor_no_section
    (SheafActionStackification.section_of_effective_canonicalData genuine N e)


/-- Arrow descent holds although the displayed object descent fails. -/
example : localPresentation.IsPrestack (SheafCover.topology (J := SmoothOpenSite.topology)) :=
  inferInstance

/-- The selected input is a prestack, but it is not already a stack. -/
theorem not_isStack :
    ¬ localPresentation.IsStack (SheafCover.topology (J := SmoothOpenSite.topology)) := by
  intro h
  have := localPresentation.isEquivalence_toDescentData localFamily TorsorStack.cover_mem
  exact not_effective
    ⟨(localPresentation.toDescentData localFamily).objPreimage localDatum,
      ⟨(localPresentation.toDescentData localFamily).objObjPreimageIso localDatum⟩⟩

/-- The literal labelled-chart presentation of the same clutching object,
using its actual total-space cover. -/
def chartPresentation : StackificationUniversal.LocalPresentation
    (SheafCover.topology (J := SmoothOpenSite.topology))
    (SheafActionPresentation.transformation targetAction) genuine := by
  let Q := SheafActionQuotient.reindex genuine (SplitSheaf.p genuine.torsor.family)
  let e := SheafTorsor.ofSection Q.torsor (SplitSheaf.q genuine.torsor.family)
  exact {
    domain := SplitSheaf.extension genuine.torsor.family
    cover := SplitSheaf.p genuine.torsor.family
    covering := TorsorStack.cover_mem
    object := ⟨Q.sectionMap (SheafTorsor.sectionOfArrow e)⟩
    comparison := (Q.chartOfTrivialization e).toIso }

def chartFullyFaithful (X : Sheaf SmoothOpenSite.topology Type) :
    (StackDescentTransformation.component
      (SheafActionPresentation.transformation targetAction) X).FullyFaithful :=
  SheafActionPresentation.quotientFullyFaithful targetAction

/-- This cocycle has actual chart objects and compatible group labels. -/
def chartDatum := chartPresentation.sourceData
  chartFullyFaithful

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Labelled chart data on this cover have no global chart realization. -/
theorem chart_not_effective :
    ¬ ∃ N : SheafActionPresentation.Object targetAction SmoothClutching.base,
      Nonempty (((SheafActionPresentation.pseudofunctor targetAction).toDescentData
        (fun _ : Unit => chartPresentation.cover)).obj N ≅ chartDatum) := by
  rintro ⟨N, ⟨e⟩⟩
  let r := chartPresentation.ambientRecovery
    chartFullyFaithful N e
  exact nontrivialTorsor_no_section ⟨SheafTorsor.sectionOfArrow r.hom.torsorArrow⟩

/-- An input that is already a stack is recovered by the same local-generation criterion. -/
def alreadyStackControl (X : Sheaf SmoothOpenSite.topology Type) :
    (Stack.pseudofunctor targetAction).obj (.mk (op X)) ≌
      (Stack.pseudofunctor targetAction).obj (.mk (op X)) :=
  StackificationUniversal.alreadyStackEquivalence
    (η := Pseudofunctor.StrongTrans.id (Stack.pseudofunctor targetAction))
    (fun _ => Functor.FullyFaithful.id _)
    (StackLocalGeneration.locallyGenerating_id
      (SheafCover.topology (J := SmoothOpenSite.topology))) X

open scoped CategoryTheory.Pseudofunctor.StrongTrans

variable (T : Pseudofunctor
  (LocallyDiscrete (Sheaf SmoothOpenSite.topology Type)ᵒᵖ) Cat.{0, 1})
  [T.IsStack (SheafCover.topology (J := SmoothOpenSite.topology))]

/-- Completing the displayed noneffective local input has the full mapping
property for arbitrary target stacks and modifications. -/
def localUniversal : (Stack.pseudofunctor targetAction ⟶ T) ≌ (localPresentation ⟶ T) :=
  StackificationUniversal.universalEquivalence
    (SheafActionStackification.unitFullyFaithful targetAction)
    (SheafActionStackification.locallyGenerating targetAction) T

/-- The independent chart presentation has the same universal property. -/
def chartUniversal : (Stack.pseudofunctor targetAction ⟶ T) ≌
    (SheafActionPresentation.pseudofunctor targetAction ⟶ T) :=
  SheafActionPresentation.universalEquivalence targetAction T

/-- Every modification of chart restrictions extends uniquely to the quotient. -/
def chartModificationEquiv (Φ Ψ : Stack.pseudofunctor targetAction ⟶ T) :
    (Φ ⟶ Ψ) ≃
      (SheafActionPresentation.transformation targetAction ≫ Φ ⟶
        SheafActionPresentation.transformation targetAction ≫ Ψ) :=
  (chartUniversal T).fullyFaithfulFunctor.homEquiv

/-- The equivalence uses the actual chart comparison as its forward functor. -/
example : (chartUniversal T).functor =
    StackLocalGeneration.restriction
      (SheafActionPresentation.transformation targetAction) T := rfl

end Examples.ActionStackification
