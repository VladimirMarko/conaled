import SquareKit.TypeFamilySum
import Examples.SheafFamilies

/-! Experimental dependent sum data: Bool values supported over one base point,
with support reversed by negation and both components retained after pairing. -/
noncomputable section
namespace Examples.SheafSums
open CategoryTheory Limits Opposite SquareKit.Family SquareKit.SheafFamily
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFunctions Examples.SheafFamilies

abbrev sumDisplay := SquareKit.Family.Sum.display falsePoint base

def falseFiber (U : Diamondᵒᵖ) : Fiber sumDisplay U false ≃ Bool where
  toFun x := x.val
  invFun b := ⟨b, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem trueFiber_empty (U : Diamondᵒᵖ) : IsEmpty (Fiber sumDisplay U true) :=
  ⟨fun x => Bool.noConfusion x.property⟩

abbrev tower := pullback base (comparison falsePoint negation)
abbrev towerDisplay := SquareKit.Family.Sum.display (reindex falsePoint negation)
  (reindex base (comparison falsePoint negation))

/-- Public horizontal-pasting and stagewise comparisons retain both coordinates. -/
def towerSections (U : Diamondᵒᵖ) : tower.obj.obj U ≃
    Types.PullbackObj (sumDisplay.hom.app U) (negation.hom.app U) :=
  (((sheafToPresheaf topology (Type)) ⋙ (CategoryTheory.evaluation Diamondᵒᵖ (Type)).obj U).mapIso
    (SquareKit.Family.Sum.substitutionIso falsePoint base negation)).toEquiv.trans
      (sectionsEquiv sumDisplay negation U)

theorem towerSections_base (U : Diamondᵒᵖ) (x : tower.obj.obj U) :
    (towerSections U x).val.2 = towerDisplay.hom.app U x := by
  have h := sectionsEquiv_snd sumDisplay negation U
    ((SquareKit.Family.Sum.substitutionIso falsePoint base negation).hom.hom.app U x)
  exact h.trans (congrArg (fun k => k.hom.app U x)
    (SquareKit.Family.Sum.substitutionIso_display falsePoint base negation))

def trueFiber (U : Diamondᵒᵖ) : Fiber towerDisplay U true ≃ Bool where
  toFun x := (towerSections U x.val).val.1
  invFun b := ⟨(towerSections U).symm ⟨(b,true), rfl⟩, by
    have h := towerSections_base U ((towerSections U).symm ⟨(b,true), rfl⟩)
    simpa only [Equiv.apply_symm_apply] using h.symm⟩
  left_inv x := by
    apply Subtype.ext
    apply (towerSections U).injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (towerSections_base U x.val).trans x.property |>.symm
  right_inv b := by simp

theorem falseFiber_empty (U : Diamondᵒᵖ) : IsEmpty (Fiber towerDisplay U false) := by
  refine ⟨fun x => ?_⟩
  have h := (towerSections U x.val).property
  have hb := (towerSections_base U x.val).trans x.property
  change false = !(towerSections U x.val).val.2 at h
  rw [hb] at h
  exact Bool.noConfusion h

/-- Restrict the first family to its inhabited point. -/
abbrev firstAtFalse := variableTerm falsePoint
abbrev restrictedSecond := reindex base (comparison falsePoint falsePoint)

def secondValue : SheafImage.terminal ⟶ pullback base (comparison falsePoint falsePoint) :=
  SquareKit.Family.pair base (comparison falsePoint falsePoint) truePoint firstAtFalse.val
    (by rw [variable_comparison]; rfl)

def secondAtFalse : Term (reindex restrictedSecond firstAtFalse.val) :=
  (termEquiv restrictedSecond firstAtFalse.val).symm
    ⟨secondValue, pair_reindex _ _ _ _ _⟩

abbrev paired := SquareKit.Family.Sum.pairTerm (reindex falsePoint falsePoint) restrictedSecond
  firstAtFalse secondAtFalse

theorem paired_first : SquareKit.Family.Sum.first _ _ paired = firstAtFalse :=
  SquareKit.Family.Sum.first_pair _ _ _ _

theorem paired_second :
    (SquareKit.Family.Sum.second _ _ paired).val ≫
      (baseIso restrictedSecond (congrArg Subtype.val paired_first)).hom = secondAtFalse.val :=
  SquareKit.Family.Sum.second_pair _ _ _ _

/-- The retained dependent Bool value is true under the sum substitution comparison. -/
theorem paired_value :
    paired.val ≫ (SquareKit.Family.Sum.substitutionIso falsePoint base falsePoint).hom ≫
      comparison sumDisplay falsePoint = truePoint := by
  rw [SquareKit.Family.Sum.substitutionIso_value]
  change (secondAtFalse.val ≫ comparison restrictedSecond firstAtFalse.val) ≫
    comparison base (comparison falsePoint falsePoint) = truePoint
  have h : secondAtFalse.val ≫ comparison restrictedSecond firstAtFalse.val = secondValue :=
    congrArg Subtype.val ((termEquiv restrictedSecond firstAtFalse.val).apply_symm_apply _)
  rw [h]
  exact pair_comparison _ _ _ _ _
end Examples.SheafSums
