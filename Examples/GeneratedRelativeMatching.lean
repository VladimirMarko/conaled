import SquareKit.SmoothQuotientCechFamilyEvaluationRecovery

/-! Independent relative matching recovers the supplied local generated fiber. -/
noncomputable section
namespace Examples.GeneratedRelativeMatching
open CategoryTheory SquareKit SquareKit.Internal.PathTransport
open SheafActionQuotient SmoothOpenSite SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (A : SplitSheaf.Ty X)

/-- Recovery uses the supplied local fiber, including its non-discrete groupoid. -/
example (d : Datum a hΓ A) (x : (relativeMatchingFamily a hΓ hB A).obj d) :
    ((dependentComprehensionEquivalence a hΓ hB A).functor.obj
      (⟨d, x⟩ : Grothendieck (relativeMatchingFamily a hΓ hB A ⋙ Grpd.forgetToCat))).localObject =
      (⟨d.localObject, x.localFiber⟩ : GroupoidModel.Extend
        (interpretedFamily a hΓ hB (SplitSheaf.Ext A))) := rfl

/-- Distinct total arrows survive reconstruction; no thinness premise is used. -/
example {x y : Grothendieck (relativeMatchingFamily a hΓ hB A ⋙ Grpd.forgetToCat)}
    (f g : x ⟶ y) (h : f ≠ g) :
    (dependentComprehensionEquivalence a hΓ hB A).functor.map f ≠
      (dependentComprehensionEquivalence a hΓ hB A).functor.map g := by
  intro he
  exact h ((dependentComprehensionEquivalence a hΓ hB A).functor.map_injective he)

/-- The decomposition also applies after an arbitrary generated finite tail. -/
example {n Δ T} (hT : Typed.TelDeriv.{2} Γ γ n Δ T) :
    Grothendieck (relativeMatchingFamily a (.telescope hΓ hT)
      (.base (.telescope hΓ hT)) A ⋙ Grpd.forgetToCat) ≌
      Datum a (.ext (.telescope hΓ hT) (.base (.telescope hΓ hT))) A :=
  dependentComprehensionEquivalence a (.telescope hΓ hT) (.base (.telescope hΓ hT)) A

/-- Actual evaluation retains the entire total matching datum of each fiber value. -/
example (c : (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A)))
    (x : (b (SmoothQuotientCechLocal.model a A)).obj c) :
    ((SmoothQuotientCechLocal.familyEvaluation a A hΓ hB c).obj x).datum ≅
      (SmoothQuotientCechLocal.fiberTotalEvaluation a A hΓ hB c).obj x :=
  (SmoothQuotientCechLocal.familyEvaluation_total a A hΓ hB c).app x

/-- Recovery is natural for every supplied vertical arrow, not just objects. -/
example (c : (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A)))
    {x y : (b (SmoothQuotientCechLocal.model a A)).obj c} (f : x ⟶ y) :
    ((SmoothQuotientCechLocal.familyEvaluation a A hΓ hB c).map f).matchingArrow ≫
        ((SmoothQuotientCechLocal.familyEvaluation_total a A hΓ hB c).app y).hom =
      ((SmoothQuotientCechLocal.familyEvaluation_total a A hΓ hB c).app x).hom ≫
        (SmoothQuotientCechLocal.fiberTotalEvaluation a A hΓ hB c).map f :=
  (SmoothQuotientCechLocal.familyEvaluation_total a A hΓ hB c).hom.naturality f

/-- The extracted value is the actual generated family-map component. -/
example (c : (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A)))
    (x : (b (SmoothQuotientCechLocal.model a A)).obj c) :
    HEq ((SmoothQuotientCechLocal.familyEvaluation a A hΓ hB c).obj x).localFiber
      (((SmoothQuotientCechLocal.localFamilyMap a A hΓ hB).app c).obj x) :=
  SmoothQuotientCechLocal.familyEvaluation_localComponent a A hΓ hB c x

end Examples.GeneratedRelativeMatching
