import SquareKit.SmoothPrincipalTopology
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Experimental universal base-change squares in the small presentation site. -/
noncomputable section
namespace SquareKit.SmoothPresentationSite
open CategoryTheory CategoryTheory.Limits SmoothAlgebra PresentedLocalization

theorem localization_isPushout {A B : Code} (f : A ⟶ B) (s : Carrier A) :
    IsPushout (localizationBase A s) f (localizationMap f s)
      (localizationBase B ((smoothMap f).toFun s)) := by
  have hu (c : PushoutCocone (localizationBase A s) f) :
      ∃! g : localization B ((smoothMap f).toFun s) ⟶ c.pt,
        localizationMap f s ≫ g=c.inl ∧ localizationBase B ((smoothMap f).toFun s) ≫ g=c.inr :=
    pushout_universal A.equations (representative A.equations s) B.equations
      (representative B.equations ((smoothMap f).toFun s)) (smoothMap f) (by simp)
      (smoothMap c.inl) (smoothMap c.inr) c.condition
  apply IsPushout.of_isColimit
    (PushoutCocone.IsColimit.mk (localization_square f s) (fun c => (hu c).choose)
      (fun c => (hu c).choose_spec.1.1) (fun c => (hu c).choose_spec.1.2)
      (fun c g hl hr => (hu c).choose_spec.2 g ⟨hl,hr⟩))

theorem localization_isPullback {A B : Code} (f : A ⟶ B) (s : Carrier A) :
    IsPullback (localizationMap f s).op (localizationBase B ((smoothMap f).toFun s)).op
      (localizationBase A s).op f.op := (localization_isPushout f s).op.flip

/-- Pullback of a generated principal sieve is exactly the generated image-element sieve. -/
theorem principalSieve_pullback {ι : Type*} {A B : Code} (f : A ⟶ B) (s : ι → Carrier A) :
    (principalSieve A s).pullback f.op=principalSieve B (fun i => (smoothMap f).toFun (s i)) := by
  apply Sieve.ext
  intro Z g
  constructor
  · rintro ⟨W,u,v,⟨i⟩,he⟩
    let hp := localization_isPullback f (s i)
    exact ⟨_,hp.lift u g he,_,⟨i⟩,hp.lift_snd u g he⟩
  · rintro ⟨W,u,v,⟨i⟩,he⟩
    refine ⟨_,u ≫ (localizationMap f (s i)).op,_,⟨i⟩,?_⟩
    rw [Category.assoc,(localization_isPullback f (s i)).w,← Category.assoc,he]


end SquareKit.SmoothPresentationSite
