import SquareKit.SheafSections

/-! Experimental comparison of constant-family section objects with the
constructed ordinary sheaf exponential. -/
noncomputable section
namespace SquareKit.SheafSections
open CategoryTheory SheafRelation
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ B X Y : Sheaf J (Type (max u v))}

/-- A section of B × Γ → Γ is determined by its B coordinate. -/
def constantParam (Γ B X : Sheaf J (Type (max u v))) :
    Param (snd B Γ) X ≃ (product Γ X ⟶ B) where
  toFun f := f.val ≫ fst B Γ
  invFun f := ⟨lift f (fst Γ X), rfl⟩
  left_inv f := by
    apply Subtype.ext
    ext U x
    exact Prod.ext rfl (congrArg (fun k : product Γ X ⟶ Γ => k.hom.app U x) f.property).symm
  right_inv f := rfl

/-- Constant-family sections and exponential maps classify the same maps. -/
def constantHomEquiv (Γ B X : Sheaf J (Type (max u v))) :
    (X ⟶ sections (snd B Γ)) ≃ (X ⟶ SheafFunction.exponential Γ B) :=
  (homEquiv (snd B Γ) X).symm.trans ((constantParam Γ B X).trans
    { toFun := SheafFunction.curry
      invFun := SheafFunction.uncurry
      left_inv := SheafFunction.beta
      right_inv := SheafFunction.eta })

theorem constantHomEquiv_natural (f : X ⟶ sections (snd B Γ)) (g : Y ⟶ X) :
    constantHomEquiv Γ B Y (g ≫ f) = g ≫ constantHomEquiv Γ B X f := by
  change SheafFunction.curry ((uncurry (snd B Γ) (g ≫ f)).val ≫ fst B Γ) = _
  rw [uncurry_parameter]
  exact (congrArg SheafFunction.curry (Category.assoc _ _ _)).trans
    (SheafFunction.curry_parameter _ g)

/-- The actual internal object of a constant family's sections is Γ ⇒ B. -/
def constantIso (Γ B : Sheaf J (Type (max u v))) :
    sections (snd B Γ) ≅ SheafFunction.exponential Γ B where
  hom := constantHomEquiv Γ B _ (𝟙 _)
  inv := (constantHomEquiv Γ B _).symm (𝟙 _)
  hom_inv_id := by
    apply (constantHomEquiv Γ B _).injective
    rw [constantHomEquiv_natural, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    have h' := constantHomEquiv_natural (𝟙 (sections (snd B Γ)))
      ((constantHomEquiv Γ B _).symm (𝟙 _))
    simpa only [Category.comp_id, Equiv.apply_symm_apply] using h'.symm

theorem constantIso_curry (f : Param (snd B Γ) X) :
    curry (snd B Γ) f ≫ (constantIso Γ B).hom = SheafFunction.curry (f.val ≫ fst B Γ) := by
  have h := constantHomEquiv_natural (𝟙 (sections (snd B Γ))) (curry (snd B Γ) f)
  change curry (snd B Γ) f ≫ constantHomEquiv Γ B _ (𝟙 _) = _
  rw [← h, Category.comp_id]
  change SheafFunction.curry ((uncurry (snd B Γ) (curry (snd B Γ) f)).val ≫ fst B Γ) = _
  rw [beta]

theorem constantIso_evaluation :
    SheafFunction.parameterMap Γ (constantIso Γ B).hom ≫ SheafFunction.evaluation Γ B =
      evaluation (snd B Γ) ≫ fst B Γ :=
  SheafFunction.evaluation_curry _

end SquareKit.SheafSections
