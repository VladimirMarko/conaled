import SquareKit.SheafProjectionProduct

/-! Experimental constant-family comparison for projection dependent products.
The constructed general right adjoint is used throughout; the constant-family
case is identified with the previously constructed sheaf exponential. -/
noncomputable section
namespace SquareKit.SheafProjectionProduct
open CategoryTheory SheafRelation
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A Γ B : Sheaf J (Type (max u v))}

/-- Slice maps into a constant family are determined by their value coordinate. -/
def constantMaps (X : Over Γ) (B : Sheaf J (Type (max u v))) :
    (X ⟶ Over.mk (snd B Γ)) ≃ (X.left ⟶ B) where
  toFun f := f.left ≫ fst B Γ
  invFun f := Over.homMk (lift f X.hom) rfl
  left_inv f := by
    apply Over.OverMorphism.ext
    ext U x
    exact Prod.ext rfl (congrArg (fun k => k.hom.app U x) (Over.w f)).symm
  right_inv f := rfl

/-- Hom classification for the constant-family product, natural in X. -/
def constantHomEquiv (A Γ B : Sheaf J (Type (max u v))) (X : Over Γ) :
    (X ⟶ (pi A Γ).obj (Over.mk (snd B (product A Γ)))) ≃
      (X ⟶ Over.mk (snd (SheafFunction.exponential A B) Γ)) :=
  ((adjunction A Γ).homEquiv X (Over.mk (snd B (product A Γ)))).symm.trans
    ((constantMaps ((Over.pullback (snd A Γ)).obj X) B).trans
      (({ toFun := fun f => (parameterIso A Γ X).inv ≫ f
          invFun := fun f => (parameterIso A Γ X).hom ≫ f
          left_inv := by intro f; simp
          right_inv := by intro f; simp } :
        (((Over.pullback (snd A Γ)).obj X).left ⟶ B) ≃ (product A X.left ⟶ B)).trans
        (({ toFun := SheafFunction.curry
            invFun := SheafFunction.uncurry
            left_inv := SheafFunction.beta
            right_inv := SheafFunction.eta } :
          (product A X.left ⟶ B) ≃ (X.left ⟶ SheafFunction.exponential A B)).trans
          (constantMaps X (SheafFunction.exponential A B)).symm)))

theorem constantHomEquiv_value (X : Over Γ)
    (f : X ⟶ (pi A Γ).obj (Over.mk (snd B (product A Γ)))) :
    (constantHomEquiv A Γ B X f).left ≫ fst (SheafFunction.exponential A B) Γ =
      SheafFunction.curry ((parameterIso A Γ X).inv ≫
        (((adjunction A Γ).homEquiv X (Over.mk (snd B (product A Γ)))).symm f).left ≫
          fst B (product A Γ)) := rfl

theorem constantHomEquiv_natural {X Y : Over Γ} (f : X ⟶ (pi A Γ).obj (Over.mk (snd B (product A Γ))))
    (g : Y ⟶ X) :
    constantHomEquiv A Γ B Y (g ≫ f) = g ≫ constantHomEquiv A Γ B X f := by
  apply (constantMaps Y (SheafFunction.exponential A B)).injective
  change SheafFunction.curry ((parameterIso A Γ Y).inv ≫
    (((adjunction A Γ).homEquiv Y _).symm (g ≫ f)).left ≫ fst B (product A Γ)) =
      g.left ≫ SheafFunction.curry ((parameterIso A Γ X).inv ≫
        (((adjunction A Γ).homEquiv X _).symm f).left ≫ fst B (product A Γ))
  rw [(adjunction A Γ).homEquiv_naturality_left_symm]
  have hn : (parameterIso A Γ Y).inv ≫ ((Over.pullback (snd A Γ)).map g).left =
      SheafFunction.parameterMap A g.left ≫ (parameterIso A Γ X).inv := by
    apply (cancel_mono (parameterIso A Γ X).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [parameterIso_natural, Iso.inv_hom_id_assoc]
  change SheafFunction.curry ((parameterIso A Γ Y).inv ≫
    (((Over.pullback (snd A Γ)).map g).left ≫ _) ≫ _) = _
  simp only [← Category.assoc]
  rw [hn]
  simp only [Category.assoc]
  exact SheafFunction.curry_parameter _ g.left

/-- Product of a constant B-family along A×Γ→Γ is (A⇒B)×Γ→Γ. -/
def constantIso (A Γ B : Sheaf J (Type (max u v))) :
    (pi A Γ).obj (Over.mk (snd B (product A Γ))) ≅
      Over.mk (snd (SheafFunction.exponential A B) Γ) where
  hom := constantHomEquiv A Γ B _ (𝟙 _)
  inv := (constantHomEquiv A Γ B _).symm (𝟙 _)
  hom_inv_id := by
    apply (constantHomEquiv A Γ B _).injective
    rw [constantHomEquiv_natural, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    have h := constantHomEquiv_natural (𝟙 ((pi A Γ).obj (Over.mk (snd B (product A Γ)))))
      ((constantHomEquiv A Γ B _).symm (𝟙 _))
    simpa only [Category.comp_id, Equiv.apply_symm_apply] using h.symm

theorem curry_comparison (X : Over Γ)
    (f : (Over.pullback (snd A Γ)).obj X ⟶ Over.mk (snd B (product A Γ))) :
    (adjunction A Γ).homEquiv X _ f ≫ (constantIso A Γ B).hom =
      (constantMaps X (SheafFunction.exponential A B)).symm
        (SheafFunction.curry ((parameterIso A Γ X).inv ≫ f.left ≫ fst B (product A Γ))) := by
  have h := constantHomEquiv_natural (𝟙 ((pi A Γ).obj (Over.mk (snd B (product A Γ)))))
    ((adjunction A Γ).homEquiv X _ f)
  change _ ≫ constantHomEquiv A Γ B _ (𝟙 _) = _
  rw [← h, Category.comp_id]
  apply (constantMaps X (SheafFunction.exponential A B)).injective
  change SheafFunction.curry ((parameterIso A Γ X).inv ≫
    (((adjunction A Γ).homEquiv X _).symm ((adjunction A Γ).homEquiv X _ f)).left ≫ _) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem evaluation_comparison :
    SheafFunction.parameterMap A ((constantIso A Γ B).hom.left ≫ fst (SheafFunction.exponential A B) Γ) ≫
      SheafFunction.evaluation A B =
    (parameterIso A Γ ((pi A Γ).obj (Over.mk (snd B (product A Γ))))).inv ≫
      ((adjunction A Γ).counit.app (Over.mk (snd B (product A Γ)))).left ≫ fst B (product A Γ) := by
  have h := constantHomEquiv_value (A := A) (Γ := Γ) (B := B)
    ((pi A Γ).obj (Over.mk (snd B (product A Γ)))) (𝟙 _)
  rw [Adjunction.homEquiv_symm_id] at h
  change (constantIso A Γ B).hom.left ≫ fst (SheafFunction.exponential A B) Γ = _ at h
  rw [h]
  exact SheafFunction.evaluation_curry _

end SquareKit.SheafProjectionProduct
