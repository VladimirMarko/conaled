import SquareKit.SheafFamily
import SquareKit.Internal.SheafContexts

/-! Experimental comparison of regular contexts with display-map families.
The existing context and substitution API is unchanged. -/
noncomputable section
namespace SquareKit.Internal.SheafFamilies
open CategoryTheory Limits Opposite SheafContexts
universe u v w
variable {J : Type v} [SmallCategory J] {K : GrothendieckTopology J}
variable {S : Type u} {F P : S → S → Type u}
variable (M : Presheaf.Model.{u,v,w} (J := J) F P)
variable (hM : ∀ s, CategoryTheory.Presieve.IsSheaf K (M.carrier s))

/-- Regular extension is the constant family with the new value first. -/
def extensionIso (s : S) (Γ : List S) :
    context M hM (s :: Γ) ≅ SheafRelation.product (sort M hM s) (context M hM Γ) where
  hom := SheafRelation.lift (term M hM (.var .zero)) (projection M hM)
  inv := ⟨{ app _ := ↾fun x => Env.extend x.1 x.2
            naturality := by
              intro U V f
              ext x t i
              cases i <;> rfl }⟩
  hom_inv_id := by
    ext U ρ t i
    cases i <;> rfl
  inv_hom_id := rfl

theorem extensionIso_projection (s : S) (Γ : List S) :
    (extensionIso M hM s Γ).hom ≫ SheafRelation.snd _ _ = projection M hM := rfl

/-- The previous contextual pullback supplies the chosen family substitution. -/
def substitutionIso {Γ Δ : List S} (σ : Sub F Γ Δ) (s : S) :
    context M hM (s :: Δ) ≅
      pullback (projection M hM (s := s) (Γ := Γ)) (substitution M hM σ) :=
  (context_pullback M hM σ s).isoPullback

@[simp, reassoc] theorem substitutionIso_projection {Γ Δ : List S} (σ : Sub F Γ Δ) (s : S) :
    (substitutionIso M hM σ s).hom ≫ Family.reindex (projection M hM) (substitution M hM σ) =
      projection M hM := (context_pullback M hM σ s).isoPullback_hom_snd

@[simp, reassoc] theorem substitutionIso_comparison {Γ Δ : List S} (σ : Sub F Γ Δ) (s : S) :
    (substitutionIso M hM σ s).hom ≫ Family.comparison (projection M hM) (substitution M hM σ) =
      substitution M hM σ.lift := (context_pullback M hM σ s).isoPullback_hom_fst

/-- Pairing an existing extended-context map recovers it through the comparison. -/
theorem pairing {Γ Δ : List S} (σ : Sub F Γ Δ) (s : S)
    {T : Sheaf K (Type (max u w))} (k : T ⟶ context M hM (s :: Δ)) :
    Family.pair (projection M hM) (substitution M hM σ)
      (k ≫ substitution M hM σ.lift) (k ≫ projection M hM)
      (by simp only [Category.assoc, projection_substitution]) =
        k ≫ (substitutionIso M hM σ s).hom := by
  apply pullback.hom_ext <;> simp [Family.pair, Category.assoc]
end SquareKit.Internal.SheafFamilies
