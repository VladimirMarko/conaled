import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Whiskering

/-! Equality transport around selected natural isomorphisms. -/
noncomputable section
namespace SquareKit.Internal.PathTransport
open CategoryTheory CategoryTheory.Functor
universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

theorem whiskerRelabel {L₁ L₂ F₁ F₂ : C ⥤ D} (R : D ⥤ E)
    (p₁ : L₁ = F₁) (p₂ : L₂ = F₂) (η : F₁ ≅ F₂)
    {G₁ G₂ : C ⥤ E} (q₁ : F₁ ⋙ R = G₁) (q₂ : F₂ ⋙ R = G₂)
    (e₁ : L₁ ⋙ R = G₁) (e₂ : L₂ ⋙ R = G₂) :
    isoWhiskerRight (eqToIso p₁ ≪≫ η ≪≫ (eqToIso p₂).symm) R =
      eqToIso e₁ ≪≫ ((eqToIso q₁).symm ≪≫ isoWhiskerRight η R ≪≫ eqToIso q₂) ≪≫
        (eqToIso e₂).symm := by
  subst F₁
  subst F₂
  subst G₁
  subst G₂
  simp

theorem diagonalRelabel (L : C ⥤ D) {R₁ R₂ : D ⥤ E} (S : E ⥤ D)
    (h₁ : R₁ ⋙ S = 𝟭 D) (h₂ : R₂ ⋙ S = 𝟭 D)
    (e₁ : (L ⋙ R₁) ⋙ S = L) (e₂ : (L ⋙ R₂) ⋙ S = L) :
    eqToIso e₁ ≪≫ Iso.refl L ≪≫ (eqToIso e₂).symm =
      isoWhiskerLeft L (eqToIso h₁) ≪≫ (isoWhiskerLeft L (eqToIso h₂)).symm := by
  ext c
  simp

theorem leftEq (L : C ⥤ D) {F G : D ⥤ E} (h : F = G)
    (e : L ⋙ F = L ⋙ G) : isoWhiskerLeft L (eqToIso h) = eqToIso e := by
  subst G
  simp

/-- A cocycle survives independent equality transports at all three vertices. -/
theorem tripleRelabel {A₁ A₂ B₁ B₂ C₁ C₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (a : A₁ ≅ A₂) (b : B₁ ≅ B₂) (c : C₁ ≅ C₂)
    (p₁ : X₁ = A₁) (p₂ : X₂ = A₂) (q₁ : Y₁ = B₁) (q₂ : Y₂ = B₂)
    (r₁ : Z₁ = C₁) (r₂ : Z₂ = C₂)
    (hm : A₂ = B₁) (hf : A₁ = C₁) (hl : B₂ = C₂)
    (em : X₂ = Y₁) (ef : X₁ = Z₁) (el : Y₂ = Z₂)
    (h : a ≪≫ eqToIso hm ≪≫ b = eqToIso hf ≪≫ c ≪≫ (eqToIso hl).symm) :
    (eqToIso p₁ ≪≫ a ≪≫ (eqToIso p₂).symm) ≪≫ eqToIso em ≪≫
      (eqToIso q₁ ≪≫ b ≪≫ (eqToIso q₂).symm) =
    eqToIso ef ≪≫ (eqToIso r₁ ≪≫ c ≪≫ (eqToIso r₂).symm) ≪≫
      (eqToIso el).symm := by
  subst X₁; subst X₂; subst Y₁; subst Y₂; subst Z₁; subst Z₂
  simpa using h

end SquareKit.Internal.PathTransport
