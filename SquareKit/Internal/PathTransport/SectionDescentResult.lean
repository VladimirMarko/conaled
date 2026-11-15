import SquareKit.Internal.PathTransport.NormalizedSectionDescent

/-! A selected section reconstruction together with its recovery and uniqueness
laws, for specialization without unfolding the normalization construction. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.SectionDescent
open CategoryTheory
universe u v u' v' w z
variable {Γ : Type u} [Category.{v} Γ] {Δ : Type u'} [Category.{v'} Δ]
variable {A : Γ ⥤ Grpd.{z,w}} {B : Δ ⥤ Grpd.{z,w}}
variable (e : Γ ≌ Δ) (E : Extend A ≌ Extend B)
variable (α : E.functor ⋙ weaken B ≅ weaken A ⋙ e.functor)

structure Result where
  reconstruct : Section B → Section A
  recovery (s : Section B) : (reconstruct s).lift ⋙ E.functor ≅ e.functor ⋙ s.lift
  recovery_base (s : Section B) (γ : Γ) :
    ((recovery s).hom.app γ).base = α.hom.app ((reconstruct s).lift.obj γ)
  verticalEquiv (s t : Section B) :
    {η : (reconstruct s).lift ⟶ (reconstruct t).lift // ∀ γ, (η.app γ).base = 𝟙 γ} ≃
    {η : s.lift ⟶ t.lift // ∀ δ, (η.app δ).base = 𝟙 δ}

def result : Result e E α where
  reconstruct := Normalized.descended e E α
  recovery := Normalized.recoveredOriginal e E α
  recovery_base := Normalized.recoveredOriginal_base e E α
  verticalEquiv := Normalized.sectionVerticalEquiv e E α

end SquareKit.Internal.PathTransport.GroupoidModel.SectionDescent
