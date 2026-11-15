import SquareKit.Internal.PathTransport.AlignedSignatureComparison

/-! The normalized generated maps depend on codes, not their typing derivations. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
universe u
variable (S : Signature.{u})
theorem generatedContextMap_derivation
    (hΓ kΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap S hΓ = generatedContextMap S kΓ := rfl

theorem generatedFamilyMap_derivation
    (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hB kB : Typed.TyDeriv.{u+1} Γ γ B b) :
    generatedFamilyMap S hΓ hB = generatedFamilyMap S hΓ kB := rfl

universe v w
variable {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]
variable {F G : C ⥤ D} (η : F ≅ G) (P : C ⥤ Type w) (Q : D ⥤ Type w)
variable (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
theorem alignedContextComparison_derivation
    (h : α ≫ CategoryTheory.Functor.whiskerRight η.hom Q = β)
    (hΓ kΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison η P Q α β h hΓ =
      alignedContextComparison η P Q α β h kΓ := rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
