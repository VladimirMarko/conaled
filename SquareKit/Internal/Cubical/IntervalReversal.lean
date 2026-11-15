import SquareKit.Internal.Cubical.Interval

/-! Reverse a generalized interval without replacing dimensions by endpoints. -/
namespace SquareKit.Cubical
open CategoryTheory
universe u

theorem Cube.endpoint_reversal (I : Cube) (b : Bool) :
    comp (endpoint I b) reversal = endpoint I (!b) := by
  apply Quotient.sound
  intro i
  cases b
  · exact Expr.Conv.neg_zero
  · exact Expr.Conv.neg_one

namespace Presheaf

def reverseInterval (Γ : Context.{u}) : total (interval Γ) ⟶ total (interval Γ) where
  app _ := TypeCat.ofHom (fun z => ⟨z.1,⟨Cube.comp z.2.down Cube.reversal⟩⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg (fun r => (⟨Γ.map f z.1,ULift.up r⟩ : (total (interval Γ)).obj J))
      (Category.assoc f.unop z.2.down Cube.reversal)

theorem reverseInterval_endpoint (Γ : Context.{u}) (b : Bool) :
    endpointSub Γ b ≫ reverseInterval Γ = endpointSub Γ (!b) := by
  ext I z
  exact congrArg (fun r => (⟨z,ULift.up r⟩ : (total (interval Γ)).obj I)) (Cube.endpoint_reversal I.unop b)

theorem reverseInterval_twice (Γ : Context.{u}) :
    reverseInterval Γ ≫ reverseInterval Γ = 𝟙 _ := by
  ext I z
  have h : Cube.comp (Cube.comp z.2.down Cube.reversal) Cube.reversal = z.2.down :=
    (@Category.assoc Cube _ I.unop ⟨1⟩ ⟨1⟩ ⟨1⟩ z.2.down Cube.reversal Cube.reversal).trans
      ((congrArg (Cube.comp z.2.down) Cube.reversal_twice).trans (@Category.comp_id Cube _ I.unop ⟨1⟩ z.2.down))
  exact congrArg (fun r => (⟨z.1,ULift.up r⟩ : (total (interval Γ)).obj I)) h

theorem reverseInterval_natural {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    reverseInterval Δ ≫ liftSub (interval Γ) σ =
      liftSub (interval Γ) σ ≫ reverseInterval Γ := rfl

end Presheaf
end SquareKit.Cubical
