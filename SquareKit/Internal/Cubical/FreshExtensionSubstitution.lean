import SquareKit.Internal.Cubical.ElementFreshening
import SquareKit.Internal.Cubical.PartialRestriction

/-! Fresh coordinates commute with substitution in the parameter context. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem freshExtension_substitution {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    (liftSub (interval Γ) σ).mapElements.obj (freshExtension x) =
      freshExtension (σ.mapElements.obj x) :=
  congrArg (fun γ => (total (interval Γ)).elementsMk (Opposite.op (Cube.extend x.obj.unop))
    ⟨γ,ULift.up (Cube.fresh x.obj.unop)⟩) (σ.naturality_apply (dropOpp x.obj) x.val)

theorem Term.val_heq {Γ : Context.{u}} {A : Family Γ} (t : Term A)
    {x y : Γ.Elements} (e : x = y) : HEq (t.val x) (t.val y) := by cases e; rfl

end SquareKit.Cubical.Presheaf
