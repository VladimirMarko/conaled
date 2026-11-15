import SquareKit.Internal.Cubical.ContextualStructuralModel
import SquareKit.Internal.Cubical.TelescopeFillingSubstitution
import SquareKit.Internal.PathTransport.ContextualModel

/-! The existing indexed source telescopes are translated to the constructed
cubical tails, retaining each selected family filler. -/
namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber

namespace Telescope

def realize {Γ n} : StructuralModel.Telescope M Γ n → Presheaf.Telescope Γ
  | .nil => .nil Γ
  | .cons A T => .cons A.family (realize T)

theorem total_eq {Γ n} (T : StructuralModel.Telescope M Γ n) : (realize Base Fiber T).context = T.total := by
  induction T with
  | nil => rfl
  | cons A T ih => exact ih

noncomputable def fillers {Γ n} : (T : StructuralModel.Telescope M Γ n) → (realize Base Fiber T).Fillings
  | .nil => .nil Γ
  | .cons A T => .cons A.filling (fillers T)

theorem fillers_lawful {Γ n} (T : StructuralModel.Telescope M Γ n) : (fillers Base Fiber T).Lawful := by
  induction T with
  | nil => trivial
  | cons A T ih => exact ⟨A.lawful,ih⟩

theorem lift_eq {Γ Δ} (A : LawfulFamily Γ) (σ : ULift.{u+1} (Δ ⟶ Γ)) :
    ((M).lift A σ).down = liftSub A.family σ.down := rfl

theorem realize_pullback {Γ Δ : (M).Context} {n} (T : StructuralModel.Telescope M Γ n)
    (σ : (M).Substitution Δ Γ) :
    realize Base Fiber (StructuralModel.Telescope.pullback M T σ) = (realize Base Fiber T).reindex σ.down := by
  cases T with
  | nil => rfl
  | cons A T =>
    exact congrArg (Presheaf.Telescope.cons (reindex A.family σ.down))
      (realize_pullback T ((M).lift A σ))

theorem map_eq {Γ Δ : (M).Context} {n} (T : StructuralModel.Telescope M Γ n)
    (σ : (M).Substitution Δ Γ) :
    eqToHom (total_eq Base Fiber (StructuralModel.Telescope.pullback M T σ)).symm ≫
      eqToHom (congrArg Presheaf.Telescope.context (realize_pullback Base Fiber T σ)) ≫
      (realize Base Fiber T).map σ.down ≫ eqToHom (total_eq Base Fiber T) =
      (StructuralModel.Telescope.liftSub M T σ).down := by
  cases T with
  | nil => rfl
  | cons A T => exact map_eq T ((M).lift A σ)

end Telescope
end SquareKit.Cubical.Contextual
