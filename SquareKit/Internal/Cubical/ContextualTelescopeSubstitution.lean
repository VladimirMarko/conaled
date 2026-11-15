import SquareKit.Internal.Cubical.ContextualTelescopes

namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber
namespace Telescope

private theorem cons_heq {Γ : Presheaf.Context.{u}} {A : Family Γ}
    {T U : Presheaf.Telescope (total A)} (e : T = U) (F : Filling A)
    {fs : T.Fillings} {gs : U.Fillings} (h : HEq fs gs) :
    HEq (Presheaf.Telescope.Fillings.cons F fs) (Presheaf.Telescope.Fillings.cons F gs) := by
  cases e
  cases h
  rfl

theorem fillers_pullback {Γ Δ : (M).Context} {n} (T : StructuralModel.Telescope M Γ n)
    (σ : (M).Substitution Δ Γ) :
    HEq (fillers Base Fiber (StructuralModel.Telescope.pullback M T σ)) ((fillers Base Fiber T).reindex σ.down) := by
  cases T with
  | nil => rfl
  | cons A T =>
    exact cons_heq (realize_pullback Base Fiber T ((M).lift A σ))
      (A.filling.reindex σ.down) (fillers_pullback T ((M).lift A σ))

end Telescope
end SquareKit.Cubical.Contextual
