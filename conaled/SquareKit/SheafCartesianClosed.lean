import SquareKit.SheafFunction

/-! Adapt the sheaf closed structure to the Cartesian monoidal dictionary.
Mathlib exposes two monoidal dictionaries on full subcategories. Their tensor
functors agree; transporting the adjunction avoids relying on dictionary identity. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SheafCartesianClosed
open CategoryTheory MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Closure for the Cartesian monoidal dictionary used by geometric slicing. -/
@[instance_reducible] def closed (A : Sheaf J (Type (max u v))) :
    @Closed _ _ (inferInstance : CartesianMonoidalCategory (Sheaf J (Type (max u v)))).toMonoidalCategory A where
  rightAdj := (inferInstance : Closed A).rightAdj
  adj := (inferInstance : Closed A).adj.ofNatIsoLeft
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext j x; rfl))
end SquareKit.SheafCartesianClosed
