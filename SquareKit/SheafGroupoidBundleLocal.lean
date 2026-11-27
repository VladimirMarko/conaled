import SquareKit.SheafGroupoidActionLocal

/-! A principal bundle is regular after its own total-space cover. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws] {X : Sheaf J (Type (max u v))}
variable (P : Principal G X)

abbrev total := Action.total P.toAction
abbrev projection := P.toAction.projection
abbrev anchor := Action.anchor P.toAction
abbrev localObject := Action.localObject P.toAction

/-- The tautological point acts on each regular arrow fiber. -/
def localMap : Map (regular G (localObject P)) (reindex P (projection P)) where
  hom := Action.localFamilyMap P.toAction
  equivariant x a b g p := by
    change P.act (X.obj.elementsMk x.obj x.val.1.1) (regularFiberEquiv G (localObject P) x a
      ((regularFiberEquiv G (localObject P) x a).symm
        (g ≫ regularFiberEquiv G (localObject P) x b p))) x.val.2 = _
    rw [Equiv.apply_symm_apply]
    exact P.act_comp (X.obj.elementsMk x.obj x.val.1.1) g
      (regularFiberEquiv G (localObject P) x b p) x.val.2

/-- Local triviality is proved using the actual total-space cover. -/
def localIso : regular G (localObject P) ≅ reindex P (projection P) :=
  asIso (localMap P : regular G (localObject P) ⟶ reindex P (projection P))

end SquareKit.SheafGroupoid.Bundle
