import SquareKit.SheafActionQuotient

/-! Actual label laws for chart arrows, retaining group multiplication order. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Opposite
namespace SquareKit.SheafActionQuotient
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}} {M X : Sheaf J (Type w)} {a : Action G M}

/-- Composition retains the right-translation order, for arbitrary groups. -/
theorem arrowLabel_comp_apply {m n p : X ⟶ M}
    (f : Arrow (chart a m) (chart a n)) (g : Arrow (chart a n) (chart a p))
    (U : Cᵒᵖ) (x : X.obj.obj U) :
    (arrowLabel (Arrow.comp f g)).hom.app U x =
      (show G.obj.obj U from (arrowLabel f).hom.app U x) *
      (show G.obj.obj U from (arrowLabel g).hom.app U x) := by
  have h := g.torsorArrow.equivariant (X.obj.elementsMk U x)
    (show G.obj.obj U from (arrowLabel f).hom.app U x) (1 : G.obj.obj U)
  change g.torsorArrow.iso.hom.app (X.obj.elementsMk U x)
    ((show G.obj.obj U from (arrowLabel f).hom.app U x) * 1) =
    (show G.obj.obj U from (arrowLabel f).hom.app U x) *
      (show G.obj.obj U from (arrowLabel g).hom.app U x) at h
  rw [mul_one] at h
  exact h

theorem arrowLabel_ident_apply (m : X ⟶ M) (U : Cᵒᵖ) (x : X.obj.obj U) :
    (arrowLabel (Arrow.ident (chart a m))).hom.app U x = (1 : G.obj.obj U) := rfl

theorem arrowLabel_reindex_apply {Y : Sheaf J (Type w)} {m n : X ⟶ M}
    (f : Arrow (chart a m) (chart a n)) (r : Y ⟶ X) (U : Cᵒᵖ) (x : Y.obj.obj U) :
    (arrowLabel (m := r ≫ m) (n := r ≫ n) (f.reindex r)).hom.app U x = (arrowLabel f).hom.app U (r.hom.app U x) := rfl

theorem arrowLabel_inverse_apply {m n : X ⟶ M}
    (f : Arrow (chart a m) (chart a n)) (U : Cᵒᵖ) (x : X.obj.obj U) :
    (arrowLabel f.inverse).hom.app U x = (show G.obj.obj U from (arrowLabel f).hom.app U x)⁻¹ := by
  have h := congrArg (fun z : Arrow (chart a m) (chart a n) =>
    z.torsorArrow.iso.inv.app (X.obj.elementsMk U x) (1 : G.obj.obj U)) (arrowLabel_recovers f)
  change (1 : G.obj.obj U) * (show G.obj.obj U from (arrowLabel f).hom.app U x)⁻¹ =
    (arrowLabel f.inverse).hom.app U x at h
  exact (one_mul _).symm.trans h |>.symm

end SquareKit.SheafActionQuotient
