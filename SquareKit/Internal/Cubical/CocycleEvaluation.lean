import SquareKit.Internal.Cubical.CocyclePresheaf

/-! Evaluate a slice cocycle on a flag of formal cube substitutions. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

private theorem overHom_heq {N : Cube} {X X' Y Y' : Over N}
    (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : HEq f.left g.left) : HEq f g := by
  cases hX; cases hY
  apply heq_of_eq
  apply Over.OverMorphism.ext
  exact eq_of_heq h

abbrev CubeCocycle (N : Cube) := Cocycle2 (Over N)

def CubeCocycle.eval {N I J K : Cube} (z : CubeCocycle N)
    (f : I ⟶ J) (g : J ⟶ K) (t : K ⟶ N) : ℤ :=
  z.cochain
    (Over.homMk f (show f ≫ (g ≫ t) = f ≫ (g ≫ t) from rfl) :
      Over.mk (f ≫ (g ≫ t)) ⟶ Over.mk (g ≫ t))
    (Over.homMk g (show g ≫ t = g ≫ t from rfl) : Over.mk (g ≫ t) ⟶ Over.mk t)

theorem CubeCocycle.closed_eval {N I J K L : Cube} (z : CubeCocycle N)
    (f : I ⟶ J) (g : J ⟶ K) (h : K ⟶ L) (t : L ⟶ N) :
    z.eval g h t - z.eval (f ≫ g) h t + z.eval f (g ≫ h) t - z.eval f g (h ≫ t) = 0 := by
  have e := z.closed
    (Over.homMk f rfl : Over.mk (f ≫ (g ≫ (h ≫ t))) ⟶ Over.mk (g ≫ (h ≫ t)))
    (Over.homMk g rfl : Over.mk (g ≫ (h ≫ t)) ⟶ Over.mk (h ≫ t))
    (Over.homMk h rfl : Over.mk (h ≫ t) ⟶ Over.mk t)
  simp only [eval,δ2] at *
  convert e using 1 <;> congr 2 <;> simp [Over.mk,CostructuredArrow.mk,Over.homMk,CostructuredArrow.homMk,
    Category.assoc]
  all_goals congr 1
  all_goals first | rfl | simp only [Category.assoc] | apply overHom_heq <;> simp [Over.mk,CostructuredArrow.mk,Category.assoc]

theorem CubeCocycle.pullback_eval {M N I J K : Cube} (z : CubeCocycle N)
    (σ : M ⟶ N) (f : I ⟶ J) (g : J ⟶ K) (t : K ⟶ M) :
    CubeCocycle.eval (z.pullback (Over.map σ)) f g t = z.eval f g (t ≫ σ) := by
  simp only [eval,Cocycle2.pullback]
  congr 1 <;> simp [Over.mk,CostructuredArrow.mk,Over.map,Comma.mapRight,Over.homMk,
    CostructuredArrow.homMk,Category.assoc]
  all_goals apply overHom_heq <;> simp [Over.mk,CostructuredArrow.mk,Category.assoc]

end SquareKit.Cubical.CategoryCocycles
