import SquareKit.Internal.Cubical.CocycleGlobalization

/-! The global cochain construction retains the original slice cocycles. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

theorem globalToMap_mapToGlobal {Γ : Presheaf.Context.{0}} (v : Γ ⟶ cocycles) :
    globalToMap (mapToGlobal v) = v := by
  apply NatTrans.ext
  funext I
  apply ConcreteCategory.hom_ext
  intro x
  apply Cocycle2.ext
  funext X Y Z f g
  change CubeCocycle.eval (v.app (Opposite.op Z.left) (Γ.map Z.hom.op x))
    f.left g.left (𝟙 Z.left) = (v.app I x).cochain f g
  have eh := map_restriction v
    (x := Γ.elementsMk I x)
    (y := Γ.elementsMk (Opposite.op Z.left) (Γ.map Z.hom.op x))
    (Functor.Elements.homMk Z.hom.op rfl)
  calc
    _ = CubeCocycle.eval ((v.app I x).pullback (Over.map Z.hom))
        f.left g.left (𝟙 Z.left) := congrArg (fun q => CubeCocycle.eval q f.left g.left (𝟙 Z.left)) eh.symm
    _ = CubeCocycle.eval (v.app I x) f.left g.left ((𝟙 Z.left) ≫ Z.hom) :=
      CubeCocycle.pullback_eval _ _ _ _ _
    _ = _ := by rw [Category.id_comp]; exact CubeCocycle.eval_arrows _ f g

end SquareKit.Cubical.CategoryCocycles
