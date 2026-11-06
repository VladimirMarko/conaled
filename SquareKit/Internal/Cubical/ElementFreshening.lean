import SquareKit.Internal.Cubical.CubeProductFunctor
import SquareKit.Internal.Cubical.IntervalExtension

/-! Fresh-coordinate specialization on all generalized elements of a context. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def intervalBaseElement {Γ : Context.{u}} (x : (total (interval Γ)).Elements) : Γ.Elements :=
  Γ.elementsMk x.obj x.val.1

def freshenElements (Γ : Context.{u}) : (total (interval Γ)).Elements ⥤ (total (interval Γ)).Elements where
  obj x := freshExtension (intervalBaseElement x)
  map {x y} f := Functor.Elements.homMk (Cube.extensionMap f.hom.unop).op (by
    have hb := congrArg (fun z => z.1) f.map_val
    change Γ.map f.hom x.val.1 = y.val.1 at hb
    change (⟨Γ.map (Cube.extensionMap f.hom.unop).op (Γ.map (dropOpp x.obj) x.val.1),
      ULift.up (Cube.extensionMap f.hom.unop ≫ Cube.fresh x.obj.unop)⟩ :
      (total (interval Γ)).obj (Opposite.op (Cube.extend y.obj.unop))) =
      ⟨Γ.map (dropOpp y.obj) y.val.1,ULift.up (Cube.fresh y.obj.unop)⟩
    rw [Cube.extensionMap_fresh]
    congr 1
    rw [← Γ.map_comp_apply]
    have hc : dropOpp x.obj ≫ (Cube.extensionMap f.hom.unop).op = f.hom ≫ dropOpp y.obj :=
      congrArg Quiver.Hom.op (Cube.extensionMap_drop f.hom.unop)
    rw [hc,Γ.map_comp_apply,hb])
  map_id x := by
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.op (Cube.extensionMap_id x.obj.unop)
  map_comp f g := by
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.op (Cube.extensionMap_comp g.hom.unop f.hom.unop)

end SquareKit.Cubical.Presheaf
