import SquareKit.Internal.Cubical.ElementFreshening
import SquareKit.Internal.Cubical.CategoryCocycles

/-! The two graph natural transformations on generalized interval elements. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def freshToElement (Γ : Context.{u}) : freshenElements Γ ⟶ 𝟭 (total (interval Γ)).Elements where
  app x := specializeInterval (intervalBaseElement x) x.val.2
  naturality {x y} f := by
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    let dim : (total (interval Γ)).obj y.obj → Cube.Hom y.obj.unop ⟨1⟩ := fun z => z.2.down
    have hr := congrArg dim f.map_val
    change Cube.comp f.hom.unop x.val.2.down = y.val.2.down at hr
    change Cube.graph y.val.2.down ≫ Cube.extensionMap f.hom.unop =
      f.hom.unop ≫ Cube.graph x.val.2.down
    rw [← hr]
    exact Cube.graph_naturality _ _

def intervalCap (Γ : Context.{u}) (b : Bool) : total (interval Γ) ⟶ total (interval Γ) :=
  projection (interval Γ) ≫ endpointSub Γ b

def freshToCap (Γ : Context.{u}) (b : Bool) : freshenElements Γ ⟶ (intervalCap Γ b).mapElements where
  app x := specializeInterval (intervalBaseElement x) (ULift.up (Cube.endpoint x.obj.unop b))
  naturality {x y} f := by
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    change Cube.graph (Cube.endpoint y.obj.unop b) ≫ Cube.extensionMap f.hom.unop =
      f.hom.unop ≫ Cube.graph (Cube.endpoint x.obj.unop b)
    have e := Cube.graph_naturality f.hom.unop (Cube.endpoint x.obj.unop b)
    change Cube.graph (Cube.comp f.hom.unop (Cube.endpoint x.obj.unop b)) ≫
      Cube.extensionMap f.hom.unop = _ at e
    rw [Cube.comp_endpoint] at e
    exact e

end SquareKit.Cubical.Presheaf
