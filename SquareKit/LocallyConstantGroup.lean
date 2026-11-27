import SquareKit.LocallyConstantSheaf
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Algebra.Category.Grp.Limits

/-! Group-valued locally constant sheaves and their actual constant-label unit.
The underlying set sheaf is the existing concrete constant sheaf. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.LocallyConstantGroup
open CategoryTheory Opposite TopologicalSpace
open LocallyConstantSheaf
variable (X : TopCat.{0}) (G : Type) [Group G]

def data : (Opens X)ᵒᵖ ⥤ GrpCat where
  obj U := GrpCat.of (LocallyConstant U.unop G)
  map f := GrpCat.ofHom (LocallyConstant.comapMonoidHom
    ⟨f.unop, (Opens.isOpenEmbedding_of_le f.unop.le).continuous⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

def obj : Sheaf (site X) GrpCat :=
  ⟨data X G, (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget GrpCat)).2
    (LocallyConstantSheaf.data_isSheaf X G)⟩

def unit : (Functor.const (Opens X)ᵒᵖ).obj (GrpCat.of G) ⟶ data X G where
  app _ := GrpCat.ofHom LocallyConstant.constMonoidHom

/-- The concrete comparison commutes with the sheafification adjunction unit. -/
theorem constantIso_unit (A : Type) :
    toSheafify (site X) ((Functor.const (Opens X)ᵒᵖ).obj A) ≫
      (constantIso X A).hom.hom = LocallyConstantSheaf.unit X A := by
  change toSheafify (site X) _ ≫ sheafifyMap (site X) (LocallyConstantSheaf.unit X A) ≫
    ((sheafificationAdjunction (site X) (Type 0)).counit.app (LocallyConstantSheaf.obj X A)).hom = _
  rw [sheafificationAdjunction_counit_app_val, ← Category.assoc, ← toSheafify_naturality,
    Category.assoc, toSheafify_sheafifyLift, Category.comp_id]

/-- Already sheaf-valued arrows recover through the actual adjunction unit. -/
def alreadySheaf : LocallyConstantSheaf.data X G ≅
    sheafify (site X) (LocallyConstantSheaf.data X G) :=
  isoSheafify (site X) (data_isSheaf X G)

omit [Group G] in
@[simp] theorem alreadySheaf_hom : (alreadySheaf X G).hom =
    toSheafify (site X) (LocallyConstantSheaf.data X G) := rfl
end SquareKit.LocallyConstantGroup
