import SquareKit.SheafGroupoidAtlasPresentation
import SquareKit.SheafGroupoidStackification

/-! Completion of actual atlas maps and independent arrow-coordinate changes. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Chart
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws]
variable {U V W : Sheaf J (Type (max u v))}
variable {p : U ⟶ G.objects} {q : V ⟶ G.objects} {s : W ⟶ G.objects}
variable (D : Chart G p p) (E : Chart G q q) (F : Chart G s s)

/-- Complete the already constructed map of represented atlas groupoids. -/
def completedMap (r : U ⟶ V) (comm : r ≫ q = p) :
    Bundle.pseudofunctor D.atlasOperations ⟶ Bundle.pseudofunctor E.atlasOperations :=
  Bundle.completeMap (D.representedMap E r comm)

def completedMap_unit (r : U ⟶ V) (comm : r ≫ q = p) :
    Bundle.unit D.atlasOperations ≫ D.completedMap E r comm ≅
      D.representedMap E r comm ≫ Bundle.unit E.atlasOperations :=
  Bundle.completeMap_unit _

def completedMap_id : D.completedMap D (𝟙 U) (Category.id_comp p) ≅
    𝟙 (Bundle.pseudofunctor D.atlasOperations) :=
  Bundle.completeMapModification D.representedMap_id ≪≫ Bundle.completeMap_id

def completedMap_comp (r : U ⟶ V) (comm : r ≫ q = p)
    (t : V ⟶ W) (comm' : t ≫ s = q) :
    D.completedMap E r comm ≫ E.completedMap F t comm' ≅
      D.completedMap F (r ≫ t) (by rw [Category.assoc, comm', comm]) :=
  Bundle.completeMap_comp _ _ ≪≫
    Bundle.completeMapModification (D.representedMap_comp E F r comm t comm')

/-- Parameter changes commute with the completed comparison by its actual naturality. -/
def completedMap_restriction (r : U ⟶ V) (comm : r ≫ q = p)
    {X Y : Sheaf J (Type (max u v))} (k : Y ⟶ X) :
    Bundle.restriction k ⋙ StackDescentTransformation.component (D.completedMap E r comm) Y ≅
      StackDescentTransformation.component (D.completedMap E r comm) X ⋙ Bundle.restriction k :=
  Cat.Hom.toNatIso ((D.completedMap E r comm).naturality k.op.toLoc)

variable (E' : Chart G p p)

/-- Independent coordinates use the actual identity square on the object atlas. -/
def completedCoordinateChange : Bundle.pseudofunctor D.atlasOperations ⟶
    Bundle.pseudofunctor E'.atlasOperations := D.completedMap E' (𝟙 U) (Category.id_comp p)

/-- Changing coordinates and returning recovers the entire completed groupoid. -/
def completedCoordinateRoundtrip :
    D.completedCoordinateChange E' ≫ E'.completedCoordinateChange D ≅
      𝟙 (Bundle.pseudofunctor D.atlasOperations) :=
  D.completedMap_comp E' D (𝟙 U) (Category.id_comp p) (𝟙 U) (Category.id_comp p) ≪≫
    D.completedMap_id

end SquareKit.SheafGroupoid.Chart
