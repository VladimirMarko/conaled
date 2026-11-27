import SquareKit.SheafGroupoidStack

/-! Completion of represented sheaf groupoids: extension and comparisons of
actual input transformations through the regular-bundle unit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Operations J) [G.Laws]
variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

/-- Extension is a functor on full mapping categories, including modifications. -/
def extend : (G.pseudofunctor ⟶ T) ⥤ (pseudofunctor G ⟶ T) :=
  (universalEquivalence G T).inverse

/-- The extension agrees with the supplied map on the actual unit. -/
def extendRecovery (θ : G.pseudofunctor ⟶ T) : unit G ≫ (extend G T).obj θ ≅ θ :=
  (universalEquivalence G T).counitIso.app θ

/-- Already-stack inputs are recovered by the actual regular-bundle unit. -/
def alreadyStack [G.pseudofunctor.IsStack (SheafCover.topology (J := J))]
    (X : Sheaf J (Type (max u v))) : G.Object X ≌ Principal G X :=
  StackificationUniversal.alreadyStackEquivalence (η := unit G)
    (fun _ => regularFullyFaithful G) (locallyGenerating G) X

@[simp] theorem alreadyStack_functor [G.pseudofunctor.IsStack (SheafCover.topology (J := J))]
    (X : Sheaf J (Type (max u v))) : (alreadyStack G X).functor = regularFunctor G := rfl

variable {G} {H K : Operations J} [H.Laws] [K.Laws]

/-- Construct the input transformation first; completion then extends its unit composite. -/
def completeMap (F : G.pseudofunctor ⟶ H.pseudofunctor) : pseudofunctor G ⟶ pseudofunctor H :=
  (extend G (pseudofunctor H)).obj (F ≫ unit H)

def completeMap_unit (F : G.pseudofunctor ⟶ H.pseudofunctor) :
    unit G ≫ completeMap F ≅ F ≫ unit H := extendRecovery G (pseudofunctor H) _

/-- Input modifications extend as actual modifications of completed maps. -/
def completeMapModification {F F' : G.pseudofunctor ⟶ H.pseudofunctor} (i : F ≅ F') :
    completeMap F ≅ completeMap F' :=
  (extend G (pseudofunctor H)).mapIso (whiskerRightIso i (unit H))

/-- Identity comparison is obtained uniquely through fully faithful precomposition. -/
def completeMap_id : completeMap (𝟙 G.pseudofunctor) ≅ 𝟙 (pseudofunctor G) :=
  (universalEquivalence G (pseudofunctor G)).fullyFaithfulFunctor.preimageIso
    (completeMap_unit (𝟙 G.pseudofunctor) ≪≫ leftUnitor (unit G) ≪≫ (rightUnitor (unit G)).symm)

/-- Composition of actual input maps is preserved up to an invertible modification. -/
def completeMap_comp (F : G.pseudofunctor ⟶ H.pseudofunctor)
    (F' : H.pseudofunctor ⟶ K.pseudofunctor) :
    completeMap F ≫ completeMap F' ≅ completeMap (F ≫ F') :=
  (universalEquivalence G (pseudofunctor K)).fullyFaithfulFunctor.preimageIso
    ((associator (unit G) (completeMap F) (completeMap F')).symm ≪≫
      whiskerRightIso (completeMap_unit F) (completeMap F') ≪≫
      associator F (unit H) (completeMap F') ≪≫
      whiskerLeftIso F (completeMap_unit F') ≪≫
      (associator F F' (unit K)).symm ≪≫ (completeMap_unit (F ≫ F')).symm)

end SquareKit.SheafGroupoid.Bundle
