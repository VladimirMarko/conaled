import SquareKit.SheafGroupoidStackification
import SquareKit.Internal.PseudofunctorCoherence
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-! Locally generating fully faithful maps induce equivalences of the actual bundle completions. -/
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
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (F : G.pseudofunctor ⟶ H.pseudofunctor)
variable (hFF : ∀ X : Sheaf J (Type (max u v)),
  (StackDescentTransformation.component F X).FullyFaithful)
variable (hLG : StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J)) F)
variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

def completeMapMappingSquare :
    StackLocalGeneration.restriction (completeMap F) T ⋙ (universalEquivalence G T).functor ≅
      (universalEquivalence H T).functor ⋙ StackLocalGeneration.restriction F T :=
  (associatorNatIsoRight (unit G) (completeMap F) T).symm ≪≫
    (precomposing G.pseudofunctor (pseudofunctor H) T).mapIso (completeMap_unit F) ≪≫
      associatorNatIsoRight F (unit H) T

def completeMapMappingEquivalence :
    (pseudofunctor H ⟶ T) ≌ (pseudofunctor G ⟶ T) := by
  let e := StackificationUniversal.universalEquivalence hFF hLG T
  letI : (StackLocalGeneration.restriction F T).IsEquivalence := e.isEquivalence_functor
  letI : (StackLocalGeneration.restriction (completeMap F) T ⋙
      (universalEquivalence G T).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (completeMapMappingSquare F T).symm
  letI := Functor.isEquivalence_of_comp_right
    (StackLocalGeneration.restriction (completeMap F) T) (universalEquivalence G T).functor
  exact (StackLocalGeneration.restriction (completeMap F) T).asEquivalence

@[simp] theorem completeMapMappingEquivalence_functor :
    (completeMapMappingEquivalence F hFF hLG T).functor =
      StackLocalGeneration.restriction (completeMap F) T := rfl

def completeMapInverse : pseudofunctor H ⟶ pseudofunctor G :=
  (completeMapMappingEquivalence F hFF hLG (pseudofunctor G)).inverse.obj
    (𝟙 (pseudofunctor G))

def completeMapEquivalenceUnit :
    𝟙 (pseudofunctor G) ≅ completeMap F ≫ completeMapInverse F hFF hLG :=
  ((completeMapMappingEquivalence F hFF hLG (pseudofunctor G)).counitIso.app _).symm

def completeMapEquivalenceCounit :
    completeMapInverse F hFF hLG ≫ completeMap F ≅ 𝟙 (pseudofunctor H) :=
  (completeMapMappingEquivalence F hFF hLG (pseudofunctor H)).fullyFaithfulFunctor.preimageIso
    ((associator (completeMap F) (completeMapInverse F hFF hLG) (completeMap F)).symm ≪≫
      whiskerRightIso (completeMapEquivalenceUnit F hFF hLG).symm (completeMap F) ≪≫
      leftUnitor (completeMap F) ≪≫ (rightUnitor (completeMap F)).symm)

/-- The forward transformation is the existing completed map, with coherent inverse data. -/
def completeMapEquivalence : Bicategory.Equivalence (pseudofunctor G) (pseudofunctor H) :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (completeMapEquivalenceUnit F hFF hLG) (completeMapEquivalenceCounit F hFF hLG)

@[simp] theorem completeMapEquivalence_hom :
    (completeMapEquivalence F hFF hLG).hom = completeMap F := rfl

private def componentIso {A B : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
    Cat.{max u v, max (u + 1) (v + 1)}} {a b : A ⟶ B} (e : a ≅ b)
    (X : Sheaf J (Type (max u v))) :
    StackDescentTransformation.component a X ≅ StackDescentTransformation.component b X :=
  Cat.Hom.toNatIso ((PseudofunctorCoherence.evaluation A B (.mk (op X))).mapIso e)

def completeMapComponentEquivalence (X : Sheaf J (Type (max u v))) :
    Principal G X ≌ Principal H X :=
  CategoryTheory.Equivalence.mk
    (StackDescentTransformation.component (completeMap F) X)
    (StackDescentTransformation.component (completeMapInverse F hFF hLG) X)
    (componentIso (completeMapEquivalence F hFF hLG).unit X)
    (componentIso (completeMapEquivalence F hFF hLG).counit X)

@[simp] theorem completeMapComponentEquivalence_functor (X : Sheaf J (Type (max u v))) :
    (completeMapComponentEquivalence F hFF hLG X).functor =
      StackDescentTransformation.component (completeMap F) X := rfl

end SquareKit.SheafGroupoid.Bundle

namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (F : G.pseudofunctor ⟶ H.pseudofunctor)
variable (hFF : ∀ X : Sheaf J (Type (max u v)),
  (StackDescentTransformation.component F X).FullyFaithful)
variable (hLG : StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J)) F)
variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

def completeMapModificationEquiv (α β : pseudofunctor H ⟶ T) :
    (α ⟶ β) ≃ (completeMap F ≫ α ⟶ completeMap F ≫ β) :=
  (completeMapMappingEquivalence F hFF hLG T).fullyFaithfulFunctor.homEquiv

end SquareKit.SheafGroupoid.Bundle
