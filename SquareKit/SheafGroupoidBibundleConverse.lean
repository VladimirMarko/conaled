import SquareKit.SheafGroupoidBibundleInvertibility
import SquareKit.Internal.PseudofunctorCoherence

/-! Full faithfulness and local anchor coverage from tensor invertibility. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle SquareKit.SheafGroupoid.Bundle.BalancedProduct
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H)

def componentIso {A B : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
    Cat.{max u v, max (u + 1) (v + 1)}} {a b : A ⟶ B} (e : a ≅ b)
    (X : Sheaf J (Type (max u v))) :
    StackDescentTransformation.component a X ≅ StackDescentTransformation.component b X :=
  Cat.Hom.toNatIso ((PseudofunctorCoherence.evaluation A B (.mk (op X))).mapIso e)

def TensorInverse.componentEquivalence (i : TensorInverse P) (X : Sheaf J (Type (max u v))) :
    Principal G X ≌ Principal H X :=
  CategoryTheory.Equivalence.mk
    (StackDescentTransformation.component (tensorTransformation P) X)
    (StackDescentTransformation.component (tensorTransformation i.inverse) X)
    (componentIso (i.stackEquivalence P).unit X)
    (componentIso (i.stackEquivalence P).counit X)

def TensorInverse.sourceFullyFaithful (i : TensorInverse P) (X : Sheaf J (Type (max u v))) :
    (sourceFunctor P (X := X)).FullyFaithful :=
  ((regularFullyFaithful G).comp (i.componentEquivalence P X).fullyFaithfulFunctor).ofIso
    (componentIso (tensorRecovery P) X)

instance identity_anchor_locallySurjective :
    Presheaf.IsLocallySurjective J (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor (identity H).right).hom := by
  apply Presheaf.isLocallySurjective_of_surjective
  intro U k
  exact ⟨⟨(k,k),identityFiber (𝟙 (⟨k⟩ : H.Section U))⟩,rfl⟩

theorem TensorInverse.anchor_locallySurjective (i : TensorInverse P) :
    Presheaf.IsLocallySurjective J (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor P.right).hom := by
  have he : i.coevaluation.hom.toMap.totalMap ≫ SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor (identity H).right =
      SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor (tensor i.inverse P).right := rfl
  have hcover : Presheaf.IsLocallySurjective J (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor (tensor i.inverse P).right).hom := by
    rw [← he]
    infer_instance
  have : Epi (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor (compositionRightBundle i.inverse.right P.right P.left)) :=
    letI : Presheaf.IsLocallySurjective J (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor (compositionRightBundle i.inverse.right P.right P.left)).hom := hcover
    inferInstance
  have ha := balancedMap_anchor i.inverse.right P.right P.left
  have : Epi (ordinaryFirst i.inverse.right P.right ≫ SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor P.right) := by
    rw [← ha]
    infer_instance
  have : Epi (SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor P.right) := epi_of_epi (ordinaryFirst i.inverse.right P.right) _
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance

end SquareKit.SheafGroupoid.Bibundle
