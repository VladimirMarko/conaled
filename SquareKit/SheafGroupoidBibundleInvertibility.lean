import SquareKit.SheafGroupoidBibundleDoubleOpposite
import SquareKit.SheafGroupoidBibundleStackEquivalence
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-! Actual tensor invertibility and equivalence of the induced stack map. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H)

structure TensorInverse where
  inverse : Bibundle H G
  evaluation : tensor P inverse ≅ identity G
  coevaluation : tensor inverse P ≅ identity H

def TensorInverse.ofLeftPrincipal (hP : LeftPrincipal P) : TensorInverse P where
  inverse := opposite P hP
  evaluation := evaluationIso P hP
  coevaluation := oppositeEvaluationIso P hP

def TensorInverse.stackEquivalence (i : TensorInverse P) :
    Bicategory.Equivalence (Bundle.pseudofunctor G) (Bundle.pseudofunctor H) :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    ((tensorStackComp P i.inverse ≪≫ concreteStackAssignment.mapIso i.evaluation ≪≫ tensorStackUnit).symm)
    (tensorStackComp i.inverse P ≪≫ concreteStackAssignment.mapIso i.coevaluation ≪≫ tensorStackUnit)

@[simp] theorem TensorInverse.stackEquivalence_hom (i : TensorInverse P) :
    (i.stackEquivalence P).hom = tensorTransformation P := rfl

/-- Full mapping recovery reflects two-sided inverse modifications to actual tensor isomorphisms. -/
def TensorInverse.ofStackInverse
    (Q : Bundle.pseudofunctor H ⟶ Bundle.pseudofunctor G)
    (η : 𝟙 (Bundle.pseudofunctor G) ≅ tensorTransformation P ≫ Q)
    (ε : Q ≫ tensorTransformation P ≅ 𝟙 (Bundle.pseudofunctor H)) : TensorInverse P := by
  let R := concreteStackEquivalence.inverse.obj Q
  let e : tensorTransformation R ≅ Q := concreteStackEquivalence.counitIso.app Q
  refine ⟨R, ?_, ?_⟩
  · exact concreteStackEquivalence.fullyFaithfulFunctor.preimageIso
      ((tensorStackComp P R).symm ≪≫ Bicategory.whiskerLeftIso (tensorTransformation P) e ≪≫
        η.symm ≪≫ (tensorStackUnit (G := G)).symm)
  · exact concreteStackEquivalence.fullyFaithfulFunctor.preimageIso
      ((tensorStackComp R P).symm ≪≫ Bicategory.whiskerRightIso e (tensorTransformation P) ≪≫
        ε ≪≫ (tensorStackUnit (G := H)).symm)

def TensorInverse.ofStackEquivalence
    (e : Bicategory.Equivalence (Bundle.pseudofunctor G) (Bundle.pseudofunctor H))
    (h : e.hom = tensorTransformation P) : TensorInverse P :=
  TensorInverse.ofStackInverse P e.inv
    (e.unit ≪≫ Bicategory.whiskerRightIso (eqToIso h) e.inv)
    (Bicategory.whiskerLeftIso e.inv (eqToIso h).symm ≪≫ e.counit)

theorem tensorInverse_iff_stackEquivalence : Nonempty (TensorInverse P) ↔
    ∃ e : Bicategory.Equivalence (Bundle.pseudofunctor G) (Bundle.pseudofunctor H),
      e.hom = tensorTransformation P := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i.stackEquivalence P, rfl⟩
  · rintro ⟨e,h⟩
    exact ⟨TensorInverse.ofStackEquivalence P e h⟩

end SquareKit.SheafGroupoid.Bibundle
