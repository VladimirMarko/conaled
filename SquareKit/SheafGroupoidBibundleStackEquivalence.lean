import SquareKit.SheafGroupoidBibundleTensorRecovery

/-! The full stack mapping equivalence uses actual tensor composition. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open SquareKit.SheafGroupoid.Bundle.BalancedAction SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H) {X Y Z : Sheaf J (Type (max u v))}

variable {K : Operations J} [K.Laws] (Q : Bibundle H K)

def tensorIso {P P' : Bibundle G H} {Q Q' : Bibundle H K}
    (i : P ≅ P') (j : Q ≅ Q') : tensor P Q ≅ tensor P' Q' :=
  asIso (SquareKit.SheafGroupoid.Bibundle.map i.hom j.hom)

def sourceIso {P P' : Bibundle G H} (i : P ≅ P') :
    sourceTransformation P ≅ sourceTransformation P' := sourceAssignment.mapIso i

def tensorSourceComparison : sourceTransformation P ≫ tensorTransformation Q ≅
    sourceTransformation (tensor P Q) :=
  reconstructionIso _ ≪≫ sourceIso
    (reconstructedTensorIso Q (sourceTransformation P) ≪≫
      tensorIso (sourceUnitIso.app P).symm (Iso.refl Q))

theorem sourceTransformation_identity :
    sourceTransformation (SquareKit.SheafGroupoid.Bibundle.identity G) = Bundle.unit G := rfl

def tensorRecovery : Bundle.unit G ≫ tensorTransformation P ≅ sourceTransformation P :=
  (eqToIso (sourceTransformation_identity (G := G))).symm |> fun i =>
    CategoryTheory.Bicategory.whiskerRightIso i (tensorTransformation P) ≪≫
      tensorSourceComparison (SquareKit.SheafGroupoid.Bibundle.identity G) P ≪≫
      sourceAssignment.mapIso (SquareKit.SheafGroupoid.Bibundle.leftUnitor P)

def tensorExtensionComparison : tensorTransformation P ≅ stackTransformation P :=
  (Bundle.universalEquivalence G (Bundle.pseudofunctor H)).fullyFaithfulFunctor.preimageIso
    (tensorRecovery P ≪≫ (stackTransformation_recovery P).symm)

def tensorStackUnit : tensorTransformation (SquareKit.SheafGroupoid.Bibundle.identity G) ≅
    𝟙 (Bundle.pseudofunctor G) :=
  (Bundle.universalEquivalence G (Bundle.pseudofunctor G)).fullyFaithfulFunctor.preimageIso
    (tensorRecovery (SquareKit.SheafGroupoid.Bibundle.identity G) ≪≫
      eqToIso sourceTransformation_identity ≪≫
      (CategoryTheory.Bicategory.rightUnitor (Bundle.unit G)).symm)

def tensorStackComp : tensorTransformation P ≫ tensorTransformation Q ≅
    tensorTransformation (tensor P Q) :=
  (Bundle.universalEquivalence G (Bundle.pseudofunctor K)).fullyFaithfulFunctor.preimageIso
    ((CategoryTheory.Bicategory.associator (Bundle.unit G) (tensorTransformation P)
      (tensorTransformation Q)).symm ≪≫
      CategoryTheory.Bicategory.whiskerRightIso (tensorRecovery P) (tensorTransformation Q) ≪≫
      tensorSourceComparison P Q ≪≫ (tensorRecovery (tensor P Q)).symm)



def concreteStackAssignment : Bibundle G H ⥤ (Bundle.pseudofunctor G ⟶ Bundle.pseudofunctor H) :=
  stackAssignment.copyObj tensorTransformation (fun P => (tensorExtensionComparison P).symm)

def concreteStackAssignmentIso :
    concreteStackAssignment (G := G) (H := H) ≅ stackAssignment :=
  (stackAssignment.isoCopyObj tensorTransformation (fun P => (tensorExtensionComparison P).symm)).symm

def concreteStackEquivalence : Bibundle G H ≌
    (Bundle.pseudofunctor G ⟶ Bundle.pseudofunctor H) :=
  stackEquivalence.changeFunctor concreteStackAssignmentIso.symm


end SquareKit.SheafGroupoid.Bibundle
