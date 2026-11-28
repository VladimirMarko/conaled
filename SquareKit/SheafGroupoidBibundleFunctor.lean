import SquareKit.SheafGroupoidBibundleStackEquivalence
import SquareKit.SheafGroupoidAtlasComparison

/-! Functor-induced bibundles recover actual completion and atlas comparisons. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open CategoryTheory.Bicategory
open SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K : Operations J} [G.Laws] [H.Laws] [K.Laws]

def functorBibundle (F : G.pseudofunctor ⟶ H.pseudofunctor) : Bibundle G H :=
  recoveredBibundle (F ≫ Bundle.unit H)

theorem functorBibundle_right (F : G.pseudofunctor ⟶ H.pseudofunctor) :
    (functorBibundle F).right = Bundle.regular H
      ((StackDescentTransformation.component F G.objects).obj (SquareKit.SheafGroupoid.Bibundle.identityObject G)) := rfl

def functorStackComparison (F : G.pseudofunctor ⟶ H.pseudofunctor) :
    tensorTransformation (functorBibundle F) ≅ Bundle.completeMap F :=
  (Bundle.universalEquivalence G (Bundle.pseudofunctor H)).fullyFaithfulFunctor.preimageIso
    (tensorRecovery (functorBibundle F) ≪≫ (reconstructionIso (F ≫ Bundle.unit H)).symm ≪≫
      (Bundle.completeMap_unit F).symm)

def functorBibundleModification {F F' : G.pseudofunctor ⟶ H.pseudofunctor} (i : F ≅ F') :
    functorBibundle F ≅ functorBibundle F' :=
  reconstruction.mapIso (whiskerRightIso i (Bundle.unit H))

def functorBibundleUnit : functorBibundle (𝟙 G.pseudofunctor) ≅ SquareKit.SheafGroupoid.Bibundle.identity G :=
  concreteStackEquivalence.fullyFaithfulFunctor.preimageIso
    (functorStackComparison (𝟙 G.pseudofunctor) ≪≫ Bundle.completeMap_id ≪≫ tensorStackUnit.symm)

def functorCompositeComparison (F : G.pseudofunctor ⟶ H.pseudofunctor)
    (F' : H.pseudofunctor ⟶ K.pseudofunctor) :
    tensorTransformation (tensor (functorBibundle F) (functorBibundle F')) ≅
      Bundle.completeMap F ≫ Bundle.completeMap F' :=
  (tensorStackComp (functorBibundle F) (functorBibundle F')).symm ≪≫
    whiskerRightIso (functorStackComparison F) (tensorTransformation (functorBibundle F')) ≪≫
    whiskerLeftIso (Bundle.completeMap F) (functorStackComparison F')

def functorBibundleComp (F : G.pseudofunctor ⟶ H.pseudofunctor)
    (F' : H.pseudofunctor ⟶ K.pseudofunctor) :
    tensor (functorBibundle F) (functorBibundle F') ≅ functorBibundle (F ≫ F') :=
  concreteStackEquivalence.fullyFaithfulFunctor.preimageIso
    (functorCompositeComparison F F' ≪≫ Bundle.completeMap_comp F F' ≪≫
      (functorStackComparison (F ≫ F')).symm)


section Atlas
variable {U V W : Sheaf J (Type (max u v))}
variable {p : U ⟶ G.objects} {q : V ⟶ G.objects} {s : W ⟶ G.objects}
variable (D : Chart G p p) (E : Chart G q q) (R : Chart G s s)

def atlasBibundle (r : U ⟶ V) (hr : r ≫ q = p) : Bibundle D.atlasOperations E.atlasOperations :=
  functorBibundle (D.representedMap E r hr)

def atlasStackComparison (r : U ⟶ V) (hr : r ≫ q = p) :
    tensorTransformation (atlasBibundle D E r hr) ≅ D.completedMap E r hr :=
  functorStackComparison _

def atlasUnitStackComparison :
    tensorTransformation (atlasBibundle D D (𝟙 U) (Category.id_comp p)) ≅
      tensorTransformation (SquareKit.SheafGroupoid.Bibundle.identity D.atlasOperations) :=
  atlasStackComparison D D _ _ ≪≫ D.completedMap_id ≪≫ tensorStackUnit.symm

def atlasBibundleUnit : atlasBibundle D D (𝟙 U) (Category.id_comp p) ≅
    SquareKit.SheafGroupoid.Bibundle.identity D.atlasOperations :=
  concreteStackEquivalence.fullyFaithfulFunctor.preimageIso (atlasUnitStackComparison D)

def atlasCompStackComparison (r : U ⟶ V) (hr : r ≫ q = p)
    (t : V ⟶ W) (ht : t ≫ s = q) :
    tensorTransformation (tensor (atlasBibundle D E r hr) (atlasBibundle E R t ht)) ≅
      tensorTransformation (atlasBibundle D R (r ≫ t) (by rw [Category.assoc, ht, hr])) :=
  functorCompositeComparison (D.representedMap E r hr) (E.representedMap R t ht) ≪≫
    D.completedMap_comp E R r hr t ht ≪≫ (atlasStackComparison D R _ _).symm

def atlasBibundleComp (r : U ⟶ V) (hr : r ≫ q = p)
    (t : V ⟶ W) (ht : t ≫ s = q) :
    tensor (atlasBibundle D E r hr) (atlasBibundle E R t ht) ≅
      atlasBibundle D R (r ≫ t) (by rw [Category.assoc, ht, hr]) :=
  concreteStackEquivalence.fullyFaithfulFunctor.preimageIso
    (atlasCompStackComparison D E R r hr t ht)

theorem atlasBibundleUnit_recovers :
    concreteStackAssignment.map (atlasBibundleUnit D).hom = (atlasUnitStackComparison D).hom :=
  concreteStackEquivalence.fullyFaithfulFunctor.map_preimage _

theorem atlasBibundleComp_recovers (r : U ⟶ V) (hr : r ≫ q = p)
    (t : V ⟶ W) (ht : t ≫ s = q) :
    concreteStackAssignment.map (atlasBibundleComp D E R r hr t ht).hom =
      (atlasCompStackComparison D E R r hr t ht).hom :=
  concreteStackEquivalence.fullyFaithfulFunctor.map_preimage _

theorem atlasStackComparison_restriction (r : U ⟶ V) (hr : r ≫ q = p)
    {X Y : Sheaf J (Type (max u v))} (k : Y ⟶ X) (T : Bundle.Principal D.atlasOperations X) :
    (((atlasStackComparison D E r hr).hom.as.app (.mk (op Y))).toNatTrans.app (Bundle.reindex T k)).comp
      ((D.completedMap_restriction E r hr k).hom.app T) =
    (SquareKit.SheafGroupoid.Bundle.BalancedFactorization.baseChangeMap T (atlasBibundle D E r hr).right
      (atlasBibundle D E r hr).left k).comp
      ((((atlasStackComparison D E r hr).hom.as.app (.mk (op X))).toNatTrans.app T).reindex k) :=
  StackDescentTransformation.modification_naturality (atlasStackComparison D E r hr).hom.as k T

def atlasAmbientBibundle : Bibundle D.atlasOperations G := functorBibundle D.ambientTransformation

def atlasCommonStackComparison (r : W ⟶ U) (hr : r ≫ p = s)
    (t : W ⟶ V) (ht : t ≫ q = s) :
    tensorTransformation (tensor (atlasBibundle R D r hr) (atlasAmbientBibundle D)) ≅
      tensorTransformation (tensor (atlasBibundle R E t ht) (atlasAmbientBibundle E)) :=
  functorCompositeComparison (R.representedMap D r hr) D.ambientTransformation ≪≫
    D.completedCommonRefinement E R r hr t ht ≪≫
      (functorCompositeComparison (R.representedMap E t ht) E.ambientTransformation).symm

def atlasCommonRefinement (r : W ⟶ U) (hr : r ≫ p = s)
    (t : W ⟶ V) (ht : t ≫ q = s) :
    tensor (atlasBibundle R D r hr) (atlasAmbientBibundle D) ≅
      tensor (atlasBibundle R E t ht) (atlasAmbientBibundle E) :=
  concreteStackEquivalence.fullyFaithfulFunctor.preimageIso
    (atlasCommonStackComparison D E R r hr t ht)

theorem atlasCommonRefinement_recovers (r : W ⟶ U) (hr : r ≫ p = s)
    (t : W ⟶ V) (ht : t ≫ q = s) :
    concreteStackAssignment.map (atlasCommonRefinement D E R r hr t ht).hom =
      (atlasCommonStackComparison D E R r hr t ht).hom :=
  concreteStackEquivalence.fullyFaithfulFunctor.map_preimage _

end Atlas
end SquareKit.SheafGroupoid.Bibundle
