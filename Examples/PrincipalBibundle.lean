import SquareKit.SheafGroupoidBibundleFunctor
import SquareKit.SheafGroupoidTrivialActionMap
import SquareKit.SheafGroupoidStackificationRecovery
import SquareKit.SheafGroupoidCompletionEquivalence
import Examples.SheafTorsorCocycle
/-! Balanced bibundle composition on a C4 torsor requiring nontrivial gluing. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.PrincipalBibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SheafGroupoidAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
section ActionRecovery
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
def identityArrowChange := (operations a).changeTransformation (Iso.refl _)
theorem identityArrowChange_locallyGenerating : StackLocalGeneration.LocallyGenerating
    (SheafCover.topology (J := J)) (identityArrowChange a) := by
  intro X m
  refine ⟨X, 𝟙 X, ?_, ⟨m.map⟩, ⟨Iso.refl _⟩⟩
  exact ⟨X, 𝟙 X, inferInstance, Sieve.ofArrows_mk _ _ ()⟩
def actionRecovery (X : Sheaf J (Type (max u v))) :
    Bundle.Principal (operations a) X ≌ SheafActionQuotient.Object a X :=
  (Bundle.completeMapComponentEquivalence (identityArrowChange a)
    (fun _ => (operations a).changeFullyFaithful (Iso.refl _))
    (identityArrowChange_locallyGenerating a) X).symm.trans
      (Bundle.Recovery.actionEquivalence a (Iso.refl _) X)
end ActionRecovery

namespace Clutching
open Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
abbrev group := SmoothOpenSite.locallyConstantGroup C4
abbrev productGroup := SmoothOpenSite.locallyConstantGroup (C4 × C4)
abbrev base := SmoothClutching.base
abbrev action := trivialAction group base
abbrev groupoid := operations action
abbrev productGroupoid := operations (trivialAction productGroup base)
def diagonal : group ⟶ productGroup := SmoothOpenSite.locallyConstantGroupMap
  ((MonoidHom.id C4).prod (MonoidHom.id C4))
def first : productGroup ⟶ group := SmoothOpenSite.locallyConstantGroupMap (MonoidHom.fst C4 C4)
theorem diagonal_first : diagonal ≫ first = 𝟙 group := by
  change SmoothOpenSite.locallyConstantGroupMap _ ≫ SmoothOpenSite.locallyConstantGroupMap _ = _
  rw [← SmoothOpenSite.locallyConstantGroupMap_comp]
  exact SmoothOpenSite.locallyConstantGroupMap_id C4

def torsorObject : SheafActionQuotient.Object action base where
  torsor := Examples.SheafTorsorCocycle.Clutching.datum.glue.obj
  value x _ := x.val
  natural f _ := f.map_val
  equivariant _ _ _ := rfl

def bundle : Bundle.Principal groupoid base := (actionRecovery action base).inverse.obj torsorObject
def inclusion : Bibundle groupoid productGroupoid :=
  Bibundle.functorBibundle (trivialMapTransformation diagonal)
def projection : Bibundle productGroupoid groupoid :=
  Bibundle.functorBibundle (trivialMapTransformation first)
def splitComparison : Bibundle.tensor inclusion projection ≅ Bibundle.identity groupoid :=
  Bibundle.functorBibundleComp _ _ ≪≫
    Bibundle.functorBibundleModification (trivialMapComp diagonal first) ≪≫
    Bibundle.functorBibundleModification
      (eqToIso (congrArg (trivialMapTransformation (M := base)) diagonal_first)) ≪≫
    Bibundle.functorBibundleModification trivialMapId ≪≫ Bibundle.functorBibundleUnit
def twice : Bundle.Principal groupoid base :=
  (Bibundle.tensorComponent projection).obj ((Bibundle.tensorComponent inclusion).obj bundle)

def twiceComparison : twice ≅ bundle :=
  (Cat.Hom.toNatIso ((PseudofunctorCoherence.evaluation (Bundle.pseudofunctor groupoid)
    (Bundle.pseudofunctor groupoid) (.mk (op base))).mapIso
      (Bibundle.tensorStackComp inclusion projection ≪≫
        Bibundle.concreteStackAssignment.mapIso splitComparison ≪≫ Bibundle.tensorStackUnit))).app bundle

def decodedTwice := (actionRecovery action base).functor.obj twice

def decodedTwiceComparison : decodedTwice ≅ torsorObject :=
  (actionRecovery action base).functor.mapIso twiceComparison ≪≫
    (actionRecovery action base).counitIso.app torsorObject

theorem twice_no_section : ¬ Nonempty (SplitSheaf.Tm decodedTwice.torsor.family) := by
  rintro ⟨s⟩
  exact Examples.SheafTorsorCocycle.Clutching.no_section
    ⟨SheafTorsor.sectionOfArrow ((SheafTorsor.ofSection _ s).comp
      decodedTwiceComparison.hom.torsorArrow)⟩

def tripleAssociativity :
    (Bibundle.tensorComponent (Bibundle.tensor (Bibundle.tensor inclusion projection) inclusion)).obj bundle ≅
      (Bibundle.tensorComponent (Bibundle.tensor inclusion (Bibundle.tensor projection inclusion))).obj bundle :=
  (Cat.Hom.toNatIso ((PseudofunctorCoherence.evaluation (Bundle.pseudofunctor groupoid)
    (Bundle.pseudofunctor productGroupoid) (.mk (op base))).mapIso
      (Bibundle.concreteStackAssignment.mapIso (Bibundle.associator inclusion projection inclusion)))).app bundle

end Clutching
end Examples.PrincipalBibundle
