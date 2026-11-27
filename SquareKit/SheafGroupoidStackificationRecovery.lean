import SquareKit.SheafGroupoidStackification
import SquareKit.SheafGroupoidCompletionRecovery

/-! Recovery of the action-presentable completion from general principal bundles. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle.Recovery
open CategoryTheory Opposite Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M A : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
  (e : A ≅ SheafGroupoidAction.arrows (G := G) (M := M))

/-- The action quotient is a proved output comparison, never an input to general completion. -/
def toAction : pseudofunctor (SheafGroupoidCompletion.operations a e) ⟶
    SheafGroupoidCompletion.completion a :=
  (extend (SheafGroupoidCompletion.operations a e) (SheafGroupoidCompletion.completion a)).obj
    (SheafGroupoidCompletion.unit a e)

def toAction_unit : unit (SheafGroupoidCompletion.operations a e) ≫ toAction a e ≅
    SheafGroupoidCompletion.unit a e :=
  extendRecovery (SheafGroupoidCompletion.operations a e) _ _

/-- The old completion's established universal property constructs the inverse comparison. -/
def fromAction : SheafGroupoidCompletion.completion a ⟶
    pseudofunctor (SheafGroupoidCompletion.operations a e) :=
  (SheafGroupoidCompletion.universalEquivalence a e
    (pseudofunctor (SheafGroupoidCompletion.operations a e))).inverse.obj
      (unit (SheafGroupoidCompletion.operations a e))

def fromAction_unit : SheafGroupoidCompletion.unit a e ≫ fromAction a e ≅
    unit (SheafGroupoidCompletion.operations a e) :=
  (SheafGroupoidCompletion.universalEquivalence a e
    (pseudofunctor (SheafGroupoidCompletion.operations a e))).counitIso.app _

/-- Recovery holds as an invertible modification on the full general completion. -/
def to_from : toAction a e ≫ fromAction a e ≅
    𝟙 (pseudofunctor (SheafGroupoidCompletion.operations a e)) :=
  (universalEquivalence (SheafGroupoidCompletion.operations a e)
    (pseudofunctor (SheafGroupoidCompletion.operations a e))).fullyFaithfulFunctor.preimageIso
    ((associator (unit (SheafGroupoidCompletion.operations a e)) (toAction a e) (fromAction a e)).symm ≪≫
      whiskerRightIso (toAction_unit a e) (fromAction a e) ≪≫ fromAction_unit a e ≪≫
      (rightUnitor (unit (SheafGroupoidCompletion.operations a e))).symm)

/-- The inverse recovers all old quotient objects and arrows, naturally in parameters. -/
def from_to : fromAction a e ≫ toAction a e ≅ 𝟙 (SheafGroupoidCompletion.completion a) :=
  (SheafGroupoidCompletion.universalEquivalence a e
    (SheafGroupoidCompletion.completion a)).fullyFaithfulFunctor.preimageIso
    ((associator (SheafGroupoidCompletion.unit a e) (fromAction a e) (toAction a e)).symm ≪≫
      whiskerRightIso (fromAction_unit a e) (toAction a e) ≪≫ toAction_unit a e ≪≫
      (rightUnitor (SheafGroupoidCompletion.unit a e)).symm)

/-- Whole-fiber equivalence, derived from the two actual comparison transformations. -/
def actionEquivalence (X : Sheaf J (Type (max u v))) :
    Principal (SheafGroupoidCompletion.operations a e) X ≌ SheafActionQuotient.Object a X :=
  CategoryTheory.Equivalence.mk
    (StackDescentTransformation.component (toAction a e) X)
    (StackDescentTransformation.component (fromAction a e) X)
    (Cat.Hom.toNatIso ((PseudofunctorCoherence.evaluation (pseudofunctor (SheafGroupoidCompletion.operations a e))
      (pseudofunctor (SheafGroupoidCompletion.operations a e)) (.mk (op X))).mapIso (to_from a e).symm))
    (Cat.Hom.toNatIso ((PseudofunctorCoherence.evaluation (SheafGroupoidCompletion.completion a)
      (SheafGroupoidCompletion.completion a) (.mk (op X))).mapIso (from_to a e)))

/-- The actual new unit recovers the original action-presentable unit. -/
def actionEquivalence_unit (X : Sheaf J (Type (max u v))) :
    regularFunctor (SheafGroupoidCompletion.operations a e) ⋙ (actionEquivalence a e X).functor ≅
      SheafGroupoidCompletion.quotient a e :=
  Cat.Hom.toNatIso ((PseudofunctorCoherence.evaluation (SheafGroupoidCompletion.operations a e).pseudofunctor
    (SheafGroupoidCompletion.completion a) (.mk (op X))).mapIso (toAction_unit a e))

/-- Substitution comparison is the naturality of the actual output transformation. -/
def actionEquivalence_restriction {X Y : Sheaf J (Type (max u v))} (r : Y ⟶ X) :
    restriction r ⋙ (actionEquivalence a e Y).functor ≅
      (actionEquivalence a e X).functor ⋙ SheafActionQuotient.restriction r :=
  Cat.Hom.toNatIso ((toAction a e).naturality r.op.toLoc)

/-- The original action input needs no separately supplied arrow presentation. -/
abbrev originalActionEquivalence (X : Sheaf J (Type (max u v))) :=
  actionEquivalence a (Iso.refl _) X

variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

/-- Mapping categories recover through the common input, including every modification. -/
def mappingEquivalence : (pseudofunctor (SheafGroupoidCompletion.operations a e) ⟶ T) ≌
    (SheafGroupoidCompletion.completion a ⟶ T) :=
  (universalEquivalence (SheafGroupoidCompletion.operations a e) T).trans
    (SheafGroupoidCompletion.universalEquivalence a e T).symm

/-- The mapping comparison commutes with the two actual precomposition functors. -/
def mapping_unit : (mappingEquivalence a e T).functor ⋙
    StackLocalGeneration.restriction (SheafGroupoidCompletion.unit a e) T ≅
      StackLocalGeneration.restriction (unit (SheafGroupoidCompletion.operations a e)) T :=
  Functor.isoWhiskerLeft (universalEquivalence (SheafGroupoidCompletion.operations a e) T).functor
    (SheafGroupoidCompletion.universalEquivalence a e T).counitIso

end SquareKit.SheafGroupoid.Bundle.Recovery

namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.IsContinuous J K] [F.IsCocontinuous J K]
variable {G : Sheaf K GrpCat.{u}} {M A X : Sheaf K (Type u)}
variable (a : SheafActionQuotient.Action G M)
  (e : A ≅ SheafGroupoidAction.arrows (G := G) (M := M))
variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]

/-- Dense-site recovery uses exactly the original comparison hypotheses. -/
def principalBundleEquivalence :
    SheafGroupoid.Bundle.Principal (SheafGroupoidCompletion.operations a e) X ≌
      SheafGroupoid.Bundle.Principal
        (SheafGroupoidCompletion.operations (action J K F a) (Iso.refl _)) (sheaf J K F X) :=
  (SheafGroupoid.Bundle.Recovery.actionEquivalence a e X).trans
    ((quotientEquivalence J K F a).trans
      (SheafGroupoid.Bundle.Recovery.actionEquivalence (action J K F a) (Iso.refl _) (sheaf J K F X)).symm)

/-- The new dense-site equivalence recovers the established whole-fiber comparison. -/
def principalBundleEquivalence_comparison :
    (principalBundleEquivalence (X := X) J K F a e).functor ⋙
      (SheafGroupoid.Bundle.Recovery.actionEquivalence (action J K F a) (Iso.refl _) (sheaf J K F X)).functor ≅
    (SheafGroupoid.Bundle.Recovery.actionEquivalence a e X).functor ⋙
      (quotientEquivalence J K F a).functor :=
  Functor.isoWhiskerLeft ((SheafGroupoid.Bundle.Recovery.actionEquivalence a e X).functor ⋙
    (quotientEquivalence J K F a).functor)
    (SheafGroupoid.Bundle.Recovery.actionEquivalence (action J K F a) (Iso.refl _) (sheaf J K F X)).counitIso

/-- The original source unit commutes with this comparison, on full quotient objects. -/
def principalBundleEquivalence_unit :
    SheafGroupoid.Bundle.regularFunctor (SheafGroupoidCompletion.operations a e) ⋙
      (principalBundleEquivalence (X := X) J K F a e).functor ⋙
      (SheafGroupoid.Bundle.Recovery.actionEquivalence (action J K F a) (Iso.refl _) (sheaf J K F X)).functor ≅
    groupoidPresentationFunctor J K F a e ⋙ SheafActionPresentation.quotient (action J K F a) :=
  Functor.isoWhiskerLeft (SheafGroupoid.Bundle.regularFunctor (SheafGroupoidCompletion.operations a e))
    (principalBundleEquivalence_comparison J K F a e) ≪≫
  Functor.isoWhiskerRight (SheafGroupoid.Bundle.Recovery.actionEquivalence_unit a e X)
    (quotientEquivalence J K F a).functor ≪≫ (groupoidQuotientComparison J K F a e).symm

end SquareKit.SheafSiteComparison
