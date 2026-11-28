import SquareKit.SheafGroupoidAtlasInvariance
import SquareKit.SheafGroupoidStackificationRecovery

/-! Covering atlas equivalences recover the original action-quotient maps and mapping categories. -/
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
variable {G : Sheaf J GrpCat.{max u v}} {M A U : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
  (e : A ≅ SheafGroupoidAction.arrows (G := G) (M := M))
variable {p : U ⟶ M} (D : Chart (SheafGroupoidCompletion.operations a e) p p)

def atlasToAction : pseudofunctor D.atlasOperations ⟶ SheafGroupoidCompletion.completion a :=
  D.completedAmbient ≫ toAction a e

def atlasToAction_unit : unit D.atlasOperations ≫ atlasToAction a e D ≅
    D.atlasPresentation ≫ SheafGroupoidCompletion.chartUnit a e D :=
  (associator (unit D.atlasOperations) D.completedAmbient (toAction a e)).symm ≪≫
    whiskerRightIso (completeMap_unit D.ambientTransformation) (toAction a e) ≪≫
    associator D.ambientTransformation (unit (SheafGroupoidCompletion.operations a e)) (toAction a e) ≪≫
    whiskerLeftIso D.ambientTransformation (toAction_unit a e) ≪≫
    associator D.atlasPresentation D.transformation (SheafGroupoidCompletion.unit a e)

/-- The old action-atlas quotient is recovered with only its original atlas-cover hypothesis. -/
def atlasActionEquivalence [Presheaf.IsLocallySurjective J p.hom]
    (X : Sheaf J (Type (max u v))) : Principal D.atlasOperations X ≌
      SheafActionQuotient.Object a X :=
  (completeMapComponentEquivalence D.ambientTransformation D.ambientFullyFaithful
    D.ambientLocallyGenerating X).trans (actionEquivalence a e X)

@[simp] theorem atlasActionEquivalence_functor [Presheaf.IsLocallySurjective J p.hom]
    (X : Sheaf J (Type (max u v))) : (atlasActionEquivalence a e D X).functor =
      StackDescentTransformation.component (atlasToAction a e D) X := rfl

def atlasActionEquivalence_unit [Presheaf.IsLocallySurjective J p.hom]
    (X : Sheaf J (Type (max u v))) :
    regularFunctor D.atlasOperations ⋙ (atlasActionEquivalence a e D X).functor ≅
      D.atlasToChart ⋙ SheafGroupoidCompletion.chartQuotient a e D :=
  Cat.Hom.toNatIso ((PseudofunctorCoherence.evaluation D.atlasOperations.pseudofunctor
    (SheafGroupoidCompletion.completion a) (.mk (op X))).mapIso
    (atlasToAction_unit a e D))

variable {V : Sheaf J (Type (max u v))} {q : V ⟶ M}
  (E : Chart (SheafGroupoidCompletion.operations a e) q q)

def atlasToAction_refinement (r : U ⟶ V) (comm : r ≫ q = p) :
    D.completedMap E r comm ≫ atlasToAction a e E ≅ atlasToAction a e D :=
  (associator (D.completedMap E r comm) E.completedAmbient (toAction a e)).symm ≪≫
    whiskerRightIso (D.completedMap_ambient E r comm) (toAction a e)

end SquareKit.SheafGroupoid.Bundle.Recovery

namespace SquareKit.SheafGroupoid.Bundle.Recovery
open CategoryTheory Opposite Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M A U : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
  (e : A ≅ SheafGroupoidAction.arrows (G := G) (M := M))
variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

def toActionMappingSquare :
    StackLocalGeneration.restriction (toAction a e) T ⋙
      (universalEquivalence (SheafGroupoidCompletion.operations a e) T).functor ≅
    (SheafGroupoidCompletion.universalEquivalence a e T).functor :=
  (associatorNatIsoRight (unit (SheafGroupoidCompletion.operations a e)) (toAction a e) T).symm ≪≫
    (precomposing (SheafGroupoidCompletion.operations a e).pseudofunctor
      (SheafGroupoidCompletion.completion a) T).mapIso (toAction_unit a e)

def toActionMappingEquivalence : (SheafGroupoidCompletion.completion a ⟶ T) ≌
    (pseudofunctor (SheafGroupoidCompletion.operations a e) ⟶ T) := by
  letI : (StackLocalGeneration.restriction (toAction a e) T ⋙
      (universalEquivalence (SheafGroupoidCompletion.operations a e) T).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (toActionMappingSquare a e T).symm
  letI := Functor.isEquivalence_of_comp_right (StackLocalGeneration.restriction (toAction a e) T)
    (universalEquivalence (SheafGroupoidCompletion.operations a e) T).functor
  exact (StackLocalGeneration.restriction (toAction a e) T).asEquivalence

variable {p : U ⟶ M} (D : Chart (SheafGroupoidCompletion.operations a e) p p)
variable [Presheaf.IsLocallySurjective J p.hom]

def atlasActionMappingEquivalence : (SheafGroupoidCompletion.completion a ⟶ T) ≌
    (pseudofunctor D.atlasOperations ⟶ T) :=
  ((toActionMappingEquivalence a e T).trans
    (completeMapMappingEquivalence D.ambientTransformation D.ambientFullyFaithful
      D.ambientLocallyGenerating T)).changeFunctor
    (associatorNatIsoRight D.completedAmbient (toAction a e) T).symm

@[simp] theorem atlasActionMappingEquivalence_functor :
    (atlasActionMappingEquivalence a e T D).functor =
      StackLocalGeneration.restriction (atlasToAction a e D) T := rfl

def atlasActionModificationEquiv (α β : SheafGroupoidCompletion.completion a ⟶ T) :
    (α ⟶ β) ≃ (atlasToAction a e D ≫ α ⟶ atlasToAction a e D ≫ β) :=
  (atlasActionMappingEquivalence a e T D).fullyFaithfulFunctor.homEquiv

end SquareKit.SheafGroupoid.Bundle.Recovery
