import SquareKit.Internal.CoherentFamilyFibration
import Examples.CoherentFamilyClassification

/-! Total-arrow recovery, ordered substitution and loss controls for the coherent-family fibration. -/
noncomputable section
set_option autoImplicit false
namespace Examples.CoherentFamilyFibration
open CategoryTheory Opposite
open SquareKit.RepresentableClassification
open SquareKit.CoherentFamilyClassification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open Examples.CoherentFamilyClassification Examples.CategoryValuedEvaluation

def twistedTotal : CoherentFamily.CodeTotal (C := ℕ) (Type) := ⟨context, localData⟩
def collapsedTotal : CoherentFamily.CodeTotal (C := ℕ) (Type) :=
  ⟨context, (code context.Elements (Type)).obj ((Functor.const _).obj PUnit)⟩
def collapseTotal : twistedTotal ⟶ collapsedTotal :=
  (ι (CoherentFamily.diagrams (C := ℕ) (Type)).toPseudofunctor' context).map collapse

example : ((CoherentFamily.totalDecode (Type)).map collapseTotal).base = 𝟙 context := rfl
example : collapseTotal ≫ (CoherentFamily.totalRecovery (Type)).hom.app collapsedTotal =
    (CoherentFamily.totalRecovery (Type)).hom.app twistedTotal ≫
      ((CoherentFamily.totalDecode (Type) ⋙ CoherentFamily.totalCode (Type)).map collapseTotal) :=
  (CoherentFamily.totalRecovery (Type)).hom.naturality collapseTotal

/-- Decoding the total object retains its nonidentity Boolean action. -/
example : ((CoherentFamily.totalDecode (Type)).obj twistedTotal).fiber.map step false = true := rfl

/-- The total map still has its noninvertible component. -/
example : (((CoherentFamily.totalDecode (Type)).map collapseTotal).fiber.app (point 0)) false = PUnit.unit := rfl

/-- Removing the restriction condition loses the required recovery. -/
example : IsEmpty (badData.obj (Arrow.mk step) ≅
    badData.obj ((identityArrow _).obj (point 1))) := badData_no_recovery

namespace Ordered
open Examples.NonCubicalClassification
abbrev A := Examples.CoherentFamilyClassification.Substitution.classified
abbrev X : CoherentFamily.CodeTotal (C := Base) (Type) := ⟨Examples.NonCubicalClassification.context, A⟩
abbrev first := cartesianLift (F := (CoherentFamily.diagrams (C := Base) (Type)).toPseudofunctor') A successor
abbrev second := cartesianLift
  (F := (CoherentFamily.diagrams (C := Base) (Type)).toPseudofunctor')
  ((reindex successor.mapElements).obj A) double

example : (second ≫ first).base = double ≫ successor := rfl
example : ((second ≫ first).base.app (op (SingleObj.star ℕ))) 2 = 5 := rfl
example : ((CoherentFamily.totalDecode (Type)).obj
    (domainCartesianLift (F := (CoherentFamily.diagrams (C := Base) (Type)).toPseudofunctor')
      ((reindex successor.mapElements).obj A) double)).fiber.obj
        (Examples.NonCubicalClassification.point 2) = Fin 6 := rfl
example : ((CoherentFamily.totalDecode (Type)).obj
    (domainCartesianLift (F := (CoherentFamily.diagrams (C := Base) (Type)).toPseudofunctor')
      ((reindex double.mapElements).obj A) successor)).fiber.obj
        (Examples.NonCubicalClassification.point 2) = Fin 7 := rfl

example : (CoherentFamily.totalDecode (Type)).map (second ≫ first) =
    (CoherentFamily.totalDecode (Type)).map second ≫ (CoherentFamily.totalDecode (Type)).map first :=
  (CoherentFamily.totalDecode (Type)).map_comp second first

example : (forget (CoherentFamily.system (C := Base) (Type))).IsCartesian successor
    ((CoherentFamily.totalDecode (Type)).map first) :=
  SquareKit.CoGrothendieckMap.map_cartesianLift (CoherentFamily.decoder (Type)) A successor

end Ordered
end Examples.CoherentFamilyFibration

namespace Examples.CoherentFamilyFibration
open CategoryTheory
open Examples.CategoryValuedEvaluation

/-- The noninvertible vertical arrow remains noninvertible in the total category. -/
theorem collapseTotal_not_iso : ¬ IsIso collapseTotal := by
  intro h
  let := h
  have he : (collapseTotal ≫ inv collapseTotal).fiber.hom.app (Arrow.mk (𝟙 (point 0))) false =
      (collapseTotal ≫ inv collapseTotal).fiber.hom.app (Arrow.mk (𝟙 (point 0))) true := rfl
  rw [IsIso.hom_inv_id] at he
  change false = true at he
  contradiction

example :
    ((SquareKit.RepresentableClassification.CoherentFamily.totalRecovery (Type)).hom.app
      twistedTotal).fiber.hom.app (Arrow.mk step) false = true := rfl

namespace LargeHoms
/-- A small object type with a hom type in the next universe. -/
inductive Base : Type where | point
instance : Category.{1} Base where
  Hom _ _ := ULift.{1} Unit
  id _ := ⟨()⟩
  comp _ _ := ⟨()⟩
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc _ _ _ := rfl

/-- Universe admission tests w > u,v; an all-small example would miss this case. -/
example :
    SquareKit.RepresentableClassification.CoherentFamily.CodeTotal.{0} (C := Base) (Type) ≌
      SquareKit.RepresentableClassification.CoherentFamily.FamilyTotal.{0} (C := Base) (Type) :=
  SquareKit.RepresentableClassification.CoherentFamily.totalEquivalence (Type)
end LargeHoms
end Examples.CoherentFamilyFibration

namespace Examples.CoherentFamilyFibration.Ordered
open CategoryTheory Opposite
open SquareKit.RepresentableClassification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open Examples.NonCubicalClassification

/-- The composite substitution also has its cartesian comparison after decoding. -/
example : (forget (CoherentFamily.system (C := Base) (Type))).IsCartesian (double ≫ successor)
    ((CoherentFamily.totalDecode (Type)).map
      (cartesianLift (F := (CoherentFamily.diagrams (C := Base) (Type)).toPseudofunctor')
        A (double ≫ successor))) :=
  SquareKit.CoGrothendieckMap.map_cartesianLift (CoherentFamily.decoder (Type)) A (double ≫ successor)

/-- The total recovery comparison is natural over a nonidentity substitution. -/
example : first ≫ (CoherentFamily.totalRecovery (Type)).hom.app X =
    (CoherentFamily.totalRecovery (Type)).hom.app _ ≫
      ((CoherentFamily.totalDecode (Type) ⋙ CoherentFamily.totalCode (Type)).map first) :=
  (CoherentFamily.totalRecovery (Type)).hom.naturality first
end Examples.CoherentFamilyFibration.Ordered
