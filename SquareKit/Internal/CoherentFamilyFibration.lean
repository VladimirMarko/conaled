import SquareKit.CoGrothendieckMap
import SquareKit.Internal.RepresentableCoherentRecovery

/-! Coherent local diagrams and direct families have equivalent total categories
of substitution arrows. Recovery uses the existing pseudonatural comparisons. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.RepresentableClassification.CoherentFamily
open CategoryTheory CategoryTheory.Functor Opposite
open scoped Pseudofunctor.StrongTrans
open Pseudofunctor.CoGrothendieck
universe u v w a b
variable {C : Type v} [Category.{w} C] (V : Type a) [Category.{b} V]

abbrev CodeTotal := Pseudofunctor.CoGrothendieck (diagrams.{u} (C := C) V).toPseudofunctor'
abbrev FamilyTotal := Pseudofunctor.CoGrothendieck (system.{u} (C := C) V)

abbrev totalDecode : CodeTotal (C := C) V ⥤ FamilyTotal (C := C) V := Pseudofunctor.CoGrothendieck.map (decoder (C := C) V)
abbrev totalCode : FamilyTotal (C := C) V ⥤ CodeTotal (C := C) V := Pseudofunctor.CoGrothendieck.map (coder (C := C) V)

def totalRecovery : 𝟭 (CodeTotal (C := C) V) ≅ totalDecode (C := C) V ⋙ totalCode (C := C) V :=
  (mapIdIso _).symm ≪≫
    (CoGrothendieckMap.homFunctor _ _).mapIso (classificationUnit (C := C) V) ≪≫
      mapCompIso (decoder (C := C) V) (coder (C := C) V)

def totalCounit : totalCode (C := C) V ⋙ totalDecode (C := C) V ≅ 𝟭 (FamilyTotal (C := C) V) :=
  (mapCompIso (coder (C := C) V) (decoder (C := C) V)).symm ≪≫
    (CoGrothendieckMap.homFunctor _ _).mapIso (classificationCounit (C := C) V) ≪≫ mapIdIso _

/-- The total equivalence uses coherent modifications, not only fibre equivalences. -/
def totalEquivalence : CodeTotal (C := C) V ≌ FamilyTotal (C := C) V :=
  CategoryTheory.Equivalence.mk (totalDecode (C := C) V) (totalCode (C := C) V) (totalRecovery (C := C) V) (totalCounit (C := C) V)

@[simp] theorem totalDecode_projection :
    totalDecode (C := C) V ⋙ forget (system (C := C) V) = forget (diagrams (C := C) V).toPseudofunctor' := rfl
@[simp] theorem totalCode_projection :
    totalCode (C := C) V ⋙ forget (diagrams (C := C) V).toPseudofunctor' = forget (system (C := C) V) := rfl

/-- The selected indexed category is recovered as the actual categorical fibre. -/
def codeFiberEquivalence (Γ : Context.{u} C) :
    SquareKit.CoherentFamilyClassification.Code Γ.Elements V ≌
      (forget (diagrams (C := C) V).toPseudofunctor').Fiber Γ :=
  (HasFibers.inducedFunctor (forget (diagrams (C := C) V).toPseudofunctor') Γ).asEquivalence

def directFiberEquivalence (Γ : Context.{u} C) :
    (Γ.Elements ⥤ V) ≌ (forget (system (C := C) V)).Fiber Γ :=
  (HasFibers.inducedFunctor (forget (system (C := C) V)) Γ).asEquivalence

example : (forget (diagrams.{u} (C := C) V).toPseudofunctor').IsFibered := inferInstance
example : (forget (system.{u} (C := C) V)).IsFibered := inferInstance

end SquareKit.RepresentableClassification.CoherentFamily

namespace SquareKit.RepresentableClassification.CoherentFamily
open CategoryTheory CategoryTheory.Functor Opposite
open Pseudofunctor.CoGrothendieck
open scoped Pseudofunctor.StrongTrans
universe u v w a b
variable {C : Type v} [Category.{w} C] (V : Type a) [Category.{b} V]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

@[simp] theorem totalRecovery_base (x : CodeTotal.{u} (C := C) V) :
    ((totalRecovery V).hom.app x).base = 𝟙 x.base := by
  simp [totalRecovery, CoGrothendieckMap.homFunctor, CoGrothendieckMap.mapModification,
    mapIdIso, mapCompIso]

@[simp] theorem totalCounit_base (x : FamilyTotal.{u} (C := C) V) :
    ((totalCounit V).hom.app x).base = 𝟙 x.base := by
  simp [totalCounit, CoGrothendieckMap.homFunctor, CoGrothendieckMap.mapModification,
    mapIdIso, mapCompIso]

end SquareKit.RepresentableClassification.CoherentFamily

namespace SquareKit.RepresentableClassification.CoherentFamily
open CategoryTheory CategoryTheory.Functor Opposite
open Pseudofunctor.CoGrothendieck
open scoped Pseudofunctor.StrongTrans
universe u v w a b
variable {C : Type v} [Category.{w} C] (V : Type a) [Category.{b} V]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

@[simp] theorem totalRecovery_inv_base (x : CodeTotal.{u} (C := C) V) :
    ((totalRecovery V).inv.app x).base = 𝟙 x.base := by
  simp [totalRecovery, CoGrothendieckMap.homFunctor, CoGrothendieckMap.mapModification,
    mapIdIso, mapCompIso]

@[simp] theorem totalCounit_inv_base (x : FamilyTotal.{u} (C := C) V) :
    ((totalCounit V).inv.app x).base = 𝟙 x.base := by
  simp [totalCounit, CoGrothendieckMap.homFunctor, CoGrothendieckMap.mapModification,
    mapIdIso, mapCompIso]

@[simp] theorem totalDecode_map_base {x y : CodeTotal.{u} (C := C) V} (f : x ⟶ y) :
    ((totalDecode V).map f).base = f.base := rfl
@[simp] theorem totalCode_map_base {x y : FamilyTotal.{u} (C := C) V} (f : x ⟶ y) :
    ((totalCode V).map f).base = f.base := rfl

/-- The packaged equivalence's adjusted unit is also over identity on the base. -/
@[simp] theorem totalEquivalence_unit_base (x : CodeTotal.{u} (C := C) V) :
    ((totalEquivalence V).unitIso.hom.app x).base = 𝟙 x.base := by
  simp [totalEquivalence, CategoryTheory.Equivalence.mk, CategoryTheory.Equivalence.adjointifyη]

@[simp] theorem totalEquivalence_counit_base (x : FamilyTotal.{u} (C := C) V) :
    ((totalEquivalence V).counitIso.hom.app x).base = 𝟙 x.base := totalCounit_base V x

/-- Both directions retain all cartesian arrows. -/
theorem totalDecode_cartesian {x y : CodeTotal.{u} (C := C) V} (f : x ⟶ y)
    [(forget (diagrams V).toPseudofunctor').IsCartesian f.base f] :
    (forget (system V)).IsCartesian f.base ((totalDecode V).map f) :=
  CoGrothendieckMap.map_cartesian (decoder V) f

theorem totalCode_cartesian {x y : FamilyTotal.{u} (C := C) V} (f : x ⟶ y)
    [(forget (system V)).IsCartesian f.base f] :
    (forget (diagrams V).toPseudofunctor').IsCartesian f.base ((totalCode V).map f) :=
  CoGrothendieckMap.map_cartesian (coder V) f

end SquareKit.RepresentableClassification.CoherentFamily
