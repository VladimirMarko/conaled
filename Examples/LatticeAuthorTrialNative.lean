import Examples.NativeLatticeTransportCases
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace NativeTrial692
open CategoryTheory Examples.LatticeTransportBridge Examples.CompositionalStructureIdentity
open SquareKit.StructureIdentity
open Examples.NativeStructureRecovery (comparablePair)

def shift : Int ≃o Int where
  toEquiv :=
    { toFun := fun z => z + 3
      invFun := fun z => z - 3
      left_inv := by intro z; change (z + 3) - 3 = z; omega
      right_inv := by intro z; change (z - 3) + 3 = z; omega }
  map_rel_iff' := by intro a b; change a + 3 ≤ b + 3 ↔ a ≤ b; omega

theorem shift_value (z : Int) : shift z = z + 3 := rfl
theorem shift_inverse (z : Int) : shift.symm z = z - 3 := rfl

def pair (x y : Int) (h : x ≤ y) : OrderedPair Int := ⟨(x,y),h⟩
def selected : OrderedPair Int := pair (-2) 4 (by decide)

theorem direct_value (p : OrderedPair Int) :
    (directTransport shift p).val = (p.val.1 + 3, p.val.2 + 3) := rfl

theorem direct_recovery (p : OrderedPair Int) :
    directTransport shift.symm (directTransport shift p) = p :=
  (directTransport shift).symm_apply_apply p

def gap (p : OrderedPair Int) : Int := p.val.2 - p.val.1

theorem direct_gap (p : OrderedPair Int) : gap (directTransport shift p) = gap p := by
  change (p.val.2 + 3) - (p.val.1 + 3) = p.val.2 - p.val.1
  omega

theorem selected_value : (directTransport shift selected).val = (1,7) := rfl
theorem selected_strict : (directTransport shift selected).val.1 <
    (directTransport shift selected).val.2 := by decide

theorem nonidentity : shift 0 = 3 ∧ shift 0 ≠ 0 := by decide

theorem meet_preserved (x y : Int) : shift (x ⊓ y) = shift x ⊓ shift y := shift.map_inf x y
theorem join_preserved (x y : Int) : shift (x ⊔ y) = shift x ⊔ shift y := shift.map_sup x y

def negation : Int ≃ Int where
  toFun := fun z => -z
  invFun := fun z => -z
  left_inv := neg_neg
  right_inv := neg_neg

theorem negation_not_monotone : ¬ Monotone (fun z : Int => -z) := by
  intro h
  have hh := h (show (0 : Int) ≤ 1 by decide)
  norm_num at hh

theorem negation_rejected : ¬ lattice.Preserves negation (latticeModel Int) (latticeModel Int) := by
  intro h
  have hh := (binary_preserves negation _ _).mp h.1 0 1
  change -(min (0 : Int) 1) = min (-0) (-1) at hh
  norm_num at hh

namespace Presheaf
open SquareKit.Cubical.Presheaf StructureIdentity.Native StructuredIdentity
open Examples.NativeLatticeTransport.Presheaf
variable {Γ : Context.{1}}

noncomputable def sourceAdmission := admission (Γ := Γ) Int
noncomputable def targetAdmission := admission (Γ := Γ) Int
noncomputable def transport := latticePathData (sourceAdmission (Γ := Γ)) targetAdmission shift
noncomputable def path := (transport (Γ := Γ)).path

theorem source_eq : (transport (Γ := Γ)).source = sourceObject sourceAdmission :=
  latticePathData_source _ _ _
theorem target_eq : (transport (Γ := Γ)).target = targetObject sourceAdmission targetAdmission shift :=
  latticePathData_target _ _ _
theorem path_eq : path (Γ := Γ) = latticePath sourceAdmission targetAdmission shift :=
  latticePathData_path _ _ _

noncomputable def pathRecovery :=
  UaComparison.modelRightInverseAt lattice (transport (Γ := Γ)).source transport.target transport.path
noncomputable def selectedRecovery :=
  equivalenceRecoveryData (sourceAdmission (Γ := Γ)) targetAdmission shift

theorem selectedRecovery_target : (selectedRecovery (Γ := Γ)).target =
    structuredEquivalence sourceAdmission targetAdmission shift :=
  equivalenceRecoveryData_target _ _ _

noncomputable def projectionRecovery :=
  latticeProjectionData (sourceAdmission (Γ := Γ)) targetAdmission shift

noncomputable def witness (p : OrderedPair Int) (x : Γ.Elements) : OrderedPair Int :=
  pathOrderedPair sourceAdmission targetAdmission shift p x

theorem witness_direct (p : OrderedPair Int) (x : Γ.Elements) :
    witness p x = directTransport shift p := pathOrderedPair_direct _ _ _ _ _

theorem witness_value (p : OrderedPair Int) (x : Γ.Elements) :
    (witness p x).val = (p.val.1 + 3, p.val.2 + 3) := by
  rw [witness_direct]; exact direct_value p

theorem witness_gap (p : OrderedPair Int) (x : Γ.Elements) : gap (witness p x) = gap p := by
  rw [witness_direct]; exact direct_gap p

theorem witness_inverse (p : OrderedPair Int) (x : Γ.Elements) :
    pathOrderedPair targetAdmission sourceAdmission shift.symm (witness p x) x = p := by
  rw [pathOrderedPair_direct, witness_direct]; exact direct_recovery p

theorem selected_value (x : Γ.Elements) : (witness selected x).val = (1,7) := by
  rw [witness_direct]; exact NativeTrial692.selected_value

theorem selected_strict (x : Γ.Elements) :
    (witness selected x).val.1 < (witness selected x).val.2 := by
  rw [selected_value]; decide

theorem zero_value (x : Γ.Elements) :
    (targetAdmission.decoding.hom.app x
      ((latticeTransportedPoint sourceAdmission targetAdmission shift 0).val x)).down = 3 :=
  latticeTransportedPoint_decode _ _ _ _ _

noncomputable def nativeSolution (p : OrderedPair Int) (x : Γ.Elements) :=
  pathSolution sourceAdmission targetAdmission shift p x

theorem nativeSolution_recovery (p : OrderedPair Int) (x : Γ.Elements) :
    (presentedSolutionsTransport comparablePair sourceAdmission.decoding targetAdmission.decoding
      shift.toEquiv (fields sourceAdmission) x).symm (nativeSolution p x) =
      orderedWitness sourceAdmission p x := by
  unfold nativeSolution
  rw [pathSolution_moved]
  exact movedWitness_recovery _ _ _ _ _

theorem meet_recovery (x : Γ.Elements) (u v : Int) :
    (decode rawLattice targetAdmission.decoding x
      ((movedFields sourceAdmission targetAdmission shift).val x)).1 u v = u ⊓ v :=
  movedFields_meet _ _ _ _ _ _

theorem join_recovery (x : Γ.Elements) (u v : Int) :
    (decode rawLattice targetAdmission.decoding x
      ((movedFields sourceAdmission targetAdmission shift).val x)).2 u v = u ⊔ v :=
  movedFields_join _ _ _ _ _ _

theorem negation_native_rejected (x : Γ.Elements) :
    ¬ Nonempty ((preserves rawLattice
      (presentedCarrierIso sourceAdmission.decoding sourceAdmission.decoding negation).hom
      (presentedCarrierIso sourceAdmission.decoding sourceAdmission.decoding negation).inv
      (fields sourceAdmission) (fields sourceAdmission)).obj x) := by
  rintro ⟨h⟩
  have hp := ((presentedPreservationEquiv rawLattice sourceAdmission.decoding sourceAdmission.decoding
    negation (fields sourceAdmission) (fields sourceAdmission) x) h).down.down
  rw [fields_decode] at hp
  exact negation_rejected hp

end Presheaf

namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Native StructuredIdentity
open Examples.NativeLatticeTransport.Cartesian
variable {Γ : Context.{1}}

noncomputable def sourceAdmission := admission (Γ := Γ) Int
noncomputable def targetAdmission := admission (Γ := Γ) Int
noncomputable def transport := latticePathData (sourceAdmission (Γ := Γ)) targetAdmission shift
noncomputable def path := (transport (Γ := Γ)).path

theorem source_eq : (transport (Γ := Γ)).source = sourceObject sourceAdmission :=
  latticePathData_source _ _ _
theorem target_eq : (transport (Γ := Γ)).target = targetObject sourceAdmission targetAdmission shift :=
  latticePathData_target _ _ _
theorem path_eq : path (Γ := Γ) = latticePath sourceAdmission targetAdmission shift :=
  latticePathData_path _ _ _

noncomputable def pathRecovery :=
  UaComparison.modelRightInverseAt lattice (transport (Γ := Γ)).source transport.target transport.path
noncomputable def selectedRecovery :=
  equivalenceRecoveryData (sourceAdmission (Γ := Γ)) targetAdmission shift

theorem selectedRecovery_target : (selectedRecovery (Γ := Γ)).target =
    structuredEquivalence sourceAdmission targetAdmission shift :=
  equivalenceRecoveryData_target _ _ _

noncomputable def projectionRecovery :=
  latticeProjectionData (sourceAdmission (Γ := Γ)) targetAdmission shift

noncomputable def witness (p : OrderedPair Int) (x : Γ.Elements) : OrderedPair Int :=
  pathOrderedPair sourceAdmission targetAdmission shift p x

theorem witness_direct (p : OrderedPair Int) (x : Γ.Elements) :
    witness p x = directTransport shift p := pathOrderedPair_direct _ _ _ _ _

theorem witness_value (p : OrderedPair Int) (x : Γ.Elements) :
    (witness p x).val = (p.val.1 + 3, p.val.2 + 3) := by
  rw [witness_direct]; exact direct_value p

theorem witness_gap (p : OrderedPair Int) (x : Γ.Elements) : gap (witness p x) = gap p := by
  rw [witness_direct]; exact direct_gap p

theorem witness_inverse (p : OrderedPair Int) (x : Γ.Elements) :
    pathOrderedPair targetAdmission sourceAdmission shift.symm (witness p x) x = p := by
  rw [pathOrderedPair_direct, witness_direct]; exact direct_recovery p

theorem selected_value (x : Γ.Elements) : (witness selected x).val = (1,7) := by
  rw [witness_direct]; exact NativeTrial692.selected_value

theorem selected_strict (x : Γ.Elements) :
    (witness selected x).val.1 < (witness selected x).val.2 := by
  rw [selected_value]; decide

theorem zero_value (x : Γ.Elements) :
    (targetAdmission.decoding.hom.app x
      ((latticeTransportedPoint sourceAdmission targetAdmission shift 0).val x)).down = 3 :=
  latticeTransportedPoint_decode _ _ _ _ _

noncomputable def nativeSolution (p : OrderedPair Int) (x : Γ.Elements) :=
  pathSolution sourceAdmission targetAdmission shift p x

theorem nativeSolution_recovery (p : OrderedPair Int) (x : Γ.Elements) :
    (presentedSolutionsTransport comparablePair sourceAdmission.decoding targetAdmission.decoding
      shift.toEquiv (fields sourceAdmission) x).symm (nativeSolution p x) =
      orderedWitness sourceAdmission p x := by
  unfold nativeSolution
  rw [pathSolution_moved]
  exact movedWitness_recovery _ _ _ _ _

theorem meet_recovery (x : Γ.Elements) (u v : Int) :
    (decode rawLattice targetAdmission.decoding x
      ((movedFields sourceAdmission targetAdmission shift).val x)).1 u v = u ⊓ v :=
  movedFields_meet _ _ _ _ _ _

theorem join_recovery (x : Γ.Elements) (u v : Int) :
    (decode rawLattice targetAdmission.decoding x
      ((movedFields sourceAdmission targetAdmission shift).val x)).2 u v = u ⊔ v :=
  movedFields_join _ _ _ _ _ _

theorem negation_native_rejected (x : Γ.Elements) :
    ¬ Nonempty ((preserves rawLattice
      (presentedCarrierIso sourceAdmission.decoding sourceAdmission.decoding negation).hom
      (presentedCarrierIso sourceAdmission.decoding sourceAdmission.decoding negation).inv
      (fields sourceAdmission) (fields sourceAdmission)).obj x) := by
  rintro ⟨h⟩
  have hp := ((presentedPreservationEquiv rawLattice sourceAdmission.decoding sourceAdmission.decoding
    negation (fields sourceAdmission) (fields sourceAdmission) x) h).down.down
  rw [fields_decode] at hp
  exact negation_rejected hp

end Cartesian

theorem decoded_models_agree {Γ : SquareKit.Cubical.Presheaf.Context.{1}}
    (p : OrderedPair Int) (x : (SquareKit.Cubical.Cartesian.restrict Γ).Elements) :
    Presheaf.witness p ((SquareKit.Cubical.Cartesian.elements Γ).obj x) =
      Cartesian.witness p x := by
  rw [Presheaf.witness_direct, Cartesian.witness_direct]

end NativeTrial692

#print axioms NativeTrial692.shift
#print axioms NativeTrial692.shift_value
#print axioms NativeTrial692.shift_inverse
#print axioms NativeTrial692.pair
#print axioms NativeTrial692.selected
#print axioms NativeTrial692.direct_value
#print axioms NativeTrial692.direct_recovery
#print axioms NativeTrial692.gap
#print axioms NativeTrial692.direct_gap
#print axioms NativeTrial692.selected_value
#print axioms NativeTrial692.selected_strict
#print axioms NativeTrial692.nonidentity
#print axioms NativeTrial692.meet_preserved
#print axioms NativeTrial692.join_preserved
#print axioms NativeTrial692.negation
#print axioms NativeTrial692.negation_not_monotone
#print axioms NativeTrial692.negation_rejected
#print axioms NativeTrial692.Presheaf.sourceAdmission
#print axioms NativeTrial692.Presheaf.targetAdmission
#print axioms NativeTrial692.Presheaf.transport
#print axioms NativeTrial692.Presheaf.path
#print axioms NativeTrial692.Presheaf.source_eq
#print axioms NativeTrial692.Presheaf.target_eq
#print axioms NativeTrial692.Presheaf.path_eq
#print axioms NativeTrial692.Presheaf.pathRecovery
#print axioms NativeTrial692.Presheaf.selectedRecovery
#print axioms NativeTrial692.Presheaf.selectedRecovery_target
#print axioms NativeTrial692.Presheaf.projectionRecovery
#print axioms NativeTrial692.Presheaf.witness
#print axioms NativeTrial692.Presheaf.witness_direct
#print axioms NativeTrial692.Presheaf.witness_value
#print axioms NativeTrial692.Presheaf.witness_gap
#print axioms NativeTrial692.Presheaf.witness_inverse
#print axioms NativeTrial692.Presheaf.selected_value
#print axioms NativeTrial692.Presheaf.selected_strict
#print axioms NativeTrial692.Presheaf.zero_value
#print axioms NativeTrial692.Presheaf.nativeSolution
#print axioms NativeTrial692.Presheaf.nativeSolution_recovery
#print axioms NativeTrial692.Presheaf.meet_recovery
#print axioms NativeTrial692.Presheaf.join_recovery
#print axioms NativeTrial692.Presheaf.negation_native_rejected
#print axioms NativeTrial692.Cartesian.sourceAdmission
#print axioms NativeTrial692.Cartesian.targetAdmission
#print axioms NativeTrial692.Cartesian.transport
#print axioms NativeTrial692.Cartesian.path
#print axioms NativeTrial692.Cartesian.source_eq
#print axioms NativeTrial692.Cartesian.target_eq
#print axioms NativeTrial692.Cartesian.path_eq
#print axioms NativeTrial692.Cartesian.pathRecovery
#print axioms NativeTrial692.Cartesian.selectedRecovery
#print axioms NativeTrial692.Cartesian.selectedRecovery_target
#print axioms NativeTrial692.Cartesian.projectionRecovery
#print axioms NativeTrial692.Cartesian.witness
#print axioms NativeTrial692.Cartesian.witness_direct
#print axioms NativeTrial692.Cartesian.witness_value
#print axioms NativeTrial692.Cartesian.witness_gap
#print axioms NativeTrial692.Cartesian.witness_inverse
#print axioms NativeTrial692.Cartesian.selected_value
#print axioms NativeTrial692.Cartesian.selected_strict
#print axioms NativeTrial692.Cartesian.zero_value
#print axioms NativeTrial692.Cartesian.nativeSolution
#print axioms NativeTrial692.Cartesian.nativeSolution_recovery
#print axioms NativeTrial692.Cartesian.meet_recovery
#print axioms NativeTrial692.Cartesian.join_recovery
#print axioms NativeTrial692.Cartesian.negation_native_rejected
#print axioms NativeTrial692.decoded_models_agree
