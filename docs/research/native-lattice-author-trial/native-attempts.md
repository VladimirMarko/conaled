# Native attempt archive

Frozen #692 trial evidence. Original relative paths and SHA-256 hashes follow. Failed source versions and outputs are retained verbatim; they are not integrated declarations. Generated olean binaries are omitted.

## Native.lean

SHA-256: `59157c5d9b4b78b469a48c3d4db1d1ff0220c33c9b5f4218fffbf373e711a9b1`

````text
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
````

## attempts/01.lean

SHA-256: `ffe5b26c192be000ec39517d0f95b7344c9a05525ef9ed24c98ea4fe8bd00629`

````text
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
      left_inv := by intro z; omega
      right_inv := by intro z; omega }
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
````

## attempts/01.log

SHA-256: `c5eb351817feb7509da451144a91282955a1b6cc262afe8a05e5bbb23a6d2ab1`

````text
[0mdirenv: loading ~/Code/conaled/.envrc
[0mdirenv: using flake
[0mdirenv: nix-direnv: Using cached dev shell
input file '/tmp/conaled-692-evidence/native/Native.lean' must be contained in root directory (/home/vlad/Code/conaled/)
````

## attempts/01.time

SHA-256: `0013f85ee1238554bc79309834849da221990d994f761c64a36eb01196c6792a`

````text
{
  "user_seconds": 0.301018,
  "system_seconds": 0.359367,
  "peak_rss_kb": 799168
}
````

## attempts/02.lean

SHA-256: `ffe5b26c192be000ec39517d0f95b7344c9a05525ef9ed24c98ea4fe8bd00629`

````text
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
      left_inv := by intro z; omega
      right_inv := by intro z; omega }
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
````

## attempts/02.log

SHA-256: `f2ec06f16f4177e3489577617a0b137b3ce7f75fd5691aed2613680ec9a5a73e`

````text
[0mdirenv: loading ~/Code/conaled/.envrc
[0mdirenv: using flake
[0mdirenv: nix-direnv: Using cached dev shell
/tmp/conaled-692-evidence/native/Native.lean:16:30: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a - b ≥ 1
where
 a := z
 b := (fun z => z - 3) ((fun z => z + 3) z)
/tmp/conaled-692-evidence/native/Native.lean:17:31: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a - b ≥ 1
where
 a := z
 b := (fun z => z + 3) ((fun z => z - 3) z)
````

## attempts/02.time

SHA-256: `0eb3f52cfc4c65724bc0f1c4dedf3a44f4e31edc9be04eba2c62014c1c6e9d1f`

````text
{
  "user_seconds": 2.100842,
  "system_seconds": 0.8985289999999999,
  "peak_rss_kb": 3592804
}
````

## attempts/03.lean

SHA-256: `59157c5d9b4b78b469a48c3d4db1d1ff0220c33c9b5f4218fffbf373e711a9b1`

````text
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
````

## attempts/03.log

SHA-256: `4fe35a2492d9201df8cf54e4afd4c5cd23123487259dc3a07d995c18050b42a9`

````text
[0mdirenv: loading ~/Code/conaled/.envrc
[0mdirenv: using flake
[0mdirenv: nix-direnv: Using cached dev shell
'NativeTrial692.shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.shift_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.shift_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.pair' does not depend on any axioms
'NativeTrial692.selected' does not depend on any axioms
'NativeTrial692.direct_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.direct_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.gap' does not depend on any axioms
'NativeTrial692.direct_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.selected_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.selected_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.nonidentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.meet_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.join_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.negation' depends on axioms: [propext]
'NativeTrial692.negation_not_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.negation_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.sourceAdmission' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.targetAdmission' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.path' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.source_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.target_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.path_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.pathRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.selectedRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.selectedRecovery_target' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.projectionRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.witness_direct' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.witness_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.witness_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.witness_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.selected_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.selected_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.nativeSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.nativeSolution_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.meet_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.join_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Presheaf.negation_native_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.sourceAdmission' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.targetAdmission' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.path' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.source_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.target_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.path_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.pathRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.selectedRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.selectedRecovery_target' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.projectionRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.witness_direct' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.witness_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.witness_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.witness_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.selected_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.selected_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.nativeSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.nativeSolution_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.meet_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.join_recovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.Cartesian.negation_native_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'NativeTrial692.decoded_models_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
````

## attempts/03.time

SHA-256: `b9486a9373bc3aa82c7e8a08a8bdb6da65941812ec490ed4f2a45730523958c1`

````text
{
  "user_seconds": 2.235019,
  "system_seconds": 0.866439,
  "peak_rss_kb": 3607992
}
````

## environment-errors.txt

SHA-256: `2ee1be79772bf1924590a0fc1f8ba16ac8b008150b7c4190795bef1fb94dd5aa`

````text
Before any Lean invocation: python3 unavailable outside direnv; reran generation through direnv. /usr/bin/time absent; initial runner launch failed before subprocess started, switched to Python resource.getrusage. The source snapshot 01 made before failed launch was identical to invocation 01. No proof/API assistance received.
````

## invocations.jsonl

SHA-256: `089f5ee063b64538943c5b1acc81a463894e710edf662a6d95b5e04c0385bac5`

````text
{"invocation": 1, "source": "/tmp/conaled-692-evidence/native/attempts/01.lean", "sha256": "ffe5b26c192be000ec39517d0f95b7344c9a05525ef9ed24c98ea4fe8bd00629", "command": ["timeout", "30s", "direnv", "exec", "/home/vlad/Code/conaled", "lake", "env", "lean", "-o", "/tmp/conaled-692-evidence/native/Native.olean", "/tmp/conaled-692-evidence/native/Native.lean"], "clock_start": "2026-11-24T00:14:47.541714+00:00", "clock_end": "2026-11-24T00:14:48.001426+00:00", "lock_wait_seconds": 1.711399818304926e-05, "elapsed_seconds": 0.4595035590027692, "exit_status": 1, "resource_metrics": "/tmp/conaled-692-evidence/native/attempts/01.time", "output": "/tmp/conaled-692-evidence/native/attempts/01.log"}
{"invocation": 2, "source": "/tmp/conaled-692-evidence/native/attempts/02.lean", "sha256": "ffe5b26c192be000ec39517d0f95b7344c9a05525ef9ed24c98ea4fe8bd00629", "command": ["timeout", "30s", "direnv", "exec", "/home/vlad/Code/conaled", "lake", "env", "lean", "-R", "/tmp/conaled-692-evidence/native", "-o", "/tmp/conaled-692-evidence/native/Native.olean", "/tmp/conaled-692-evidence/native/Native.lean"], "clock_start": "2026-11-24T00:14:54.379708+00:00", "clock_end": "2026-11-24T00:14:56.553122+00:00", "lock_wait_seconds": 3.559600736480206e-05, "elapsed_seconds": 2.173086221999256, "exit_status": 1, "resource_metrics": "/tmp/conaled-692-evidence/native/attempts/02.time", "output": "/tmp/conaled-692-evidence/native/attempts/02.log"}
{"invocation": 3, "source": "/tmp/conaled-692-evidence/native/attempts/03.lean", "sha256": "59157c5d9b4b78b469a48c3d4db1d1ff0220c33c9b5f4218fffbf373e711a9b1", "command": ["timeout", "30s", "direnv", "exec", "/home/vlad/Code/conaled", "lake", "env", "lean", "-R", "/tmp/conaled-692-evidence/native", "-o", "/tmp/conaled-692-evidence/native/Native.olean", "/tmp/conaled-692-evidence/native/Native.lean"], "clock_start": "2026-11-24T00:15:20.929824+00:00", "clock_end": "2026-11-24T00:15:23.061415+00:00", "lock_wait_seconds": 1.6264006262645125e-05, "elapsed_seconds": 2.131377218000125, "exit_status": 0, "resource_metrics": "/tmp/conaled-692-evidence/native/attempts/03.time", "output": "/tmp/conaled-692-evidence/native/attempts/03.log"}
````

## report.md

SHA-256: `44e0b5effda5a0e430e90f35c185e1df480fdd78754e66194964ae4f62860031`

````text
# Native author trial #692

Outcome: success at invocation 3, stopped after the successful check. Final source: `Native.lean`; emitted object: `Native.olean`. The final source hash is `59157c5d9b4b78b469a48c3d4db1d1ff0220c33c9b5f4218fffbf373e711a9b1`. Protocol hash: `fd834e2f03128c234ad9d493afc4f43237c62af300a663a5def32a16a4d19377`. Baseline checked after compilation: `a38e05358d47f1739aa2f1fbcae8f9cc0d120f86`.

The protocol selected gpt-6-astra/high. Runtime model details were not inspected or self-attested. This report records one bounded agent-author observation. Prior library preparation in #621/#691 is excluded from this client effort. No model adoption or general productivity conclusion follows.

## Checked contracts

The independently written `shift` order isomorphism maps integers by addition of 3, with subtraction of 3 as inverse. `direct_value`, `direct_recovery`, and `direct_gap` apply to every dependent ordered pair, including the supplied `pair x y h` for arbitrary `x ≤ y`. The source proof remains part of the subtype value in recovery. `selected_value` and `selected_strict` check that (-2,4) becomes (1,7) with strict order. `nonidentity` checks 0 maps to 3 and differs from 0. `meet_preserved` and `join_preserved` exercise the order isomorphism's lattice laws. `negation_not_monotone` uses 0 ≤ 1, and `negation_rejected` refutes preservation of the admitted lattice presentation via its meet law.

Both `Presheaf` and `Cartesian` namespaces instantiate actual public admissions for Int, independently name the source and target, and construct `transport` with `latticePathData`. The source, target and path are connected to the public law-bearing path by `source_eq`, `target_eq`, and `path_eq`.

In each model, `selectedRecovery` retains the complete selected structured equivalence and its native left-inverse path through `equivalenceRecoveryData`; `selectedRecovery_target` identifies the selected complete target. `pathRecovery` applies `UaComparison.modelRightInverseAt` to the actual law-bearing path, retaining its complete native two-path. Inspection of these public result types confirmed that they recover the whole equivalence/path, rather than only an underlying function. `projectionRecovery` retains the public projection recovery.

Each `witness` calls `pathOrderedPair`, whose public construction uses universal-decoder transport along the law-bearing path projection. `witness_direct` proves equality of complete subtype values with the direct mathematical transport. `witness_value`, `witness_gap`, `witness_inverse`, the selected value and strictness, and `zero_value` establish the integer observations. `nativeSolution_recovery` reconstructs the complete actual path solution, uses `pathSolution_moved`, and applies inverse presented solution transport to recover the original complete native ordered witness. `meet_recovery` and `join_recovery` decode the transported fields. `negation_native_rejected` refutes an inhabitant of the actual native preservation family through `presentedPreservationEquiv` and the independently proved rejecting control.

`decoded_models_agree` compares the complete dependent ordered-pair values across restriction from the presheaf model to the Cartesian model. It does not equate independently selected ua paths.

## Statement review

The domain is ordinary Int with its existing order and lattice instances, not the order dual. All universal pair theorems quantify over the proof-bearing subtype; no additional preservation or recovery assumption is supplied by callers. The positive selected example and the explicit negation control make the expected order direction observable. Recovery equalities concern complete dependent values. Native recovery witnesses are homogeneous paths supplied by the public API, not Lean equalities between selected ua paths. All expectations are the frozen integer arithmetic and order expectations from the protocol.

## Invocation evidence

`invocations.jsonl` contains exact command arrays, source snapshots and hashes, output and resource files, UTC start/end, monotonic wall duration, lock wait and exit status. Every actual Lean invocation used the shared lock and a 30 second timeout. Snapshots and logs are under `attempts/`. Default maxRecDepth 512 and maxHeartbeats 200000 were retained; no limit overrides, transparency changes or kernel bypass were used.

| Invocation | Exit | Wall seconds | Result |
|---|---:|---:|---|
| 1 | 1 | 0.459504 | Lean rejected an external input without an explicit external root. |
| 2 | 1 | 2.173086 | Two inverse proofs failed because omega did not reduce the nested function applications. |
| 3 | 0 | 2.131377 | Passed after explicit arithmetic goals were given with `change`; all authored axiom queries passed. |

Total measured invocation wall time: 4.763967 seconds. Total shared-lock wait: 0.000069 seconds. Peak child RSS across runs: 3607992 KiB. User/system counters and per-run RSS are in `.time` files. Wall timings conservatively include direnv/Lake launch overhead. The successful check ended at `2026-11-24T00:15:23.061415+00:00`. The author did not capture an assignment-time clock reading; assignment-to-success elapsed time must use the orchestrator's assignment timestamp. The earliest explicit clock captured during source reading was `2026-11-24T00:13:04Z`.

Before Lean invocation 1, two environment launches failed: Python was unavailable outside direnv; then `/usr/bin/time` was unavailable. The wrapper switched to Python's child resource counters. Those events are recorded in `environment-errors.txt`. The source snapshot made by the failed `/usr/bin/time` launch was identical to invocation 1. No mathematical conclusion is drawn from these environmental or encoding errors.

The final run printed axiom dependencies for all 66 explicitly authored definitions and theorems. Only `propext`, `Classical.choice`, and `Quot.sound` occurred; some declarations used none. No `sorry`, `admit`, new axiom, `native_decide`, or equivalent bypass occurs in the final file. The repository-wide integrated build/audit was not run inside this frozen client trial; integration validation belongs to the orchestrator's later workflow.

## Sources and assistance

Read the allowed public bridge, native transport, cases and geometric example, and the relevant native UaComparison recovery definitions. The geometric example supplied the existing public client pattern for packaged path/recovery values. Common integer setup and arithmetic/rejection proofs were independently authored. Read repository task, formal-development, domain, architecture, environment, validation and EDD guidance. No sibling attempt, web, external agent, or proof/API help was used. No subagent was spawned. Parent communications supplied only the original task/protocol and received progress updates. No repository file or imported artifact was edited.
````

## run.py

SHA-256: `7791b0eac3b0be9862e72a3c669ffde69dd508548c9c917353fb7b5d9d542a65`

````text
from pathlib import Path
import datetime, fcntl, hashlib, json, os, subprocess, time, resource
base=Path('/tmp/conaled-692-evidence/native')
manifest=base/'invocations.jsonl'
rows=[json.loads(s) for s in manifest.read_text().splitlines()] if manifest.exists() else []
assert len(rows)<25
assert sum(r['elapsed_seconds'] for r in rows)<480
n=len(rows)+1
prefix=base/'attempts'/f'{n:02}'
source=base/'Native.lean'
snapshot=Path(str(prefix)+'.lean'); snapshot.write_bytes(source.read_bytes())
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
wait_start=time.monotonic()
with open('/tmp/conaled-native-followups-lake.lock','w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 wait=time.monotonic()-wait_start
 command=['timeout','30s','direnv','exec','/home/vlad/Code/conaled','lake','env','lean','-R',str(base),'-o',str(base/'Native.olean'),str(source)]
 t=time.monotonic()
 with open(str(prefix)+'.log','w') as output:
  result=subprocess.run(command,cwd='/home/vlad/Code/conaled',stdout=output,stderr=subprocess.STDOUT)
 elapsed=time.monotonic()-t
 usage=resource.getrusage(resource.RUSAGE_CHILDREN)
 Path(str(prefix)+'.time').write_text(json.dumps(dict(user_seconds=usage.ru_utime,system_seconds=usage.ru_stime,peak_rss_kb=usage.ru_maxrss),indent=2))
 record=dict(invocation=n,source=str(snapshot),sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),command=command,clock_start=start,clock_end=datetime.datetime.now(datetime.timezone.utc).isoformat(),lock_wait_seconds=wait,elapsed_seconds=elapsed,exit_status=result.returncode,resource_metrics=str(prefix)+'.time',output=str(prefix)+'.log')
 with manifest.open('a') as f: f.write(json.dumps(record)+'\n')
 print(json.dumps(record,indent=2)); print(Path(str(prefix)+'.log').read_text())
````
