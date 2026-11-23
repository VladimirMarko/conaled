import Examples.CompositionalStructureIdentity
import Examples.NativeStructureRecovery
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.Fin.Tuple
import Examples.GeometricMatroids

/-! Order isomorphisms preserve the admitted algebraic lattice presentation.
The dependent client consists of a pair together with its order witness. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.LatticeTransportBridge
open SquareKit.StructureIdentity Examples.CompositionalStructureIdentity
open Examples.NativeStructureRecovery (comparablePair)

variable {X Y Z : Type} [Lattice X] [Lattice Y] [Lattice Z]

theorem orderIso_preserves (e : X ≃o Y) :
    lattice.Preserves e.toEquiv (latticeModel X) (latticeModel Y) :=
  ⟨(binary_preserves _ _ _).mpr e.map_inf,
    (binary_preserves _ _ _).mpr e.map_sup⟩

theorem orderIso_transport (e : X ≃o Y) :
    lattice.transport e.toEquiv (latticeModel X) = latticeModel Y :=
  (lattice.preserves_iff _ _ _).mp (orderIso_preserves e)

/-- The order witness is part of the value, not an external assumption. -/
def OrderedPair (X : Type) [LE X] := {p : X × X // p.1 ≤ p.2}

def directTransport (e : X ≃o Y) : OrderedPair X ≃ OrderedPair Y where
  toFun p := ⟨(e p.val.1, e p.val.2), e.monotone p.property⟩
  invFun p := ⟨(e.symm p.val.1, e.symm p.val.2), e.symm.monotone p.property⟩
  left_inv p := by apply Subtype.ext; exact Prod.ext (e.symm_apply_apply _) (e.symm_apply_apply _)
  right_inv p := by apply Subtype.ext; exact Prod.ext (e.apply_symm_apply _) (e.apply_symm_apply _)

def solutionOrderEquiv : comparablePair.Solutions (latticeModel X).val ≃ OrderedPair X where
  toFun p := ⟨p.val, inf_eq_left.mp p.property⟩
  invFun p := ⟨p.val, show p.val.1 ⊓ p.val.2 = p.val.1 from inf_eq_left.mpr p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem solution_transport_direct (e : X ≃o Y)
    (p : comparablePair.Solutions (latticeModel X).val) :
    solutionOrderEquiv (comparablePair.solutionEquiv e.toEquiv (orderIso_preserves e) p) =
      directTransport e (solutionOrderEquiv p) := rfl

theorem directTransport_trans (e : X ≃o Y) (f : Y ≃o Z) (p : OrderedPair X) :
    directTransport (e.trans f) p = directTransport f (directTransport e p) := rfl

def swap : (Bool × Bool) ≃o (Bool × Bool) where
  toEquiv := Equiv.prodComm _ _
  map_rel_iff' := and_comm

def ordered : OrderedPair (Bool × Bool) := ⟨((false, false), (true, false)), by decide⟩

example : (directTransport swap ordered).val = ((false, false), (false, true)) := rfl
example : swap (true, false) ≠ (true, false) := by decide
example : directTransport swap.symm (directTransport swap ordered) = ordered :=
  (directTransport swap).symm_apply_apply _

/-- Complementing both coordinates is a bijection but reverses this order. -/
def badBijection : (Bool × Bool) ≃ (Bool × Bool) := complement.prodCongr complement

theorem badBijection_rejected :
    ¬ lattice.Preserves badBijection (latticeModel (Bool × Bool)) (latticeModel (Bool × Bool)) := by
  intro h
  have hh := (binary_preserves badBijection _ _).mp h.1 (false, false) (true, false)
  have bad := congrArg Prod.fst hh
  change true = false at bad
  exact Bool.noConfusion bad

/-- Complement is an order isomorphism to the dual lattice, not to the original order. -/
def dualBool : Bool ≃o OrderDual Bool where
  toEquiv := complement
  map_rel_iff' := by intro a b; cases a <;> cases b <;> decide

def boolInclusion : OrderedPair Bool := ⟨(false, true), by decide⟩

example : (directTransport dualBool boolInclusion).val = (true, false) := rfl

/-- Function and product presentations of the four-element Boolean lattice. -/
def tupleBridge : (Fin 2 → Bool) ≃o (Bool × Bool) := OrderIso.finTwoArrowIso Bool

def tupleOrdered : OrderedPair (Fin 2 → Bool) := directTransport tupleBridge.symm ordered

theorem tuple_ordered_recovery : directTransport tupleBridge tupleOrdered = ordered :=
  (directTransport tupleBridge).apply_symm_apply ordered

/-- The existing geometric-lattice representation supplies a distinct target carrier. -/
noncomputable def flatsBridge := Examples.GeometricMatroids.booleanFlats

def inclusion : OrderedPair (Set (Fin 2)) := ⟨(∅, {0}), Set.empty_subset _⟩

noncomputable def flatInclusion := directTransport flatsBridge inclusion

theorem flats_transport :
    lattice.transport flatsBridge.toEquiv (latticeModel (Set (Fin 2))) =
      latticeModel (Applications.Matroid.Flat (Applications.Matroid.Geometric.matroid (Set (Fin 2)))) :=
  orderIso_transport flatsBridge

theorem flatInclusion_strict : flatInclusion.val.1 ≠ flatInclusion.val.2 := by
  intro h
  have h' := flatsBridge.injective h
  change (∅ : Set (Fin 2)) = {0} at h'
  have : (0 : Fin 2) ∈ (∅ : Set (Fin 2)) := h'.symm ▸ Set.mem_singleton 0
  exact this

end Examples.LatticeTransportBridge
