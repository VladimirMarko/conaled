import SquareKit.AssemblySliceCoherence
import SquareKit.AssemblySlicePullback
import Examples.AssemblyPartialMaps

/-! Selected-data, bottom and changing-base cases for the tracked lift (#386). -/

namespace AssemblyLifting
open Realizability Realizability.Assembly CategoryTheory
open Encodable
open Nat.Partrec (Code)

abbrev N := encoded Nat

theorem join_defined : (programLiftMul N).toFun (some (some (17 : Nat))) = some (17 : Nat) := rfl

theorem join_inner_bottom : (programLiftMul N).toFun (some none) = none := rfl

theorem join_outer_bottom : (programLiftMul N).toFun none = none := rfl

theorem flatten_loses_outer_definedness :
    (some none : (programLift (programLift N)).Carrier) ≠ none ∧
      (programLiftMul N).toFun (some none) = (programLiftMul N).toFun none :=
  ⟨(by intro h; cases h), rfl⟩

/-- This realizer terminates twice, returning the selected natural number. -/
theorem nested_program_realizes :
    (programLift (programLift N)).realizes
      (encode (Code.const (encode (Code.const (17 : Nat))))) (some (some (17 : Nat))) := by
  refine ⟨encode (Code.const (17 : Nat)), ?_, (17 : Nat), ?_, rfl⟩ <;> simp [Code.eval_const]

/-- The multiplication tracker works on every realizer, including the
constructed nested program; its output realizes exactly 17. -/
theorem multiplication_tracks_selected :
    ∃ φ, Nat.Partrec φ ∧ ∃ n,
      n ∈ φ (encode (Code.const (encode (Code.const (17 : Nat))))) ∧
        (programLift N).realizes n (some (17 : Nat)) := by
  obtain ⟨φ, hp, ht⟩ := (programLiftMul N).tracked
  exact ⟨φ, hp, ht _ _ nested_program_realizes⟩

def successor : Hom N N := ofComputable Nat.succ Computable.succ

example : (programLiftMap (programLiftMap successor)).comp (programLiftMul N) =
    (programLiftMul N).comp (programLiftMap successor) := programLiftMul_natural successor

example : (programLiftUnit (programLift N)).comp (programLiftMul N) =
    Hom.id (programLift N) := programLiftMul_left_unit N

example : (programLiftMap (programLiftUnit N)).comp (programLiftMul N) =
    Hom.id (programLift N) := programLiftMul_right_unit N

example : (programLiftMap (programLiftMul N)).comp (programLiftMul N) =
    (programLiftMul (programLift N)).comp (programLiftMul N) := programLiftMul_assoc N

/-- A genuine varying family: the first coordinate determines the fiber,
while the second is selected data which must survive base change. -/
def family : Hom (prod N N) N := fst N N

def selectedInput : (pullback (successor.comp successor) (sliceBase family)).Carrier :=
  ⟨((3 : Nat), ⟨((5 : Nat), some ((5 : Nat), (17 : Nat))), fun _ h => by cases h; rfl⟩), rfl⟩

def selectedOutput : (pullback (successor.comp successor) family).Carrier :=
  ⟨((3 : Nat), ((5 : Nat), (17 : Nat))), rfl⟩

theorem comparison_keeps_selected :
    ((baseChangeLift family (successor.comp successor)).toFun selectedInput).val.2 =
      some selectedOutput :=
  (baseChangeLift_graph _ _ _ _).mpr ⟨rfl, rfl⟩

theorem comparison_keeps_base :
    ((baseChangeLift family (successor.comp successor)).toFun selectedInput).val.1 = (3 : Nat) :=
  congrArg (fun k => k.toFun selectedInput) (baseChangeLift_base family (successor.comp successor))

def bottomInput : (pullback (successor.comp successor) (sliceBase family)).Carrier :=
  ⟨((3 : Nat), ⟨((5 : Nat), none), fun _ h => by cases h⟩), rfl⟩

theorem comparison_keeps_bottom :
    ((baseChangeLift family (successor.comp successor)).toFun bottomInput).val.2 = none :=
  baseChangeLift_none _ _ _ rfl

theorem comparison_inverse_recovers :
    (baseChangeUnlift family (successor.comp successor)).toFun
      ((baseChangeLift family (successor.comp successor)).toFun selectedInput) = selectedInput :=
  congrArg (fun k => k.toFun selectedInput) (baseChangeLift_unlift _ _)

example : (baseChangeUnlift family (Hom.id N)).comp (pullbackIdentity (sliceBase family)) =
    sliceMap (pullbackFst (Hom.id N) family) family (pullbackIdentity family)
      (pullback_square (Hom.id N) family).symm := baseChange_identity family

/-- The two-step coherence theorem applies to two nonidentity changes and
therefore preserves the chosen 17 through the iterated pullback route. -/
example :
    ((baseChangeUnlift (pullbackFst successor family) successor).comp
      (pullbackMap (sliceBase (pullbackFst successor family)) (pullbackFst successor (sliceBase family))
        successor (baseChangeUnlift family successor) (baseChangeUnlift_base family successor))).comp
      (pullbackUnassoc (sliceBase family) successor successor) =
    (sliceMap (pullbackFst successor (pullbackFst successor family))
      (pullbackFst (successor.comp successor) family)
      (pullbackUnassoc family successor successor) (Hom.ext fun _ => rfl)).comp
      (baseChangeUnlift family (successor.comp successor)) := baseChange_comp _ _ _

/-- A slice classifier handles the undecidable halting domain from P1,
retaining its selected input index and total base. -/
noncomputable def haltingSlice : Hom N (sliceLift (Hom.id N)) :=
  sliceClassify (Hom.id N) (Hom.id N) AssemblyPartialMaps.haltingIdentity (fun _ _ => rfl)

theorem haltingSlice_graph (n m : Nat) :
    (haltingSlice.toFun n).val.2 = some m ↔ (run n).Dom ∧ n = m :=
  AssemblyPartialMaps.haltingIdentity_graph n m

/-- The tempting ordinary-lift pullback excludes every bottom, unlike the
slice lift. This holds for every tracked family, not only the fixture. -/
theorem unit_pullback_excludes_bottom {A B : Assembly} (p : Hom A B)
    (d : (pullback (programLiftUnit B) (programLiftMap p)).Carrier) : d.val.2 ≠ none := by
  intro h
  have hd := d.property
  change some d.val.1 = Option.map p.toFun d.val.2 at hd
  rw [h] at hd
  cases hd

theorem slice_bottom_at_three :
    ((sliceBottom family).toFun (3 : Nat)).val.1 = (3 : Nat) ∧ ((sliceBottom family).toFun (3 : Nat)).val.2 = none :=
  ⟨rfl, sliceBottom_value family (3 : Nat)⟩

end AssemblyLifting
