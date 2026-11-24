module
public import Applications.ModelCombination.SignatureTransport
public import Examples.NativeModelCombination

/-! Three operation presentations on one frozen native contract. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace NativeModelCombination.StateOperations
open Examples
abbrev X := List Nat
abbrev Y : Type := List Nat × PUnit
abbrev overlap : X ≃ Y := listPair

def suppliedJoin (x y : Y) : Y := (x.1 ++ y.1, PUnit.unit)
def suppliedUnit : Y := ([], PUnit.unit)

theorem supplied_assoc (x y z : Y) :
    suppliedJoin (suppliedJoin x y) z = suppliedJoin x (suppliedJoin y z) := by
  simp [suppliedJoin, List.append_assoc]
theorem supplied_left_unit (y : Y) : suppliedJoin suppliedUnit y = y := by
  rcases y with ⟨ys,⟨⟩⟩; simp [suppliedJoin, suppliedUnit]
theorem supplied_right_unit (y : Y) : suppliedJoin y suppliedUnit = y := by
  rcases y with ⟨ys,⟨⟩⟩; simp [suppliedJoin, suppliedUnit]

def combined : Combination (FreeMonoid Nat) ([4] : X) ([4],PUnit.unit) 17 lengthObserve X :=
  combine [4] ([4],PUnit.unit) 17 lengthObserve overlap rfl

def direct (x y : X) : X := overlap.symm (suppliedJoin (overlap x) (overlap y))
def helper : X → X → X := OperationTransport.binary overlap suppliedJoin

def signature (x y : X) : X :=
  let : SignatureTransport.language.Structure Y :=
    SignatureTransport.suppliedStructure suppliedJoin suppliedUnit
  let : SignatureTransport.language.Structure X := overlap.symm.inducedStructure
  FirstOrder.Language.Structure.funMap (L := SignatureTransport.language) SignatureTransport.Symbol.join
    (fun i => if i = 0 then x else y)

theorem direct_recovery (x y : Y) : overlap (direct (overlap.symm x) (overlap.symm y)) =
    suppliedJoin x y := by simp [direct]
theorem direct_assoc (x y z : X) : direct (direct x y) z = direct x (direct y z) := by
  apply overlap.injective
  simpa [direct] using supplied_assoc (overlap x) (overlap y) (overlap z)
theorem direct_left_unit (x : X) : direct (overlap.symm suppliedUnit) x = x := by
  apply overlap.injective
  simpa [direct] using supplied_left_unit (overlap x)
theorem direct_right_unit (x : X) : direct x (overlap.symm suppliedUnit) = x := by
  apply overlap.injective
  simpa [direct] using supplied_right_unit (overlap x)

theorem helper_recovery (x y : Y) : overlap (helper (overlap.symm x) (overlap.symm y)) =
    suppliedJoin x y := OperationTransport.recover_binary overlap suppliedJoin x y
theorem helper_assoc (x y z : X) : helper (helper x y) z = helper x (helper y z) :=
  OperationTransport.associative overlap suppliedJoin supplied_assoc x y z
theorem helper_left_unit (x : X) : helper (overlap.symm suppliedUnit) x = x :=
  OperationTransport.left_unit overlap suppliedJoin suppliedUnit supplied_left_unit x
theorem helper_right_unit (x : X) : helper x (overlap.symm suppliedUnit) = x :=
  OperationTransport.right_unit overlap suppliedJoin suppliedUnit supplied_right_unit x

theorem signature_eq_helper : signature = helper := rfl
theorem signature_assoc (x y z : X) : signature (signature x y) z = signature x (signature y z) :=
  SignatureTransport.associative overlap suppliedJoin suppliedUnit supplied_assoc x y z

theorem signature_recovery (x y : Y) :
    overlap (signature (overlap.symm x) (overlap.symm y)) = suppliedJoin x y :=
  helper_recovery x y
theorem signature_left_unit (x : X) : signature (overlap.symm suppliedUnit) x = x :=
  SignatureTransport.left_unit overlap suppliedJoin suppliedUnit supplied_left_unit x
theorem signature_right_unit (x : X) : signature x (overlap.symm suppliedUnit) = x :=
  SignatureTransport.right_unit overlap suppliedJoin suppliedUnit supplied_right_unit x

theorem presentations : direct = helper ∧ signature = helper := ⟨rfl,rfl⟩
theorem native_meaning (x y : X) : helper x y = x ++ y := rfl
example : direct [8,9] [4] = [8,9,4] := rfl
example : signature [8,9] [4] = [8,9,4] := rfl
example : combined.out (helper [8,9] [4]) = 3 := rfl
example : combined.point ≠ overlap.symm suppliedUnit := by decide
example : combined.out combined.point ≠ combined.resultPoint := by decide

/-- Explicit agreement admits the actual native concatenation as a shared operation. -/
theorem shared_append : (fun x y : X => x ++ y) = helper :=
  (OperationTransport.common_iff overlap _ suppliedJoin).mpr (fun _ _ => rfl)

/-- Carrier identification alone does not make a different native operation agree. -/
theorem shared_projection_rejected : (fun x _ : X => x) ≠ helper := by
  intro h
  have hh := congrFun (congrFun h []) [4]
  change ([] : List Nat) = [4] at hh
  contradiction

/-- The false mixed equation fails for the actual supplied action and concatenation. -/
theorem prefix_not_distributive :
    ¬ ∀ (p : FreeMonoid Nat) (x y : X), p • helper x y = helper (p • x) (p • y) := by
  intro h
  have hh := h (FreeMonoid.ofList [8]) [] []
  change ([8] : List Nat) = [8,8] at hh
  contradiction

/-- Every alternative carrier with these complete recoveries has the same obstruction. -/
theorem no_distributive_alternative {Z : Type*} [MulAction (FreeMonoid Nat) Z]
    (C : Combination (FreeMonoid Nat) ([4] : X) ([4],PUnit.unit) 17 lengthObserve Z)
    (op : Z → Z → Z) (recover : ∀ z w, C.left (op z w) = C.left z ++ C.left w) :
    ¬ ∀ (p : FreeMonoid Nat) z w, p • op z w = op (p • z) (p • w) := by
  intro h
  have hh := congrArg C.left (h (FreeMonoid.ofList [8]) (C.left.symm []) (C.left.symm []))
  simp only [C.left_action, recover, Equiv.apply_symm_apply] at hh
  change ([8] : List Nat) = [8,8] at hh
  contradiction

-- Retain the stronger pre-existing universal rejections and native Boolean/list clients.
example := boolean_once
example := retains_ordered_state
example := independent_result_constant
example := @no_singleton_combination
example := @no_invariant_alternative
end NativeModelCombination.StateOperations
