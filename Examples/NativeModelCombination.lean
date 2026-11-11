module

public import Applications.ModelCombination.ActionObservation
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Logic.Equiv.Bool
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-! Independent native inputs and expected meanings for bounded model combination. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace NativeModelCombination.Examples

abbrev BooleanXOR := Multiplicative Bool

example (m : BooleanXOR) (x : Bool) : m • x = (m.toAdd ^^ x) := rfl

def boolFin : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun y := y.val == 1
  left_inv b := by cases b <;> rfl
  right_inv y := by
    fin_cases y <;> rfl

def boolObserve (y : Fin 2) : Bool := y.val == 1

theorem bool_point : boolFin false = 0 := rfl

theorem bool_native (m : BooleanXOR) (x : Bool) :
    boolObserve (boolFin (m • x)) = (m.toAdd ^^ x) := by
  cases m <;> cases x <;> rfl

instance : MulAction (FreeMonoid Nat) (List Nat) where
  smul m xs := m.toList ++ xs
  one_smul _ := rfl
  mul_smul m n xs := List.append_assoc m.toList n.toList xs

def listPair : List Nat ≃ List Nat × PUnit where
  toFun xs := (xs,PUnit.unit)
  invFun ys := ys.1
  left_inv _ := rfl
  right_inv ys := by rcases ys with ⟨ys,⟨⟩⟩; rfl

def lengthObserve (ys : List Nat × PUnit) : Nat := ys.1.length

theorem list_point : listPair [] = ([],PUnit.unit) := rfl

theorem list_native (pfx : FreeMonoid Nat) (xs : List Nat) :
    lengthObserve (listPair (pfx • xs)) = pfx.toList.length + xs.length :=
  List.length_append

theorem ordered_expected :
    (FreeMonoid.ofList [8,9] : FreeMonoid Nat) • [4] = [8,9,4] := rfl

theorem length_expected : lengthObserve ([8,9,4],PUnit.unit) = 3 := rfl

def boolean : Combination BooleanXOR false (0 : Fin 2) false boolObserve Bool :=
  combine false 0 false boolObserve boolFin bool_point

theorem boolean_once : boolean.out ((Multiplicative.ofAdd true) • false) = true := by
  exact (boolean.action_output boolFin rfl (Multiplicative.ofAdd true) false).trans (by rfl)

theorem boolean_twice :
    boolean.out ((Multiplicative.ofAdd true) • ((Multiplicative.ofAdd true) • false)) = false := by
  rw [← boolean.mixed]
  rfl

theorem boolean_right_recovery (y : Fin 2) : boolean.out (boolean.right.symm y) = boolObserve y :=
  boolean.right_observation y

theorem boolean_left_recovery (m : BooleanXOR) (x : Bool) :
    boolean.left (m • boolean.left.symm x) = (m.toAdd ^^ x) := by
  have h := congrFun (congrFun boolean.left_reduct m) x
  exact h

/-- The selected result constant need not be the observation of the state point. -/
def differentConstant : Combination BooleanXOR false (0 : Fin 2) true boolObserve Bool :=
  combine false 0 true boolObserve boolFin bool_point

theorem independent_result_constant : differentConstant.out differentConstant.point ≠
    differentConstant.resultPoint := by decide

def listCombined : Combination (FreeMonoid Nat) ([] : List Nat)
    ([],PUnit.unit) 0 lengthObserve (List Nat) :=
  combine [] ([],PUnit.unit) 0 lengthObserve listPair list_point

theorem prefix_observation (pfx : FreeMonoid Nat) (xs : List Nat) :
    listCombined.out (pfx • xs) = pfx.toList.length + xs.length := by
  exact (listCombined.action_output listPair rfl pfx xs).trans (list_native pfx xs)

theorem prefix_caller :
    listCombined.out ((FreeMonoid.ofList [8,9] : FreeMonoid Nat) • [4]) = 3 := by
  rw [prefix_observation]
  rfl

theorem prefix_mixed (m n : FreeMonoid Nat) (xs : List Nat) :
    listCombined.out ((m*n) • xs) = listCombined.out (m • (n • xs)) :=
  listCombined.mixed m n xs

theorem list_right_recovery (ys : List Nat × PUnit) :
    listCombined.out (listCombined.right.symm ys) = lengthObserve ys :=
  listCombined.right_observation ys

theorem retains_ordered_state :
    listCombined.left ((FreeMonoid.ofList [8,9] : FreeMonoid Nat) • [4]) = [8,9,4] := by
  rw [listCombined.left_action]
  exact ordered_expected

theorem right_recovers_order : listCombined.right.symm ([9,8],PUnit.unit) = [9,8] := rfl

theorem observation_not_injective : ¬ Function.Injective lengthObserve := by
  intro h
  have hh := h (a₁ := ([8,9],PUnit.unit)) (a₂ := ([9,8],PUnit.unit)) (by rfl)
  have hn := congrArg (fun ys => ys.1.head?) hh
  contradiction

instance : MulAction BooleanXOR PUnit where
  smul _ _ := PUnit.unit
  one_smul x := Subsingleton.elim _ x
  mul_smul _ _ _ := rfl

/-- Both supplied components exist, but their required invertible overlap does not. -/
theorem singleton_overlap_impossible (e : PUnit ≃ Bool) : False := by
  have h : e.symm false = e.symm true := Subsingleton.elim _ _
  have h' : false = true := e.symm.injective h
  contradiction

theorem no_singleton_combination {Z : Type*} [MulAction BooleanXOR Z]
    (C : Combination BooleanXOR PUnit.unit false false (id : Bool → Bool) Z) : False :=
  singleton_overlap_impossible C.overlap

/-- Every alternative joint presentation satisfying the same recovery and overlap
fails the extra invariance axiom, not only the canonical formula. -/
theorem no_invariant_alternative {Z : Type*} [MulAction BooleanXOR Z]
    (C : Combination BooleanXOR false (0 : Fin 2) false boolObserve Z)
    (sameOverlap : C.overlap = boolFin) :
    ¬ ∀ (m : BooleanXOR) (z : Z), C.out (m • z) = C.out z := by
  intro invariant
  have h := invariant (Multiplicative.ofAdd true) (C.left.symm false)
  rw [C.action_output boolFin sameOverlap, C.output boolFin sameOverlap] at h
  change true = false at h
  contradiction

/-- A different valid presentation demonstrates that raw output functions and
chosen state points need not agree before applying the recovery maps. -/
def flipped : Combination BooleanXOR false (0 : Fin 2) false boolObserve Bool where
  point := true
  resultPoint := false
  out z := boolObserve (boolFin (!z))
  left := Equiv.boolNot
  right := Equiv.boolNot.trans boolFin
  left_point := rfl
  right_point := rfl
  result_point := rfl
  left_action m z := by cases m <;> cases z <;> rfl
  right_observation y := by fin_cases y <;> rfl

theorem flipped_overlap : flipped.overlap = boolFin := by
  apply Equiv.ext
  intro x
  cases x <;> rfl

theorem flipped_not_invariant :
    ¬ ∀ (m : BooleanXOR) (x : Bool), flipped.out (m • x) = flipped.out x :=
  no_invariant_alternative flipped flipped_overlap

theorem presentations_differ : flipped.out false ≠ boolean.out false := by decide

theorem boolean_not_invariant :
    ¬ ∀ (m : BooleanXOR) (x : Bool), boolean.out (m • x) = boolean.out x :=
  no_invariant_alternative boolean rfl

end NativeModelCombination.Examples
