module

public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Algebra.FreeMonoid.Basic
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

end NativeModelCombination.Examples
