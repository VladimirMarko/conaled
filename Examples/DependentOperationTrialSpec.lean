import SquareKit.DependentOperation.SelectorBase

/-! Independent mathematical task oracle for #358. This file defines only
position operations and fixed expected results. It supplies no new compiler,
machine realization, substitution proof or author submission. -/
namespace Examples.DependentOperationTrialSpec
open SquareKit.DependentOperation.Selector

def rotate (n) (i : Position n) : Position n :=
  ⟨(i.val+1) % (n+1), Nat.mod_lt _ (by omega)⟩

def half (n) (i : Position n) : Position n := ⟨i.val/2, by have := i.isLt; omega⟩

def compress (n) (i : Position n) : Position (n/2) := ⟨i.val/2, by have := i.isLt; omega⟩

def backward (n) (i : Position n) : Position n :=
  ⟨(i.val+n) % (n+1), Nat.mod_lt _ (by omega)⟩

def stageOne (i : Position 4) := rotate 4 i

def stageTwo (i : Position 5) := half 5 (rotate 5 (half 5 (rotate 5 i)))

def stageThree (i : Position 8) : Position 7 :=
  operate (.insert 6) (operate (.reflect 6) (rotate 6 (operate (.pad 4)
    (operate (.reflect 4) (compress 9 (operate (.insert 8) (half 8 (rotate 8 i))))))))

example : stageOne 3 = 4 := rfl
example : stageTwo 4 = 1 := rfl
example : stageThree 6 = 3 := rfl
example : stageThree (Fin.rev 6) = 2 := rfl
example : stageThree (Fin.rev 0) = 1 := rfl

/-- The changed local contract changes the independently expected result. -/
example : backward 4 3 = 2 := rfl
example : rotate 4 3 ≠ backward 4 3 := by decide

end Examples.DependentOperationTrialSpec
