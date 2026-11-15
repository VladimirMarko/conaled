import Applications.Sorting.NaturalRuns

/-! Consequential source branches and arbitrary lawful worker accumulators. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.NaturalRuns
open Applications.Sorting

def natLT (a b : Nat) : Bool := decide (a < b)

theorem empty_payload : runsBy (fun a _ : Empty => nomatch a) [] = [] :=
  runsBy_nil _

theorem singleton : runsBy natLT [7] = [[7]] := runsBy_singleton _ _

/-- The first failed ascending boundary restarts at 2, without dropping it. -/
theorem restart_boundary : runsBy natLT [1, 3, 2, 4] = [[1, 3], [2, 4]] := by
  simp [natLT, runsBy_cons_cons, ascBy_cons, Batteries.DList.singleton,
    Batteries.DList.push]

/-- Equal adjacent keys belong to the ascending run. -/
theorem ascending_ties : runsBy natLT [1, 1, 2, 3] = [[1, 1, 2, 3]] := by
  simp [natLT, runsBy_cons_cons, ascBy_cons, Batteries.DList.singleton,
    Batteries.DList.push]

/-- The returned flattened list is a permutation, not the chronological input. -/
theorem descending_reversal : runsBy natLT [4, 3, 2, 1] = [[1, 2, 3, 4]] := by
  simp [natLT, runsBy_cons_cons, descBy_cons]

def seededBuilder (xs : List Nat) : List Nat := [1, 3] ++ xs

theorem seededBuilder_law : DListLaw seededBuilder := by
  intro xs ys
  simp [seededBuilder, List.append_assoc]

/-- This lawful source function is supplied directly, with no scanner history. -/
theorem arbitrary_builder_restart :
    ascSourceBy natLT 5 seededBuilder seededBuilder_law [4, 6] = [[1, 3, 5], [4, 6]] := by
  simp [ascSourceBy_cons, ascSourceBy_nil, seededBuilder, natLT, runsBy_cons_cons,
    ascBy_cons, Batteries.DList.singleton, Batteries.DList.push]

end Examples.NaturalRuns
