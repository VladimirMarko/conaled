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
  exact runsOn_of_sorted id [1, 1, 2, 3] (by decide) (by simp)

/-- The returned flattened list is a permutation, not the chronological input. -/
theorem descending_reversal : runsBy natLT [4, 3, 2, 1] = [[1, 2, 3, 4]] := by
  exact runsOn_of_strictly_descending id [4, 3, 2, 1] (by decide) (by simp)

/-- The source's nonempty hypothesis cannot be removed from its one-run law. -/
theorem empty_is_not_one_run : runsOn id ([] : List Nat) ≠ [[]] := by
  simp [runsOn]

/-- Equal keys preserve both arbitrary payloads without requiring payload instances. -/
theorem payloads_need_no_structure {β : Type} (p q : β) :
    runsOn Prod.fst [(1 : Nat, p), (1, q)] = [[(1, p), (1, q)]] := by
  apply runsOn_of_sorted
  · simp [KeySorted]
  · simp

/-- Individual runs are ordered even when their flattened concatenation is not. -/
theorem restart_blocks_sorted :
    ∀ run ∈ runsBy natLT [1, 3, 2, 4], KeySorted id run :=
  runsOn_sorted id [1, 3, 2, 4]

theorem restart_flatten_not_sorted :
    ¬KeySorted id (runsBy natLT [1, 3, 2, 4]).flatten := by
  rw [restart_boundary]
  decide

abbrev Record := Int × String

def mixedRecords : List Record := [(3, "A"), (2, "B"), (2, "C"), (1, "D")]
def mixedRuns : List (List Record) := [[(2, "B"), (3, "A")], [(1, "D"), (2, "C")]]

/-- A tie ends the first strict descent, retaining both distinct key-2 records. -/
theorem mixed_records : runsOn Prod.fst mixedRecords = mixedRuns := by
  simp [runsOn, mixedRecords, mixedRuns, runsBy_cons_cons, descBy_cons]

theorem mixed_occurrences : ((runsOn Prod.fst mixedRecords).flatten : Multiset Record) =
    (mixedRecords : Multiset Record) :=
  runsBy_multiset _ mixedRecords

theorem mixed_expected_blocks_sorted : ∀ run ∈ mixedRuns, KeySorted Prod.fst run := by
  rw [← mixed_records]
  exact runsOn_sorted Prod.fst mixedRecords

theorem mixed_shape :
    (runsOn Prod.fst mixedRecords).length = 2 ∧
    (runsOn Prod.fst mixedRecords).flatten.length = 4 ∧
    ∀ run ∈ runsOn Prod.fst mixedRecords, run ≠ [] := by
  refine ⟨?_, runsBy_flatten_length _ mixedRecords, runsBy_nonempty _ mixedRecords⟩
  rw [mixed_records]
  rfl

/-- This concrete observation does not assert arbitrary-worker stability. -/
theorem mixed_equal_key_order :
    (runsOn Prod.fst mixedRecords).flatten.filter (fun r => decide (r.1 = 2)) =
      [(2, "B"), (2, "C")] := by
  rw [mixed_records]
  decide

theorem weak_descent_with_ties :
    runsOn Prod.fst ([(3, "A"), (3, "B"), (2, "C")] : List Record) =
      [[(3, "A"), (3, "B")], [(2, "C")]] := by
  simp [runsOn, runsBy_cons_cons, ascBy_cons, Batteries.DList.singleton]

theorem weak_descent_not_one_reversal :
    runsOn Prod.fst ([(3, "A"), (3, "B"), (2, "C")] : List Record) ≠
      [[(2, "C"), (3, "B"), (3, "A")]] := by
  rw [weak_descent_with_ties]
  decide

def nonnegativeLT (a b : Record) : Bool :=
  if 0 ≤ a.1 ∧ 0 ≤ b.1 then decide (a.1 < b.1) else false

theorem nonnegative_compatible :
    ∀ a ∈ mixedRecords, ∀ b ∈ mixedRecords,
      (nonnegativeLT a b = true → a.1 ≤ b.1) ∧
      (nonnegativeLT a b = false → b.1 ≤ a.1) := by
  intro a ha b hb
  simp only [mixedRecords, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> decide

/-- The input-local contract applies despite deliberate bad behavior on negative keys. -/
theorem local_comparator_sorted :
    ∀ run ∈ runsBy nonnegativeLT mixedRecords, KeySorted Prod.fst run :=
  runsBy_sorted_compatible_on Prod.fst nonnegativeLT mixedRecords nonnegative_compatible

theorem local_comparator_is_not_globally_compatible :
    ¬(nonnegativeLT (-2, "x") (-1, "y") = false → (-1 : Int) ≤ -2) := by
  decide

def seededBuilder (xs : List Nat) : List Nat := [1, 3] ++ xs

theorem seededBuilder_law : DListLaw seededBuilder := by
  intro xs ys
  simp [seededBuilder, List.append_assoc]

/-- This lawful source function is supplied directly, with no scanner history. -/
theorem arbitrary_builder_restart :
    ascSourceBy natLT 5 seededBuilder seededBuilder_law [4, 6] = [[1, 3, 5], [4, 6]] := by
  simp [ascSourceBy_cons, ascSourceBy_nil, seededBuilder, natLT, runsBy_cons_cons,
    ascBy_cons, Batteries.DList.singleton, Batteries.DList.push]

theorem arbitrary_builder_occurrences :
    (ascSourceBy natLT 5 seededBuilder seededBuilder_law [4, 6]).flatten.Perm
      [1, 3, 5, 4, 6] :=
  ascSourceBy_perm natLT 5 seededBuilder seededBuilder_law [4, 6]

theorem arbitrary_builder_length :
    (ascSourceBy natLT 5 seededBuilder seededBuilder_law [4, 6]).flatten.length = 5 := by
  simpa [seededBuilder] using
    ascSourceBy_flatten_length natLT 5 seededBuilder seededBuilder_law [4, 6]

/-- The worker's run bound counts the remaining tail, not its supplied prefix. -/
theorem arbitrary_builder_run_bound :
    (ascSourceBy natLT 5 seededBuilder seededBuilder_law [4, 6]).length ≤ 3 :=
  ascBy_length_le natLT 5 (dListOfLaw seededBuilder seededBuilder_law) [4, 6]

theorem arbitrary_builder_sorted :
    ∀ run ∈ ascSourceBy natLT 5 seededBuilder seededBuilder_law [4, 6],
      KeySorted id run := by
  apply ascSourceBy_sorted id 5 seededBuilder seededBuilder_law [4, 6]
  · decide
  · simp [seededBuilder]

def unsortedBuilder (xs : List Nat) : List Nat := [2, 1] ++ xs

theorem unsortedBuilder_law : DListLaw unsortedBuilder := by
  intro xs ys
  simp [unsortedBuilder, List.append_assoc]

theorem unsorted_builder_value :
    ascSourceBy natLT 3 unsortedBuilder unsortedBuilder_law [] = [[2, 1, 3]] := by
  rw [ascSourceBy_nil]
  rfl

/-- The D law suffices for full occurrences, but not for ordering the supplied prefix. -/
theorem lawful_builder_does_not_imply_sorted :
    (ascSourceBy natLT 3 unsortedBuilder unsortedBuilder_law []).flatten.Perm [2, 1, 3] ∧
    ¬KeySorted id (ascSourceBy natLT 3 unsortedBuilder unsortedBuilder_law []).flatten := by
  refine ⟨ascSourceBy_perm natLT 3 unsortedBuilder unsortedBuilder_law [], ?_⟩
  rw [unsorted_builder_value]
  decide

/-- A sorted prefix alone also fails when the current element violates its bound. -/
theorem sorted_prefix_needs_upper_bound :
    KeySorted id (Batteries.DList.ofList ([2] : List Nat)).toList ∧
    ¬KeySorted id (ascBy natLT 1 (Batteries.DList.ofList [2]) []).flatten := by
  constructor
  · rw [Batteries.DList.toList_ofList]
    decide
  · rw [ascBy_nil]
    decide

def equalAccumulator : List Record := [(2, "earlier")]
def equalCurrent : Record := (2, "later")

theorem weak_descending_value :
    descBy (fun x y : Record => decide (x.1 < y.1)) equalCurrent equalAccumulator [] =
      [[(2, "later"), (2, "earlier")]] := by
  rw [descBy_nil]
  rfl

/-- The source's weak descending premises are satisfiable at this tied state. -/
theorem weak_descending_sorted :
    ∀ run ∈ descBy (fun x y : Record => decide (x.1 < y.1))
      equalCurrent equalAccumulator [], KeySorted Prod.fst run := by
  apply descBy_sorted Prod.fst equalCurrent equalAccumulator []
  · decide
  · simp [equalAccumulator, equalCurrent]

theorem weak_descending_occurrences :
    (descBy (fun x y : Record => decide (x.1 < y.1))
      equalCurrent equalAccumulator []).flatten.Perm [(2, "earlier"), (2, "later")] :=
  descBy_perm _ equalCurrent equalAccumulator []

/-- Arbitrary weakly ordered descending states need not preserve equal-key payload order. -/
theorem weak_descending_not_stable :
    ¬Stable Prod.fst ([(2, "earlier"), (2, "later")] : List Record)
      (descBy (fun x y : Record => decide (x.1 < y.1))
        equalCurrent equalAccumulator []).flatten := by
  intro h
  have hk := h 2
  rw [weak_descending_value] at hk
  simp at hk

end Examples.NaturalRuns
