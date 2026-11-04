import Applications.Selection.CoordinateSensitivity

/-! Source sensitivity and the public one-based selection interface. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.CoordinateSensitivity
open Applications.Selection
open Applications.Selection.CoordinateSensitivity

theorem middle_of_triple : (ordered ([8, 1, 5] : List Int))[1]? = some 5 := by
  simp only [ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

/-- This uses the universal theorem for each of the three different positions. -/
theorem every_triple_coordinate (i : Fin 3) :
    ∃ z : Int, (ordered (([8, 1, 5] : List Int).set i.val z))[1]? ≠ some 5 := by
  obtain ⟨z, hz⟩ := exists_set_changes ([8, 1, 5] : List Int) 1 i.val
    (by decide) (by decide) i.isLt
  exact ⟨z, by simpa only [middle_of_triple] using hz⟩

theorem triple_fresh_witness (i : Fin 3) :
    ∃ z : Int, z ∉ ([8, 1, 5] : List Int) ∧
      (ordered (([8, 1, 5] : List Int).set i.val z))[1]? ≠
        (ordered ([8, 1, 5] : List Int))[1]? :=
  exists_fresh_set_changes _ 1 i.val (by decide) (by decide) i.isLt

-- Independently calculated witnesses exercise coordinates above, below and at
-- the original selected value, respectively.
theorem above_coordinate_replaced :
    (ordered (([8, 1, 5] : List Int).set 0 (-1)))[1]? = some 1 := by
  simp only [ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

theorem below_coordinate_replaced :
    (ordered (([8, 1, 5] : List Int).set 1 9))[1]? = some 8 := by
  simp only [ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

theorem selected_coordinate_replaced :
    (ordered (([8, 1, 5] : List Int).set 2 9))[1]? = some 8 := by
  simp only [ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

theorem singleton_sensitive (a : Int) :
    ∃ z : Int, (ordered ([a].set 0 z))[0]? ≠ some a := by
  obtain ⟨z, hz⟩ := exists_set_changes [a] 0 0 (by simp) (by simp) (by simp)
  exact ⟨z, by simpa only [show (ordered [a])[0]? = some a from rfl] using hz⟩

theorem valid_ranks_are_injective :
    Function.Injective
      (fun k : Fin 3 => (ordered ([8, 1, 5] : List Int))[k.val]?) :=
  ordered_index_injective _ (by decide)

/-- The preceding valid-index qualification is necessary. -/
theorem invalid_ranks_agree :
    (ordered ([8, 1, 5] : List Int))[3]? = none ∧
      (ordered ([8, 1, 5] : List Int))[4]? = none := by
  constructor <;> apply List.getElem?_eq_none_iff.mpr <;>
    rw [(ordered_perm _).length_eq] <;> decide

theorem one_based_middle_changes (i : Fin 3) :
    ∃ z : Int, sortSelect 2 (([8, 1, 5] : List Int).set i.val z) ≠
      sortSelect 2 ([8, 1, 5] : List Int) :=
  sortSelect_set_changes _ 1 i.val (by decide) (by decide) i.isLt

theorem last_pivot_middle_changes (i : Fin 3) :
    ∃ z : Int, selectWith lastPivot 2 (([8, 1, 5] : List Int).set i.val z) ≠
      selectWith lastPivot 2 ([8, 1, 5] : List Int) :=
  selectWith_set_changes lastPivot last_pivot_valid _ 1 i.val
    (by decide) (by decide) i.isLt

theorem finite_coordinate_adapter :
    List.ofFn (Function.update (![8, 1, 5] : Fin 3 → Int) 1 9) = [8, 9, 5] := by
  rw [ofFn_update]
  decide +kernel

theorem increasing_input_sensitive (n : Nat) (k i : Fin n) :
    ∃ z : Int,
      (ordered (List.ofFn (Function.update (fun j : Fin n => (j.val : Int)) i z)))[k.val]? ≠
        (ordered (List.ofFn (fun j : Fin n => (j.val : Int))))[k.val]? := by
  apply exists_update_changes
  intro j l he
  exact Fin.ext (Int.ofNat.inj he)

end Examples.CoordinateSensitivity
