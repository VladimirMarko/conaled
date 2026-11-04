import Applications.Selection.Consumers
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Init.Data.List.Nat.Count

/-!
Coordinate sensitivity of integer selection (FDSA, Exercise 3.4).

The book observation is the zero-based index of `ordered`. The public
one-based selectors are connected separately. This file proves sensitivity;
an execution model and a query lower bound belong to `CoordinateQueries`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection.CoordinateSensitivity
universe u
variable {α : Type u} {n : Nat}

private theorem exists_above (xs : List Int) :
    ∃ z : Int, ∀ x ∈ xs, x < z := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨max x z + 1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have h := le_max_left x z
      omega
    · have h := le_max_right x z
      have h' := hz y hy
      omega

private theorem exists_below (xs : List Int) :
    ∃ z : Int, ∀ x ∈ xs, z < x := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨min x z - 1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have h := min_le_left x z
      omega
    · have h := min_le_right x z
      have h' := hz y hy
      omega

/-- The hint in Exercise 3.4 applies only to valid occurrence indices. -/
theorem ordered_index_injective [LinearOrder α] (xs : List α) (hd : xs.Nodup) :
    Function.Injective (fun k : Fin xs.length => (ordered xs)[k.val]?) := by
  intro i j hij
  have hi : i.val < (ordered xs).length := by
    rw [(ordered_perm xs).length_eq]
    exact i.isLt
  have hj : j.val < (ordered xs).length := by
    rw [(ordered_perm xs).length_eq]
    exact j.isLt
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hij
  have hs : (ordered xs).Nodup := (ordered_perm xs).nodup_iff.mpr hd
  exact Fin.ext (hs.getElem_inj.mp (Option.some.inj hij))

/-- A fresh replacement can change any valid rank at any valid input coordinate.
The fresh witness is proved to exist, not supplied as an input assumption. -/
theorem exists_fresh_set_changes (xs : List Int) (k i : Nat)
    (hd : xs.Nodup) (hk : k < xs.length) (hi : i < xs.length) :
    ∃ z : Int, z ∉ xs ∧
      (ordered (xs.set i z))[k]? ≠ (ordered xs)[k]? := by
  have hk' : k < (ordered xs).length := by
    rwa [(ordered_perm xs).length_eq]
  let a : Int := (ordered xs)[k]
  have ha : (ordered xs)[k]? = some a := List.getElem?_eq_getElem hk'
  have haMem : a ∈ xs :=
    (ordered_perm xs).mem_iff.mp (List.mem_of_getElem? ha)
  have hr : RankedAt xs k a := ranked_iff_index.mpr ha
  have hcount := (ranked_strict_counts xs k a hd hr).2
  by_cases hx : xs[i] ≤ a
  · obtain ⟨z, hz⟩ := exists_above xs
    have hzFresh : z ∉ xs := fun hm => (lt_irrefl z) (hz z hm)
    refine ⟨z, hzFresh, ?_⟩
    intro he
    have hr' : RankedAt (xs.set i z) k a := ranked_iff_index.mpr (he.trans ha)
    have hcount' := (ranked_strict_counts (xs.set i z) k a
      (hd.set hzFresh) hr').2
    simp only [List.length_set] at hcount'
    have hupdate := List.countP_set (p := fun x => decide (a < x)) (a := z) hi
    have hnot : ¬ a < xs[i] := not_lt_of_ge hx
    have haz : a < z := hz a haMem
    simp only [decide_eq_true_eq, hnot, haz, ↓reduceIte, Nat.sub_zero] at hupdate
    omega
  · obtain ⟨z, hz⟩ := exists_below xs
    have hzFresh : z ∉ xs := fun hm => (lt_irrefl z) (hz z hm)
    refine ⟨z, hzFresh, ?_⟩
    intro he
    have hr' : RankedAt (xs.set i z) k a := ranked_iff_index.mpr (he.trans ha)
    have hcount' := (ranked_strict_counts (xs.set i z) k a
      (hd.set hzFresh) hr').2
    simp only [List.length_set] at hcount'
    have hupdate := List.countP_set (p := fun x => decide (a < x)) (a := z) hi
    have hxi : a < xs[i] := lt_of_not_ge hx
    have hnot : ¬ a < z := not_lt_of_ge (le_of_lt (hz a haMem))
    have hpositive : 0 < xs.countP (fun x => decide (a < x)) :=
      List.countP_pos_iff.mpr ⟨xs[i], List.getElem_mem hi, by simpa using hxi⟩
    simp only [decide_eq_true_eq, hxi, hnot, ↓reduceIte, Nat.add_zero] at hupdate
    omega

/-- Exactly the zero-based coordinate-sensitivity conclusion of Exercise 3.4. -/
theorem exists_set_changes (xs : List Int) (k i : Nat)
    (hd : xs.Nodup) (hk : k < xs.length) (hi : i < xs.length) :
    ∃ z : Int, (ordered (xs.set i z))[k]? ≠ (ordered xs)[k]? := by
  obtain ⟨z, _, hz⟩ := exists_fresh_set_changes xs k i hd hk hi
  exact ⟨z, hz⟩

/-- The same sensitivity at public one-based rank `k+1`. -/
theorem sortSelect_set_changes (xs : List Int) (k i : Nat)
    (hd : xs.Nodup) (hk : k < xs.length) (hi : i < xs.length) :
    ∃ z : Int, sortSelect (k + 1) (xs.set i z) ≠ sortSelect (k + 1) xs := by
  obtain ⟨z, hz⟩ := exists_set_changes xs k i hd hk hi
  exact ⟨z, by simpa [sortSelect] using hz⟩

/-- Pivot-policy independence transports values, without attaching a cost model. -/
theorem selectWith_set_changes (choose : List Int → Option Int)
    (hv : PivotValid choose) (xs : List Int) (k i : Nat)
    (hd : xs.Nodup) (hk : k < xs.length) (hi : i < xs.length) :
    ∃ z : Int, selectWith choose (k + 1) (xs.set i z) ≠
      selectWith choose (k + 1) xs := by
  simpa only [selectWith_eq_sortSelect choose hv] using
    sortSelect_set_changes xs k i hd hk hi

/-- Coordinate updates commute with the standard finite-function/list adapter. -/
theorem ofFn_update (input : Fin n → α) (i : Fin n) (z : α) :
    List.ofFn (Function.update input i z) = (List.ofFn input).set i.val z := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  by_cases he : j = i.val
  · subst j
    simp only [List.getElem_ofFn, List.getElem_set_self, Function.update_self]
  · rw [List.getElem_ofFn, List.getElem_set_ne (Ne.symm he), List.getElem_ofFn]
    apply Function.update_of_ne
    intro h
    exact he (congrArg Fin.val h)

/-- Sensitivity with the exact input representation consumed by query protocols. -/
theorem exists_update_changes (input : Fin n → Int) (k i : Fin n)
    (hd : Function.Injective input) :
    ∃ z : Int,
      (ordered (List.ofFn (Function.update input i z)))[k.val]? ≠
        (ordered (List.ofFn input))[k.val]? := by
  obtain ⟨z, hz⟩ := exists_set_changes (List.ofFn input) k.val i.val
    (List.nodup_ofFn_ofInjective hd) (by simpa using k.isLt) (by simpa using i.isLt)
  exact ⟨z, by simpa only [ofFn_update] using hz⟩

end Applications.Selection.CoordinateSensitivity
