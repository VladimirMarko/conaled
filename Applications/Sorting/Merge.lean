import Applications.Sorting.Stable

/-! Standard left-tie merging, with input-local compatibility laws. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

abbrev mergeBy [LE κ] [DecidableLE κ] (key : α → κ) (xs ys : List α) : List α :=
  List.merge xs ys (fun x y => decide (key x ≤ key y))

theorem mergeBy_perm [LE κ] [DecidableLE κ] (key : α → κ) (xs ys : List α) :
    (mergeBy key xs ys).Perm (xs ++ ys) := List.merge_perm_append _

theorem merge_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xs ys : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ ys, (cmp a b = true → key a ≤ key b) ∧
      (cmp a b = false → key b ≤ key a))
    (hx : KeySorted key xs) (hy : KeySorted key ys) :
    KeySorted key (List.merge xs ys cmp) := by
  match xs, ys with
  | [], ys => simpa using hy
  | xs, [] => simpa using hx
  | x :: xs, y :: ys => 
    rw [List.cons_merge_cons]
    split
    · rename_i hxy
      have hle := (hc x (by simp) y (by simp)).1 hxy
      apply List.pairwise_cons.mpr
      constructor
      · intro z hz
        rcases List.mem_merge.mp hz with hz | hz
        · exact (List.pairwise_cons.mp hx).1 z hz
        · rcases List.mem_cons.mp hz with he | hz
          · subst z; exact hle
          · exact Std.le_trans hle ((List.pairwise_cons.mp hy).1 z hz)
      · exact merge_sorted_compatible_on key cmp xs (y :: ys)
          (fun a ha b hb => hc a (by simp [ha]) b hb) (List.pairwise_cons.mp hx).2 hy
    · rename_i hxy
      have hle := (hc x (by simp) y (by simp)).2 (Bool.eq_false_iff.mpr hxy)
      apply List.pairwise_cons.mpr
      constructor
      · intro z hz
        rcases List.mem_merge.mp hz with hz | hz
        · rcases List.mem_cons.mp hz with he | hz
          · subst z; exact hle
          · exact Std.le_trans hle ((List.pairwise_cons.mp hx).1 z hz)
        · exact (List.pairwise_cons.mp hy).1 z hz
      · exact merge_sorted_compatible_on key cmp (x :: xs) ys
          (fun a ha b hb => hc a ha b (by simp [hb])) hx (List.pairwise_cons.mp hy).2
termination_by xs.length + ys.length

theorem merge_sorted_compatible [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool)
    (hc : ∀ a b, (cmp a b = true → key a ≤ key b) ∧
      (cmp a b = false → key b ≤ key a))
    (xs ys : List α) (hx : KeySorted key xs) (hy : KeySorted key ys) :
    KeySorted key (List.merge xs ys cmp) :=
  merge_sorted_compatible_on key cmp xs ys (fun a _ b _ => hc a b) hx hy

theorem mergeBy_sorted [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs ys : List α) (hx : KeySorted key xs) (hy : KeySorted key ys) :
    KeySorted key (mergeBy key xs ys) := by
  apply merge_sorted_compatible key _ _ xs ys hx hy
  intro a b
  exact ⟨of_decide_eq_true, fun h => 
    (Std.le_total (a := key a) (b := key b)).resolve_left (of_decide_eq_false h)⟩

theorem mergeBy_filter [LE κ] [DecidableLE κ] [Std.IsPreorder κ] [DecidableEq κ]
    (key : α → κ) (xs ys : List α) (hx : KeySorted key xs) (hy : KeySorted key ys)
    (k : κ) :
    (mergeBy key xs ys).filter (fun a => decide (key a = k)) =
      xs.filter (fun a => decide (key a = k)) ++ ys.filter (fun a => decide (key a = k)) := by
  match xs, ys with
  | [], ys => simp [mergeBy]
  | xs, [] => simp [mergeBy]
  | x :: xs, y :: ys => 
    unfold mergeBy
    rw [List.cons_merge_cons]
    simp only [decide_eq_true_eq]
    by_cases hxy : key x ≤ key y
    · rw [ite_eq_left hxy]
      have ih := mergeBy_filter key xs (y :: ys) (List.pairwise_cons.mp hx).2 hy k
      simp only [mergeBy, List.filter_cons, decide_eq_true_eq] at ih ⊢
      by_cases hxk : key x = k
      · simp only [ite_eq_left hxk, List.cons_append]
        exact congrArg (List.cons x) ih
      · simp only [ite_eq_right hxk]
        exact ih
    · rw [ite_eq_right hxy]
      have ih := mergeBy_filter key (x :: xs) ys hx (List.pairwise_cons.mp hy).2 k
      by_cases hyk : key y = k
      · have hempty : (x :: xs).filter (fun a => decide (key a = k)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro a ha
          have hxa : key x ≤ key a := by
            rcases List.mem_cons.mp ha with rfl | ha
            · exact Std.le_refl _
            · exact (List.pairwise_cons.mp hx).1 a ha
          simp only [decide_eq_true_eq]
          intro hak
          apply hxy
          simpa only [hak, ←hyk] using hxa
        change (y :: mergeBy key (x :: xs) ys).filter _ = _
        rw [hempty]
        simp only [List.nil_append, List.filter_cons, decide_eq_true_eq, ite_eq_left hyk]
        rw [ih, hempty]
        rfl
      · simpa only [mergeBy, List.filter_cons, decide_eq_true_eq, ite_eq_right hyk] using ih
termination_by xs.length + ys.length

theorem mergeBy_stable [LE κ] [DecidableLE κ] [Std.IsPreorder κ] [DecidableEq κ]
    (key : α → κ) (xs ys : List α) (hx : KeySorted key xs) (hy : KeySorted key ys) :
    Stable key (xs ++ ys) (mergeBy key xs ys) := by
  intro k
  rw [mergeBy_filter key xs ys hx hy, List.filter_append]

/-- Merging sorted blocks realizes stable sorting of their concatenation. -/
theorem mergeBy_spec [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] [DecidableEq κ]
    (key : α → κ) (xs ys : List α) (hx : KeySorted key xs) (hy : KeySorted key ys) :
    StableSort key (xs ++ ys) (mergeBy key xs ys) :=
  ⟨mergeBy_sorted key xs ys hx hy, mergeBy_perm key xs ys, mergeBy_stable key xs ys hx hy⟩

end Applications.Sorting
