import Applications.Sorting.Merge

/-! The bounded source adapter retains only the textbook's left-tie recurrence. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting

universe u v
variable {α : Type u} {κ : Type v}

/-- Literal source recurrence; public algorithms use standard `List.merge`. -/
def sourceMerge [LE α] [DecidableLE α] : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x ≤ y then x :: sourceMerge xs (y :: ys) else y :: sourceMerge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

theorem sourceMerge_eq_merge [LE α] [DecidableLE α] (xs ys : List α) :
    sourceMerge xs ys = List.merge xs ys (fun x y => decide (x ≤ y)) := by
  induction xs, ys using sourceMerge.induct with
  | case1 ys => simp [sourceMerge]
  | case2 x xs => simp [sourceMerge]
  | case3 x xs y ys h ih => simp [sourceMerge, h, ih]
  | case4 x xs y ys h ih => simp [sourceMerge, h, ih]

/-- Pulling back key order recovers the source without ordering the records. -/
theorem mergeBy_source [LE κ] [DecidableLE κ] (key : α → κ) (xs ys : List α) :
    letI : LE α := ⟨fun x y => key x ≤ key y⟩
    letI : DecidableLE α := fun x y => inferInstanceAs (Decidable (key x ≤ key y))
    sourceMerge xs ys = mergeBy key xs ys := by
  let : LE α := ⟨fun x y => key x ≤ key y⟩
  let : DecidableLE α := fun x y => inferInstanceAs (Decidable (key x ≤ key y))
  exact sourceMerge_eq_merge xs ys

end Applications.Sorting
