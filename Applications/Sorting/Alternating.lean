import Applications.Sorting.Merge

/-! Alternating accumulator piles and their merge sorter, as requested by
Exercise 2.5. The splitter traverses the input once by consuming two heads
and consing one onto each pile. Its piles reverse alternate occurrences;
ordinary sorting correctness therefore does not imply stable key sorting.
No numerical execution-cost formula is asserted here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
open scoped List
universe u v
variable {α : Type u} {κ : Type v}

/-- One pass builds reversed alternating piles, retaining both supplied accumulators. -/
def halve : List α → List α × List α → List α × List α
  | [], acc => acc
  | [x], (left, right) => (x :: left, right)
  | x :: y :: xs, (left, right) => halve xs (x :: left, y :: right)

@[simp] theorem halve_nil (acc : List α × List α) : halve [] acc = acc := rfl

@[simp] theorem halve_singleton (x : α) (left right : List α) :
    halve [x] (left, right) = (x :: left, right) := rfl

theorem halve_cons_cons (x y : α) (xs left right : List α) :
    halve (x :: y :: xs) (left, right) = halve xs (x :: left, y :: right) := rfl

/-- Every input and accumulator occurrence is retained, without an element equality test. -/
theorem halve_perm (xs left right : List α) :
    ((halve xs (left, right)).1 ++ (halve xs (left, right)).2).Perm
      (xs ++ left ++ right) := by
  match xs with
  | [] => simp
  | [x] => simp
  | x :: y :: rest =>
    rw [halve_cons_cons]
    calc
      _ ~ rest ++ (x :: left) ++ (y :: right) :=
        halve_perm rest (x :: left) (y :: right)
      _ ~ x :: (rest ++ (left ++ y :: right)) := List.perm_middle
      _ ~ x :: (rest ++ y :: (left ++ right)) :=
        ((List.Perm.refl rest).append List.perm_middle).cons x
      _ ~ (x :: y :: rest) ++ left ++ right := by
        simpa only [List.cons_append, List.append_assoc] using
          (List.perm_middle (a := y) (l₁ := rest) (l₂ := left ++ right)).cons x
termination_by xs.length

theorem mem_halve (xs left right : List α) (x : α) :
    x ∈ (halve xs (left, right)).1 ∨ x ∈ (halve xs (left, right)).2 ↔
      x ∈ xs ∨ x ∈ left ∨ x ∈ right := by
  simpa only [List.mem_append, or_assoc] using (halve_perm xs left right).mem_iff (a := x)

/-- The left pile receives the extra occurrence on odd input lengths. -/
theorem halve_lengths (xs left right : List α) :
    (halve xs (left, right)).1.length = left.length + (xs.length + 1) / 2 ∧
      (halve xs (left, right)).2.length = right.length + xs.length / 2 := by
  match xs with
  | [] => simp
  | [x] => simp
  | x :: y :: rest =>
    rw [halve_cons_cons]
    have h := halve_lengths rest (x :: left) (y :: right)
    simp only [List.length_cons] at h ⊢
    omega
termination_by xs.length

/-- The numbers added to arbitrary piles differ by at most one.
The final pile sizes need not be balanced when their starting sizes differ. -/
theorem halve_balance (xs left right : List α) :
    (halve xs (left, right)).2.length - right.length ≤
        (halve xs (left, right)).1.length - left.length ∧
      (halve xs (left, right)).1.length - left.length ≤
        (halve xs (left, right)).2.length - right.length + 1 := by
  have h := halve_lengths xs left right
  omega

theorem halve_empty_balance (xs : List α) :
    (halve xs ([], [])).2.length ≤ (halve xs ([], [])).1.length ∧
      (halve xs ([], [])).1.length ≤ (halve xs ([], [])).2.length + 1 := by
  simpa using halve_balance xs [] []

/-- Only a nontrivial input is recursively sorted; both actual piles then shrink. -/
theorem halve_strict (xs : List α) (hn : 2 ≤ xs.length) :
    (halve xs ([], [])).1.length < xs.length ∧
      (halve xs ([], [])).2.length < xs.length := by
  have h := halve_lengths xs [] []
  simp only [List.length_nil, Nat.zero_add] at h
  omega

/-- Explicit two-base-case sorter using the actual alternating piles. -/
def sortAlternatingBy (cmp : α → α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
      let parts := halve (x :: y :: xs) ([], [])
      List.merge (sortAlternatingBy cmp parts.1) (sortAlternatingBy cmp parts.2) cmp
termination_by xs => xs.length
decreasing_by
  · exact (halve_strict _ (by simp)).1
  · exact (halve_strict _ (by simp)).2

@[simp] theorem sortAlternatingBy_nil (cmp : α → α → Bool) :
    sortAlternatingBy cmp [] = [] := by rw [sortAlternatingBy]

@[simp] theorem sortAlternatingBy_singleton (cmp : α → α → Bool) (x : α) :
    sortAlternatingBy cmp [x] = [x] := by rw [sortAlternatingBy]

theorem sortAlternatingBy_cons_cons (cmp : α → α → Bool) (x y : α) (xs : List α) :
    sortAlternatingBy cmp (x :: y :: xs) =
      List.merge (sortAlternatingBy cmp (halve (x :: y :: xs) ([], [])).1)
        (sortAlternatingBy cmp (halve (x :: y :: xs) ([], [])).2) cmp := by
  rw [sortAlternatingBy]

theorem sortAlternatingBy_pair (cmp : α → α → Bool) (x y : α) :
    sortAlternatingBy cmp [x, y] = List.merge [x] [y] cmp := by
  simpa only [halve_cons_cons, halve_nil, sortAlternatingBy_singleton] using
    sortAlternatingBy_cons_cons cmp x y []

theorem sortAlternatingBy_perm (cmp : α → α → Bool) (xs : List α) :
    (sortAlternatingBy cmp xs).Perm xs := by
  match xs with
  | [] => simp
  | [x] => simp
  | x :: y :: rest =>
    rw [sortAlternatingBy_cons_cons]
    exact (List.merge_perm_append cmp).trans
      (((sortAlternatingBy_perm cmp (halve (x :: y :: rest) ([], [])).1).append
        (sortAlternatingBy_perm cmp (halve (x :: y :: rest) ([], [])).2)).trans
          (by simpa using halve_perm (x :: y :: rest) [] []))
termination_by xs.length
decreasing_by
  · exact (halve_strict _ (by simp)).1
  · exact (halve_strict _ (by simp)).2

theorem sortAlternatingBy_length (cmp : α → α → Bool) (xs : List α) :
    (sortAlternatingBy cmp xs).length = xs.length :=
  (sortAlternatingBy_perm cmp xs).length_eq

theorem mem_sortAlternatingBy (cmp : α → α → Bool) (xs : List α) (x : α) :
    x ∈ sortAlternatingBy cmp xs ↔ x ∈ xs := (sortAlternatingBy_perm cmp xs).mem_iff

/-- Reuse the existing input-local merge contract; no law on arbitrary payloads is needed. -/
theorem sortAlternatingBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (cmp : α → α → Bool) (xs : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs, (cmp a b = true → key a ≤ key b) ∧
      (cmp a b = false → key b ≤ key a)) :
    KeySorted key (sortAlternatingBy cmp xs) := by
  match xs with
  | [] => simp [KeySorted]
  | [x] => simp [KeySorted]
  | x :: y :: rest =>
    rw [sortAlternatingBy_cons_cons]
    have hleft : ∀ a ∈ (halve (x :: y :: rest) ([], [])).1, a ∈ x :: y :: rest := by
      intro a ha
      have h := (halve_perm (x :: y :: rest) [] []).mem_iff.mp
        (List.mem_append.mpr (Or.inl ha))
      simpa only [List.append_nil] using h
    have hright : ∀ a ∈ (halve (x :: y :: rest) ([], [])).2, a ∈ x :: y :: rest := by
      intro a ha
      have h := (halve_perm (x :: y :: rest) [] []).mem_iff.mp
        (List.mem_append.mpr (Or.inr ha))
      simpa only [List.append_nil] using h
    apply merge_sorted_compatible_on key cmp
    · intro a ha b hb
      exact hc a (hleft a ((mem_sortAlternatingBy cmp _ a).mp ha))
        b (hright b ((mem_sortAlternatingBy cmp _ b).mp hb))
    · exact sortAlternatingBy_sorted_compatible_on key cmp _
        (fun a ha b hb => hc a (hleft a ha) b (hleft b hb))
    · exact sortAlternatingBy_sorted_compatible_on key cmp _
        (fun a ha b hb => hc a (hright a ha) b (hright b hb))
termination_by xs.length
decreasing_by
  · exact (halve_strict _ (by simp)).1
  · exact (halve_strict _ (by simp)).2

abbrev sortAlternatingOn [LE κ] [DecidableLE κ] (key : α → κ) (xs : List α) : List α :=
  sortAlternatingBy (fun x y => decide (key x ≤ key y)) xs

/-- The source ordinary correctness contract; this makes no stability assertion. -/
theorem sortAlternatingOn_correct [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs : List α) :
    KeySorted key (sortAlternatingOn key xs) ∧ (sortAlternatingOn key xs).Perm xs := by
  refine ⟨?_, sortAlternatingBy_perm _ _⟩
  apply sortAlternatingBy_sorted_compatible_on key
  intro a _ b _
  exact ⟨of_decide_eq_true, fun h =>
    (Std.le_total (a := key a) (b := key b)).resolve_left (of_decide_eq_false h)⟩

end Applications.Sorting
