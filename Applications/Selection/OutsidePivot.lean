import Applications.Selection.ThreeWay

/-! Outside-range pivots do not make progress in the actual selection recurrence.

The partition and dispatch identities below refer to the existing algorithm.
On a nonempty valid state an outside pivot leaves both the list and requested
rank unchanged. Every finite administrative fuel therefore expires without an
answer, whereas the valid sorted-index specification is nonempty. This is the
fuel formulation of the infinite recurrence path; none is not reinterpreted as
a successful result or as a statement about all arbitrary pivot policies.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection.OutsidePivot
universe u
variable {α : Type u} [LinearOrder α]

theorem partition3_below (p : α) (xs : List α)
    (hout : ∀ x ∈ xs, p < x) : partition3 p xs = ([], [], xs) := by
  have hl : xs.filter (fun x => decide (x < p)) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by
      simp [not_lt_of_ge (le_of_lt (hout x hx))])
  have he : xs.filter (fun x => decide (x = p)) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by simp [ne_of_gt (hout x hx)])
  have hr : xs.filter (fun x => decide (p < x)) = xs :=
    List.filter_eq_self.mpr (fun x hx => by simp [hout x hx])
  rw [partition3_eq_filters, hl, he, hr]

theorem partition3_above (p : α) (xs : List α)
    (hout : ∀ x ∈ xs, x < p) : partition3 p xs = (xs, [], []) := by
  have hl : xs.filter (fun x => decide (x < p)) = xs :=
    List.filter_eq_self.mpr (fun x hx => by simp [hout x hx])
  have he : xs.filter (fun x => decide (x = p)) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by simp [ne_of_lt (hout x hx)])
  have hr : xs.filter (fun x => decide (p < x)) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by
      simp [not_lt_of_ge (le_of_lt (hout x hx))])
  rw [partition3_eq_filters, hl, he, hr]

/-- The right recursive call is the identical state, even for an invalid rank. -/
theorem dispatch_below (recur : Nat → List α → Option α) (p : α)
    (k : Nat) (xs : List α) (hout : ∀ x ∈ xs, p < x) :
    dispatch recur p k xs = recur k xs := by
  simp [dispatch, partition3_below p xs hout]

/-- The valid requested rank chooses the identical left recursive state. -/
theorem dispatch_above (recur : Nat → List α → Option α) (p : α)
    (k : Nat) (xs : List α) (hk : k < xs.length)
    (hout : ∀ x ∈ xs, x < p) : dispatch recur p k xs = recur k xs := by
  simp [dispatch, partition3_above p xs hout, hk]

theorem runWith_step_below (choose : List α → Option α) (p : α)
    (xs : List α) (k fuel : Nat) (hne : xs ≠ [])
    (hc : choose xs = some p) (hout : ∀ x ∈ xs, p < x) :
    runWith choose (fuel + 1) k xs = runWith choose fuel k xs := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x xs =>
      rw [runWith, hc]
      exact dispatch_below _ p k (x :: xs) hout

theorem runWith_step_above (choose : List α → Option α) (p : α)
    (xs : List α) (k fuel : Nat) (hk : k < xs.length)
    (hc : choose xs = some p) (hout : ∀ x ∈ xs, x < p) :
    runWith choose (fuel + 1) k xs = runWith choose fuel k xs := by
  cases xs with
  | nil => simp at hk
  | cons x xs =>
      rw [runWith, hc]
      exact dispatch_above _ p k (x :: xs) hk hout

/-- No finite fuel reaches an answer along this nonempty self-recursive state. -/
theorem runWith_below_none (choose : List α → Option α) (p : α)
    (xs : List α) (k fuel : Nat) (hne : xs ≠ [])
    (hc : choose xs = some p) (hout : ∀ x ∈ xs, p < x) :
    runWith choose fuel k xs = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [runWith_step_below choose p xs k fuel hne hc hout, ih]

theorem runWith_above_none (choose : List α → Option α) (p : α)
    (xs : List α) (k fuel : Nat) (hk : k < xs.length)
    (hc : choose xs = some p) (hout : ∀ x ∈ xs, x < p) :
    runWith choose fuel k xs = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [runWith_step_above choose p xs k fuel hk hc hout, ih]

theorem not_pivotValid_below (choose : List α → Option α) (p : α)
    (xs : List α) (hne : xs ≠ []) (hc : choose xs = some p)
    (hout : ∀ x ∈ xs, p < x) : ¬ PivotValid choose := by
  intro hv
  obtain ⟨q, hq, hmem⟩ := hv xs hne
  have hpq : p = q := Option.some.inj (hc.symm.trans hq)
  subst q
  exact (lt_irrefl p) (hout p hmem)

theorem not_pivotValid_above (choose : List α → Option α) (p : α)
    (xs : List α) (hne : xs ≠ []) (hc : choose xs = some p)
    (hout : ∀ x ∈ xs, x < p) : ¬ PivotValid choose := by
  intro hv
  obtain ⟨q, hq, hmem⟩ := hv xs hne
  have hpq : p = q := Option.some.inj (hc.symm.trans hq)
  subst q
  exact (lt_irrefl p) (hout p hmem)

/-- The existing one-based public boundary also fails for the bad policy. -/
theorem selectWith_below_none (choose : List α → Option α) (p : α)
    (xs : List α) (k : Nat) (hne : xs ≠ [])
    (hc : choose xs = some p) (hout : ∀ x ∈ xs, p < x) :
    selectWith choose (k + 1) xs = none := by
  simpa [selectWith] using runWith_below_none choose p xs k xs.length hne hc hout

theorem selectWith_above_none (choose : List α → Option α) (p : α)
    (xs : List α) (k : Nat) (hk : k < xs.length)
    (hc : choose xs = some p) (hout : ∀ x ∈ xs, x < p) :
    selectWith choose (k + 1) xs = none := by
  simpa [selectWith] using runWith_above_none choose p xs k xs.length hk hc hout

/-- Fuel exhaustion cannot equal the nonempty valid sorted-index answer. -/
theorem runWith_below_ne_spec (choose : List α → Option α) (p : α)
    (xs : List α) (k fuel : Nat) (hk : k < xs.length)
    (hc : choose xs = some p) (hout : ∀ x ∈ xs, p < x) :
    runWith choose fuel k xs ≠ (ordered xs)[k]? := by
  have hne : xs ≠ [] := by intro h; subst xs; simp at hk
  rw [runWith_below_none choose p xs k fuel hne hc hout]
  intro h
  have hn := List.getElem?_eq_none_iff.mp h.symm
  rw [(ordered_perm xs).length_eq] at hn
  omega

theorem runWith_above_ne_spec (choose : List α → Option α) (p : α)
    (xs : List α) (k fuel : Nat) (hk : k < xs.length)
    (hc : choose xs = some p) (hout : ∀ x ∈ xs, x < p) :
    runWith choose fuel k xs ≠ (ordered xs)[k]? := by
  rw [runWith_above_none choose p xs k fuel hk hc hout]
  intro h
  have hn := List.getElem?_eq_none_iff.mp h.symm
  rw [(ordered_perm xs).length_eq] at hn
  omega

end Applications.Selection.OutsidePivot
