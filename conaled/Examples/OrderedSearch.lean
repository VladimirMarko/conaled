import Applications.Search.Ordered.Consumers

/-! Exact inversion, threshold rounding, interval endpoints and strictness boundaries. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.OrderedSearch
open _root_.OrderedSearch

def affine (n : Nat) : Nat := 3 * n + 1

theorem affine_strict : StrictMono affine := by intro i j h; dsimp [affine]; omega

theorem identity_strict : StrictMono (fun n : Nat => n) := fun _ _ h => h

-- The three original source searches now use the public exhaustive refinements.
example : search2 affine 16 = [5] := by
  rw [search2_eq_search affine affine_strict]
  decide +kernel
example : sourceSearch2 affine 16 = [5] := by
  rw [sourceSearch2_eq_search affine affine_strict]
  decide +kernel
example : search2 affine 15 = [] := by
  rw [search2_eq_search affine affine_strict]
  decide +kernel
example : upperPick 4 = 2 ∧ lowerPick 4 = 1 := by decide
example : binarySearch affine 16 3 4 = sourceBinarySearch affine 16 3 4 :=
  binarySearch_eq_source affine affine_strict 16 3 4

example : (preimageSquare affine affine_strict).impl 16 = some 5 :=
  (preimage_some_iff affine affine_strict 16 5).mpr rfl
example : (preimageValue affine affine_strict).impl 16 = some 16 :=
  preimageValue_hit affine affine_strict 16 5 rfl
example : (preimageSquare affine affine_strict).impl 15 = none := by
  apply (preimage_none_iff affine affine_strict 15).mpr
  intro n; dsimp [affine]; omega
example : (preimageValue affine affine_strict).impl 15 = none := by
  apply preimageValue_miss
  intro n; dsimp [affine]; omega

/-- Independently, five is the first index whose affine value reaches fifteen. -/
theorem affine_threshold15 : LeastThreshold affine 15 5 := by
  constructor
  · decide
  · intro x hx; dsimp [affine] at hx; omega

example : (roundUp affine affine_strict).impl 15 = (5, 16) := by
  have h := leastThreshold_unique affine 15 _ 5
    (leastIndex_spec affine affine_strict 15) affine_threshold15
  have he := (roundUp affine affine_strict).commutes 15
  change (roundUp affine affine_strict).impl 15 =
    (leastIndex affine affine_strict 15, affine (leastIndex affine affine_strict 15)) at he
  simpa [h, affine] using he
example : let p := (roundUp affine affine_strict).impl 15
    p.2 = affine p.1 ∧ 15 ≤ p.2 ∧ ∀ j, j < p.1 → affine j < 15 :=
  roundUp_spec affine affine_strict 15
example : affine (((roundUp affine affine_strict).impl 15).1 - 1) < 15 ∧
    15 ≤ ((roundUp affine affine_strict).impl 15).2 := by
  apply roundUp_sandwich
  have h := leastThreshold_unique affine 15 _ 5
    (smallest_spec affine affine_strict 15 (bound affine affine_strict 15)) affine_threshold15
  change 0 < smallest affine 15 (bound affine affine_strict 15)
  omega

-- The auxiliary short-list facts have no restriction on the element type.
example (xs : List String) (h : xs.length ≤ 1)
    (hm : ∀ x, x ∈ xs ↔ x = "hit") : xs = ["hit"] :=
  short_lists_eq xs ["hit"] h (by simp) (by simpa using hm)

-- The source's fictitious -1 lower endpoint is an explicit Option sentinel.
example : (bound (fun n => n) identity_strict 0).lower = none ∧
    (bound (fun n => n) identity_strict 0).upper = 0 := by decide +kernel
example : LeastThreshold (fun n => n) 0
    (smallest (fun n => n) 0 (bound (fun n => n) identity_strict 0)) :=
  smallest_spec _ identity_strict 0 _
example : (preimageSquare (fun n => n) identity_strict).impl 0 = some 0 :=
  (preimage_some_iff _ identity_strict 0 0).mpr rfl
example : (bound affine affine_strict 0).lower = none ∧
    (bound affine affine_strict 0).upper = 0 := by decide +kernel
example : (preimageSquare affine affine_strict).impl 0 = none := by
  apply (preimage_none_iff affine affine_strict 0).mpr
  intro n; dsimp [affine]; omega
example : LeastThreshold affine 0 (sourceSmallest affine 0 (bound affine affine_strict 0)) :=
  sourceSmallest_spec affine affine_strict 0 _

example : sourceSmallest affine 0 (bound affine affine_strict 0) = 0 := by
  apply leastThreshold_unique affine 0 _ 0 (sourceSmallest_spec affine affine_strict 0 _)
  exact ⟨by decide, fun _ _ => Nat.zero_le _⟩

example : binarySearch affine 16 7 0 = [] := by
  rw [binarySearch, binarySearchWith_eq_exhaustive upperPick upperPick_lt affine affine_strict]
  rfl
example : binarySearch affine 16 5 1 = [5] := by
  rw [binarySearch, binarySearchWith_eq_exhaustive upperPick upperPick_lt affine affine_strict]
  decide +kernel
example : binarySearch affine 15 5 1 = [] := by
  rw [binarySearch, binarySearchWith_eq_exhaustive upperPick upperPick_lt affine affine_strict]
  decide +kernel

-- Finite cuts allow plateaus and need only Monotone, unlike exact inversion.
theorem constant_monotone : Monotone (fun _ : Nat => 4) := fun _ _ _ => Nat.le_refl _
example : ThresholdSpec (fun _ => 4) 4 3 4 (lowerBound (fun _ => 4) 4 3 4) :=
  lowerBound_spec _ constant_monotone 4 3 4
example : lowerBound (fun _ => 4) 4 3 4 = 3 := by
  have h := lowerBound_spec (fun _ => 4) constant_monotone 4 3 4
  obtain ⟨hl, _, before, _⟩ := h
  by_contra he
  have h := before 3 (by omega) (by omega)
  exact Nat.lt_irrefl 4 h
example : lowerBound (fun _ => 4) 3 3 4 = 3 := by
  have h := lowerBound_spec (fun _ => 4) constant_monotone 3 3 4
  obtain ⟨hl, _, before, _⟩ := h
  by_contra he
  have h := before 3 (by omega) (by omega)
  change 4 < 3 at h
  omega
example : lowerBound (fun _ => 4) 5 3 4 = 7 := by
  have h := lowerBound_spec (fun _ => 4) constant_monotone 5 3 4
  obtain ⟨_, hu, _, after⟩ := h
  by_contra he
  have h := after _ (Nat.le_refl _) (by omega)
  change 5 ≤ 4 at h
  omega
example : lowerBound affine 15 7 0 = 7 := by
  have h := lowerBound_spec affine affine_strict.monotone 15 7 0
  have := h.1; have := h.2.1
  omega

example : binarySearchWith (fun _ => 0) (fun _ h => h) affine 16 3 4 = [5] := by
  rw [binarySearchWith_eq_exhaustive _ _ affine affine_strict]
  decide +kernel

-- Actual repeated doubling, with the certified predecessor and endpoint facts.
example : (bound (fun n => n) identity_strict 7).upper = 8 ∧
    (bound (fun n => n) identity_strict 7).lower = some 4 := by decide +kernel
example : 7 ≤ (bound (fun n => n) identity_strict 7).upper :=
  (bound (fun n => n) identity_strict 7).upper_hit
example : ∀ a, (bound (fun n => n) identity_strict 7).lower = some a → a < 7 :=
  (bound (fun n => n) identity_strict 7).lower_miss
example : (preimageSquare (fun n => n) identity_strict).impl 7 = some 7 :=
  (preimage_some_iff _ identity_strict 7 7).mpr rfl
example : (bound (fun n => n) identity_strict 8).upper = 8 := by decide +kernel
example : sourceSmallest (fun n => n) 8 (bound (fun n => n) identity_strict 8) = 8 := by
  apply leastThreshold_unique _ 8 _ 8 (sourceSmallest_spec _ identity_strict 8 _)
  exact ⟨by decide, fun _ h => h⟩

/-- A plateau gives multiple exact occurrences, which binary search does not enumerate. -/
example : binarySearch (fun _ => 4) 4 0 2 ≠ exhaustiveInterval (fun _ => 4) 4 0 2 := by
  intro h
  have hl := binarySearchWith_length_le upperPick upperPick_lt (fun _ => 4) 4 0 2
  change (binarySearch (fun _ => 4) 4 0 2).length ≤ 1 at hl
  rw [h] at hl
  have he : exhaustiveInterval (fun _ => 4) 4 0 2 = [0, 1] := by decide +kernel
  rw [he] at hl
  contradiction

end Examples.OrderedSearch
