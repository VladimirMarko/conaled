import Mathlib.Order.WellFounded

/-!
# One-dimensional search on strictly increasing natural-valued functions

New reconstruction with explicit finite-interval and global specifications.
The generic binary recursion preserves both midpoint choices separately:
`binarySearch` uses the recovered upper midpoint on even half-open intervals;
`sourceBinarySearch` uses the book's lower midpoint. Result equality is not a
claim about identical comparison traces. Source `search1` remains exhaustive.
-/

set_option autoImplicit false
set_option warningAsError true

namespace OrderedSearch

/-- The source strictly increasing function domain, using the standard order predicate. -/
abbrev Increasing (f : Nat → Nat) : Prop := StrictMono f

def search (f : Nat → Nat) (target : Nat) : List Nat :=
  (List.range (target + 1)).filter (fun x => decide (target = f x))

def exhaustiveInterval (f : Nat → Nat) (target lower count : Nat) : List Nat :=
  (List.range' lower count).filter (fun x => decide (target = f x))

def search1 (f : Nat → Nat) (target : Nat) : List Nat :=
  exhaustiveInterval f target 0 (target + 1)

theorem search1_eq_search (f : Nat → Nat) (target : Nat) : search1 f target = search f target := by
  simp [search1, exhaustiveInterval, search, ← List.range_eq_range']

theorem mem_exhaustiveInterval (f : Nat → Nat) (target lower count x : Nat) :
    x ∈ exhaustiveInterval f target lower count ↔
      lower ≤ x ∧ x < lower + count ∧ f x = target := by
  simp only [exhaustiveInterval, List.mem_filter, List.mem_range', decide_eq_true_eq, Nat.one_mul]
  constructor
  · rintro ⟨⟨i, hi, he⟩, hf⟩; omega
  · rintro ⟨hl, hu, hf⟩
    exact ⟨⟨x - lower, by omega, by omega⟩, hf.symm⟩

theorem mem_search (f : Nat → Nat) (hf : Increasing f) (target x : Nat) :
    x ∈ search f target ↔ f x = target := by
  simp only [search, List.mem_filter, List.mem_range, decide_eq_true_eq]
  have := hf.le_apply (x := x)
  omega

def upperPick (count : Nat) : Nat := count / 2
def lowerPick (count : Nat) : Nat := (count - 1) / 2

theorem upperPick_lt (count : Nat) (h : 0 < count) : upperPick count < count := by
  exact Nat.div_lt_self h (by decide)

theorem lowerPick_lt (count : Nat) (h : 0 < count) : lowerPick count < count := by
  have : (count - 1) / 2 ≤ count - 1 := Nat.div_le_self _ _
  unfold lowerPick
  omega

/-- Total binary recursion with an explicit in-range pivot selection. -/
def binarySearchWith (pick : Nat → Nat) (hp : ∀ n, 0 < n → pick n < n)
    (f : Nat → Nat) (target lower : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 =>
      let k := pick (n + 1)
      let m := lower + k
      if target < f m then binarySearchWith pick hp f target lower k
      else if target = f m then [m]
      else binarySearchWith pick hp f target (m + 1) (n - k)
termination_by count => count
decreasing_by
  all_goals have _h := hp (n + 1) (by omega); omega

theorem mem_binarySearchWith (pick : Nat → Nat) (hp : ∀ n, 0 < n → pick n < n)
    (f : Nat → Nat) (hf : Increasing f) (target lower count x : Nat) :
    x ∈ binarySearchWith pick hp f target lower count ↔
      lower ≤ x ∧ x < lower + count ∧ f x = target := by
  cases count with
  | zero =>
    simp only [binarySearchWith, Nat.add_zero]
    constructor
    · intro hx; cases hx
    · rintro ⟨hl, hu, _⟩; omega
  | succ n =>
    have hk := hp (n + 1) (by omega)
    rw [binarySearchWith]
    split
    · rename_i hlt
      rw [mem_binarySearchWith pick hp f hf]
      constructor
      · rintro ⟨hl, hu, he⟩; exact ⟨hl, by omega, he⟩
      · rintro ⟨hl, hu, he⟩
        have hm : x < lower + pick (n + 1) := by
          apply Classical.byContradiction
          intro hn
          have := hf.monotone (a :=  lower + pick (n + 1)) (b := x) (by omega)
          omega
        exact ⟨hl, hm, he⟩
    · rename_i hlt
      split
      · rename_i heq
        simp only [List.mem_singleton]
        constructor
        · intro hx; subst x; exact ⟨by omega, by omega, heq.symm⟩
        · rintro ⟨_, _, hx⟩
          exact hf.injective (hx.trans heq)
      · rename_i heq
        rw [mem_binarySearchWith pick hp f hf]
        constructor
        · rintro ⟨hl, hu, he⟩; exact ⟨by omega, by omega, he⟩
        · rintro ⟨hl, hu, he⟩
          have hm : lower + pick (n + 1) < x := by
            apply Classical.byContradiction
            intro hn
            have := hf.monotone (a :=  x) (b := lower + pick (n + 1)) (by omega)
            omega
          exact ⟨by omega, by omega, he⟩
termination_by count
decreasing_by all_goals have _h := hp (n + 1) (by omega); omega

theorem binarySearchWith_length_le (pick : Nat → Nat) (hp : ∀ n, 0 < n → pick n < n)
    (f : Nat → Nat) (target lower count : Nat) :
    (binarySearchWith pick hp f target lower count).length ≤ 1 := by
  cases count with
  | zero => simp [binarySearchWith]
  | succ n =>
    rw [binarySearchWith]
    split
    · exact binarySearchWith_length_le pick hp f target lower _
    · split
      · simp
      · exact binarySearchWith_length_le pick hp f target _ _
termination_by count
decreasing_by all_goals have _h := hp (n + 1) (by omega); omega

def binarySearch (f : Nat → Nat) (target lower count : Nat) : List Nat :=
  binarySearchWith upperPick upperPick_lt f target lower count

def sourceBinarySearch (f : Nat → Nat) (target lower count : Nat) : List Nat :=
  binarySearchWith lowerPick lowerPick_lt f target lower count

def search2 (f : Nat → Nat) (target : Nat) : List Nat :=
  binarySearch f target 0 (target + 1)

def sourceSearch2 (f : Nat → Nat) (target : Nat) : List Nat :=
  sourceBinarySearch f target 0 (target + 1)

theorem length_le_one_of_unique {α : Type*} (xs : List α) (hn : xs.Nodup)
    (hu : ∀ x ∈ xs, ∀ y ∈ xs, x = y) : xs.length ≤ 1 := by
  cases xs with
  | nil => simp
  | cons x xs =>
    have hsub : x :: xs ⊆ [x] := fun y hy => List.mem_singleton.mpr
      (hu y hy x (by simp))
    exact hn.length_le_of_subset hsub

theorem short_lists_eq {α : Type*} (xs ys : List α) (hx : xs.length ≤ 1) (hy : ys.length ≤ 1)
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys := by
  cases xs with
  | nil =>
    symm
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x h
    have bad := (hm x).mpr h
    cases bad
  | cons x xs =>
    have he : xs = [] := List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hx; omega)
    subst xs
    cases ys with
    | nil => have bad := (hm x).mp (by simp); cases bad
    | cons y ys =>
      have he : ys = [] := List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hy; omega)
      subst ys
      have he : x = y := by simpa using (hm x).mp (by simp)
      simp [he]

theorem exhaustiveInterval_length_le (f : Nat → Nat) (hf : Increasing f)
    (target lower count : Nat) : (exhaustiveInterval f target lower count).length ≤ 1 := by
  apply length_le_one_of_unique
  · exact (List.nodup_range' 1).filter _
  · intro x hx y hy
    exact hf.injective (((mem_exhaustiveInterval f target lower count x).mp hx).2.2.trans
      ((mem_exhaustiveInterval f target lower count y).mp hy).2.2.symm)

theorem binarySearchWith_eq_exhaustive (pick : Nat → Nat) (hp : ∀ n, 0 < n → pick n < n)
    (f : Nat → Nat) (hf : Increasing f) (target lower count : Nat) :
    binarySearchWith pick hp f target lower count = exhaustiveInterval f target lower count := by
  apply short_lists_eq
  · exact binarySearchWith_length_le pick hp f target lower count
  · exact exhaustiveInterval_length_le f hf target lower count
  · intro x
    rw [mem_binarySearchWith pick hp f hf, mem_exhaustiveInterval]

theorem binarySearch_spec (f : Nat → Nat) (hf : Increasing f) (target lower count x : Nat) :
    x ∈ binarySearch f target lower count ↔ lower ≤ x ∧ x < lower + count ∧ f x = target :=
  mem_binarySearchWith upperPick upperPick_lt f hf target lower count x

theorem binarySearch_eq_source (f : Nat → Nat) (hf : Increasing f) (target lower count : Nat) :
    binarySearch f target lower count = sourceBinarySearch f target lower count := by
  unfold binarySearch sourceBinarySearch
  rw [binarySearchWith_eq_exhaustive upperPick upperPick_lt f hf,
    binarySearchWith_eq_exhaustive lowerPick lowerPick_lt f hf]

theorem search2_eq_search (f : Nat → Nat) (hf : Increasing f) (target : Nat) :
    search2 f target = search f target := by
  rw [search2, binarySearch, binarySearchWith_eq_exhaustive upperPick upperPick_lt f hf]
  exact search1_eq_search f target

theorem sourceSearch2_eq_search (f : Nat → Nat) (hf : Increasing f) (target : Nat) :
    sourceSearch2 f target = search f target := by
  rw [sourceSearch2, ← binarySearch_eq_source f hf]
  exact search2_eq_search f hf target

end OrderedSearch
