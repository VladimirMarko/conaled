import Applications.Resources.Selection
import Applications.Resources.SelectionRecurrence
import Mathlib.Order.RelClasses

/-! The actual selector's cutoff and the scalar recurrence's cutoff.

For every group size at least two, one is the least base cutoff ensuring a
strictly shorter first recursive input. The measured worker supplies the
corresponding terminating and correct implementation; pivot membership makes
both later strict sides shorter. Singleton grouping instead returns the same
input to the pivot call. These are observations of the actual measured median
preparation, including duplicates, rather than an assumed size recurrence.

The size-five scalar side bound has a separate least cutoff of thirteen.
Twenty satisfies that condition and admits the explicit small-input budget483.
These facts explain the mathematical sufficiency of the book's choice without
asserting a uniquely established historical motive. Source: FDSA Exercises3.6
and3.8, printed pp.40 and44.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SelectionCutoff
open Applications.Selection Applications.Sequences.Chunks
open Resources.Selection Resources.SelectionMedians Resources.SelectionAuxiliary
open Resources.SelectionRecurrence
universe u
variable {α : Type u} [LinearOrder α]

/-- The first recursive call of the nested recipe, oriented child to parent.
The public valid-rank guard and worker cutoff guard are both retained. This
relation is also defined at disputed parameters where the total worker's
termination premises cannot be supplied. -/
def FirstPivotCall (d cutoff : Nat) (child parent : Nat × List α) : Prop :=
  parent.1 < parent.2.length ∧ cutoff < parent.2.length ∧
    child = (((parent.2.length ⌈/⌉ d) - 1) / 2, (chunkMediansRun d parent.2).1)

theorem no_first_call_of_invalid (d cutoff k : Nat) (xs : List α)
    (child : Nat × List α) (hk : xs.length ≤ k) :
    ¬ FirstPivotCall d cutoff child (k, xs) := by
  intro h
  exact (Nat.not_lt_of_ge hk) h.1

theorem no_first_call_of_small (d cutoff k : Nat) (xs : List α)
    (child : Nat × List α) (hs : xs.length ≤ cutoff) :
    ¬ FirstPivotCall d cutoff child (k, xs) := by
  intro h
  exact (Nat.not_lt_of_ge hs) h.2.1

theorem one_ceil_div (d : Nat) (hd : 0 < d) : (1 : Nat) ⌈/⌉ d = 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have h : 1 + d - 1 = d := by omega
  rw [h, Nat.div_self (Nat.ne_of_gt hd)]

/-- The exact obstruction is singleton size, for every fixed d≥2. -/
theorem ceil_div_strict_iff (n d : Nat) (hd : 2 ≤ d) :
    n ⌈/⌉ d < n ↔ 1 < n := by
  constructor
  · intro h
    by_contra hn
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl
    · simpa using h
    · rw [one_ceil_div d (by omega)] at h
      omega
  · intro hn
    have hc : n ⌈/⌉ d ≤ n - 1 := by
      apply (ceilDiv_le_iff_le_mul (by omega : 0 < d)).mpr
      calc
        n ≤ 2 * (n - 1) := by omega
        _ ≤ d * (n - 1) := Nat.mul_le_mul_right _ hd
    omega

theorem first_pivot_length_strict_iff (d : Nat) (hd : 2 ≤ d) (xs : List α) :
    (chunkMediansRun d xs).1.length < xs.length ↔ 1 < xs.length := by
  rw [chunkMediansRun_length]
  exact ceil_div_strict_iff xs.length d hd

/-- An explicit payload prevents the converse from being vacuous on an empty
payload type. The forward guarantee itself works for every payload type. -/
theorem actual_cutoff_iff (d cutoff : Nat) (hd : 2 ≤ d) (a : α) :
    (∀ xs : List α, cutoff < xs.length →
      (chunkMediansRun d xs).1.length < xs.length) ↔ 1 ≤ cutoff := by
  constructor
  · intro h
    by_contra hc
    have hzero : cutoff = 0 := by omega
    have bad := (first_pivot_length_strict_iff d hd [a]).mp
      (h [a] (by simp [hzero]))
    simp only [List.length_cons, List.length_nil, Nat.lt_irrefl] at bad
  · intro hc xs hx
    exact (first_pivot_length_strict_iff d hd xs).mpr (by omega)

theorem lowerMedianValue_singleton (a : α) (h : [a] ≠ []) :
    lowerMedianValue [a] h = a := by
  simpa only [List.mem_singleton] using lowerMedianValue_mem [a] h

/-- This is the actual first recursive input when cutoff zero admits a singleton. -/
theorem singleton_medians (d : Nat) (hd : 0 < d) (a : α) :
    (chunkMediansRun d [a]).1 = [a] := by
  rw [chunkMediansRun_value]
  unfold chunkMedians
  rw [chop_eq_singleton d [a] hd (by simp)
    (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil,
    lowerMedianValue_singleton]

theorem zero_cutoff_self_pivot (d : Nat) (hd : 0 < d) (a : α) :
    0 < ([a] : List α).length ∧
      (((([a] : List α).length ⌈/⌉ d) - 1) / 2,
        (chunkMediansRun d [a]).1) = (0, [a]) := by
  rw [singleton_medians d hd a]
  simp only [List.length_cons, List.length_nil, one_ceil_div d hd]
  exact ⟨by decide, rfl⟩

theorem zero_cutoff_self_call (d : Nat) (hd : 0 < d) (a : α) :
    FirstPivotCall d 0 (0, [a]) (0, [a]) := by
  exact ⟨by simp, by simp, (zero_cutoff_self_pivot d hd a).2.symm⟩

/-- The exact guarded singleton self-call obstructs well-founded recursion
for this recipe at cutoff zero, independent of the payload's value. -/
theorem zero_cutoff_not_wellFounded (d : Nat) (hd : 0 < d) (a : α) :
    ¬ WellFounded (FirstPivotCall (α := α) d 0) := by
  intro h
  have edge := zero_cutoff_self_call d hd a
  exact @WellFounded.asymmetric _ _ h (0, [a]) (0, [a]) edge edge

/-- Singleton chunks preserve the entire ordered sequence of payloads. -/
theorem group_one_medians (xs : List α) : (chunkMediansRun 1 xs).1 = xs := by
  rw [chunkMediansRun_value]
  simp only [chunkMedians, chop_one, List.attach_map, List.map_map,
    Function.comp_apply, lowerMedianValue_singleton]
  exact List.attach_map_subtype_val xs

theorem group_one_self_pivot (xs : List α) :
    (((xs.length ⌈/⌉ 1) - 1) / 2, (chunkMediansRun 1 xs).1) =
      ((xs.length - 1) / 2, xs) := by
  rw [group_one_medians]
  simp only [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_cancel, Nat.div_one]

/-- No finite base cutoff removes the first-child obstruction for group size1. -/
theorem group_one_has_no_cutoff (cutoff : Nat) (a : α) :
    ∃ xs : List α, cutoff < xs.length ∧ (chunkMediansRun 1 xs).1 = xs := by
  refine ⟨List.replicate (cutoff + 1) a, ?_, group_one_medians _⟩
  simp only [List.length_replicate]
  omega

/-- The first pivot call resets the rank to the lower median rank. At that
rank singleton grouping repeats the whole guarded state, including duplicates. -/
theorem group_one_self_call (cutoff : Nat) (xs : List α) (hx : cutoff < xs.length) :
    FirstPivotCall 1 cutoff ((xs.length - 1) / 2, xs) ((xs.length - 1) / 2, xs) := by
  refine ⟨?_, hx, (group_one_self_pivot xs).symm⟩
  change (xs.length - 1) / 2 < xs.length
  omega

theorem group_one_not_wellFounded (cutoff : Nat) (a : α) :
    ¬ WellFounded (FirstPivotCall (α := α) 1 cutoff) := by
  intro h
  let xs := List.replicate (cutoff + 1) a
  have hx : cutoff < xs.length := by
    simp only [xs, List.length_replicate]
    omega
  have edge := group_one_self_call cutoff xs hx
  exact @WellFounded.asymmetric _ _ h
    ((xs.length - 1) / 2, xs) ((xs.length - 1) / 2, xs) edge edge

/-- The actual recursive pivot exists and belongs to the original input. Thus
all possible recursive inputs are smaller above any positive base cutoff. -/
theorem recursive_children_decrease (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (xs : List α) (hlarge : cutoff < xs.length) :
    ∃ p : α, (selectRunWith d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
      (chunkMediansRun d xs).1).1 = some p ∧ p ∈ xs ∧
      (chunkMediansRun d xs).1.length < xs.length ∧
      (partition3 p xs).1.length < xs.length ∧
      (partition3 p xs).2.2.length < xs.length := by
  have hmpos : 0 < (chunkMediansRun d xs).1.length := by
    apply List.length_pos_iff.mpr
    intro hm
    rcases (chunkMediansRun_eq_nil_iff d xs).mp hm with hz | hx
    · omega
    · subst xs
      simp only [List.length_nil] at hlarge
      omega
  have hi : ((xs.length ⌈/⌉ d) - 1) / 2 < (chunkMediansRun d xs).1.length := by
    have hl := chunkMediansRun_length d xs
    omega
  obtain ⟨p, hp⟩ := selectRunWith_exists d cutoff hd hc _ _ hi
  have hmem : p ∈ xs := chunkMediansRun_mem d xs p
    (selectRunWith_mem d cutoff hd hc _ _ p hp)
  have strict := partition_strict_sizes p xs hmem
  exact ⟨p, hp, hmem, (first_pivot_length_strict_iff d hd xs).mpr (by omega),
    strict.1, strict.2⟩

/-- Cutoff1 has an actual terminating implementation with the complete optional
value contract, for every group size≥2 and including invalid ranks. -/
theorem cutoff_one_value (d : Nat) (hd : 2 ≤ d) (k : Nat) (xs : List α) :
    (selectRunWith d 1 hd (by decide) k xs).1 = (ordered xs)[k]? :=
  selectRunWith_value d 1 hd (by decide) k xs

/-- The crude scalar's two children need the separate cutoff13. -/
theorem scalar_cutoff_iff (cutoff : Nat) :
    (∀ n : Nat, cutoff < n → pivotSize n < n ∧ sideSize n < n) ↔
      13 ≤ cutoff := by
  constructor
  · intro h
    by_contra hc
    have bad := (sideSize_lt_iff 13).mp (h 13 (by omega)).2
    omega
  · intro hc n hn
    exact ⟨(pivotSize_lt_iff n).mpr (by omega),
      (sideSize_lt_iff n).mpr (by omega)⟩

theorem twenty_scalar_safe (n : Nat) (hn : 20 < n) :
    pivotSize n < n ∧ sideSize n < n :=
  (scalar_cutoff_iff 20).mpr (by decide) n hn

theorem twenty_polynomial_budget (n : Nat) (hn : n ≤ 20) :
    n * n + 4 * n + 3 ≤ 483 := by
  nlinarith [Nat.mul_le_mul hn hn]

/-- The explicit483 budget also bounds the actual measured small branch. -/
theorem twenty_actual_base_budget (k : Nat) (xs : List α)
    (hk : k < xs.length) (hs : xs.length ≤ 20) :
    (selectRun k xs).2 ≤ 483 := by
  rw [selectRun_small k xs hk hs]
  change 1 + (SymmetricCosts.lengthRun xs).2 + (slowSelectRun k xs).2 ≤ 483
  exact slowSelectRun_cutoff_bound k xs hk hs

end Resources.SelectionCutoff
