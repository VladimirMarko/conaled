import Applications.Resources.CallCount
import Applications.Resources.Growth
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! Comparisons between explicit call-count observations. Each list occurrence
is one charged entry; its extra local work belongs to that same occurrence.
A fixed-program catalogue gives a uniform constant independently of the input
trace. Theorems about these observations do not infer a compiler cost model.
Provenance and statement review: `docs/research/fdsa-call-models.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.CallCount
universe u v w
variable {ι : Type u} {α : Type v} {β : Type w}

/-- Count the original entry and its explicitly assigned local extra work. -/
def refinedCost (extra : ι → Nat) (calls : List ι) : Nat :=
  (calls.map (fun i => 1 + extra i)).sum

@[simp] theorem refinedCost_nil (extra : ι → Nat) : refinedCost extra [] = 0 := rfl

@[simp] theorem refinedCost_cons (extra : ι → Nat) (i : ι) (calls : List ι) :
    refinedCost extra (i :: calls) = 1 + extra i + refinedCost extra calls := rfl

theorem refinedCost_append (extra : ι → Nat) (calls more : List ι) :
    refinedCost extra (calls ++ more) = refinedCost extra calls + refinedCost extra more := by
  simp [refinedCost]

theorem refinedCost_zero (calls : List ι) :
    refinedCost (fun _ => 0) calls = calls.length := by
  induction calls with
  | nil => rfl
  | cons i calls ih => simp [ih, Nat.add_comm]

theorem coarse_le_refinedCost (extra : ι → Nat) (calls : List ι) :
    calls.length ≤ refinedCost extra calls := by
  induction calls with
  | nil => exact Nat.le_refl 0
  | cons i calls ih =>
      simp only [List.length_cons, refinedCost_cons]
      omega

/-- The local bound is uniform over every occurrence in this actual trace. -/
theorem refinedCost_le (extra : ι → Nat) (K : Nat) (calls : List ι)
    (localBound : ∀ i ∈ calls, extra i ≤ K) :
    refinedCost extra calls ≤ (K + 1) * calls.length := by
  revert localBound
  induction calls with
  | nil => simp
  | cons i calls ih =>
      intro localBound
      have head := localBound i (by simp)
      have tail := ih (fun j hj => localBound j (List.mem_cons_of_mem i hj))
      simp only [refinedCost_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- One catalogue fixes the same constant for all covered input traces.
The finite identifiers are local body cases, not the values being processed.
-/
theorem catalogue_refined_bounds (extra : ι → Nat) (catalogue : Finset ι)
    (calls : List ι) (covered : ∀ i ∈ calls, i ∈ catalogue) :
    calls.length ≤ refinedCost extra calls ∧
      refinedCost extra calls ≤ (catalogue.sup extra + 1) * calls.length := by
  constructor
  · exact coarse_le_refinedCost extra calls
  · exact refinedCost_le extra (catalogue.sup extra) calls
      (fun i hi => Finset.le_sup (covered i hi))

/-- Refined observations have the same upper asymptotic order under one local
bound holding eventually for the input family, with no positivity restriction.
-/
theorem refinedCost_isBigO (l : Filter α) (calls : α → List ι)
    (extra : ι → Nat) (K : Nat)
    (localBound : ∀ᶠ x in l, ∀ i ∈ calls x, extra i ≤ K) :
    Asymptotics.IsBigO l (fun x => (refinedCost extra (calls x) : ℝ))
      (fun x => ((calls x).length : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨((K + 1 : Nat) : ℝ), localBound.mono (fun x hx => ?_)⟩
  simpa using (Nat.cast_le (α := ℝ)).mpr (refinedCost_le extra K (calls x) hx)

theorem coarse_isBigO_refinedCost (l : Filter α) (calls : α → List ι)
    (extra : ι → Nat) :
    Asymptotics.IsBigO l (fun x => ((calls x).length : ℝ))
      (fun x => (refinedCost extra (calls x) : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨1, Filter.Eventually.of_forall (fun x => ?_)⟩
  simpa using (Nat.cast_le (α := ℝ)).mpr (coarse_le_refinedCost extra (calls x))

theorem cost_le_add_entry (T : Nat) : T ≤ T + 1 := Nat.le_succ T

/-- Dropping one entry preserves a multiplicative bound only on positive costs. -/
theorem add_entry_le (T : Nat) (positive : 1 ≤ T) : T + 1 ≤ 2 * T := by omega

theorem tick_cost_comparison (r : Measured β Nat) (positive : 1 ≤ r.2) :
    r.2 ≤ (tick r).2 ∧ (tick r).2 ≤ 2 * r.2 := by
  simpa only [tick_cost] using And.intro (cost_le_add_entry r.2) (add_entry_le r.2 positive)

/-- Eventual positivity, rather than merely not being identically zero, is the
uniform qualification needed by the source's omitted-entry convention.
-/
theorem add_entry_isBigO (l : Filter α) (T : α → Nat)
    (positive : ∀ᶠ x in l, 1 ≤ T x) :
    Asymptotics.IsBigO l (fun x => ((T x + 1 : Nat) : ℝ))
      (fun x => (T x : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2, positive.mono (fun x hx => ?_)⟩
  simpa using (Nat.cast_le (α := ℝ)).mpr (add_entry_le (T x) hx)

theorem cost_isBigO_add_entry (l : Filter α) (T : α → Nat) :
    Asymptotics.IsBigO l (fun x => (T x : ℝ))
      (fun x => ((T x + 1 : Nat) : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨1, Filter.Eventually.of_forall (fun x => ?_)⟩
  simpa using (Nat.cast_le (α := ℝ)).mpr (cost_le_add_entry (T x))

theorem zero_cost_entry_matters (K : Nat) : ¬ 0 + 1 ≤ K * 0 := by simp

end Resources.CallCount
