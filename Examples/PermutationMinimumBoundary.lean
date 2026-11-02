import Applications.Probability.PermutationMinimum
import Mathlib.Tactic.FinCases

/-!
# Empty, outsider and tied-priority boundaries for uniform permutation minima

The raw outsider comparison is connected to a genuine full-set minimum, so its
probability uses the public uniform-permutation theorem. Empty and tied events
exercise the event definition without asserting that the theorem applies when
membership or injectivity is absent.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationMinimum
open scoped ENNReal

namespace Examples.PermutationMinimumBoundary

local instance : MeasurableSpace (Equiv.Perm Empty) := ⊤
local instance : MeasurableSpace (Equiv.Perm (Fin 2)) := ⊤

/-- The empty index universe still has its identity permutation as a sample. -/
theorem empty_index_normalized :
    uniformOn (Set.univ : Set (Equiv.Perm Empty)) Set.univ = 1 := by
  exact uniformOn_self Set.finite_univ ⟨Equiv.refl Empty, Set.mem_univ _⟩

/-- An empty subset has no minimum member, even when an index is available. -/
theorem empty_subset_event :
    minimumEvent (id : Fin 2 → Fin 2) ∅ 0 = ∅ :=
  minimumEvent_empty _ _

theorem empty_subset_mass :
    uniformOn Set.univ (minimumEvent (id : Fin 2 → Fin 2) ∅ 0) = 0 := by
  rw [empty_subset_event]
  exact measure_empty

/-- Candidate 0 is outside the singleton subset {1}. -/
theorem outsider_event_empty :
    minimumEvent (id : Fin 2 → Fin 2) {1} 0 = ∅ :=
  minimumEvent_of_not_mem _ _ _ (by decide)

theorem outsider_mass :
    uniformOn Set.univ (minimumEvent (id : Fin 2 → Fin 2) {1} 0) = 0 := by
  rw [outsider_event_empty]
  exact measure_empty

/-- Dropping membership leaves only the comparison of two assigned priorities. -/
def outsiderComparison : Set (Equiv.Perm (Fin 2)) :=
  {π | π 0 ≤ π 1}

/-- That comparison is the event that 0 is the minimum of the full pair. -/
theorem outsiderComparison_eq_full_minimum :
    outsiderComparison =
      minimumEvent (id : Fin 2 → Fin 2) Finset.univ 0 := by
  ext π
  change (π 0 ≤ π 1) ↔
    ((0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) ∧
      ∀ b ∈ (Finset.univ : Finset (Fin 2)), π 0 ≤ π b)
  constructor
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    intro b _
    fin_cases b
    · exact le_rfl
    · exact h
  · intro h
    exact h.2 1 (Finset.mem_univ _)

/-- The mass comes from the public minimum law on the full two-member set. -/
theorem outsiderComparison_mass :
    uniformOn Set.univ outsiderComparison = (2 : ℝ≥0∞)⁻¹ := by
  rw [outsiderComparison_eq_full_minimum]
  simpa using
    (uniformOn_minimumEvent (id : Fin 2 → Fin 2) Function.injective_id
      (Finset.univ : Finset (Fin 2)) 0 (Finset.mem_univ _))

/-- The outsider comparison does not have the singleton reciprocal mass one. -/
theorem outsiderComparison_ne_singleton_inverse :
    uniformOn Set.univ outsiderComparison ≠
      (({1} : Finset (Fin 2)).card : ℝ≥0∞)⁻¹ := by
  rw [outsiderComparison_mass]
  simpa using (ne_of_lt ENNReal.one_half_lt_one)

/-- Both keys receive the same priority, regardless of the sampled permutation. -/
def tiedPriority : Fin 2 → ℕ := fun _ => 0

theorem tiedPriority_not_injective : ¬ Function.Injective tiedPriority := by
  intro h
  have h01 : (0 : Fin 2) = 1 := h rfl
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- Every member is a non-strict minimum on every sample when priorities tie. -/
theorem tied_event_univ (a : Fin 2) :
    minimumEvent tiedPriority Finset.univ a = Set.univ := by
  ext π
  simp [minimumEvent, tiedPriority]

theorem tied_mass (a : Fin 2) :
    uniformOn Set.univ (minimumEvent tiedPriority Finset.univ a) = 1 := by
  rw [tied_event_univ]
  exact uniformOn_self Set.finite_univ ⟨Equiv.refl (Fin 2), Set.mem_univ _⟩

/-- Without injectivity, the reciprocal-cardinality conclusion fails. -/
theorem tied_mass_ne_half (a : Fin 2) :
    uniformOn Set.univ (minimumEvent tiedPriority Finset.univ a) ≠
      (2 : ℝ≥0∞)⁻¹ := by
  rw [tied_mass]
  exact ne_of_gt ENNReal.one_half_lt_one

end Examples.PermutationMinimumBoundary
