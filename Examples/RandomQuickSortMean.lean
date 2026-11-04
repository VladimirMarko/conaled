import Applications.Resources.RandomQuickSortMean
import Examples.RandomQuickSort
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.NormNum

/-! Connected clients of the actual random-quicksort expectations.
The expected constants were fixed before this implementation: T has means
1, 5, 13 and 71/3 on the displayed distinct-key sizes, while the two-key
append-inclusive mean is 39/2. Equal-key tags keep the quadratic source law.
These examples do not supply the pending rank, harmonic or asymptotic proofs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomQuickSortMean
open Resources Resources.RandomQuickSort MeasureTheory
open scoped BigOperators ENNReal
universe u

noncomputable section

local notation "natLt" => (fun a b : Nat => decide (a < b))

/-- An actual empty-input expectation requires no inhabited payload. -/
theorem empty_uninhabited_means :
    exerciseMean (fun _ _ : Empty => false) [] = 1 ∧
      literalMean (fun _ _ : Empty => false) [] = 1 := by
  simp

theorem singleton_means {α : Type u} (lt : α → α → Bool) (x : α) :
    exerciseMean lt [x] = 5 ∧ literalMean lt [x] = 8 := by
  simp

/-- The finite sample type is the actual pivot index, not the infinite Nat
cost carrier. The actual PMF map is transported to its finite integral. -/
private theorem integral_nat_map_fin {n : Nat} (p : PMF (Fin n)) (f : Fin n → Nat) :
    (∫ k : Nat, (k : ℝ) ∂(p.map f).toMeasure) =
      ∑ i : Fin n, (p i).toReal * (f i : ℝ) := by
  rw [← PMF.toMeasure_map (f := f) (p := p) (measurable_of_countable f)]
  rw [integral_map (measurable_of_countable f).aemeasurable
    (measurable_of_countable (fun k : Nat => (k : ℝ))).aestronglyMeasurable]
  simpa only [smul_eq_mul] using PMF.integral_eq_sum p (fun i => (f i : ℝ))

theorem two_key_exercise_mean : exerciseMean natLt [0, 1] = 13 := by
  simp [exerciseMean, Examples.RandomQuickSort.two_key_exercise, PMF.toMeasure_pure]

/-- The actual two runs cost (13,6) and (13,7), hence totals 19 and 20.
Their equal masses give a nonintegral real mean, 39/2. -/
theorem two_key_literal_mean : literalMean natLt [0, 1] = (39 : ℝ) / 2 := by
  have hlaw : literalLaw natLt [0, 1] =
      PMF.map (fun i : Fin 2 => if i = 0 then 19 else 20) (uniformIndex 1) := by
    rw [literalLaw, Examples.RandomQuickSort.two_key_execution, PMF.map_comp]
    apply congrArg (fun f : Fin 2 → Nat => PMF.map f (uniformIndex 1))
    funext i
    change 13 + (if i = 0 then 6 else 7) = if i = 0 then 19 else 20
    by_cases hi : i = 0 <;> simp [hi]
  rw [literalMean, hlaw, integral_nat_map_fin, Fin.sum_univ_two]
  norm_num [uniformIndex_apply]

/-- This mean integrates the checked actual 21/25 law. The midpoint has mass
1/3, the two endpoints together have mass 2/3, so the mean is 71/3. -/
theorem three_key_exercise_mean : exerciseMean natLt [0, 1, 2] = (71 : ℝ) / 3 := by
  rw [exerciseMean, Examples.RandomQuickSort.three_key_exercise_law,
    integral_nat_map_fin, Fin.sum_univ_three]
  norm_num [uniformIndex_apply]

/-- The payload universe and tags are unrestricted. Equal keys force the
actual quadratic joint costs even when the output tag order is random. -/
theorem constant_key_payload_means {α : Type u} (tags : List α) :
    exerciseMean (fun a b : Nat × α => decide (a.1 < b.1))
        (tags.map (fun tag => (7, tag))) =
      ((2 * tags.length ^ 2 + 2 * tags.length + 1 : Nat) : ℝ) ∧
    literalMean (fun a b : Nat × α => decide (a.1 < b.1))
        (tags.map (fun tag => (7, tag))) =
      ((2 * tags.length ^ 2 + 5 * tags.length + 1 : Nat) : ℝ) := by
  have hf : ∀ a ∈ tags.map (fun tag => (7, tag)),
      ∀ b ∈ tags.map (fun tag => (7, tag)), decide (a.1 < b.1) = false := by
    intro a ha b hb
    obtain ⟨ta, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨tb, _, rfl⟩ := List.mem_map.mp hb
    rfl
  constructor
  · simpa only [List.length_map] using exerciseMean_of_all_false _ _ hf
  · simpa only [List.length_map] using literalMean_of_all_false _ _ hf

/-- Distinct payload tags do not imply distinct keys. Their means differ from
the distinct-key two-element literal mean, despite the same exercise cost. -/
theorem two_equal_key_tag_means :
    exerciseMean (fun a b : Nat × Bool => decide (a.1 < b.1))
        [(7, false), (7, true)] = 13 ∧
    literalMean (fun a b : Nat × Bool => decide (a.1 < b.1))
        [(7, false), (7, true)] = 19 := by
  simpa using constant_key_payload_means [false, true]

theorem all_equal_three_means :
    exerciseMean natLt [2, 2, 2] = 25 ∧ literalMean natLt [2, 2, 2] = 34 := by
  have hrun : run natLt [2, 2, 2] = PMF.pure ([2, 2, 2], (25, 9)) :=
    Examples.RandomQuickSort.all_equal_three
  constructor
  · simp [exerciseMean, exerciseLaw, hrun, PMF.pure_map, PMF.toMeasure_pure]
  · simp [literalMean, literalLaw, hrun, PMF.pure_map, PMF.toMeasure_pure]

/-- Both actual natural observations have genuine real integrability for
arbitrary payloads; finite carrier assumptions are not being inferred on α. -/
theorem arbitrary_payload_integrable {α : Type u} (lt : α → α → Bool) (xs : List α) :
    Integrable (fun k : Nat => (k : ℝ)) (exerciseLaw lt xs).toMeasure ∧
      Integrable (fun k : Nat => (k : ℝ)) (literalLaw lt xs).toMeasure :=
  ⟨exerciseLaw_integrable lt xs, literalLaw_integrable lt xs⟩

/-- The two means compare through the same run, without a new coupling premise. -/
theorem arbitrary_payload_mean_comparison {α : Type u} (lt : α → α → Bool)
    (xs : List α) :
    exerciseMean lt xs ≤ literalMean lt xs ∧
      literalMean lt xs ≤ 2 * exerciseMean lt xs :=
  literalMean_comparison lt xs

end
end Examples.RandomQuickSortMean
