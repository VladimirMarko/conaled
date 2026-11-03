import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! Exact finite Metropolis–Hastings tables. No random-bit source is assumed. -/
namespace Applications.Probability

open scoped BigOperators

/-- An exact rational stochastic table. -/
structure Table (α β : Type*) [Fintype β] where
  entry : α → β → ℚ
  nonneg : ∀ x y, 0 ≤ entry x y
  sum_row : ∀ x, ∑ y, entry x y = 1

/-- Positive unnormalized target weights and a stochastic proposal. -/
structure FiniteMH (α : Type*) [Fintype α] where
  weight : α → ℚ
  positive : ∀ x, 0 < weight x
  proposal : Table α α

namespace FiniteMH
variable {α : Type*} [Fintype α] (m : FiniteMH α)

/-- Zero forward proposal mass explicitly has zero acceptance. -/
def acceptance (x y : α) : ℚ :=
  if m.proposal.entry x y = 0 then 0
  else min 1 (m.weight y * m.proposal.entry y x /
    (m.weight x * m.proposal.entry x y))

def accepted (x y : α) : ℚ := m.proposal.entry x y * m.acceptance x y

theorem acceptance_nonneg (x y : α) : 0 ≤ m.acceptance x y := by
  unfold acceptance
  split
  · rfl
  · exact le_min (by norm_num) (div_nonneg
      (mul_nonneg (m.positive y).le (m.proposal.nonneg y x))
      (mul_nonneg (m.positive x).le (m.proposal.nonneg x y)))

theorem acceptance_le_one (x y : α) : m.acceptance x y ≤ 1 := by
  unfold acceptance
  split
  · norm_num
  · exact min_le_left _ _

theorem accepted_nonneg (x y : α) : 0 ≤ m.accepted x y :=
  mul_nonneg (m.proposal.nonneg x y) (m.acceptance_nonneg x y)

theorem accepted_le_proposal (x y : α) : m.accepted x y ≤ m.proposal.entry x y := by
  simpa [accepted] using mul_le_mul_of_nonneg_left (m.acceptance_le_one x y)
    (m.proposal.nonneg x y)

/-- Accepted target flow is the minimum of the two proposal flows. -/
theorem accepted_flow (x y : α) :
    m.weight x * m.accepted x y =
      min (m.weight x * m.proposal.entry x y) (m.weight y * m.proposal.entry y x) := by
  by_cases h : m.proposal.entry x y = 0
  · simp [accepted, acceptance, h, min_eq_left
      (mul_nonneg (m.positive y).le (m.proposal.nonneg y x))]
  · have hp : 0 < m.weight x * m.proposal.entry x y :=
      mul_pos (m.positive x) (lt_of_le_of_ne (m.proposal.nonneg x y) (Ne.symm h))
    simp only [accepted, acceptance, ite_eq_right h, ← mul_assoc, mul_min_of_nonneg _ _ hp.le,
      mul_one, mul_div_cancel₀ _ (ne_of_gt hp)]

theorem accepted_balance (x y : α) :
    m.weight x * m.accepted x y = m.weight y * m.accepted y x := by
  rw [m.accepted_flow, m.accepted_flow, min_comm]

/-- All rejected proposal mass stays at the current state. -/
def rejection (x : α) : ℚ := 1 - ∑ y, m.accepted x y

theorem rejection_nonneg (x : α) : 0 ≤ m.rejection x := by
  unfold rejection
  have := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => m.accepted_le_proposal x y)
  rw [m.proposal.sum_row] at this
  linarith

def transition [DecidableEq α] : Table α α where
  entry x y := m.accepted x y + if x = y then m.rejection x else 0
  nonneg x y := add_nonneg (m.accepted_nonneg x y) (by split <;> simp_all [m.rejection_nonneg])
  sum_row x := by simp [Finset.sum_add_distrib, rejection]

theorem detailed_balance [DecidableEq α] (x y : α) :
    m.weight x * m.transition.entry x y = m.weight y * m.transition.entry y x := by
  by_cases h : x = y
  · subst y; rfl
  · simpa [transition, h, Ne.symm h] using m.accepted_balance x y

def normalizer : ℚ := ∑ x, m.weight x

theorem normalizer_pos [Nonempty α] : 0 < m.normalizer := by
  exact Finset.sum_pos (fun x _ => m.positive x) Finset.univ_nonempty

/-- Normalization is exact rational arithmetic, independent of a sampler. -/
def target (x : α) : ℚ := m.weight x / m.normalizer

theorem target_nonneg [Nonempty α] (x : α) : 0 ≤ m.target x :=
  div_nonneg (m.positive x).le m.normalizer_pos.le

theorem target_sum [Nonempty α] : ∑ x, m.target x = 1 := by
  simp only [target, ← Finset.sum_div]
  change m.normalizer / m.normalizer = 1
  exact div_self (ne_of_gt m.normalizer_pos)

theorem target_balance [DecidableEq α] (x y : α) :
    m.target x * m.transition.entry x y = m.target y * m.transition.entry y x := by
  simpa only [target, div_mul_eq_mul_div] using
    congrArg (fun z => z / m.normalizer) (m.detailed_balance x y)

theorem stationary [DecidableEq α] (y : α) :
    ∑ x, m.target x * m.transition.entry x y = m.target y := by
  simp_rw [m.target_balance]
  rw [← Finset.mul_sum, m.transition.sum_row, mul_one]

theorem acceptance_zero_forward (x y : α) (h : m.proposal.entry x y = 0) :
    m.acceptance x y = 0 := by simp [acceptance, h]

theorem accepted_zero_reverse (x y : α) (h : m.proposal.entry y x = 0) :
    m.accepted x y = 0 := by
  have hf := m.accepted_flow x y
  simp [h, min_eq_right (mul_nonneg (m.positive x).le (m.proposal.nonneg x y))] at hf
  exact hf.resolve_left (ne_of_gt (m.positive x))

end FiniteMH

namespace FiniteMHExamples

/-- Target (1/4, 3/4), proposal rows (0,1) and (1/2,1/2). -/
def asymmetric : FiniteMH Bool where
  weight x := if x then 3 else 1
  positive x := by cases x <;> norm_num
  proposal := {
    entry := fun x y => if x then 1/2 else if y then 1 else 0
    nonneg := by intro x y; cases x <;> cases y <;> norm_num
    sum_row := by intro x; cases x <;> norm_num [Fintype.sum_bool] }

/-- The reverse acceptance ratio is 2/3, not the target-only ratio 1/3. -/
theorem asymmetric_acceptance : asymmetric.acceptance true false = 2/3 := by
  norm_num [FiniteMH.acceptance, asymmetric]

theorem asymmetric_rejection : asymmetric.rejection true = 1/6 := by
  norm_num [FiniteMH.rejection, FiniteMH.accepted, FiniteMH.acceptance,
    asymmetric, Fintype.sum_bool]

/-- The 1/6 rejected mass augments the proposal's 1/2 self-loop to 2/3. -/
theorem asymmetric_transition : asymmetric.transition.entry true true = 2/3 := by
  norm_num [FiniteMH.transition, FiniteMH.rejection, FiniteMH.accepted,
    FiniteMH.acceptance, asymmetric, Fintype.sum_bool]

theorem asymmetric_target : asymmetric.target false = 1/4 ∧
    asymmetric.target true = 3/4 := by
  norm_num [FiniteMH.target, FiniteMH.normalizer, asymmetric, Fintype.sum_bool]

theorem asymmetric_stationary (y : Bool) :
    ∑ x, asymmetric.target x * asymmetric.transition.entry x y = asymmetric.target y :=
  asymmetric.stationary y

/-- Directed three-cycle proposals have no reverse support. -/
def oneWayCycle : FiniteMH (Fin 3) where
  weight _ := 1
  positive _ := by norm_num
  proposal := {
    entry := fun x y => if y = x + 1 then 1 else 0
    nonneg := by intro x y; split <;> norm_num
    sum_row := by intro x; simp }

theorem cycle_reverse_zero (x : Fin 3) :
    oneWayCycle.proposal.entry (x + 1) x = 0 := by
  fin_cases x <;> decide

/-- Even a proposal made with probability one is rejected without reverse support. -/
theorem cycle_accepted_zero (x : Fin 3) : oneWayCycle.accepted x (x + 1) = 0 :=
  oneWayCycle.accepted_zero_reverse x (x + 1) (cycle_reverse_zero x)

theorem cycle_identity (x y : Fin 3) :
    oneWayCycle.transition.entry x y = if x = y then 1 else 0 := by
  fin_cases x <;> fin_cases y <;> norm_num [FiniteMH.transition, FiniteMH.rejection, FiniteMH.accepted, FiniteMH.acceptance, oneWayCycle, Fin.sum_univ_succ]

end FiniteMHExamples
end Applications.Probability
