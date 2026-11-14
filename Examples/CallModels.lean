import Applications.Resources.CallComparison
import Applications.Resources.ListReversal
import Mathlib.Tactic.NormNum

/-! Independent expected calculations for the Chapter1 tariff and inlining
comparisons, connected to their public laws and the actual append call count.
See `docs/research/fdsa-call-models.md` for the model and statement review.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.CallModels
open Resources Resources.CallCount
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Source append enters one cons branch per element, then its terminal branch. -/
def appendEvents (xs : List α) : List Bool := xs.map (fun _ => true) ++ [false]

theorem appendEvents_nil : appendEvents ([] : List α) = [false] := rfl

theorem appendEvents_cons (x : α) (xs : List α) :
    appendEvents (x :: xs) = true :: appendEvents xs := rfl

theorem appendEvents_cost (xs ys : List α) :
    (ListReversal.appendRun xs ys).2 = (appendEvents xs).length := by
  simp [ListReversal.appendRun_exact, appendEvents]

/-- Illustrative local tariff: terminal variable access, or three accesses and
one constructor in a cons body. It does not count compiler instructions.
-/
def appendExtra : Bool → Nat
  | false => 1
  | true => 4

theorem append_refined_exact (xs : List α) :
    refinedCost appendExtra (appendEvents xs) = 5 * xs.length + 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [appendEvents_cons, refinedCost_cons, ih]
      simp [appendExtra, Nat.mul_add]
      omega

theorem append_refined_bounds (xs ys : List α) :
    (ListReversal.appendRun xs ys).2 ≤ refinedCost appendExtra (appendEvents xs) ∧
      refinedCost appendExtra (appendEvents xs) ≤ 5 * (ListReversal.appendRun xs ys).2 := by
  rw [appendEvents_cost]
  have covered : ∀ b ∈ appendEvents xs, b ∈ ({false, true} : Finset Bool) := by
    intro b _
    cases b <;> simp
  have catalogue := catalogue_refined_bounds appendExtra {false, true} (appendEvents xs) covered
  have cap : ({false, true} : Finset Bool).sup appendExtra = 4 := by decide
  simpa only [cap] using catalogue

theorem append_refined_isBigO (l : Filter β) (xs ys : β → List α) :
    Asymptotics.IsBigO l (fun x => (refinedCost appendExtra (appendEvents (xs x)) : ℝ))
      (fun x => ((ListReversal.appendRun (xs x) (ys x)).2 : ℝ)) := by
  have bound : ∀ x b, b ∈ appendEvents (xs x) → appendExtra b ≤ 4 := by
    intro _ b _
    cases b <;> decide
  simpa only [appendEvents_cost] using refinedCost_isBigO l
    (fun x => appendEvents (xs x)) appendExtra 4 (Filter.Eventually.of_forall bound)

example : refinedCost appendExtra (appendEvents ([3, 1, 3] : List Nat)) = 17 :=
  append_refined_exact _

example : (ListReversal.appendRun ([3, 1, 3] : List Nat) [9]).2 = 4 := by
  rw [appendEvents_cost]
  rfl

example : refinedCost appendExtra (appendEvents ([] : List Empty)) = 2 :=
  append_refined_exact _

example (xs : List α) : refinedCost (fun _ : α => 0) xs = xs.length :=
  refinedCost_zero xs

example (l : Filter α) (program : α → Measured β Nat)
    (positive : ∀ᶠ x in l, 1 ≤ (program x).2) :
    Asymptotics.IsBigO l (fun x => ((tick (program x)).2 : ℝ))
      (fun x => ((program x).2 : ℝ)) := by
  simpa only [tick_cost] using add_entry_isBigO l (fun x => (program x).2) positive

example (r : Measured α Nat) : (tick r).1 = r.1 := tick_value r

example (K : Nat) : ¬ (tick (pure () : Measured Unit Nat)).2 ≤ K * 0 :=
  zero_cost_entry_matters K

/-- An intermittently zero family is not covered by eventual positivity. -/
def intermittentCost (n : Nat) : Nat := if n % 2 = 0 then 0 else n

example : intermittentCost 1 = 1 := rfl

theorem intermittent_entry_not_isBigO :
    ¬ Asymptotics.IsBigO Filter.atTop
      (fun n => ((intermittentCost n + 1 : Nat) : ℝ))
      (fun n => (intermittentCost n : ℝ)) := by
  intro h
  obtain ⟨C, bound⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨N, fromN⟩ := Filter.eventually_atTop.mp bound
  have even := fromN (2 * N) (by omega)
  have zero : intermittentCost (2 * N) = 0 := by simp [intermittentCost]
  norm_num [zero] at even

end Examples.CallModels
