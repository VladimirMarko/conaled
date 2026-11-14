import Applications.Resources.BinaryCounter
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Connected cases for mapped, signed and invariant-restricted potential
accounting. These observe actual measured executions; the small transitions
below are accounting examples, not implementations of later book algorithms.
Statement review and independent expected calculations:
`docs/research/fdsa-potential-accounting.md`. -/
namespace Examples.MappedPotentialAccounting
open Resources

namespace Counter
open Resources.BinaryCounter

/-- Transport the local write law, then telescope the actual counter execution.
No canonicality or zero-initial-potential premise is required.
-/
theorem real_boundary (n : Nat) (bs : Bits) :
    (totalCost n bs : ℝ) + (ones (advance n bs) : ℝ) =
      (ones bs : ℝ) + 2 * (n : ℝ) := by
  have localLaw : ∀ (_ : Unit) s,
      (Nat.castAddMonoidHom ℝ) (incWithCost s).2 + (ones (incWithCost s).1 : ℝ) =
        (ones s : ℝ) + 2 := by
    intro _ s
    simpa [incWithCost_eq, add_comm] using
      congrArg (fun k : Nat => (k : ℝ)) (flipCost_potential s)
  have constantBudget :
      budget (fun (_ : Unit) => incWithCost) (fun _ _ => (2 : ℝ))
        (List.replicate n ()) bs = 2 * (n : ℝ) := by
    have mapped := budget_map (Nat.castAddMonoidHom ℝ)
      (fun (_ : Unit) => incWithCost) (fun _ _ => (2 : Nat)) (List.replicate n ()) bs
    rw [budget_constant] at mapped
    simpa using mapped.symm
  have boundary := run_potential_map_exact (fun (_ : Unit) => incWithCost)
    (fun _ _ => (2 : ℝ)) (fun s => (ones s : ℝ)) (Nat.castAddMonoidHom ℝ)
    localLaw (List.replicate n ()) bs
  rw [constantBudget] at boundary
  simpa only [counter_run, advanceWithCost_eq, Nat.coe_castAddMonoidHom] using boundary

example : value (advance 4 []) = 4 := by simpa [value] using value_advance 4 []

example : (totalCost 4 [] : ℝ) = 7 := by
  have boundary := real_boundary 4 []
  have final : ones (advance 4 []) = 1 := rfl
  have paid : (totalCost 4 [] : ℝ) + 1 = 8 := by
    norm_num [final, ones] at boundary
    exact boundary
  calc
    (totalCost 4 [] : ℝ) = 8 - 1 := (eq_sub_iff_add_eq).2 paid
    _ = 7 := by norm_num

example (n : Nat) : (totalCost n [] : ℝ) + (ones (advance n []) : ℝ) = 2 * n := by
  simpa [ones] using real_boundary n []

end Counter

namespace InitialCredit

private def clearStep (_ : Unit) (_ : Nat) : Measured Nat Nat := (0, 1)
private def potential (s : Nat) : Int := 2 * (s : Int)
private def charge (_ : Unit) (s : Nat) : Int := 1 - 2 * (s : Int)

example (s : Nat) : 0 ≤ potential s := by
  exact mul_nonneg (by decide) (by omega)

/-- A first charge of minus one is followed by a charge of plus one, because
the actual state has changed. The raw work remains two.
-/
private theorem boundary (is : List Unit) (s : Nat) :
    budget clearStep charge is s =
      ((run clearStep is s).2 : Int) + potential (run clearStep is s).1 - potential s := by
  change budget clearStep (fun _ t => (1 : Int) - 2 * (t : Int)) is s = _
  simpa [clearStep, potential] using
    budget_amortized clearStep potential (Nat.castAddMonoidHom Int) is s

example : charge () 1 = -1 := rfl
example : (run clearStep [(), ()] 1).2 = 2 := rfl

example : budget clearStep charge [(), ()] 1 = 0 := by
  rw [boundary]
  norm_num [run, Resources.bind, Resources.pure, clearStep, potential]

example : ¬ ((run clearStep [(), ()] 1).2 : Int) ≤
    budget clearStep charge [(), ()] 1 := by
  rw [boundary]
  norm_num [run, Resources.bind, Resources.pure, clearStep, potential]

example : budget clearStep charge [(), ()] 1 ≠ charge () 1 + charge () 1 := by
  rw [boundary]
  norm_num [run, Resources.bind, Resources.pure, clearStep, potential, charge]

end InitialCredit

namespace Fractional

private def step (_ : Unit) (s : Nat) : Measured Nat Nat :=
  if s = 0 then (1, 1) else if s = 1 then (0, 1) else (s, 100)

private def Valid (s : Nat) : Prop := s ≤ 1
private noncomputable def potential (s : Nat) : ℝ := if s = 1 then 1 / 2 else 0
private noncomputable def charge (_ : Unit) (s : Nat) : ℝ := if s = 0 then 3 / 2 else 1 / 2

private theorem closed (i : Unit) (s : Nat) (hs : Valid s) : Valid (step i s).1 := by
  have small : s = 0 ∨ s = 1 := by unfold Valid at hs; omega
  rcases small with rfl | rfl <;> norm_num [step, Valid]

private theorem localLaw (i : Unit) (s : Nat) (hs : Valid s) :
    (Nat.castAddMonoidHom ℝ) (step i s).2 + potential (step i s).1 =
      potential s + charge i s := by
  have small : s = 0 ∨ s = 1 := by unfold Valid at hs; omega
  rcases small with rfl | rfl <;> norm_num [step, potential, charge]

private theorem nonneg (s : Nat) (_ : Valid s) : 0 ≤ potential s := by
  unfold potential
  split <;> norm_num

private theorem boundary (is : List Unit) (s : Nat) (hs : Valid s) :
    ((run step is s).2 : ℝ) + potential (run step is s).1 =
      potential s + budget step charge is s :=
  run_potential_map_exact_of_invariant step charge potential (Nat.castAddMonoidHom ℝ)
    Valid closed localLaw is s hs

private theorem work_bound (is : List Unit) (s : Nat) (hs : Valid s) :
    ((run step is s).2 : ℝ) ≤ potential s + budget step charge is s :=
  run_cost_le_map_of_invariant step charge potential (Nat.castAddMonoidHom ℝ)
    Valid closed (fun i s hs => (localLaw i s hs).le) nonneg is s hs

example : Valid 0 := by norm_num [Valid]

example : budget step charge [()] 0 = (3 / 2 : ℝ) := by
  have paid := boundary [()] 0 (by norm_num [Valid])
  norm_num [run, Resources.bind, Resources.pure, step, potential] at paid
  exact paid.symm

example : budget step charge [(), ()] 0 = (2 : ℝ) := by
  have paid := boundary [(), ()] 0 (by norm_num [Valid])
  norm_num [run, Resources.bind, Resources.pure, step, potential] at paid
  exact paid.symm

example (is : List Unit) : ((run step is 0).2 : ℝ) ≤ budget step charge is 0 := by
  simpa [potential] using work_bound is 0 (by norm_num [Valid])

example : ¬ ((step () 2).2 : ℝ) + potential (step () 2).1 ≤
    potential 2 + charge () 2 := by
  norm_num [step, potential, charge]

end Fractional

/-- The exact boundary theorem also preserves noncommutative observations. -/
private def recordStep (i : Nat) (s : Unit) : Measured Unit (Additive (FreeMonoid Nat)) :=
  (s, Additive.ofMul (FreeMonoid.of i))

example (is : List Nat) :
    (run recordStep is ()).2 =
      budget recordStep (fun i _ => Additive.ofMul (FreeMonoid.of i)) is () := by
  simpa using run_potential_map_exact recordStep
    (fun i _ => Additive.ofMul (FreeMonoid.of i)) (fun _ => 0)
    (AddMonoidHom.id (Additive (FreeMonoid Nat))) (fun _ _ => by simp [recordStep]) is ()

example : budget recordStep (fun i _ => Additive.ofMul (FreeMonoid.of i)) [1, 2] () =
    Additive.ofMul (FreeMonoid.ofList [1, 2]) := rfl

end Examples.MappedPotentialAccounting
