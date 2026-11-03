import Applications.Resources.BinaryCounter
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.NormNum

/-! Connected applications of the shared potential laws. The Real observer
reweights the existing counted-write program; ordered words exercise exact
accounting without a commutativity assumption. -/
namespace Examples.PotentialTransport
open Resources

namespace Counter
open Resources.BinaryCounter

/-- Preserve the increment program and map only its measured write count. -/
def realStep (_ : Unit) (bs : Bits) : Measured Bits ℝ :=
  reweight (Nat.castAddMonoidHom ℝ) (incWithCost bs)

theorem realStep_potential (i : Unit) (bs : Bits) :
    (realStep i bs).2 + (ones (realStep i bs).1 : ℝ) = (ones bs : ℝ) + 2 := by
  simpa [realStep, reweight, incWithCost_eq, add_comm] using
    congrArg (fun k : Nat => (k : ℝ)) (flipCost_potential bs)

/-- Both projections refer to the original measured run. -/
theorem realRun_transport (n : Nat) (bs : Bits) :
    run realStep (List.replicate n ()) bs =
      ((advanceWithCost n bs).1, ((advanceWithCost n bs).2 : ℝ)) := by
  exact (reweight_run (Nat.castAddMonoidHom ℝ)
    (fun (_ : Unit) => incWithCost) (List.replicate n ()) bs).symm

/-- Map the existing Nat budget along the unchanged state trajectory. -/
theorem realBudget (n : Nat) (bs : Bits) :
    budget realStep (fun _ _ => (2 : ℝ)) (List.replicate n ()) bs = 2 * (n : ℝ) := by
  calc
    budget realStep (fun _ _ => (2 : ℝ)) (List.replicate n ()) bs =
        budget (fun (_ : Unit) => incWithCost) (fun _ _ => (2 : ℝ))
          (List.replicate n ()) bs :=
      budget_congr_state realStep (fun (_ : Unit) => incWithCost)
        (fun _ _ => (2 : ℝ)) (fun _ _ => rfl) (List.replicate n ()) bs
    _ = (budget (fun (_ : Unit) => incWithCost) (fun _ _ => (2 : Nat))
          (List.replicate n ()) bs : ℝ) := by
      simpa only [Nat.coe_castAddMonoidHom, Nat.cast_ofNat] using
        (budget_map (Nat.castAddMonoidHom ℝ) (fun (_ : Unit) => incWithCost)
          (fun _ _ => (2 : Nat)) (List.replicate n ()) bs).symm
    _ = 2 * (n : ℝ) := by simp [budget_constant]

/-- Apply the exact telescope to the lifted local law, for every initial state. -/
theorem realRun_potential (n : Nat) (bs : Bits) :
    (run realStep (List.replicate n ()) bs).2 +
        (ones (run realStep (List.replicate n ()) bs).1 : ℝ) =
      (ones bs : ℝ) + 2 * (n : ℝ) := by
  simpa only [realBudget] using
    run_potential_exact realStep (fun _ _ => (2 : ℝ))
      (fun bs => (ones bs : ℝ)) realStep_potential (List.replicate n ()) bs

theorem realRun_bound (n : Nat) (bs : Bits) :
    (run realStep (List.replicate n ()) bs).2 ≤ (ones bs : ℝ) + 2 * (n : ℝ) := by
  have hfinal : 0 ≤ (ones (run realStep (List.replicate n ()) bs).1 : ℝ) :=
    Nat.cast_nonneg _
  simpa only [realBudget] using
    run_cost_le_of_nonneg_final realStep (fun _ _ => (2 : ℝ))
      (fun bs => (ones bs : ℝ)) (fun i bs => le_of_eq (realStep_potential i bs))
      (List.replicate n ()) bs hfinal

example (n : Nat) : (run realStep (List.replicate n ()) []).2 ≤ 2 * (n : ℝ) := by
  simpa only [ones, Nat.cast_zero, zero_add] using realRun_bound n []

/-- The independent write calculation is 1 + 2 + 1 + 3 = 7. -/
theorem realRun_four :
    run realStep (List.replicate 4 ()) [] = ([false, false, true], (7 : ℝ)) := by
  have observed : advanceWithCost 4 [] = ([false, false, true], 7) := rfl
  simpa only [observed, Nat.cast_ofNat] using realRun_transport 4 []

/-- The four-step run retains one final one bit: its account is 7 + 1 = 8. -/
theorem realRun_four_balance :
    (run realStep (List.replicate 4 ()) []).2 +
      (ones (run realStep (List.replicate 4 ()) []).1 : ℝ) = 8 := by
  calc
    _ = (ones ([] : Bits) : ℝ) + 2 * (4 : ℝ) := realRun_potential 4 []
    _ = 8 := by norm_num [ones]

end Counter

namespace OrderedWords

/-- Emit the first token of the remaining word, with no reordering. -/
def step (_ : Unit) : List Nat → Measured (List Nat) (FreeAddMonoid Nat)
  | [] => ([], 0)
  | x :: xs => (xs, FreeAddMonoid.of x)

theorem step_potential (i : Unit) (xs : List Nat) :
    (step i xs).2 + FreeAddMonoid.ofList (step i xs).1 =
      FreeAddMonoid.ofList xs + (0 : FreeAddMonoid Nat) := by
  cases xs <;> simp [step]

theorem two_steps :
    run step [(), ()] [1, 2, 3] = ([3], FreeAddMonoid.ofList [1, 2]) := by
  change run step ([()] ++ [()]) [1, 2, 3] = _
  rw [run_append]
  rfl

/-- Emitted tokens precede the remaining tokens in the exact identity. -/
theorem two_steps_conserve :
    (run step [(), ()] [1, 2, 3]).2 +
        FreeAddMonoid.ofList (run step [(), ()] [1, 2, 3]).1 =
      FreeAddMonoid.ofList [1, 2, 3] := by
  simpa only [budget, zero_add, add_zero] using
    run_potential_exact step (fun _ _ => (0 : FreeAddMonoid Nat))
      FreeAddMonoid.ofList step_potential [(), ()] [1, 2, 3]

end OrderedWords

namespace IndependentCharge

def step (_ : Unit) (s : Nat) : Measured Nat Nat := (s + 1, 1)

def charge (_ : Unit) (s : Nat) : FreeAddMonoid Nat := FreeAddMonoid.of s

/-- Nat observations and ordered-word charges follow the same actual states. -/
theorem two_step_budget :
    budget step charge [(), ()] 0 = FreeAddMonoid.ofList [0, 1] := by
  calc
    budget step charge [(), ()] 0 =
        budget step charge [()] 0 + budget step charge [()] (run step [()] 0).1 :=
      budget_append step charge [()] [()] 0
    _ = FreeAddMonoid.ofList [0, 1] := rfl

end IndependentCharge
end Examples.PotentialTransport
