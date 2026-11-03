import Applications.Resources.Workload
import Mathlib.Algebra.Group.Nat.Defs

/-! Trajectory-dependent charges and telescoping with explicit boundary potentials.
Provenance and statement review: `docs/research/adwh-potential-accounting.md`. -/
namespace Resources
universe u v
variable {ι : Type u} {σ : Type v}

/-- Sum amortized charges along the same actual state trajectory. -/
def budget (step : ι → σ → σ × Nat) (charge : ι → σ → Nat) : List ι → σ → Nat
  | [], _ => 0
  | i :: is, s => charge i s + budget step charge is (step i s).1

theorem budget_append (step : ι → σ → σ × Nat) (charge : ι → σ → Nat)
    (is js : List ι) (s : σ) :
    budget step charge (is ++ js) s =
      budget step charge is s + budget step charge js (run step is s).1 := by
  induction is generalizing s with
  | nil => simp [run, pure, budget]
  | cons i is ih => simp [run, bind, budget, ih, Nat.add_assoc]

/-- Source equation (2.3), expressed without truncated subtraction. -/
theorem charge_iff_signed (cost before after amortized : Nat) :
    cost + after ≤ before + amortized ↔
      (cost : Int) ≤ (before : Int) - after + amortized := by omega

/-- General telescoping bound with both boundary potentials retained. -/
theorem run_potential (step : ι → σ → σ × Nat) (charge : ι → σ → Nat)
    (potential : σ → Nat)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (is : List ι) (s : σ) :
    (run step is s).2 + potential (run step is s).1 ≤
      potential s + budget step charge is s := by
  induction is generalizing s with
  | nil => simp [run, pure, budget]
  | cons i is ih =>
      have hs := hstep i s
      have hr := ih (step i s).1
      simp only [run, bind, budget]
      omega

/-- Exact local identities telescope to an exact global identity. -/
theorem run_potential_exact (step : ι → σ → σ × Nat) (charge : ι → σ → Nat)
    (potential : σ → Nat)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 = potential s + charge i s)
    (is : List ι) (s : σ) :
    (run step is s).2 + potential (run step is s).1 =
      potential s + budget step charge is s := by
  induction is generalizing s with
  | nil => simp [run, pure, budget]
  | cons i is ih =>
      have hs := hstep i s
      have hr := ih (step i s).1
      simp only [run, bind, budget]
      omega

theorem run_cost_le (step : ι → σ → σ × Nat) (charge : ι → σ → Nat)
    (potential : σ → Nat)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (is : List ι) (s : σ) :
    (run step is s).2 ≤ potential s + budget step charge is s := by
  have h := run_potential step charge potential hstep is s
  omega

theorem run_zero_potential (step : ι → σ → σ × Nat) (charge : ι → σ → Nat)
    (potential : σ → Nat)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (is : List ι) (s : σ) (zero : potential s = 0) :
    (run step is s).2 ≤ budget step charge is s := by
  simpa [zero] using run_cost_le step charge potential hstep is s

theorem budget_constant (step : ι → σ → σ × Nat) (k : Nat) (is : List ι) (s : σ) :
    budget step (fun _ _ => k) is s = k * is.length := by
  induction is generalizing s with
  | nil => simp [budget]
  | cons i is ih => simp [budget, ih, Nat.mul_add, Nat.add_comm]

theorem budget_le_constant (step : ι → σ → σ × Nat) (charge : ι → σ → Nat)
    (k : Nat) (bound : ∀ i s, charge i s ≤ k) (is : List ι) (s : σ) :
    budget step charge is s ≤ k * is.length := by
  induction is generalizing s with
  | nil => simp [budget]
  | cons i is ih =>
      have hs := bound i s
      have hr := ih (step i s).1
      simp only [budget, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem run_constant_charge (step : ι → σ → σ × Nat) (potential : σ → Nat)
    (k : Nat)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 ≤ potential s + k)
    (is : List ι) (s : σ) :
    (run step is s).2 + potential (run step is s).1 ≤ potential s + k * is.length := by
  simpa [budget_constant] using
    run_potential step (fun _ _ => k) potential hstep is s


/-- A run may spend stored initial potential even with zero new charge. -/
theorem initial_potential_matters :
    let step : Unit → Nat → Measured Nat Nat := fun _ s => (0, s)
    (∀ i s, (step i s).2 + (step i s).1 ≤ s + 0) ∧
      (run step [()] 1).2 > budget step (fun _ _ => 0) [()] 1 := by
  constructor
  · intro _ s; simp
  · decide

end Resources
