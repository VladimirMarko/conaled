import Applications.Resources.Workload
import Mathlib.Algebra.Order.Group.Nat

/-! Trajectory-dependent charges and telescoping with explicit boundary potentials.
Provenance and statement review: `docs/research/adwh-potential-accounting.md`. -/
namespace Resources
universe u v w x y
variable {ι : Type u} {σ : Type v} {C : Type w} {D : Type x} {E : Type y}

/-- Sum charges along the actual state trajectory. The charge and step observation
may have different types; only the step's state projection selects the next state. -/
def budget [Zero D] [Add D] (step : ι → σ → σ × C) (charge : ι → σ → D) :
    List ι → σ → D
  | [], _ => 0
  | i :: is, s => charge i s + budget step charge is (step i s).1

theorem budget_append [Zero C] [Add C] [AddMonoid D]
    (step : ι → σ → σ × C) (charge : ι → σ → D)
    (is js : List ι) (s : σ) :
    budget step charge (is ++ js) s =
      budget step charge is s + budget step charge js (run step is s).1 := by
  induction is generalizing s with
  | nil => simp [run, pure, budget]
  | cons i is ih => simp [run, bind, budget, ih, add_assoc]

/-- An additive observation map commutes with summing charges on a fixed trajectory. -/
theorem budget_map [AddMonoid D] [AddMonoid E] (h : D →+ E)
    (step : ι → σ → σ × C) (charge : ι → σ → D) (is : List ι) (s : σ) :
    h (budget step charge is s) =
      budget step (fun i s => h (charge i s)) is s := by
  induction is generalizing s with
  | nil => simp only [budget, map_zero]
  | cons i is ih => simp only [budget, map_add, ih]

/-- Changing a step's observation preserves the budget whenever its next state is
unchanged. No algebraic structure on either step observation is required. -/
theorem budget_congr_state [Zero D] [Add D]
    (step : ι → σ → σ × C) (other : ι → σ → σ × E) (charge : ι → σ → D)
    (same : ∀ i s, (step i s).1 = (other i s).1) (is : List ι) (s : σ) :
    budget step charge is s = budget other charge is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => simp only [budget, ih, same]

/-- Source equation (2.3), expressed without truncated subtraction. -/
theorem charge_iff_signed (cost before after amortized : Nat) :
    cost + after ≤ before + amortized ↔
      (cost : Int) ≤ (before : Int) - after + amortized := by omega

/-- General telescoping bound with both boundary potentials retained. Addition
need only be monotone on each side; costs and charges need not be nonnegative. -/
theorem run_potential [AddMonoid C] [Preorder C] [AddLeftMono C] [AddRightMono C]
    (step : ι → σ → σ × C) (charge : ι → σ → C) (potential : σ → C)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (is : List ι) (s : σ) :
    (run step is s).2 + potential (run step is s).1 ≤
      potential s + budget step charge is s := by
  induction is generalizing s with
  | nil => simp [run, pure, budget]
  | cons i is ih =>
      simp only [run_cons, budget]
      calc
        ((step i s).2 + (run step is (step i s).1).2) +
            potential (run step is (step i s).1).1 =
            (step i s).2 + ((run step is (step i s).1).2 +
              potential (run step is (step i s).1).1) := add_assoc _ _ _
        _ ≤ (step i s).2 + (potential (step i s).1 +
              budget step charge is (step i s).1) :=
          add_le_add_left (ih (step i s).1) _
        _ = ((step i s).2 + potential (step i s).1) +
              budget step charge is (step i s).1 := (add_assoc _ _ _).symm
        _ ≤ (potential s + charge i s) + budget step charge is (step i s).1 :=
          add_le_add_right (hstep i s) _
        _ = potential s + (charge i s + budget step charge is (step i s).1) :=
          add_assoc _ _ _

/-- Exact local identities telescope in execution order. Neither commutativity,
cancellation nor an order on the additive monoid is required. -/
theorem run_potential_exact [AddMonoid C]
    (step : ι → σ → σ × C) (charge : ι → σ → C) (potential : σ → C)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 = potential s + charge i s)
    (is : List ι) (s : σ) :
    (run step is s).2 + potential (run step is s).1 =
      potential s + budget step charge is s := by
  induction is generalizing s with
  | nil => simp [run, pure, budget]
  | cons i is ih =>
      simp only [run_cons, budget]
      rw [add_assoc, ih, ← add_assoc (step i s).2, hstep, add_assoc]

/-- A cost-only bound may discard the final potential when that actual final
value is nonnegative. This premise is automatic for Nat, but not for Int or Real. -/
theorem run_cost_le_of_nonneg_final
    [AddMonoid C] [Preorder C] [AddLeftMono C] [AddRightMono C]
    (step : ι → σ → σ × C) (charge : ι → σ → C) (potential : σ → C)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (is : List ι) (s : σ) (hfinal : 0 ≤ potential (run step is s).1) :
    (run step is s).2 ≤ potential s + budget step charge is s := by
  have below : (run step is s).2 ≤
      (run step is s).2 + potential (run step is s).1 := by
    simpa only [add_zero] using add_le_add_left hfinal (run step is s).2
  exact below.trans (run_potential step charge potential hstep is s)

theorem run_cost_le (step : ι → σ → σ × Nat) (charge : ι → σ → Nat)
    (potential : σ → Nat)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (is : List ι) (s : σ) :
    (run step is s).2 ≤ potential s + budget step charge is s := by
  exact run_cost_le_of_nonneg_final step charge potential hstep is s (Nat.zero_le _)

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
