import Applications.Resources.Workload
import Mathlib.Algebra.Order.Group.Nat

/-! Trajectory-dependent charges and telescoping with explicit boundary potentials.
Raw work and accounting charges can have different carriers. The additive
boundary laws preserve observation order; signed amortized charges use a
commutative group. Provenance and statement review:
`docs/research/adwh-potential-accounting.md` and
`docs/research/fdsa-potential-accounting.md`. -/
namespace Resources
universe u v w x y
variable {ι : Type u} {σ : Type v} {C : Type w} {D : Type x} {E : Type y}

/-- Sum amortized charges along the same actual state trajectory. -/
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

/-- Additive observation maps preserve a budget on its actual state trajectory.
The raw work carrier needs no algebra because this observation uses only states.
-/
theorem budget_map [AddZero D] [AddZero E] (h : D →+ E)
    (step : ι → σ → σ × C) (charge : ι → σ → D) (is : List ι) (s : σ) :
    h (budget step charge is s) = budget step (fun i s => h (charge i s)) is s := by
  induction is generalizing s with
  | nil => exact h.map_zero
  | cons i is ih => simp only [budget, map_add, ih]

/-- Mapped work telescopes using local laws only on preserved valid states.
Neither carrier needs an order-compatible cost map: the supplied local law
already compares its image. The accounting addition need not commute.
-/
theorem run_potential_map_of_invariant [AddZero C] [AddMonoid D] [Preorder D]
    [AddLeftMono D] [AddRightMono D]
    (step : ι → σ → σ × C) (charge : ι → σ → D) (potential : σ → D)
    (h : C →+ D) (P : σ → Prop)
    (closed : ∀ i s, P s → P (step i s).1)
    (hstep : ∀ i s, P s →
      h (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (is : List ι) (s : σ) (hs : P s) :
    h (run step is s).2 + potential (run step is s).1 ≤
      potential s + budget step charge is s := by
  induction is generalizing s with
  | nil => simp [run, pure, budget]
  | cons i is ih =>
      have localLaw := hstep i s hs
      have tail := ih (step i s).1 (closed i s hs)
      simp only [run_cons, budget, map_add]
      calc
        (h (step i s).2 + h (run step is (step i s).1).2) +
            potential (run step is (step i s).1).1 =
            h (step i s).2 +
              (h (run step is (step i s).1).2 + potential (run step is (step i s).1).1) :=
          add_assoc _ _ _
        _ ≤ h (step i s).2 +
            (potential (step i s).1 + budget step charge is (step i s).1) :=
          ‹AddLeftMono D›.elim (h (step i s).2) tail
        _ = (h (step i s).2 + potential (step i s).1) +
            budget step charge is (step i s).1 := (add_assoc _ _ _).symm
        _ ≤ (potential s + charge i s) + budget step charge is (step i s).1 :=
          ‹AddRightMono D›.elim (budget step charge is (step i s).1) localLaw
        _ = potential s + (charge i s + budget step charge is (step i s).1) :=
          add_assoc _ _ _

/-- Exact boundary accounting needs only additive laws in the target. -/
theorem run_potential_map_exact_of_invariant [AddZero C] [AddMonoid D]
    (step : ι → σ → σ × C) (charge : ι → σ → D) (potential : σ → D)
    (h : C →+ D) (P : σ → Prop)
    (closed : ∀ i s, P s → P (step i s).1)
    (hstep : ∀ i s, P s →
      h (step i s).2 + potential (step i s).1 = potential s + charge i s)
    (is : List ι) (s : σ) (hs : P s) :
    h (run step is s).2 + potential (run step is s).1 =
      potential s + budget step charge is s := by
  induction is generalizing s with
  | nil => simp [run, pure, budget]
  | cons i is ih =>
      have localLaw := hstep i s hs
      have tail := ih (step i s).1 (closed i s hs)
      simp only [run_cons, budget, map_add]
      calc
        (h (step i s).2 + h (run step is (step i s).1).2) +
            potential (run step is (step i s).1).1 =
            h (step i s).2 +
              (h (run step is (step i s).1).2 + potential (run step is (step i s).1).1) :=
          add_assoc _ _ _
        _ = h (step i s).2 +
            (potential (step i s).1 + budget step charge is (step i s).1) :=
          congrArg (fun d => h (step i s).2 + d) tail
        _ = (h (step i s).2 + potential (step i s).1) +
            budget step charge is (step i s).1 := (add_assoc _ _ _).symm
        _ = (potential s + charge i s) + budget step charge is (step i s).1 :=
          congrArg (fun d => d + budget step charge is (step i s).1) localLaw
        _ = potential s + (charge i s + budget step charge is (step i s).1) :=
          add_assoc _ _ _

theorem run_potential_map [AddZero C] [AddMonoid D] [Preorder D]
    [AddLeftMono D] [AddRightMono D]
    (step : ι → σ → σ × C) (charge : ι → σ → D) (potential : σ → D)
    (h : C →+ D)
    (hstep : ∀ i s,
      h (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (is : List ι) (s : σ) :
    h (run step is s).2 + potential (run step is s).1 ≤
      potential s + budget step charge is s :=
  run_potential_map_of_invariant step charge potential h (fun _ => True)
    (fun _ _ _ => True.intro) (fun i s _ => hstep i s) is s True.intro

theorem run_potential_map_exact [AddZero C] [AddMonoid D]
    (step : ι → σ → σ × C) (charge : ι → σ → D) (potential : σ → D)
    (h : C →+ D)
    (hstep : ∀ i s,
      h (step i s).2 + potential (step i s).1 = potential s + charge i s)
    (is : List ι) (s : σ) :
    h (run step is s).2 + potential (run step is s).1 =
      potential s + budget step charge is s :=
  run_potential_map_exact_of_invariant step charge potential h (fun _ => True)
    (fun _ _ _ => True.intro) (fun i s _ => hstep i s) is s True.intro

/-- Dropping the final potential requires its nonnegativity on the actual
preserved domain. The initial potential remains available in the conclusion.
-/
theorem run_cost_le_map_of_invariant [AddZero C] [AddMonoid D] [Preorder D]
    [AddLeftMono D] [AddRightMono D]
    (step : ι → σ → σ × C) (charge : ι → σ → D) (potential : σ → D)
    (h : C →+ D) (P : σ → Prop)
    (closed : ∀ i s, P s → P (step i s).1)
    (hstep : ∀ i s, P s →
      h (step i s).2 + potential (step i s).1 ≤ potential s + charge i s)
    (nonneg : ∀ s, P s → 0 ≤ potential s)
    (is : List ι) (s : σ) (hs : P s) :
    h (run step is s).2 ≤ potential s + budget step charge is s := by
  have final := nonneg _ (run_invariant step P closed is s hs)
  have boundary := run_potential_map_of_invariant step charge potential h P
    closed hstep is s hs
  have lower : h (run step is s).2 ≤
      h (run step is s).2 + potential (run step is s).1 := by
    simpa only [add_zero] using
      ‹AddLeftMono D›.elim (h (run step is s).2) final
  exact lower.trans boundary

/-- The signed source amortized expression, summed along the actual trajectory.
Commutative-group subtraction is essential here; no sign assumptions are needed.
-/
theorem budget_amortized [AddZero C] [AddCommGroup D]
    (step : ι → σ → σ × C) (potential : σ → D) (h : C →+ D)
    (is : List ι) (s : σ) :
    budget step (fun i s => h (step i s).2 + potential (step i s).1 - potential s) is s =
      h (run step is s).2 + potential (run step is s).1 - potential s := by
  have boundary := run_potential_map_exact step
    (fun i s => h (step i s).2 + potential (step i s).1 - potential s) potential h
    (fun i s => by rw [add_comm (potential s), sub_add_cancel]) is s
  apply (eq_sub_iff_add_eq).2
  exact (add_comm _ _).trans boundary.symm

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
      potential s + budget step charge is s :=
  run_potential_map step charge potential (AddMonoidHom.id Nat) hstep is s

/-- Exact local identities telescope to an exact global identity. -/
theorem run_potential_exact (step : ι → σ → σ × Nat) (charge : ι → σ → Nat)
    (potential : σ → Nat)
    (hstep : ∀ i s, (step i s).2 + potential (step i s).1 = potential s + charge i s)
    (is : List ι) (s : σ) :
    (run step is s).2 + potential (run step is s).1 =
      potential s + budget step charge is s :=
  run_potential_map_exact step charge potential (AddMonoidHom.id Nat) hstep is s

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
