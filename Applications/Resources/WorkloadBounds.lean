import Applications.Resources.Workload

/-!
# Bounds on actual runs with restricted inputs

The command list must stay in the allowed domain and the initial state must
satisfy the invariant. Both local premises apply only there. Each tail starts
at the preceding step's returned state; no replacement trajectory is executed.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources

universe u v w
variable {ι : Type u} {σ : Type v} {C : Type w}

theorem run_invariant_on [Zero C] [Add C] (step : ι → σ → Measured σ C)
    (allowed : ι → Prop) (I : σ → Prop)
    (closed : ∀ i s, allowed i → I s → I (step i s).1)
    (is : List ι) (inputs : ∀ i ∈ is, allowed i) (s : σ) (initial : I s) :
    I (run step is s).1 := by
  induction is generalizing s with
  | nil => exact initial
  | cons i is ih =>
      exact ih (fun j hj => inputs j (List.mem_cons_of_mem i hj)) _
        (closed i s (inputs i (List.mem_cons_self)) initial)

theorem run_work_le_sum_on (step : ι → σ → Measured σ Nat)
    (allowed : ι → Prop) (I : σ → Prop) (weight : ι → Nat)
    (closed : ∀ i s, allowed i → I s → I (step i s).1)
    (bounded : ∀ i s, allowed i → I s → (step i s).2 ≤ weight i)
    (is : List ι) (inputs : ∀ i ∈ is, allowed i) (s : σ) (initial : I s) :
    (run step is s).2 ≤ (is.map weight).sum := by
  induction is generalizing s with
  | nil => exact Nat.le_refl 0
  | cons i is ih =>
      have hi := inputs i (List.mem_cons_self)
      have tail := ih (fun j hj => inputs j (List.mem_cons_of_mem i hj)) _
        (closed i s hi initial)
      simpa only [run_cons, List.map_cons, List.sum_cons] using
        Nat.add_le_add (bounded i s hi initial) tail

theorem run_work_le_on (step : ι → σ → Measured σ Nat)
    (allowed : ι → Prop) (I : σ → Prop) (bound : Nat)
    (closed : ∀ i s, allowed i → I s → I (step i s).1)
    (bounded : ∀ i s, allowed i → I s → (step i s).2 ≤ bound)
    (is : List ι) (inputs : ∀ i ∈ is, allowed i) (s : σ) (initial : I s) :
    (run step is s).2 ≤ is.length * bound := by
  calc
    _ ≤ (is.map (fun _ => bound)).sum :=
      run_work_le_sum_on step allowed I (fun _ => bound) closed bounded is inputs s initial
    _ = is.length * bound := by
      clear inputs
      induction is with
      | nil => simp
      | cons i is ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
          Nat.add_mul, Nat.one_mul, ih, Nat.add_comm]

end Resources
