import Applications.Resources.SelectionPolicy
import Applications.Resources.HalvingTrace

/-!
FDSA p35: halving bounds for the actual measured policy executor.

The trace and tariff below are consequences of `SelectionPolicy.runWith`.
The policy must construct an input occurrence, both strict buckets must be at
most half the current size, and its actual measured construction must satisfy
the stated uniform tariff. No distinctness assumption is used. Equal blocks
may terminate the execution early. Entries include the terminal invocation;
recursive edges are one fewer. Scan volume is kept separate from source calls.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.HalvingSelection
open Applications.Selection
universe u
variable {α : Type u} [LinearOrder α]

/-- Both possible recursive buckets halve, including on repeated values. -/
def HalvingPolicy (choose : List α → Measured (Option α) Nat) : Prop :=
  ∀ xs p, (choose xs).1 = some p →
    2 * (partition3 p xs).1.length ≤ xs.length ∧
      2 * (partition3 p xs).2.2.length ≤ xs.length

/-- The actual valid execution, not an independently supplied size sequence. -/
theorem runWith_trace (choose : List α → Measured (Option α) Nat)
    (hv : PivotValid (fun xs => (choose xs).1)) (hh : HalvingPolicy choose)
    (fuel k : Nat) (xs : List α) (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    HalvingTrace.Halves xs.length (SelectionPolicy.runWith choose fuel k xs).1.2 := by
  induction fuel generalizing k xs with
  | zero => omega
  | succ fuel ih =>
      have hx : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
      obtain ⟨p, hp, hm⟩ := hv xs hx
      have hs := partition_lengths p xs
      have hd := partition_strict_sizes p xs hm
      have hb := hh xs p hp
      rw [SelectionPolicy.runWith_step choose fuel k xs hx p hp]
      by_cases hl : k < (partition3 p xs).1.length
      · simp only [hl, ↓reduceIte, SelectionPolicy.prepend]
        exact HalvingTrace.Halves.step hb.1
          (ih k (partition3 p xs).1 hl (by omega))
      · by_cases he : k < (partition3 p xs).1.length + (partition3 p xs).2.1.length
        · simp only [hl, he, ↓reduceIte]
          exact HalvingTrace.Halves.stop (by omega)
        · simp only [hl, he, ↓reduceIte, SelectionPolicy.prepend]
          exact HalvingTrace.Halves.step hb.2
            (ih (k - (partition3 p xs).1.length - (partition3 p xs).2.1.length)
              (partition3 p xs).2.2 (by omega) (by omega))

theorem runWith_scan_bounds (choose : List α → Measured (Option α) Nat)
    (hv : PivotValid (fun xs => (choose xs).1)) (hh : HalvingPolicy choose)
    (fuel k : Nat) (xs : List α) (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    xs.length ≤ (SelectionPolicy.runWith choose fuel k xs).1.2.sum ∧
      (SelectionPolicy.runWith choose fuel k xs).1.2.sum ≤ 2 * xs.length := by
  have ht := runWith_trace choose hv hh fuel k xs hk hf
  exact ⟨HalvingTrace.initial_le_sum ht, HalvingTrace.sum_le_twice ht⟩

/-- The stronger floor-log bound counts edges, not active invocations. -/
theorem runWith_edges_log (choose : List α → Measured (Option α) Nat)
    (hv : PivotValid (fun xs => (choose xs).1)) (hh : HalvingPolicy choose)
    (fuel k : Nat) (xs : List α) (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (SelectionPolicy.runWith choose fuel k xs).1.2.length - 1 ≤ Nat.log 2 xs.length :=
  HalvingTrace.edges_le_log (runWith_trace choose hv hh fuel k xs hk hf)

theorem runWith_edges_clog (choose : List α → Measured (Option α) Nat)
    (hv : PivotValid (fun xs => (choose xs).1)) (hh : HalvingPolicy choose)
    (fuel k : Nat) (xs : List α) (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (SelectionPolicy.runWith choose fuel k xs).1.2.length - 1 ≤ Nat.clog 2 xs.length :=
  HalvingTrace.edges_le_clog (runWith_trace choose hv hh fuel k xs hk hf)

/-- At size one there is one active invocation and no recursive edge. -/
theorem runWith_singleton_trace (choose : List α → Measured (Option α) Nat)
    (hv : PivotValid (fun xs => (choose xs).1)) (hh : HalvingPolicy choose)
    (fuel : Nat) (x : α) :
    (SelectionPolicy.runWith choose (fuel + 1) 0 [x]).1.2 = [1] :=
  HalvingTrace.singleton_at_one
    (runWith_trace choose hv hh (fuel + 1) 0 [x] (by simp) (by simp))

/-- Charge the actual pivot execution, both bucket lengths and equal lookup.
This trace tariff does not require halving; it follows each actual valid path.
The callback bound must hold for every nonempty intermediate input. -/
theorem runWith_tariff (choose : List α → Measured (Option α) Nat)
    (hv : PivotValid (fun xs => (choose xs).1)) (A B : Nat)
    (hc : ∀ ys, ys ≠ [] → (choose ys).2 ≤ A * ys.length + B)
    (fuel k : Nat) (xs : List α) (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    (SelectionPolicy.runWith choose fuel k xs).1.2.sum ≤
        (SelectionPolicy.runWith choose fuel k xs).2 ∧
      (SelectionPolicy.runWith choose fuel k xs).2 ≤
        (A + 4) * (SelectionPolicy.runWith choose fuel k xs).1.2.sum +
          (B + 5) * (SelectionPolicy.runWith choose fuel k xs).1.2.length := by
  induction fuel generalizing k xs with
  | zero => omega
  | succ fuel ih =>
      have hx : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
      obtain ⟨p, hp, hm⟩ := hv xs hx
      have hs := partition_lengths p xs
      have hd := partition_strict_sizes p xs hm
      have hpCost := hc xs hx
      have local_bound :
          (xs.length + 1) + (choose xs).2 + (xs.length + 1) +
            ((partition3 p xs).1.length + 1) +
            ((partition3 p xs).2.1.length + 1) + 1 ≤
          (A + 4) * xs.length + (B + 5) := by
        rw [Nat.add_mul]
        omega
      rw [SelectionPolicy.runWith_step choose fuel k xs hx p hp]
      by_cases hl : k < (partition3 p xs).1.length
      · have hi := ih k (partition3 p xs).1 hl (by omega)
        simp only [hl, ↓reduceIte, SelectionPolicy.prepend,
          List.sum_cons, List.length_cons]
        constructor
        · omega
        · simp only [Nat.mul_add, Nat.mul_one]
          omega
      · by_cases he : k < (partition3 p xs).1.length + (partition3 p xs).2.1.length
        · have hi : k - (partition3 p xs).1.length < (partition3 p xs).2.1.length := by
            omega
          have lookup_bound :
              min (k - (partition3 p xs).1.length) (partition3 p xs).2.1.length + 1 ≤
                xs.length := by omega
          simp only [hl, he, ↓reduceIte, List.sum_cons, List.sum_nil,
            List.length_cons, List.length_nil, Nat.add_zero, Nat.mul_one]
          constructor
          · omega
          · rw [Nat.add_mul]
            omega
        · have hi := ih
            (k - (partition3 p xs).1.length - (partition3 p xs).2.1.length)
            (partition3 p xs).2.2 (by omega) (by omega)
          simp only [hl, he, ↓reduceIte, SelectionPolicy.prepend,
            List.sum_cons, List.length_cons]
          constructor
          · omega
          · simp only [Nat.mul_add, Nat.mul_one]
            omega

/-- Actual source calls are uniformly linear once an actual linear pivot
constructor and actual halving property have been established. -/
theorem runWith_linear_cost (choose : List α → Measured (Option α) Nat)
    (hv : PivotValid (fun xs => (choose xs).1)) (hh : HalvingPolicy choose)
    (A B : Nat) (hc : ∀ ys, ys ≠ [] → (choose ys).2 ≤ A * ys.length + B)
    (fuel k : Nat) (xs : List α) (hk : k < xs.length) (hf : xs.length ≤ fuel) :
    xs.length ≤ (SelectionPolicy.runWith choose fuel k xs).2 ∧
      (SelectionPolicy.runWith choose fuel k xs).2 ≤
        (2 * (A + 4) + 2 * (B + 5)) * xs.length := by
  have ht := runWith_trace choose hv hh fuel k xs hk hf
  have hc' := runWith_tariff choose hv A B hc fuel k xs hk hf
  have volume := HalvingTrace.sum_le_twice ht
  have entries := (HalvingTrace.length_le_sum ht).trans volume
  refine ⟨(HalvingTrace.initial_le_sum ht).trans hc'.1, ?_⟩
  calc
    (SelectionPolicy.runWith choose fuel k xs).2 ≤
        (A + 4) * (SelectionPolicy.runWith choose fuel k xs).1.2.sum +
          (B + 5) * (SelectionPolicy.runWith choose fuel k xs).1.2.length := hc'.2
    _ ≤ (A + 4) * (2 * xs.length) + (B + 5) * (2 * xs.length) :=
      Nat.add_le_add (Nat.mul_le_mul_left (A + 4) volume)
        (Nat.mul_le_mul_left (B + 5) entries)
    _ = (2 * (A + 4) + 2 * (B + 5)) * xs.length := by ring

end Resources.HalvingSelection
