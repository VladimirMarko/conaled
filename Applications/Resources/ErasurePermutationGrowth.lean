import Applications.Resources.ErasurePermutations
import Applications.Resources.PositionalPermutationGrowth

/-! Bounds for executed first-equal removal, with unit-priced equality oracles. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.ErasurePermutations
universe u
variable {α : Type u}

private theorem sum_bounds (f : α → Nat) (xs : List α) (a b : Nat)
    (h : ∀ x ∈ xs, a ≤ f x ∧ f x ≤ b) :
    xs.length*a ≤ (xs.map f).sum ∧ (xs.map f).sum ≤ xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    constructor <;> omega

variable [DecidableEq α]

theorem generate_bounds_all (xs : List α) :
    (5*xs.length+1)*Nat.factorial xs.length ≤ (generate xs).2 ∧
    (generate xs).2 ≤ (20*xs.length+1)*Nat.factorial xs.length := by
  cases xs with
  | nil => rw [generate_eqn]; simp
  | cons x xs =>
    have hb : ∀ y ∈ x :: xs,
        (5*xs.length+1)*Nat.factorial xs.length ≤
          (removeRun y (x :: xs)).2 + (generate (removeRun y (x :: xs)).1).2 ∧
        (removeRun y (x :: xs)).2 + (generate (removeRun y (x :: xs)).1).2 ≤
          (20*xs.length+1)*Nat.factorial xs.length+3*(xs.length+1)+1 := by
      intro y hy
      have hr := removeRun_length y (x :: xs) hy
      have hn : (removeRun y (x :: xs)).1.length = xs.length := by
        simp only [List.length_cons] at hr
        omega
      have hi := generate_bounds_all (removeRun y (x :: xs)).1
      rw [hn] at hi
      have hu := removeRun_upper y (x :: xs)
      simp only [List.length_cons] at hu
      constructor <;> omega
    have hs := sum_bounds _ (x :: xs) _ _ hb
    change (x :: xs).length * _ ≤ subproblemWork (x :: xs) ∧
      subproblemWork (x :: xs) ≤ (x :: xs).length * _ at hs
    have hsq := PositionalPermutations.square_le_two_factorial (xs.length+1)
    have hn := Nat.self_le_factorial (xs.length+1)
    have hp := Nat.factorial_pos (xs.length+1)
    have hu : 3*((xs.length+1)*(xs.length+1))+6*(xs.length+1)+3 ≤
        15*Nat.factorial (xs.length+1) := by omega
    rw [generate_work_cons]
    simp only [List.length_cons] at hs ⊢
    rw [Nat.factorial_succ] at hu ⊢
    constructor <;> nlinarith
termination_by xs.length
decreasing_by exact removeRun_decrease y (x :: xs) hy

theorem generate_bounds (xs : List α) (hn : 1 ≤ xs.length) :
    xs.length*Nat.factorial xs.length ≤ (generate xs).2 ∧
    (generate xs).2 ≤ 21*(xs.length*Nat.factorial xs.length) := by
  have h := generate_bounds_all xs
  have hm := Nat.mul_le_mul_right (Nat.factorial xs.length)
    (show 20*xs.length+1 ≤ 21*xs.length by omega)
  constructor <;> nlinarith

theorem observed_bounds (xs : List α) (hn : 1 ≤ xs.length) :
    xs.length*Nat.factorial xs.length ≤ (observed xs).2 ∧
    (observed xs).2 ≤ 26*(xs.length*Nat.factorial xs.length) := by
  rw [observed_eq]
  have hu := (generate_bounds xs hn).2
  have hp := Nat.factorial_pos xs.length
  have hm := Nat.mul_le_mul_right (Nat.factorial xs.length) hn
  constructor <;> omega

theorem generate_theta (inputs : Nat → List α) (h : ∀ n, (inputs n).length = n) :
    Asymptotics.IsTheta Filter.atTop (fun n => ((generate (inputs n)).2 : ℝ))
      (fun n : Nat => ((n*Nat.factorial n : Nat) : ℝ)) := by
  constructor
  · apply isBigO_of_nat_bound _ _ 21 1
    intro n hn
    simpa only [h n] using (generate_bounds (inputs n) (by rw [h]; exact hn)).2
  · apply isBigO_of_nat_bound _ _ 1 1
    intro n hn
    simpa only [h n, Nat.one_mul] using (generate_bounds (inputs n) (by rw [h]; exact hn)).1

theorem observed_theta (inputs : Nat → List α) (h : ∀ n, (inputs n).length = n) :
    Asymptotics.IsTheta Filter.atTop (fun n => ((observed (inputs n)).2 : ℝ))
      (fun n : Nat => ((n*Nat.factorial n : Nat) : ℝ)) := by
  constructor
  · apply isBigO_of_nat_bound _ _ 26 1
    intro n hn
    simpa only [h n] using (observed_bounds (inputs n) (by rw [h]; exact hn)).2
  · apply isBigO_of_nat_bound _ _ 1 1
    intro n hn
    simpa only [h n, Nat.one_mul] using (observed_bounds (inputs n) (by rw [h]; exact hn)).1

theorem generate_not_shifted_lower (inputs : Nat → List α)
    (h : ∀ n, (inputs n).length = n) : ¬ Asymptotics.IsBigO Filter.atTop
    (fun n : Nat => (Nat.factorial (n+2) : ℝ))
    (fun n => ((generate (inputs n)).2 : ℝ)) := by
  intro hc
  exact PositionalPermutations.shifted_factorial_not_bigO (hc.trans (generate_theta inputs h).1)

theorem observed_not_shifted_lower (inputs : Nat → List α)
    (h : ∀ n, (inputs n).length = n) : ¬ Asymptotics.IsBigO Filter.atTop
    (fun n : Nat => (Nat.factorial (n+2) : ℝ))
    (fun n => ((observed (inputs n)).2 : ℝ)) := by
  intro hc
  exact PositionalPermutations.shifted_factorial_not_bigO (hc.trans (observed_theta inputs h).1)

end Resources.ErasurePermutations
