import Applications.Resources.PositionalPermutations
import Applications.Resources.Growth

/-! Growth of the executed positional construction and complete spine observation.
The shifted-factorial rejection concerns these explicit prices, not GHC time. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.PositionalPermutations

theorem triangle_upper (n : Nat) : triangle n ≤ n*n := by
  calc
    _ ≤ ∑ _i ∈ Finset.range n, n :=
      Finset.sum_le_sum (fun i hi => Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    _ = n*n := by simp

theorem square_le_two_factorial (n : Nat) : n*n ≤ 2 * Nat.factorial n := by
  induction n with
  | zero => decide
  | succ n ih =>
    cases n with
    | zero => decide
    | succ n =>
      by_cases hz : n = 0
      · subst n; decide
      · rw [Nat.factorial_succ]
        have hb := Nat.mul_le_mul_left (n+1) (show 2 ≤ n+1 by omega)
        have hh : n+1+1 ≤ (n+1)*(n+1) := by omega
        have hm := Nat.mul_le_mul_left (n+1+1) (Nat.le_trans hh ih)
        nlinarith

theorem construction_lower (n : Nat) :
    (5*n+1) * Nat.factorial n ≤ constructionWork n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [constructionWork, Nat.factorial_succ]
    have hm := Nat.mul_le_mul_left (n+1) ih
    nlinarith

theorem construction_upper (n : Nat) :
    constructionWork n ≤ (20*n+1) * Nat.factorial n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have ht := Nat.le_trans (triangle_upper (n+1)) (square_le_two_factorial (n+1))
    have hn := Nat.self_le_factorial (n+1)
    have hf := Nat.factorial_pos (n+1)
    have hm := Nat.mul_le_mul_left (n+1) ih
    have hp : 3 * triangle (n+1) + 5*(n+1)+4 ≤ 15 * Nat.factorial (n+1) := by omega
    rw [constructionWork, Nat.factorial_succ]
    rw [Nat.factorial_succ] at hp
    nlinarith

theorem construction_bounds (n : Nat) (hn : 1 ≤ n) :
    n * Nat.factorial n ≤ constructionWork n ∧
      constructionWork n ≤ 21 * (n * Nat.factorial n) := by
  have hl := construction_lower n
  have hu := construction_upper n
  have hm := Nat.mul_le_mul_right (Nat.factorial n) (show 20*n+1 ≤ 21*n by omega)
  constructor <;> nlinarith

theorem construction_theta : Asymptotics.IsTheta Filter.atTop
    (fun n : Nat => (constructionWork n : ℝ))
    (fun n : Nat => ((n * Nat.factorial n : Nat) : ℝ)) := by
  constructor
  · exact isBigO_of_nat_bound _ _ 21 1 (fun n hn => (construction_bounds n hn).2)
  · exact isBigO_of_nat_bound _ _ 1 1 (fun n hn => by simpa using (construction_bounds n hn).1)

universe u
variable {α : Type u}

theorem observed_bounds (xs : List α) (hn : 1 ≤ xs.length) :
    xs.length * Nat.factorial xs.length ≤ (observed xs).2 ∧
      (observed xs).2 ≤ 26 * (xs.length * Nat.factorial xs.length) := by
  rw [observed_eq]
  have hu := (construction_bounds xs.length hn).2
  have hp := Nat.factorial_pos xs.length
  have hm := Nat.mul_le_mul_right (Nat.factorial xs.length) hn
  constructor <;> omega

theorem generate_theta (inputs : Nat → List α) (h : ∀ n, (inputs n).length = n) :
    Asymptotics.IsTheta Filter.atTop (fun n => ((generate (inputs n)).2 : ℝ))
      (fun n : Nat => ((n * Nat.factorial n : Nat) : ℝ)) := by
  simpa only [generate_work, h] using construction_theta

theorem observed_theta (inputs : Nat → List α) (h : ∀ n, (inputs n).length = n) :
    Asymptotics.IsTheta Filter.atTop (fun n => ((observed (inputs n)).2 : ℝ))
      (fun n : Nat => ((n * Nat.factorial n : Nat) : ℝ)) := by
  constructor
  · apply isBigO_of_nat_bound _ _ 26 1
    intro n hn
    simpa only [h n] using (observed_bounds (inputs n) (by rw [h]; exact hn)).2
  · apply isBigO_of_nat_bound _ _ 1 1
    intro n hn
    simpa only [h n, Nat.one_mul] using (observed_bounds (inputs n) (by rw [h]; exact hn)).1

/-- A quantified obstruction, not an extrapolation from finite fixtures. -/
theorem shifted_factorial_not_bigO : ¬ Asymptotics.IsBigO Filter.atTop
    (fun n : Nat => (Nat.factorial (n+2) : ℝ))
    (fun n : Nat => ((n * Nat.factorial n : Nat) : ℝ)) := by
  intro h
  obtain ⟨C, _, he⟩ := (isBigO_natCast_iff _ _).mp h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  let n := C+N+1
  have hh := hN n (by dsimp [n]; omega)
  rw [Nat.factorial_succ, Nat.factorial_succ] at hh
  have hf := Nat.factorial_pos n
  have hc : ((n+2)*(n+1)) * Nat.factorial n ≤ (C*n) * Nat.factorial n := by
    nlinarith
  have hd := Nat.le_of_mul_le_mul_right hc hf
  have hn : C < n := by dsimp [n]; omega
  nlinarith

theorem construction_not_shifted_lower : ¬ Asymptotics.IsBigO Filter.atTop
    (fun n : Nat => (Nat.factorial (n+2) : ℝ))
    (fun n : Nat => (constructionWork n : ℝ)) := by
  intro h
  exact shifted_factorial_not_bigO (h.trans construction_theta.1)

theorem observed_not_shifted_lower (inputs : Nat → List α)
    (h : ∀ n, (inputs n).length = n) : ¬ Asymptotics.IsBigO Filter.atTop
    (fun n : Nat => (Nat.factorial (n+2) : ℝ))
    (fun n => ((observed (inputs n)).2 : ℝ)) := by
  intro hc
  exact shifted_factorial_not_bigO (hc.trans (observed_theta inputs h).1)

end Resources.PositionalPermutations
