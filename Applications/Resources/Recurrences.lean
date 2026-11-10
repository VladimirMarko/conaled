import Applications.Resources.Growth
import SquareKit.FiniteRecurrences
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Map

/-!
# Growth of native positive-index affine folds

The finite mathematics retains independent bases and toll coefficients. These
corollaries use the standard real-cast growth interface and the exact finite
coefficients and inclusive thresholds. No recurrence evaluator is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources

open Filter Asymptotics SquareKit.FiniteRecurrences
open scoped BigOperators

/-- Positive linear tolls give quadratic growth, including an initial base of zero.
The comparison witnesses are `b+c, 1` and `2, 1`. -/
theorem additive_recurrence_isTheta (b c : Nat) (hc : 0 < c) :
    (fun n => (((List.range' 1 n).foldl (fun x k => x + c * k) b : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => ((n * n : Nat) : ℝ)) := by
  constructor
  · exact isBigO_of_nat_bound _ _ (b + c) 1
      (fun n hn => (additive_bounds b c n hc hn).2)
  · exact isBigO_of_nat_bound _ _ 2 1
      (fun n hn => (additive_bounds b c n hc hn).1)

/-- Positive linear tolls give exponential growth for every independent base.
The upper threshold is zero; the reverse threshold is one. -/
theorem doubling_recurrence_isTheta (b c : Nat) (hc : 0 < c) :
    (fun n => (((List.range' 1 n).foldl (fun x k => 2 * x + c * k) b : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => ((2 ^ n : Nat) : ℝ)) := by
  constructor
  · exact isBigO_of_nat_bound _ _ (b + 2 * c) 0 (fun n _ => doubling_upper b c n)
  · apply isBigO_of_nat_bound _ _ 2 1
    intro n hn
    calc
      2 ^ n = 1 * 2 ^ n := by simp
      _ ≤ c * 2 ^ n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hc)
      _ ≤ 2 * (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b :=
        doubling_lower b c n hn

/-- The reserve and lower bounds give factorial growth, with no positive-base
premise. The witnesses are `b+3*c, 1` and `1, 1`. -/
theorem factorial_recurrence_isTheta (b c : Nat) (hc : 0 < c) :
    (fun n => (((List.range' 1 n).foldl (fun x k => k * x + c * k) b : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => (Nat.factorial n : ℝ)) := by
  constructor
  · apply isBigO_of_nat_bound _ _ (b + 3 * c) 1
    intro n hn
    have h := factorial_reserve b c n hn
    omega
  · apply isBigO_of_nat_bound _ _ 1 1
    intro n hn
    have h : Nat.factorial n ≤
        (List.range' 1 n).foldl (fun x k => k * x + c * k) b := by
      calc
        Nat.factorial n = 1 * Nat.factorial n := by simp
        _ ≤ c * Nat.factorial n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hc)
        _ ≤ (List.range' 1 n).foldl (fun x k => k * x + c * k) b :=
          factorial_lower b c n hn
    simpa using h


/-- A single eventual toll bound extends to every positive index; the toll at
zero remains unconstrained. The natural coefficient is chosen once for all n. -/
theorem positive_linear_bound_of_isBigO
    (toll : Nat → Nat)
    (h : Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => (toll n : ℝ)) (fun n : Nat => (n : ℝ))) :
    ∃ C : Nat, 0 < C ∧ ∀ n : Nat, toll (n + 1) ≤ C * (n + 1) := by
  obtain ⟨c, hc, hbound⟩ := Asymptotics.bound_of_isBigO_nat_atTop h
  obtain ⟨C, hC⟩ := exists_nat_gt c
  refine ⟨C, (Nat.cast_pos (α := ℝ)).mp (hc.trans hC), ?_⟩
  intro n
  have hn : (0 : ℝ) < ((n + 1 : Nat) : ℝ) :=
    (Nat.cast_pos (α := ℝ)).mpr (Nat.succ_pos n)
  have hreal : (toll (n + 1) : ℝ) ≤ c * ((n + 1 : Nat) : ℝ) := by
    simpa only [Real.norm_natCast] using hbound (x := n + 1) (ne_of_gt hn)
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_mul]
  exact hreal.trans (mul_le_mul_of_nonneg_right hC.le hn.le)

/-- Reuse the accepted sequence comparison with the fixed linear-toll model.
Only the positive transition indices need a pointwise toll inequality. -/
private theorem affine_fold_le_linear_toll
    (weight toll : Nat → Nat) (b C : Nat)
    (hupper : ∀ n : Nat, toll (n + 1) ≤ C * (n + 1)) (n : Nat) :
    (List.range' 1 n).foldl (fun x k => weight k * x + toll k) b ≤
      (List.range' 1 n).foldl (fun x k => weight k * x + C * k) b := by
  refine affine_fold_le weight toll
    (fun m => (List.range' 1 m).foldl (fun x k => weight k * x + C * k) b)
    b ?_ ?_ n
  · simp
  · intro m
    rw [affine_fold_succ weight (fun k => C * k) b m]
    exact Nat.add_le_add_left (hupper m) _

/-- An arbitrary toll of linear order gives quadratic accumulated growth for
every independent natural base, including zero. The witnesses are b+C at one
and 4*D at 2*N; the finite triangular reserve is retained until absorption. -/
theorem additive_toll_recurrence_isTheta
    (toll : Nat → Nat) (b : Nat)
    (h : Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => (toll n : ℝ)) (fun n : Nat => (n : ℝ))) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat =>
        (((List.range' 1 n).foldl (fun x k => x + toll k) b : Nat) : ℝ))
      (fun n : Nat => ((n * n : Nat) : ℝ)) := by
  obtain ⟨C, hC, hupper⟩ := positive_linear_bound_of_isBigO toll h.1
  obtain ⟨D, _, htail⟩ :=
    (isBigO_natCast_iff (l := (atTop : Filter Nat)) (fun n : Nat => n) toll).mp h.2
  obtain ⟨N, hlower⟩ := eventually_atTop.mp htail
  constructor
  · apply isBigO_of_nat_bound _ _ (b + C) 1
    intro n hn
    have hcompare := affine_fold_le_linear_toll (fun _ => 1) toll b C hupper n
    simp only [one_mul] at hcompare
    exact hcompare.trans (additive_bounds b C n hC hn).2
  · apply isBigO_of_nat_bound _ _ (4 * D) (2 * N)
    intro n hn
    rw [additive_toll_exact]
    have hreserve := triangle_le_scaled_toll_sum toll D N hlower n
    have hn_triangle := (SquareKit.FiniteSums.triangle_bounds n).1
    have hN_triangle := (SquareKit.FiniteSums.triangle_bounds N).2
    have hN_square : 4 * (N * N) ≤ n * n := by
      nlinarith only [Nat.mul_le_mul hn hn]
    have hsum : n * n ≤ 4 * D * (∑ k ∈ Finset.Ico 1 (n + 1), toll k) := by
      nlinarith only [hreserve, hn_triangle, hN_triangle, hN_square]
    exact hsum.trans (Nat.mul_le_mul_left (4 * D) (Nat.le_add_left _ _))

/-- A positive independent base supplies the exponential lower contribution;
the arbitrary toll needs only an eventual upper bound, so zero toll is allowed.
The upper witness is b+2*C at zero and the reverse witness is one at zero. -/
theorem doubling_toll_recurrence_isTheta
    (toll : Nat → Nat) (b : Nat) (hb : 0 < b)
    (h : Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => (toll n : ℝ)) (fun n : Nat => (n : ℝ))) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat =>
        (((List.range' 1 n).foldl (fun x k => 2 * x + toll k) b : Nat) : ℝ))
      (fun n : Nat => ((2 ^ n : Nat) : ℝ)) := by
  obtain ⟨C, _, hupper⟩ := positive_linear_bound_of_isBigO toll h
  constructor
  · apply isBigO_of_nat_bound _ _ (b + 2 * C) 0
    intro n _
    exact (affine_fold_le_linear_toll (fun _ => 2) toll b C hupper n).trans
      (doubling_upper b C n)
  · apply isBigO_of_nat_bound _ _ 1 0
    intro n _
    have hb_one : 1 ≤ b := hb
    have hbase : 2 ^ n ≤ b * 2 ^ n := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (2 ^ n) hb_one
    simpa only [one_mul] using hbase.trans (doubling_base_lower toll b n)

/-- A positive independent base supplies the factorial lower contribution;
the arbitrary toll needs only an eventual upper bound. The reserve gives upper
witness b+3*C at one; the propagated base gives reverse witness one at zero. -/
theorem factorial_toll_recurrence_isTheta
    (toll : Nat → Nat) (b : Nat) (hb : 0 < b)
    (h : Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => (toll n : ℝ)) (fun n : Nat => (n : ℝ))) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat =>
        (((List.range' 1 n).foldl (fun x k => k * x + toll k) b : Nat) : ℝ))
      (fun n : Nat => (Nat.factorial n : ℝ)) := by
  obtain ⟨C, _, hupper⟩ := positive_linear_bound_of_isBigO toll h
  constructor
  · apply isBigO_of_nat_bound _ _ (b + 3 * C) 1
    intro n hn
    have hcompare := affine_fold_le_linear_toll (fun k => k) toll b C hupper n
    have hreserve := factorial_reserve b C n hn
    exact hcompare.trans ((Nat.le_add_right _ _).trans hreserve)
  · apply isBigO_of_nat_bound _ _ 1 0
    intro n _
    have hb_one : 1 ≤ b := hb
    have hbase : Nat.factorial n ≤ b * Nat.factorial n := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (Nat.factorial n) hb_one
    simpa only [one_mul] using hbase.trans (factorial_base_lower toll b n)

/-- For natural functions, positive natural and rational eventual comparison
coefficients are equivalent. The comparator is allowed to vanish. -/
theorem nat_bound_iff_rat_bound (f g : Nat → Nat) :
    (∃ C N : Nat, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * g n) ↔
      (∃ C : ℚ, 0 < C ∧ ∃ N : Nat,
        ∀ n, N ≤ n → (f n : ℚ) ≤ C * (g n : ℚ)) := by
  have hcast :
      ((fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ))) ↔
        ((fun n => (f n : ℚ)) =O[atTop] (fun n => (g n : ℚ))) := by
    simp only [Asymptotics.isBigO_iff, ← Rat.norm_cast_real, Rat.cast_natCast]
  have hnat := isBigO_natCast_iff (l := (atTop : Filter Nat)) f g
  have hrat := isBigO_rat_iff_eventually_le_mul (l := (atTop : Filter Nat))
    (fun n => (f n : ℚ)) (fun n => (g n : ℚ))
    (Eventually.of_forall fun n => Nat.cast_nonneg (f n))
    (Eventually.of_forall fun n => Nat.cast_nonneg (g n))
  constructor
  · rintro ⟨C, N, hC, hbound⟩
    have hn := hnat.mpr ⟨C, hC, eventually_atTop.mpr ⟨N, hbound⟩⟩
    obtain ⟨D, hD, hDbound⟩ := hrat.mp (hcast.mp hn)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hDbound
    exact ⟨D, hD, M, hM⟩
  · rintro ⟨C, hC, N, hbound⟩
    have hq := hrat.mpr ⟨C, hC, eventually_atTop.mpr ⟨N, hbound⟩⟩
    obtain ⟨D, hD, hDbound⟩ := hnat.mp (hcast.mpr hq)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hDbound
    exact ⟨D, M, hD, hM⟩

end Resources

namespace Resources

open Filter Asymptotics SquareKit.FiniteRecurrences

/-- Pulling back along the second projection retains every first-coordinate fiber.
The single threshold bounds only the second coordinate. -/
theorem eventually_comap_snd_atTop (p : Nat × Nat → Prop) :
    (∀ᶠ q in Filter.comap Prod.snd Filter.atTop, p q) ↔
      ∃ N : Nat, ∀ m n : Nat, N ≤ n → p (m, n) := by
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun m n hn => hN n hn (m, n) rfl⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn q hq
    rcases q with ⟨m, k⟩
    change k = n at hq
    subst k
    exact hN m n hn

/-- Uniform growth of natural counts uses one positive coefficient and one
second-coordinate threshold before all pairs, including the zero first fiber. -/
theorem isBigO_natCast_comap_snd_iff (f g : Nat → Nat → Nat) :
    Asymptotics.IsBigO (Filter.comap Prod.snd Filter.atTop)
      (fun q : Nat × Nat => (f q.1 q.2 : ℝ))
      (fun q : Nat × Nat => (g q.1 q.2 : ℝ)) ↔
      ∃ C N : Nat, 0 < C ∧ ∀ m n : Nat, N ≤ n → f m n ≤ C * g m n := by
  rw [isBigO_natCast_iff]
  constructor
  · rintro ⟨C, hC, hbound⟩
    obtain ⟨N, hN⟩ := (eventually_comap_snd_atTop _).mp hbound
    exact ⟨C, N, hC, hN⟩
  · rintro ⟨C, N, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    exact (eventually_comap_snd_atTop _).mpr ⟨N, hbound⟩

/-- Uniform Theta retains independent positive coefficients and thresholds for
the two comparison directions. No nonzero-comparator premise is required. -/
theorem isTheta_natCast_comap_snd_iff (f g : Nat → Nat → Nat) :
    Asymptotics.IsTheta (Filter.comap Prod.snd Filter.atTop)
      (fun q : Nat × Nat => (f q.1 q.2 : ℝ))
      (fun q : Nat × Nat => (g q.1 q.2 : ℝ)) ↔
      (∃ C N : Nat, 0 < C ∧ ∀ m n : Nat, N ≤ n → f m n ≤ C * g m n) ∧
      (∃ D M : Nat, 0 < D ∧ ∀ m n : Nat, M ≤ n → g m n ≤ D * f m n) := by
  exact and_congr (isBigO_natCast_comap_snd_iff f g)
    (isBigO_natCast_comap_snd_iff g f)

/-- An independent quadratic base and linear toll give uniform two-parameter
growth. The witnesses are B+C at NB+NC and D+E at ND+NE. -/
theorem two_run_recurrence_isTheta (base toll : Nat → Nat)
    (hb : Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => (base n : ℝ)) (fun n : Nat => ((n * n : Nat) : ℝ)))
    (ht : Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => (toll n : ℝ)) (fun n : Nat => (n : ℝ))) :
    Asymptotics.IsTheta (Filter.comap Prod.snd Filter.atTop)
      (fun q : Nat × Nat =>
        (((List.range' 1 q.1).foldl (fun x _ => x + toll q.2) (base q.2) : Nat) : ℝ))
      (fun q : Nat × Nat => ((q.1 * q.2 + q.2 * q.2 : Nat) : ℝ)) := by
  obtain ⟨B, hB, hbu_event⟩ :=
    (isBigO_natCast_iff (l := (Filter.atTop : Filter Nat))
      base (fun n : Nat => n * n)).mp hb.1
  obtain ⟨NB, hbu⟩ := Filter.eventually_atTop.mp hbu_event
  obtain ⟨D, hD, hbl_event⟩ :=
    (isBigO_natCast_iff (l := (Filter.atTop : Filter Nat))
      (fun n : Nat => n * n) base).mp hb.2
  obtain ⟨ND, hbl⟩ := Filter.eventually_atTop.mp hbl_event
  obtain ⟨C, hC, htu_event⟩ :=
    (isBigO_natCast_iff (l := (Filter.atTop : Filter Nat))
      toll (fun n : Nat => n)).mp ht.1
  obtain ⟨NC, htu⟩ := Filter.eventually_atTop.mp htu_event
  obtain ⟨E, hE, htl_event⟩ :=
    (isBigO_natCast_iff (l := (Filter.atTop : Filter Nat))
      (fun n : Nat => n) toll).mp ht.2
  obtain ⟨NE, htl⟩ := Filter.eventually_atTop.mp htl_event
  apply (isTheta_natCast_comap_snd_iff
    (fun m n => (List.range' 1 m).foldl (fun x _ => x + toll n) (base n))
    (fun m n => m * n + n * n)).mpr
  constructor
  · refine ⟨B + C, NB + NC, by omega, ?_⟩
    intro m n hn
    change (List.range' 1 m).foldl (fun x _ => x + toll n) (base n) ≤
      (B + C) * (m * n + n * n)
    rw [constant_toll_exact]
    have hbase := hbu n (by omega)
    have htoll := Nat.mul_le_mul_left m (htu n (by omega))
    calc
      base n + m * toll n ≤ B * (n * n) + m * (C * n) :=
        Nat.add_le_add hbase htoll
      _ = B * (n * n) + C * (m * n) := by ring
      _ ≤ B * (m * n + n * n) + C * (m * n + n * n) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left B (Nat.le_add_left _ _))
          (Nat.mul_le_mul_left C (Nat.le_add_right _ _))
      _ = (B + C) * (m * n + n * n) := by ring
  · refine ⟨D + E, ND + NE, by omega, ?_⟩
    intro m n hn
    change m * n + n * n ≤
      (D + E) * (List.range' 1 m).foldl (fun x _ => x + toll n) (base n)
    rw [constant_toll_exact]
    have hbase := hbl n (by omega)
    have htoll := Nat.mul_le_mul_left m (htl n (by omega))
    calc
      m * n + n * n ≤ m * (E * toll n) + D * base n :=
        Nat.add_le_add htoll hbase
      _ = E * (m * toll n) + D * base n := by ring
      _ ≤ E * (base n + m * toll n) + D * (base n + m * toll n) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left E (Nat.le_add_left _ _))
          (Nat.mul_le_mul_left D (Nat.le_add_right _ _))
      _ = (D + E) * (base n + m * toll n) := by ring

/-- Separate eventual base and scaled-step bounds give uniform growth for an
arbitrary two-parameter count. The witnesses are B+C and D+E at N; D may be zero. -/
theorem two_param_recurrence_isTheta (T : Nat → Nat → Nat) (B D C E N : Nat)
    (hB : 0 < B) (hC : 0 < C) (hE : 0 < E)
    (hb : ∀ n, N ≤ n → n * n ≤ D * T 0 n ∧ T 0 n ≤ B * (n * n))
    (hs : ∀ m n, N ≤ n → E * T m n + n ≤ E * T (m + 1) n ∧
      T (m + 1) n ≤ T m n + C * n) :
    Asymptotics.IsTheta (Filter.comap Prod.snd Filter.atTop)
      (fun q : Nat × Nat => (T q.1 q.2 : ℝ))
      (fun q : Nat × Nat => ((q.1 * q.2 + q.2 * q.2 : Nat) : ℝ)) := by
  apply (isTheta_natCast_comap_snd_iff T (fun m n => m * n + n * n)).mpr
  constructor
  · refine ⟨B + C, N, by omega, ?_⟩
    intro m n hn
    simpa only [Nat.add_comm] using
      (two_param_eventual_bounds T B D C E N hE hb hs m n hn).2
  · refine ⟨D + E, N, by omega, ?_⟩
    intro m n hn
    simpa only [Nat.add_comm] using
      (two_param_eventual_bounds T B D C E N hE hb hs m n hn).1

end Resources
