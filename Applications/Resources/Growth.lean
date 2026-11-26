import Mathlib.Basic.NNReal.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Natural measured counts use the standard asymptotic interface after real casting. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources

/-- An explicit natural bound gives the same eventual bound on real-cast counts. -/
theorem isBigO_of_nat_bound (f g : Nat → Nat) (C N : Nat)
    (bound : ∀ n, N ≤ n → f n ≤ C * g n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ)) (fun n => (g n : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(C : ℝ), Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  simpa using (Nat.cast_le (α := ℝ)).mpr (bound n hn)

open Filter
universe u

/-- For eventually nonnegative rational functions, norm growth is exactly a
positive rational eventual upper bound. The signs need not hold initially. -/
theorem isBigO_rat_iff_eventually_le_mul {ι : Type u} {l : Filter ι}
    (f g : ι → ℚ) (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x) :
    f =O[l] g ↔ ∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, f x ≤ C * g x := by
  constructor
  · intro h
    obtain ⟨c, hc, hbound⟩ := Asymptotics.isBigO_iff'.mp h
    obtain ⟨K, hK⟩ := exists_nat_gt c
    have hKpos : 0 < K := (Nat.cast_pos (α := ℝ)).mp (hc.trans hK)
    refine ⟨(K : ℚ), Nat.cast_pos.mpr hKpos, ?_⟩
    filter_upwards [hf, hg, hbound] with x hfx hgx hx
    have hfr : 0 ≤ (f x : ℝ) := Rat.cast_nonneg.mpr hfx
    have hgr : 0 ≤ (g x : ℝ) := Rat.cast_nonneg.mpr hgx
    have hnormf : ‖f x‖ = (f x : ℝ) := by
      rw [← Rat.norm_cast_real, Real.norm_of_nonneg hfr]
    have hnormg : ‖g x‖ = (g x : ℝ) := by
      rw [← Rat.norm_cast_real, Real.norm_of_nonneg hgr]
    rw [hnormf, hnormg] at hx
    have hupper : (f x : ℝ) ≤ (K : ℝ) * (g x : ℝ) :=
      hx.trans (mul_le_mul_of_nonneg_right hK.le hgr)
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_mul, Rat.cast_natCast] using hupper
  · rintro ⟨C, hC, hbound⟩
    apply Asymptotics.isBigO_iff'.mpr
    refine ⟨(C : ℝ), Rat.cast_pos.mpr hC, ?_⟩
    filter_upwards [hf, hg, hbound] with x hfx hgx hx
    have hfr : 0 ≤ (f x : ℝ) := Rat.cast_nonneg.mpr hfx
    have hgr : 0 ≤ (g x : ℝ) := Rat.cast_nonneg.mpr hgx
    rw [← Rat.norm_cast_real (f x), ← Rat.norm_cast_real (g x),
      Real.norm_of_nonneg hfr, Real.norm_of_nonneg hgr]
    simpa only [Rat.cast_mul] using (Rat.cast_le (K := ℝ)).mpr hx

/-- A positive natural coefficient characterizes growth of natural counts at
any filter after real casting. No nonzero premise is imposed on the comparator. -/
theorem isBigO_natCast_iff {ι : Type u} {l : Filter ι} (f g : ι → ℕ) :
    (fun x => (f x : ℝ)) =O[l] (fun x => (g x : ℝ)) ↔
      ∃ C : ℕ, 0 < C ∧ ∀ᶠ x in l, f x ≤ C * g x := by
  constructor
  · intro h
    obtain ⟨c, hc, hbound⟩ := Asymptotics.isBigO_iff'.mp h
    obtain ⟨K, hK⟩ := exists_nat_gt c
    refine ⟨K, (Nat.cast_pos (α := ℝ)).mp (hc.trans hK), ?_⟩
    filter_upwards [hbound] with x hx
    simp only [Real.norm_natCast] at hx
    have hupper : (f x : ℝ) ≤ (K : ℝ) * (g x : ℝ) :=
      hx.trans (mul_le_mul_of_nonneg_right hK.le (Nat.cast_nonneg _))
    apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_mul] using hupper
  · rintro ⟨C, hC, hbound⟩
    apply Asymptotics.isBigO_iff'.mpr
    refine ⟨(C : ℝ), Nat.cast_pos.mpr hC, ?_⟩
    filter_upwards [hbound] with x hx
    simp only [Real.norm_natCast]
    simpa only [Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hx

/-- The shifted square has comparison constants one and four from index one. -/
theorem successor_square_bounds (n : ℕ) (hn : 1 ≤ n) :
    n * n ≤ (n + 1) * (n + 1) ∧ (n + 1) * (n + 1) ≤ 4 * n * n := by
  constructor
  · exact Nat.mul_le_mul (Nat.le_succ n) (Nat.le_succ n)
  · have h : n + 1 ≤ 2 * n := by omega
    calc
      (n + 1) * (n + 1) ≤ (2 * n) * (2 * n) := Nat.mul_le_mul h h
      _ = (2 * 2) * (n * n) := mul_mul_mul_comm _ _ _ _
      _ = 4 * n * n := (Nat.mul_assoc 4 n n).symm

/-- Real-cast nonnegative functions admit a positive natural comparison
coefficient at every filter. The comparator may vanish. -/
theorem isBigO_toReal_iff {ι : Type u} {l : Filter ι} (f g : ι → NNReal) :
    (fun x => (f x : ℝ)) =O[l] (fun x => (g x : ℝ)) ↔
      ∃ C : ℕ, 0 < C ∧ ∀ᶠ x in l, f x ≤ (C : NNReal) * g x := by
  constructor
  · intro h
    obtain ⟨c, hc, hbound⟩ := Asymptotics.isBigO_iff'.mp h
    obtain ⟨K, hK⟩ := exists_nat_gt c
    refine ⟨K, (Nat.cast_pos (α := ℝ)).mp (hc.trans hK), ?_⟩
    filter_upwards [hbound] with x hx
    rw [Real.norm_of_nonneg (NNReal.coe_nonneg (f x)), Real.norm_of_nonneg (NNReal.coe_nonneg (g x))] at hx
    have hupper : (f x : ℝ) ≤ (K : ℝ) * (g x : ℝ) :=
      hx.trans (mul_le_mul_of_nonneg_right hK.le (NNReal.coe_nonneg (g x)))
    exact_mod_cast hupper
  · rintro ⟨C, hC, hbound⟩
    apply Asymptotics.isBigO_iff'.mpr
    refine ⟨(C : ℝ), Nat.cast_pos.mpr hC, ?_⟩
    filter_upwards [hbound] with x hx
    rw [Real.norm_of_nonneg (NNReal.coe_nonneg (f x)), Real.norm_of_nonneg (NNReal.coe_nonneg (g x))]
    exact_mod_cast hx
/-- The natural ceiling log has at most twice the real binary log once `n ≥ 2`.
The lower bound on `n` supplies the unit of slack needed for ceiling. -/
theorem clog_two_cast_le_two_logb (n : Nat) (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.logb 2 n := by
    calc
      1 = Real.logb 2 (2 : ℝ) := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 n := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn'
  have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 n + 1 := by
    rw [← Real.natCeil_logb_natCast 2 n]
    simp only [Nat.cast_ofNat]
    exact Nat.ceil_lt_add_one (by linarith)
  linarith

/-- An eventual affine ceiling-log bound gives ordinary logarithmic work.
The additive term is absorbed only beyond `n ≥ 1`; zero coefficients and an
arbitrary starting threshold remain allowed. -/
theorem isBigO_logb_succ_of_clog_bound (f : Nat → Nat) (a b N : Nat)
    (bound : ∀ n, N ≤ n → f n ≤ a * Nat.clog 2 (n + 1) + b) :
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2 * ((a + b : Nat) : ℝ),
    Filter.eventually_atTop.mpr ⟨max N 1, fun n hn => ?_⟩⟩
  have hN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have hone : 1 ≤ n := (Nat.le_max_right _ _).trans hn
  have hclog : 1 ≤ Nat.clog 2 (n + 1) :=
    Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 1)
  have hconstant : b ≤ b * Nat.clog 2 (n + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hclog
  have hnat : f n ≤ (a + b) * Nat.clog 2 (n + 1) := by
    calc
      f n ≤ a * Nat.clog 2 (n + 1) + b := bound n hN
      _ ≤ a * Nat.clog 2 (n + 1) + b * Nat.clog 2 (n + 1) :=
        Nat.add_le_add_left hconstant _
      _ = (a + b) * Nat.clog 2 (n + 1) := by ring
  have hb : (f n : ℝ) ≤ ((a + b : Nat) : ℝ) * (Nat.clog 2 (n + 1) : ℝ) := by
    exact_mod_cast hnat
  have hlog : 0 ≤ Real.logb 2 (n + 1 : Nat) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  rw [Real.norm_natCast, Real.norm_of_nonneg hlog]
  calc
    (f n : ℝ) ≤ ((a + b : Nat) : ℝ) * (Nat.clog 2 (n + 1) : ℝ) := hb
    _ ≤ ((a + b : Nat) : ℝ) * (2 * Real.logb 2 (n + 1 : Nat)) :=
      mul_le_mul_of_nonneg_left (clog_two_cast_le_two_logb (n + 1) (by omega))
        (Nat.cast_nonneg _)
    _ = 2 * ((a + b : Nat) : ℝ) * Real.logb 2 (n + 1 : Nat) := by ring

/-- A proved ceiling-log count bound yields the ordinary real `O(n log₂ n)`
statement. This numerical bridge makes no claim about compiled execution. -/
theorem isBigO_of_clog_two_bound (f : Nat → Nat) (C N : Nat)
    (bound : ∀ n, N ≤ n → f n ≤ C * (n * Nat.clog 2 n)) :
    Asymptotics.IsBigO Filter.atTop (fun n => (f n : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2 * (C : ℝ), Filter.eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩⟩
  have hN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have htwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hlog : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  have hb : (f n : ℝ) ≤ (C : ℝ) * ((n : ℝ) * (Nat.clog 2 n : ℝ)) := by
    exact_mod_cast bound n hN
  have hc := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (clog_two_cast_le_two_logb n htwo)
      (Nat.cast_nonneg n)) (Nat.cast_nonneg C)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hlog)]
  calc
    (f n : ℝ) ≤ (C : ℝ) * ((n : ℝ) * (Nat.clog 2 n : ℝ)) := hb
    _ ≤ (C : ℝ) * ((n : ℝ) * (2 * Real.logb 2 n)) := hc
    _ = 2 * (C : ℝ) * ((n : ℝ) * Real.logb 2 n) := by ring

end Resources
