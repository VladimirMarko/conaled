import Mathlib.Basic.NNReal.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Algebra.Order.Archimedean.Basic

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
theorem isBigO_nnrealCast_iff {ι : Type u} {l : Filter ι} (f g : ι → NNReal) :
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

end Resources
