import Applications.Parallel.FFTRounds
import Applications.Parallel.FFTRoots
import Applications.Parallel.MeasuredFFT

/-! The exact normalized complex Fourier matrix and its entropy lower bound. -/

namespace Applications.Parallel.FFTUnitary

open scoped BigOperators Matrix

noncomputable def fourierMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (↑(Real.sqrt N) : ℂ)⁻¹ * FFTScalar.phase N (i.val * j.val)

theorem fourierMatrix_normSq {N : ℕ} (i j : Fin N) :
    Complex.normSq (fourierMatrix N i j) = (N : ℝ)⁻¹ := by
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [Complex.normSq_eq_norm_sq]
  simp only [fourierMatrix, norm_mul, norm_inv, FFTScalar.phase,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [inv_pow, Real.sq_sqrt hn]

theorem entropyTerm_inv (x : ℝ) :
    entropyTerm x⁻¹ = x⁻¹ * Real.log x / Real.log 2 := by
  simp [entropyTerm, Real.negMulLog_def, Real.log_inv]

theorem fourierMatrix_entropy {N : ℕ} (hN : 0 < N) :
    matrixEntropy (fourierMatrix N) = (N : ℝ) * (Real.log N / Real.log 2) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [matrixEntropy, fourierMatrix_normSq, entropyTerm_inv,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- A feasible program must pay for the entropy of every Fourier coefficient. -/
theorem fourier_gate_lower_bound {N : ℕ} (hN : 0 < N) (p : Program N)
    (hp : (p.unitary : Matrix (Fin N) (Fin N) ℂ) = fourierMatrix N) :
    (N : ℝ) * (Real.log N / Real.log 2) ≤ 2 * p.gateCount := by
  rw [← fourierMatrix_entropy hN, ← hp]
  exact program_entropy_le p

theorem factor_log (s : Factor) : Real.log s.size / Real.log 2 = s.logSize := by
  rw [s.size_eq_pow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num)))

/-- The structural butterfly count is a lower bound for every admitted exact program,
not just for programs obtained from factor trees. -/
theorem factor_gate_lower_bound (s : Factor) (p : Program s.size)
    (hp : (p.unitary : Matrix (Fin s.size) (Fin s.size) ℂ) = fourierMatrix s.size) :
    s.butterflies ≤ p.gateCount := by
  have h := fourier_gate_lower_bound s.size_pos p hp
  rw [factor_log] at h
  have hb : (2 : ℝ) * s.butterflies = (s.logSize : ℝ) * s.size := by
    exact_mod_cast s.twice_butterflies
  have hi : (s.butterflies : ℝ) ≤ p.gateCount := by nlinarith
  exact_mod_cast hi

theorem fourierMatrix_ne_zero {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    fourierMatrix N i j ≠ 0 := by
  intro hz
  have h := fourierMatrix_normSq i j
  rw [hz] at h
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simpa [hn] using h.symm

/-- Parallel depth is bounded independently of the scalar arithmetic cost model. -/
theorem fourier_round_lower_bound (s : Factor) (p : Program s.size)
    (hp : (p.unitary : Matrix (Fin s.size) (Fin s.size) ℂ) = fourierMatrix s.size) :
    s.logSize ≤ p.roundCount := by
  let i : Fin s.size := ⟨0, s.size_pos⟩
  have hs : rowSupport (fourierMatrix s.size) i = Finset.univ := by
    ext j
    simp [fourierMatrix_ne_zero s.size_pos]
  have h := program_support_bound p i
  rw [hp, hs] at h
  simp only [Finset.card_univ, Fintype.card_fin, s.size_eq_pow] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

example (p : Program (Factor.rightPow 4).size)
    (hp : (p.unitary : Matrix (Fin (Factor.rightPow 4).size)
      (Fin (Factor.rightPow 4).size) ℂ) = fourierMatrix (Factor.rightPow 4).size) :
    32 ≤ p.gateCount := by
  exact factor_gate_lower_bound (Factor.rightPow 4) p hp

end Applications.Parallel.FFTUnitary
