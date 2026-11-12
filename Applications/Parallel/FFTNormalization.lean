import Applications.Parallel.NormalizedFourier
import Mathlib.Tactic.LinearCombination

/-! Normalization and exact matrix semantics for the existing factor-tree FFT. -/
namespace Applications.Parallel.FFTUnitary

open scoped BigOperators Matrix

noncomputable def normalization (N : ℕ) : ℂ := (↑(Real.sqrt N) : ℂ)⁻¹

@[simp] theorem normalization_one : normalization 1 = 1 := by simp [normalization]

theorem normalization_mul (m n : ℕ) : normalization (m * n) = normalization m * normalization n := by
  simp [normalization, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), mul_comm]

@[simp] theorem normalization_star (N : ℕ) : star (normalization N) = normalization N := by
  simp [normalization]

@[simp] theorem normalization_conj (N : ℕ) :
    starRingEnd ℂ (normalization N) = normalization N := normalization_star N

theorem normalization_sq (N : ℕ) : normalization N ^ 2 = (N : ℂ)⁻¹ := by
  rw [normalization, inv_pow]
  congr 1
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  norm_cast

/-- The decoder's reversal is an explicit register reindexing. -/
theorem normalized_fft_decode (s : Factor) (x : s.Data ℂ) (k : Fin s.reverse.size) :
    normalization s.size * s.reverse.decode (s.fft s.fourierRoot x) k =
      (fourierMatrix s.size *ᵥ s.decode x) (Fin.cast s.size_reverse k) := by
  rw [s.fourier_correct]
  simp only [Factor.directDFT, Matrix.mulVec, dotProduct, fourierMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← FFTScalar.phase_fourierRoot, FFTScalar.phase_pow, one_mul]
  simp only [Fin.val_cast]
  rw [Nat.mul_comm j.val k.val]
  change normalization s.size * (s.decode x j * FFTScalar.phase s.size (k.val * j.val)) = _
  dsimp [normalization]
  ring

noncomputable def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![normalization 2, normalization 2; normalization 2, -normalization 2]

theorem hadamard_unitary : hadamardMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  have hc := normalization_sq 2
  norm_num at hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hadamardMatrix,
      normalization_conj] <;> linear_combination 2 * hc

noncomputable def hadamard : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨hadamardMatrix, hadamard_unitary⟩

theorem hadamard_fourier : hadamardMatrix = fourierMatrix 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, fourierMatrix, normalization, FFTScalar.phase_zero,
      FFTScalar.phase_two]

/-- Exact phase constants are admissible diagonal unitary entries. -/
noncomputable def phaseUnitary (N k : ℕ) : _root_.unitary ℂ := by
  have hn : Complex.normSq (FFTScalar.phase N k) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    unfold FFTScalar.phase
    rw [Complex.norm_exp_ofReal_mul_I]
    norm_num
  refine ⟨FFTScalar.phase N k, ?_, ?_⟩
  · change starRingEnd ℂ (FFTScalar.phase N k) * FFTScalar.phase N k = 1
    rw [mul_comm, Complex.mul_conj, hn]
    rfl
  · change FFTScalar.phase N k * starRingEnd ℂ (FFTScalar.phase N k) = 1
    rw [Complex.mul_conj, hn]
    rfl

@[simp] theorem phaseUnitary_coe (N k : ℕ) :
    (phaseUnitary N k : ℂ) = FFTScalar.phase N k := rfl

/-- The original algebraic twiddle factorization specialized to exact complex phases. -/
theorem phase_factorization (s t : Factor) (a b c d : ℕ) :
    FFTScalar.phase (s.size * t.size) ((b + t.size * a) * (c + s.size * d)) =
      FFTScalar.phase s.size (a * c) * FFTScalar.phase (s.size * t.size) (b * c) *
        FFTScalar.phase t.size (b * d) := by
  have hroot : FFTScalar.phase (s.size * t.size) 1 ^ (s.size * t.size) = 1 := by
    change FFTScalar.phase (s.comp t).size 1 ^ (s.comp t).size = 1
    rw [FFTScalar.phase_fourierRoot]
    exact (s.comp t).fourierRoot_pow
  have ht : FFTScalar.phase (s.size * t.size) 1 ^ s.size = FFTScalar.phase t.size 1 := by
    rw [FFTScalar.phase_pow, one_mul]
    apply FFTScalar.phase_ratio (Nat.mul_pos s.size_pos t.size_pos) t.size_pos
    ring
  have h := Factor.twiddle_factorization (FFTScalar.phase (s.size * t.size) 1)
    s.size t.size a b d c hroot
  rw [FFTScalar.phase_child, ht] at h
  simpa only [FFTScalar.phase_pow, one_mul] using h

/-- The normalized Cooley–Tukey coefficient identity. The final permutation changes
row-major `(c,d)` storage to the conventional Fourier output index `(d,c)`. -/
theorem fourierMatrix_comp_entry (s t : Factor)
    (a c : Fin s.size) (b d : Fin t.size) :
    fourierMatrix (s.size * t.size)
      (Fin.cast (Nat.mul_comm t.size s.size) (finProdFinEquiv (d, c)))
      (finProdFinEquiv (a, b)) =
    fourierMatrix t.size d b * FFTScalar.phase (s.size * t.size) (c.val * b.val) *
      fourierMatrix s.size c a := by
  change normalization (s.size * t.size) *
    FFTScalar.phase (s.size * t.size)
      ((c.val + s.size * d.val) * (b.val + t.size * a.val)) =
    (normalization t.size * FFTScalar.phase t.size (d.val * b.val)) *
      FFTScalar.phase (s.size * t.size) (c.val * b.val) *
      (normalization s.size * FFTScalar.phase s.size (c.val * a.val))
  rw [Nat.mul_comm (c.val + s.size * d.val), phase_factorization, normalization_mul]
  rw [Nat.mul_comm a.val c.val, Nat.mul_comm b.val c.val, Nat.mul_comm b.val d.val]
  ring

/-- The coefficient identity as two finite passes with the intermediate twiddle. -/
theorem fourierMatrix_comp_mulVec (s t : Factor)
    (x : Fin (s.size * t.size) → ℂ) (c : Fin s.size) (d : Fin t.size) :
    (fourierMatrix (s.size * t.size) *ᵥ x)
      (Fin.cast (Nat.mul_comm t.size s.size) (finProdFinEquiv (d, c))) =
    ∑ b, (fourierMatrix t.size d b *
      (FFTScalar.phase (s.size * t.size) (c.val * b.val) *
        ∑ a, (fourierMatrix s.size c a * x (finProdFinEquiv (a, b))))) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← finProdFinEquiv.sum_comp (fun j : Fin (s.size * t.size) =>
    fourierMatrix (s.size * t.size)
      (Fin.cast (Nat.mul_comm t.size s.size) (finProdFinEquiv (d, c))) j * x j)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [fourierMatrix_comp_entry]
  ring

end Applications.Parallel.FFTUnitary
